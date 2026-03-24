/**
 * 高性能 DNS over HTTPS 代理
 * 功能：请求合并、缓存、EDNS Client Subnet 注入
 */

// ==================== 常量配置 ====================
const ECS_CONFIG = {
  ipv4Prefix: 16,
  ipv6Prefix: 48,
};

const CACHE_TTL_MAX = 31536000;   // 1年
const CACHE_TTL_MIN = 60;          // 最小60秒
const UPSTREAM_TIMEOUT = 5000;     // 5秒超时

const UPSTREAM_URL = 'https://dns.google/dns-query';

const decoder = new TextDecoder();
const inflight = new Map();         // 请求合并 Map

// ==================== 辅助函数 ====================

/**
 * Base64URL 转 Uint8Array（高性能版）
 */
function base64UrlToUint8Array(base64Url) {
  const s = base64Url.replace(/-/g, '+').replace(/_/g, '/');
  const pad = s.length % 4;
  const str = s + (pad ? '='.repeat(4 - pad) : '');
  const raw = atob(str);
  const u8 = new Uint8Array(raw.length);
  for (let i = 0; i < raw.length; i++) u8[i] = raw.charCodeAt(i);
  return u8;
}

/**
 * IP 地址转字节数组（IPv4/IPv6）
 */
function ipToBytes(ip) {
  if (ip.includes(':')) {
    // IPv6 压缩处理
    const parts = ip.split('::');
    if (parts.length > 2) return null;
    const left = parts[0] ? parts[0].split(':') : [];
    const right = parts[1] ? parts[1].split(':') : [];
    const full = new Array(8).fill(0);
    for (let i = 0; i < left.length; i++) full[i] = parseInt(left[i] || '0', 16);
    for (let i = 0; i < right.length; i++) full[8 - right.length + i] = parseInt(right[i] || '0', 16);
    const out = new Uint8Array(16);
    for (let i = 0; i < 8; i++) {
      out[i * 2] = full[i] >> 8;
      out[i * 2 + 1] = full[i] & 0xff;
    }
    return out;
  } else {
    // IPv4
    const parts = ip.split('.');
    if (parts.length !== 4) return null;
    const bytes = new Uint8Array(4);
    for (let i = 0; i < 4; i++) {
      const n = parseInt(parts[i], 10);
      if (isNaN(n) || n < 0 || n > 255) return null;
      bytes[i] = n;
    }
    return bytes;
  }
}

/**
 * 掩码截断（直接修改原数组，返回自身）
 */
function applyPrefixMask(bytes, prefix) {
  const totalBits = bytes.length === 4 ? 32 : 128;
  const bits = Math.min(prefix, totalBits);
  const fullBytes = bits >> 3;          // 整除8
  const remBits = bits & 7;             // 余数
  for (let i = fullBytes; i < bytes.length; i++) bytes[i] = 0;
  if (remBits && fullBytes < bytes.length) {
    bytes[fullBytes] &= (0xff << (8 - remBits)) & 0xff;
  }
  return bytes;
}

/**
 * 生成子网缓存键（紧凑十六进制）
 */
function getSubnetKey(ip, prefix) {
  const bytes = ipToBytes(ip);
  if (!bytes) return 'unknown';
  const masked = applyPrefixMask(bytes, prefix);
  const len = Math.ceil(prefix / 8);
  let key = '';
  for (let i = 0; i < len; i++) {
    const b = masked[i];
    key += (b < 16 ? '0' : '') + b.toString(16);
  }
  return key;
}

// ==================== DNS 解析（高性能版）====================

/**
 * 解析 DNS 查询报文
 */
function parseDNSQuery(buffer) {
  if (buffer.byteLength < 12 || buffer.byteLength > 4096) return null;
  const pkt = new Uint8Array(buffer);
  // 直接使用 Uint8Array 索引，避免 DataView 开销
  const flags = (pkt[2] << 8) | pkt[3];
  const qdCount = (pkt[4] << 8) | pkt[5];
  if ((flags >> 15) !== 0 || ((flags >> 11) & 0xf) !== 0 || qdCount !== 1) return null;

  // 读取域名（内联，减少函数调用）
  let pos = 12;
  let nameLabels = [];
  let ptrDepth = 0;
  let firstNextPos = -1;
  let steps = 0;

  while (steps++ < 100) {
    if (pos >= pkt.length) return null;
    const len = pkt[pos];
    if (len === 0) {
      pos++;
      if (firstNextPos === -1) firstNextPos = pos;
      break;
    }
    if ((len & 0xc0) === 0xc0) {
      if (pos + 1 >= pkt.length || ptrDepth >= 10) return null;
      const ptr = ((len & 0x3f) << 8) | pkt[pos + 1];
      if (ptr < 12 || ptr >= pkt.length) return null;
      if (firstNextPos === -1) firstNextPos = pos + 2;
      pos = ptr;
      ptrDepth++;
      continue;
    }
    if (len > 63) return null;
    pos++;
    if (pos + len > pkt.length) return null;
    const labelBytes = pkt.subarray(pos, pos + len);
    // 快速字符合法性检查（允许 ASCII 字符）
    for (let i = 0; i < labelBytes.length; i++) {
      const c = labelBytes[i];
      if (c < 32 || c === 127) return null;
    }
    nameLabels.push(decoder.decode(labelBytes));
    pos += len;
  }
  if (firstNextPos === -1 || steps >= 100) return null;

  const qname = nameLabels.join('.').toLowerCase();
  if (firstNextPos + 4 > pkt.length) return null;
  const qtype = (pkt[firstNextPos] << 8) | pkt[firstNextPos + 1];
  const qclass = (pkt[firstNextPos + 2] << 8) | pkt[firstNextPos + 3];
  if (qclass !== 1) return null;

  // 解析 EDNS（OPT RR）
  let arPos = firstNextPos + 4;
  const arCount = (pkt[10] << 8) | pkt[11];
  let doFlag = 0;
  for (let i = 0; i < arCount; i++) {
    // 快速跳过 RR 的 NAME（可能压缩）
    let rrPos = arPos;
    if (rrPos >= pkt.length) break;
    if (pkt[rrPos] === 0) {
      rrPos++;
    } else if ((pkt[rrPos] & 0xc0) === 0xc0) {
      rrPos += 2;
    } else {
      // 普通域名，简单跳过（不解析）
      while (rrPos < pkt.length) {
        const l = pkt[rrPos++];
        if (l === 0) break;
        rrPos += l;
      }
    }
    if (rrPos + 10 > pkt.length) break;
    const type = (pkt[rrPos] << 8) | pkt[rrPos + 1];
    const rdlen = (pkt[rrPos + 8] << 8) | pkt[rrPos + 9];
    if (type === 41) {
      const ttl = (pkt[rrPos + 4] << 24) | (pkt[rrPos + 5] << 16) | (pkt[rrPos + 6] << 8) | pkt[rrPos + 7];
      doFlag = (ttl & 0x8000) ? 1 : 0;
    }
    arPos = rrPos + 10 + rdlen;
  }
  return { qname, qtype, doFlag };
}

// ==================== TTL 解析（高性能版）====================

/**
 * 从 DNS 响应中提取最小 TTL
 */
function parseMinTTL(buffer) {
  const pkt = new Uint8Array(buffer);
  if (pkt.length < 12) return CACHE_TTL_MIN;
  const qdCount = (pkt[4] << 8) | pkt[5];
  const anCount = (pkt[6] << 8) | pkt[7];
  const nsCount = (pkt[8] << 8) | pkt[9];
  let pos = 12;

  // 跳过 Question 节
  for (let i = 0; i < qdCount; i++) {
    // 跳过域名（压缩或普通）
    while (pos < pkt.length) {
      const len = pkt[pos];
      if (len === 0) { pos++; break; }
      if ((len & 0xc0) === 0xc0) { pos += 2; break; }
      pos += len + 1;
    }
    pos += 4; // QTYPE + QCLASS
  }

  let minTTL = Infinity;

  // 遍历资源记录
  function processRRs(count) {
    for (let i = 0; i < count; i++) {
      if (pos + 12 > pkt.length) break;
      // 跳过域名
      if ((pkt[pos] & 0xc0) === 0xc0) {
        pos += 2;
      } else {
        while (pos < pkt.length) {
          const len = pkt[pos++];
          if (len === 0) break;
          pos += len;
        }
      }
      if (pos + 10 > pkt.length) break;
      const ttl = (pkt[pos + 4] << 24) | (pkt[pos + 5] << 16) | (pkt[pos + 6] << 8) | pkt[pos + 7];
      const rdlen = (pkt[pos + 8] << 8) | pkt[pos + 9];
      if (ttl < minTTL) minTTL = ttl;
      pos += 10 + rdlen;
    }
  }

  processRRs(anCount);
  processRRs(nsCount);

  if (!isFinite(minTTL)) minTTL = CACHE_TTL_MIN;
  return Math.min(CACHE_TTL_MAX, Math.max(CACHE_TTL_MIN, minTTL));
}

// ==================== ECS 注入（高性能版）====================

/**
 * 在 DNS 请求中注入 EDNS Client Subnet
 */
function injectECS(buffer, clientIP, prefix) {
  const pkt = new Uint8Array(buffer);
  if (pkt.length < 12) return buffer;

  // 跳过 Question 节
  let pos = 12;
  const qdCount = (pkt[4] << 8) | pkt[5];
  for (let i = 0; i < qdCount; i++) {
    while (pos < pkt.length) {
      const l = pkt[pos];
      if (l === 0) { pos++; break; }
      if ((l & 0xc0) === 0xc0) { pos += 2; break; }
      pos += l + 1;
    }
    pos += 4;
  }

  // 查找现有 OPT RR
  let arCount = (pkt[10] << 8) | pkt[11];
  let optStart = -1, optEnd = -1;
  let cursor = pos;
  for (let i = 0; i < arCount; i++) {
    if (cursor + 11 > pkt.length) break;
    let rrPos = cursor;
    if ((pkt[rrPos] & 0xc0) === 0xc0) {
      rrPos += 2;
    } else {
      while (rrPos < pkt.length) {
        const l = pkt[rrPos++];
        if (l === 0) break;
        rrPos += l;
      }
    }
    if (rrPos + 10 > pkt.length) break;
    const type = (pkt[rrPos] << 8) | pkt[rrPos + 1];
    const rdlen = (pkt[rrPos + 8] << 8) | pkt[rrPos + 9];
    if (type === 41) {
      optStart = cursor;
      optEnd = rrPos + 10 + rdlen;
      break;
    }
    cursor = rrPos + 10 + rdlen;
  }

  // 准备 ECS 数据
  const ipBytes = ipToBytes(clientIP);
  if (!ipBytes) return buffer;
  const isV6 = ipBytes.length === 16;
  const actualPrefix = prefix ?? (isV6 ? ECS_CONFIG.ipv6Prefix : ECS_CONFIG.ipv4Prefix);
  const addr = applyPrefixMask(ipBytes, actualPrefix).subarray(0, Math.ceil(actualPrefix / 8));

  const ecsOptionLen = 2 + 1 + 1 + addr.length; // CODE(2) + LEN(2) + FAMILY(2) + SOURCE(1) + SCOPE(1) + ADDR
  const ecsOption = new Uint8Array(4 + ecsOptionLen);
  ecsOption[0] = 0; ecsOption[1] = 8;                 // OPTION-CODE = 8
  ecsOption[2] = ecsOptionLen >> 8;                   // OPTION-LENGTH
  ecsOption[3] = ecsOptionLen & 0xff;
  ecsOption[4] = 0;                                   // FAMILY 高字节
  ecsOption[5] = isV6 ? 2 : 1;                        // FAMILY 低字节
  ecsOption[6] = actualPrefix;                        // SOURCE PREFIX-LENGTH
  ecsOption[7] = 0;                                   // SCOPE PREFIX-LENGTH
  ecsOption.set(addr, 8);

  // 如果存在 OPT RR，替换；否则新增
  if (optStart !== -1) {
    const oldOpt = pkt.subarray(optStart, optEnd);
    // 遍历旧选项，收集非 ECS 选项
    const otherOpts = [];
    let offset = 11;
    while (offset + 4 <= oldOpt.length) {
      const code = (oldOpt[offset] << 8) | oldOpt[offset + 1];
      const len = (oldOpt[offset + 2] << 8) | oldOpt[offset + 3];
      if (code !== 8) {
        otherOpts.push(oldOpt.subarray(offset, offset + 4 + len));
      }
      offset += 4 + len;
    }
    // 计算新 OPT RR 总长度
    let newOptLen = 11 + ecsOption.length;
    for (const opt of otherOpts) newOptLen += opt.length;
    const newOpt = new Uint8Array(newOptLen);
    newOpt.set(oldOpt.subarray(0, 11), 0);  // 复制 OPT RR 头部
    newOpt[9] = (newOptLen - 11) >> 8;
    newOpt[10] = (newOptLen - 11) & 0xff;
    let wpos = 11;
    newOpt.set(ecsOption, wpos);
    wpos += ecsOption.length;
    for (const opt of otherOpts) {
      newOpt.set(opt, wpos);
      wpos += opt.length;
    }
    // 拼接最终报文
    const newPkt = new Uint8Array(pkt.length - (optEnd - optStart) + newOpt.length);
    newPkt.set(pkt.subarray(0, optStart), 0);
    newPkt.set(newOpt, optStart);
    newPkt.set(pkt.subarray(optEnd), optStart + newOpt.length);
    return newPkt.buffer;
  } else {
    // 新增 OPT RR
    const optRR = new Uint8Array(11 + ecsOption.length);
    optRR[0] = optRR[1] = 0;      // NAME 为 0
    optRR[2] = 0; optRR[3] = 41;  // TYPE = 41
    optRR[4] = 0; optRR[5] = 16;  // CLASS = 16 (UDP 最大尺寸)
    optRR[6] = 0; optRR[7] = 0;   // TTL = 0
    optRR[8] = 0; optRR[9] = 0;   // RDLEN 占位
    optRR[10] = 0;
    const rdlen = ecsOption.length;
    optRR[9] = rdlen >> 8;
    optRR[10] = rdlen & 0xff;
    optRR.set(ecsOption, 11);
    const newPkt = new Uint8Array(pkt.length + optRR.length);
    newPkt.set(pkt, 0);
    newPkt.set(optRR, pkt.length);
    // 更新 ARCOUNT
    const newArCount = arCount + 1;
    newPkt[10] = newArCount >> 8;
    newPkt[11] = newArCount & 0xff;
    return newPkt.buffer;
  }
}

// ==================== 主处理函数 ====================

async function handleDoH(request, env, ctx) {
  try {
    // 获取客户端 IP
    let clientIP = request.headers.get('EO-Connecting-IP') || request.headers.get('CF-Connecting-IP') || '1.1.0.0';

    // 读取 DNS 报文
    let queryBuffer;
    if (request.method === 'POST') {
      queryBuffer = await request.arrayBuffer();
    } else {
      const dnsParam = new URL(request.url).searchParams.get('dns');
      if (!dnsParam) return new Response('Bad Request', { status: 400 });
      queryBuffer = base64UrlToUint8Array(dnsParam).buffer;
    }

    const parsed = parseDNSQuery(queryBuffer);
    if (!parsed) return new Response('Bad Request', { status: 400 });

    // 构建缓存键
    const isV6 = clientIP.includes(':');
    const prefix = isV6 ? ECS_CONFIG.ipv6Prefix : ECS_CONFIG.ipv4Prefix;
    const subnetKey = getSubnetKey(clientIP, prefix);
    const cacheKey = `https://cache.local/${parsed.qname}/${parsed.qtype}/${parsed.doFlag}/${subnetKey}`;

    // 缓存读取
    const cache = caches.default;
    let cached;
    try {
      cached = await cache.match(cacheKey);
    } catch (err) {
      if (err.status !== 504) console.error('Cache match error:', err);
    }
    if (cached) return cached;

    // 请求合并
    if (inflight.has(cacheKey)) return inflight.get(cacheKey);

    const promise = (async () => {
      // 注入 ECS 并请求上游
      const finalQuery = injectECS(queryBuffer, clientIP, prefix);
      const controller = new AbortController();
      const timeoutId = setTimeout(() => controller.abort(), UPSTREAM_TIMEOUT);
      let upstreamRes;
      try {
        upstreamRes = await fetch(UPSTREAM_URL, {
          method: 'POST',
          headers: {
            'content-type': 'application/dns-message',
            accept: 'application/dns-message',
          },
          body: finalQuery,
          signal: controller.signal,
        });
      } finally {
        clearTimeout(timeoutId);
      }

      if (!upstreamRes.ok) {
        return new Response('Upstream DNS error', { status: 502 });
      }

      const responseBody = await upstreamRes.arrayBuffer();
      const ttl = parseMinTTL(responseBody);

      const response = new Response(responseBody, {
        headers: {
          'content-type': 'application/dns-message',
          'cache-control': `max-age=${ttl}`,
        },
      });

      if (ctx?.waitUntil) {
        ctx.waitUntil(cache.put(cacheKey, response.clone()));
      }
      return response;
    })();

    inflight.set(cacheKey, promise);
    try {
      return await promise;
    } finally {
      inflight.delete(cacheKey);
    }
  } catch (err) {
    console.error('DoH handler error:', err);
    return new Response('Internal Server Error', { status: 500 });
  }
}

// ==================== HTTP 路由 ====================

async function handleRequest(request, env, ctx) {
  const url = new URL(request.url);
  if (url.pathname === '/') {
    return new Response(
      'Welcome to DNS Proxy Gateway\n\nEndpoints:\n- /dns-query\n- /resolve',
      { headers: { 'content-type': 'text/plain; charset=utf-8' } }
    );
  }
  if (url.pathname === '/dns-query') {
    return handleDoH(request, env, ctx);
  }
  // 其他请求（如 /resolve）直接转发
  const upstreamUrl = new URL('https://dns.google' + url.pathname + url.search);
  return fetch(upstreamUrl, {
    method: request.method,
    headers: request.headers,
  });
}

addEventListener('fetch', event => {
  event.respondWith(handleRequest(event.request, {}, event));
});