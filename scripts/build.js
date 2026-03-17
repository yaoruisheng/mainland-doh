const fs = require('fs');
const coreLogic = process.env.CORE_LOGIC;

if (!coreLogic) {
    console.error("Error: Missing CORE_LOGIC Secret in Environment");
    process.exit(1);
}

function expandIPv6(ip) {
    const parts = ip.includes('::') ? (() => {
        const [l, r] = ip.split('::');
        const lp = l ? l.split(':') : [], rp = r ? r.split(':') : [];
        return [...lp, ...Array(8 - (lp.length + rp.length)).fill('0'), ...rp];
    })() : ip.split(':');
    return parts.map(p => p.padStart(4, '0')).join('');
}

const v4Processor = {
    toRange: (cidr) => {
        const [ip, mask] = cidr.split('/');
        const m = parseInt(mask);
        const octets = ip.split('.').map(Number);
        const start = (octets[0] * 16777216) + (octets[1] * 65536) + (octets[2] * 256) + octets[3];
        return [start, start + Math.pow(2, 32 - m) - 1];
    },
    merge: (ranges) => {
        if (!ranges.length) return [];
        ranges.sort((a, b) => a[0] - b[0]);
        const res = [ranges[0]];
        for (let i = 1; i < ranges.length; i++) {
            let last = res[res.length - 1];
            if (ranges[i][0] <= last[1] + 1) last[1] = Math.max(last[1], ranges[i][1]);
            else res.push(ranges[i]);
        }
        return res.flat();
    }
};

const v6Processor = {
    toRange: (cidr) => {
        const [ip, mask] = cidr.split('/');
        const m = Math.min(parseInt(mask), 64); // 仅处理前 64 位前缀
        const start = BigInt("0x" + expandIPv6(ip).substring(0, 16));
        const size = 1n << BigInt(64 - m);
        return [start, start + size - 1n];
    },
    merge: (ranges) => {
        if (!ranges.length) return [];
        ranges.sort((a, b) => (a[0] > b[0] ? 1 : -1));
        const res = [ranges[0]];
        for (let i = 1; i < ranges.length; i++) {
            let last = res[res.length - 1];
            if (ranges[i][0] <= last[1] + 1n) last[1] = ranges[i][1] > last[1] ? ranges[i][1] : last[1];
            else res.push(ranges[i]);
        }
        return res.flat();
    }
};

const v4Final = v4Processor.merge(fs.readFileSync('cn_ipv4.txt', 'utf8').split('\n').filter(Boolean).map(v4Processor.toRange));
const v6Final = v6Processor.merge(fs.readFileSync('cn_ipv6.txt', 'utf8').split('\n').filter(Boolean).map(v6Processor.toRange));

const finalScript = `/** Generated on ${new Date().toISOString()} **/
const V4 = new Uint32Array([${v4Final.join(',')}]);
const V6 = BigUint64Array.from([${v6Final.map(n => n + 'n').join(',')}]);
${coreLogic}`;

fs.writeFileSync('index.js', finalScript);
console.log("Build Complete: index.js generated with optimized IP tables.");
