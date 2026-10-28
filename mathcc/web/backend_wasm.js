/* In-browser backend: runs mathcc.wasm in a Web Worker (WASI shim, no server).
   Provides window.MATHCC_BACKEND(path, body) with the same JSON as web/server.py. */
(function () {
  const WORKER_SRC = `
  let mod = null;
  class Exit { constructor(c){ this.code = c; } }
  function run(args, stdinBytes) {
    const out = [], err = []; let inst, mem, pos = 0;
    const dv = () => new DataView(mem.buffer), u8 = () => new Uint8Array(mem.buffer);
    const enc = new TextEncoder(), argv = args.map(a => enc.encode(a + '\\0'));
    const imp = {};
    const F = {
      args_sizes_get(c, s){ dv().setUint32(c, argv.length, true); dv().setUint32(s, argv.reduce((a,b)=>a+b.length,0), true); return 0; },
      args_get(av, buf){ let p = buf; argv.forEach((a,i) => { dv().setUint32(av + 4*i, p, true); u8().set(a, p); p += a.length; }); return 0; },
      environ_sizes_get(c, s){ dv().setUint32(c, 0, true); dv().setUint32(s, 0, true); return 0; },
      environ_get(){ return 0; },
      clock_time_get(id, prec, outp){ const t = id === 0 ? BigInt(Math.round(Date.now()*1e6)) : BigInt(Math.round(performance.now()*1e6)); dv().setBigUint64(outp, t, true); return 0; },
      clock_res_get(id, outp){ dv().setBigUint64(outp, 1000n, true); return 0; },
      random_get(p, n){ crypto.getRandomValues(u8().subarray(p, p+n)); return 0; },
      proc_exit(c){ throw new Exit(c); },
      fd_close(){ return 0; },
      fd_fdstat_get(fd, p){ if (fd > 2) return 8; const v = dv(); v.setUint8(p, 2); v.setUint16(p+2, 0, true); v.setBigUint64(p+8, 0xFFFFFFFFFFFFFFFFn, true); v.setBigUint64(p+16, 0n, true); return 0; },
      fd_prestat_get(){ return 8; }, fd_prestat_dir_name(){ return 8; },
      fd_seek(){ return 70; },
      fd_write(fd, iovs, n, nw){
        const v = dv(); let total = 0;
        for (let i = 0; i < n; i++) { const p = v.getUint32(iovs+8*i, true), l = v.getUint32(iovs+8*i+4, true); (fd === 2 ? err : out).push(u8().slice(p, p+l)); total += l; }
        v.setUint32(nw, total, true); return 0;
      },
      fd_read(fd, iovs, n, nr){
        if (fd !== 0) return 8; const v = dv(); let total = 0;
        for (let i = 0; i < n; i++) { const p = v.getUint32(iovs+8*i, true), l = v.getUint32(iovs+8*i+4, true), k = Math.min(l, stdinBytes.length - pos); u8().set(stdinBytes.subarray(pos, pos+k), p); pos += k; total += k; if (k < l) break; }
        v.setUint32(nr, total, true); return 0;
      }
    };
    for (const i of WebAssembly.Module.imports(mod)) { (imp[i.module] = imp[i.module] || {})[i.name] = F[i.name] || (() => 52); }
    inst = new WebAssembly.Instance(mod, imp); mem = inst.exports.memory;
    let code = 0;
    try { inst.exports._start(); } catch (e) { if (e instanceof Exit) code = e.code; else throw e; }
    const dec = new TextDecoder(), join = a => { const t = a.reduce((s,x)=>s+x.length,0), r = new Uint8Array(t); let o = 0; a.forEach(x => { r.set(x, o); o += x.length; }); return dec.decode(r); };
    return { code, stdout: join(out), stderr: join(err) };
  }
  onmessage = async e => {
    const m = e.data;
    try {
      if (m.module) mod = m.module;
      const r = run(m.args, new TextEncoder().encode(m.stdin || ''));
      postMessage({ id: m.id, ok: true, result: r });
    } catch (ex) { postMessage({ id: m.id, ok: false, error: String(ex) }); }
  };`;

  function parseCompile(text) {
    const res = { inputs: '', outputs: [], evaluation: [], cert: null, verify: [], bench: [], wrote: null };
    let cur = null, section = null, tac = false;
    for (const line of text.split('\n')) {
      if (line.startsWith('mathcc |')) { res.inputs = line.split('inputs:').pop().trim(); continue; }
      let m = line.match(/^\[(.+)\]$/);
      if (m) { cur = { name: m[1], original: '', simplified: '', guards: [], proven: 0, runtimeGuards: 0, skipped: '', size: {}, stability: '', tac: [], result: '', noGuard: true, why: [], skips: [] };
               res.outputs.push(cur); section = 'out'; tac = false; continue; }
      if (line.startsWith('evaluation:')) { section = 'eval'; cur = null; continue; }
      if (line.startsWith('certificate check')) { section = 'cert'; cur = null; res.cert = { notes: [] }; continue; }
      if (line.startsWith('end-to-end verification')) { section = 'verify'; cur = null; continue; }
      if (line.startsWith('benchmark')) { section = 'bench'; cur = null; continue; }
      if (section === 'out' && cur) {
        if (line.startsWith('  original  :')) cur.original = line.slice(line.indexOf(':') + 1).trim();
        else if (line.startsWith('  simplified:')) cur.simplified = line.slice(line.indexOf(':') + 1).trim();
        else if (line.startsWith('  guards    :')) {
          const body = line.slice(line.indexOf(':') + 1).trim(); tac = false;
          let mm = body.match(/(\d+) side condition/); if (mm) cur.proven = +mm[1];
          mm = body.match(/^(\d+) runtime check/); if (mm) { cur.runtimeGuards = +mm[1]; cur.noGuard = false; }
        }
        else if (line.startsWith('              - ')) cur.guards.push(line.slice(line.indexOf('- ') + 2).trim());
        else if (line.startsWith('              (')) { const mm = line.match(/(\d+) more proven/); if (mm) cur.proven = +mm[1]; }
        else if (line.startsWith('  skipped   :')) cur.skipped = line.slice(line.indexOf(':') + 1).trim();
        else if (line.startsWith('  size      :')) {
          const mm = line.match(/DAG (\d+) -> (\d+) nodes ; VM (\d+) -> (\d+)/);
          if (mm) cur.size = { dagFrom: +mm[1], dagTo: +mm[2], vmFrom: +mm[3], vmTo: +mm[4] };
        }
        else if (line.startsWith('  stability:')) cur.stability = line.trim();
        else if (line.startsWith('  why:')) tac = false;
        else if (line.startsWith('    step|')) {
          const parts = line.trim().split('|'); const gs = [];
          if (parts.length > 4 && parts[4]) parts[4].split(';').forEach(g => { const i = g.lastIndexOf('~'); gs.push({ text: g.slice(0, i), status: { P: 'proven', R: 'runtime', I: 'ignored' }[g.slice(i + 1)] || 'runtime' }); });
          cur.why.push({ rule: parts[1], pre: parts[2], post: parts[3], guards: gs });
        }
        else if (line.startsWith('    skip|')) { const parts = line.trim().split('|'); cur.skips.push({ guard: parts[1], reason: parts.slice(2).join('|') }); }
        else if (line.startsWith('  three-address code')) tac = true;
        else if (tac && line.startsWith('    ')) {
          const s = line.trim();
          if (s.startsWith('result =')) cur.result = s; else if (!s.startsWith('guard ')) cur.tac.push(s);
        }
      } else if (section === 'eval' && line.startsWith('  ')) {
        const mm = line.match(/^\s+(\S+)\s+original = (\S+)\s+compiled = (\S+)\s*(\(.*\))?/);
        if (mm) res.evaluation.push({ name: mm[1], original: mm[2], compiled: mm[3], fallback: !!mm[4] });
      } else if (section === 'cert' && res.cert) {
        let mm = line.match(/rewrite steps: (\d+) \| verified: (\d+) \| too few valid samples: (\d+) \| FAILED: (\d+)/);
        if (mm) Object.assign(res.cert, { steps: +mm[1], verified: +mm[2], sparse: +mm[3], failed: +mm[4] });
        mm = line.match(/conditional steps: (\d+) \| guard proven necessary by a counterexample: (\d+)/);
        if (mm) Object.assign(res.cert, { conditional: +mm[1], witnessed: +mm[2] });
        if (line.startsWith('    ')) res.cert.notes.push(line.trim());
      } else if (section === 'verify' && line.startsWith('  ')) {
        const mm = line.match(/^\s+(\S+)\s+(\d+) points \| mismatches: (\d+) \| fallbacks used: (\d+) \| ill-conditioned skipped: (\d+)(?: \| e\.g\. (.*))?/);
        if (mm) res.verify.push({ name: mm[1], points: +mm[2], mismatches: +mm[3], fallbacks: +mm[4], skipped: +mm[5], example: mm[6] || '' });
      } else if (section === 'bench' && line.startsWith('  ')) {
        const mm = line.match(/^\s+(\S+)\s+tree-walk\s+([\d.]+) \| VM\(original\)\s+([\d.]+) \| VM\(compiled\+guards\)\s+([\d.]+) \| speed-up vs tree-walk ([\d.]+)x/);
        if (mm) res.bench.push({ name: mm[1], tree: +mm[2], vm: +mm[3], fast: +mm[4], speedup: +mm[5] });
      }
    }
    return res;
  }
  function parseDiscover(text) {
    const rules = [], head = [];
    for (const line of text.split('\n')) {
      const m = line.match(/^\s+(.+?)\s+-> (.+?)\s+\[(.+?)\]\s+(verified|UNVERIFIED)$/);
      if (m) rules.push({ lhs: m[1].trim(), rhs: m[2].trim(), cond: m[3], verified: m[4] === 'verified' });
      else if (line.trim() && !line.startsWith('new rules')) head.push(line);
    }
    return { summary: head, rules };
  }
  window.mathccParse = { parseCompile, parseDiscover };

  /* ---- worker plumbing ---- */
  let worker = null, nextId = 1; const pending = new Map(); let wasmModule = null;
  function ensureWorker() {
    if (worker) return Promise.resolve();
    const b64 = window.MATHCC_WASM_B64, bin = Uint8Array.from(atob(b64), c => c.charCodeAt(0));
    return WebAssembly.compile(bin).then(m => {
      wasmModule = m;
      worker = new Worker(URL.createObjectURL(new Blob([WORKER_SRC], { type: 'text/javascript' })));
      worker.onmessage = e => { const p = pending.get(e.data.id); if (!p) return; pending.delete(e.data.id); e.data.ok ? p.res(e.data.result) : p.rej(new Error(e.data.error)); };
    });
  }
  async function runMathcc(args, stdin) {
    await ensureWorker();
    return new Promise((res, rej) => {
      const id = nextId++; pending.set(id, { res, rej });
      worker.postMessage({ id, args: ['mathcc', ...args], stdin, module: wasmModule });
    });
  }

  async function compile(req) {
    const src = String(req.source || '');
    if (src.length > 20000) return { error: 'Program is too long (limit 20000 characters).' };
    let mode = req.mode; if (!['guarded', 'conservative', 'unsafe'].includes(mode)) mode = 'guarded';
    const args = ['-', '--mode', mode, '--tac', '--why'];
    if (req.stable) args.push('--stable');
    if (req.cert) args.push('--cert');
    const point = String(req.point || '').trim();
    if (point) {
      if (!/^[A-Za-z_][A-Za-z0-9_]*=-?[0-9.eE+-]+(,[A-Za-z_][A-Za-z0-9_]*=-?[0-9.eE+-]+)*$/.test(point)) return { error: 'Test point must look like x=2,y=0.5' };
      args.push('--set', point);
    }
    const verify = Math.max(0, Math.min(parseInt(req.verify || 0, 10) || 0, 200000));
    if (verify) args.push('--verify', String(verify));
    const bench = Math.max(0, Math.min(parseInt(req.bench || 0, 10) || 0, 5000000));
    if (bench) args.push('--bench', String(bench));
    args.push('--c-stdout');
    const r = await runMathcc(args, src);
    if (r.code !== 0) return { error: (r.stderr.trim() || r.stdout.trim() || 'compiler failed').replace(/^error: /, '') };
    const [report, c] = r.stdout.split('----C----\n');
    const res = parseCompile(report);
    res.mode = mode; res.c = c || ''; res.raw = report;
    return res;
  }
  async function discover() {
    const r = await runMathcc(['--discover'], '');
    return parseDiscover(r.stdout);
  }

  window.MATHCC_BACKEND = async function (path, body) {
    if (path === '/api/compile') return compile(body || {});
    if (path === '/api/discover') return discover();
    if (path === '/api/examples') return window.MATHCC_EXAMPLES || [];
    return { error: 'not found' };
  };
})();
