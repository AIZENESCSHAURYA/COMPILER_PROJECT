#!/usr/bin/env python3
"""Builds site/index.html: ONE self-contained file (UI + compiler as WebAssembly + examples).
No server, no install: open it in a browser, or host it on any static host (GitHub Pages, Netlify, ...).

    python3 web/build_site.py            # needs web/wasm/mathcc.wasm  (make wasm)
"""
import base64, json, os
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
html = open(os.path.join(HERE, "static", "index.html"), encoding="utf-8").read()
js = open(os.path.join(HERE, "backend_wasm.js"), encoding="utf-8").read()
wasm = open(os.path.join(HERE, "wasm", "mathcc.wasm"), "rb").read()
ex = [{"name": f[:-3], "source": open(os.path.join(ROOT, "examples", f), encoding="utf-8").read()}
      for f in sorted(os.listdir(os.path.join(ROOT, "examples"))) if f.endswith(".mc")]
assert "</script" not in js
inject = ("<script>window.MATHCC_WASM_B64=\"%s\";window.MATHCC_EXAMPLES=%s;</script>\n<script>\n%s\n</script>\n"
          % (base64.b64encode(wasm).decode(), json.dumps(ex).replace("</", "<\\/"), js))
assert "<script>" in html
html = html.replace("<script>", inject + "<script>", 1)
os.makedirs(os.path.join(ROOT, "site"), exist_ok=True)
out = os.path.join(ROOT, "site", "index.html")
open(out, "w", encoding="utf-8").write(html)
print("wrote %s (%d KB)" % (out, os.path.getsize(out) // 1024))
