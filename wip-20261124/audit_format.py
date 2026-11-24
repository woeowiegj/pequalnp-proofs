import sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
lines = s.splitlines()
for i, line in enumerate(lines):
    if not line.startswith("import "):
        body = "\n".join(lines[i:])
        break
else:
    body = ""
for bad in ["import", '"', "#", "initialize", "macro", "syntax", "notation", "elab", "attribute", "native_decide", "sorry", "axiom"]:
    assert bad not in body, f"FORBIDDEN TOKEN: {bad}"
assert len(s.encode("utf-8")) <= 512 * 1024, "FILE TOO LARGE"
print("FORMAT AUDIT PASSED! bytes =", len(s.encode("utf-8")))
