import sys
from pathlib import Path

SCRATCH = Path(r"D:\Dev\pequalnp-20261124-agy\scratch")

EXACT_CHILD1_STMT = """∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.FanInTwo C →
    C.gates.countP (fun g => !(g.op.eval [false])) ≤ 15 →
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠
      (fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x"""


def split_imports(text: str):
    imports = []
    body = []
    in_header = True
    for line in text.splitlines():
        if in_header and (line.startswith("import ") or line.strip() == ""):
            if line.startswith("import "):
                imp = line.strip()
                if imp not in ("import ProveLowBin", "import NoSevenU2"):
                    imports.append(imp)
        else:
            in_header = False
            body.append(line)
    return imports, "\n".join(body)


def strip_outer_namespace(body: str, ns: str) -> str:
    lines = body.splitlines()
    start = 0
    while start < len(lines) and lines[start].strip() == "":
        start += 1
    if start < len(lines) and lines[start].strip() == f"namespace {ns}":
        start += 1
    end = len(lines)
    while end > start and lines[end - 1].strip() == "":
        end -= 1
    if end > start and lines[end - 1].strip() == f"end {ns}":
        end -= 1
    return "\n".join(lines[start:end])


def build_merged(mod_name: str, out_path: Path, stmt: str = EXACT_CHILD1_STMT):
    p1_txt = (SCRATCH / "ProveLowBin.lean").read_text(encoding="utf-8")
    p2_txt = (SCRATCH / "NoSevenU2.lean").read_text(encoding="utf-8")
    p3_txt = (SCRATCH / "TreeExtract.lean").read_text(encoding="utf-8")

    i1, b1 = split_imports(p1_txt)
    i2, b2 = split_imports(p2_txt)
    i3, b3 = split_imports(p3_txt)

    all_imports = sorted(set(i1 + i2 + i3))

    b1_inner = strip_outer_namespace(b1, "PEqualNP.Outside.ProveLowBin")
    b1_inner = b1_inner.replace("PEqualNP.Outside.ProveLowBin.", f"PEqualNP.Outside.{mod_name}.")
    b3_fixed = b3.replace("open PEqualNP.Outside.ProveLowBin\n", "")
    b3_fixed = b3_fixed.replace("PEqualNP.Outside.ProveLowBin.", f"PEqualNP.Outside.{mod_name}.")

    out = []
    out.extend(all_imports)
    out.append("")
    out.append(f"namespace PEqualNP.Outside.{mod_name}")
    out.append("")
    out.append(b1_inner)
    out.append("")
    out.append(b2)
    out.append("")
    out.append(b3_fixed)
    out.append("")
    out.append(f"end PEqualNP.Outside.{mod_name}")
    out.append("")
    out.append(f"theorem PEqualNP.Outside.{mod_name} :")
    out.append(f"    {stmt} :=")
    out.append(f"  PEqualNP.Outside.{mod_name}.TreeExtract.p10_ge_sixteen_bin")
    out.append("")

    final_txt = "\n".join(out)
    out_path.write_text(final_txt, encoding="utf-8")
    print(f"Wrote {out_path} ({len(final_txt.encode('utf-8'))} bytes, {len(out)} lines)")


if __name__ == "__main__":
    mod = sys.argv[1] if len(sys.argv) > 1 else "P10Ge16Bin"
    out_file = Path(sys.argv[2]) if len(sys.argv) > 2 else (SCRATCH / f"{mod}.lean")
    stmt_file = Path(sys.argv[3]) if len(sys.argv) > 3 else None
    stmt = stmt_file.read_text(encoding="utf-8").strip() if stmt_file else EXACT_CHILD1_STMT
    build_merged(mod, out_file, stmt)
