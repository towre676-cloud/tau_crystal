from pathlib import Path
p=Path("scripts/freed/angle_10_relative_index.py")
s=p.read_text(encoding="utf-8")
s=s.replace("for p in glob.glob(pat):", "for p in glob.glob(pat, recursive=True):")
p.write_text(s, encoding="utf-8")
