from pathlib import Path
p=Path("scripts/freed/angle_10_relative_index.py")
s=p.read_text(encoding="utf-8")
s=s.replace("datetime.datetime.utcnow().strftime(", "datetime.datetime.now(datetime.UTC).strftime(")
p.write_text(s, encoding="utf-8")
