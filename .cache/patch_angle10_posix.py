from pathlib import Path
p=Path("scripts/freed/angle_10_relative_index.py")
s=p.read_text(encoding="utf-8")
s=s.replace("print(str(out))", "print(out.as_posix())")
if "inputs": not in s:
    pass
s=s.replace("\"inputs\": inputs", "\"inputs\": {k:(Path(v).as_posix() if isinstance(v,str) else v) for k,v in inputs.items()}")
p.write_text(s, encoding="utf-8")
