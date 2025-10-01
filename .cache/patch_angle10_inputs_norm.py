from pathlib import Path
p=Path("scripts/freed/angle_10_relative_index.py")
s=p.read_text(encoding="utf-8")
if "print(out.as_posix())" not in s and "print(str(out))" in s:
    s=s.replace("print(str(out))","print(out.as_posix())")
if "inputs_norm=" not in s and "inputs={" in s:
    idx=s.find("inputs={")
    eol=s.find("\\n", idx)
    if eol!=-1:
        ins="\\ninputs_norm={k:(Path(v).as_posix() if isinstance(v,str) else v) for k,v in inputs.items()}\\n"
        s=s[:eol+1]+ins+s[eol+1:]
if "\"inputs\": inputs," in s:
    s=s.replace("\"inputs\": inputs,","\\\"inputs\\\": inputs_norm,")
elif "\"inputs\": inputs" in s:
    s=s.replace("\"inputs\": inputs","\\\"inputs\\\": inputs_norm")
p.write_text(s, encoding="utf-8")
