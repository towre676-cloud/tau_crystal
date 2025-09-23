import sys
print("executable:", sys.executable)
print("python:", sys.version.split()[0])
print("sys.path[0]:", sys.path[0])
mods = ["numpy","PIL","cv2","mediapipe","google.protobuf"]
ok = True
for m in mods:
    try:
        x = __import__(m)
        ver = getattr(x, "__version__", getattr(getattr(x,"__version__",""),"__version__", "n/a"))
        print(f"import {m}: OK ({ver})")
    except Exception as e:
        ok = False
        print(f"import {m}: FAIL -> {e}")
sys.exit(0 if ok else 1)
