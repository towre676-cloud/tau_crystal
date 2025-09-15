import io,json,sys,jsonschema
schema=json.load(io.open("docs/schemas/experimental.json","r",encoding="utf-8"))
for f in sys.argv[1:]:
    inst=json.load(io.open(f,"r",encoding="utf-8"))
    jsonschema.validate(inst,schema)
    print("✓",f)
