import io,json,sys
import jsonschema
schema=json.load(io.open("docs/schemas/experimental_fft_bootstrap.json","r",encoding="utf-8"))
for f in sys.argv[1:]:
  inst=json.load(io.open(f,"r",encoding="utf-8"))
  jsonschema.validate(inst,schema)
  print("✓",f)
