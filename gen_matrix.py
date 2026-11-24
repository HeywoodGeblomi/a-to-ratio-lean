import json, sys
d = json.load(open(sys.argv[1]))
fmt = lambda m: "[" + ", ".join("[" + ", ".join(str(int(x)) for x in row) + "]" for row in m) + "]"
print("def M : IMat := " + fmt(d["M_plus"]))
print("def A : IMat := " + fmt(d["A"]))
