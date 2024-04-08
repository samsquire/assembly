recs = []
for line in open("samples5").read().split("\n"):
  comps = line.split(" ")
  #print(comps)
  if comps[0] == "":
    continue
  try:
    data = [int(x) for x in comps]
    recs.append(data)
  except:
    pass
  comps = None
  #print(data)

recs.sort(key= lambda x: x[0])

print("loaded")
f = open("ordered", "w")
for item in recs:
  f.write("{}\n".format(" ".join(map(lambda x: str(x), item))))
f.close()