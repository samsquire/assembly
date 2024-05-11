recs = []
cols = {
  "r": [],
  "w": []
}

for line in open("accesslog").read().split("\n"):
  comps = line.split(" ")
  #print(comps)
  if comps[0] == "":
    continue
  try:
    cols[comps[0]].append(" ".join(comps[1:]))
  except:
    pass
  comps = None
  #print(data)

print("read")

reads = set(cols["r"])
writes = set(cols["w"])
print("setted")
diff = writes - reads
print(len(diff))
for item in diff:
  print(item)