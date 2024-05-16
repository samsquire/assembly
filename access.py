recs = []
cols = {
  "r": [],
  "w": []
}
import mmap

recs = []
f = open("accesslog", "r")
# memory-map the file, size 0 means whole file
mm = mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ)
line = mm.readline().decode("utf8")

while line != "":
  comps = line.split(" ")
  line = mm.readline().decode("utf8")
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