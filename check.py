import mmap

recs = []
f = open("samples", "r")
# memory-map the file, size 0 means whole file
mm = mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ)
line = mm.readline().decode("utf8").strip()

while line != "":
  comps = line.split(" ")
  line = mm.readline().decode("utf8").strip()
  # print(comps)
  #print(comps)
  if comps[0] == "":
    continue
  try:
    data = [int(x) for x in comps[:-1]]
    recs.append(data)
  except:
    pass
  comps = None

  #print(data)

print("read")
mm.close()
recs.sort(key=lambda x: x[0])

print("loaded")
group = []
for rec in recs:
  if rec[1] == 1:
    # print("epoch")
    known = {}
    duplicate = None
    an = None
    for index, item in enumerate(group):
      if item[2] == 0:
        continue
      if item[3] not in known:
        known[item[3]] = (index, item)
      elif known[item[3]][1][4] != item[4]:
        duplicate = (index, item)
        an = known[item[3]]
        break
    if duplicate:
      print("duplicate {} {}".format(duplicate, an))
    group.clear()
  else:
    group.append(rec)
