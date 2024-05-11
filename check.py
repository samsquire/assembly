recs = []
for line in open("samples").read().split("\n"):
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

print("read")
recs.sort(key= lambda x: x[0])

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
    

