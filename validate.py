f = open("output").read()
lines = f.split("\n")
num = 0
prev = 0
for lineno, line in enumerate(lines):
  if line and "CHANGE" in line:
    comps = line.split(" ")
    num = int(comps[1])
    if (num - prev) > 1:
      print("Error {} @ line {}".format(num - prev, lineno))
    if num == prev:
      print("duplicate @ line {}".format(lineno))
    prev = num
    

print("Done\n")

