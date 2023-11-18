f = open("output").read()
lines = f.split("\n")
num = 0
prev = 0
for line in lines:
  if line:
    num = int(line)
    prev = num
    if num - prev > 1:
      print("Error")

print("Done\n")

