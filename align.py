

value = 64
size = 16

item = value
for i in range(0, 10):
  item += size
  print("{:x} {}".format(item, item))