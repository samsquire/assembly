f1 = open("mailbox1").read()
lines1 = set(f1.split("\n"))
f2 = open("mailbox2").read()
lines2 = set(f2.split("\n"))

print(lines1)

from pprint import pprint
data = list(lines1 - lines2)
data.sort()
pprint(data)


