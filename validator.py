import sys
stack = []
# startreceive n thread
for line in sys.stdin:
  if "startreceive" in line:
    comps = line.strip().split(" ") 
    stack.append(("startreceive", comps[1], comps[2]))
  if "endreceive" in line:
    comps = line.strip().split(" ") 
    stack.append(("endreceive", comps[1], comps[2]))
template = {
  "thread": None,
  "mailbox": None
}

current = {
}

thread_stack = []
thread_stack = []
from pprint import pprint
for item in stack:
  if item[0] == "startreceive":
    other_thread = item[1]
    me = item[2]
    other_key = "other-{}".format(other_thread)
    me_key = "me-{}".format(me)
    if other_key not in current:
      current[other_key] = 0 
    else:
      current[other_key] = current[other_key] + 1
      
    if me_key not in current:
      current[me_key] = 0
    else:
      current[me_key] = current[me_key] + 1
    pprint(current)  

  if item[0] == "endreceive":
    other_thread = item[1]
    me = item[2]
    other_key = "other-{}".format(other_thread)
    me_key = "me-{}".format(me)

    if other_key not in current:
      current[other_key] = -1
    else:
      current[other_key] = current[other_key] - 1
    
    if me_key not in current:
      current[me_key] = -1
    else:
      current[me_key] = current[me_key] - 1
    pprint(current)  
    
