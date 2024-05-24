import argparse

parser = argparse.ArgumentParser()

parser.add_argument('file')

args = parser.parse_args()

filedata = open(file).read()

class Parser:
  def __init__(self, text):
    self.text = text
    self.pos = 0
    self.last_char = " "

  def getchar(self):
    if self.pos + 1 == len(self.text):
      self.end = True
    else:
      self.last_char = self.text[self.pos]
      self.pos = self.pos + 1
    return self.last_char
    
  def gettoken(self):
    while self.last_char == " " or self.last_char == "\n":
      self.last_char = self.getchar()

