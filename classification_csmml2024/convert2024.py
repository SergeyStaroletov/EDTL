# EDTL patterns and LTL projections - simplifacator to obtain classes 
# @author getmanova
# @author star
# @author garanina


from enum import Enum
import unittest
  
#
# Enum-class for checking the type 
#
class TermType(Enum):
     BoolConst = 0
     BoolVar = 1
     And = 2
     Or = 3
     Impl = 4
     Not = 5
     W = 6
     U = 7
     G = 8
     F = 9

#
# Base abstract class 
#
class Term:
  pass

def printx(a) -> str:
  if (a.type() == TermType.BoolConst) or (a.type() == TermType.BoolVar) or (a.type() == TermType.Not): return a.printme()
  else: return "(" + a.printme() + ")" 

class Term:
  def __init__(self) -> None:
    pass
  def printme(self) -> str:
    pass
  def childcount(self) -> int:
    pass
  def left(self) -> Term:
    pass
  def right(self) -> Term:
    pass
  def type(self) -> TermType:
    pass
  def equals(self, other: Term) -> bool:
#    print('checking ')
#    print(self.printme() + ' vs ')
#    print(other.printme())
    return self.printme() == other.printme()
 
#
# Class for const/var terms 
#
class NoOpTerm(Term):
  def childcount(self) -> int:
    return 0
  def val(self):
    pass

#
# Class for one operation terms 
#
class OneOpTerm(Term):
  a: Term
  def __init__(self, a:Term) -> None:
    self.a = a
  def childcount(self) -> int:
    return 1
  def left(self) -> Term:
    return self.a

#
# Class for two operation terms 
#
class TwoOpTerm(Term):
  a: Term
  b: Term
  def __init__(self, a:Term, b:Term) -> None:
    self.a = a
    self.b = b
  def childcount(self) -> int:
    return 2
  def left(self) -> Term:
    return self.a
  def right(self) -> Term:
    return self.b

#
# Class for true/false
#
class BoolConstTerm(NoOpTerm):
  v: bool
  def __init__(self, boolVar:bool) -> None:
    self.v = boolVar
  def printme(self) -> str:
    if self.v: return "true"
    else: return "false"
  def type(self) -> TermType:
    return TermType.BoolConst
  def val(self) -> bool:
    return self.v

#
# Class for string-named variables
#
class BoolFreeTerm(NoOpTerm):
  v: str
  def __init__(self, freeFar:str) -> None:
    self.v = freeFar
  def printme(self) -> str:
    return self.v
  def type(self) -> TermType:
    return TermType.BoolVar
  def val(self) -> str: 
    return self.v

#
# Classes for particular LTL operations
#
class NotTerm(OneOpTerm):
  def type(self) -> TermType:
    return TermType.Not
  def printme(self) -> str:
    return  "¬" + printx(self.left())

class AndTerm(TwoOpTerm):
  def type(self) -> TermType:
    return TermType.And
  def printme(self) -> str:
    return printx(self.left()) + " ∧ " + printx(self.right())

class OrTerm(TwoOpTerm):
  def type(self) -> TermType:
    return TermType.Or
  def printme(self) -> str:
    return printx(self.left()) + " ∨ " + printx(self.right())

class ImplTerm(TwoOpTerm):
  def type(self)->TermType:
    return TermType.Impl
  def printme(self) -> str:
    return printx(self.left()) + " → " + printx(self.right())

class UTerm(TwoOpTerm):
  def type(self) -> TermType:
    return TermType.U
  def printme(self) -> str:
    return printx(self.left()) + " U " + printx(self.right())

class WTerm(TwoOpTerm):
  def type(self) -> TermType:
    return TermType.W
  def printme(self) -> str:
    return printx(self.left()) + " W " + printx(self.right())

class GTerm(OneOpTerm):
  def type(self) -> TermType:
    return TermType.G
  def printme(self) -> str:
    return "G " + printx(self.left())

class FTerm(OneOpTerm):
  def type(self) -> TermType:
    return TermType.F
  def printme(self) -> str:
    return "F " + printx(self.left())

#
# Routines for simplifications
#

# check a and not(b)/not(a) and b 
def CheckNotHelper(a:Term, b:Term):
  if (a.type() == TermType.BoolConst) and (b.type() == TermType.BoolConst):
    return a.val() != b.val()
  if (a.type() == TermType.Not) and (b.type() != TermType.Not):
    return a.left().equals(b)
  if (a.type() != TermType.Not) and (b.type() == TermType.Not):
    return b.left().equals(a)
  return False  


def DisSimpl(a:Term, b:Term):
  
  if ((a.type() == TermType.BoolConst) and (a.val() == True)) or \
  ((b.type() == TermType.BoolConst) and (b.val() == True)): 
    return BoolConstTerm(True)
  elif (a.type() == TermType.BoolConst) and (a.val() == False): return b
  elif (b.type() == TermType.BoolConst) and (b.val() == False): return a
  
  #a ∨ a = a
  elif (a.equals(b)):
    return a

  #a ∨ ¬a = a
  elif CheckNotHelper(a,b):
    return BoolConstTerm(True)  

  #a ∨ (b ∧ a) = a
  elif (b.type() == TermType.And) and (a.equals(b.right())):
    return a
  
  #a ∨ (a ∧ b) = a
  elif (b.type() == TermType.And) and (a.equals(b.left())):
    return a
  
  # a v (b ∧ ¬a) = a v b
  elif (b.type() == TermType.And) and CheckNotHelper(a, b.right()):
    return DisSimpl(a, b.left()) 
  
  # a v (¬a ∧ b) = a v b
  elif (b.type() == TermType.And) and CheckNotHelper(a, b.left()):
    return DisSimpl(a, b.right()) 
  
  # a v (b ∧ ¬a) = a v b
  elif (a.type() == TermType.And) and CheckNotHelper(b, a.right()):
    return DisSimpl(b, a.left()) 
  
  # a v (¬a ∧ b) = a v b
  elif (a.type() == TermType.And) and CheckNotHelper(b, a.left()):
    return DisSimpl(b, a.right()) 

  # (a ∧ ¬b) v (b ∧ a) 
  elif (b.type() == TermType.And) and (a.type() == TermType.And) and \
  ((a.left().equals(b.left()) and CheckNotHelper(a.right(),b.right())) or\
  (a.left().equals(b.right()) and CheckNotHelper(a.right(),b.left()))):
    return a.left() 

  # (a ∧ ¬b) v (b ∧ a)
  elif (b.type() == TermType.And) and (a.type() == TermType.And) and \
  ((a.right().equals(b.left()) and CheckNotHelper(a.left(),b.right())) or\
  (a.right().equals(b.right()) and CheckNotHelper(a.left(),b.left()))):
    return a.right() 

  # (a ∧ ¬b) v (c v (b ∧ a)) 
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and \
       (a.type() == TermType.And) and \
  ((a.right().equals(b.right().left()) and CheckNotHelper(a.left(),b.right().right())) or\
  (a.right().equals(b.right().right()) and CheckNotHelper(a.left(),b.right().left()))):
    return DisSimpl(a.right(), b.left()) 

  # (a ∧ ¬b) v (c v (b ∧ a)) 
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and\
       (a.type() == TermType.And) and \
  ((a.left().equals(b.right().left()) and CheckNotHelper(a.right(),b.right().right())) or\
  (a.left().equals(b.right().right()) and CheckNotHelper(a.right(),b.right().left()))):
    return DisSimpl(a.left(), b.left()) 
  
  # (a ∧ ¬b) v (b v (a ∧ c)) = (a ∧ ¬b) v b
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and\
       (a.type() == TermType.And) and CheckNotHelper(a.right(),b.left()) and\
       (a.left().equals(b.right().left()) or a.left().equals(b.right().right())):
    return DisSimpl(a.left(), b.left()) 

  # (a ∧ ¬b) v (b v (a ∧ c)) = (a ∧ ¬b) v b
  elif (b.type() == TermType.Or) and (b.left().type() == TermType.And) and\
       (a.type() == TermType.And) and CheckNotHelper(a.right(),b.right()) and\
       (a.left().equals(b.left().left()) or a.left().equals(b.left().right())):
    return DisSimpl(a.left(), b.right()) 

  # (a ∧ ¬b) v (b v (a ∧ c)) = (a ∧ ¬b) v b
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and\
       (a.type() == TermType.And) and CheckNotHelper(a.left(),b.left()) and\
       (a.right().equals(b.right().left()) or a.right().equals(b.right().right())):
    return DisSimpl(a.right(), b.left()) 

  # (a ∧ ¬b) v (b v (a ∧ c)) = (a ∧ ¬b) v b
  elif (b.type() == TermType.Or) and (b.left().type() == TermType.And) and\
       (a.type() == TermType.And) and CheckNotHelper(a.left(),b.right()) and\
       (a.right().equals(b.left().left()) or a.right().equals(b.left().right())):
    return DisSimpl(a.right(), b.right()) 

  #a ∨ (b ∧ (a ∨ c)) = a ∨ (b ∧ c)
  elif (b.type() == TermType.And) and (b.right().type() == TermType.Or) and \
  (b.right().left().equals(a)):
    return DisSimpl(a, ConSimpl(b.left(), b.right().right())) 
  
  # a v (b ∧ (c v a) = a ∨ (b ∧ c)
  elif (b.type() == TermType.And) and (b.right().type() == TermType.Or) and \
  (b.right().right().equals(a)):
    return DisSimpl(a, ConSimpl(b.left(), b.right().left())) 
  
  #a ∨ F(a ∨ b) = F(a ∨ b)
  elif (b.type() == TermType.F) and (b.left().type() == TermType.Or) and a.equals(b.left().left()):
    return b
  
  #a ∨ (b U a) = (b U a)
  elif (b.type() == TermType.U) and (b.right().equals(a)):
    return b
  
  #G(¬a) ∨ F(a) = true
  elif (a.type() == TermType.G) and (b.type() == TermType.F) and \
   CheckNotHelper(a.left(), b.left()):
    return BoolConstTerm(True)
  
  #a ∨ F(a) = F(a)
  elif (b.type() == TermType.F) and (b.left().equals(a)):
    return b
  
  # (G a) v a = G a
  elif (a.type() == TermType.G) and (a.left().equals(b)): return a
  
  #a ∨ (a ∨ b) = a V b | a ∨ (b ∨ a) = a ∨ b
  elif (b.type() == TermType.Or) and (b.left().equals(a) or b.right().equals(a)):
    return b
  
  #G(¬a) ∨ (F(a) ∨ с) = true
  elif (a.type() == TermType.G) and (b.type() == TermType.Or) and \
  (b.left().type() == TermType.F) and CheckNotHelper(a.left().left(), b.left().left()):
    return BoolConstTerm(True)
  
  #a ∨ (b U (a ∨ c)) = (b U (a ∨ c))
  elif (b.type() == TermType.U) and (b.right().type() == TermType.Or) and (b.right().left().equals(a)):
    return b  
  
  # a v (b ∧ (c v (c U a))) = a v (b ∧ (c U a)) = b ∧ (c U a)
  elif (b.type() == TermType.And) and    \
       (b.right().type() == TermType.Or) and  \
       (b.right().right().type() == TermType.U) and  \
       (b.right().right().right().equals(a)):
    return ConSimpl(b.left(),b.right().right())
   
  # a v (b v (c v a))) = b v (c v a) 
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.Or) and (b.right().right().equals(a)):
    return b  
  
  # inv v (¬trig v (inv ∧ rea)) = inv v !trig 
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and (b.right().left().equals(a) or b.right().right().equals(a)):
    return DisSimpl(a, b.left())  

  # a v (b ∧ ((c ∧ b) W a))) = (c ∧ b) W a 
  elif (b.type() == TermType.And) and    \
       (b.right().type() == TermType.W) and (b.right().left().type() == TermType.And) and\
       (b.right().right().equals(a)) and (b.right().left().right().equals(b.left())):
    return b.right()

  # a v (b W (a v c)) = b W (a v c)
  elif (b.type() == TermType.W) and (b.right().type() == TermType.Or) and (b.right().left().equals(a)):
    return b
  
  # a v (b W a) = b W a
  elif (b.type() == TermType.W) and (b.right().equals(a)):
    return b
  
  # a v (a W b) =  a v b
  elif (b.type() == TermType.W) and (b.left().equals(a)):
    return DisSimpl(a, b.right())
  
  # a v (b ∧ (a W (a v c)) = a | (b & (a | c)) = a | b&a | b&c 
  elif (b.type() == TermType.And) and (b.right().type() == TermType.W) and (b.right().left().equals(a)) and\
    (b.right().right().type() == TermType.Or) and (b.right().right().left().equals(a)):
    return DisSimpl(a, ConSimpl(b.left(), b.right().right()))
  
  # a v (b ∧ ((d ∧ a) W (a v (b ∧ c)))) = a v (b ∧ c) 
  elif (b.type() == TermType.And) and (b.right().type() == TermType.W) and\
       (b.right().left().type() == TermType.And) and (b.right().right().type() == TermType.Or) and (b.right().right().right().type() == TermType.And) and\
       (b.right().left().right().equals(a) or b.right().left().left().equals(a)) and b.right().right().left().equals(a) and b.right().right().right().left().equals(b.left()):
    return DisSimpl(a, b.left())
  
   #a v (b ∧ ((c ∧ b) W (a v (c ∧ b)))) = a v ((c ∧ b) W (a v (c ∧ b)))) = a | (b & (a | (b & c))) = a | (b & c)
  elif (b.type() == TermType.And) and (b.right().type() == TermType.W) and\
       (b.right().left().type() == TermType.And) and (b.right().right().type() == TermType.Or) and\
       (b.right().right().right().type() == TermType.And) and\
       (b.right().left().right().equals(b.left()) or b.right().left().left().equals(b.left())) and\
        b.right().right().left().equals(a) and\
       (b.right().right().right().left().equals(b.left()) or b.right().right().right().right().equals(b.left())):
    return DisSimpl(a, b.right().left())

   #a v (b ∧ ((c ∧ b) W a)) = (c ∧ b) W a
  elif (b.type() == TermType.And) and (b.right().type() == TermType.W) and\
       (b.right().left().type() == TermType.And) and\
       (b.right().left().right().equals(b.left()) or b.right().left().left().equals(b.left())) and\
        b.right().right().equals(a):
    return b.right()

   #a v (b ∧ ( b W (a v (c ∧ b)))) = a v (b W (a v (c ∧ b))))
  elif (b.type() == TermType.And) and (b.right().type() == TermType.W) and\
       (b.right().right().type() == TermType.Or) and\
       (b.right().right().right().type() == TermType.And) and\
        b.right().left().equals(b.left()) and\
        b.right().right().left().equals(a) and\
       (b.right().right().right().left().equals(b.left()) or b.right().right().right().right().equals(b.left())):
    return b.right()
  
   #a v (b ∧ (b W a) = a v (b W a)
  elif (b.type() == TermType.And) and (b.right().type() == TermType.W) and\
        b.right().left().equals(b.left()) and\
        b.right().right().equals(a):
    return b.right()
  
  # ¬a ∨ (¬b ∨ (a ∧ (¬c W (¬b ∨ d)))) = !a | (a & (!c W (d | !b))) 
  elif (b.type() == TermType.Or) and\
       (b.right().type() == TermType.And) and (b.right().right().type() == TermType.W) and\
       (b.right().right().right().type() == TermType.Or) and\
        CheckNotHelper(a, b.right().left()) and b.left().equals(b.right().right().right().left()):
    return ImplSimpl(b.right().left(),b.right().right())

# ¬a ∨ (¬b ∨ (a ∧ (c W ¬b)))
  elif (b.type() == TermType.Or) and\
       (b.right().type() == TermType.And) and (b.right().right().type() == TermType.W) and\
        CheckNotHelper(a, b.right().left()) and b.left().equals(b.right().right().right()):
    return ImplSimpl(b.right().left(),b.right().right())


# (a ∧ ¬b) ∨ (¬a ∨ (b ∧ (a W (¬a ∨ c)))) = true 
  elif (a.type() == TermType.And) and (b.type() == TermType.Or) and\
       (b.right().type() == TermType.And) and (b.right().right().type() == TermType.W) and\
       (b.right().right().right().type() == TermType.Or) and\
        CheckNotHelper(a.left(), b.left()) and a.left().equals(b.right().right().left()) and\
        CheckNotHelper(a.left(), b.right().right().right().left()) and\
        CheckNotHelper(a.right(), b.right().left()):
    return BoolConstTerm(True)


  else: 
    return OrTerm(a, b)



def ConSimpl(a:Term, b:Term):

  # ¬ (¬ a)
  if (a.type() == TermType.Not) and (a.left().type() == TermType.Not):
    a = a.left().left()
  if (b.type() == TermType.Not) and (b.left().type() == TermType.Not):
    b = b.left().left()
  
  if ((a.type() == TermType.BoolConst) and (a.val() == False)) or \
  ((b.type() == TermType.BoolConst) and (b.val() == False)): 
    return BoolConstTerm(False)
  elif (a.type() == TermType.BoolConst) and (a.val() == True): 
    return b
  elif (b.type() == TermType.BoolConst) and (b.val() == True): 
    return a
  elif (a.type() == TermType.Not) and (a.left().equals(b)): 
    return BoolConstTerm(False)
  elif (b.type() == TermType.Not) and (b.left().equals(a)): 
    return BoolConstTerm(False)

  # a ∧ a = a
  elif a.equals(b):
    return a  
  
  # a ∧ (a ∧ b) = a ∧ (b ∧ a)
  elif (b.type() == TermType.And) and (b.left().equals(a) or b.right().equals(a)): 
    return b
  
  # ¬a ∧ (a ∧ b) = false
  elif (b.type() == TermType.And) and (CheckNotHelper(b.left(), a) or CheckNotHelper(b.right(),a)): 
    return BoolConstTerm(False)
  
  # (¬ a) ∧ (a v b) = (¬ a) ∧ b
  elif (a.type() == TermType.Not) and (b.type() == TermType.Or) and (a.left().equals(b.left())): 
    return ConSimpl(a,b.right())

  # (¬ a) ∧ (b v a) = (¬ a) ∧ b
  elif (a.type() == TermType.Not) and (b.type() == TermType.Or) and (a.left().equals(b.right())): 
    return ConSimpl(a,b.left())  
  
  # a ∧ (a v b) = a
  elif (b.type() == TermType.Or) and (a.equals(b.left()) or a.equals(b.right())): 
    return a
  
  # (¬a) ∧ (b v (a ∧ c)) = (¬a) ∧ b
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and CheckNotHelper(a, (b.right().left())): 
    return ConSimpl(a,b.left())
  
  # a ∧ (¬a W b) = a ∧ b
  elif (b.type() == TermType.W) and CheckNotHelper(a, b.left()): 
    return ConSimpl(a, b.right())
  
  # a ∧ G(¬a)
  elif (b.type() == TermType.G) and CheckNotHelper(a, b.left()): 
    return BoolConstTerm(False)
  
  # a ∧ G (b ∧ ¬a) = false = ¬a ∧ G (a ∧ b)
  elif (b.type() == TermType.G) and (b.left().type() == TermType.And) and\
     (CheckNotHelper(a, b.left().right()) or CheckNotHelper(a, b.left().left())): 
    return BoolConstTerm(False)  

  # a ∧ G(a)
  elif (b.type() == TermType.G) and a.equals(b.left()): 
    return b
  
    # a ∧ G(b ∧ a)
  elif (b.type() == TermType.G) and (b.left().type() == TermType.And) and (a.equals(b.left().right()) or a.equals(b.left().left())): 
    return b

  # a ∧ ((b ∧ ¬a) W c) = a ∧ c
  elif (b.type() == TermType.W) and\
    (b.left().type() == TermType.And) and\
       CheckNotHelper(a, b.left().right()): 
    return ConSimpl(a, b.right())
  
  # ¬a ∧ ((a ∧ b) W (a ∧ c))) = false
  elif (b.type() == TermType.W) and\
    (b.left().type() == TermType.And) and (b.right().type() == TermType.And) and\
       CheckNotHelper(a, b.left().left()) and CheckNotHelper(a, b.right().left()): 
    return BoolConstTerm(False)

  # ¬a ∧ ((a ∧ b) W (c v (a ∧ d)))) = ¬a ∧ c
  elif (b.type() == TermType.W) and\
    (b.left().type() == TermType.And) and (b.right().type() == TermType.Or) and (b.right().right().type() == TermType.And) and\
       CheckNotHelper(a, b.left().left()) and CheckNotHelper(a, b.right().right().left()): 
    return ConSimpl(a,b.right().left())
  
  # ¬a ∧ ((a ∧ b) W c) = ¬a ∧ c
  elif (b.type() == TermType.W) and\
    (b.left().type() == TermType.And) and\
       CheckNotHelper(a, b.left().left()): 
    return ConSimpl(a,b.right())
  
  # a ∧ (b W (a v с)))
  elif (b.type() == TermType.W) and\
    (b.right().type() == TermType.Or) and\
       a.equals(b.right().left()): 
    return a
  
  # a ∧ ((a ∧ b) W (a ∧ c)) = (a ∧ b) W (a ∧ c)
  elif (b.type() == TermType.W) and\
    (b.right().type() == TermType.And) and (b.left().type() == TermType.And) and\
       (a.equals(b.left().left()) or a.equals(b.left().right())) and\
       (a.equals(b.right().left()) or a.equals(b.right().right())): 
    return b

  # a ∧ (a W a ∧ c)) = a W (a ∧ c)
  elif (b.type() == TermType.W) and\
    (b.right().type() == TermType.And) and\
       a.equals(b.left()) and\
       (a.equals(b.right().left()) or a.equals(b.right().right())): 
    return b

  # a ∧ (b W a)
  elif (b.type() == TermType.W) and a.equals(b.right()): 
    return a

  else: return AndTerm(a, b)


def No(a:Term):
  if (a.type() == TermType.BoolConst): 
    return BoolConstTerm(not a.val())
  else: 
    return NotTerm(a)


def ImplSimpl(a:Term, b:Term):
  if ((a.type() == TermType.BoolConst) or (b.type() == TermType.BoolConst)):
    return DisSimpl(No(a), b)
  
  # ¬a -> a = a
  elif CheckNotHelper(a, b): 
    return b
  
  # (¬rel ->)
  elif (a.type() == TermType.Not) and (a.left().type() == TermType.BoolVar):
        if (a.left().val() == 'rel'): return DisSimpl(a.left(),b)
  
  # ¬a -> a ∨ b = b
  elif ((b.type() == TermType.Or) and CheckNotHelper(a, b.left())): 
    return b

  # a -> a ∨ b = true
  elif ((b.type() == TermType.Or) and (a.equals(b.left()) or a.equals(b.right()))): 
    return BoolConstTerm(True)
  
  # a → (a ∧ b) = a → b  
  elif (b.type() == TermType.And) and a.equals(b.left()): 
    return ImplSimpl(a, b.right())

  elif (b.type() == TermType.And) and a.equals(b.right()): 
    return ImplSimpl(a, b.left())
      
  # a -> a = true
  elif a.equals(b): 
    return BoolConstTerm(True)

  # c∧¬a -> a 
  elif ((a.type() == TermType.And) and CheckNotHelper(a.right(),b)): 
    return ImplSimpl(a.left(), b)
  
  # c∧¬a -> a ∨ b
  elif ((a.type() == TermType.And) and (b.type() == TermType.Or) and CheckNotHelper(a.right(),b.left())): 
    return ImplSimpl(a.left(), b)
  
  # trig → (rel v (inv ∧ ¬trig)) = trig → rel 
  elif ((b.type() == TermType.Or) and (b.right().type() == TermType.And) and\
        (CheckNotHelper(a,b.right().left()) or CheckNotHelper(a,b.right().right()))): 
    return ImplSimpl(a, b.left())
  
  # ¬a -> F a
  elif ((b.type() == TermType.F) and CheckNotHelper(a, b.left())): 
    return b
  
  # a → (G ¬a)
  elif ((b.type() == TermType.G) and CheckNotHelper(a, b.left())): 
    return b.left()
  
  # c∧¬a -> F a
  elif ((a.type() == TermType.And) and (b.type() == TermType.F) and CheckNotHelper(a.right(),b.left())): 
    return ImplSimpl(a.left(), b)
  
  # ¬a -> F(a ∨ b)
  elif ((b.type() == TermType.F) and (b.left().type() == TermType.Or) and CheckNotHelper(a, b.left().left())): 
    return b
  
  # c∧¬a -> F(a ∨ b)
  elif (a.type() == TermType.And) and (b.type() == TermType.F) and (b.left().type() == TermType.Or) and \
        CheckNotHelper(a.right(), b.left().left()): 
    return ImplSimpl(a.left(), b)
  
  # ¬a -> b W a = b W a
  elif (b.type() == TermType.W) and CheckNotHelper(a, b.right()): 
    return b  
  
  # (a ∧ ¬b) → (b W c) = (a ∧ ¬b) → c
  elif (b.type() == TermType.W) and (a.type() == TermType.And) and\
    (CheckNotHelper(a.right(), b.left()) or CheckNotHelper(a.left(), b.left())):
    return ImplSimpl(a, b.right())    

  # a → (b ∧ ¬a) W c = a → c
  elif (b.type() == TermType.W) and (b.left().type() == TermType.And) and\
    (CheckNotHelper(a, b.left().left()) or CheckNotHelper(a, b.left().right())):
    return ImplSimpl(a, b.right())    


  # a → (b W (a ∧ b)) = a → b
  elif (b.type() == TermType.W) and (b.right().type() == TermType.And) and\
        (a.equals(b.right().left()) or a.equals(b.right().right())) and\
        (b.left().equals(b.right().left()) or b.left().equals(b.right().right())): 
    return ImplSimpl(a, b.left())    
  
  # ¬a -> b W (a ∨ c) = b W (a ∨ c) 
  elif (b.type() == TermType.W) and (b.right().type() == TermType.Or ) and\
        ((CheckNotHelper(a, b.right().left())) or CheckNotHelper(a, b.right().right()) or\
         a.equals(b.right().left()) or a.equals(b.right().right())):
    return b  

  # a -> b W (a ∨ c) = true
  elif (b.type() == TermType.W) and (b.right().type() == TermType.Or ) and\
         (a.equals(b.right().left()) or a.equals(b.right().right())):
    return BoolConstTerm(True)  

  # c∧¬a -> b W a = c -> b W a
  elif ((a.type() == TermType.And) and (b.type() == TermType.W) and CheckNotHelper(a.right(), b.right())): 
    return ImplSimpl(a.left(), b)  
  
  
  # c∧¬a -> b W (a ∨ d) = c -> b W (a ∨ d)
  elif ((a.type() == TermType.And) and (b.type() == TermType.W) and (b.right().type() == TermType.Or ) and\
        CheckNotHelper(a.right(), b.right().left())):
    return ImplSimpl(a.left(), b)  
  
  # a → (¬a W b) = a → b
  elif ((b.type() == TermType.W) and CheckNotHelper(a, b.left())): 
    return ImplSimpl(a, b.right())  
  
  # (a ∧ ¬b) → (c W (d W b)) = !a | (c W (d W b))
  elif ((a.type() == TermType.And) and (b.type() == TermType.W) and\
         (b.right().type() == TermType.W) and\
         CheckNotHelper(a.right(), b.right().right())): 
    return ImplSimpl(a.left(), b)


  # a → (b v (a ∧ (c W (b v (e ∧ d))))) = ¬a v (a ∧ (c W (b v (d ∧ e))))
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and\
       (b.right().right().type() == TermType.W) and (b.right().right().right().type() == TermType.Or) and\
         a.equals(b.right().left()) and b.left().equals(b.right().right().right().left()): 
    return ImplSimpl(a, b.right())

  # a → (b v (a ∧ (c W b))) = ¬a v (a ∧ (c W b))
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.And) and\
       (b.right().right().type() == TermType.W) and\
         a.equals(b.right().left()) and b.left().equals(b.right().right().right()): 
    return ImplSimpl(a, b.right())
  
  else:
    return ImplTerm(a, b)
  

def FutureSimpl(a:Term):
  if (a.type() == TermType.BoolConst): return a
  else: return FTerm(a)
  



def GloballySimpl(a:Term):
  if (a.type() == TermType.BoolConst): return a
  
  #G(F(a)) = GF(a)
  elif (a.type() == TermType.F): return GTerm(a)
  
  #G(G(a)) = G(a)
  elif (a.type() == TermType.G): return GloballySimpl(a.left())

  # G ((G a) v a) = G(a)
  elif (a.type() == TermType.Or) and (a.left().type() == TermType.G) and (a.left().left().equals(a.right())): return GloballySimpl(a.right())
  
  # G (¬a ∧ (b W a)) = G (¬a ∧ b)
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and \
    CheckNotHelper(a.left(),a.right().right()):
      return GloballySimpl(ConSimpl(a.left(), a.right().left()))
  
  # G (a W (b ∧ a)) = G a
  elif (a.type() == TermType.W) and (a.right().type() == TermType.And) and \
    (a.left().equals(a.right().right()) or a.left().equals(a.right().left())):
      return GloballySimpl(a.left())
  
  # G (a ∧ (¬b W b)) = G a
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and \
    CheckNotHelper(a.right().left(),a.right().right()):
      return GloballySimpl(a.left())

  # G (a ∧ ((b ∧ (¬ c)) W (c ∧ b))) = G (a ∧ b)
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().left().type() == TermType.And) and (a.right().right().type() == TermType.And) and \
    CheckNotHelper(a.right().left().right(),a.right().right().left()) and a.right().left().left().equals(a.right().right().right()):
      return GloballySimpl(ConSimpl(a.left(),a.right().left().left()))

  # G ((¬ a) ∧ F a) = false
  elif (a.type() == TermType.And) and (a.right().type() == TermType.F) and \
    CheckNotHelper(a.left(),a.right().left()):
      return BoolConstTerm(False)

  # G ((¬ a) ∧ F (a ∨ b)) = G ((¬ a) ∧ F b)
  elif (a.type() == TermType.And) and (a.right().type() == TermType.F) and (a.right().left().type() == TermType.Or) and \
    CheckNotHelper(a.left(),a.right().left().left()):
      return GloballySimpl(ConSimpl(a.left(), FutureSimpl(a.right().left().right())))

  # G ((¬ a) ∧ ( b W (a ∨ c))) = G ((¬ a) ∧ ( b W c ))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.Or) and \
    CheckNotHelper(a.left(),a.right().right().left()):
      return GloballySimpl(ConSimpl(a.left(), WeakUntilSimpl(a.right().left(),a.right().right().right())))
  
  # G ((¬ a) ∧ (b W (c ∧ (F a)))) = G ((¬ a) ∧ G b)
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
       (a.right().right().right().type() == TermType.F) and CheckNotHelper(a.left(),a.right().right().right().left()):
      return GloballySimpl(ConSimpl(a.left(), a.right().left()))

  # G ((¬ a) ∧ (b W (c ∧ (F (a v d))))) = G ((¬ a) ∧ (b W (c ∧ (F d))))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
       (a.right().right().right().type() == TermType.F) and (a.right().right().right().left().type() == TermType.Or) and CheckNotHelper(a.left(),a.right().right().right().left().left()):
      return GloballySimpl(ConSimpl(a.left(), WeakUntilSimpl(a.right().left(), ConSimpl(a.right().right().left(), FutureSimpl(a.right().right().right().left().right())))))

  # G ((a ∧ (¬ b)) W (b ∧ (G a))) = G (a)
  elif (a.type() == TermType.W) and (a.left().type() == TermType.And) and (a.right().type() == TermType.And) and (a.right().right().type() == TermType.G) and \
       a.left().left().equals(a.right().right().left()) and CheckNotHelper(a.left().right(),a.right().left()):
      return GloballySimpl(a.right().right())

  # G ((a ∧ (¬ b)) W (b ∧ a)) = G (a)
  elif (a.type() == TermType.W) and (a.left().type() == TermType.And) and (a.right().type() == TermType.And) and \
       a.left().left().equals(a.right().right()) and CheckNotHelper(a.left().right(),a.right().left()):
      return GloballySimpl(a.right().right())
  
  # G ((¬a) ∧ (b W ((¬a) ∧ c))) = G ((¬ a) ∧ ( b W c ))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
        (a.left().type() == TermType.Not) and (a.right().right().left().type() == TermType.Not) and \
         a.left().left().equals(a.right().right().left().left()):
      return GloballySimpl(ConSimpl(a.left(), WeakUntilSimpl(a.right().left(),a.right().right().right())))
  
  # G (¬a ∧ (¬a W (¬a ∧ b))) = G (¬a ∧ (true W b)) = G(¬a) 
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
        (a.left().type() == TermType.Not) and (a.right().right().left().type() == TermType.Not) and (a.right().left().type() == TermType.Not) and\
        a.left().left().equals(a.right().right().left().left()) and a.left().left().equals(a.right().left().left()):
      return GloballySimpl(a.left())
  
  # G (¬a ∧ (¬a W b)) = G (¬a ∧ (true W b)) = G(¬a)
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and \
        (a.left().type() == TermType.Not) and (a.right().left().type() == TermType.Not) and\
        a.left().left().equals(a.right().left().left()):
      return GloballySimpl(a.left())
  
  # G (¬a W (b v a)) = true
  elif (a.type() == TermType.W) and (a.right().type() == TermType.Or) and\
        (CheckNotHelper(a.left(), a.right().right()) or CheckNotHelper(a.left(), a.right().left())):
      return BoolConstTerm(True)
  
  # G (¬a W (G a)) = G(a -> Ga)
  elif (a.type() == TermType.W) and (a.right().type() == TermType.G) and \
        CheckNotHelper(a.left(), a.right().left()):
      return GloballySimpl(ImplSimpl(a.right().left(), GloballySimpl(a.right().left())))  
  
  # G (a W (G b)) = G(¬a -> G(b))
  elif (a.type() == TermType.W) and (a.right().type() == TermType.G):
      return GloballySimpl(ImplSimpl(No(a.left()), a.right()))
  
  # G ((a ∧ ¬b) W (G (a ∧ b))) = G(¬(a | b) -> G(a & b)) != G(a ∧ ¬b) v FG(a ∧ b)
  elif (a.type() == TermType.W) and (a.right().type() == TermType.G) and \
       (a.left().type() == TermType.And) and (a.right().left().type() == TermType.And) and \
        CheckNotHelper(a.left().right(), a.right().left().right()) and\
        a.left().left().equals(a.right().left().left()):
      return GloballySimpl(ImplSimpl(No(a.left())), a.right())  

  # G (a ∧ ((a ∧ b) W (a ∧ c))) = G(a & (b | c)) != G (a ∧ (b W c))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and \
        (a.right().left().type() == TermType.And) and (a.right().right().type() == TermType.And) and\
        a.left().equals(a.right().left().left()) and a.left().equals(a.right().right().left()):
      return GloballySimpl(ConSimpl(a.left(), DisSimpl(a.right().left().right(),a.right().right().right())))

  # G (a ∧ (a W (a ∧ b))) = G a
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and \
    (a.right().right().type() == TermType.And) and\
    a.left().equals(a.right().left()) and a.left().equals(a.right().right().left()):
      return GloballySimpl(a.left())

  # G (a W (b ∧ (G a))) = G a
  elif (a.type() == TermType.W) and (a.right().type() == TermType.And) and \
    (a.right().right().type() == TermType.G) and\
    a.left().equals(a.right().right().left()):
      return GloballySimpl(a.left())
  
  # G (a W b) = G(a v b)
  elif (a.type() == TermType.W):
      return GloballySimpl(DisSimpl(a.left(),a.right()))

# G(a v ((¬a ∧ ¬b) W (b W a))) = G((¬b ∧ ¬a) v (b W a))
  elif (a.type() == TermType.Or) and (a.right().type() == TermType.W) and\
       (a.right().left().type() == TermType.And) and (a.right().right().type() == TermType.W) and\
       CheckNotHelper(a.left(), a.right().left().left()) and a.left().equals(a.right().right().right()) and\
       CheckNotHelper(a.right().left().right(), a.right().right().left()):
      return GloballySimpl(ImplSimpl(DisSimpl(a.left(),a.right().right().left()),a.right().right()))


# G (a v (b W c W a))) = G(b v (c W a)) 
  elif (a.type() == TermType.Or) and (a.right().type() == TermType.W) and\
       (a.right().right().type() == TermType.W) and\
        a.left().equals(a.right().right().right()):
      return GloballySimpl(DisSimpl(a.left(),a.right().right()))

# G (a → (G (b ∧ ¬a))) = G ¬a
  elif (a.type() == TermType.Impl) and (a.right().type() == TermType.G) and\
       (a.right().left().type() == TermType.And) and CheckNotHelper(a.left(), a.right().left().right()):
      return GloballySimpl(a.right().left().right())

# G (a → (c v (a ∧ (¬b W (b v d))))) = true
  elif (a.type() == TermType.Impl) and (a.right().type() == TermType.Or) and\
       (a.right().right().type() == TermType.And) and (a.right().right().right().type() == TermType.W) and\
       (a.right().right().right().right().type() == TermType.Or) and\
       a.left().equals(a.right().right().left()) and\
       CheckNotHelper(a.right().right().right().left(), a.right().right().right().right().left()):
      return BoolConstTerm(True)

# G (trig → (¬fin W (fin W ¬trig))) = G(fin → (fin W ¬trig))
  elif (a.type() == TermType.Impl) and (a.right().type() == TermType.W) and\
       (a.right().right().type() == TermType.W) and\
       CheckNotHelper(a.left(), a.right().right().right()) and\
       CheckNotHelper(a.right().left(), a.right().right().left()):
      return GloballySimpl(ImplSimpl(a.right().right().left(), a.right().right()))

# G (a → (a W (d v (¬a ∧ (¬b W (b v c)))))) = true
  elif (a.type() == TermType.Impl) and (a.right().type() == TermType.W) and\
       (a.right().right().type() == TermType.Or) and (a.right().right().right().type() == TermType.And) and\
       (a.right().right().right().right().type() == TermType.W) and (a.right().right().right().right().right().type() == TermType.Or) and\
       a.left().equals(a.right().left()) and CheckNotHelper(a.left(), a.right().right().right().left()) and\
       CheckNotHelper(a.right().right().right().right().left(), a.right().right().right().right().right().left()):
      return BoolConstTerm(True)

# G (a → ((b ∧ ¬c) W ((b ∧ c) W ¬a))) = G((b ∧ ¬c) v ((b ∧ c) W ¬a)) 
  elif (a.type() == TermType.Impl) and (a.right().type() == TermType.W) and\
       (a.right().right().type() == TermType.W) and (a.right().left().type() == TermType.And) and\
       (a.right().right().left().type() == TermType.And) and\
       CheckNotHelper(a.left(), a.right().right().right()) and\
       CheckNotHelper(a.right().left().right(), a.right().right().left().right()) and\
        a.right().left().left().equals(a.right().right().left().left()):
      return GloballySimpl(DisSimpl(a.right().left(),a.right().right()))


  else: return GTerm(a)


def WeakUntilSimpl(a:Term, b:Term):
  
  # 0 W 0 = 0
  # 1 W 0 = 1 W 1 = 0 W 1 = 1
  if ((a.type() == TermType.BoolConst) and (b.type() == TermType.BoolConst)):
    if ((a.val() == False) and (b.val() == False)): return BoolConstTerm(False)
    else: return BoolConstTerm(True)

  # 0 W b = b
  # 1 W b = 1
  elif (b.type() != TermType.BoolConst) and (a.type() == TermType.BoolConst):
    if (a.val() == False): return b
    else: return BoolConstTerm(True)
  
  # a W 1 = 1
  # a W 0 = G a
  elif (a.type() != TermType.BoolConst) and (b.type() == TermType.BoolConst):
    if (b.val() == True): return BoolConstTerm(True)
    else: return GloballySimpl(a)

  #a W a = a
  elif (a.equals(b)):
    return a

  # a W (b v a) = a W (a v b) 
  elif (b.type() == TermType.Or) and (a.equals(b.right()) or a.equals(b.left())):
    return b

  # (a ∧ b) W (c v a) = c v a
  elif (a.type() == TermType.And) and (b.type() == TermType.Or) and (a.left().equals(b.right())):
    return b

  # (a ∧ b) W a) = a
  elif (a.type() == TermType.And) and (a.left().equals(b) or a.right().equals(b)):
    return b

  # (a ∧ b) W (b v c) = b v c
  elif (a.type() == TermType.And) and (b.type() == TermType.Or) and\
    a.right().equals(b.left()):
    return b
  
  # ¬a W a = = G(¬a) \/ F(a) = true
  elif CheckNotHelper(a, b):
    return BoolConstTerm(True)
  
  # ¬a W (a v b) = true
  elif (b.type() == TermType.Or) and (CheckNotHelper(a, b.right()) or CheckNotHelper(a, b.left())):
    return BoolConstTerm(True)

  # (a ∧ ¬b) W (¬a v b) = 
  elif (a.type() == TermType.And) and (b.type() == TermType.Or) and\
    CheckNotHelper(a.left(), b.left()) and CheckNotHelper(a.right(), b.right()):
    return BoolConstTerm(True)

  # (a ∧ ¬b) W (b ∧ (G a)) = G (a)
  elif (a.type() == TermType.And) and (b.type() == TermType.And) and (b.right().type() == TermType.G) and \
       a.left().equals(b.right().left()) and CheckNotHelper(a.right(),b.left()):
      return GloballySimpl(a.left())

  # (¬a ∧ c) W a = c W a
  elif (a.type() == TermType.And) and (a.left().type() == TermType.Not) and \
       a.left().left().equals(b):
      return WeakUntilSimpl(a.right(), b)
  
  # (¬a ∧ c) W (a v d) = c W (a v d)
  elif (a.type() == TermType.And) and (b.type() == TermType.Or) and (a.left().type() == TermType.Not) and \
       a.left().left().equals(b.left()):
      return WeakUntilSimpl(a.right(), b)
  
  # ¬a W (a ∧ (¬a W b)) = ¬a W (a ∧ b)
  elif (a.type() == TermType.Not) and (b.type() == TermType.And) and (b.right().type() == TermType.W) and (b.right().left().type() == TermType.Not) and\
       a.left().equals(b.left()) and a.left().equals(b.right().left().left()):
      return WeakUntilSimpl(a, ConSimpl(b.left(),b.right().right()))
  
  # (a ∧ b) W (c W (b v d)) = c W (b v d)
  elif (a.type() == TermType.And) and (b.type() == TermType.W) and (b.right().type() == TermType.Or) and\
       a.right().equals(b.right().left()):
      return b
  
  # (a ∧ b) W (c W b) = c W b
  elif (a.type() == TermType.And) and (b.type() == TermType.W) and\
       a.right().equals(b.right()):
      return b
  
  # a W (a W b) = (a W b)
  elif (b.type() == TermType.W) and a.equals(b.left()):
      return b
  
  # a W (G a) = G a
  elif (b.type() == TermType.G) and a.equals(b.left()):
      return b
  

  else: return WTerm(a, b)


#
# MAIN
#
def Main():

  import pandas as pd
  import numpy as np
  from matplotlib import pyplot as plt 

  def BoolToString(a:Term):
    return a.printme()

  a = 8
  mas = [] 
  for i1 in range(3370): 
      mas.append([0] * a)

  cnt = []
  for i in range(6): 
      cnt.append([0])
  for i in range(6):
    cnt[i] = 0

  i = 0
  trigger = BoolConstTerm(True)
  release = BoolConstTerm(False)
  invariant = BoolConstTerm(False)
  final = BoolConstTerm(False)
  delay = BoolConstTerm(False)
  reaction = BoolConstTerm(False)


  
  def Reduce(k):
   
    x0 = ConSimpl(invariant, reaction)
    x1 = DisSimpl(release, x0)
    x2 = ConSimpl(invariant, No(delay))
    x3 = WeakUntilSimpl(x2, x1)
    x4 = ConSimpl(final, x3)
    x5 = DisSimpl(release, x4)
    x6 = ConSimpl(invariant, No(final))
    x7 = WeakUntilSimpl(x6, x5)
    x8 = ConSimpl(trigger, No(release))
    x9 = ImplSimpl(x8, x7)
    x10 = GloballySimpl(x9)


    mas[k][0] = BoolToString(trigger)
    mas[k][1] = BoolToString(release)
    mas[k][2] = BoolToString(invariant)
    mas[k][3] = BoolToString(final)
    mas[k][4] = BoolToString(delay)
    mas[k][5] = BoolToString(reaction)
    mas[k][6] = BoolToString(x10)
    return k+1

  cnt[0] = 0
  while cnt[0] < 2:
    if (cnt[0] == 0 ): trigger = BoolConstTerm(True)
    if (cnt[0] == 1 ): trigger = BoolFreeTerm('trig')
    cnt[0]+=1
    cnt[1] = 0
    while cnt[1] < 5:
      if (cnt[1] == 0): release = BoolConstTerm(True)
      if (cnt[1] == 1): release = BoolConstTerm(False)
      if (cnt[1] == 2): release = BoolFreeTerm('rel')
      if (cnt[1] == 3): 
        if (trigger.type() == TermType.BoolVar and trigger.v == 'trig'):
          release = BoolFreeTerm('trig')
        else: break
      if (cnt[1] == 4): 
        if (trigger.type() == TermType.BoolVar and trigger.v == 'trig'):
          release = NotTerm(BoolFreeTerm('trig'))
        else: break
      cnt[1]+=1
      cnt[2] = 0
      while cnt[2] < 6:
        if (cnt[2] == 0): invariant = BoolConstTerm(True)
        if (cnt[2] == 1): invariant = BoolConstTerm(False)
        if (cnt[2] == 2): invariant = BoolFreeTerm('inv')
        if (cnt[2] == 3): 
            if trigger.type() == TermType.BoolVar and trigger.v == 'trig':
              invariant = BoolFreeTerm('trig')
            else: cnt[2] = 4
        if (cnt[2] == 4):
          if (release.type() == TermType.BoolVar and release.v == 'rel'):
            invariant = BoolFreeTerm('rel')
          else: break
        if (cnt[2] == 5): 
          if (release.type() == TermType.BoolVar and release.v == 'rel'):
            invariant = NotTerm(BoolFreeTerm('rel'))
          else: break
        cnt[2]+=1
        cnt[3] = 0
        while cnt[3] < 9:
            if (cnt[3] == 0): final = BoolConstTerm(True)
            if (cnt[3] == 1): final = BoolConstTerm(False)
            if (cnt[3] == 2): final = BoolFreeTerm('fin')
            if (cnt[3] == 3):
              if (trigger.type() == TermType.BoolVar and trigger.v == 'trig'):
                final = BoolFreeTerm('trig')
              else: cnt[3] = 5
            if (cnt[3] == 4): 
              if (trigger.type() == TermType.BoolVar and trigger.v == 'trig'):
                final = NotTerm(BoolFreeTerm('trig'))
              else: cnt[3] = 5
            if (cnt[3] == 5):
              if (release.type() == TermType.BoolVar and release.v == 'rel'):
                final = BoolFreeTerm('rel')
              else: cnt[3] = 7
            if (cnt[3] == 6):
              if (release.type() == TermType.BoolVar and release.v == 'rel'):
                final = NotTerm(BoolFreeTerm('rel'))
              else: cnt[3] = 7
            if (cnt[3] == 7):
              if (invariant.type() == TermType.BoolVar and invariant.v == 'inv'):
                final = BoolFreeTerm('inv')
              else: break                      
            if (cnt[3] == 8): 
              if (invariant.type() == TermType.BoolVar and invariant.v == 'inv'):
                final = NotTerm(BoolFreeTerm('inv'))
              else: break                      
            cnt[3] += 1
            cnt[4] = 0
            while cnt[4] < 11:
                if (cnt[4] == 0): delay = BoolConstTerm(True)
                if (cnt[4] == 1): delay = BoolConstTerm(False)
                if (cnt[4] == 2): delay = BoolFreeTerm('del')
                if (cnt[4] == 3):
                  if (trigger.type() == TermType.BoolVar and trigger.v == 'trig'):
                    delay = BoolFreeTerm('trig')
                  else: cnt[4] = 5
                if (cnt[4] == 4): 
                  if (trigger.type() == TermType.BoolVar and trigger.v == 'trig'):
                    delay = NotTerm(BoolFreeTerm('trig'))
                  else: cnt[4] = 5
                if (cnt[4] == 5):
                  if (release.type() == TermType.BoolVar and release.v == 'rel'):
                    delay = BoolFreeTerm('rel')
                  else: cnt[4] = 7
                if (cnt[4] == 6): 
                  if (release.type() == TermType.BoolVar and release.v == 'rel'):
                    delay = NotTerm(BoolFreeTerm('rel'))
                  else: cnt[4] = 7
                if (cnt[4] == 7):
                  if (invariant.type() == TermType.BoolVar and invariant.v == 'inv'):
                    delay = BoolFreeTerm('inv')
                  else: cnt[4] = 9
                if (cnt[4] == 8): 
                  if (invariant.type() == TermType.BoolVar and invariant.v == 'inv'):
                      delay = NotTerm(BoolFreeTerm('inv'))
                  else: cnt[4] = 9
                if (cnt[4] == 9):
                  if (final.type() == TermType.BoolVar and  final.v == 'fin'):
                    delay = BoolFreeTerm('fin')
                  else: break
                if (cnt[4] == 10): 
                  if (final.type() == TermType.BoolVar and  final.v == 'fin'):
                    delay = NotTerm(BoolFreeTerm('fin')) 
                  else: break
                cnt[4]+=1
                cnt[5] = 0
                while cnt[5] < 3:
                  if (cnt[5] == 0): reaction = BoolConstTerm(True)
                  if (cnt[5] == 1): reaction = BoolConstTerm(False)
                  if (cnt[5] == 2): reaction = BoolFreeTerm('rea')
                  i = Reduce(i)
                  cnt[5] += 1
                  

# G ((trig ∧ ¬ rel) → ( (inv ∧ ¬fin) W (rel v (fin ∧ ((inv ∧ (¬ del)) W (rel v (inv ∧ rea))))))) 

  for i in range(0, len(mas)):
      for i2 in range(0, len(mas[i])):
          print(mas[i][i2], end=' ')
      print()

  from openpyxl import Workbook
  wb = Workbook()
  ws = wb.active
  for subarray in mas:
     ws.append(subarray)
  wb.save('./edtl-ltl.xlsx')



if __name__ == '__main__':
  Main()