# @author getmanova
# @author star


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
  if (a.type() == TermType.BoolConst) or (a.type() == TermType.BoolVar): return a.printme()
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
    #print('checking ')
    #print(self.printme() + ' vs ')
    #print(other.printme())
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
    return  "¬ " + printx(self.left())

class AndTerm(TwoOpTerm):
  def type(self) -> TermType:
    return TermType.And
  def printme(self) -> str:
    return printx(self.left()) + " ∧ " + printx(self.right())

class OrTerm(TwoOpTerm):
  def type(self) -> TermType:
    return TermType.Or
  def printme(self) -> str:
    return printx(self.left()) + " v " + printx(self.right())

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
def DisSimpl(a:Term, b:Term):
  if ((a.type() == TermType.BoolConst) and (a.val() == True)) or \
  ((b.type() == TermType.BoolConst) and (b.val() == True)): 
    return BoolConstTerm(True)
  elif (a.type() == TermType.BoolConst) and (a.val() == False): return b
  elif (b.type() == TermType.BoolConst) and (b.val() == False): return a
  #a ∨ a = a
  elif (a.equals(b)):
    return a
  #a ∨ (b ∧ (a ∨ c)) = a ∨ (b ∧ c)
  elif (b.type() == TermType.And) and (b.right().type() == TermType.Or) and \
  (b.right().left().equals(a)):
    return OrTerm(a, AndTerm(b.left(), b.right().right())) 
  #a ∨ F(a ∨ b) = F(a ∨ b)
  elif (b.type() == TermType.F) and (b.left().type() == TermType.Or):
    return b
  #a ∨ (b U a) = (b U a)
  elif (b.type() == TermType.U) and (b.right().equals(a)):
    return b
  #G(¬a) ∨ F(a) = true
  elif (a.type() == TermType.G) and (a.left().type() == TermType.Not) and \
  (b.type() == TermType.F) and (a.left().left().equals(b.left())):
    return BoolConstTerm(True)
  #a ∨ F(a) = F(a)
  elif (b.type() == TermType.F) and (b.left().equals(a)):
    return b
  #elif (b.find(' ∧ '+a+')') > 0): ??
  #  return a;
  #a ∨ (a ∨ b) = a V b | a ∨ (b ∨ a) = a ∨ b
  elif (b.type() == TermType.Or) and (b.left().equals(a) or b.right().equals(a)):
    return b
  #G(¬a) ∨ (F(a) ∨ (с)) = (с)
  elif (a.type() == TermType.G) and (a.left().type() == TermType.Not) and (b.type() == TermType.Or) and \
  (b.left().type() == TermType.F) and (b.left().left().equals(a.left().left())):
    return b.right()
  #a ∨ (b U (a ∨ c)) = (b U (a ∨ c))
  elif (b.type() == TermType.U) and (b.right().type() == TermType.Or) and (b.right().left().equals(a)):
    return b
  else: 
    return OrTerm(a, b)



def ConSimpl(a:Term, b:Term):
  if ((a.type() == TermType.BoolConst) and (a.val() == False)) or \
  ((b.type() == TermType.BoolConst) and (b.val() == False)): 
    return BoolConstTerm(False)
  elif (a.type() == TermType.BoolConst) and (a.val() == True): 
    return b
  elif (b.type() == TermType.BoolConst) and (b.val() == True): 
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
  else:
    return ImplTerm(a, b)


def FutureSimpl(a:Term):
  if (a.type() == TermType.BoolConst): return a
  else: return FTerm(a)
  

# check a and not(b)/not(a) and b 
def CheckNotHelper(a:Term, b:Term):
  if (a.type() == TermType.BoolConst) and (b.type() == TermType.BoolConst):
    return a.val() != b.val()
  if (a.type() == TermType.Not) and (b.type() != TermType.Not):
    return a.left().equals(b)
  if (a.type() != TermType.Not) and (b.type() == TermType.Not):
    return b.left().equals(a)
  return False
  

def GloballySimpl(a:Term):
  if (a.type() == TermType.BoolConst): return a
  #G(F(a)) = GF(a)
  elif (a.type() == TermType.F): return GTerm(a)
  #G(G(a)) = G(a)
  elif (a.type() == TermType.G): return GTerm(a.left())
  #51 G(G(a ∧ ¬b) ∨ (a U (b ∧ a))) = G(a)
  elif (a.type() == TermType.Or) and (a.left().type() == TermType.G) and (a.right().type() == TermType.U) and \
       (a.right().right().type() == TermType.And) and (a.left().left().type() == TermType.And) and \
       (a.left().left().left().equals(a.right().left())) and (a.right().left().equals(a.right().right().right())) and \
       CheckNotHelper((a.left().left().right()), a.right().right().left()):
    return GTerm(a.left().left().left())

  #52 G(G(a ∧ ¬b) ∨ ((a ∧ ¬b) U (b ∧ (a U (a ∧ c))))) = G(a ∧ (G(¬b) ∨ F(b ∧ F(c))))
  elif (a.type() == TermType.Or) and (a.left().type() == TermType.G) and (a.right().type() == TermType.U) \
    and (a.right().right().type() == TermType.And) and (a.right().right().right().type() == TermType.U) \
    and (a.right().right().right().right().type() == TermType.And) and (a.left().left().equals(a.right().left())) \
    and (a.left().left().left().equals(a.right().right().right().left())) and \
    (a.left().left().left().equals(a.right().right().right().right().left())) and \
    CheckNotHelper(a.left().left().right(), a.right().right().left()):
      print(a.right().right().right().type())
      #return GTerm(AndTerm(a.left().left().left(), OrTerm(GTerm(a.left().left().right()), FTerm(AndTerm(a.right().right().left(),
      #FTerm(a.right().right().right().right().right()))))))
      return GTerm(ConSimpl(a.left().left().left(), DisSimpl(GloballySimpl(a.left().left().right()), FutureSimpl(DisSimpl(a.right().right().left(),
      FutureSimpl(a.right().right().right().right().right()))))))
      
  #53 G(G(a ∧ ¬b) ∨ ((a ∧ ¬b) U (b ∧ (a ∧ c)))) = G(a ∧ (G(¬b) ∨ F(b ∧ c)))
  elif (a.type() == TermType.Or) and (a.right().type() == TermType.U) and (a.left().type() == TermType.G) and \
    (a.left().left().type() == TermType.And) and (a.right().left().type() == TermType.And) and \
    (a.left().left().equals(a.right().left())) and (a.right().right().type() == TermType.And) and \
    (a.right().right().right().type() == TermType.And) and CheckNotHelper(a.left().left().right(), a.right().right().left()):
      #return GTerm(AndTerm(a.left().left().left(), OrTerm(GTerm(a.left().left().right()), 
      #FTerm(AndTerm(a.right().right().left(), a.right().right().right().right())))))
      return GTerm(ConSimpl(a.left().left().left(), DisSimpl(GloballySimpl(a.left().left().right()), 
      FutureSimpl(DisSimpl(a.right().right().left(), a.right().right().right().right())))))

  #44 G(G(a) ∨ (a U b)) = G(a ∧ F(b))
  elif (a.type() == TermType.Or) and (a.left().type() == TermType.G) and (a.right().type() == TermType.U) and \
    (a.left().left().equals(a.right().left())):
      #return GTerm(AndTerm(a.left().left(), FTerm(a.right().right())))
      return GloballySimpl(ConSimpl(a.left().left(), FutureSimpl(a.right().right())))
  
  #45 G((a ∧ b) U (a ∧ c)) = G(a ∧ (b U c))
  elif (a.type() == TermType.U) and (a.left().type() == TermType.And) and (a.right().type() == TermType.And) and \
    (a.left().left().equals(a.right().left())):
      #return GTerm(AndTerm(a.left().left(), UTerm(a.left().right(), a.right().right())))
      return GloballySimpl(ConSimpl(a.left().left(), UntilSimpl(a.left().right(), a.right().right())))
    
  else: return GTerm(a)



def UntilSimpl(a:Term, b:Term):

  if (b.type() == TermType.BoolConst) and (b.val() == False): 
    return BoolConstTerm(False)
  elif (b.type() == TermType.BoolConst) and (b.val() == True): 
    return BoolConstTerm(True)
  elif ((a.type() == TermType.BoolConst) and (a.val() == False) and (b.type() != TermType.BoolConst)): 
    return b
  elif ((a.type() == TermType.BoolConst) and (a.val() == True) and (b.type() != TermType.BoolConst)): 
    return FutureSimpl(b)

  #a U a = a
  elif (a.equals(b)):
    return a

  # ¬a U a = F(a)
  elif CheckNotHelper(a, b):
    return FutureSimpl(b)

  #¬a U (b ∨ a) = F(a) ∨ (¬a U b)
  elif (a.type() == TermType.Not) and (b.type() == TermType.Or) and (CheckNotHelper(a, b.right())):
    #return disSimpl(FutureSimpl(a.left()), UntilSimpl(a, b.left()))
    return OrTerm(FTerm(a.left()), UTerm(a, b.left()))
    
  #46 (a ∧ b) U (c ∨ a) = a ∨ ((a ∧ b) U c)
  elif (a.type() == TermType.And) and (b.type() == TermType.Or) and (a.left().equals(b.right())):
    #return OrTerm(a.left(), UTerm(a, b.left()))
    return DisSimpl(a.left(), UTerm(a, b.left()))
    
  #47 (a ∧ b) U a = a
  elif (a.type() == TermType.And) and (a.left().equals(b)):
    return b

  #48 a U (b ∨ a) = a ∨ (a U b)
  elif (b.type() == TermType.Or) and (a.equals(b.right())):
    #return OrTerm(a, UTerm(a, b.left()))
    return DisSimpl(a, UntilSimpl(a, b.left()))

  #50 (a ∧ ¬b) U (b ∧ a) = a U (b ∧ a)
  elif (a.type() == TermType.And) and (b.type() == TermType.And) and (a.left().equals(b.right())) \
    and (CheckNotHelper(a.right(), b.left())):
      #return UTerm(a.left(), b)
      return UntilSimpl(a.left(), b)

  else: return UTerm(a, b)



def WeakUntil(a:Term, b:Term):
  if ((a.type() == TermType.BoolConst) and (b.type() == TermType.BoolConst)):
    if ((a.val() == False) and (b.val() == False)): return BoolConstTerm(False)
    else: return BoolConstTerm(True)
  elif ((b.type() != TermType.BoolConst) and (a.type() != TermType.BoolConst)): return WeakUntil(a, b)
  elif (b.type() != TermType.BoolConst):
    if (a.type() == TermType.BoolConst) and (a.val() == False): return b
    elif (a.type() == TermType.BoolConst) and (a.val() == True): return BoolConstTerm(True)
  elif (a.type() != TermType.BoolConst):
    if (b.type() == TermType.BoolConst) and (b.val() == True): return BoolConstTerm(True)
    elif (b.type() == TermType.BoolConst) and (b.val() == False): return GloballySimpl(a)



#
# TESTS
#
class TestSimplifiers(unittest.TestCase):
      
    def setUp(self):
        print("Running tests for simplifiers...")
  
    def test_dis(self):
        a = BoolFreeTerm('a')
        b = BoolFreeTerm('b')
        c = BoolFreeTerm('c')
        #a ∨ a = a
        self.assertTrue(DisSimpl(a, a).equals(a))
        #a ∨ (b ∧ (a ∨ c)) = a ∨ (b ∧ c)
        self.assertTrue(DisSimpl(a, AndTerm(b, OrTerm(a, c))).equals(OrTerm(a, AndTerm(b, c))))
        #a ∨ F(a ∨ b) = F(a ∨ b)
        self.assertTrue(DisSimpl(a, FTerm(OrTerm(a, b))).equals(FTerm(OrTerm(a, b))))
        #a ∨ (b U a) = (b U a)
        self.assertTrue(DisSimpl(a, UTerm(b, a)).equals(UTerm(b, a)))
        #G(¬a) ∨ F(a) = true
        self.assertTrue(DisSimpl(GTerm(NotTerm(a)), FTerm(a)).equals(BoolConstTerm(True)))
        #a ∨ F(a) = F(a)
        self.assertTrue(DisSimpl(a, FTerm(a)).equals(FTerm(a)))
        #a ∨ (a ∨ b) = a V b | a ∨ (b ∨ a) = a ∨ b
        self.assertTrue(DisSimpl(a, OrTerm(a, b)).equals(OrTerm(a, b)))
        self.assertTrue(DisSimpl(a, OrTerm(b, a)).equals(OrTerm(b, a)))
        #G(¬a) ∨ (F(a) ∨ (с)) = (с)
        self.assertTrue(DisSimpl(GTerm(NotTerm(a)), OrTerm(FTerm(a), c)).equals(c))
        #a ∨ (b U (a ∨ c)) = (b U (a ∨ c))
        self.assertTrue(DisSimpl(a, UTerm(b, OrTerm(a, c))).equals(UTerm(b, OrTerm(a, c))))

    def test_globally(self):
        a = BoolFreeTerm('a')
        b = BoolFreeTerm('b')
        c = BoolFreeTerm('c')
        #G(F(a)) = GF(a)
        self.assertTrue(GloballySimpl(FTerm(a)).equals(GTerm(FTerm(a))))
        #G(G(a)) = G(a)
        self.assertTrue(GloballySimpl(GTerm(a)).equals(GTerm(a)))
        #51 G(G(a ∧ ¬b) ∨ (a U (b ∧ a))) = G(a)
        self.assertTrue(GloballySimpl(OrTerm(GTerm(AndTerm(a, NotTerm(b))), UTerm(a, AndTerm(b, a)))).equals(GTerm(a)))
        #52 G(G(a ∧ ¬b) ∨ ((a ∧ ¬b) U (b ∧ (a U (a ∧ c))))) = G(a ∧ (G(¬b) ∨ F(b ∧ F(c))))
        self.assertTrue(GloballySimpl(OrTerm(GTerm(AndTerm(a, NotTerm(b))), 
          UTerm(AndTerm(a, NotTerm(b)), AndTerm(b, UTerm(a, AndTerm(a, c)))))).equals(
            GTerm(AndTerm(a, OrTerm(GTerm(NotTerm(b)), FTerm(AndTerm(b, FTerm(c))))))))
        #53 G(G(a ∧ ¬b) ∨ ((a ∧ ¬b) U (b ∧ (a ∧ c)))) = G(a ∧ (G(¬b) ∨ F(b ∧ c)))
        self.assertTrue(GloballySimpl(OrTerm(GTerm(AndTerm(a, NotTerm(b))), 
          UTerm(AndTerm(a, NotTerm(b)), AndTerm(b, AndTerm(a, c))))).equals(
            GTerm(AndTerm(a, OrTerm(GTerm(NotTerm(b)), FTerm(AndTerm(b, c)))))))
        #44 G(G(a) ∨ (a U b)) = G(a ∧ F(b))
        self.assertTrue(GloballySimpl(OrTerm(GTerm(a), UTerm(a, b))).equals(GTerm(AndTerm(a, FTerm(b)))))
        #45 G((a ∧ b) U (a ∧ c)) = G(a ∧ (b U c))
        self.assertTrue(GloballySimpl(UTerm(AndTerm(a, b), AndTerm(a, c))).equals(GTerm(AndTerm(a, UTerm(b, c)))))

    def test_until(self):
        a = BoolFreeTerm('a')
        b = BoolFreeTerm('b')
        c = BoolFreeTerm('c')
        #a U a = a
        self.assertTrue(UntilSimpl(a, a).equals(a))
        # ¬a U a = F(a)
        self.assertTrue(UntilSimpl(NotTerm(a), a).equals(FTerm(a)))
        #¬a U (b ∨ a) = F(a) ∨ (¬a U b)
        self.assertTrue(UntilSimpl(NotTerm(a), OrTerm(b, a)).equals(OrTerm(FTerm(a), UTerm(NotTerm(a), b))))
        #46 (a ∧ b) U (c ∨ a) = a ∨ ((a ∧ b) U c)
        self.assertTrue(UntilSimpl(AndTerm(a, b), OrTerm(c, a)).equals(OrTerm(a, UTerm(AndTerm(a, b), c))))
        #47 (a ∧ b) U a = a
        self.assertTrue(UntilSimpl(AndTerm(a, b), a).equals(a))
        #48 a U (b ∨ a) = a ∨ (a U b)
        self.assertTrue(UntilSimpl(a, OrTerm(b, a)).equals(OrTerm(a, UTerm(a, b))))
        #50 (a ∧ ¬b) U (b ∧ a) = a U (b ∧ a)
        self.assertTrue(UntilSimpl(AndTerm(a, NotTerm(b)), AndTerm(b, a)).equals(UTerm(a, AndTerm(b, a))))
# /TESTS


#
# MAIN
#
def Main():

  import pandas as pd
  import numpy as np
  from matplotlib import pyplot as plt 

  data_frame = pd.read_csv('atributs.csv', encoding='utf8')
  print(data_frame);

  def konv(a_txt):
    if (a_txt == 'true*'): 
      return BoolConstTerm(True)
    elif (a_txt == 'false*'): 
      return BoolConstTerm(False)
    else: return BoolFreeTerm(a_txt)

  def BoolToString(a:Term):
    return a.printme()


  a = 12
  mas = [] 
  for i1 in range(243): 
      mas.append([0] * a)


  for i in data_frame.index:
    release_txt = data_frame['release'][i]
    delay_txt = data_frame['delay'][i]
    final_txt = data_frame['final'][i]
    reaction_txt = data_frame['reaction'][i]
    invariant_txt = data_frame['invariant'][i]

    release = konv(release_txt)
    delay = konv(delay_txt)
    final = konv(final_txt)
    reaction = konv(reaction_txt)
    invariant = konv(invariant_txt)

    trigger = BoolFreeTerm('trig')
    x0 = ConSimpl(trigger, No(release))
    x1 = ConSimpl(invariant, reaction)
    x2 = DisSimpl(release, x1)
    x3 = ConSimpl(invariant, No(delay))
    x4 = UntilSimpl(x3, x2)
    x5 = ConSimpl(final, x4)
    x6 = DisSimpl(release, x5)
    x7 = ConSimpl(invariant, No(final))
    x8 = UntilSimpl(x7, x6)

    x9 = ConSimpl(invariant, No(final))
    x10 = GloballySimpl(x9)
    x11 = DisSimpl(x10, x8)
    x12 = ConSimpl(invariant, x11)
    x13 = ImplSimpl(x0, x12)
    x14 = GloballySimpl(x13)

    
    trigger = BoolConstTerm(True)
    
    y0 = ConSimpl(trigger, No(release))
    y1 = ConSimpl(invariant, reaction)
    y2 = DisSimpl(release, y1)
    y3 = ConSimpl(invariant, No(delay))
    y4 = UntilSimpl(y3, y2)
    y5 = ConSimpl(final, y4)
    y6 = DisSimpl(release, y5)
    y7 = ConSimpl(invariant, No(final))
    y8 = UntilSimpl(y7, y6)
    y9 = ConSimpl(invariant, No(final))

    y10 = GloballySimpl(y9)
    y11 = DisSimpl(y10, y8)
    y12 = ConSimpl(invariant, y11)
    y13 = ImplSimpl(y0, y12)
    y14 = GloballySimpl(y13)

    trigger = BoolConstTerm(False)
    z1 = BoolConstTerm(True)
    
    mas[i][0] = BoolToString(release)
    mas[i][1] = BoolToString(delay)
    mas[i][2] = BoolToString(final)
    mas[i][3] = BoolToString(reaction)
    mas[i][4] = BoolToString(invariant)

    mas[i][5] = BoolToString(x14)
    mas[i][6] = BoolToString(y14)
    mas[i][7] = BoolToString(z1)

  for i in range(0, len(mas)):
      for i2 in range(0, len(mas[i])):
          print(mas[i][i2], end=' ')
      print()

  # from openpyxl import Workbook
  # wb = Workbook()
  # ws = wb.active
  # for subarray in mas:
  #    ws.append(subarray)
  # wb.save('./edtl-ltl.xlsx')



if __name__ == '__main__':
  #unittest.main()
  Main()