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
    print('checking ')
    print(self.printme() + ' vs ')
    print(other.printme())
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
  #a ∨ (b ∧ a) = a
  elif (b.type() == TermType.And) and (a.equals(b.right())):
    return a
  #a ∨ (a ∧ b) = a
  elif (b.type() == TermType.And) and (a.equals(b.left())):
    return a
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
  elif (a.type() == TermType.G) and (a.left().type() == TermType.Not) and \
  (b.type() == TermType.F) and (a.left().left().equals(b.left())):
    return BoolConstTerm(True)
  #a ∨ F(a) = F(a)
  elif (b.type() == TermType.F) and (b.left().equals(a)):
    return b
  # (G a) v a = G a
  elif (a.type() == TermType.G) and (a.left().equals(b)): return a
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
  # a v (b ∧ (c v (c U a))) = a v (b ∧ (c U a)) = b ∧ (c U a)
  elif (b.type() == TermType.And) and    \
       (b.right().type() == TermType.Or) and  \
       (b.right().right().type() == TermType.U) and  \
       (b.right().right().right().equals(a)):
    #return DisSimpl(a,ConSimpl(b.left(),b.right().right()))
    return ConSimpl(b.left(),b.right().right())
   
  # a v (b v (c v a))) = b v (c v a) 
  elif (b.type() == TermType.Or) and (b.right().type() == TermType.Or) and (b.right().right().equals(a)):
    return b  



  #a v (b ∧ (c W (a v d)))))
  elif (b.type() == TermType.And) and    \
       (b.right().type() == TermType.W) and  \
       (b.right().right().type() == TermType.Or) and  \
       (b.right().right().left().equals(a)):
    return b

  #a v (b ∧ (c W a)))) = b ∧ (c W a)
  elif (b.type() == TermType.And) and    \
       (b.right().type() == TermType.W) and  \
       (b.right().right().equals(a)):
    return b


  # a v (b W (a v c))) = b W (a v c)
  elif (b.type() == TermType.W) and (b.right().type() == TermType.Or) and (b.right().left().equals(a)):
    return b
  # a v (b W a)) = b W a
  elif (b.type() == TermType.W) and (b.right().equals(a)):
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
  elif (a.type() == TermType.Not) and (a.left().equals(b)): 
    return BoolConstTerm(False)
  elif (b.type() == TermType.Not) and (b.left().equals(a)): 
    return BoolConstTerm(False)
  # (¬ a) ∧ (a v b) = (¬ a) ∧ b
  elif (a.type() == TermType.Not) and (b.type() == TermType.Or) and (a.left().equals(b.left())): 
    return ConSimpl(a,b.right())
  # (¬ a) ∧ (b v a) = (¬ a) ∧ b
  elif (a.type() == TermType.Not) and (b.type() == TermType.Or) and (a.left().equals(b.right())): 
    return ConSimpl(a,b.left())
  # (¬ a) ∧ (b v (b U a)) = (¬ a) ∧ (b U a)
  elif (a.type() == TermType.Not) and (b.type() == TermType.Or) and (b.right().type() == TermType.U) and (a.left().equals(b.right().right())) and (b.left().equals(b.right().left())) : 
    return ConSimpl(a,b.right())
  # (¬ a) ∧ (b v ((b ∧ c) U a)) = (¬ a) ∧ ((b ∧ c) U a)
  elif (a.type() == TermType.Not) and (b.type() == TermType.Or) and (b.right().type() == TermType.U) and (b.right().left().type() == TermType.And) and\
      (a.left().equals(b.right().right())) and (b.left().equals(b.right().left().left())) : 
    return ConSimpl(a,b.right())
  else: return AndTerm(a, b)


def No(a:Term):
  if (a.type() == TermType.BoolConst): 
    return BoolConstTerm(not a.val())
  else: 
    return NotTerm(a)


def ImplSimpl(a:Term, b:Term):
  if ((a.type() == TermType.BoolConst) or (b.type() == TermType.BoolConst)):
    return DisSimpl(No(a), b)
  # ¬a -> a
  elif ((a.type() == TermType.Not) and (a.left().equals(b))): 
    return b
  # (¬rel ->)
  elif ((a.type() == TermType.Not) and (a.left().val() == 'rel')): 
    return DisSimpl(a.left(),b)
  # ¬a -> a ∨ b
  elif ((a.type() == TermType.Not) and (b.type() == TermType.Or) and (a.left().equals(b.left()))): 
    return b
  # c∧¬a -> a
  elif ((a.type() == TermType.And) and (a.right().type() == TermType.Not) and a.right().left().equals(b)): 
    return ImplSimpl(a.left(), b)
  # c∧¬a -> a ∨ b
  elif ((a.type() == TermType.And) and (a.right().type() == TermType.Not) and (b.type() == TermType.Or) and (a.right().left().equals(b.left()))): 
    return ImplSimpl(a.left(), b)
  # ¬a -> F a
  elif ((a.type() == TermType.Not) and (b.type() == TermType.F) and (a.left().equals(b.left()))): 
    return b
  # c∧¬a -> F a
  elif ((a.type() == TermType.And) and (a.right().type() == TermType.Not) and (b.type() == TermType.F) and (a.right().left().equals(b.left()))): 
    return ImplSimpl(a.left(), b)
  # ¬a -> F(a ∨ b)
  elif ((a.type() == TermType.Not) and (b.type() == TermType.F) and (b.left().type() == TermType.Or) and (a.left().equals(b.left().left()))): 
    return b
  # c∧¬a -> F(a ∨ b)
  elif ((a.type() == TermType.And) and (a.right().type() == TermType.Not) and (b.type() == TermType.F) and (b.left().type() == TermType.Or) and (a.left().equals(b.left().left()))): 
    return ImplSimpl(a.left(), b)
  # ¬a -> b U a 
  elif ((a.type() == TermType.Not) and (b.type() == TermType.U) and (a.left().equals(b.right()))): 
    return b  
  # ¬a -> b U (a ∨ c)
  elif ((a.type() == TermType.Not) and (b.type() == TermType.U) and (b.right().type() == TermType.Or ) and (a.left().equals(b.right().left()))):
    return b  
  # ¬a -> b W a = b W a
  elif ((a.type() == TermType.Not) and (b.type() == TermType.W) and (a.left().equals(b.right()))): 
    return b  
  # ¬a -> b W (a ∨ c) = b W (a ∨ c)
  elif ((a.type() == TermType.Not) and (b.type() == TermType.W) and (b.right().type() == TermType.Or ) and (a.left().equals(b.right().left()))):
    return b  
  # c∧¬a -> b W a = c -> b W a
  elif ((a.type() == TermType.And) and (a.right().type() == TermType.Not) and (b.type() == TermType.W) and (a.right().left().equals(b.right()))): 
    return ImplSimpl(a.left(), b)  
  # c∧¬a -> b W (a ∨ d) = c -> b W (a ∨ d)
  elif ((a.type() == TermType.And) and (a.right().type() == TermType.Not) and (b.type() == TermType.W) and (b.right().type() == TermType.Or ) and (a.right().left().equals(b.right().left()))):
    return ImplSimpl(a.left(), b)  
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
  elif (a.type() == TermType.G): return GloballySimpl(a.left())

  # G ((G a) v a) = G(a)
  elif (a.type() == TermType.Or) and (a.left().type() == TermType.G) and (a.left().left().equals(a.right())): return GloballySimpl(a.right())
  
  #51 G(G(a ∧ ¬b) ∨ (a U (b ∧ a))) = G(a)
  elif (a.type() == TermType.Or) and (a.left().type() == TermType.G) and (a.right().type() == TermType.U) and \
       (a.right().right().type() == TermType.And) and (a.left().left().type() == TermType.And) and \
       (a.left().left().left().equals(a.right().left())) and (a.right().left().equals(a.right().right().right())) and \
       CheckNotHelper((a.left().left().right()), a.right().right().left()):
    return GloballySimpl(a.left().left().left())

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
      return GloballySimpl(ConSimpl(a.left().left().left(), DisSimpl(GloballySimpl(a.left().left().right()), FutureSimpl(ConSimpl(a.right().right().left(),
      FutureSimpl(a.right().right().right().right().right()))))))
      
  #53 G(G(a ∧ ¬b) ∨ ((a ∧ ¬b) U (b ∧ (a ∧ c)))) = G(a ∧ (G(¬b) ∨ F(b ∧ c)))
  elif (a.type() == TermType.Or) and (a.right().type() == TermType.U) and (a.left().type() == TermType.G) and \
    (a.left().left().type() == TermType.And) and (a.right().left().type() == TermType.And) and \
    (a.left().left().equals(a.right().left())) and (a.right().right().type() == TermType.And) and \
    (a.right().right().right().type() == TermType.And) and CheckNotHelper(a.left().left().right(), a.right().right().left()):
      #return GTerm(AndTerm(a.left().left().left(), OrTerm(GTerm(a.left().left().right()), 
      #FTerm(AndTerm(a.right().right().left(), a.right().right().right().right())))))
      return GloballySimpl(ConSimpl(a.left().left().left(), DisSimpl(GloballySimpl(a.left().left().right()), 
      FutureSimpl(ConSimpl(a.right().right().left(), a.right().right().right().right())))))

  #44 G(G(a) ∨ (a U b)) = G(a ∧ F(b))
  #elif (a.type() == TermType.Or) and (a.left().type() == TermType.G) and (a.right().type() == TermType.U) and \
  #  (a.left().left().equals(a.right().left())):
  #    #return GTerm(AndTerm(a.left().left(), FTerm(a.right().right())))
  #    return GloballySimpl(ConSimpl(a.left().left(), FutureSimpl(a.right().right())))
  
  #45 G((a ∧ b) U (a ∧ c)) = G(a ∧ (b U c))
  elif (a.type() == TermType.U) and (a.left().type() == TermType.And) and (a.right().type() == TermType.And) and \
    (a.left().left().equals(a.right().left())):
      #return GTerm(AndTerm(a.left().left(), UTerm(a.left().right(), a.right().right())))
      return GloballySimpl(ConSimpl(a.left().left(), UntilSimpl(a.left().right(), a.right().right())))
    
  #46 G(a U (a ∧ b)) = G(a ∧ F b)
  elif (a.type() == TermType.U) and (a.right().type() == TermType.And) and \
    (a.left().equals(a.right().left())):
      return GloballySimpl(ConSimpl(a.left(), FutureSimpl(a.right().right())))
    
  #47 G(a U (b ∧ a)) = G(a ∧ F b)
  elif (a.type() == TermType.U) and (a.right().type() == TermType.And) and \
    (a.left().equals(a.right().right())):
      return GloballySimpl(ConSimpl(a.left(), FutureSimpl(a.right().left())))
  
  # G ((¬ a) ∧ ( b U a)) = false
  elif (a.type() == TermType.And) and (a.right().type() == TermType.U) and \
    CheckNotHelper(a.left(),a.right().right()):
      return BoolConstTerm(False)
  
  # G ((¬ a) ∧ ( b W a)) = G ((¬ a) ∧ b))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and \
    CheckNotHelper(a.left(),a.right().right()):
      return GloballySimpl(ConSimpl(a.left(), a.right().left()))
  
  # G (a ∧ ((¬ b) W b)) = G a
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and \
    CheckNotHelper(a.right().left(),a.right().right()):
      return GloballySimpl(a.left())

  # G (a ∧ ((b ∧ (¬ c)) W (c ∧ b))) = G (a ∧ c)
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

  # G ((¬ a) ∧ ( b U (a ∨ c) )) = G ((¬ a) ∧ ( b U c ))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.U) and (a.right().right().type() == TermType.Or) and \
    CheckNotHelper(a.left(),a.right().right().left()):
      return GloballySimpl(ConSimpl(a.left(), UntilSimpl(a.right().left(),a.right().right().right())))

  # G ((¬ a) ∧ ( b W (a ∨ c) )) = G ((¬ a) ∧ ( b W c ))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.Or) and \
    CheckNotHelper(a.left(),a.right().right().left()):
      return GloballySimpl(ConSimpl(a.left(), WTerm(a.right().left(),a.right().right().right())))
  
  # G ((¬ a) ∧ (b W (c ∧ (F a)))) = G (a -> G b)
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
       (a.right().right().right().type() == TermType.F) and CheckNotHelper(a.left(),a.right().right().right().left()):
      #return GloballySimpl(ConSimpl(a.left(), WTerm(a.right().left(),a.right().right().left())))
      return GloballySimpl(ImplSimpl(a.left().left(), GloballySimpl(a.right().left())))

  # G ((¬ a) ∧ (b W (c ∧ (d U a)))) = G (a -> G b)
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
       (a.right().right().right().type() == TermType.U) and CheckNotHelper(a.left(),a.right().right().right().right()):
      #return GloballySimpl(ConSimpl(a.left(), WTerm(a.right().left(),a.right().right().left())))
      return GloballySimpl(ImplSimpl(a.left().left(), GloballySimpl(a.right().left())))

  # G ((¬ a) ∧ (b W (c ∧ (F (a v d))))) = G ((¬ a) ∧ (b W (c ∧ (F d))))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
       (a.right().right().right().type() == TermType.F) and (a.right().right().right().left().type() == TermType.Or) and CheckNotHelper(a.left(),a.right().right().right().left().left()):
      return GloballySimpl(ConSimpl(a.left(), WTerm(a.right().left(), AndTerm(a.right().right().left(), FTerm(a.right().right().right().left().right())))))

  # G ((¬ a) ∧ (b W (c ∧ (d U (a v e))))) = G ((¬ a) ∧ (b W (c ∧ (d U e))))
  elif (a.type() == TermType.And) and (a.right().type() == TermType.W) and (a.right().right().type() == TermType.And) and \
       (a.right().right().right().type() == TermType.U) and (a.right().right().right().right().type() == TermType.Or) and CheckNotHelper(a.left(),a.right().right().right().right().left()):
      return GloballySimpl(ConSimpl(a.left(), WTerm(a.right().left(), AndTerm(a.right().right().left(), UTerm(a.right().right().right().left(), a.right().right().right().right().right())))))
  
  # G ((a ∧ (¬ b)) W (b ∧ (G a))) = G (a)
  elif (a.type() == TermType.W) and (a.left().type() == TermType.And) and (a.right().type() == TermType.And) and (a.right().right().type() == TermType.G) and \
       a.left().left().equals(a.right().right().left()) and CheckNotHelper(a.left().right(),a.right().left()):
      return GloballySimpl(a.right().right())

  # G ((a ∧ (¬ b)) W (b ∧ a)) = G (a)
  elif (a.type() == TermType.W) and (a.left().type() == TermType.And) and (a.right().type() == TermType.And) and \
       a.left().left().equals(a.right().right()) and CheckNotHelper(a.left().right(),a.right().left()):
      return GloballySimpl(a.right().right())


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
    return DisSimpl(FutureSimpl(a.left()), UntilSimpl(a, b.left()))
    #return OrTerm(FTerm(a.left()), UTerm(a, b.left()))
    
  #46 (a ∧ b) U (c ∨ a) = a ∨ ((a ∧ b) U c)
  #elif (a.type() == TermType.And) and (b.type() == TermType.Or) and (a.left().equals(b.right())):
    #return OrTerm(a.left(), UTerm(a, b.left()))
   # return DisSimpl(a.left(), UTerm(a, b.left()))
    
  #47 (a ∧ b) U a = a
  elif (a.type() == TermType.And) and (a.left().equals(b)):
    return b

  #48 a U (b ∨ a) = a ∨ b
  elif (b.type() == TermType.Or) and (a.equals(b.right())):
    #return OrTerm(a, UTerm(a, b.left()))
    return DisSimpl(a, b.left())

  #50 (a ∧ ¬b) U (b ∧ a) = a U (b ∧ a)
  #elif (a.type() == TermType.And) and (b.type() == TermType.And) and (a.left().equals(b.right())) \
   # and (CheckNotHelper(a.right(), b.left())):
      #return UTerm(a.left(), b)
    #  return UntilSimpl(a.left(), b)

  else: return UTerm(a, b)



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

  # a W (b v a) = b v a
  elif (b.type() == TermType.Or) and (a.equals(b.right())):
    return b

  # (a ∧ b) W (c v a) = c v a
  elif (a.type() == TermType.And) and (b.type() == TermType.Or) and (a.left().equals(b.right())):
    return b

  # (a ∧ b) W a) = a
  elif (a.type() == TermType.And) and (a.left().equals(b)):
    return b

  # ¬a W a = = G(¬a) \/ F(a) = true
  elif CheckNotHelper(a, b):
    return BoolConstTerm(True)

  # ¬a W (b v a) = ¬a W b
  elif (b.type() == TermType.Or) and CheckNotHelper(a, b.right()):
    return WeakUntilSimpl(a, b.left())

  # (a ∧ ¬b) W (b ∧ (G a)) = G (a)
  elif (a.type() == TermType.And) and (b.type() == TermType.And) and (b.right().type() == TermType.G) and \
       a.left().equals(b.right().left()) and CheckNotHelper(a.right(),b.left()):
      return GloballySimpl(a.left())

  # a W b
#  elif ((b.type() != TermType.BoolConst) and (a.type() != TermType.BoolConst)): return WTerm(a, b)
  else: return WTerm(a, b)


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

# false	true	fin	true	inv
    if (release_txt == 'false*' and delay_txt == 'true*' and final_txt == 'fin' and reaction_txt == 'true*' and invariant_txt == 'inv'):
      y13 = 1
    else: y13 = 2

# G ((trig ∧ ¬ rel) → ( (inv ∧ ¬fin) W (rel v (fin ∧ ((inv ∧ (¬ del)) W (rel v (inv ∧ rea))))))) = 		


    trigger = BoolFreeTerm('trig')
    x0 = ConSimpl(trigger, No(release))
    x1 = ConSimpl(invariant, reaction)
    x2 = DisSimpl(release, x1)
    x3 = ConSimpl(invariant, No(delay))
    x4 = WeakUntilSimpl(x3, x2)
    x5 = ConSimpl(final, x4)
    x6 = DisSimpl(release, x5)
    x7 = ConSimpl(invariant, No(final))
    x8 = WeakUntilSimpl(x7, x6)
    x9 = ImplSimpl(x0, x8)
    x10 = GloballySimpl(x9)

    
    trigger = BoolConstTerm(True)
    
    #y0 = ConSimpl(trigger, No(release))
    y0 = ConSimpl(trigger, No(release))
    y1 = ConSimpl(invariant, reaction)
    y2 = DisSimpl(release, y1)
    y3 = ConSimpl(invariant, No(delay))
    y4 = WeakUntilSimpl(y3, y2)
    y5 = ConSimpl(final, y4)
    y6 = DisSimpl(release, y5)
    y7 = ConSimpl(invariant, No(final))
    y8 = WeakUntilSimpl(y7, y6)
    y9 = ImplSimpl(y0, y8)
    y10 = GloballySimpl(y9)

    # if (y15.type() == TermType.G): y16 = GloballySimpl(y15.left())
    # else: y16 = y15

    trigger = BoolConstTerm(False)
    z1 = BoolConstTerm(True)
    
    mas[i][0] = BoolToString(release)
    mas[i][1] = BoolToString(delay)
    mas[i][2] = BoolToString(final)
    mas[i][3] = BoolToString(reaction)
    mas[i][4] = BoolToString(invariant)

    mas[i][5] = BoolToString(x10)
    mas[i][6] = BoolToString(y10)
    mas[i][7] = BoolToString(z1)

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
  #unittest.main()
  Main()