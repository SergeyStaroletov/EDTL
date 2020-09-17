#include <iostream>

#define DEBUG

enum vars { H, D };

// test case:
// HANDS yes/no
int H_VAL[] = {1, 1, 0, 0, 0};
// HANDS DRIER on/off
int D_VAL[] = {0, 1, 1, 1, 1};

class Term {
 public:
  virtual int value(int i, int j, int h) = 0;
  void debug(const std::string &msg, int i) {
#ifdef DEBUG
    std::cout << "value of " << i << msg << " term" << std::endl;
#endif
  }
};

// const
class ConstTerm : public Term {
  int val;

 public:
  ConstTerm(int c) : val(c) {}
  int value(int i, int j, int h) { return val; }
};

// value of the variable
class ValTerm : public Term {
 private:
  vars var;

 public:
  ValTerm(vars var) : var(var) {}
  int value(int i, int j, int h) {
    if (i < 0) i = 0;
    debug("val", i);

    if (var == vars::D) return D_VAL[i];
    if (var == vars::H) return H_VAL[i];
    return 0;
  };
};

// boolean operations

// negation
class NegTerm : public Term {
 private:
  Term *term;

 public:
  NegTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("neg", i);

    return !term->value(i, j, h);
  }
};

// and
class AndTerm : public Term {
 private:
  Term *term1, *term2;

 public:
  AndTerm(Term *term1, Term *term2) : term1(term1), term2(term2) {}
  int value(int i, int j, int h) {
    debug("and", i);

    return term1->value(i, j, h) && term2->value(i, j, h);
  }
};

// or
class OrTerm : public Term {
 private:
  Term *term1, *term2;

 public:
  OrTerm(Term *term1, Term *term2) : term1(term1), term2(term2) {}
  int value(int i, int j, int h) {
    debug("or", i);

    return term1->value(i, j, h) || term2->value(i, j, h);
  }
};

// our values
class TildaTerm : public Term {
 private:
  Term *term;

 public:
  TildaTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("tilda", i);
    if (i <= 0) return false;

    return (i != 0) && term->value(i - 1, j, h) && term->value(i, j, h);
  }
};

class SlashTerm : public Term {
 private:
  Term *term;

 public:
  SlashTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("slash", i);
    if (i <= 0) return false;

    return (i != 0) && term->value(i - 1, j, h) && !term->value(i, j, h);
  }
};

class BackShashTerm : public Term {
 private:
  Term *term;

 public:
  BackShashTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("backslash", i);
    if (i <= 0) return false;

    return (i != 0) && !term->value(i - 1, j, h) && term->value(i, j, h);
  }
};

class UnderlineTerm : public Term {
 private:
  Term *term;

 public:
  UnderlineTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("underline", i);
    if (i <= 0) return false;

    return (i != 0) && !term->value(i - 1, j, h) && !term->value(i, j, h);
  }
};

// functions
class PassedTerm : public Term {
 private:
  Term *term;

 public:
  PassedTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("passed", i);

    return (i * h >= j * h + term->value(i, j, h));
  }
};

class ChangesTerm : public Term {
 private:
  Term *term;

 public:
  ChangesTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("changes", i);
    if (i <= 0) return false;

    return term->value(i - 1, j, h) != term->value(i, j, h);
  }
};

class IncreasesTerm : public Term {
 private:
  Term *term;

 public:
  IncreasesTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("increases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j, h) < term->value(i, j, h);
  }
};

class DecreasesTerm : public Term {
 private:
  Term *term;

 public:
  DecreasesTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("decreases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j, h) > term->value(i, j, h);
  }
};

class NotIncreasesTerm : public Term {
 private:
  Term *term;

 public:
  NotIncreasesTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("notincreases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j, h) <= term->value(i, j, h);
  }
};

class NotDecreasesTerm : public Term {
 private:
  Term *term;

 public:
  NotDecreasesTerm(Term *term) : term(term) {}
  int value(int i, int j, int h) {
    debug("notdecreases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j, h) >= term->value(i, j, h);
  }
};

// abstract class for the system
class CheckableSystem {
 public:
  CheckableSystem() {}
  virtual int trigger(int i, int j, int h) = 0;
  virtual bool isTrigger() = 0;
  virtual int reset(int i, int j, int h) = 0;
  virtual int postcondition(int i, int j, int h) = 0;
  virtual int precondition(int i, int j, int h) = 0;

  virtual int ASAP(int i, int j, int h) = 0;
  virtual int final(int i, int j, int h) = 0;

  bool check(int h, int max) {
    int i = 0;
    while (true) {
      if (i >= max) return true;
      if (this->trigger(i, 0, h)) {
        if (this->reset(i, 0, h)) goto checked;
        int j = i;
        while (this->final(j, i, h)) {
          if (j >= max) return true;

          if (this->reset(j, i, h)) goto checked;
          if (this->precondition(j, i, h)) {
            std::cout << "first case: ";
            std::cout << i << j << std::endl;
            return false;
          }
          j++;
        }
        int k = j;
        while (this->ASAP(k, j, h)) {
          if (k >= max) return true;

          if (this->reset(k, j, h)) goto checked;
          if (this->postcondition(k, j, h)) break;
          if (!this->precondition(k, j, h)) {
            std::cout << "second case: ";
            std::cout << i << j << k << std::endl;
            return false;
          }
          k++;
        }
      }
    checked:;
      i++;
    }
  }
};

/*
class CASE1 : public CheckableSystem {
 public:
  virtual int trigger(int i, int j, int h) {
    return (new AndTerm(new SlashTerm(new ValTerm(vars::H)),
                        new TildaTerm(new ValTerm(vars::D))))
        ->value(i, j, h);
  };

  virtual bool isTrigger() { return true; }
  virtual int reset(int i, int j, int h) {
    return (new ValTerm(vars::H))->value(i, j, h);
  }
  virtual int postcondition(int i, int j, int h) {
    return (new ValTerm(vars::D))->value(i, j, h);
  }
  virtual int precondition(int i, int j, int h) {
    return (new ValTerm(vars::D))->value(i, j, h);
  }

  virtual int ASAP(int i, int j, int h) { return 1; }
  virtual int final(int i, int j, int h) { return 5; }
};
*/

class CASE4 : public CheckableSystem {
 public:
  virtual int trigger(int i, int j, int h) {
    return (new AndTerm(new ValTerm(vars::H), new ValTerm(vars::D)))
        ->value(i, j, h);
  };

  virtual bool isTrigger() { return true; }
  virtual int reset(int i, int j, int h) { return false; }
  virtual int postcondition(int i, int j, int h) {
    std::cout << "postcondition called" << std::endl;
    return (new NegTerm(new ValTerm(vars::D)))->value(i, j, h);
  }
  virtual int precondition(int i, int j, int h) {
    std::cout << "precondition called" << std::endl;

    return (new NegTerm(new ValTerm(vars::D)))->value(i, j, h);
  }

  virtual int ASAP(int i, int j, int h) {
    return (new PassedTerm(new ConstTerm(0)))->value(i, j, h);
  }
  virtual int final(int i, int j, int h) {
    int ret = (new PassedTerm(new ConstTerm(0)))->value(i, j, h);  // 0 was safe
    std::cout << "final returned " << ret << std::endl;
    return ret;
  }
};

int main(int argc, char *argv[]) {
  CheckableSystem *system = new CASE4();

  int max = sizeof(H_VAL) / sizeof(int) - 1;

  int h = 10;  //
  if (system->check(h, max))
    std::cout << "System is safe" << std::endl;
  else
    std::cout << "! System is unsafe " << std::endl;

  return 0;
}
