/*
@author Sergey Staroletov
@year 2020-2021
*/
#include <iostream>
#include <list>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>

//#define DEBUG

enum Vars { H, D };

struct TestVec
{
    std::initializer_list<bool> vals;
    Vars key;
};

class Havoc
{
public:
    static Havoc *inst;

    static Havoc *instance() { return inst; }
    Havoc() { inst = this; }

    void addTestVector(std::initializer_list<TestVec> tv)
    {
        // call can be havoc->addVector({{1, 1, 0, 0, 0}, vars::H}, {{0, 1, 1, 1, 1}, vars::D} );
        std::vector<bool> vec;
        std::map<Vars, std::vector<bool>> mp;
        //check we have H and D
        std::set<Vars> s1, s2;
        for (auto x : tv) {
            s1.insert(x.key);
        }
        for (int v = H; v <= D; v++) {
            s2.insert(static_cast<Vars>(v));
        }
        if (s1 != s2)
            throw std::invalid_argument("Not all variables are presented in addVector()");

        unsigned sz = 0;
        for (auto x : tv) {
            std::vector<bool> vec;
            for (auto y : x.vals) {
                vec.push_back(y);
            }
            mp[x.key] = vec;
            if (sz != 0 && vec.size() != sz)
                throw std::invalid_argument("Wrong vec size in addVector()");
            sz = vec.size();
        }
        sizes.push_back(sz);
        casesData.push_back(mp);
        cases++;
    }

    int getCurrentMaxStep() { return sizes[currentCase]; }

    bool get(Vars key, int num)
    {
        assert(casesData.size() >= currentCase);
        auto m = casesData.at(currentCase);
        if (m.find(key) != m.end()) {
            std::vector<bool> vec = m[key];
            return vec[num];
        }
        throw std::invalid_argument("Key not found in get()");
        return false;
    }

    unsigned getCases() { return cases; }

    void setActiveCase(unsigned c)
    {
        assert(c < cases);
        currentCase = c;
    }

private:
    unsigned cases;
    std::vector<unsigned> sizes;
    unsigned currentCase;
    Havoc(const Havoc &root) = delete;
    Havoc &operator=(const Havoc &) = delete;
    std::vector<std::map<Vars, std::vector<bool>>> casesData;
};

Havoc *Havoc::inst = 0;

// logic in terms
class Term
{
public:
    virtual int value(int i, int j) = 0;
    void debug(const std::string &msg, int i)
    {
#ifdef DEBUG
    std::cout << "value of " << i << " (" << msg << " term)" << std::endl;
#endif
    }
};

// const
class ConstTerm : public Term
{
    int val;

public:
    ConstTerm(int c) : val(c) {}
    int value(int i __unused, int j __unused) { return val; }
};

// value of the variable
class ValTerm : public Term
{
private:
    Vars var;

public:
    ValTerm(Vars var) : var(var) {}
    int value(int i, int j __unused)
    {
        if (i < 0)
            i = 0;
        debug("val", i);

        return Havoc::instance()->get(var, i);
    };
};

// boolean operations

// negation
class NegTerm : public Term {
 private:
  Term *term;

 public:
  NegTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("neg", i);

    return !term->value(i, j);
  }
};

// and
class AndTerm : public Term {
 private:
  Term *term1, *term2;

 public:
  AndTerm(Term *term1, Term *term2) : term1(term1), term2(term2) {}
  int value(int i, int j) {
    debug("and", i);

    return term1->value(i, j) && term2->value(i, j);
  }
};

// or
class OrTerm : public Term {
 private:
  Term *term1, *term2;

 public:
  OrTerm(Term *term1, Term *term2) : term1(term1), term2(term2) {}
  int value(int i, int j) {
    debug("or", i);

    return term1->value(i, j) || term2->value(i, j);
  }
};

// our addition
class TildaTerm : public Term {
 private:
  Term *term;

 public:
  TildaTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("tilda", i);
    if (i <= 0) return false;

    return (i != 0) && term->value(i - 1, j) && term->value(i, j);
  }
};

class SlashTerm : public Term {
 private:
  Term *term;

 public:
  SlashTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("slash", i);
    if (i <= 0) return false;

    return (i != 0) && !term->value(i - 1, j) && term->value(i, j);
  }
};

class BackSlashTerm : public Term {
 private:
  Term *term;

 public:
  BackSlashTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("backslash", i);
    if (i <= 0) return false;

    return (i != 0) && term->value(i - 1, j) && !term->value(i, j);
  }
};

class UnderlineTerm : public Term {
 private:
  Term *term;

 public:
  UnderlineTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("underline", i);
    if (i <= 0) return false;

    return (i != 0) && !term->value(i - 1, j) && !term->value(i, j);
  }
};

// functions
class PassedTerm : public Term {
 private:
  Term *term;

 public:
  PassedTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("passed", i);

    return (i >= j + term->value(i, j) - 1); // check it
  }
};

class ChangesTerm : public Term {
 private:
  Term *term;

 public:
  ChangesTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("changes", i);
    if (i <= 0) return false;

    return term->value(i - 1, j) != term->value(i, j);
  }
};

class IncreasesTerm : public Term {
 private:
  Term *term;

 public:
  IncreasesTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("increases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j) < term->value(i, j);
  }
};

class DecreasesTerm : public Term {
 private:
  Term *term;

 public:
  DecreasesTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("decreases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j) > term->value(i, j);
  }
};

class NotIncreasesTerm : public Term {
 private:
  Term *term;

 public:
  NotIncreasesTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("notincreases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j) <= term->value(i, j);
  }
};

class NotDecreasesTerm : public Term {
 private:
  Term *term;

 public:
  NotDecreasesTerm(Term *term) : term(term) {}
  int value(int i, int j) {
    debug("notdecreases", i);
    if (i <= 0) return false;

    return term->value(i - 1, j) >= term->value(i, j);
  }
};

// abstract class for the req
class CheckableReq {
 protected:
  std::string desc;

 public:
  CheckableReq() {}

  void setDesc(const std::string &desc) { this->desc = desc; }
  std::string &getDesc() { return desc; }

  virtual int trigger(int i, int j) = 0;
  virtual int invariant(int i, int j) = 0;
  virtual int reaction(int i, int j) = 0;
  virtual int release(int i, int j) = 0;
  virtual int delay(int i, int j) = 0;
  virtual int final(int i, int j) = 0;

  //bounded checking algorhitm
  bool check(int len) {
    int trig = 1;
    while (trig < len) {
      if (this->trigger(trig, 0)) {
        if (this->release(trig, trig)) goto checked;
        int fin = trig;
        while (!this->final(fin, trig)) {
          if (this->release(fin, trig)) goto checked;
          if (!this->invariant(fin, trig)) return false;
          fin++;
          if (fin == len) goto checked;
        }
        int del = fin;
        while (!this->delay(del, fin) && !this->reaction(del + 1, fin)) {
          if (this->release(del, trig)) goto checked;
          if (!this->invariant(del, fin)) return false;
          del++;
          if (del == len) goto checked;
        }
        if (!this->release(del, trig) && this->delay(del, fin) &&
            !this->invariant(del, fin))
          return false;
      }
    checked:
      trig++;
    }
    return true;
  }
};

class CASE1 : public CheckableReq
{
public:
    CASE1() { setDesc("If the dryer is on, then it turns off after no hands for 2 seconds"); }

    virtual int trigger(int i, int j)
    { // \H && D
        return (new AndTerm(new BackSlashTerm(new ValTerm(Vars::H)), (new ValTerm(Vars::D))))
            ->value(i, j);
    }

    virtual int release(int i, int j)
    { // H
        return (new ValTerm(Vars::H))->value(i, j);
    }

    virtual int final(int i, int j)
    { // passed 2s
        return (new PassedTerm(new ConstTerm(2)))->value(i, j);
    }

    virtual int delay(int i __unused, int j __unused)
    { // true
        return true;
    }

    virtual int invariant(int i, int j)
    { // D
        return (new ValTerm(Vars::D))->value(i, j);
    }

    virtual int reaction(int i, int j)
    { // !D
        return (new NegTerm(new ValTerm(Vars::D)))->value(i, j);
    }
};

class CASE2 : public CheckableReq {
 public:
  CASE2() {
    setDesc(
        "If the dryer was not turned on and hands appeared, it will turn on "
        "after no more than 1 cycle");
  }

  virtual int trigger(int i, int j)
  { // /H && !D
      return (new AndTerm(new SlashTerm(new ValTerm(Vars::H)), (new NegTerm(new ValTerm(Vars::D)))))
          ->value(i, j);
  }

  virtual int release(int i __unused, int j __unused) {  // false
    return false;
  }

  virtual int final(int i __unused, int j __unused) {  // true
    return true;
  }

  virtual int delay(int i __unused, int j __unused) {  // true
    return true;
  }

  virtual int invariant(int i, int j)
  { // !D
      return (new NegTerm(new ValTerm(Vars::D)))->value(i, j);
  }

  virtual int reaction(int i, int j)
  { // D
      return (new ValTerm(Vars::D))->value(i, j);
  }
};

class CASE3 : public CheckableReq {
 public:
  CASE3() {
    setDesc("If there are hands and the dryer is on, it will not turn off");
  }

  virtual int trigger(int i, int j)
  { // H && D
      return (new AndTerm(new ValTerm(Vars::H), new ValTerm(Vars::D)))->value(i, j);
  }

  virtual int release(int i __unused, int j __unused) {  // false
    return false;
  }

  virtual int final(int i, int j)
  { // !H
      return (new NegTerm(new ValTerm(Vars::H)))->value(i, j);
  }

  virtual int delay(int i __unused, int j __unused) {  // true
    return true;
  }

  virtual int invariant(int i, int j)
  { // D
      return (new ValTerm(Vars::D))->value(i, j);
  }

  virtual int reaction(int i __unused, int j __unused) {  // *
    return true;
  }
};

class CASE4 : public CheckableReq {
 public:
  CASE4() {
    setDesc(
        "If there are no hands and the dryer is not turned on, the dryer will "
        "not turn on until the hands appear");
  }

  virtual int trigger(int i, int j)
  { // !H && !D
      return (new AndTerm(new NegTerm(new ValTerm(Vars::H)), new NegTerm(new ValTerm(Vars::D))))
          ->value(i, j);
  }

  virtual int release(int i, int j)
  { // H
      return (new ValTerm(Vars::H))->value(i, j);
  }

  virtual int final(int i __unused, int j __unused) {  // false
    return false;
  }

  virtual int delay(int i __unused, int j __unused) {  // *
    return true;
  }

  virtual int invariant(int i, int j)
  { // !D
      return (new NegTerm(new ValTerm(Vars::D)))->value(i, j);
  }

  virtual int reaction(int i __unused, int j __unused) {  // *
    return true;
  }
};

class CASE5 : public CheckableReq {
 public:
  CASE5() { setDesc("The time of continuous work is no more than an hour"); }

  virtual int trigger(int i, int j)
  { // /D
      return (new SlashTerm(new NegTerm(new ValTerm(Vars::D))))->value(i, j);
  }

  virtual int release(int i, int j)
  { // \D
      return (new BackSlashTerm(new NegTerm(new ValTerm(Vars::D))))->value(i, j);
  }

  virtual int final(int i, int j) {                                // passed(1h)
    return (new PassedTerm(new ConstTerm(60 * 60)))->value(i, j);  //??
  }

  virtual int delay(int i __unused, int j __unused) {  // true
    return true;
  }

  virtual int invariant(int i __unused, int j __unused) {  // true
    return true;
  }

  virtual int reaction(int i, int j)
  { // \D
      return (new BackSlashTerm(new NegTerm(new ValTerm(Vars::D))))->value(i, j);
  }
};

class CheckableSystem
{
public:
    CheckableSystem(){};

    void addReqs(std::initializer_list<CheckableReq *> reqs)
    {
        for (auto req : reqs) {
            addReq(req);
        }
    }
    void addReq(CheckableReq *req) { reqs.push_back(req); }

    bool check()
    {
        bool ok = true;
        Havoc *havoc = Havoc::instance();
        for (unsigned c = 0; c < havoc->getCases(); c++) {
            havoc->setActiveCase(c);
            std::cout << "Checking test case " << c << " " << std::endl;
            int len = havoc->getCurrentMaxStep();
            for (auto req : this->reqs) {
                std::cout << "Checking '" << req->getDesc() << "' ";
                if (!req->check(len)) {
                    std::cout << "[failed]" << std::endl;
                    ok = false;
                } else {
                    std::cout << "[OK]" << std::endl;
                }
            }
        }
        return ok;
    }

private:
    std::list<CheckableReq *> reqs;
};

int main(int argc __unused, char *argv[] __unused)
{
    CheckableSystem *system = new CheckableSystem();
    Havoc *havoc = new Havoc();

    try {
        havoc->addTestVector(
            {TestVec{{0, 1, 1, 0, 0, 0}, Vars::H}, TestVec{{0, 0, 1, 1, 1, 0}, Vars::D}}); //good
        havoc->addTestVector({TestVec{{1, 1, 0, 0, 0, 0}, Vars::H},
                              TestVec{{1, 1, 0, 0, 1, 1}, Vars::D}}); //violates some requirements

        //different dimensions: will not be compiled
        //havoc->addVector(
        //    {TestVec{{1, 1, 0, 0, 0}, Vars::H}, TestVec{{1, 0, 1, 0}, Vars::D}}); //wrong
        //havoc->addVector({TestVec{{1, 1, 0, 0, 0}, Vars::H}}); //wrong

        system->addReqs({new CASE1(), new CASE2(), new CASE3(), new CASE4(), new CASE5()});

        if (system->check())
            std::cout << "System is safe" << std::endl;
        else
            std::cout << "! System is unsafe " << std::endl;

    } catch (std::invalid_argument(s)) {
        std::cout << "Exception " << s.what() << std::endl;
    }

    delete system;
    return 0;
}
