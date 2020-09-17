//

bool trigger;
bool inv;
bool final;
bool react;
bool delay;
bool release;

//test case
#define max 3
bool  H[max] = {0, 1, 1, 1};
bool  D[max] = {0, 0, 1, 1};

//requirements for our system

inline Trigger(i) {
    trigger = H[i] && D[i];
}

inline Release(i) {
    release = false;
}

inline Final(i) {
    final = !H[i];
}

inline Invariant(i) {
    inv = D[i];
}

inline React(i) {
    react = false;
}

inline Delay(i) {
    delay = false;
}


bool flag;
active proctype main() 
{
   int i;

   //forall values in the testcase
   for (i : 0 .. max - 1) {
        //turn off the trigger at this step not to hold the formula
        flag = false;
        
        //calculate
        Release(i);
        Final(i);
        Invariant(i);
        React(i);
        Delay(i);

        Trigger(i);
        flag = true;
    }
}

ltl spec { [](flag -> (trigger->((([](inv && !final) || ((inv U (final && (inv U (react || delay))) && !delay W react))))))) }
