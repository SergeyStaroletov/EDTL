bool trigger, reaction, release, final, invariant, delay;

mtype = {s_start, s_trigger1, s_release1, s_final, s_invariant1, s_fail, s_invariant2, s_reaction, s_delay, s_release2, s_trigger2};
mtype state = s_start;

bool gremlin_active = false;


inline read (){
    gremlin_active = true;
    printf ("doing some read...\n");
    gremlin_active = false;
}


active proctype edtl_gremlin() {
    do 
        ::gremlin_active -> 
            if
               ::true -> trigger = true;
               ::true -> trigger = false;
               ::true -> reaction = true;
               ::true -> reaction = false;
               ::true -> release = true;
               ::true -> release = false;
               ::true -> final = true;
               ::true -> final = false;
               ::true -> invariant = true;
               ::true -> invariant = false;
               ::true -> delay = true;
               ::true -> delay = false;
            fi
        ::else -> skip;
    od
}


active proctype edtl_automata() {

    do
        ::state == s_start -> {
            //init?
            state = s_trigger1;
        }
        ::state == s_trigger1 -> {
            if 
                ::trigger == false -> {
                    read();
                }
                ::else -> state = s_release1;
            fi
        }
        ::state == s_release1 -> {
            if 
                ::release == true -> {
                    read();
                    state = s_trigger1;
                }
                ::else -> state = s_final;
            fi
        }
        ::state == s_final -> {
            if
                ::final == false -> state = s_invariant1;
                ::else -> state = s_invariant2;
            fi
        }
        ::state == s_invariant1 -> {
            if
                ::invariant == true -> {
                    read();
                    state = s_release1;
                }
                ::else -> state = s_fail;
            fi
        }
        ::state == s_fail -> state = s_fail; //loop
        ::state == s_invariant2 -> {
            if
                ::invariant == false -> state = s_fail;
                ::else -> state = s_reaction; 
            fi
        }
        ::state == s_reaction -> {
            if
                ::reaction == true -> {
                    read();
                    state = s_trigger1;
                }
                ::else -> state = s_delay;
            fi
        }
        ::state == s_delay -> {
            if 
                ::delay == true -> state = s_fail;
                ::else -> {
                    read();
                    state = s_trigger2;
                }
            fi
        }
        ::state == s_trigger2 -> {
            if
                ::trigger == false -> state = s_release2;
                ::else -> state = s_release1;
            fi
        }
        ::state == s_release2 -> {
            if
                ::release == false -> state = s_invariant2;
                ::else -> {
                    read();
                    state = s_trigger1;
                }
            fi
        }
    od
}

ltl {[] (state!=s_fail)}