# EDTL
Event-driven temporal logic, test implementation  in C++

Initial article was published in <a href="https://link.springer.com/chapter/10.1007/978-3-030-89247-0_7">FSEN'21</a>

The Hand dryer is a simple control system which uses a hands sensor as an input and a dryer switching device as an output. 
Due to the blackbox principle, we abstract from the control logic and observe only the input and output values. 
We formulate the following requirements:

1. If the dryer is on, then it turns off after no hands are present for 1 second.
2. If the dryer was not turned on and hands appeared, it will turn on after no more than 1 cycle.
3. If the hands are present and the dryer is on, it will not turn off.
4. If there is no hands and the dryer is not turned on, the dryer will not turnon until the hands appear.
5. The time of continuous work is no more than an hour.

The requirenments are formulated and checked in C++ code in terms of EDTL. 

Implementation-specific issues will be discussed in a <a href="http://www.ict.nsc.ru/jct/site_content?l=eng">JCT article</a> (accepted).

```
CheckableSystem * system = new CheckableSystem();

system->addReqs({
    new CASE1(), new CASE2(), new CASE3(), new CASE4(), new CASE5()
});

havoc->addTestVector({
    TestVec{{0, 1, 1, 0, 0, 0}, Vars::H},
    TestVec{{0, 0, 1, 1, 1, 0}, Vars::D}
}); //good
havoc->addTestVector({
    TestVec{{1, 1, 0, 0, 0, 0}, Vars::H},
    TestVec{{1, 1, 0, 0, 1, 1}, Vars::D}
}); //violates some requirements

if (system->check())
    cout << "System is safe" << endl;
else
    cout << "System is unsafe " << endl;
```


