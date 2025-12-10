pragma circom 2.0.0;

template Sqrt() {
    signal input in;
    signal output out;


    out <-- 0; // Just so it compiles
    out*out === in;
}

component main {public [in]} = Sqrt();