pragma circom 2.1.0;

template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

template BigIsZero(k) {
    signal input in[k];
    signal output out;

    component isZeros[k];
    var total = k;
    for (var i = 0; i < k; i ++) {
        isZeros[i] = IsZero();
        isZeros[i].in <== in[i];
        total -= isZeros[i].out;
    }
    component checkZero = IsZero();
    checkZero.in <== total;
    out <== checkZero.out;
}

// Nondet test case
component main = BigIsZero(2);
