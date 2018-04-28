qubit u1(float lambda, qubit q) {
    return U(0., 0., lambda, q);
}

qubit u2(float phi, float lambda, qubit q) {
    return U(3.14159265 / 2., phi, lambda, q);
}

int main() {
    qubit q1;
    qubit q2;

		q1 = false;
		q2 = false;
    u1(1.618, q1);
    u2(3.268, 6.28, q2);
    return 0;
}
