int main() {
    int c;
    float d;
		tup(int, float) e;
    c = 1;
    d = 1.;
    e = (c, d);
		print(e[0]);
		printf(e[1]);
    return 0;
}
