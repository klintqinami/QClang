int main() {
	int a;
	float b;
	tup(int, float) c;

	/* test destructuring tuples */
	c = (42, 42.);
	(a, b) = c;
	print(a);
	printf(b);
	return 0;
}
