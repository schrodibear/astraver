class Gcd {

    static int gcd(int x, int y) {
        while (y > 0) {
            int r = x % y;
            x = y;
            y = r;
        }
        return x;
    }

}
