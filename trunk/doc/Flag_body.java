public void flag() {
    int b = 0, i = 0, r = t.length;
    /*@ loop_invariant
      @  (\forall int k; 0 <= k && k < t.length ==> isColor(t[k])) &&
      @  0 <= b && b <= i && i <= r && r <= t.length &&
      @  isMonochrome(0,b,BLUE) && isMonochrome(b,i,WHITE) &&
      @  isMonochrome(r,t.length,RED);
      @ decreases r - i; 
      @*/
    while (i < r) { 
	switch (t[i]) {
	case BLUE:  swap(b, i); b++; i++; break;      
	case WHITE: i++; break;
	case RED:   r--; swap(r, i); break;
	}
    }
}

