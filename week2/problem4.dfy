function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

lemma LemmaEvenExponent(b: int, e: int)
    requires e >= 0 && e % 2 == 0
    ensures Power(b, e) == Power(b * b, e / 2)
    decreases e
{
    if e == 0 {
        // Power(b,0) == 1 == Power(b*b,0)
    } else {
        // unfold two steps
        assert Power(b, e) == b * Power(b, e - 1);
        assert Power(b, e - 1) == b * Power(b, e - 2);
        assert Power(b, e) == (b * b) * Power(b, e - 2);

        // induction hypothesis
        LemmaEvenExponent(b, e - 2);
        assert Power(b, e - 2) == Power(b * b, (e - 2) / 2);

        // (e-2)/2 = e/2 - 1
        assert (e - 2) / 2 == e / 2 - 1;

        // expand RHS one step
        assert Power(b * b, e / 2) == (b * b) * Power(b * b, e / 2 - 1);

        // done
        assert Power(b, e) == Power(b * b, e / 2);
    }
}

lemma LemmaOddExponent(b: int, e: int)
    requires e > 0 && e % 2 == 1
    ensures Power(b, e) == b * Power(b * b, e / 2)
{
    assert Power(b, e) == b * Power(b, e - 1);
    LemmaEvenExponent(b, e - 1);
    assert Power(b, e - 1) == Power(b * b, (e - 1) / 2);
    assert (e - 1) / 2 == e / 2;
    assert Power(b, e) == b * Power(b * b, e / 2);
}

method FastPower(base: int, exp: int) returns (result: int)
    requires exp >= 0
    requires base > 0
    ensures result == Power(base, exp)
{
    var x := base;
    var n := exp;
    result := 1;

    while n > 0
        invariant 0 <= n <= exp
        invariant x > 0
        invariant result >= 1
        invariant result * Power(x, n) == Power(base, exp)
        decreases n
    {
        if n % 2 == 1 {
            LemmaOddExponent(x, n);
            result := result * x;
        } else {
            LemmaEvenExponent(x, n);
        }

        // square step
        assert x > 0;    // from invariant
        x := x * x;
        n := n / 2;
        assert x > 0;    // positivity preserved
    }

    assert Power(x, 0) == 1;
    assert result == Power(base, exp);
}
