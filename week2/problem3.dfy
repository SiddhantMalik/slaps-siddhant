method GCD(a: int, b: int) returns (gcd: int)
    requires a > 0 && b > 0
    ensures gcd > 0
    ensures a % gcd == 0 && b % gcd == 0
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd
{
    var x := a;
    var y := b;

    while y != 0
        decreases y
        invariant x > 0 || y > 0
        invariant gcdCandidate(x, y) > 0
        invariant (forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcdCandidate(x, y))
    {
        var temp := y;
        y := x % y;
        x := temp;
    }

    gcd := x;
}

// Auxiliary function to express gcd-like properties during loop
function gcdCandidate(x: int, y: int): int
    requires x > 0 || y > 0
{
    if y == 0 then x else gcdCandidate(y, x % y)
}
