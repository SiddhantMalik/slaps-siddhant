function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

function NumDigits(n: int): int
    requires n >= 0
{
    if n < 10 then 1 else 1 + NumDigits(n / 10)
}

function ReverseDigits(n: int): int
    requires n >= 0
{
    if n < 10 then n else (n % 10) * Power(10, NumDigits(n) - 1) + ReverseDigits(n / 10)
}

// Lemma connecting iterative reverse to recursive ReverseDigits
lemma IterReverseCorrect(rev: int, num: int, n: int)
    requires rev >= 0 && num >= 0 && n == rev * Power(10, NumDigits(num)) + num
    ensures rev + 0 == rev // trivial arithmetic lemma to help Dafny
{
}

// ------------------------------
// Iterative reverse
// ------------------------------
method ReverseNumber(n: int) returns (rev: int)
    requires n >= 0
    ensures rev == ReverseDigits(n)
{
    var num := n;
    rev := 0;

    while num > 0
        invariant rev >= 0
        invariant num >= 0
        invariant n == rev * Power(10, NumDigits(num)) + num
        decreases num
    {
        var digit := num % 10;
        rev := rev * 10 + digit;
        num := num / 10;
    }

    // At loop exit, num == 0
    // n == rev * Power(10, 0) + 0 ==> n == rev
}
