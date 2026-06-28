function Exp(n : nat, k : nat) : nat
requires k >= 0
{
    if k == 0
        then 1
        else n * Exp(n, k - 1)
}

lemma SwapOne(n : nat, k : nat, q : nat)
ensures Exp(n, k) * Exp (n, q + 1) == Exp(n, k + 1) * Exp(n, q)
{

}

lemma DropAll(n : nat, k : nat, q : nat)
ensures Exp(n, k) * Exp(n, q) == Exp(n, k - k) * Exp(n, q + k)
{
    if (k == 0)
    {
        assert Exp(n, 0) * Exp(n, q) == Exp(n, 0 - 0) * Exp(n, q + 0);
        assert Exp(n, k) * Exp(n, q) == Exp(n, k - k) * Exp(n, q + k);
    }

    if (k > 0)
    {
        SwapOne(n, k - 1, q + 1);
        DropAll(n, k - 1, q + 1);
    }

}

lemma ExponentsAdd(n : nat, k : nat, q : nat)
requires k >= 0
requires q >= 0
ensures Exp(n, k) * Exp(n, q) == Exp(n, k + q)
{
    assert k == 0 || k > 0;
    assert q == 0 || q > 0;

    if (k == 0 && q == 0)
    {
        assert Exp(n, k) == 1;
        assert Exp(n, q) == 1;
        assert Exp(n, k) * Exp(n, q) == Exp(n, k + q);
    }

    if (k == 0 && q > 0)
    {
        assert Exp(n, k) == 1;
        assert Exp(n, k) * Exp(n, q) == Exp(n, q);
        assert k + q == q;
        assert Exp(n, k) * Exp(n, q) == Exp(n, k + q);
    }

    if (k > 0 && q == 0)
    {
        assert Exp(n, q) == 1;
        assert Exp(n, k) * Exp(n, q) == Exp(n, k);
        assert k + q == k;
        assert Exp(n, k) * Exp(n, q) == Exp(n, k + q);
    }

    if (k > 0 && q > 0)
    {
        DropAll(n, k , q);
    }
}

lemma EvenPowerIsHalvesTwice(n : nat, k : nat)
requires k % 2 == 0
ensures Exp(n, k) == Exp(n, k / 2) * Exp(n, k / 2)
{
    ExponentsAdd(n, k /2, k / 2);
}

lemma EquivalenceA(n : nat, k : nat)
requires k % 2 == 1
ensures Exp(n, (k - 1) / 2) * Exp(n, (k - 1) / 2) * n == Exp(n, k)
{
    var q := (k - 1) / 2;
    ExponentsAdd(n, q, q);

}

lemma EquivalenceB(n : nat, k : nat, p : nat)
requires k % 2 == 1
requires p == Exp(n, (k - 1) / 2)
ensures Exp(n, k) == n * p * p
{
    EquivalenceA(n, k);
}

method FastExponentiation(n : nat, k : nat) returns (r : nat)
ensures r == Exp(n, k)
{
    assert k == 0 || k > 0; 

    if k == 0
    {
        r := 1;
        return;
    }

    assert k > 0;

    if k > 0
    {
        assert k % 2 == 0 || k % 2 == 1;

        if (k % 2 == 0)
        {
            var partial := FastExponentiation(n, k / 2);
            r := partial * partial;
            EvenPowerIsHalvesTwice(n, k);
            return;
        }
        if (k % 2 == 1)
        {
            assert Exp(n, k) == Exp(n, k - 1) * n;
            var q := (k - 1) / 2;
            assert 2 * q + 1 == k;
            var partial := FastExponentiation(n, q);
            r := n * partial * partial;
            assert partial == Exp(n, (k - 1) / 2);
            EquivalenceB(n, k, partial);
            return;
        }
    }
}