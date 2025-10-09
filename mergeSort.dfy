// Define merge sort for sequences of integers, and prove its output is sorted //

// Convert a sequence to a set
ghost function toSet<T(!new)>(s: seq<T>) : set<T>
ensures forall x :: x in s <==> x in toSet(s)
{
  set x | x in s
}

// Split a list in half, and return the right half
// (using integer division to decide where the middle is)
function rightSplit(xs : seq<int>) : seq<int>
ensures |xs| > 1 ==> |rightSplit(xs)| >= 1
ensures |xs| > 1 ==> |rightSplit(xs)| < |xs|
{
    xs[(|xs| / 2)..]
}

// Split a list in half, and return the left half
// (using integer division to decide where the middle is)
function leftSplit(xs : seq<int>) : seq<int>
ensures |xs| > 1 ==> |leftSplit(xs)| >= 1
ensures |xs| > 1 ==> |leftSplit(xs)| < |xs|
{
    xs[..(|xs| / 2)]
}

// Return a tuple with the head and tail of a list
function crack(xs : seq<int>) : (int, seq<int>)
requires |xs| >= 1
ensures [crack(xs).0] + crack(xs).1 == xs
ensures |crack(xs).1| < |xs|
ensures |crack(xs).1| == |xs| - 1
ensures sorted (xs) ==> sorted (crack(xs).1)
{
    (xs[0], xs[1..])
}

// Note a list is the concatenation of its left and right halves
lemma splitsAreSplits(xs : seq<int>)
ensures xs == leftSplit(xs) + rightSplit(xs)
{}

// Define what it is for a list to be sorted
predicate sorted (xs : seq<int>)
{
  forall i,j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
}

// Note the empty list is sorted
lemma emptyIsSorted(xs : seq<int>)
requires |xs| == 0
ensures sorted(xs)
{}

// Note singletons are always sorted too
lemma singletonIsSorted(xs : seq<int>)
requires |xs| == 1
ensures sorted(xs)
{}

// Note the length of x:xs ++ y:ys is strictly greater than the length of
// x:xs ++ ys and xs ++ y:ys 
lemma chipping(xs : seq<int>, ys : seq<int>)
requires |xs| >= 1
requires |ys| >= 1
ensures |[crack(xs).0] + crack(xs).1 + crack(ys).1| < |xs| + |ys|
ensures |[crack(ys).0] + crack(xs).1 + crack(ys).1| < |xs| + |ys|
{}

// Note sorted lists have sorted tails
lemma sortedSplit(xs : seq<int>, y : int, ys : seq<int>)
requires sorted(xs)
requires xs == [y] + ys
requires |xs| >= 1
ensures sorted(ys)
{
    assert sorted(xs) ==> sorted(xs[1..]);
    assert xs[1..] == ys;
    assert sorted(ys);
}

// If a list is sorted, the first element is less or equal 
// than all its other elements
lemma firstSmaller(xs : seq<int>, y : int, ys : seq<int>)
requires sorted(xs)
requires xs == [y] + ys
requires |xs| >= 1
ensures forall i :: 0 <= i < |ys| ==> y <= ys[i]
{
    sortedSplit(xs, y, ys);
    assert sorted(ys);
    assert y == xs[0];
    assert ys == xs[1..];
    assert forall i :: 0 <= i < |xs| ==> y <= xs[i];
}

// If a list is sorted, prepending an element smaller than
// all its other elements yields a sorted list
lemma sortedInsertion (x : int, xs : seq<int>)
requires sorted(xs)
requires forall i :: 0 <= i < |xs| ==> x <= xs[i]
ensures sorted([x] + xs)
{}

// Split a list into halves, return them in a tuple
function split(xs : seq<int>) : (seq<int>, seq<int>)
ensures |xs| == 0 ==> split(xs) == ([], [])
ensures |xs| > 1 ==> |split(xs).0| >= 1
ensures |xs| > 1 ==> |split(xs).1| >= 1
{
    (leftSplit(xs), rightSplit(xs))
}

// Note elements smaller than all elements in set(xs) are 
// smaller than all xs[i]
lemma sortingLemma (x : int, xs : seq<int>)
requires forall y :: y in xs ==> x <= y
ensures forall i :: 0 <= i < |xs| ==> x <= xs[i]
{
    assert forall i :: 0 <= i < |xs| ==> xs[i] in xs;
    assert forall i :: 0 <= i < |xs| ==> x <= xs[i];
}

// Prove mergeSort sorts a list of integers

// This actually proves something weaker (than the output of mergeSort(xs) is 
// sorted and that it contains all elements in xs). It does not prove the
// multisets are equal / that each element appears the right number of times

// Proving mergesort(xs) has the same length as xs would not cut it,
// because the sorted list could well contain extra copies of one element,
// and remove copies of another.

function merge(xs : seq<int>, ys : seq<int>) : seq<int>
requires sorted(xs)
requires sorted(ys)
ensures sorted(merge(xs, ys))
ensures toSet(merge(xs, ys)) == toSet(xs) + toSet(ys)
decreases |xs| + |ys|
{
    match (|xs|, |ys|)
        case (0, 0) => []
        case (0, r) => ys
        case (l, 0) => xs
        case (l, r) => 
            (match (crack(xs), crack(ys))
                case ((c, cs), (d, ds)) =>
                    assert |cs + ys| < |xs + ys|;
                    assert |xs + ds| < |xs + ys|;
                    assert sorted(cs);
                    assert sorted(ds);
                    firstSmaller(xs, c, cs);
                    firstSmaller(ys, d, ds);
                    assert forall z :: z in ys ==> d <= z; 
                    assert forall z :: z in xs ==> c <= z; 
                    if c < d
                        then
                            assert c < d;
                            assert forall z :: z in ys ==> c <= z;
                            assert forall x :: x in toSet(ys) ==> c <= x;
                            assert forall x :: x in toSet(cs)  ==> c <= x;
                            assert forall x :: x in toSet(ys) + toSet(cs) ==> c <= x;
                            assert forall z :: z in merge(cs, ys) ==> c <= z;
                            sortingLemma(c, merge(cs, ys));
                            sortedInsertion(c, merge(cs, ys));
                            assert sorted(merge(cs, ys)) ==> sorted([c] + merge(cs, ys));
                            [c] + merge(cs, ys)
                        else
                            assert d <= c;
                            assert forall z :: z in xs ==> d <= z; 
                            assert forall x :: x in toSet(xs) ==> d <= x;
                            assert forall x :: x in toSet(ds)  ==> d <= x;
                            assert forall x :: x in toSet(xs) + toSet(ds) ==> d <= x;
                            assert forall z :: z in merge(ds, xs) ==> d <= z;
                            sortingLemma(d, merge(xs, ds));
                            sortedInsertion(d, merge(xs, ds));
                            assert sorted(merge(xs, ds)) ==> sorted([d] + merge(xs, ds));
                            [d] + merge(xs, ds))
}

function mergeSort(xs : seq<int>) : seq<int>
ensures sorted(mergeSort(xs))
ensures toSet(xs) == toSet(mergeSort(xs))
decreases |xs|
{
    match (leftSplit(xs), rightSplit(xs))
        case (ls, rs) =>
            match (|ls|, |rs|)
                case (0, 0) => []
                case (_, 0) => ls
                case (0, _) => rs
                case (l, r) => merge(mergeSort(ls), mergeSort(rs))
}
