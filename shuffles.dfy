/* 

Here we'll prove that the shuffle operation is associative, which was very hard to prove in Isabelle.

This is to make an experiment, after noticing that proofs for SAT encodings (for instance, for the 
Tseitin encoding) look more straight forward and much shorter in Dafny, compared to Isabelle.

The proof works by defining a 'choice' function on lists and 'directions', mapping pairs of words
and a list of choices to words in the shuffle of the words in the pair, and mapping triples of words
and lists of choices to words in their shuffle (first with one bracketing, then the other).

Since every element in the shuffle of xs and ys is 'chosen' by picking the 'left' or 'right'
list at any given moment, there is a correspondence between lists of choices and elements
in the shuffle of two lists.

Perhaps this operation can be defined so that indices compose, or to be more general, 
but for the sake of simplicity we define 'trirections', take a projection (the left or
right projection), a 'remainder' projection, and use that to show (xs || (ys || zs)) = ((xs || ys) || zs)

LLRRRL RRRLLL


*/

// ===============================================================

/*

Lists, operations on lists, and some lemmas

Proving the length of a list is non-negative is important because proving some functions
terminate requires proving some functions of lists are bounded below by zero

*/

datatype Lista<A> = Cons(head : A, tail : Lista<A>)
                  | Nil

datatype Direction = L
                   | R

// Return the length of a list
function Length<A(==)>(list : Lista<A>) : nat
{
    match (list)
        case Nil => 0
        case Cons(x, xs) => 1 + Length(xs)
}

// Count occurences of 'element' in 'list'
function Count<A(==)>(element : A, list : Lista<A>) : nat
{
    match (list)
        case Nil => 0
        case Cons(x, xs) => if x == element then 1 + Count(element, xs) else Count(element, xs)
}

// Prove the length of a list is zero or greater
lemma CountNotNegative<A(==)>(x : A, xs : Lista<A>)
ensures Count(x, xs) >= 0
{
    match (xs)
        case Nil => {
            assert Count(x, Nil) == 0;
            assert Count(x, Nil) >= 0;
        }
        case Cons(z, zs) => {

        }
}

// Prove lists other than the empty list have a length greater than one
lemma NonzeroCount<A(==)>(x : A, xs : Lista<A>)
ensures Count(x, Cons(x, xs)) > 0
{
    CountNotNegative(x, xs);
    assert Count(x, Cons(x, xs)) == 1 + Count(x, xs);
}

// Map xs to the singleton {xs}
function Singleton<A(==)>(list : Lista<A>) : set<Lista<A>>
{
    {list}
}

// Define 'Prepend' for 'characters' and languages
function Prepend<A(==)>(elem : A, listtas : set<Lista<A>>) : set<Lista<A>>
{
    (set ls | ls in listtas :: Cons(elem, ls))
}

// Define the shuffle operation for lists
function Shuffle<A(==)>(xs : Lista<A>, ys : Lista<A>) : set<Lista<A>>
{
    match (xs, ys)
        case (Nil, Nil) => Singleton(Nil)
        case (Nil, ys) => Singleton(ys)
        case (xs, Nil) => Singleton(xs)
        case (Cons(x, ts), Cons(y, ss)) => Prepend(x, Shuffle(ts, ys)) + Prepend(y, Shuffle(xs, ss))
}


// Define the shuffle operation for languages (the set of shuffles of pairs in a product of languages)
function ProductShuffle<A(==)>(xs : set<Lista<A>>, ys : set<Lista<A>>) : set<Lista<A>>
{
    (set ls, rs, ss | ls in xs && rs in ys && ss in Shuffle(ls, rs) :: ss)
}

// Choose a shuffle given a sequence of 'direction choices'
// for instance, LLRR 'indexes' or 'chooses' the shuffle abcd from ab and cd,
// while RLLR 'chooses' cabd
function Choose<A(==)>(xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>) : Lista<A>
{
    match (xs, ys, ds)
        case (Nil, _, _) => ys
        case (_, Nil, _) => xs
        case (_, _, Nil) => Nil
        case (Cons(b, bs), ys, Cons(L, es)) => Cons(b, Choose(bs, ys, es))
        case (xs, Cons(c, cs), Cons(R, es)) => Cons(c, Choose(xs, cs, es))
}

// Suppose you choose a string z:zs from (x:xs || y:ys), taking the directions in d:ds each time.
// If d:ds makes chooses left first, then you get the suffix / tail zs by choosing with ds from (xs || y:ys).
// If d:ds makes chooses right first, then zs is the result of choosing ds from (x:xs || ys).
lemma ChoiceSuffix<A(==)>(xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires Even(xs, ys, ds)
requires ds != Nil
ensures ds.head == L ==> Choose(xs, ys, ds).tail == Choose(xs.tail, ys, ds.tail)
ensures ds.head == R ==> Choose(xs, ys, ds).tail == Choose(xs, ys.tail, ds.tail)
{
    
}

/* ============================================================================================================================================================== */

/* Shuffles can be said to have branches, in that, whenever a 
sequence belongs to the shuffle of x:xs and y:ys, it either 'chose'
x first, and belongs to the left branch, or 'chose' y first, and belongs
to the right branch. */

// Hence, we define the 'branch' of a shuffle where you get all shuffles beginning with the left choice...
function LeftBranch<A(==)>(xs : Lista<A>, ys : Lista<A>) : set<Lista<A>>
{
    match (xs, ys)
        case (Nil, Nil) => Singleton(Nil)
        case (Nil, ys) => Singleton(ys)
        case (xs, Nil) => Singleton(xs)
        case (Cons(x, ts), Cons(y, ss)) => Prepend(x, Shuffle(ts, ys))
}

// And the other branch, the one for words beginning with the right choice.
function RightBranch<A(==)>(xs : Lista<A>, ys : Lista<A>) : set<Lista<A>>
{
    match (xs, ys)
        case (Nil, Nil) => Singleton(Nil)
        case (Nil, ys) => Singleton(ys)
        case (xs, Nil) => Singleton(xs)
        case (Cons(x, ts), Cons(y, ss)) => Prepend(y, Shuffle(xs, ss))
}

// We note the whole shuffle is the union of those two branches.
// One must be mindful it is not a disjoint union, since branches may have a non-empty intersection.
lemma UnionOfBranchesIsWholeShuffle<A(==)>(xs : Lista<A>, ys : Lista<A>)
ensures LeftBranch(xs, ys) + RightBranch(xs, ys) == Shuffle(xs, ys)
{

}

// Note the length of the empty list is zero
lemma NilZero<A(==)>(ds : Lista<Direction>)
ensures Count(L, Nil) == 0
ensures Count(R, Nil) == 0
{

}

// ...and length is always positive ...
lemma LengthIsPositive<A(==)>(xs : Lista<A>)
ensures Length(xs) >= 0
{
    if (xs == Nil)
    {
        assert Length(xs) == 0;
        assert Length(xs) >= 0;
    }
}

// and n + 1 is always greater than n.
lemma PlusOneHigher(n : int)
ensures n + 1 > n
{

}

// One consequence of that is that Cons lists never have length zero.
lemma ConsLengthIsNonzero<A(==)>(xs : Lista<A>)
requires xs != Nil
ensures Length(xs) > 0
{

}

// Since Dafny does not a priori know the empty list is the only list 
// with length zero, we state that as a lemma.
lemma LengthZeroImpliesIsNil<A(==)>(xs : Lista<A>)
requires Length(xs) == 0
ensures xs == Nil
{
    if (Length(xs) > 0)
    {
        assert xs != Nil;
    }

    if (Length(xs) == 0)
    {
        if (xs != Nil)
        {
            ConsLengthIsNonzero(xs);
        }
    }
}

// As a corollary, lists with non-zero length are not the empty list.
lemma NonzeroLengthImpliesNotNil<A(==)>(xs : Lista<A>)
requires Length(xs) > 0
ensures xs != Nil
{

}

/* We now move on to some more lemmas establishing relations between choices and shuffles: */

// If a list of directions has |xs| 'lefts' and |ys| 'rights',
// then choosing from xs and ys using the 'directions' in ds gives
// you a shuffle.
lemma NilChoicesCheck<A(==)> (xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires ds == Nil
requires Count(L, ds) == Length(xs)
requires Count(R, ds) == Length(ys)
ensures Choose(xs, ys, ds) in Shuffle(xs, ys)
{
    assert Count(L, ds) == 0;
    assert Count(R, ds) == 0;
    assert Length(xs) == 0;
    assert Length(ys) == 0;
    LengthZeroImpliesIsNil(xs);
    LengthZeroImpliesIsNil(ys);
    assert xs == Nil;
    assert ys == Nil;
}

// If zs is in (xs || ys), then, hah! x:zs is in (x:xs || ys), and, in particular, on its left branch
lemma PrependLeftInLeftBranch<A(==)> (zs : Lista<A>, xs : Lista<A>, ys : Lista<A>)
requires zs in Shuffle(xs, ys)
ensures forall x : A :: Cons(x, zs) in LeftBranch(Cons(x, xs), ys)
{

}

// Same as before, but for the right branch
lemma PrependRightInRightBranch<A(==)> (zs : Lista<A>, xs : Lista<A>, ys : Lista<A>)
requires zs in Shuffle(xs, ys)
ensures forall y : A :: Cons(y, zs) in RightBranch(xs, Cons(y, ys))
{

}

// Another lemma associating choice suffixes with their shuffles:
lemma LeftChoiceCase<A(==)> (x : A, xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires xs != Nil
requires ds != Nil
requires ds.head == L
ensures Choose(xs, ys, ds) == Cons(xs.head, Choose(xs.tail, ys, ds.tail))
{
    match (xs, ys, ds)
        case (Nil, _, _) => assert false;
        case (_, Nil, _) => assert Choose(xs, ys, ds) == Cons(xs.head, Choose(xs.tail, ys, ds.tail));
        case (_, _, Nil) => assert false;
        case (Cons(z, zs), ys, Cons(L, cs)) => assert Choose(xs, ys, ds) == Cons(xs.head, Choose(xs.tail, ys, ds.tail));
        case (xs, Cons(c, cs), Cons(R, es)) => assert false;
}

// ... again, the same but for the right case.
lemma RightChoiceCase<A(==)> (x : A, xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires ys != Nil
requires ds != Nil
requires ds.head == R
ensures Choose(xs, ys, ds) == Cons(ys.head, Choose(xs, ys.tail, ds.tail))
{
    match (xs, ys, ds)
        case (Nil, _, _) => assert Choose(xs, ys, ds) == Cons(ys.head, Choose(xs, ys.tail, ds.tail));
        case (_, Nil, _) => assert false;
        case (_, _, Nil) => assert false;
        case (Cons(z, zs), ys, Cons(L, cs)) => assert false;
        case (xs, Cons(c, cs), Cons(R, es)) => assert Choose(xs, ys, ds) == Cons(ys.head, Choose(xs, ys.tail, ds.tail));
}

lemma PopoLeft<A(==)> (x : A, zs : Lista<A>, xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires zs == Choose(xs, ys, ds)
ensures Cons(x, zs) == Choose(Cons(x, xs), ys, Cons(L, ds))
{

}

lemma PrependLeftInChooseLefth<A(==)> (zs : Lista<A>, xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires zs == Choose(xs, ys, ds)
ensures forall x : A :: Cons(x, zs) == Choose(Cons(x, xs), ys, Cons(L, ds))
{

}

lemma LeftChoiceChecks<A(==)> (zs : Lista<A>, xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires zs in Shuffle(xs, ys)
requires zs == Choose(xs, ys, ds)
ensures forall x : A :: Choose(Cons(x, xs), ys, Cons(L, ds)) == Cons(x, zs)
{
    
}

/* This is the important part: */

// We say xs, ys and ds are 'even' if ds has |xs| lefts and |ys| rights
predicate Even<A(==)>(xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
{
    Count(R, ds) == Length(ys) && Count(L, ds) == Length(xs)
}

// We note left and right 'expansions' preserve eveness
lemma EvenExpandLeftIsEven<A(==)>(xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires Even(xs, ys, ds)
ensures forall x : A :: Even(Cons(x, xs), ys, Cons(L, ds))
{

}

lemma EvenExpandRightIsEven<A(==)>(xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires Even(xs, ys, ds)
ensures forall y : A :: Even(xs, Cons(y, ys), Cons(R, ds))
{

}

/* We'll prove by induction that even choices produce shuffles */

// Base case for the proof

lemma EvenZeroInShuffles<A(==)>(xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires Even(xs, ys, ds)
requires ds == Nil
ensures Choose(xs, ys, ds) in Shuffle(xs, ys)
{
    LengthZeroImpliesIsNil(xs);
    LengthZeroImpliesIsNil(ys);
}

lemma LeftExpansionInShuffles<A(==)>(zs : Lista<A>, xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>) 
requires zs in Shuffle(xs, ys)
requires zs == Choose(xs, ys, ds)
ensures forall x : A :: Cons(x, zs) in Shuffle(Cons(x, xs), ys)
{

}

lemma RightExpansionInShuffles<A(==)>(zs : Lista<A>, xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>) 
requires zs in Shuffle(xs, ys)
requires zs == Choose(xs, ys, ds)
ensures forall y : A :: Cons(y, zs) in Shuffle(xs, Cons(y, ys))
{

}

// Dafny proves that even choices are shuffles with surprising ease
lemma EvenChoiceInShuffles<A(==)>(xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires Even(xs, ys, ds)
ensures Choose(xs, ys, ds) in Shuffle(xs, ys)
{
    if (ds == Nil)
    {
        EvenZeroInShuffles(xs, ys, ds);
    }
}

// We note the shuffle of singletons yields the same language as the shuffle of lists
lemma SingletonProductIsShuffle<A(==)>(xs : Lista<A>, ys : Lista<A>)
ensures ProductShuffle({xs}, {ys}) == Shuffle(xs, ys)
{

}

// We relate the length of even lists and choices
// If xs, ys, and ds are even, then |ds| = |xs| + |ys|
lemma ChoiceLength<A(==)> (xs : Lista<A>, ys : Lista<A>, ds : Lista<Direction>)
requires Even(xs, ys, ds)
ensures Length(Choose(xs, ys, ds)) == Length(xs) + Length(ys)
{

}

// We will define a ternary analogue for even pairs and choices, treven triples and choices.

// We now define an analogue for directions, trirections, that let us choose from three sequences, the left, the middle, or right.
datatype Trirection = I
                    | M
                    | D

// The ternary analogue of eveness is treveness
predicate Treven<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ds : Lista<Trirection>)
{
    Count(I, ds) == Length(xs) && Count(M, ds) == Length(ys) && Count(D, ds) == Length(zs)
}

// We can interpret sequences of ternary choices over xs, ys and zs as compositions of binary
// choices with a different bracketings of xs, ys, and zs.
// This means we have mappings from ternary to binary choices that preserve shuffle choices.

// One of these bracketings is (xs || ys) || zs, the other is xs || (ys || zs).
// We call one the left projection, and the other the right projection.

function LeftProjection(ds : Lista<Trirection>) : Lista<Direction>
{
    match (ds)
        case Nil => Nil
        case Cons(I, cs) => Cons(L, LeftProjection(cs))
        case Cons(M, cs) => Cons(R, LeftProjection(cs))
        case Cons(D, cs) => LeftProjection(cs)
}

function RightProjection(ds : Lista<Trirection>) : Lista<Direction>
{
    match (ds)
        case Nil => Nil
        case Cons(I, cs) => RightProjection(cs)
        case Cons(M, cs) => Cons(L, RightProjection(cs))
        case Cons(D, cs) => Cons(R, RightProjection(cs))
}

// The following lemmas prove that projections indeed preserve shuffles.

// The proof is rather indirect: first we prove projections preserve
// the number of left, middle and right choices.
// Then we prove projections preserve certain relation between treveness and eveness,
// which in turn proves 'treven shuffles are shuffles'

// This will allow us to make some tedious and syntactically convoluted but conceptually simple proofs
// to nail the point that the shuffle of languages is associative.

lemma RightProjectionPreservesMChoices(ds : Lista<Trirection>)
ensures Count(M, ds) == Count(L, RightProjection(ds))
{

}

lemma RightProjectionPreservesRChoices(ds : Lista<Trirection>)
ensures Count(D, ds) == Count(R, RightProjection(ds))
{

}

lemma LeftProjectionPreservesIChoices(ds : Lista<Trirection>)
ensures Count(I, ds) == Count(L, LeftProjection(ds))
{

}

lemma LeftProjectionPreservesMChoices(ds : Lista<Trirection>)
ensures Count(M, ds) == Count(R, LeftProjection(ds))
{

}

function LeftComposition(ds : Lista<Direction>, cs : Lista<Direction>) : Lista<Trirection>
{
    match (ds)
        case Nil => Nil
        case Cons(L, es) => Cons(I, LeftComposition(es, cs))
        case Cons(R, es) =>
            (match cs
                case Nil => Nil
                case Cons(L, fs) => Cons(M, LeftComposition(es, fs))
                case Cons(R, fs) => Cons(D, LeftComposition(es, fs))
            )
}

function LeftRemainder (ds : Lista<Trirection>) : Lista<Direction>
{
    match (ds)
        case Nil => Nil
        case Cons(I, es) => Cons(L, LeftRemainder(es))
        case Cons(M, es) => Cons(L, LeftRemainder(es))
        case Cons(D, es) => Cons(R, LeftRemainder(es))
}

function RightRemainder (ds : Lista<Trirection>) : Lista<Direction>
{
    match (ds)
        case Nil => Nil
        case Cons(I, es) => Cons(L, RightRemainder(es))
        case Cons(M, es) => Cons(R, RightRemainder(es))
        case Cons(D, es) => Cons(R, RightRemainder(es))
}

function RightComposition(ds : Lista<Direction>, cs : Lista<Direction>) : Lista<Trirection>
{
    match (cs)
        case Nil => Nil
        case Cons(R, es) => Cons(D, RightComposition(ds, es))
        case Cons(L, es) =>
            (match ds
                case Nil => Nil
                case Cons(L, fs) => Cons(I, RightComposition(fs, es))
                case Cons(R, fs) => Cons(M, RightComposition(fs, es))
            )
}

// ================================================================================================================

lemma RightRemainderLengthInductive (ts : Lista<Trirection>)
ensures Length(RightRemainder(ts)) == Length(ts)
{
    match ts
        case Nil => assert Length<Trirection>(Nil) == Length(RightRemainder(Nil));
        case Cons(_, cs) => {
            assert Length<Trirection>(ts) == 1 + Length(cs);
            assert Length<Trirection>(ts) == 1 + Length(RightRemainder(cs));
        }
}

lemma LeftRemainderLengthInductive (ts : Lista<Trirection>)
ensures Length(LeftRemainder(ts)) == Length(ts)
{
    match ts
        case Nil => assert Length<Trirection>(Nil) == Length(LeftRemainder(Nil));
        case Cons(_, cs) => {
            assert Length<Trirection>(ts) == 1 + Length(cs);
            assert Length<Trirection>(ts) == 1 + Length(LeftRemainder(cs));
        }
}

lemma RightRemainderLength (ds: Lista<Direction>, ts : Lista<Trirection>)
requires ds == RightRemainder(ts)
ensures Length(ds) == Length(ts)
{
    RightRemainderLengthInductive(ts);
}

lemma LeftRemainderLength (ds: Lista<Direction>, ts : Lista<Trirection>)
requires ds == LeftRemainder(ts)
ensures Length(ds) == Length(ts)
{
    LeftRemainderLengthInductive(ts);
}

// ================================================================================================================

lemma RightProjectionsCompose (ts : Lista<Trirection>)
ensures LeftComposition(RightRemainder(ts), RightProjection(ts)) == ts
{

}

lemma LeftProjectionsCompose (ts : Lista<Trirection>)
ensures RightComposition(LeftProjection(ts), LeftRemainder(ts)) == ts
{

}

lemma IfRightProjectionsCompose (ds : Lista<Direction>, cs : Lista<Direction>, ts : Lista<Trirection>)
requires cs == RightRemainder(ts)
requires ds == RightProjection(ts)
ensures LeftComposition(cs, ds) == ts
{

}

lemma IfLeftProjectionsCompose (ds : Lista<Direction>, cs : Lista<Direction>, ts : Lista<Trirection>)
requires cs == LeftProjection(ts)
requires ds == LeftRemainder(ts)
ensures RightComposition(cs, ds) == ts
{
    
}

lemma RightProjectionCountL (ts : Lista<Trirection>)
ensures Count(L, RightProjection(ts)) == Count(M, ts)
{

}

lemma RightProjectionCountR (ts : Lista<Trirection>)
ensures Count(R, RightProjection(ts)) == Count(D, ts)
{

}

lemma LeftProjectionCountL (ts : Lista<Trirection>)
ensures Count(L, LeftProjection(ts)) == Count(I, ts)
{

}

lemma LeftProjectionCountR (ts : Lista<Trirection>)
ensures Count(R, LeftProjection(ts)) == Count(M, ts)
{

}

lemma RightRemainderCountL (ts : Lista<Trirection>)
ensures Count(L, RightRemainder(ts)) == Count(I, ts)
{

}

lemma RightRemainderCountR (ts : Lista<Trirection>)
ensures Count(R, RightRemainder(ts)) == Count(M, ts) + Count(D, ts)
{

}

lemma LeftRemainderCountL (ts : Lista<Trirection>)
ensures Count(L, LeftRemainder(ts)) == Count(I, ts) + Count(M, ts);
{

}

lemma LeftRemainderCountR (ts : Lista<Trirection>)
ensures Count(R, LeftRemainder(ts)) == Count(D, ts)
{

}

// ================================================================================================================

lemma TrevenImpliesRightEven<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures Even(ys, zs, RightProjection(ts))
{
    RightProjectionCountL(ts);
    RightProjectionCountR(ts);
    var right := RightProjection(ts);
    assert right == RightProjection(ts);
    assert Count (L, right) == Length(ys);
    assert Count (R, right) == Length(zs);
}

lemma TrevenImpliesLeftEven<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures Even(xs, ys, LeftProjection(ts))
{
    LeftProjectionCountL(ts);
    LeftProjectionCountR(ts);
    var left := LeftProjection(ts);
    assert left == LeftProjection(ts);
}

lemma TrevenImpliesRightRemainderEven<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures Even(xs, Choose(ys, zs, RightProjection(ts)), RightRemainder(ts))
{
    RightProjectionCountL(ts);
    RightProjectionCountR(ts);
    RightRemainderCountL(ts);
    RightRemainderCountR(ts);
    var right := RightProjection(ts);
    var remainder := RightRemainder(ts);
    var ws := Choose(ys, zs, RightProjection(ts));
    assert Count (L, remainder) == Length(xs);
    assert Count (R, remainder) == Length(ys) + Length(zs);
    TrevenImpliesRightEven(xs, ys, zs, ts);
    assert Even(ys, zs, right);
    ChoiceLength(ys, zs, right);
    assert Length(ws) == Length(ys) + Length(zs);
    assert Even(xs, ws, RightRemainder(ts));
}

lemma TrevenImpliesLeftRemainderEven<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures Even(Choose(xs, ys, LeftProjection(ts)), zs, LeftRemainder(ts))
{
    var left := LeftProjection(ts);
    assert left == LeftProjection(ts);
    var remainder := LeftRemainder(ts);
    var ws := Choose(xs, ys, LeftProjection(ts));
    LeftProjectionCountL(ts);
    LeftProjectionCountR(ts);
    LeftRemainderCountL(ts);
    LeftRemainderCountR(ts);
    assert Count (R, remainder) == Length(zs);
    assert Count (L, remainder) == Length(xs) + Length(ys);
    TrevenImpliesLeftEven(xs, ys, zs, ts);
    assert Even(xs, ys, left);
    ChoiceLength(xs, ys, left);
    assert Length(ws) == Length(xs) + Length(ys);
    assert Even(ws, zs, remainder);
}

// ==============================================================================================================


lemma ContainsRightProjection<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures Choose(ys, zs, RightProjection(ts)) in Shuffle(ys, zs)
{
    TrevenImpliesRightEven(xs, ys, zs, ts);
    EvenChoiceInShuffles(ys, zs, RightProjection(ts));
}

lemma ContainsLeftProjection<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures Choose(xs, ys, LeftProjection(ts)) in Shuffle(xs, ys)
{
    TrevenImpliesLeftEven(xs, ys, zs, ts);
    EvenChoiceInShuffles(xs, ys, LeftProjection(ts));
}

lemma RightShuffleParts <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ws : Lista<A>)
requires ws in Shuffle(ys, zs)
ensures forall alpha :: alpha in Shuffle(xs, ws) ==> alpha in ProductShuffle({xs}, ProductShuffle({ys}, {zs}))
{

}

lemma LeftShuffleParts <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ws : Lista<A>)
requires ws in Shuffle(xs, ys)
ensures forall alpha :: alpha in Shuffle(ws, zs) ==> alpha in ProductShuffle(ProductShuffle({xs}, {ys}), {zs})
{

}

// ================================================================================================================

function RightTrevenChoice<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>) : Lista<A>
{
    Choose(xs, Choose(ys, zs, RightProjection(ts)), RightRemainder(ts))
}

function LeftTrevenChoice<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>) : Lista<A>
{
    Choose(Choose(xs, ys, LeftProjection(ts)), zs, LeftRemainder(ts))
}

// ================================================================================================================


lemma RightShuffleInProductShuffle <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures RightTrevenChoice(xs, ys, zs, ts) in ProductShuffle({xs}, ProductShuffle({ys}, {zs}))
{
    
    var ws : Lista<A> := Choose(ys, zs, RightProjection(ts));
    var shuffle := Choose(xs, ws, RightRemainder(ts));
    ContainsRightProjection(xs, ys, zs, ts);
    assert Choose(ys, zs, RightProjection(ts)) in Shuffle(ys, zs);
    RightShuffleParts(xs, ys, zs, ws);
    TrevenImpliesRightEven(xs, ys, zs, ts);
    TrevenImpliesLeftEven(xs, ys, zs, ts);
    assert Even(ys, zs, RightProjection(ts));
    TrevenImpliesRightRemainderEven(xs, ys, zs, ts);
    assert Even(xs, ws, RightRemainder(ts));
    EvenChoiceInShuffles(xs, ws, RightRemainder(ts));
    assert shuffle in Shuffle(xs, ws);
    assert shuffle in ProductShuffle({xs}, ProductShuffle({ys}, {zs}));
}

lemma LeftShuffleInProductShuffle <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures LeftTrevenChoice(xs, ys, zs, ts) in ProductShuffle(ProductShuffle({xs}, {ys}), {zs})
{
    
    var ws : Lista<A> := Choose(xs, ys, LeftProjection(ts));
    var shuffle := Choose(ws, zs, LeftRemainder(ts));
    ContainsLeftProjection(xs, ys, zs, ts);
    assert Choose(xs, ys, LeftProjection(ts)) in Shuffle(xs, ys);
    LeftShuffleParts(xs, ys, zs, ws);
    TrevenImpliesLeftEven(xs, ys, zs, ts);
    TrevenImpliesRightEven(xs, ys, zs, ts);
    assert Even(xs, ys, LeftProjection(ts));
    TrevenImpliesLeftRemainderEven(xs, ys, zs, ts);
    assert Even(ws, zs, LeftRemainder(ts));
    EvenChoiceInShuffles(ws, zs, LeftRemainder(ts));
    assert shuffle in Shuffle(ws, zs);
    assert shuffle in ProductShuffle(ProductShuffle({xs}, {ys}), {zs});
}

// ================================================================================================================

lemma NilChoicesEqual <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
requires xs == Nil
requires ys == Nil
requires zs == Nil
requires ts == Nil
ensures LeftTrevenChoice(xs, ys, zs, ts) == RightTrevenChoice(xs, ys, zs, ts)
{

}

// We show certain 'head swaps' break treveness.
// This is useful to exclude certain cases when doing induction.

lemma TrevenBreak <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures forall y : A :: !Treven(xs, Cons(y, ys), zs, Cons(D, ts))
ensures forall y : A :: !Treven(xs, Cons(y, ys), zs, Cons(I, ts))
ensures forall z : A :: !Treven(xs, ys, Cons(z, zs), Cons(M, ts))
ensures forall z : A :: !Treven(xs, ys, Cons(z, zs), Cons(I, ts))
ensures forall x : A :: !Treven(Cons(x, xs), ys, zs, Cons(M, ts))
ensures forall x : A :: !Treven(Cons(x, xs), ys, zs, Cons(D, ts))
{

}

lemma TrevenChoicesTrevenIBis <A(==)> (x : A, xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(Cons(x, xs), ys, zs, Cons(I, ts))
ensures Treven(xs, ys, zs, ts)
{

}

lemma TrevenChoicesTrevenDBis <A(==)> (z : A, xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, Cons(z, zs), Cons(D, ts))
ensures Treven(xs, ys, zs, ts)
{

}

lemma TrevenChoicesTrevenMBis <A(==)> (y : A, xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, Cons(y, ys), zs, Cons(M, ts))
ensures Treven(xs, ys, zs, ts)
{

}



// =====================================================================

lemma HeadTrevenExpansion <A(==)> (x : A, xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures Treven(Cons(x, xs), ys, zs, Cons(I, ts))
ensures Treven(xs, Cons(x, ys), zs, Cons(M, ts))
ensures Treven(xs, ys, Cons(x, zs), Cons(D, ts))
{

}

lemma TrevenExpansion <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures forall x :: Treven(Cons(x, xs), ys, zs, Cons(I, ts))
ensures forall x :: Treven(xs, Cons(x, ys), zs, Cons(M, ts))
ensures forall x :: Treven(xs, ys, Cons(x, zs), Cons(D, ts))
{

}

// ==================================================================================================

lemma ExpansionLemma <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
requires LeftTrevenChoice(xs, ys, zs, ts) == RightTrevenChoice(xs, ys, zs, ts)
ensures forall x :: Treven(Cons(x, xs), ys, zs, Cons(I, ts))
ensures forall x :: Treven(xs, Cons(x, ys), zs, Cons(M, ts))
ensures forall x :: Treven(xs, ys, Cons(x, zs), Cons(D, ts))
ensures forall x :: LeftTrevenChoice(Cons(x, xs), ys, zs, Cons(I, ts)) == RightTrevenChoice(Cons(x, xs), ys, zs, Cons(I, ts))
ensures forall x :: LeftTrevenChoice(xs, Cons(x, ys), zs, Cons(M, ts)) == RightTrevenChoice(xs, Cons(x, ys), zs, Cons(M, ts))
ensures forall x :: LeftTrevenChoice(xs, ys, Cons(x, zs), Cons(D, ts)) == RightTrevenChoice(xs, ys, Cons(x, zs), Cons(D, ts))
{

}

// We say ts is a 'witness' of a shuffle if choosing from xs, ys and zs 'following' that witness yields that very same shuffle.

lemma WitnessExpansionLemma <A(==)> (zs : Lista<A>, xs : Lista<A>, ys : Lista<A>, ts : Lista<Direction>)
requires zs in Shuffle(xs, ys)
requires Choose(xs, ys, ts) == zs
ensures forall x :: Choose(Cons(x, xs), ys, Cons(L, ts)) in Shuffle(Cons(x, xs), ys)
ensures forall y :: Choose(xs, Cons(y, ys), Cons(R, ts)) in Shuffle(xs, Cons(y, ys))
{

}

//========================================================================

//========================================================================

lemma LeftRightChoicesNil <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires xs == Nil
requires ys == Nil
requires zs == Nil
requires ts == Nil
ensures LeftTrevenChoice(xs, ys, zs, ts) == RightTrevenChoice(xs, ys, zs, ts)
{

}

// This is the lemma establishing the equivalent choices from the left projection and the right projection are indeed equivalent.
// Since witneses are indexes of shuffles, we call it 'indexing lemma' in want of a better name.
lemma IndexingLemma <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
requires Treven(xs, ys, zs, ts)
ensures LeftTrevenChoice(xs, ys, zs, ts) == RightTrevenChoice(xs, ys, zs, ts)
{
    if (ts == Nil)
    {
        assert Length(xs) == Count(I, ts);
        assert Length(xs) == 0;
        LengthZeroImpliesIsNil(xs);
        assert xs == Nil;
        assert Length(ys) == Count(M, ts);
        assert Length(ys) == 0;
        LengthZeroImpliesIsNil(ys);
        assert ys == Nil;
        assert Length(zs) == Count(D, ts);
        assert Length(zs) == 0;
        LengthZeroImpliesIsNil(zs);
        assert zs == Nil;
        NilChoicesEqual(xs, ys, zs, ts);
        assert LeftTrevenChoice(xs, ys, zs, ts) == Nil;
        assert RightTrevenChoice(xs, ys, zs, ts) == Nil;
        assert LeftTrevenChoice(xs, ys, zs, ts) == RightTrevenChoice(xs, ys, zs, ts);
        LeftRightChoicesNil(xs, ys, zs, ts);
    }

    
    if (ts != Nil)
    {
        match ts
            case Cons(I, cs) => 
            {
                assert Length(xs) == Count(I, ts);
                CountNotNegative(I, ts);
                NonzeroCount(I, cs);
                assert Length(xs) > 0;
                NonzeroLengthImpliesNotNil(xs);
                assert xs != Nil;
                TrevenChoicesTrevenIBis(xs.head, xs.tail, ys, zs, ts.tail);
                assert Treven(xs.tail, ys, zs, ts.tail);
                TrevenChoicesTrevenIBis(xs.head, xs.tail, ys, zs, ts.tail);
                IndexingLemma(xs.tail, ys, zs, ts.tail);
            }
            case Cons(D, cs) => 
            {
                assert Length(zs) == Count(D, ts);
                CountNotNegative(D, ts);
                NonzeroCount(D, cs);
                assert Length(zs) > 0;
                NonzeroLengthImpliesNotNil(zs);
                assert zs != Nil;
                TrevenChoicesTrevenDBis(zs.head, xs, ys, zs.tail, ts.tail);
                IndexingLemma(xs, ys, zs.tail, ts.tail);
            }
            case Cons(M, cs) => 
            {
                assert Length(ys) == Count(M, ts);
                CountNotNegative(M, ts);
                NonzeroCount(M, cs);
                assert Length(ys) > 0;
                NonzeroLengthImpliesNotNil(ys);
                assert ys != Nil;
                TrevenChoicesTrevenMBis(ys.head, xs, ys.tail, zs, ts.tail);
                IndexingLemma(xs, ys.tail, zs, ts.tail);
            }
    }
}

// Some lemmas that help us relate sums of lengths for ternary choices and do induction over ternary choices

lemma LengthIsBoundedBelow<A(==)>(zs : Lista<A>, xs : Lista<A>, ys : Lista<A>)
ensures Length(zs) + Length(xs) + Length(ys) >= 0
{

}

lemma ElectionLemmaInductiveForward <A(==)>(zs : Lista<A>, xs : Lista<A>, ys : Lista<A>)
requires ys != Nil
requires zs != Nil
requires zs.head == ys.head
requires zs.tail in Shuffle(xs, ys.tail)
ensures zs in Shuffle(xs, ys)
{
}

lemma ElectionLemma<A(==)>(zs : Lista<A>, xs : Lista<A>, ys : Lista<A>)
requires zs in Shuffle(xs, ys)
ensures exists ts :: Choose(xs, ys, ts) == zs
decreases Length(zs) + Length(xs) + Length(ys)
{
    if (zs == Nil)
    {
        assert Choose(xs, ys, Nil) == zs;
        assert exists ts :: Choose(xs, ys, ts) == zs;
    }

    if (zs != Nil)
    {
        assert Choose(xs, ys, Witness(xs, ys, zs)) == zs;
        assert exists ts :: Choose(xs, ys, ts) == zs;
    }

}

lemma WitnessSuffixesLemma<A(==)>(x : A, xs : Lista<A>, ys : Lista<A>, zs : Lista<A>)
requires zs in Shuffle(xs, ys)
ensures Cons(x, zs) in Shuffle(Cons(x, xs), ys)
{

}

lemma FluffleLemma<A(==)>(x : A, xs : Lista<A>, yss : set<Lista<A>>, zs: Lista<A>)
requires zs in ProductShuffle({xs}, yss)
ensures Cons(x, zs) in ProductShuffle({Cons(x, xs)}, yss)
{
    assert zs in ProductShuffle({xs}, yss) ==> exists ms :: ms in yss && zs in Shuffle(xs, ms);
    var ms :| ms in yss && zs in Shuffle(xs, ms);
    WitnessSuffixesLemma(x, Cons(x, xs), ms, Cons(x, zs));
}

// Uniformity Lemma
lemma UniformityLemma<A(==)>(xs : Lista<A>, xss : set<Lista<A>>, yss :set<Lista<A>>)
requires {xs} <= xss
ensures forall zs : Lista<A> :: zs in ProductShuffle({xs}, yss) ==> zs in ProductShuffle(xss, yss)
{

}

// Expansion Uniformity Lemma
lemma ExpansionUniformityLemma<A(==)>(x : A, xs : Lista<A>, xss : set<Lista<A>>, yss :set<Lista<A>>, zs : Lista<A>)
requires {xs} <= xss
requires zs in ProductShuffle({xs}, yss)
ensures Cons(x, zs) in ProductShuffle({Cons(x, xs)}, yss)
{
    assert zs in ProductShuffle({xs}, yss) ==> exists ms :: ms in yss && zs in Shuffle(xs, ms);
    var ms :| ms in yss && zs in Shuffle(xs, ms);
    assert Cons(x, zs) in Shuffle(Cons(x, xs), ms);
}

// Le sacas un coso al witness, probas que el resultado es even
lemma Prepension<A(==)> (x : A, xs : Lista<A>, ys : Lista<A>, zs : Lista<A>)
requires zs in Shuffle(xs, ys)
ensures Cons(x, zs) in Shuffle(Cons(x, xs), ys) 
ensures Cons(x, zs) in Shuffle(xs, Cons(x, ys))
{

}

function Witness <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>) : Lista<Direction>
requires zs in Shuffle(xs, ys)
ensures Even(xs, ys, Witness(xs, ys, zs))
ensures Choose(xs, ys, Witness(xs, ys, zs)) == zs
{
    match (xs, ys, zs)
        case (Nil, Nil, Nil) => Nil
        case (Cons(b, bs), Nil, Cons(d, ds)) => Cons(L, Witness(xs.tail, ys, zs.tail))
        case (Nil, Cons(c, cs), Cons(d, ds)) => Cons(R, Witness(xs, ys.tail, zs.tail)) 
        case (Cons(b, bs), Cons(c, cs), Cons(d, ds)) => (
            if (b == d)
            then
                if (zs.tail in Shuffle(xs.tail, ys))
                    then Cons(L, Witness(xs.tail, ys, zs.tail)) 
                    else 
                        if (zs.tail in Shuffle(xs, ys.tail))
                            then Cons(R, Witness(xs, ys.tail, zs.tail))
                            else Nil
                
            else
                if (c == d)
                    then Cons(R, Witness(xs, ys.tail, zs.tail))
                    else Nil
        )
        case (_, _, _) => Nil
}

lemma EitherHead <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>)
requires zs != Nil
requires zs in Shuffle(xs, ys)
ensures (xs != Nil && zs.head == xs.head) || (ys != Nil && zs.head == ys.head)
{

}

lemma LeftPartialChoice <A(==)> (xs : Lista<A>, ys : Lista<A>, cs : Lista<Direction>)
requires Even(xs, ys, cs)
requires cs != Nil
requires xs != Nil
requires cs.head == L
ensures Choose(xs, ys, cs).tail == Choose(xs.tail, ys, cs.tail)
{

}

lemma RightPartialChoice <A(==)> (xs : Lista<A>, ys : Lista<A>, cs : Lista<Direction>)
requires Even(xs, ys, cs)
requires cs != Nil
requires ys != Nil
requires cs.head == R
ensures Choose(xs, ys, cs).tail == Choose(xs, ys.tail, cs.tail)
{

}

lemma ShuffleInclusion <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>, ts : Lista<Trirection>)
{
    if (Treven(xs, ys, zs, ts))
    {
        RightShuffleInProductShuffle(xs, ys, zs, ts);
        LeftShuffleInProductShuffle(xs, ys, zs, ts);
        var Left := LeftTrevenChoice(xs, ys, zs, ts);
        var Right := RightTrevenChoice(xs, ys, zs, ts);
        IndexingLemma(xs, ys, zs, ts);
        assert Left == Right;
        assert Left in ProductShuffle(ProductShuffle({xs}, {ys}), {zs});
        assert Left in ProductShuffle({xs}, ProductShuffle({ys}, {zs}));
        assert Right in ProductShuffle(ProductShuffle({xs}, {ys}), {zs});
        assert Right in ProductShuffle({xs}, ProductShuffle({ys}, {zs}));
    }
}

//========================================================================

//========================================================================

function NTimes <A(==, !new)> (a : A, n : nat) : Lista<A>
ensures Length(NTimes(a, n)) == n
ensures Count(a, NTimes(a, n)) == n
ensures forall b :: b != a ==> Count(b, NTimes(a, n)) == 0
{
    if n == 0
        then Nil
        else Cons(a, NTimes(a, n - 1))
}

function Concat <A(==, !new)> (xs : Lista<A>, ys : Lista<A>) : Lista<A>
ensures Length(Concat(xs, ys)) == Length(xs) + Length(ys)
ensures forall x :: Count(x, Concat(xs, ys)) == Count(x, xs) + Count(x, ys)
{
    if xs == Nil
        then ys
    else
        Cons(xs.head, Concat(xs.tail, ys))
}

// We make up a 'base witness' giving us a certain shuffle in order to prove the shuffle of nonempty strings is not empty
function BaseWitness <A(==)> (xs : Lista<A>, ys : Lista<A>) : Lista<Direction>
ensures Even(xs, ys, BaseWitness(xs, ys))
{
    Concat(NTimes(L, Length(xs)), NTimes(R, Length(ys)))
}

lemma NonEmptyShuffle <A(==)>(xs : Lista<A>, ys : Lista<A>)
requires xs != Nil
requires ys != Nil
ensures exists zs :: zs in Shuffle(xs, ys)
{
    var baseWitness : Lista<Direction> := BaseWitness(xs, ys);
    assert Even(xs, ys, baseWitness);
    EvenChoiceInShuffles(xs, ys, baseWitness);
    assert Choose(xs, ys, baseWitness) in Shuffle(xs, ys); 
}

lemma NonEmptyTernaryShuffle <A(==)> (xs : Lista<A>, ys : Lista<A>, zs : Lista<A>)
requires xs != Nil
requires ys != Nil
requires zs != Nil
ensures exists ws :: ws in ProductShuffle(ProductShuffle({xs}, {ys}), {zs})
{
    var XsYsWitness := BaseWitness(xs, ys);
    assert Even(xs, ys, XsYsWitness);
    EvenChoiceInShuffles(xs, ys, XsYsWitness);
    var XsYsShuffle := Choose(xs, ys, XsYsWitness);
    assert XsYsShuffle in Shuffle(xs, ys);
    assert XsYsShuffle in ProductShuffle({xs}, {ys});

    var XsYsZsWitness := BaseWitness(XsYsShuffle, zs);
    var XsYsZsShuffle := Choose(XsYsShuffle, zs, XsYsZsWitness);
    assert Even(XsYsShuffle, zs, XsYsZsWitness);
    EvenChoiceInShuffles(XsYsShuffle, zs, XsYsZsWitness);
    assert XsYsZsShuffle in Shuffle(XsYsShuffle, zs);
    assert XsYsZsShuffle in ProductShuffle({XsYsShuffle}, {zs});

    assert XsYsZsShuffle in ProductShuffle(ProductShuffle({xs}, {ys}), {zs});
    assert exists ws :: ws in ProductShuffle(ProductShuffle({xs}, {ys}), {zs});
}


// A shuffle in the product shuffle must come from a shuffle of a pair in the product of xss and yss
lemma SourcesLemma<A(==)> (zs : Lista<A>, xss : set<Lista<A>>, yss : set<Lista<A>>)
requires zs in ProductShuffle(xss, yss)
ensures exists xs, ys :: xs in xss && ys in yss && zs in Shuffle(xs, ys)
{

}

function rightTrevenWitness(ws : Lista<Direction>, rws : Lista<Direction>) : Lista<Trirection>
requires Count(R, ws) == Length(rws)
ensures Count(L, ws) == Count(I, rightTrevenWitness(ws, rws))
ensures Count(L, rws) == Count(M, rightTrevenWitness(ws, rws))
ensures Count(R, rws) == Count(D, rightTrevenWitness(ws, rws))
{
    match ws
        case Nil => Nil
        case Cons(L, wws) => Cons(I, rightTrevenWitness(wws, rws))
        case Cons(R, wws) => (
            match rws
                case Cons(L, rrws) =>
                    assert Count(R, ws) == Length(rws) ==> Count(R, ws.tail) == Length(rws.tail);
                    Cons(M, rightTrevenWitness(wws, rrws))

                case Cons(R, rrws) =>
                    assert Count(R, ws) == Length(rws) ==> Count(R, ws.tail) == Length(rws.tail);
                    Cons(D, rightTrevenWitness(wws, rrws))
        )
}

function leftTrevenWitness(lws : Lista<Direction>, ws : Lista<Direction>) : Lista<Trirection>
requires Count(L, ws) == Length(lws)
ensures Count(L, lws) == Count(I, leftTrevenWitness(lws, ws))
ensures Count(R, lws) == Count(M, leftTrevenWitness(lws, ws))
ensures Count(R, ws) == Count(D, leftTrevenWitness(lws, ws))
{
    match ws
        case Nil => Nil
        case Cons(R, wws) => Cons(D, leftTrevenWitness(lws, wws))
        case Cons(L, wws) => (
            match lws
                case Cons(L, llws) =>
                    assert Count(L, ws) == Length(lws) ==> Count(L, ws.tail) == Length(lws.tail);
                    Cons(I, leftTrevenWitness(lws.tail, ws.tail))
                case Cons(R, llws) =>
                    assert Count(L, ws) == Length(lws) ==> Count(L, ws.tail) == Length(lws.tail);
                    Cons(M, leftTrevenWitness(lws.tail, ws.tail))
        )
}

// Even sources implies treven witnesses (left)

lemma EvenSourcesYieldTrevenWitnessesLeft<A(==)>(xs : Lista<A>, 
                                                 ys : Lista<A>,
                                                 zs : Lista<A>,
                                                 vs : Lista<A>,
                                                 ws : Lista<Direction>,
                                                 rws : Lista<Direction>)
requires Choose(ys, zs, rws) == vs
requires Even(xs, vs, ws)
requires Even(ys, zs, rws)
requires Count(R, ws) == Length(rws)
ensures Treven(xs, ys, zs, rightTrevenWitness(ws, rws))
{

}

lemma EvenSourcesYieldTrevenWitnessesRight<A(==)>(xs : Lista<A>, 
                                                 ys : Lista<A>,
                                                 zs : Lista<A>,
                                                 vs : Lista<A>,
                                                 lws : Lista<Direction>,
                                                 ws : Lista<Direction>)
requires Choose(xs, vs, lws) == vs
requires Even(vs, zs, ws)
requires Even(xs, ys, lws)
requires Count(L, ws) == Length(lws)
ensures Treven(xs, ys, zs, leftTrevenWitness(lws, ws))
{

}

// Even sources implies treven witnesses (right)

// Now we prove the shuffle operation is associative

// Here I run out of human working memory, so I'll be back when I can focus proper!
lemma ShuffleIsAssociative<A(==)>(xs : Lista<A>, ys : Lista<A>, zs : Lista<A>)
requires xs != Nil
requires ys != Nil
requires zs != Nil
requires ProductShuffle({xs}, ProductShuffle({ys}, {zs})) != {} // odd, this asumption should not be necessary
ensures ProductShuffle({xs}, ProductShuffle({ys}, {zs})) == ProductShuffle(ProductShuffle({xs}, {ys}), {zs})
{
    var anyShuffle : Lista<A> :| anyShuffle in ProductShuffle({xs}, ProductShuffle({ys}, {zs}));
    var leftShuffle := ProductShuffle({xs}, ProductShuffle({ys}, {zs}));
    var rightShuffle := ProductShuffle(ProductShuffle({xs}, {ys}), {zs});
    // Primero el caso que no está vacio
    assert exists ws :: ws in ProductShuffle({xs}, ProductShuffle({ys}, {zs}));
    // We pick some shuffle from the left shuffle. Suppose it is called vs.
    var vs :| vs in ProductShuffle({xs}, ProductShuffle({ys}, {zs}));
    var righto := ProductShuffle({ys}, {zs});
    assert leftShuffle == ProductShuffle({xs}, righto);
    // That shuffle (vs) must be from the shuffle of xs and some other shuffle from (ys || zs) 
    SourcesLemma(vs, {xs}, righto);
    // Both must have a witness, so we can use those two binary witness to obtain a ternary witness for vs
    var rightSource :| rightSource in righto && vs in Shuffle(xs, rightSource);
    var vsWitness := Witness(xs, rightSource, vs);
    assert Choose(xs, rightSource, vsWitness) == vs;
    var rightSourceWitness := Witness(ys, zs, rightSource);
    assert Choose(ys, zs, rightSourceWitness) == rightSource;
    // To obtain it, we just map Ls to Ms and Rs to Rs, using the rightSourceWitness

    // Then make another binary witness zipping the rightwitness and the Rs in the witness for vs

    // Since witnesses are even with their sources, the whole ternary witness is treven

    // And that ternary witness has a right projection

    // Which must be even...

    // And from which we can obtain exactly vs, with the other bracketing

    // Since this is the case for every vs, we know the left shuffle is a subset of the right shuffle

    // And, by a completely analogue argument, the same, but the other way around (rshuffle <= lshuffle)

}
