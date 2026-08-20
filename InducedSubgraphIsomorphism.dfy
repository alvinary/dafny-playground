/* Properties of relations */

ghost predicate Injective<A(!new, ==)>(R : set<(A, A)>)
{
    forall x, y, z, w :: (x, z) in R && (y, w) in R && x != y ==> z != w 
}

ghost predicate Symmetric<A(!new, ==)>(R : set<(A, A)>)
{
    forall x, y :: (x, y) in R ==> (y, x) in R 
}

/* Definition of induced subgraph isomorphism without terms using function application  */

ghost predicate InducedSubgraphIsomorphism<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall x, y, z, w :: (x, z) in F && (y, w) in F ==> ((x, y) in H <==> (z, w) in G)
}

// ======================================================================================================

/* 

This is a list of axioms, each with only three variables, 
which we show is equivalent to the definition of induced 
subgraph isomorphism.

If one encodes these axioms as CNFs restricting the
ranges of some variables to vertices that are already
neighbors in a graph, one can encode induced subgraph
isomorphism using O(diameter(H)|V||W|) and O(diameter(G)|V||W|) clauses,
where W is the set of vertices in G and V is the set of vertices in H.

This is close to the complexity of the standard encoding
for induced subgraph isomorphism.

 */

// O(|H_V| |G_V| delta(H))
ghost predicate InheritsImages<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall x, y, z :: (x, y) in H && (x, z) in F ==> (y, z) in Fn
}

// O(|H_V| |G_V| delta(H))
ghost predicate BlocksNonImages<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall x, y, z :: !((y, z) in Fn) && (x, y) in H ==> !((x, z) in F)
}

// O(|H_V| |G_V| delta(G))
ghost predicate InheritsImageNeighbors<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall y, z, w :: (y, z) in F && (z, w) in G ==> (y, w) in Fn
}


// O(|H_V| |G_V| delta(G))
ghost predicate NoImageNeighborNoNeighbor<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall x, z, w :: (x, z) in F && !((z, w) in G) ==> !((x, w) in Fn)
}

// O(|H_V| |G_V| delta(H))
ghost predicate NoNeighborNoImageNeighbor<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall x, y, z :: !((y, z) in F) && !((x, z) in Fn)  ==> !((x, y) in H)
}

// O(delta(G) |H_V| |G_V|)
ghost predicate DomainNeighbors<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, En : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall y, z, w :: (z, w) in G && (y, w) in F ==> (y, z) in En
}

// O(|H_V| |G_V| delta(H))
ghost predicate ExpectedNeighbors<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, En : set<(A, A)>)
requires Symmetric(H)
requires Symmetric(G)
requires Injective(F)
{
    forall x, y, z :: (y, z) in En && (x, z) in F && !((x, y) in H) ==> false
}

// ============================================================================================== //

/* 

What follows is the equivalence proof.

It is very straightforward and relies only in proving and summoning three simple lemmas.

 */

lemma CriterionLemmaPositive<A(!new, ==)>(x : A, y : A, z : A, w : A, H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>)
requires Injective(F)
requires Symmetric(G)
requires Symmetric(H)
requires H != {}
requires G != {}
requires F != {}
requires InheritsImages(H, G, F, Fn)
requires BlocksNonImages(H, G, F, Fn)
requires InheritsImageNeighbors(H, G, F, Fn)
requires NoImageNeighborNoNeighbor(H, G, F, Fn)
requires NoNeighborNoImageNeighbor(H, G, F, Fn)
requires (x, y) in H
requires (x, z) in F
requires (y, w) in F
ensures (w, z) in G
{
    assert (x, y) in H;
    assert InheritsImages(H, G, F, Fn) && (x, y) in H && (x, z) in F ==> (y, z) in Fn;
    assert InheritsImages(H, G, F, Fn) && (x, y) in H && (y, w) in F ==> (x, w) in Fn;
    if !((z, w) in G)
    {
        assert NoImageNeighborNoNeighbor(H, G, F, Fn) && !((z, w) in G);
        assert false;
    }
}

lemma CriterionLemmaNegative<A(!new, ==)>(x : A, y : A, z : A, w : A, H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>)
requires Injective(F)
requires Symmetric(G)
requires Symmetric(H)
requires H != {}
requires G != {}
requires F != {}
requires InheritsImages(H, G, F, Fn)
requires BlocksNonImages(H, G, F, Fn)
requires InheritsImageNeighbors(H, G, F, Fn)
requires NoImageNeighborNoNeighbor(H, G, F, Fn)
requires NoNeighborNoImageNeighbor(H, G, F, Fn)
requires !((w, z) in G)
requires (x, z) in F
requires (y, w) in F
ensures !((x, y) in H)
{
    assert InheritsImages(H, G, F, Fn) && (x, y) in H && (x, z) in F ==> (y, z) in Fn;
    assert InheritsImages(H, G, F, Fn) && (x, y) in H && (y, w) in F ==> (x, w) in Fn;
    if ((x, y) in H)
    {
        assert InheritsImageNeighbors(H, G, F, Fn);
        assert (x, y) in H;
        assert (y, z) in Fn;
        assert (z, w) in Fn;
        assert false;
    }
}

lemma CriterionEquivalence<A(!new, ==)>(x : A, y : A, z : A, w : A, H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>, En : set<(A, A)>)
requires Injective(F)
requires Symmetric(G)
requires Symmetric(H)
requires H != {}
requires G != {}
requires F != {}
requires InheritsImages(H, G, F, Fn)
requires BlocksNonImages(H, G, F, Fn)
requires InheritsImageNeighbors(H, G, F, Fn)
requires NoImageNeighborNoNeighbor(H, G, F, Fn)
requires NoNeighborNoImageNeighbor(H, G, F, Fn)
requires DomainNeighbors(H, G, F, En)
requires ExpectedNeighbors(H, G, F, En)
requires (x, z) in F
requires (y, w) in F
ensures (x, y) in H ==> (z, w) in G 
ensures (z, w) in G ==> (x, y) in H
{
    if (x, y) in H
    {
        CriterionLemmaPositive(x, y, z, w, H, G, F, Fn);
        assert (z, w) in G;
    }

    if !((x, y) in H)
    {
        if ((z, w) in H)
        {
            assert (x, z) in F;
            assert (y, w) in F;
            assert NoNeighborNoImageNeighbor(H, G, F, Fn);
            assert ExpectedNeighbors(H, G, F, En);
        }
        
    }
}

lemma CriterionLemma<A(!new, ==)>(H : set<(A, A)>, G : set<(A, A)>, F : set<(A, A)>, Fn : set<(A, A)>, En : set<(A, A)>)
requires Injective(F)
requires Symmetric(G)
requires Symmetric(H)
requires H != {}
requires G != {}
requires F != {}
requires InheritsImages(H, G, F, Fn)
requires BlocksNonImages(H, G, F, Fn)
requires InheritsImageNeighbors(H, G, F, Fn)
requires DomainNeighbors(H, G, F, En)
requires ExpectedNeighbors(H, G, F, En)
requires NoImageNeighborNoNeighbor(H, G, F, Fn)
requires NoNeighborNoImageNeighbor(H, G, F, Fn)
ensures InducedSubgraphIsomorphism(H, G, F)
{
    assert InheritsImages(H, G, F, Fn);

    forall x, y, z, w
    ensures (x, z) in F && (y, w) in F ==> ((x, y) in H <==> (z, w) in G)
    {
        if (((x, z) in F) && ((y, w) in F))
        {
            CriterionEquivalence(x, y, z, w, H, G, F, Fn, En);
            assert ((x, y) in H <==> (z, w) in G);
        }
        
        if !((x, z) in F) || !((y, w) in F)
        {
            assert !((x, z) in F && (y, w) in F);
            assert (x, z) in F && (y, w) in F ==> ((x, y) in H <==> (z, w) in F);
        } 
    }
}
