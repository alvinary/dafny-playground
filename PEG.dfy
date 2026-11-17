datatype PEG<A(==), B(==)> = Character(a : A)
                    | Concatenation(p1 : PEG<A, B>, p2: PEG<A, B>)
                    | OrderedAlternative(p1 : PEG<A, B>, p2: PEG<A, B>)
                    | Negation(p1 : PEG<A, B>)
                    | Preterminal(symbol : B)

datatype Position = Full(i : nat)
                  | Nil

function End<A(==), B(==, !new)>(expression : PEG<A, B>, sequence : seq<A>, index : nat, grammar : B -> PEG<A, B>, acc : set<B>, allPreterminals : set<B>) : Position
requires acc <= allPreterminals
requires LoopFree(expression, grammar, acc, allPreterminals)
decreases |ReachablePreterminals(expression, grammar, acc, allPreterminals)|, expression
ensures End(expression, sequence, index, grammar, acc, allPreterminals) != Nil <==> Match(expression, sequence, index, grammar, acc, allPreterminals)
{
  if index >= |sequence|
  then (match expression
        case Negation(p1) => Full(index)
        case _ => Nil)
  else match expression
    case Character(a) =>
      if sequence[index] == a then Full(index + 1) else Nil
    case Negation(p1) =>
      if End(p1, sequence, index, grammar, acc, allPreterminals) == Nil
      then Full(index) else Nil
    case OrderedAlternative(p1, p2) =>
      var r1 := End(p1, sequence, index, grammar, acc, allPreterminals);
      if r1 != Nil then r1
      else End(p2, sequence, index, grammar, acc, allPreterminals)
    case Concatenation(p1, p2) =>
      var r1 := End(p1, sequence, index, grammar, acc, allPreterminals);
      if r1 != Nil
      then End(p2, sequence, r1.i, grammar, acc, allPreterminals)
      else Nil
    case Preterminal(s) =>
      End(grammar(s), sequence, index, grammar, acc + {s}, allPreterminals)
}

predicate Match<A(==), B(==, !new)>(
    expression : PEG<A, B>, sequence : seq<A>, index : nat,
    grammar : B -> PEG<A, B>, acc : set<B>, allPreterminals : set<B>)
  requires acc <= allPreterminals
  requires LoopFree(expression, grammar, acc, allPreterminals)
  decreases |ReachablePreterminals(expression, grammar, acc, allPreterminals)|, expression, |sequence| - index
{
  if index >= |sequence|
  then (match expression
        case Negation(p1) => true
        case _ => false)
  else match expression
    case Character(a) => sequence[index] == a
    case Negation(p1) =>
      !Match(p1, sequence, index, grammar, acc, allPreterminals)
    case OrderedAlternative(p1, p2) =>
      Match(p1, sequence, index, grammar, acc, allPreterminals)
      || Match(p2, sequence, index, grammar, acc, allPreterminals)
    case Concatenation(p1, p2) =>
      Match(p1, sequence, index, grammar, acc, allPreterminals) &&
      Match(p2, sequence, End(p1, sequence, index, grammar, acc, allPreterminals).i,
            grammar, acc, allPreterminals)
    case Preterminal(s) =>
      Match(grammar(s), sequence, index, grammar, acc + {s}, allPreterminals)
}

ghost function ReachablePreterminals<A(==), B(==, !new)>(p : PEG<A, B>, f : B -> PEG<A, B>, acc : set<B>, uv : set<B>) : seq<B>
  requires acc <= uv
  decreases uv - acc, p
{
  match p
    case Character(a) => []
    case Negation(p1) => ReachablePreterminals(p1, f, acc, uv)
    case OrderedAlternative(p1, p2) =>
      ReachablePreterminals(p1, f, acc, uv) + ReachablePreterminals(p2, f, acc, uv)
    case Concatenation(p1, p2) =>
      ReachablePreterminals(p1, f, acc, uv) + ReachablePreterminals(p2, f, acc, uv)
    case Preterminal(s) =>
      if s in acc 
        then [s]
        else 
            if s !in uv 
                then []
                else [s] + ReachablePreterminals(f(s), f, acc + {s}, uv)
}

ghost predicate LoopFree<A(==), B(==, !new)>(p : PEG<A, B>, f : B -> PEG<A, B>, acc : set<B>, uv : set<B>)
  requires acc <= uv
  decreases uv - acc, p
{
    match p
        case Character(_) => 
            true
        case Negation(p1) => 
            LoopFree(p1, f, acc, uv)
        case OrderedAlternative(p1, p2) =>
            LoopFree(p1, f, acc, uv) && LoopFree(p2, f, acc, uv)
        case Concatenation(p1, p2) =>
            LoopFree(p1, f, acc, uv) && LoopFree(p2, f, acc, uv)
        case Preterminal(s) =>
            s in uv && s !in acc && LoopFree(f(s), f, acc + {s}, uv)
}

lemma LoopFreeNoHits<A(==), B(==, !new)>(p : PEG<A, B>, f : B -> PEG<A, B>, acc : set<B>, uv : set<B>)
    requires acc <= uv
    requires LoopFree(p, f, acc, uv)
    ensures forall t :: t in ReachablePreterminals(p, f, acc, uv) ==> t !in acc
    decreases uv - acc, p
{
    match p
        case Character(_) =>
        case Negation(p1) => 
            LoopFreeNoHits(p1, f, acc, uv);
        case OrderedAlternative(p1, p2) =>
            LoopFreeNoHits(p1, f, acc, uv); LoopFreeNoHits(p2, f, acc, uv);
        case Concatenation(p1, p2) =>
            LoopFreeNoHits(p1, f, acc, uv); LoopFreeNoHits(p2, f, acc, uv);
        case Preterminal(s) =>
            LoopFreeNoHits(f(s), f, acc + {s}, uv);
}
