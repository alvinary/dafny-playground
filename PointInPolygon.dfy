/* 
We prove that counting the number of intersections between a ray cast from a point
and the boundaries of the polyon decides if the point lies within the polygon,
provided none of the edges crossed at the boundary are colinear with the ray.
*/

// We start by defining segments
datatype Segment = Line(origin : (real, real), end : (real, real))

// We then define a polygon as a sequence of edges, each of which begins where 
// the previous ends, modulo the sequence length
ghost predicate Polygon(p : seq<Segment>)
{
    forall i :: 0 <= i < |p| ==> p[i].end == p[(i + 1) % |p|].origin
}

// A polygon is a simple polygon if no two of its segments intersect
ghost predicate SymplePolygon(p : seq<Segment>)
requires Polygon(p)
{
    forall s, t :: s in p && t in p ==> !SegmentsIntersect(s, t)
}

// A polygon is a positive polygon if it lies squarely within the 'positive' quadrant of the plane
ghost predicate PositivePolygon(p : seq<Segment>)
{
    forall s :: s in p ==> s.origin.0 > 0.0 && s.origin.1 > 0.0 && s.end.1 > 0.0 && s.end.1 > 0.0
}

// This is relevant because if polygons are in the 'positive' quadrant, 
// we can be sure 'casting a ray can be defined as placing a segment 
// from the origin to the point.

// We say two segments intersect if we can find at least one point that lies on both segments.
ghost predicate SegmentsIntersect(s1 : Segment, s2 : Segment)
{
    exists t1 : real, t2: real :: 
        0.0 <= t1 <= 1.0 && 
        0.0 <= t2 <= 1.0 && 
        s1.origin.0 + t1 * (s1.end.0 - s1.origin.0) == s2.origin.0 + t2 * (s2.end.0 - s2.origin.0) &&
        s1.origin.1 + t1 * (s1.end.1 - s1.origin.1) == s2.origin.1 + t2 * (s2.end.1 - s2.origin.1)
}

// We define a concrete computation that decides if two segments intersect.
function CheckIntersection(a1 : real, a2 : real, b1 : real, b2 : real, c1 : real, c2 : real) : bool
{
    if (a1 * b2 - a2 * b1) == 0.0 then
        if (a1 * c2 - a2 * c1) == 0.0 && (b1 * c2 - b2 * c1) == 0.0 then true
            else false
        else true
}

// We prove that the computation indeed verifies the condition
lemma CheckIntersectionChecksIntersection(s1 : Segment, s2 : Segment) 
ensures CheckIntersection(s1.end.0 - s1.origin.0, s1.end.1 - s1.origin.1,
                          s2.origin.0 - s2.end.0, s2.origin.1 - s2.end.1, 
                          s2.origin.0 - s1.origin.0, s2.origin.1 - s1.origin.1) ==> SegmentsIntersect(s1, s2)
{
    var a1 := s1.end.0 - s1.origin.0;
    var a2 := s1.end.1 - s1.origin.1;
    var b1 := s2.origin.0 - s2.end.0;
    var b2 := s2.origin.1 - s2.end.1;
    var c1 := s2.origin.0 - s1.origin.0;
    var c2 := s2.origin.1 - s1.origin.1;

    var determinant := a1 * b2 - a2 * b1;

    if (determinant != 0.0 && a1 != 0.0)
    {
        var k := (a1 * c2 - a2 * c1) / determinant;
        var q := (c1 - b1 * k) / a1;
        assert (
            s1.origin.0 + q * (s1.end.0 - s1.origin.0) == s2.origin.0 + k * (s2.end.0 - s2.origin.0) &&
            s1.origin.1 + q * (s1.end.1 - s1.origin.1) == s2.origin.1 + k * (s2.end.1 - s2.origin.1)
        );
    }

    if (determinant != 0.0 && a1 == 0.0)
    {
        var k := (a1 * c2 - a2 * c1) / determinant;
        var q := (c2 - b2 * k) / a2;
        assert s1.end.0 == s1.origin.0;
        assert s1.origin.1 + q * (s1.end.1 - s1.origin.1) == s2.origin.1 + k * (s2.end.1 - s2.origin.1);
        assert q * (s1.end.0 - s1.origin.0) == 0.0;
        assert s1.origin.0 + q * (s1.end.0 - s1.origin.0) == s1.origin.0;
        assert s1.origin.0 + q * (s1.end.0 - s1.origin.0) == s2.origin.0 + k * (s2.end.0 - s2.origin.0);
    }

    if (determinant == 0.0 && (a1 * c2 - a2 * c1) == 0.0 && (b1 * c2 - b2 * c1) == 0.0)
    {
        assert true;
    }
    else {
        assert false;
    }
}

// And we define some shorthand notation for that:
function SegmentsCross(s1 : Segment, s2 : Segment) : bool
{
    CheckIntersection(
        s1.end.0 - s1.origin.0,
        s1.end.1 - s1.origin.1,
        s2.origin.0 - s2.end.0,
        s2.origin.1 - s2.end.1,
        s2.origin.0 - s1.origin.0,
        s2.origin.1 - s1.origin.1
    )
}

// For some reason, Dafny needs this as a separate lemma
lemma CrossedSegmentsCross(s1 : Segment, s2 : Segment)
ensures SegmentsCross(s1, s2) <==> CheckIntersection(
        s1.end.0 - s1.origin.0,
        s1.end.1 - s1.origin.1,
        s2.origin.0 - s2.end.0,
        s2.origin.1 - s2.end.1,
        s2.origin.0 - s1.origin.0,
        s2.origin.1 - s1.origin.1
    )
{
    CheckIntersectionChecksIntersection(s1, s2);
}

// And this too
lemma CrossedSegmentsIntersect(s1 : Segment, s2 : Segment)
ensures SegmentsCross(s1, s2) <==> SegmentsIntersect(s1, s2)
{
    CheckIntersectionChecksIntersection(s1, s2);
}

lemma UnaryCrossedSegmentsIntersect(s1 : Segment)
ensures forall s2 :: SegmentsCross(s1, s2) ==> SegmentsIntersect(s1, s2)
{
    var s2 :| true;
    {
        if (SegmentsCross(s1, s2))
        {
            assert SegmentsCross(s1, s2);
            CheckIntersectionChecksIntersection(s1, s2);
            assert SegmentsIntersect(s1, s2);
        }
        else
        {
            assert !SegmentsCross(s1, s2);
            CheckIntersectionChecksIntersection(s1, s2);
            assert !SegmentsIntersect(s1, s2);
        }
    }
    assert forall s2 :: SegmentsCross(s1, s2) ==> SegmentsIntersect(s1, s2);
}

// We define the ray cast from the point
function Fugue(point : (real, real)) : Segment
{
    Line(point, (0.0, 0.0))
}

// Define filter
function filter<T(==)>(xs: seq<T>, p: (T) -> bool): seq<T>
ensures forall x: T :: x in xs && p(x) ==> x in filter(xs, p)
ensures forall x: T :: x in filter(xs, p) ==> p(x)
ensures forall x: T :: x in filter(xs, p) ==> x in xs
{
  if xs == [] then []
  else if p(xs[0]) then [xs[0]] + filter(xs[1..], p)
  else filter(xs[1..], p)
}

// Note filtering on p is the same as filtering on q, if p ==> q
lemma FilterMaps<T(==)>(xs: seq<T>, p: (T) -> bool, q : (T) -> bool)
requires forall x :: p(x) ==> q(x)
ensures forall x: T :: x in filter(xs, p) ==> q(x)
{
  
}

// Get all segments with which the point will 'clash' in
// its 'fugue'
function BorderClashes(point : (real, real), polygon : seq<Segment>) : seq<Segment>
requires Polygon(polygon)
requires PositivePolygon(polygon)
ensures forall segment :: segment in BorderClashes(point, polygon) ==> SegmentsIntersect(Fugue(point), segment)
{
    UnaryCrossedSegmentsIntersect(Fugue(point));
    filter<Segment>(polygon, x => SegmentsCross(Fugue(point), x))
}

/*
predicate Inside(point : (real, real), polygon : seq<Segment>)
requires Polygon(polygon)
{
    BorderClashes(point, polygon).length % 2 == 1
}
*/

/*

Pending proof parts:

* Case where the determinant is zero
* Exclude segment ends from clashes
    * Define intersection for crossing segments, to get a point
* Excluding the end of every segment saves us from
  dealing with the special case of the ray hitting
  two distinct edges at the same time

Pending statements:

* Every (point, polygon) is equivalent to some 
  displaced (p', Polygon') st. Polygon' is a 
  positive polygon
* You can always find an angle that does not 
  clash with colinear edges
* An even number of border clashes really implies
  'being inside' (perhaps using a simplified version
   of the Jordan curve theorem)

*/
