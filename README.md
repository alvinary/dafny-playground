## Sort a Sequence with Mergesort

`mergeSort.dfy` contains a short proof of correctness for mergesort that
more or less mimics a paper proof.

## Decide if a Point Lies Inside a Polygon

Suppose you wanted to check if a point is inside or outside a non-convex polygon.

There is a linear-time algorithm (informally known as 'ray-casting point-in-polygon'
or 'crossings number point-in-polygon') that solves the problem by casting a vertical
or horizontal ray straight from the point towards some point far away.

The idea is that, if you were a point inside a convex polygon, and you suddenly marched in a straight
line on a fixed direction, you'd 'run through' a wall just once, when exiting.

If you were outside the polygon, and marched towards it, you'd go through a wall once,
breaking into the polygon, and then a second time, breaking out. If you were outside,
and marched away from it, then you'd never touch any of its sides / you'd collide zero times.

So the parity of the number of crossings tells you where the point was, for convex polygons.

If the polygon is non-convex, nothing changes much, since whenever you cross a side of the polygon,
you 'switch' your inside/outside status. The point does not know if it was inside or outside
the polygon, but it can count the number of times it crosses an edge. 

If that number is even, then the point's initial location was inside the polygon, and if the
number of crossings is odd, then the polygon started inside.

The algorithm is surprisingly simple and the idea is very natural and intuitive, but
correct implementations require handling non-trivial corner cases properly, and the
algorithm involves geometry checks that are easy to get wrong.

One corner case is going through two edges at once (which happens when the ray 'hits'
an edge at one of its ends, where some other edge begins/ends too), and another
is going through another edge with not just one crossing (i.e. a colinear edge).

For instance, the point can 'start' outside a rectangle, and then go through a colinear
edge, and you'd count three edge collisions, but the polygon was outside. The point
can start from inside a colinear edge, and hit two edges (the colinear one and the 
adjacent one sharing a vertex), but it was inside, and so on.

Compared to the most widely known proof assistants, Dafny makes it surprisingly simple
to prove that a ray-casting algorithm counts crossings correctly (that is in 'PointInPolygon.dfy'),
but it is a bit harder to prove that the number of crossings is even iff the point lies outside the polygon.

In order to define what being outside or inside a polygon is, one may use a simplified
version of Jordan curves and the Jordan curve theorem, and say two points are in the
same equivalence class with respect to the polygon if one can connect them using a polyline
(a path connected by straight edges) without crossing any edge of the polygon.

Hence, we can define 'being outside the polygon' as being on the same equivalence
class of the origin (modulo some assumptions), without worrying too much about
proving that there are indeed just two equivalence classes, trusting the condition
provided as definition is indeed equivalent to the condition one intends to check.

