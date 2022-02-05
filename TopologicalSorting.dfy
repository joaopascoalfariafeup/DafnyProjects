/*
 * Proof of correctness of the classic topological sorting algorithm (Kahn's algorithm),
 * simplified, in Dafny.
 * João Pascoal Faria (jpf@fe.up.pt), FEUP, January, 2022.
*/

// Defines a directed graph with vertices of any type T as a pair (V, E), where V is the 
// vertex-set and E is the edge-set. Each directed edge is represented by a pair of vertices. 
datatype Graph<T> = Graph(V: set<T>, E: set<(T,T)>) 

// Checks if G defines a valid graph (checks that E is a subset of V*V).           
predicate validGraph<T>(G: Graph<T>) {
  forall e :: e in G.E ==> e.0 in G.V && e.1 in G.V
}

// Checks if a graph is acyclic.
predicate acyclic<T>(G: Graph<T>) {
   ! exists v :: v in G.V && existsSimplePath(G, v, v) 
}

// Check if there is a non-empty simple path from vertex u to vertex v in graph G.
// (Currently, 'simple' means without repeated edges, but could be without repeated vertices).
predicate existsSimplePath<T>(G: Graph<T>, u: T, v: T)
  decreases G.E
{
  (u, v) in G.E || exists e :: e in G.E && e.0 == u && existsSimplePath(Graph(G.V, G.E-{e}), e.1, v) 
}


// Removes a vertex v and its incident edges from a graph G.
function method removeVertex<T>(v: T, G: Graph<T>) : Graph<T> {
    Graph(G.V - {v}, set e | e in G.E && e.0 != v && e.1 != v)
}  

// Checks if a sequence s of vertices is a topological ordering
// of the vertices of a graph G.
predicate isTopSorting<T>(s: seq<T>, G: Graph<T>) 
  requires validGraph(G)
{
  multiset(s) == multiset(G.V) 
  && forall i, j:: 0 <= i <= j < |s| ==> (s[j], s[i]) !in G.E  
}

// Checks if a vertex v in a graph G has incoming edges.
predicate method hasIncomingEdges<T>(G: Graph<T>, v: T) 
 requires v in G.V
{
  exists u :: u in G.V && (u, v) in G.E
}

// Topological sorting of the vertices of an acyclic directed graph.
// Returns a sequence (linear ordering) of the vertices in topological ordering.
method topsort<T>(G: Graph<T>) returns (s: seq<T>)
  requires validGraph(G) && acyclic(G)
  ensures isTopSorting(s, G)
{
  s := [];
  var R := G; // remaining graph
  while R.V != {} 
    // relation between s and R (basically, R = G - s)
    invariant R == Graph(set v | v in G.V && v !in s, set e | e in G.E && e.0 !in s && e.1 !in s)
    // s is a topological sorting of G - R 
    invariant multiset(s) == multiset(G.V - R.V) 
    invariant forall i, j:: 0 <= i <= j < |s| ==> (s[j], s[i]) !in G.E  
    // there are no edges from vertices in R to vertices in s 
    invariant forall i:: 0 <= i < |s| ==> forall v :: v in R.V ==> (v, s[i]) !in G.E  
    decreases R.V
  {
    // recall property: a subgraph of an ayclic graph is also acyclic 
    lemmaAcyclicSubgraph(R, G);

    // recall property: a vertex without incoming edges must exist in
    // a non-empty acyclic graph
    lemmaAcyclicIndegrees(R);

    // pick a vertex without incoming edges
    var v :| v in R.V && !hasIncomingEdges(R, v); 

    // append to the result
    s := s + [v];
     
    // remove that vertex and its outgoing edges from the graph
    R := removeVertex(v, R);
  }
}

/** SECOND LEMMA ***/

// States and proves by contradiction the following property: a non-empty acyclic graph 
// must have at least one vertex without incoming edges (0 indegree).  
lemma lemmaAcyclicIndegrees<T>(G: Graph<T>) 
  requires validGraph(G) && G.V != {} && acyclic(G)
  ensures exists v :: v in G.V && !hasIncomingEdges(G, v)
{
  // For the sake of contradiction, assume that all vertices have incoming edges.
  if forall v :: v in G.V ==> hasIncomingEdges(G, v) {
    // Then a path of any length can be built, possibly with repeated edges
    // and vertices, namely a path with length |G.V| + 1 
    var p := genPath(G, |G.V| + 1);
    // Such a path must have repeated vertices, and consequently at least one cycle
    lemmaPathLen(G, p);
    // So the graph is not acyclic, which contradicts the pre-condition
    assert ! acyclic(G);
  }
}

// Generates a valid path of a specified length n in a non-empty graph G
// in which all vertices have incoming edges.
// Because of this property, a path with any length may be constructed (possibly
// with repeated edges and vertices). 
lemma genPath<T> (G: Graph<T>, n: nat) returns (p: seq<T>)
  requires validGraph(G) && G.V != {}  
  requires forall v :: v in G.V ==> hasIncomingEdges(G, v)
  ensures |p| == n && validPath(p, G)
{
  p := [];
  while |p| < n
    invariant |p| <= n && validPath(p, G)
  {
    var u :| u in G.V && (p == [] || (u, p[0]) in G.E);
    p := [u] + p;
  }
}

// Checks if a sequence p of vertices defines a valid  path
// (allowing repeated vertices and edges) in a graph G.
predicate method validPath<T>(p: seq<T>, G: Graph<T>) {
   forall i :: 0 <= i < |p| ==> p[i] in G.V
         && (i < |p| - 1 ==> (p[i], p[i+1]) in G.E)
}

// States and proves the property: given a graph G and a path p in G, 
// if the length of p exceeds the number of vertices then G has cycles.  
lemma lemmaPathLen<T>(G: Graph<T>, p: seq<T>)
  requires validGraph(G) && validPath(p, G) && |p| > |G.V| 
  ensures !acyclic(G)
{
  // first notice that, if all vertices are distinct, the length of the path 
  // cannot exceed the number of vertices in G 
  if nodups(p) {
    lemmaSeqLen(p, G.V);
  }

  // consequently, there must exist repeated vertices in p, so we pick
  // a cyclic (complex) subpath 
  var i, j :| 0 <= i < j < |p| && p[i] == p[j];
  var p' := p[i .. j+1];

  // recall auxiliary lemma that assures that a simple cycle also exist
  lemmaComplexPath(G, p');
}

// States and proves (by induction) the property: given any valid complex path p (possibly with
// repeated edges and/or vertices) in a graph G, there exists a simple
// path (without repeated edges) in G from the first to the last vertex in the complex path. 
lemma lemmaComplexPath<T>(G: Graph<T>, p: seq<T>)
  requires G.V != {} && validPath(p, G) && |p| > 1
  ensures existsSimplePath(G, p[0], p[|p|-1])
  decreases p
{
  // handles case of first vertex repeated in the middle
  if i :| 1 <= i < |p|-1 && p[i] == p[0] {
    lemmaComplexPath(G, p[i..]);
  }
  // handles recursive case of proof by induction
  else if |p| > 2 {
    lemmaComplexPath(Graph(G.V, G.E - {(p[0], p[1])}), p[1..]);
  }
}

function elems<T>(s: seq<T>): set<T> {
  set x | x in s 
}

predicate nodups<T>(s: seq<T>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// States and proves (by induction) the following property: the length of a sequence p of 
// distinct elements from a set s cannot exceed the cardinality of the set.  
lemma lemmaSeqLen<T>(p: seq<T>, s: set<T>)
  requires nodups(p) && elems(p) <= s
  ensures |p| <= |s|
{
  if p != [] {
    lemmaSeqLen(p[1..], s - {p[0]});  
  }
}

/** FIRST LEMMA ***/

// States and proves (by contradiction) the following property: a subgraph G of
// an acyclic graph G' is also acyclic.
lemma lemmaAcyclicSubgraph<T>(G: Graph<T>, G': Graph<T>) 
  requires validGraph(G) && validGraph(G') && acyclic(G') && isSubGraph(G, G')  
  ensures acyclic(G)
{
  if ! acyclic(G) {
     var u :| u in G.V && existsSimplePath(G, u, u); // exists, by the definition of acyclic
     lemmaExistsSimplePath(G, G', u, u); // recall lemma implying that such a path also exists in G
     assert !acyclic(G'); // so, G would not be acyclic, contradicting the precondition
  }
}

// Checks if a graph G is a subgraph of another graph G'.
predicate isSubGraph<T>(G: Graph<T>, G': Graph<T>) {
  G.E <= G'.E && G.V <= G'.V
}

// States and proves (by induction) the following property: if there is a (simple) path u-->v
// in a graph G and G is a subgraph of G', then a path u-->v also exists in G'.
lemma lemmaExistsSimplePath<T>(G: Graph<T>, G': Graph<T>, u: T, v: T)
  requires validGraph(G) && validGraph(G') && isSubGraph(G, G') && existsSimplePath(G, u, v) 
  ensures existsSimplePath(G', u, v)
  decreases G.E
{ 
  if (u, v) !in G.E { // recursive case
    var e :| e in G.E && e.0 == u && existsSimplePath(Graph(G.V, G.E-{e}), e.1, v); // must exist by definition of existsPath
    lemmaExistsSimplePath(Graph(G.V, G.E-{e}), Graph(G'.V, G'.E-{e}), e.1, v); // this lemma implies that 'e' also exist in G' 
  } 
}

/** Test cases ***/
method testTopSortingSingleSolution() {
  var G: Graph<nat> := Graph({1, 2, 3}, {(1, 2), (2, 3)});
  assert validGraph(G) && acyclic(G);
  var s : seq<nat> := [1, 2, 3];
  assert isTopSorting(s, G);  
  var t := topsort(G);
  assert t == s;
}

method testTopSortingMultipleSolutions() {
  var G: Graph<nat> := Graph({1, 2, 3}, {(1, 2), (1, 3)});
  assert validGraph(G) && acyclic(G);
  var s1 : seq<nat> := [1, 2, 3];
  var s2 : seq<nat> := [1, 3, 2];
  assert isTopSorting(s1, G);  
  assert isTopSorting(s2, G);  
  var t := topsort(G);
  assert t == s1 || t == s2;
}
