/*
 * Proof of correctness of the classic topological sorting algorithm (Kahn's algorithm), simplified, in Dafny.
 * Difficulty: High.
 * FEUP, MIEIC, MFES, 2020/21.
 * TODO: Improve the definition of simple path.
*/

// Defines a directed graph with vertices of any type T as a pair (V, E), where V is the 
// vertex-set and E is the edge-set. Each directed edge is represented by a pair of vertices. 
datatype Graph<T> = Graph(V: set<T>, E: set<(T,T)>) 

// Checks if G defines a valid graph.           
predicate validGraph<T>(G: Graph<T>) {
  forall e :: e in G.E ==> e.0 in G.V && e.1 in G.V
}

// Checks if a graph is acyclic.
predicate acyclic<T>(G: Graph<T>) {
  ! exists v :: v in G.V && existsSimplePath(G, v, v) 
}

// Check if there is a non-empty simple path from vertex u to vertex v in graph G.
// (Currently, 'simple' means without repeated edges, but should be without repeated vertices).
predicate existsSimplePath<T>(G: Graph<T>, u: T, v: T)
  decreases G.E
{
  (u, v) in G.E || exists e :: e in G.E && e.0 == u && existsSimplePath(Graph(G.V, G.E-{e}), e.1, v) 
}

// Removes a vertex v and incident edges from a graph G.
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


// Topological sorting of the vertices of an acyclic directed graph.
// Returns a sequence (linear ordering) of the vertices in topological ordering.
method topsort<T>(G: Graph<T>) returns (s: seq<T>)
  requires validGraph(G) && acyclic(G)
  ensures isTopSorting(s, G)
{
  s := [];
  var G' := G; // remaining graph
  while G'.V != {} 
    // relation between s and G' (basically, G' = G - s)
    invariant G' == Graph(set v | v in G.V && v !in s, set e | e in G.E && e.0 !in s && e.1 !in s)
    // remaining graph keeps same properties of initial one
    invariant validGraph(G) && acyclic(G')
    // s is a topological sort of G - G' 
    invariant multiset(s) == multiset(G.V - G'.V) 
    invariant forall i, j:: 0 <= i <= j < |s| ==> (s[j], s[i]) !in G.E  
    // s is not any subset: there are no edges from vertices in G' to vertices in s 
    invariant forall i:: 0 <= i < |s| ==> forall v :: v in G'.V ==> (v, s[i]) !in G.E  
    decreases G'.V
  {
    // recalls property that a vertex without incoming edges must exist in a non-empty acyclic graph
    lemmaAcyclic(G');

    // pick a vertex without incoming edges
    var v :| v in G'.V && !exists u :: u in G'.V && (u, v) in G'.E; 

    // append to the result
    s := s + [v];
     
    // recalls property that removing a vertex from an ayclic graph produces an acyclic graph 
    lemmaRemoveVertex(v, G');

    // remove that vertex and its outgoing edges from the graph
    G' := removeVertex(v, G');
  }
}


/** FIRST LEMMA ***/

// States and proves the following property: a non-empty acyclic graph must have 
// at least one vertex without incoming edges (0 indegree).  
lemma lemmaAcyclic<T>(G: Graph<T>) 
  requires validGraph(G) && G.V != {} && acyclic(G)
  ensures exists v :: v in G.V && !exists u :: u in G.V && (u, v) in G.E
{
  // Do the proof by contradiction. 
  // Start by assuming that all vertices have incoming edges.
  if forall v :: v in G.V ==> exists u :: u in G.V && (u, v) in G.E {
    // Then a path of any length can be built, possibly with repeated edges
    // and vertices, namely a path with length |G.V| + 1 
    var p := genComplexPath(G, |G.V| + 1);
    // Such a path must have repeated vertices, and consequently at least one cycle
    lemmaComplexPathLen(G, p);
    // So the graph is not acyclic, which contradicts the pre-condition
    assert ! acyclic(G);
  }
}

// Generates a valid path of a specified length n in a non-empty graph G
// in which all vertices have incoming edges.
// Because of this property, a path with any length may be constructed (possibly
// with repeated edges and vertices). 
lemma genComplexPath<T> (G: Graph<T>, n: nat) returns (p: seq<T>)
  requires validGraph(G) && G.V != {}  
  requires forall v :: v in G.V ==> exists u :: u in G.V && (u, v) in G.E
  ensures validComplexPath(p, G) && |p| == n
{
  p := [];
  while |p| < n
    invariant 0 <= |p| <= n && validComplexPath(p, G)
  {
    var u :| u in G.V && (p == [] || (u, p[0]) in G.E);
    p := [u] + p;
  }
}

// Checks if a sequence p of vertices defines a valid complex path
// (allowing repeated vertices and edges) in a graph G.
predicate method validComplexPath<T>(p: seq<T>, G: Graph<T>) {
   forall i :: 0 <= i < |p| ==> p[i] in G.V
         && (i < |p| - 1 ==> (p[i], p[i+1]) in G.E)
}

// States and proves the property: given a non-empty graph G and a complex path p in G, 
// if the length of p exceeds the number of vertices then G has cycles.  
lemma lemmaComplexPathLen<T>(G: Graph<T>, p: seq<T>)
  requires validGraph(G) && G.V != {} && validComplexPath(p, G) && |p| > |G.V| 
  ensures !acyclic(G)
{
  // first notice that, if all vertices are distinct, the length of the path 
  // cannot exceed the number of vertices in G 
  if forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j] {
    lemmaSeqLen(p, G.V);
  }

  // consequently, there must exist repeated vertice in p, so we pick
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
  requires G.V != {} && validComplexPath(p, G) && |p| > 1
  ensures existsSimplePath(G, p[0], p[|p|-1])
  decreases p
{
  // handles case of first edge repeated
  if i :| 1 <= i < |p|-1 && p[i] == p[0] && p[i+1] == p[1] {
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

/** SECOND LEMMA ***/

// States and proves (by contradiction) the following property: removing a vertex 
// v from an acyclic graph G produces an acyclic graph. 
lemma lemmaRemoveVertex<T>(v: T, G: Graph<T>) 
  requires validGraph(G) && acyclic(G) && v in G.V 
  ensures acyclic(removeVertex(v, G))
{
  var G' := removeVertex(v, G);
  if ! acyclic(G') {
     var u :| u in G'.V && existsSimplePath(G', u, u); // exists, by the definition of acyclic
     lemmaExistsSimplePath(G', G, u, u); // recall lemma implying that such a path also exists in G
     assert !acyclic(G); // so, G would not be acyclic, contradicting the precondition
  }
}

// Checks if a graph G is a subgraph of another graph G'.
predicate isSubGraph<T>(G: Graph<T>, G': Graph<T>) {
  G.E <= G'.E && G.V <= G'.V
}

// States and proves (by induction) the following property: if there is a (simple) path u-->v in a graph G
// and G is a subgraph of G', then a path u-->v also exists in G'.
lemma lemmaExistsSimplePath<T>(G: Graph<T>, G': Graph<T>, u: T, v: T)
  requires validGraph(G) && validGraph(G') && isSubGraph(G, G') && u in G.V && v in G.V && existsSimplePath(G, u, v) 
  ensures existsSimplePath(G', u, v)
  decreases G.E
{ 
  if (u, v) !in G.E { // recursive case
    var e :| e in G.E && e.0 == u && existsSimplePath(Graph(G.V, G.E-{e}), e.1, v); // must exist by definition of existsPath
    lemmaExistsSimplePath(Graph(G.V, G.E-{e}), Graph(G'.V, G'.E-{e}), e.1, v); // this lemma implies that 'e' also exist in G' 
  } 
}