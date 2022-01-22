/*
 * Proof of correctness of the Hierholzer algorithm (1873) to find an Eulerian circuit in
 * an Eulerian graph (method findEulerCircuit).
 * Reference: https://en.wikipedia.org/wiki/Eulerian_path.
 * J. Pascoal Faria (jpf@fe.up.pt), FEUP, Jan/2022.
 */
 
/**** Graph representation and validity ****/
 
// Vertices can be of any type that supports equality.
type Vertex = nat // or other type
 
// Graph represented as a mapping from vertices to sets of adjacent vertices.
type Graph = m: map<Vertex, set<Vertex>> | definesValidGraph(m)
 
// The mapping must be anti-reflexive and symmetric.
predicate definesValidGraph(m: map<Vertex, set<Vertex>>) {
  forall v, w :: v in m && w in m[v] ==> w != v && w in m && v in m[w]
}
 
/**** Graph modification operations ****/
 
// Removes a vertex v from a graph G (if existent).
function rmvVertex(v: Vertex, G: Graph): Graph {
  map u | u in G && u != v :: G[u] - {v}
}
 
// Removes an edge (u, v) from a graph G (if existent).
function method rmvEdge(u: Vertex, v: Vertex, G: Graph): Graph 
  ensures var G' : Graph := rmvEdge(u, v, G);
          u in G && v in G && v in G[u] ==>
            hasEvenCard(G'[v]) != hasEvenCard(G[v]) 
            && hasEvenCard(G'[u]) != hasEvenCard(G[u]) 
{
  map x | x in G :: if x == u then G[x] - {v} else if x == v then G[x] - {u} else G[x]
}
 
// Adds and edge (u, v) to a graph G.
function addEdge(u: Vertex, v: Vertex, G: Graph): Graph
  requires u in G && v in G && u != v
{
  map x | x in G :: if x == u then G[x] + {v} else if x == v then G[x] + {u} else G[x]
}
 
/**** Subgraphs ****/
 
// Check if G1 is a subgraph of G2 in terms of edges, but with the same vertex-set.
predicate isSubgraphE(G1: Graph, G2: Graph) {
  G1.Keys == G2.Keys && forall x :: x in G1 ==> G1[x] <= G2[x]
}
 
/**** Connectivity ****/
 
// Checks if a given graph is connected, i.e., there is a path between every
// two vertices.  
predicate isConnected(G: Graph) {
  forall u, v :: u in G && v in G ==> connectedVertices(u, v, G)
}
 
// Checks if vertices u and v are connected in a graph G, i.e., there is a path
// connecting them (without repeated vertices).
predicate connectedVertices(u: Vertex, v: Vertex, G: Graph)
  requires u in G && v in G
  decreases G
{
  u == v || exists w :: w in G[u] && connectedVertices(w, v, rmvVertex(u, G))  
}
 
// Proves by induction that if a vertex u belongs to a closed vertex-set C
// (under adjacency) in a graph G and v does not, then they must be disconnected.
lemma unconnectedVerticesLemma(u: Vertex, v: Vertex, G: Graph, C: set<Vertex>)
  requires u in G && v in G && u in C && v !in C
  requires forall x :: x in C && x in G ==> G[x] <= C // C is a closed vertex-set
  decreases G
  ensures !connectedVertices(u, v, G)
{
  // mimics the structure of connectedVertices
  forall w | w in G[u] {
    unconnectedVerticesLemma(w, v, rmvVertex(u, G), C);
  }  
}
 
/**** Vertex degrees ****/
 
// Checks if all vertices in a graph G have even degree (even number of incident edges).
predicate hasEvenDegrees(G: Graph) {
  forall v :: v in G ==> hasEvenCard(G[v])
}
 
// Checks if a set s has an even number of elements (even cardinal).
predicate hasEvenCard<T>(s: set<T>) {
  |s| % 2 == 0
}
 
// If we remove from a graph G with even vertex degrees the edges of a subgraph T with
// even vertex degrees, we obtain a subgraph R with even vertex degrees.
lemma evenDegreesLemma(G: Graph, R: Graph, T: Graph)
   requires G.Keys == T.Keys == R.Keys
   requires forall x :: x in G ==> T[x] <= G[x] && R[x] == G[x] - T[x]
   requires hasEvenDegrees(G) && hasEvenDegrees(T)
   ensures hasEvenDegrees(R)
{ // Thanks Dafny
}
 
/*** Walks, trails, circuits and augmentation properties ****/
 
// Checks if a sequence s of vertices defines a valid walk in a graph G.
predicate isValidWalk(s: seq<Vertex>, G: Graph)  {  
  (forall x :: x in s ==> x in G)
  && (forall i :: 0 <= i < |s| - 1 ==> s[i+1] in G[s[i]])
}
 
// Usefull augmentation property of valid walks.
lemma walkAugmentationLemma(s: seq<Vertex>, G: Graph, u: Vertex)
  requires isValidWalk(s, G) && u in G && (|s| == 0 || u in G[s[|s|-1]])
  ensures isValidWalk(s + [u], G)
{ /* Thanks Dafny */ }
 
// Checks if a sequence s of vertices traverses an edge (u, v).
predicate traversesEdge(s: seq<Vertex>, u: Vertex, v: Vertex)
  requires u != v
{
  exists i :: 1 <= i < |s| && {s[i-1], s[i]} == {u, v}
}
 
// Useful augmentation property of traversed edges.  
lemma traversesEdgeProp(s: seq<Vertex>, v: Vertex)
  requires |s| > 0 && v != s[|s|-1]
  ensures traversesEdge(s + [v], s[|s|-1], v);
{
  // it seems the only thing Dafny needs is to show the "de-concatenation"
  assert var s' := s + [v]; s'[..|s|] == s && s'[|s|] == v;
}
 
// Checks if a sequence s of vertices defines a valid trail in a graph G,
// i.e., a valid walk without repeated edges.
predicate isValidTrail(s: seq<Vertex>, G: Graph) {  
    isValidWalk(s, G)
    && forall i :: 1 <= i < |s| ==> ! traversesEdge(s[..i], s[i-1], s[i])
}
 
// Usefull aumentation property of valid trails.
lemma trailAugmentationLemma(s: seq<Vertex>, G: Graph, u: Vertex)
  requires isValidTrail(s, G) && u in G
  requires |s| > 0 ==> u in G[s[|s|-1]] // to make valid walk
  requires |s| > 0 ==> !traversesEdge(s, s[|s|-1], u) // to make valid trail
  ensures isValidTrail(s + [u], G)
{ /* Thanks Dafny */ }
 
 
// Checks if a sequence s of vertices defines a valid circuit in a graph G,
// i.e., a non-empty trail in which the first and last vertices are identical.
predicate isValidCircuit(s: seq<Vertex>, G: Graph) {  
    isValidTrail(s, G) && |s| > 0 && s[|s|-1] == s[0]
}
 
// Shows that circuit augmentation (by embedding) implies the union of traversed edges.
lemma circuitAugmentationLemma1(s1: seq<Vertex>, i: int, s2: seq<Vertex>, s3: seq<Vertex>, G: Graph)
  requires isValidCircuit(s1, G) && isValidCircuit(s2, G)
  requires 0 <= i < |s1| && s2[0] == s1[i] && s3 == s1[..i] + s2 + s1[i+1..]
  ensures forall x, y :: x in G && y in G[x] ==> (traversesEdge(s3, x, y) <==> traversesEdge(s1, x, y) || traversesEdge(s2, x, y))
{
    // it seems the only thing Dafny needs is to show the "de-concatenation" (slicing)
    assert s1[..i] == s3[ .. i];
    assert s2 == s3[i .. i + |s2|];
    assert s1[i + 1 ..] == s3[i + |s2|..];
}
 
// Proves by deduction that circuit augmentation, by embedding another circuit with
// disjoint edges, results in a valid circuit, without repeated edges.
lemma circuitAugmentationLemma2(s1: seq<Vertex>, i: int, s2: seq<Vertex>, s3: seq<Vertex>, G: Graph)
  requires isValidCircuit(s1, G) && isValidCircuit(s2, G)
  requires 0 <= i < |s1| && s2[0] == s1[i] && s3 == s1[..i] + s2 + s1[i+1..]
  requires forall k :: 1 <= k < |s1| ==> !traversesEdge(s2, s1[k-1], s1[k])
  requires forall k :: 1 <= k < |s2| ==> !traversesEdge(s1, s2[k-1], s2[k])
  ensures isValidCircuit(s3, G)
{
  // mimics the procedure for checking existence of duplicate edges
  forall j, k | 1 <= j < k < |s3|  
    ensures {s3[k-1], s3[k]} != {s3[j-1], s3[j]}
    {
      // map to indices in original sequences
      var (j', sj) := if j <= i then (j, s1) else if j < i+|s2| then (j-i, s2) else (j-(|s2|-1), s1);
      var (k', sk) := if k <= i then (k, s1) else if k < i+|s2| then (k-i, s2) else (k-(|s2|-1), s1);
      // recall that edges are distinct in original sequences (from pre-conditions)
      assert {sk[k'-1], sk[k']} != {sj[j'-1], sj[j']};
    }

  
}
 
/*** Euler trails and circuits ****/
 
// Checks if a sequence s of vertices defines an Euler circuit in a graph G,
// i.e., a circuit that traverses each edge of G exactly once.
predicate isEulerCircuit(s: seq<Vertex>, G: Graph) {
  isValidCircuit(s, G) // already ensures no duplicate edge crossing
  && forall u, v :: u in G && v in G[u] ==> traversesEdge(s, u, v)
}
 
// Proves by contradiction that a non-augmentable circuit r in a connected
// graph G must cover all edges, i.e., must be an Euler circuit.
lemma nonAugmentableCircuitLemma(G: Graph, r: seq<Vertex>)
  requires isConnected(G) && isValidCircuit(r, G)
  requires forall x, y :: x in r && y in G[x] ==> traversesEdge(r, x, y)
  ensures isEulerCircuit(r, G)
{
   assert forall x, y :: x in r && y in G[x] ==> y in r; // implied by 2nd precondition
   if v :| v in G && v !in r {  
     unconnectedVerticesLemma(r[0], v, G, set x | x in r);
     // this contradicts the hypothesis that G is connected, so v cannot exist;
     // hence all vertices of G are covered by r, and hence their incident edges (by 2nd pre).
  }
}
 
// Checks if a sequence s of vertices defines an Euler trail in a graph G,
// i.e., a trail that traverses each edge of G exactly once.
predicate isEulerTrail(s: seq<Vertex>, G: Graph) {
   |s| > 0 && isValidTrail(s, G)
   && forall x, y :: x in G && y in G[x] ==> traversesEdge(s, x, y)
}
 
// Property of vertex degrees in an Euler trail: the number of incident edges on each
// vertex is even except for the first and last vertex if different.  
predicate EulerTrailDegrees(G: Graph, r: seq<Vertex>)
  requires isEulerTrail(r, G)
{
   var first, last := r[0], r[|r|-1];
   forall x :: x in G ==> ((x == first) != (x == last) /*xor*/ <==> !hasEvenCard(G[x]))
}

// Proves by induction the above property about the vertex degrees in an Euler trail.  
lemma EulerTrailLemma(G: Graph, r: seq<Vertex>)
   requires isEulerTrail(r, G)
   ensures EulerTrailDegrees(G, r)
{
  if |r| > 1 {
    EulerTrailLemma(rmvEdge(r[|r|-2], r[|r|-1], G), r[..|r|-1]);

    var G' : Graph := rmvEdge(r[|r|-2], r[|r|-1], G);
    var first := r[0];  
    var last := r[|r|-1]; 
    var last' := r[|r|-2]; 

    assert last != last';

    assert forall x :: x in G && x != first && x != last && x != last' ==> 
             hasEvenCard(G[x]);

    if first == last' {       
      assert hasEvenCard(G'[first]);
      assert ! hasEvenCard(G[first]);

      assert hasEvenCard(G'[last]); 
      assert !hasEvenCard(G[last]);
    }
    else { // firt != last'
      assert ! hasEvenCard(G'[first]);

      assert ! hasEvenCard(G'[last']);
      assert hasEvenCard(G[last']);

      if last == first {
        assert hasEvenCard(G[first]);
      }
      else {
        assert !hasEvenCard(G[first]); 
        assert hasEvenCard(G'[last]); 
        assert !hasEvenCard(G[last]);
      }
    }
  }
}


/**** Main algorithms ****/

// Hierholzer algorithm to find an Euler circuit in a non-empty Eulerian graph G
// based on depth-first search.
method findEulerCircuit(G: Graph) returns (r: seq<Vertex>)
  requires isConnected(G) && hasEvenDegrees(G) && |G| > 0
  ensures isEulerCircuit(r, G)
{
  // build initial circuit, starting in an arbitrary vertex, and obtain remaining graph
  var v :| v in G;
  var R : Graph;
  r, R := dfs(v, G);
 
  // Ghost variable to help proving termination (vertices to explore)
  ghost var V := set x| x in R && R[x] != {};
 
  // augment r as possible
  while exists i :: 0 <= i < |r| && R[r[i]] != {}
     // r is a valid circuit in G starting in v
     invariant isValidCircuit(r, G) && |r| > 0 && r[0] == v
 
     // R is a subgraph of G with even vertex degrees
     invariant hasEvenDegrees(R) && isSubgraphE(R, G)
 
     // R contains the edges not traversed by r in G
     invariant forall x,y::x in G && y in G[x] ==> (y !in R[x] <==> traversesEdge(r,x,y))
 
     // V (variant) is the set of vertices that have adjacent vertices not yet explored
     invariant V == set x | x in R && R[x] != {}
     decreases V
  {
     // select a vertex in r with outgoing edges to explore
     var i :| 0 <= i < |r| && R[r[i]] != {};
     var u := r[i];
 
     // memmorize old values needed later
     ghost var oldr, oldV := r, V;
 
     // do a DFS from this vertex in the remaining graph, obtaining a new subcircuit 
     // and remaining graph
     var c : seq<Vertex>;
     c, R  := dfs(u, R);
 
     // insert the subcircuit in the main circuit
     r := r[.. i] + c + r[i + 1..];  
 
     // recall circuit augmentation properties to make sure invariants are maintained
     circuitAugmentationLemma1(oldr, i, c, r, G); // union of traversed edges
     circuitAugmentationLemma2(oldr, i, c, r, G); // no duplicate edges
 
     // prove that the variant decreases
     V := set x | x in R && R[x] != {};
     assert u in oldV && u !in V;
     assert V < oldV;
  }
 
  // show that all edges of G have been traversed, because G is connected
  nonAugmentableCircuitLemma(G, r);
}

// By performing a depth-first search, produces a complete valid trail in a graph G
// starting in a vertex v. Assuming all vertices in the graph have even degree,
// the produced trail is circular. 
// Returns the circular trail (r) and the remaining graph R (with unexplored edges). 
method dfs(v: Vertex, G: Graph) returns (r: seq<Vertex>, R: Graph)
  requires hasEvenDegrees(G) && v in G  
  ensures isValidCircuit(r, G) && |r| > 0 && r[0] == v
  ensures isSubgraphE(R, G) && hasEvenDegrees(R)
  ensures forall x, y :: x in G && y in G[x] ==> (y !in R[x] <==> traversesEdge(r, x, y))
  ensures R[v] == {} // all successors of v have been explored
{
    R := G; // subgraph with edges remaining to be visited
    ghost var T: Graph := map x | x in G :: {}; // subgraph with edges already traversed
    
    // Ghost variable to help proving termination (edges remaining)
    ghost var E := set x, y | x in G && y in G[x] :: (x, y);

    // initiate the result with the initial vertex (also last vertex at this point) 
    r := [v];
    var u := v;

    // augment r as possible
    while R[u] != {}
      // R is a subgraph of G (with the same vertex-set)  
      invariant isSubgraphE(R, G) 
         
      // T is a subgraph of G with edges G - R  
      invariant T.Keys == G.Keys && forall x :: x in G ==> T[x] == G[x] - R[x]

      // E is the set of edges in R 
      invariant forall x, y :: x in R && y in R[x] <==> (x, y) in E

      // r is a sequence of vertices starting in v and ending in u   
      invariant |r| > 0 && r[0] == v && r[|r|-1] == u

      // r travers exactly the edges in T (without repetions)    
      invariant isValidTrail(r, T) 
      invariant forall x, y :: x in G && y in G[x] ==> (y in T[x] <==> traversesEdge(r, x, y))
 
      // variant to ensure termination
      decreases E
    {
        // select an adjacent vertex following an edge not previously visited 
        var w :| w in R[u];

        // recall some trail augmentation properties  
        trailAugmentationLemma(r, G, w); // valid trail
        traversesEdgeProp(r, w); // traversed edges

        // augment the trail and update visited and non-visited edges and last vertex
        r := r + [w];
        R := rmvEdge(u, w, R);
        T := addEdge(u, w, T);
        E := E - {(u, w), (w, u)};
        u := w;

    }

    // shows that the obtained trail (Euler trail in T) ends in the start vertex 
    assert T[u] == G[u]; // because R[u] == {}
    assert hasEvenCard(T[u]); // because hasEvenCard(G[u])
    EulerTrailLemma(T, r);
    assert u == v;

    // shows that in the remaining graph (R) all vertices have even degrees 
    assert hasEvenDegrees(T);
    evenDegreesLemma(G, R, T);
    assert hasEvenDegrees(R);   
}
