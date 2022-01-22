/* 
* Formal verification with Dafny of the Gale–Shapley algorithm to solve the stable marriage problem,
* both described in https://en.wikipedia.org/wiki/Stable_marriage_problem.
* Then, this algorithm is applied to solve the teachers placement problem that caused serious trouble in Portugal
* in 2004.
* J. Pascoal Faria, FEUP, Jan/2022.
*/

// Sequence without duplicates
type  useq<T> =  s: seq<T> | !hasDuplicates(s)

// Injective map
type  inmap<K, V> =  m: map<K, V> |  isInjective(m)

// Checks if a sequence 's' has duplicates.
predicate hasDuplicates<T>(s: seq<T>)  {
    exists i, j :: 0 <= i < j < |s| && s[i] == s[j]
}

// Checks if a map 'm' is injective, i.e., distinct values correspond to distinct keys. 
predicate isInjective<K,V>(m: map<K,V>) {
    forall i, j :: i in m && j in m && i != j ==> m[i] != m[j]
}

// Checks if element 'e1' precedes element 'e2' in sequence 's'. 
predicate method precedes<T(==)>(e1: T, e2: T, s: seq<T>) {
    exists i, j :: 0 <= i < j < |s| && s[i] == e1 && s[j] == e2
}

// Obtains the set of elements in a sequence
function elems<T>(s: useq<T>): set<T> 
{
    set i | 0 <= i < |s| :: s[i]
}

// Checks if a matching of couples is stable, knowing the preferences of men and women.
// I.e., there is no pair (m, w) that prefer each other as compared to their current situation. 
predicate isStable<Man, Woman>(couples: inmap <Man, Woman>, menPrefs: map<Man, useq<Woman>>, womenPrefs: map <Woman, useq<Man>>)   
{
    ! exists m, w :: m in menPrefs && w in womenPrefs &&
         w in menPrefs[m] && m in womenPrefs[w] &&
        (m in couples ==> precedes(w, couples[m], menPrefs[m]))
        && (forall m' :: m' in couples && couples[m'] == w ==> precedes(m, m', womenPrefs[w]))          
}

// Stable matching by the Gale–Shapley algorithm with incomplete lists (and no ties).
// Receives the lists of preferences of men and women and returns the couples created.
// Time complexity (with proper data structures) is O(|M|*|W|), where W is the set of women and M the set of men. 
// The types Man and Woman are defined as type parameters because their internal structure is not relevant here.
method stableMatching<Man, Woman>(menPrefs: map<Man, useq<Woman>>, womenPrefs: map <Woman, useq<Man>>) 
         returns(couples: inmap <Man, Woman>) 
  // P1: women referenced in men preferences must exist 
  requires forall m :: m in menPrefs ==> forall w :: w in menPrefs[m] ==> w in womenPrefs
  // P2: women referenced in women preferences must exist 
  requires forall w :: w in womenPrefs ==> forall m :: m in womenPrefs[w] ==> m in menPrefs
  // Q1: men and women can be engaged only if they are mentioned in each others preferences 
  ensures forall m :: m in couples ==> var w  := couples[m];
       m in menPrefs && w in womenPrefs && w in menPrefs[m] && m in womenPrefs[w]
  // Q2: stable marriage (and maximality)
  ensures isStable(couples, menPrefs, womenPrefs)
{
    // Initiate the result as empty
    couples  := map[];

    // Intitalize the men preferences already explored as empty
    var menPrefsExplored  := map m | m in menPrefs :: [];

    // Ghost variable used for proving termination with Dafny (instead of menPrefsExplored, that has a too complex structure)
    ghost var unexploredPairs := set m, w | m in menPrefs && w in menPrefs[m] :: (m, w);

    // while exists a free man m who still has a woman w to propose to
    while exists m :: m in menPrefs && m !in couples && menPrefsExplored[m] < menPrefs[m]
      decreases unexploredPairs
      // I1: lists in menPrefsExplored must be sublists in menPrefs 
      invariant forall m :: m in menPrefsExplored ==> m in menPrefs && menPrefsExplored[m] <= menPrefs[m]
      // I2: all men refereced in menPrefs also exist in menPrefsExplored (even with empty list) 
      invariant forall m :: m in menPrefs ==> m in menPrefsExplored
      // I3: to assure Q1 (incrementally, with menPrefsExplored) 
      invariant forall m :: m in couples ==> var w  := couples[m];
          m in menPrefsExplored && w in menPrefsExplored[m] && w in womenPrefs && m in womenPrefs[w]
      // I4: to assure Q2 (incrementally, with menPrefsExplored)
      invariant isStable(couples, menPrefsExplored, womenPrefs)
      // I5: while engaged, men do not propose to further women (needed to prove that isStable is maintained)
      invariant forall m :: m in couples ==> couples[m] == last(menPrefsExplored[m]) 
      // I6: invariant to ensure that the update statement decreases unexploredPairs
      invariant forall m, w :: m in menPrefs && w in menPrefs[m] && w !in menPrefsExplored[m] ==> (m, w) in unexploredPairs
    {
        // select a man in such condition
        var m :| m in menPrefs && m !in couples && menPrefsExplored[m] < menPrefs[m];  

        // select the first woman on m’s list to whom m has not yet proposed
        var w := nth(menPrefs[m], |menPrefsExplored[m]|); 

        // if w is not free (i.e., some pair (m', w) already exists)
        if m' :| m' in couples && couples[m'] == w
        { 
            // if w prefers m to m'
            if m in womenPrefs[w] && precedes(m, m', womenPrefs[w])
            {
                // m' becomes free
                couples := map x | x in couples && couples[x] != w :: couples[x];

                // (m, w) become engaged
                couples := couples[m := w];
            }
        }
        else // w is free
        {
            // if w is interested in m
            if m in womenPrefs[w]
            {
                // (m, w) become engaged
                couples := couples[m := w];
            }
        }        

        // mark this pair as explored
        menPrefsExplored := menPrefsExplored[m := menPrefsExplored[m] + [w]];
        unexploredPairs := unexploredPairs - {(m, w)};
    }
}

/*
 * Some test cases for the stable marriage problem.
 */

method test<Man, Woman>(name: string, menPrefs: map<Man, seq<Woman>>, womenPrefs: map<Woman, useq<Man>>, expectedCouples: set<map<Man, Woman>>)
  requires forall m :: m in menPrefs ==> ! hasDuplicates(menPrefs[m])
  requires forall m :: m in menPrefs ==> forall w :: w in menPrefs[m] ==> w in womenPrefs
  requires forall w :: w in womenPrefs ==> forall m :: m in womenPrefs[w] ==> m in menPrefs
{
    print "test ", name, ": ";
    var actualCouples := stableMatching(menPrefs, womenPrefs);
    if actualCouples in expectedCouples {
        print "passed!\n";
        if |expectedCouples| > 1 {
            print "  actualCouples = ", actualCouples , "\n";
        }
    }
    else {
        print "failed!\n";
        print "  actualCouples = ", actualCouples , "\n";
        print "  expectedCouples = ", expectedCouples , "\n";
    }
}

method test1() {
    test("test1", map [1 := [1, 2], 2 := [1, 2]], map [1 := [1], 2 := [2]], 
           {map[1 := 1, 2 := 2]});
}

method test2() {
    test("test2",  map [1 := [2, 1], 2 := [1, 2]], map [1 := [1, 2], 2 := [2, 1]],
      {map[1 := 2, 2 := 1]});
}

method test3() {
    test("test3",  map [1 := [1, 2], 2 := [1]], map [1 := [1, 2], 2 := [2, 1]],
      {map[1 := 2, 2 := 1], map[1 := 1]});
}

method testStableMarriage() {
    print "Running test cases for the stable marriage problem ...\n";
    test1();
    test2();
    test3();
}

/* 
* Application to solve the teachers placement problem.
*/

type Teacher = nat
type Vacancy = nat

// Auxiliary function to move an element 'x' in a sequence 's' (without duplicates) to the head of the sequence.
function method moveToHead<T(==)>(s: useq<T>, x: T) : useq<T>
  requires x in s 
  ensures forall y :: y in s ==> y in moveToHead(s, x)
{
    var i :| 0 <= i < |s| && s[i] == x; [s[i]] + s[..i] + s[i+1..] 
}

// Gets the last element in a sequence
function last<T>(s: seq<T>): T
requires |s| > 0
{ s[|s|-1] }

// Gets the n-th element in a sequence
function method nth<T>(s: seq<T>, n: nat): T
requires 0 <= n < |s|
{ s[n] }

// Auxiliary predicate that checks if a teacher 't' has precedence over the current teacher that occupies vacancy 'v',
// if any, knwowing the ranked list of teachers, their initial placement, and the final placement. 
// A teacher that initially occupied 'v' has priority over all others; otherwise, priority is given
// to teachers with higher rank. 
predicate method teacherHasPrecedenceForVacancy(t: Teacher, v: Vacancy, finalPlacement: inmap<Teacher, Vacancy>, teachers: useq<Teacher>, initialPlacement: inmap<Teacher,Vacancy>)
{
    if  t2 :| t2 in finalPlacement && finalPlacement[t2] == v 
    then t != t2 && ((t, v) in initialPlacement.Items || 
                     ((t2, v) !in initialPlacement.Items && precedes(t, t2, teachers)))
    else true // the vacancy is still free, so any teacher is better than remaining free 
} 

// Solution for teachers placement problem, by reducing it to the stable marriage problem.
// Input parameters:
//   vacancies - set of vacancies available (includes positions currently occupied by teachers that want to change position)
//   teachers - ordered set of teachers, ordered by their ranking (represented as a sequence without duplicates)        
//   preferences - map that indicates for each teacher the ordered list of vacancies wanted
//   initialPlacement - map that indicates the initial placement of teachers with initial placement
// Output parameters:
//   finalPlacement - final teachers placement
method teachersPlacement(vacancies: set<Vacancy>, teachers: useq<Teacher>, preferences: map<Teacher, useq<Vacancy>>, initialPlacement: inmap <Teacher, Vacancy>) 
         returns(finalPlacement: inmap<Teacher, Vacancy>) 
  // P1: the teachers in the ranked sequence and the teachers with preferences, are the same
  requires elems(teachers) == preferences.Keys 
  // P2: the vacancies mentioned in teachers preferences must exist in the set of vacancies
  requires forall t :: t in preferences ==>  elems(preferences[t]) <= vacancies
  // P3: the teachers and vacancies mentioned in the initial placement must exist in the sets of teachers and vacancies 
  requires forall t :: t in initialPlacement ==> t in teachers && initialPlacement[t] in vacancies
  // P4: the initial placement of a teacher must be mentioned in his list of preferences as the last preference
  requires forall t :: t in initialPlacement ==> initialPlacement[t] in preferences[t]
                        && initialPlacement[t] == last(preferences[t])
  // Q1: the teachers mentioned in the final placement must exist in the set of teachers
  ensures finalPlacement.Keys <= elems(teachers)
  // Q2: a teacher may only be placed in a vacancy mentioned in his/her list of preferences 
  ensures forall t :: t in finalPlacement ==> finalPlacement[t] in preferences[t]
  // Q3: the assignment is stable, i. e., there is no pair of teacher t and vacancy v in his list of preferences,
  // such that t prefers v over his current situation (either because t is free, or because t prefers v over the assigned
  // position), and v prefers t over its current situation (either because v is free and so prefers any teacher as 
  // compared to remaining free, or t is the teacher initially placed and is not occupying v, or the teacher t' that
  // currently occupies v was not initially placed there and has a lower rank than t) 
  ensures  ! exists  t, v :: t in teachers && v in preferences[t] &&
               (t !in finalPlacement || precedes(v, finalPlacement[t], preferences[t])) // t prefers v
               && teacherHasPrecedenceForVacancy(t, v, finalPlacement, teachers, initialPlacement)
  // Q4: teachers that have an initial position must also have a final position
  ensures forall t:: t in initialPlacement ==> t in finalPlacement  
{
    // Reduction to the problem of stable marriage, with teachers as men (with the given preferences),
    // vacancies as women, and the preferences of each vacancy given by the ranked list of teachers with the 
    // teacher initially placed there (if any) moved to the head   
    var vacanciesPrefs := map v | v in vacancies ::
                            if t :| t in initialPlacement && initialPlacement[t] == v 
                            then moveToHead(teachers, t)
                            else teachers; 
    finalPlacement := stableMatching(preferences, vacanciesPrefs);  
}



/*
 * Some test cases for the teachers placement problem.
 */

method testTP(name: string, vacancies: set<Vacancy>, teachers: useq<Teacher>, preferences: map<Teacher, useq<Vacancy>>, initialPlacement: inmap <Teacher, Vacancy>,
              expectedFinalPlacement: set<inmap<Teacher, Vacancy>>) 
    requires forall t :: t in teachers ==> t in preferences 
    requires forall t :: t in preferences ==> t in teachers
    requires forall t :: t in preferences ==> forall v :: v in preferences[t] ==> v in vacancies
    requires forall t :: t in initialPlacement ==> t in teachers
    requires forall t :: t in initialPlacement ==> initialPlacement[t] in preferences[t]
                                      && initialPlacement[t] == last(preferences[t]); 
    requires forall t :: t in initialPlacement ==> initialPlacement[t] in vacancies
{
    print "test ", name, ": ";
    var actualFinalPlacement := teachersPlacement(vacancies, teachers, preferences, initialPlacement); 
    if actualFinalPlacement in expectedFinalPlacement {
        print "passed!\n";
        if |expectedFinalPlacement| > 1 {
            print "  actualFinalPlacement = ", actualFinalPlacement , "\n";
        }
    }
    else {
        print "failed!\n";
        print "  actualFinalPlacement = ", actualFinalPlacement , "\n";
        print "  expectedFinalPlacement = ", expectedFinalPlacement , "\n";
    }
}

method test1TP() {
    testTP("test1TP", {1, 2}, [1, 2, 3], map [1 := [2, 1], 2 := [1, 2], 3 := [2]], map [1 := 1], {map[1 := 2, 2 := 1]});
}

method test2TP() {
    testTP("test2TP", {1, 2}, [1, 2, 3], map [1 := [2, 1], 2 := [1, 2], 3 := [2, 1]], map [3 := 1], {map[1 := 2, 3 := 1]});
}

method testTeachersPlacement() {
    print "Running test cases for the teachers placement problem ...\n";
    test1TP();
    test2TP();
}

method Main() {
    testStableMarriage();
    testTeachersPlacement();
}
