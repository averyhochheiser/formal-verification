
/*** Even ***/

ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
// The next three lemmas prove that modulo-based definition is equivalent to existential-based definition
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m; // Hint for Dafny to choose n/2 as witness for the existential in the isEven predicate
	}
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
// Useful lemma that may be used later
// It shows that the product of two integers is even if at least one of them is even
lemma EvenTimesAny(n1: int, n2: int)
  ensures isEven(n1) || isEven(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) {
	  var m1 := n1 / 2;
	  assert n1 * n2 == 2 * (m1 * n2);
  } else if isEven(n2) {
	  var m2 := n2 / 2;
	  assert n1 * n2 == 2 * (n1 * m2);
  }
}

/*** Odd ***/

ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ 
  if n % 2 != 0 {
    var m := (n - 1) / 2;
    assert n == 2 * m + 1;
  }
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ 
  OddModulo(n);
  ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ 
  if isOdd(n1) && isOdd(n2) {
    var a |: n1 == 2 * a + 1;
    var b |: n2 == 2 * b + 1;
    assert n1 * n2 == 2 * (2 * a * b + a + b) + 1;
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ 
  if n % 2 == 0 {
    ModuloEven(n);
  } else {
    ModuloOdd(n);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ 
  if isEven(n) {
    var m |: n == 2 * m;
    assert invertParity(n) == 2 * m + 1;
  } else {
    var m |: n == 2 * m + 1;
    assert invertParity(n) == 2 * (m + 1);
  }
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
 forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s)
{ 
  b := true;
  var i := 0;
  
  while i < |s| {
    var j := i + 1;
    while j < |s| {
      if s[i] == s[j] {
        b := false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
 isSet(s) && forall i :: 0 <= i < |s| ==> isEven(s[i])
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{
  var isSet := checkSet(s);
  if !isSet {
    b := false;
  } else {
    b := true;
    var i := 0;

    while i < |s| {
      if s[i] % 2 != 0 {
        b := false;
      }
      i := i + 1;
    }
  }
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall i :: 0 <= i < |s| ==> isOdd(s[i])
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{ 
  var isSet := checkSet(s);
  if !isSet {
    b := false;
  } else {
    b := true;
    var i := 0;

    while i < |s| {
      if s[i] % 2 == 0 {
        b := false;
      }
      i := i + 1;
    }
  }
}

/*** Set Operations ***/

// For the following methods specify their behaviour so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
// Marks will be awarded for specifying as much as possible all relevant properties of the output.

/* Adds n to a set s, making sure it remains a set */
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  ensures isSet(s)
  ensures isSet(b)
  ensures n in b
  ensures forall x :: x in s ==> x in b 
  ensures forall x :: x in b ==> x in s || x == n
  ensures n in s ==> |b| == |s|
  ensures n !in s ==> |b| == |s| +1
{
  if n in s{
    b := s;
  } else{
    b := s + [n];
  }
}

/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1 && s2)
  ensures isSet(t)
  ensures forall x :: x in s1 ==> x in t
  ensures forall x :: x in s2 ==> x in t
  ensures forall x :: x in t ==> x in s1 || x in s2
  ensures |t| >= |s1| //atleast s1 size
  ensures |t| <= |s1| + |s2| // no bigger than combination
{
  t := s1; 
  var i := 0;
  while i < |s2|
  // facts must be true for while loop
    invariant 0 <= i <= |s2|
    invariant isSet(t)
    invariant forall x :: x in s1 ==> x in t
    invariant forall x :: x in s2[..i] ==> x in t
    invariant forall x :: x in t ==> x in s1 || x in s2[..i]
    invariant |s1| <= |t| <= |s1| +i 
    {
      assert s2[..i+1] == s2[..i] + [s2[i]]; // extend the prefix
      t := addToSet(t, s2[i]);
      i := i+1;
    }
    assert s2[..|s2|] == s2;  // prefix now the sequence 

}

/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1 && s2)
  ensures isSet(t)
  ensures forall x :: x in s1 && x in s2 ==> x in t 
  ensures forall x :: x in t ==> x in s1 && x in s2
  ensures |t| <= |s1| //no bigger than s1, intersection smaller
{ 
  t := []; 
  var i := 0;
  while i < |s1|
  // facts must be true for while loop
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall x :: x in s1[..i] && x in s2==> x in t
    invariant forall x :: x in t ==> x in s1[..i] && x in s2
    invariant |t| <= i 
    {
      assert s1[..i+1] == s1[..i] + [s1[i]]; // extend the prefix
      if s1[i] in s2{
        t:= addToSet(t,s1[i]);
      }
      i := i+1;
    }
    assert s1[..|s1|] == s1;  // prefix now the sequence 
}

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1)
  requires isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==> x in s1 && x !in s2
  ensures forall x :: x in s1 && x !in s2 ==> x in t
  ensures |t| <= |s1|
{
  t := []; 
  var i := 0;
  while i < |s1|
  // facts must be true for while loop
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall x :: x in s1[..i] && x !in s2==> x in t
    invariant forall x :: x in t ==> x in s1[..i] && x !in s2
    invariant |t| <= i 
    {
      assert s1[..i+1] == s1[..i] + [s1[i]]; // extend the prefix
      if s1[i] !in s2{
        t:= addToSet(t,s1[i]);
      }
      i := i+1;
    }
    assert s1[..|s1|] == s1;  // prefix now the sequence 
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: x in s ==> x * n in t // every element
  ensures forall y :: y in t ==> exists j :: 0 <= j < |s| && y == s[j] * n // no more elemnt
  ensures |t| <= |s|
  ensures n != 0 ==> |t| == |s|
  ensures n ==0 && |s| > 0 ==> t == [0]
{ 
  t := []; 
  var i := 0;
  while i < |s|
  // facts must be true for while loop
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant forall x :: x in s[..i] ==> x*n in t
    invariant forall x :: x in t ==>exists j :: 0 <= j < |s| && y == s[j] * n 
    invariant |t| <= i 
    invariant n != 0 ==> |t| == i
    invariant n ==0 && i > 0 ==> t == [0]
    {
      if  n != 0 && s[i] * n in t{
        var j :| 0<= j < i && s[i] * n == s[j] * n;
        assert false; //cant get to point si equal sj before this, goes against isSet(s)
      }
      t:= addToSet(t,s[i]*n);
      i := i+1;
    }
    assert s[..|s|] == s;  
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1)
  requires isSet(s2)
  ensures isSet(t)
  ensures forall z :: z in t ==> exists i,j :: 0 <= i < |s1| && 0 <= j < |s2| && z == s1[i] * s2[j]
  ensures forall x, y :: x in s1 && y in s2 ==> x*y in t
  ensures |t| <= |s1| * |s2|
  ensures |s1| ==0 || |s2| == 0 ==> t == []
{ 
  t := []; 
  var i := 0;
  while i < |s1|
  // facts must be true for while loop
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant forall  z :: z in t ==> exists l,j :: 0 <= l < |s1| && 0 <= j < |s2| && z == s1[l] * s2[j]
    invariant forall x, y :: x in s1 && y in s2 ==> x*y in t
    invariant |t| <= i * |s2|
    {
      assert s1[..i+1] == s1[..i] + [s1[i]]; // extend the prefix
      var sacled := setScale(s2, s1[i]);
      t:= union(t,sacled);
      i := i+1;
    }
    assert s1[..|s1|] == s1;
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isEvenSet(s)
  ensures isOddSet(t)
  ensures forall x :: x in s ==> invertParity(x) in t 
  ensures forall y :: y in t ==> exists j :: 0 <= j < |s| && y == invertParity(s[j]) 
  ensures |t| == |s|
{
  t := []; 
  var i := 0;
  while i < |s|
  // facts must be true for while loop
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant forall  y :: y in t ==> isOdd(y)
    invariant forall x :: x in s[..i] ==>invertParity(x) in t
    invariant forall y :: y in t ==> exists j :: 0 <= j < |s| && y == invertParity(s[j]) 
    invariant |t| == i 
    {
      InvertParityCorrect(s[i]);
      if invertParity(s[i]) in t{
        var j :| 0<= j < i && invertParity(s[i]) == invertParity(s[j]);
        assert false; //cant get to point invert(si) equal invertp(sj) before this, goes against isSet(s)
      }
      t:= addToSet(t, invertParity(s[i]));
      i := i+1;
    }
    assert s[..|s|] == s;  // prefix now the sequence 
}
