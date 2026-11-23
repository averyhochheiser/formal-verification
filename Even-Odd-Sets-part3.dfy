/*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m;
	}
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
lemma EvenTimes(n1: int, n2: int)
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
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ // TODO
	if n % 2 != 0 {
	  var m := n / 2;
	  assert n == 2 * m + 1;
	}
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ // TODO
	OddModulo(n);
	ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ // TODO
  if isOdd(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1 + m2) + 1;
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ // TODO
  if n % 2 == 0 {
	ModuloEven(n);
  } else {
	ModuloOdd(n);
  }
}

lemma EvenTimesOdd(n1: int, n2: int)
  ensures isEven(n1) && isOdd(n2) ==> isEven(n1 * n2)
{ // TODO
  if isEven(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO
	if isEven(n) {
		var m := invertParity(n);
		ModuloOdd(m);
	} else {
		var m := invertParity(n);
		ModuloEven(m);
	}
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == s[j] ==> i == j // TODO
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s) 
{ 
  b := true;
  var i := 0;
  
  while i < |s| 
    invariant 0 <= i <= |s|
    invariant b <==> forall p, q :: 0 <= p < i && p < q < |s| ==> s[p] != s[q]
    {
    var j := i + 1;
    while j < |s| 
      invariant i + 1 <= j <= |s|
      invariant b <==> ((forall p, q :: 0 <= p < i && p < q < |s| ==> s[p] != s[q]) 
        && (forall q :: i < q < j ==> s[i] != s[q]))
      {
      if s[i] == s[j] {
        b := false;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  assert b <==> isSet(s) by {
    if b {
      forall p, q | 0 <= p < |s| && 0 <= q < |s| && s[p] == s[q] ensures p == q
      {
        if p < q { assert s[p] != s[q]; }
        if q < p { assert s[q] != s[p]; }
      }
    }
    if !b {
      var p, q :| 0 <= p < q < |s| && s[p] == s[q];
      assert !isSet(s);
    }
  }
}

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
 isSet(s) && forall x :: x in s ==> isEven(x) // TODO
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{ 
  var isS := checkSet(s);
  if !isS {
    b := false;
  } else {
    b := true;
    var i := 0;

    while i < |s| 
      invariant 0 <= i <= |s|
      invariant b <==> forall k :: 0 <= k < i ==> s[k] % 2 == 0
    {
      if s[i] % 2 != 0 {
        b := false;
      }
      i := i + 1;
    }

    if b {
      forall x | x in s ensures isEven(x) {
        var k :| 0 <= k < |s| && s[k] == x;
        ModuloEven(x);
      }
    } else {
      var k :| 0 <= k < |s| && s[k] % 2 != 0;
      EvenModulo(s[k]);
      assert s[k] in s;
      assert !isEven(s[k]);
    }
  }
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall x :: x in s ==> isOdd(x) // TODO
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{ 
  var isS := checkSet(s);
  if !isS {
    b := false;
  } else {
    b := true;
    var i := 0;

    while i < |s| 
      invariant 0 <= i <= |s|
      invariant b <==> forall k :: 0 <= k < i ==> s[k] % 2 != 0
    {
      if s[i] % 2 == 0 {
        b := false;
      }
      i := i + 1;
    }

    if b {
      forall x | x in s ensures isOdd(x) {
        var k :| 0 <= k < |s| && s[k] == x;
        ModuloOdd(x);
      }
    } else {
      var k :| 0 <= k < |s| && s[k] % 2 == 0;
      OddModulo(s[k]);
      assert s[k] in s;
      assert !isOdd(s[k]);
    }
  }
}

/*** Set Operations ***/

/* Adds n to a set s, making sure it remains a set */
// Hint: use recursion
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)
  ensures forall x :: (0 <= x < |b|) ==> (b[x] in s || b[x] == n)
  ensures forall x :: (0 <= x < |s|) ==>  s[x] in b
  ensures n in s ==> b == s
  ensures !(n in s) ==> b == s + [n]
  ensures isEvenSet(s) && isEven(n) ==> isEvenSet(b)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(b)
{ 
  if n in s{
    b := s;
  } else{
    b := s + [n];
    forall i, j | 0 <= i < |b| && 0 <= j < |b| && b[i] == b[j] ensures i == j {
      if i < |s| && j < |s| {
      } else if i == |s| && j < |s| {
        assert b[j] == s[j];
        assert s[j] in s;
      } else if j == |s| && i < |s| {
        assert b[i] == s[i];
        assert s[i] in s;
      }
    }
  }
}

// Liv 
/* unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 || t[x] in s2)
  ensures forall x :: (0 <= x < |s1| ==> s1[x] in t)
  ensures forall x :: (0 <= x < |s2| ==> s2[x] in t)
  ensures isEvenSet(s1) && isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{ // TODO: fill in your code here and prove method correct
}

// Liv 
/* intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
  ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
{ // TODO: fill in your code here and prove method correct
  // hint: you may need to call:
  //  NotEvenANDOdd(s1[i]);
  // at the appropriate place in your code to help Dafny prove correctness
}

/* difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
  ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1 // hint: don't use addToSet in your code -- use t + [s1[i]] instead
{ // TODO: fill in your code here and prove method correct
  // hint: you may need to call:
  //  NotEvenANDOdd(s1[i]);
  // at the appropriate place in your code to help Dafny prove correctness
  t := []; 
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall x :: x in s1[..i] && x !in s2==> x in t
    invariant forall x :: x in t ==> x in s1[..i] && x !in s2
    invariant isEvenSet(s1) ==> forall x :: x in t ==> isEven(x)
    invariant isOddSet(s1) ==> forall x :: x in t ==> isOdd(x)
    invariant isEvenSet(s1) && isOddSet(s2) ==> t == s1[..i]
    {
    assert s1[..i+1] == s1[..i] + [s1[i]]; 
    if isEvenSet(s1) && isOddSet(s2) {
      NotEvenANDOdd(s1[i]);
    }

      if s1[i] !in s2{
        assert s1[i] !in t;
        t:= t + [s1[i]];
      }
      i := i+1;
    }
    assert s1[..|s1|] == s1;  
}

// Liv 
/* multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> exists i :: 0<= i < |s| && t[x] == s[i] * n)
  ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
  ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
{ // TODO: fill in your code here and prove method correct
  t:=[];
  var i := 0;
  while i < |s|
    invariant isSet(t)
    invariant forall x :: 0<= x< |t| ==> exists j :: 0 <= j < i && t[x] == s[j] * n
    invariant forall x :: 0 <= x < i ==> s[x] * n in t
    invariant isEvenSet(s) || isEven(n) ==> isEvenSet(t)
    invariant isOddSet(s) && isOdd(n) ==> isOddSet(t)
  {
    if isEven(s[i]) || isEven(n){
      EvenTimes(s[i], n);
    }
    if isOdd(s[i]) && isOdd(n){
      OddTimesOdd(s[i], n);
    }

    if s[i] * n !in t{
      t := t + [s[i] *n];
      assert t[|t| -1] == s[i] *n;
    }
    i:= i+1;
  }
}

// Liv 
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==> exists i1, j1 :: 0<= i1 < |s1| && 0<= j1 < |s2| && x == s1[i1] * s2[j1]
  ensures forall i1, j1 :: i1 in s1 && j1 in s2 ==> i1 * j1 in t
  ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{ // TODO: fill in your code here and prove method correct
}


/* converts an even set to an odd set by inverting the parity of each element  */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isEvenSet(s) || isOddSet(s)
  ensures isEvenSet(s) ==> isOddSet(t)
  ensures isOddSet(s) ==> isEvenSet(t)
  ensures |t| == |s|
  ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
{ 
  t := []; 
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant isSet(t)
    invariant forall k :: 0 <= k < i ==> t[k] == invertParity(s[k])
    invariant isEvenSet(s) ==> forall y :: y in t ==> isOdd(y)
    invariant isOddSet(s) ==> forall y :: y in t ==> isEven(y)
    {
      assert s[i] in s;
      InvertParityCorrect(s[i]);
      var v := invertParity(s[i]);
      if v in t {
        var k :| 0 <= k < |t| && t[k] == v;
        assert s[k] == s[i];
        assert false;
      }
      var oldT := t;
      t := addToSet(t, v);
      assert t == oldT + [v];
      i := i + 1;
    }
}
