
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
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
  // Marks will be awarded for specifying as much as possible all relevant properties of the output.
  // Hint: You don't need to reimplement addToSet as a function to use in your specification.
{ // TODO: Implement the method
}

/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}

/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
}
