function method unpair(n: nat): (nat, nat)
requires n >= 0
{
    // Add an implementation for this
    // (fix the original point, else increment the steps always)
    if (n == 0) then (0, 0)
    else 
      var (n1, n2) := unpair(n - 1);
      if n1 == 0 then (n2 + 1, 0) else (n1 - 1, n2 + 1) // (0, 1) -> (2, 0)
}

function method pick(i: nat): nat
{
  var (x, y) := unpair(i);
  x + i * y
}

function method encode(a: nat, b: nat) : nat
  ensures unpair(encode(a, b)) == (a, b)
  ensures pick(encode(a, b)) == a + (encode(a, b)) * b
  decreases a + b, b
{
  // if a == 0 && b == 0 then 0
  // else if b == 0 then encode(0, a - 1) + 1
  // else if a == 0 then encode(b - 1, 0) + 1
  // else if a > 0 then encode(a - 1, b + 1) + 1
  // else encode(b - 1, a + 1) + 1
  if a == 0 && b == 0 then 0
  else if b == 0 then encode(0, a - 1) + 1 // b is n2, same as unpair, reverse order (2, 0) -> (0, 1), controlled by n2 in reverse
                                          // pair is controlled by n1
  else encode(a + 1, b - 1) + 1 // (n1 - 1, n2 + 1)
}

method catchTheRabbit(a: nat, b: nat)
{
var t := 0;
  // prove that this loop terminates and therefore the rabbit is caught
  while a + t * b != pick(t)
    invariant encode(a, b) >= t
    decreases encode(a, b) - t
    { t := t + 1; }
}