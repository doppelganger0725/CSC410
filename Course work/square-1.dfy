predicate sorted(a: array<int>)
	reads a
{
	forall i ::  (0 <= i < a.Length - 1) ==> a[i] <= a[i + 1]
}

// If an array is not sorted, then find a pair of consecutive elements that witness the fact that it is not sorted.

method violation(a : array<int>) returns (i : nat)
  requires a.Length > 1;
  requires !sorted(a)
  ensures 0 <= i < a.Length - 1
  ensures a[i] > a[i + 1]
{
    var n := *;
    i := n % (a.Length - 1);
    while a[i] <= a[i + 1]
        invariant 0 <= i < a.Length - 1
    {       
        i := (i + 1) % (a.Length - 1);
    }
}

