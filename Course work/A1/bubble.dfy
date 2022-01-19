method BubbleSort(a: array?<int>) returns (n: nat) 
  modifies a
  requires a != null
  ensures n <= (a.Length * (a.Length - 1))/2
{
    var i := a.Length - 1;
    n := 0;
    while (i > 0)
      invariant i < 0 ==> (a.Length * (a.Length - 1))/2 == 0
      invariant i < 0 ==> n == 0
      invariant i >= 0 ==> a.Length - i <= a.Length
      invariant i >= 0 ==> n <= ((a.Length - i - 1) * (a.Length + i)) / 2
       {
        ghost var g: nat;
        g := n;
        var j := 0;
        while (j < i)
          invariant n - g <= j;
          invariant j <= i;
          {
            if(a[j] > a[j+1])
              {
                a[j], a[j+1] := a[j+1], a[j];
                n := n + 1;
              }
              j := j + 1;
          }
          assert j <= i;
          assert n <= g + j;
          i := i -1;
      }
}
