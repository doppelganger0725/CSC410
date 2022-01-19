lemma ArrIdx(a: array<nat>, idx: nat)
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    requires idx >= 0 && idx < a.Length
    requires a[idx] >= idx
    decreases a.Length - idx
    ensures forall n: nat :: idx < n < a.Length && a[idx] != idx ==> a[n] > n
{
    if idx == a.Length - 1 {}
    else if idx == a.Length - 2 {
        assert a[idx + 1] >= idx + 1;
    } else {
        if (a[idx] > idx) {
            ArrIdx(a, idx + 1);
            assert a[idx + 1] > idx +  1; 
        }
    }
}

method Find(a: array<nat>) returns (index: int)
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    ensures 0 <= index ==> index < a.Length && a[index] == index
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != k
{
    if a.Length == 0 { return -1;}
    if a[0] == 0 { return 0;}
    index := a.Length - 1;
    while index > 0 
    invariant 0 <= index < a.Length
    invariant a[index] == index ==> (forall n: nat :: 0 <= n <= index ==> a[n] <= index)
    invariant forall n :: 0 <= n < a.Length - 1 && n < a[n] ==> n + 1 < a[n + 1]
    invariant index == 0 ==> a[0] != 0 && (forall n: nat :: 0 < n <= a.Length - 1 ==> a[n] != n)
    {
        if a[index] == index { return; }
        if a[0] == 0 { return 0;}
        if (a[index] > index) {
            ArrIdx(a, index);
        }
        index := index/2;
    }

    return -1;
}