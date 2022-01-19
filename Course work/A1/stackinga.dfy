  lemma scores(n: nat, j:nat, k:nat)
       requires 1 <= n ;
       requires  n == j + k
       ensures forall j,k :: n == j + k && j > 0 && k > 0 ==> sum(n) == sum(j) + sum(k) + j * k
     {
       var j, k :| n == j + k && j > 0 && k > 0;
       calc{
           sum(j) + sum(k) + j * k;
           j * (j-1)/2 + k * (k-1)/2 + j * k;
           j * (j-1)/2 + (n-j) * (n-j-1)/2 + j * (n-j);
           j * (j-1)/2 + (n-j) * (n-j-1)/2 + 2 * j * (n-j)/2;
           (j * j - j + (n-j) * (n-j) - (n-j) + 2 * j * n - 2 * j * j)/2;
           (j * j - j + n * n + j * j - 2 * j * n- (n-j) + 2 * j * n - 2 * j * j)/2;
           (n * n - j - (n - j))/2;
           n * n - j - n + j / 2;
           (n * n - n) /2;
           n * (n-1) / 2;

       }
     }

 
method Game(n: nat) returns (score: nat)
    requires n > 0
    ensures score == n * (n - 1) / 2
    
    decreases *
{
    var stacks := [n];
    score := 0;
    
    while |stacks| > 0
    invariant forall p :: 0 <= p < |stacks| ==> 1 <= stacks[p] <= n
    //invariant forall i :: 0 <= i < |stacks| ==> score == old(score) + sum(stacks[i])
    invariant score + RemainScore(stacks) == n * (n - 1) / 2
    decreases *
    {
        var i :| 0 <= i < |stacks|;
        if stacks[i] == 1 {
            stacks := stacks[..i] + stacks[i + 1..];
        } else {
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;
            score := score + j * k;
            stacks := [j, k] + stacks[..i] + stacks[i + 1..];
            scores(i,j,k);
            //spickstack(stacks);
        }
    }
    
    return;
}


function sum(num: nat): nat
    requires num > 0
{
   num * (num - 1) / 2
}

function RemainScore (s: seq<nat>) : nat
requires forall p :: 0 <= p < |s| ==> 1 <= s[p]
{
    if |s| == 0 then 0
    else if |s| == 1 then sum(s[0])
    else sum(s[0]) + RemainScore(s[1..])
}

// lemma pickstack(s: seq<nat>)
// requires forall p :: 0 <= p < |s| ==> 1 <= s[p]
// ensures forall p :: 0 <= p < |s| ==> RemainScore(s) == RemainS + RemainScore(s[..p] + s[p+1..])
// {

// }