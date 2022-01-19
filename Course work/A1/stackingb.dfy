lemma moveSplit(a: seq<nat>, b:seq<nat>)
    ensures move(a + b) == move(a) + move(b)
    ensures |a| == 1 ==> move(a) == a[0] * a[0]
    ensures |b| == 1 ==> move(b) == b[0] * b[0]
{
    turnToMoveDivisibility(a, b);
    sumSplit(turnToMoveValue(a), turnToMoveValue(b));
}

lemma numberTheory(a: nat) 
    requires a > 1
    ensures forall i, j :: i + j == a && i > 0 && j > 0 ==> a * a > i * i + j * j
{
    var i, j :| i + j == a && i > 0 && j > 0;
    calc == {  
        (i + j) * (i + j);
        i * i + j * j + i * j + i * j;
        i * i + (1 + 1) * i * j + j * j;
        i * i + 2 * i * j + j * j;
        a * a;
    }
    assert a * a > i * i + j * j;
}

lemma sumSplit(a: seq<nat>, b:seq<nat>)
    ensures sum(a + b) == sum(a) + sum(b)
{
    if a == [] {
        assert a + b == b;
    } else {
        assert a + b != [];
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
        assert a[0] + sum(a[1..] + b) == sum(a + b);
        assert sum(a + b) == sum(a) + sum(b);
    }
}

lemma turnToMoveDivisibility(a:seq<nat>, b:seq<nat>)
    ensures turnToMoveValue(a + b) == turnToMoveValue(a) + turnToMoveValue(b)
{
    if a == [] {
        assert a + b == b;
        assert turnToMoveValue(a + b) == turnToMoveValue(b);
        assert turnToMoveValue(a + b) == turnToMoveValue(a) + turnToMoveValue(b);
    } else {
        assert a + b != [];
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
        calc ==
        {
            turnToMoveValue(a + b); 
            turnToMoveValue([a[0]]) + turnToMoveValue(a[1..] + b);
            turnToMoveValue([a[0]]) + turnToMoveValue(a[1..]) + turnToMoveValue(b);
            turnToMoveValue(a) + turnToMoveValue(b);
        }

    }
}

lemma moveDivisibility(s: seq<nat>, i: nat)
    requires 0 <= i < |s|
    ensures move(s) == move(s[..i]) + dummy(s[i]) + move(s[i + 1..])
{
    assert s == s[..i] + [s[i]] + s[i + 1..];
    moveSplit(s[..i] + [s[i]], s[i + 1..]);
    assert move(s) == move(s[..i] + [s[i]]) + move(s[i + 1..]);
    moveSplit(s[..i], [s[i]]);
    assert move(s) == move(s[..i]) + move([s[i]]) + move(s[i + 1..]);
    assert move([s[i]]) == sum(turnToMoveValue([s[i]]));
    assert move([s[i]]) == dummy(s[i]);
    assert move(s) == move(s[..i]) + dummy(s[i]) + move(s[i + 1..]);
}

method Game(n: nat) returns (score: nat)
    requires n > 0
    //ensures score == n * (n - 1) / 2
{
    var stacks := [n];
    score := 0;

    while |stacks| > 0
    invariant forall p :: 0 <= p < |stacks| ==> 1 <= stacks[p] <= n
    decreases move(stacks)
    {
        ghost var g := move(stacks);
        var i :| 0 <= i < |stacks|;
        if stacks[i] == 1 {
            moveSplit(stacks[..i], stacks[i + 1..]);
            moveDivisibility(stacks, i);
            assert move(stacks[..i] + stacks[i + 1..]) < g;
            stacks := stacks[..i] + stacks[i + 1..];
            assert move(stacks) < g;
        } else {
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;
            moveSplit([j, k] + stacks[..i], stacks[i + 1..]);
            moveSplit([j, k], stacks[..i]);
            moveSplit([j], [k]);
            moveDivisibility(stacks, i);
            numberTheory(stacks[i]);
            assert stacks[i] > 1;
            // turnToValueDivisibility([j, k] + stacks[..i], stacks[i + 1..]);
            // turnToValueDivisibility([j, k], stacks[..i]);
            calc == {
                move([j, k] + stacks[..i] + stacks[i + 1..]);
                move([j, k] + stacks[..i]) + move(stacks[i + 1..]);
                move([j, k]) + move(stacks[..i]) + move(stacks[i + 1..]);
            }
            assert move([j, k]) == move([j]) + move([k]);
            assert move([j, k]) == j * j + k * k;
            assert move([j, k]) < stacks[i] * stacks[i];
            assert move([j, k]) + move(stacks[..i]) + move(stacks[i + 1..]) < move(stacks[..i]) + move(stacks[i + 1..]) + stacks[i] * stacks[i];
            assert move([j, k] + stacks[..i] + stacks[i + 1..]) < g;
            score := score + j * k;
            assert move([j, k] + stacks[..i] + stacks[i + 1..]) < g;
            stacks := [j, k] + stacks[..i] + stacks[i + 1..];
            assert move(stacks) < g;
        }
        assert move(stacks) < g;
    }
    
    return;
}

function sum(s: seq<nat>): nat
{
    if s == [] then 0 else s[0] + sum(s[1..])
}

function turnToMoveValue(s: seq<nat>): seq<nat>
{
    if s == [] then [] else [dummy(s[0])] + turnToMoveValue(s[1..])
}

function move(s: seq<nat>) : nat
{
    sum(turnToMoveValue(s))
}

function dummy(v: nat) : nat
{
    v*v
}