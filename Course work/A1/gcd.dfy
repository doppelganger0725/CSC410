predicate divides(a: nat, b: nat)
requires a > 0
{
   exists k: nat :: b == k * a
}

function gcd(a: nat, b: nat): nat
   requires a > 0 && b > 0
{   
   if a == b then a else
   if b > a then gcd(a,b - a) else
    gcd(a - b,b) 
}


lemma largest(a: nat, b: nat, k: nat) 
   requires a > 0 && b > 0
   requires k > 0 && divides(k, a) && divides(k, b)
   ensures k <= gcd(a,b)
   {
      if a == b {}
      else if b > a
      {
         var i :| a ==  i * k;
         var j :| b ==  j * k;

         calc =={
            b-a;
            j * k -i * k;
            (j-i) *k;
         }
      }
      
      else {
         var i :| a == i * k;
         var j :| b == j * k;

         calc == {
            a - b;
            i * k - j * k;
            (i - j) * k;
         }
      }
   }
// using induction
lemma divLemma(a: nat, b: nat)
   requires a > 0 && b > 0
   ensures gcd(a, b) > 0
   ensures divides(gcd(a, b), a) && divides(gcd(a, b), b)
{
   if a == b {
      assert a == 1 * a;
      assert b == 1 * b;
   } else if b > a {
      divLemma(a, b - a);
      var k :| a == k * gcd(a, b - a);
      var j :| b - a == j * gcd(a, b - a);

      calc == {
         a;
         k * gcd(a, b - a);
         k * gcd(a, b);
      }

      calc == {
         b;
         b - a + a;
         j * gcd(a, b - a) + a;
         j * gcd(a, b) + k * gcd(a, b);
         (j + k) * gcd(a, b);
      }
   } else {
      divLemma(a - b, b);
      var k :| b == k * gcd(a - b, b);
      var j :| a - b == j * gcd(a - b, b);

      calc == {
         b;
         k * gcd(a - b, b);
         k * gcd(a, b);
      }

      calc == {
         a;
         a - b + b;
         j * gcd(a - b, b) + b;
         j * gcd(a, b) + k * gcd(a, b);
         (j + k) * gcd(a, b);
      }
   }
}

lemma isGCD(a: nat, b: nat)
   requires a > 0 && b > 0
   ensures gcd(a, b) > 0
   ensures divides(gcd(a, b), a) && divides(gcd(a, b), b)
   ensures forall k:: k > 0 && divides(k, a) && divides(k, b) ==> k <= gcd(a, b)
{
   divLemma(a, b);
   forall n | n > 0 && divides(n , a) && divides(n, b) {
      largest(a, b, n);
   }
}

lemma divideGcd(a: nat, b: nat, k: nat)
   requires b > a
   requires a > 0 && b > 0
   requires k > 0
   requires divides(k, a) && divides(k, b)
   ensures divides(k, b - a)
{
   var i :| a == i * k;
   var j :| b == j * k;
   calc == {
      b - a;
      (j * k) - (i * k);
      (j - i) * k; 
   }
}

lemma dividable(a: nat, b: nat, k: nat)
   requires a > 0 && b > 0
   requires k > 0
   requires divides(k, a) && divides(k, b)
   ensures divides(k, gcd(a, b))
{
   if a == b {}
   else if b > a {
      divideGcd(a, b, k);
      dividable(a, b - a, k);
      assert gcd(a, b) == gcd(a, b - a);
   } else {
      divideGcd(b, a, k);
      dividable(a - b, b, k);
      assert gcd(a, b) == gcd(a - b, b);
   }
}

lemma correctness(a: nat, b: nat)
   requires a > 0 && b > 0
   ensures gcd(a, b) > 0
   ensures forall k :: k > 0 && divides(k, a) && divides(k, b) ==> divides(k, gcd(a, b))
{
   isGCD(a, b);

   // var n :| n > 0 && divides(n, a) && divides(n, b);
   // if (a == b) {
   //    assert a == gcd(a, b);
   // } else if (a > b && divides(b, a)) {
   //    calc == {
   //       b == 1 * b;
   //       divides(b, b) && divides(b, a);
   //       b <= gcd(a, b);
   //       b >= gcd(a, b);
   //       b == gcd(a, b);
   //    }
   // } else if (b > a && divides(a, b)) {
   //    calc == {
   //       a == 1 * a;
   //       divides(a, a) && divides(a, b);
   //       a <= gcd(a, b);
   //       a >= gcd(a, b);
   //       a == gcd(a, b);
   //    }
   // } else {
   //    if (!divides(n, gcd(a, b))) {
         
   //    }
   // }
   forall n | n > 0 && divides(n , a) && divides(n, b) {
      dividable(a, b, n);
   }
}