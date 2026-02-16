include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"
include "../Auxiliary/Interview.dfy"


method verifyCDPC(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview) returns (r:bool, ghost counter:nat)
  requires f.Valid() && g.Valid() && P.Valid() && iv.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires f.Keys() == g.Keys()
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
  ensures r == certificateCDPC(f.Model(), g.Model(), P.Model(), a, b, x, y, iv.Model())
  {
    counter := 0;
    var isEmpty:bool; isEmpty, counter := iv.Empty(counter);
    if (isEmpty) {
      
    }
    else {
      
    }
    assume false;
  }
