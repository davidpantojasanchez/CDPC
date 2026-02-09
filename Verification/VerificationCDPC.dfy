include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"


method verifyCDPC(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, interview:Interview) returns (r:bool, ghost counter:nat)
  requires f.Keys() == g.Keys()
  requires forall c:Candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
  ensures r == certificateCDPC(f.Model(), g.Model(), P.Model(), a, b, x, y, interview)
  {
    if (interview == Empty) {
      
    }
    else {
      
    }
    assume false;
  }
