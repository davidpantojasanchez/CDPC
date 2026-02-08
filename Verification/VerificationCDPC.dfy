include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"


method verifyCDPC(f:map<Candidate, bool>, g:map<Candidate, int>, P:set<int>, a:real, b:real, x:real, y:real, interview:Interview) returns (r:bool)
  requires f.Keys == g.Keys
  requires forall c:Candidate | c in f.Keys :: (P <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
  ensures r == certificateCDPC(f, g, P, a, b, x, y, interview)
  {
    assume false;
  }
