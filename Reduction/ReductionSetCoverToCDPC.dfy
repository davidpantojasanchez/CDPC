include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


ghost function SetCoverToCDPC(U:set<int>, S:set<set<int>>, k:nat) : (r:(map<candidate, bool>, map<candidate, int>, set<int>, real, real, real, real))
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures forall c1, c2:candidate |  c1 in r.0.Keys && c2 in r.0.Keys :: c1.Keys == c2.Keys
  ensures r.0.Keys == r.1.Keys
  ensures forall c:candidate | c in r.0.Keys :: (r.2 <= c.Keys)
  ensures 0.0 <= r.3 <= r.4 <= 1.0
  ensures 0.0 <= r.5 <= r.6 <= 1.0


lemma SetCoverToCDPC_Lemma(U:set<int>, S:set<set<int>>, k:nat)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (f, g, P, a, b, x, y) := SetCoverToCDPC(U,S,k);
              SetCover(U,S,k) <==> CDPC(f, g, P, a, b, x, y)
