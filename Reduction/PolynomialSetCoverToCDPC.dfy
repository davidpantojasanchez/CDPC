include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"
include "../Reduction/ReductionSetCoverToCDPC.dfy"

method SetCoverToCDPC_Method(U:set<int>, S:set<set<int>>, k:nat) returns (r:(map<Candidate, bool>, map<Candidate, int>, set<int>, real, real, real, real))
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures r == SetCoverToCDPC(U, S, k)

