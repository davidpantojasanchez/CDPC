include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"
include "../Reduction/ReductionSetCoverToCDPC.dfy"

method SetCoverToCDPC_Method(U:Set<int>, S:SetSet<int>, k:nat) returns (r:(Map_Map_T<int, bool, bool>, Map_Map_T<int, bool, int>, Set<int>, real, real, real, real), ghost counter:nat)
  requires U.Valid() && S.Valid()
  ensures r.0.Valid() && r.1.Valid() && r.2.Valid()
  requires forall s | s in S.Model() :: s <= U.Model()
  requires isCover(U.Model(), S.Model())
  ensures (r.0.Model(), r.1.Model(), r.2.Model(), r.3, r.4, r.5, r.6) == SetCoverToCDPC(U.Model(), S.Model(), k)
