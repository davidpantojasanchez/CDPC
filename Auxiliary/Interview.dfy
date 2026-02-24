include "../Auxiliary/Lemmas.dfy"
include "../Problems/CDPC.dfy"


type Interview< T(==) > {

  ghost function Model():interview

  ghost function Valid():bool
  {
    AllKeysIn(Model(), Questions()) &&
    EveryPathHasCandidate(Model(), Candidates()) &&
    //(forall c1, c2:candidate |  c1 in Candidates() && c2 in Candidates() :: c1.Keys == c2.Keys) &&
    (forall c:candidate | c in Candidates() :: c.Keys == Questions())
  }

  ghost function Candidates():set<candidate>

  ghost function Questions():set<int>

  ghost function UBSize():nat
  {
    |Questions()| * |Candidates()|
  }

  method {:axiom} Key(ghost counter_in:nat) returns (key:int, ghost counter_out:nat)
    requires Valid()
    requires Model() != Null
    ensures key == Model().Key
    ensures counter_out == counter_in + 1

  method {:axiom} Get(b:bool, ghost counter_in:nat) returns (e:Interview<T>, ghost counter_out:nat)
    requires Valid()
    requires Model() != Null
    ensures e.Valid()
    ensures e.Model() == if b then Model().True else Model().False
    ensures e.Questions() == Questions() - {Model().Key}
    ensures e.Candidates() == (set cand:candidate | cand in Candidates() && cand[Model().Key] == b :: cand)
    ensures counter_out == counter_in + UBSize()
  

  method {:axiom} Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == Null)
    ensures counter_out == counter_in + 1

}
