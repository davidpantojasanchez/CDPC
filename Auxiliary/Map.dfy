include "../Auxiliary/Lemmas.dfy"

/*
Basic map (its elements have constant size)
It encapsulates the Dafny map
Contains ghost functions to assist in the verification of the properties of the map and on the computational cost of its operations
Has the typical `map` operations
*/
type Map< T1(==), T2(==) > {

  ghost function Model():map<T1,T2>

  ghost function Universe():map<T1,T2>

  ghost function Valid():bool
  {
    (Model().Keys <= Universe().Keys) &&
    (forall k | k in Model().Keys :: Model()[k] == Universe()[k]) &&
    (Cardinality() <= |Universe()|)
  }

  ghost function UBSize0():nat
  { Cardinality() }

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }


  method {:axiom} Get(key:T1, ghost counter_in:nat) returns (val:T2, ghost counter_out:nat)
    requires Valid()
    ensures key in Model().Keys
    ensures val == Model()[key]
    ensures counter_out == counter_in + UBSize0()

  method {:axiom} Insert(key:T1, val:T2, ghost counter_in:nat) returns (r:Map<T1,T2>, ghost counter_out:nat)
    requires Valid()
    ensures r.Model() == Model()[key := val]
    ensures r.Universe() == Universe()[key := val]
    ensures counter_out == counter_in + UBSize0()

  method {:axiom} Remove(key:T1, ghost counter_in:nat) returns (r:Map<T1,T2>, ghost counter_out:nat)
    requires Valid()
    ensures r.Model() == Model() - {key}
    ensures counter_out == counter_in + UBSize0()

  method {:axiom} nPairs(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == |Model()|
    ensures counter_out == counter_in + 1

  method {:axiom} ContainsKey(key:T1, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (key in Model())
    ensures counter_out == counter_in + UBSize0()

  method {:axiom} Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (|Model()| == 0)
    ensures counter_out == counter_in + 1

  method {:axiom} Copy(ghost counter_in:nat) returns (r:Map<T1,T2>, ghost counter_out:nat)
    requires Valid()
    ensures r.Model() == Model()
    ensures r.Universe() == Model()
    ensures counter_out == counter_in + UBSize0()

}
