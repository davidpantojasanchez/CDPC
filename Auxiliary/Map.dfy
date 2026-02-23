include "../Auxiliary/Lemmas.dfy"

/*
Basic map (its elements have constant size)
It encapsulates the Dafny map
Contains ghost functions to assist in the verification of the properties of the map and on the computational cost of its operations
Has the typical `map` operations
*/
type Map< T0(==), T1(==) > {

  ghost function Model():map<T0,T1>

  ghost function Universe():map<T0,T1>

  ghost function Keys():set<T0>
  { Model().Keys }

  ghost function Values():set<T1>
  { Model().Values }

  ghost function Valid():bool
  {
    (Model().Keys <= Universe().Keys) &&
    (forall k | k in Model().Keys :: Model()[k] == Universe()[k]) &&
    (Cardinality() <= |Universe()|)
  }

  ghost function UBSize():nat
  { Cardinality() }

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }


  method {:axiom} Get(key:T0, ghost counter_in:nat) returns (val:T1, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures val == Model()[key]
    ensures counter_out == counter_in + UBSize()

  method {:axiom} Insert(key:T0, val:T1, ghost counter_in:nat) returns (r:Map<T0,T1>, ghost counter_out:nat)
    requires Valid()
    ensures r.Valid()
    ensures r.Model() == Model()[key := val]
    ensures r.Universe() == Universe()[key := val]
    ensures counter_out == counter_in + UBSize()

  method {:axiom} Remove(key:T0, ghost counter_in:nat) returns (r:Map<T0,T1>, ghost counter_out:nat)
    requires Valid()
    ensures r.Valid()
    ensures r.Model() == Model() - {key}
    ensures if key !in Keys() then r.Cardinality() == Cardinality()
            else r.Cardinality() == Cardinality() - 1
    ensures r.Universe() == Universe()
    ensures counter_out == counter_in + UBSize()

 method {:axiom} PickKey(ghost counter_in:nat) returns (key:T0, ghost counter_out:nat)
    requires Valid()
    ensures key in Model().Keys
    ensures counter_out == counter_in + 1

  method {:axiom} nPairs(ghost counter_in:nat) returns (n:int, ghost counter_out:nat)
    requires Valid()
    ensures n == |Model()|
    ensures counter_out == counter_in + 1

  method {:axiom} ContainsKey(key:T0, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (key in Model())
    ensures counter_out == counter_in + UBSize()

  method {:axiom} Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == map[])
    ensures counter_out == counter_in + 1

  method {:axiom} Copy(ghost counter_in:nat) returns (r:Map<T0,T1>, ghost counter_out:nat)
    requires Valid()
    ensures r.Valid()
    ensures r.Model() == Model()
    ensures r.Universe() == Model()
    ensures counter_out == counter_in + UBSize()

}


// Maps whose keys are maps
type Map_Map_T< T0(==), T1(==), T2(==) > {

  ghost function Model():map<map<T0, T1>,T2>

  ghost function Universe():map<map<T0, T1>,T2>

  ghost function Keys():set<map<T0, T1>>
  { Model().Keys }

  ghost function Values():set<T2>
  { Model().Values }

  ghost function Valid():bool
  {
    (Model().Keys <= Universe().Keys) &&
    (forall k | k in Model().Keys :: Model()[k] == Universe()[k]) &&
    (Cardinality() <= |Universe()|)
  }

  ghost function UBSize():nat
  { Cardinality() * UBSize_Keys() }

  ghost function {:axiom} UBSize_Keys():nat
    ensures forall k | k in Universe().Keys :: UBSize_Keys() >= |k|
    ensures exists k :: k in Universe().Keys && UBSize_Keys() == |k|

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }


  method {:axiom} Get(key:Map<T0, T1>, ghost counter_in:nat) returns (val:T2, ghost counter_out:nat)
    requires Valid()
    ensures key.Model() in Model().Keys
    ensures val == Model()[key.Model()]
    ensures counter_out == counter_in + UBSize()

  method {:axiom} Insert(key:Map<T0, T1>, val:T2, ghost counter_in:nat) returns (r:Map_Map_T<T0,T1,T2>, ghost counter_out:nat)
    requires Valid()
    ensures r.Valid()
    ensures r.Model() == Model()[key.Model() := val]
    ensures r.Universe() == Universe()[key.Model() := val]
    ensures counter_out == counter_in + UBSize()

  method {:axiom} Remove(key:Map<T0, T1>, ghost counter_in:nat) returns (r:Map_Map_T<T0,T1,T2>, ghost counter_out:nat)
    requires Valid()
    ensures r.Valid()
    ensures r.Model() == Model() - {key.Model()}
    ensures if key.Model() !in Keys() then r.Cardinality() == Cardinality()
            else r.Cardinality() == Cardinality() - 1
    ensures r.Universe() == Universe()
    ensures counter_out == counter_in + UBSize()

 method {:axiom} PickKey(ghost counter_in:nat) returns (key:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures key.Valid()
    ensures key.Model() in Model().Keys
    ensures counter_out == counter_in + UBSize_Keys()

  method {:axiom} nPairs(ghost counter_in:nat) returns (n:int, ghost counter_out:nat)
    requires Valid()
    ensures n == |Model()|
    ensures counter_out == counter_in + 1

  method {:axiom} ContainsKey(key:Map<T0, T1>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (key.Model() in Model())
    ensures counter_out == counter_in + UBSize()

  method {:axiom} Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (|Model()| == 0)
    ensures counter_out == counter_in + 1

  method {:axiom} Copy(ghost counter_in:nat) returns (r:Map_Map_T<T0,T1,T2>, ghost counter_out:nat)
    requires Valid()
    ensures r.Valid()
    ensures r.Model() == Model()
    ensures r.Universe() == Model()
    ensures counter_out == counter_in + UBSize()

}


method {:axiom} New_Map<T0(==), T1(==)>(ghost counter_in:nat) returns (R:Map<T0, T1>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == map[]

method {:axiom} New_Map_Map_T<T0(==), T1(==), T2(==)>(ghost counter_in:nat) returns (R:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == map[]

method {:axiom} New_Map_params<T0(==), T1(==)>(ghost U:map<T0, T1>, ghost counter_in:nat) returns (R:Map<T0, T1>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == map[]
  ensures R.Universe() == U

method {:axiom} New_Map_Map_T_params<T0(==), T1(==), T2(==)>(ghost U:map<map<T0, T1>, T2>, ghost UBSize_Keys:nat, ghost counter_in:nat) returns (R:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == map[]
  ensures R.Universe() == U
  ensures R.UBSize_Keys() == UBSize_Keys

ghost predicate in_universe_Map(M:Map, U:Map)
{
  M.Valid() &&
  U.Valid() &&
  (M.Universe().Keys <= U.Model().Keys) &&
  (forall k | k in M.Universe().Keys :: M.Universe()[k] == U.Model()[k])
}

ghost predicate in_universe_Map_Map_T(M:Map_Map_T, U:Map_Map_T)
{
  M.Valid() &&
  U.Valid() &&
  (M.Universe().Keys <= U.Model().Keys) &&
  (forall k | k in M.Universe().Keys :: M.Universe()[k] == U.Model()[k])
}
