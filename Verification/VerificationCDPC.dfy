include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"
include "../Auxiliary/Interview.dfy"


method verifyCDPC(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview, ghost counter_in:nat) returns (r:bool, ghost counter:nat)
  decreases iv.Questions()
  requires f.Valid() && g.Valid() && P.Valid() && iv.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires f.Keys() == g.Keys()
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
  ensures r == certificateCDPC(f.Model(), g.Model(), P.Model(), a, b, x, y, iv.Model())
  {
    counter := counter_in;
    var isEmpty:bool; isEmpty, counter := iv.Empty(counter);
    if (isEmpty) {
      var nCandidates:int; nCandidates, counter := f.nPairs(counter);
      if (nCandidates == 0) {
        return true, counter;
      }
      else {
        var okApt:bool; okApt, counter := correct_apt_ratio(f, x, y, counter);
        var okPrivate:bool; okPrivate, counter := correct_private_ratio(f, P, a, b, counter);

        assert iv.Model() == Null && |f.Model()| != 0;
        ghost var aptGhost:real :=(|(set aptCand:candidate | aptCand in f.Keys() && f.Model()[aptCand] :: aptCand)| as real) / (f.Cardinality() as real);
        ghost var aptPrivate := forall p:int | p in P.Model() ::
              (
                var privateRatio:real := (|(set privCand:candidate | privCand in f.Keys() && privCand[p] :: privCand)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              );
        
        assume okApt == (aptGhost <= x || y <= aptGhost);
        assume okPrivate == aptPrivate;

        return okApt && okPrivate, counter;
      }
    }
    else {
      var question:int; question, counter := iv.Key(counter);
      var f':Map_Map_T<int, bool, bool>; f', counter := f.Copy(counter);
      var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
      var ok:bool := true;

      while (!f'Empty)
        decreases f'.Cardinality()
        invariant in_universe_Map_Map_T(f', f)
        invariant ok == (forall cand:candidate | cand in (f.Keys() - f'.Keys()) :: question in cand.Keys)
      {
        f', ok, counter := loop_check_that_candidates_have_question(f, f', question, ok, counter);
      }

      var f_true:Map_Map_T<int, bool, bool>; f_true, counter := candidates_with_same_answer(f, question, true, counter);
      var f_false:Map_Map_T<int, bool, bool>; f_false, counter := candidates_with_same_answer(f, question, false, counter);
      var g_true:Map_Map_T<int, bool, int>; g_true, counter := candidates_with_same_answer(g, question, true, counter);
      var g_false:Map_Map_T<int, bool, int>; g_false, counter := candidates_with_same_answer(g, question, false, counter);
      
      var iv_true:Interview; iv_true, counter := iv.Get(true, counter);
      var iv_false:Interview; iv_false, counter := iv.Get(false, counter);

      var b_true:bool; b_true, counter := verifyCDPC(f_true, g_true, P, a, b, x, y, iv_true, counter);
      var b_false:bool; b_false, counter := verifyCDPC(f_false, g_false, P, a, b, x, y, iv_false, counter);
      ok := ok && b_true && b_false;

      return ok, counter;
    }
  }


method loop_check_that_candidates_have_question(f:Map_Map_T<int, bool, bool>, f':Map_Map_T<int, bool, bool>, question:int, ok:bool, ghost counter_in:nat) returns (f'':Map_Map_T<int, bool, bool>, ok':bool, ghost counter:nat)
  requires in_universe_Map_Map_T(f', f)
  requires ok == (forall cand:candidate | cand in (f.Keys() - f'.Keys()) :: question in cand.Keys)
  ensures in_universe_Map_Map_T(f'', f)
  ensures ok' == (forall cand:candidate | cand in (f.Keys() - f''.Keys()) :: question in cand.Keys)
  ensures f''.Cardinality() == f'.Cardinality() - 1
{
  counter := counter_in;
  var cand:Map<int, bool>; cand, counter := f'.PickKey(counter);
  f'', counter := f'.Remove(cand, counter);
  
  var candHasQuestion:bool; candHasQuestion, counter := cand.ContainsKey(question, counter);
  ok' := ok && candHasQuestion;

  return f'', ok', counter;
}


method correct_apt_ratio(f:Map_Map_T<int, bool, bool>, x:real, y:real, ghost counter_in:nat) returns (r:bool, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= x <= y <= 1.0
  requires f.Cardinality() != 0
  ensures var aptRatio:real := (|(set isApt:candidate | isApt in f.Keys() && f.Model()[isApt] :: isApt)| as real) / (f.Cardinality() as real);
          (aptRatio <= x || y <= aptRatio)
{
  counter := counter_in;
  var f':Map_Map_T<int, bool, bool>; f', counter := f.Copy(counter);
  var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
  var numApt:int := 0;
  var numTotal:int := 0;

  while (!f'Empty)
    decreases f'.Cardinality()
    invariant in_universe_Map_Map_T(f', f)
    invariant numTotal == (f.Cardinality() - f'.Cardinality())
    invariant numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys()) && f.Model()[aptCand] :: aptCand)|
  {
    ghost var f'prev := f';
    var cand:Map<int, bool>; cand, counter := f'.PickKey(counter);
    f', counter := f'.Remove(cand, counter);
    var isApt:bool; isApt, counter := f.Get(cand, counter);
    if (isApt) {
      numApt := numApt + 1;
    }
    assert numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys()) && f.Model()[aptCand] :: aptCand)| by {
      assert f'prev.Keys() == (f'.Keys() + {cand.Model()});
      assert (f.Keys() - (f'.Keys() + {cand.Model()})) == (f.Keys() - f'.Keys() - {cand.Model()});
      assert if isApt then numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys() - {cand.Model()}) && f.Model()[aptCand] :: aptCand)| + 1
            else           numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys() - {cand.Model()}) && f.Model()[aptCand] :: aptCand)|;
      lemma_card_apt_set_when_remove_element(f.Model(), f.Keys() - f'.Keys(), cand.Model());
    }
    numTotal := numTotal + 1;
    var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
  }

  var aptRatio:real := (numApt as real) / (numTotal as real);
  return (aptRatio <= x || y <= aptRatio), counter;   // ???
}

method correct_private_ratio(f:Map_Map_T<int, bool, bool>, P:Set<int>, a:real, b:real, ghost counter_in:nat) returns (r:bool, ghost counter:nat)
  requires f.Valid()
  requires P.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= a <= b <= 1.0
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires f.Cardinality() != 0
  ensures forall p:int | p in P.Model() ::
        (
          var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
          a <= privateRatio <= b
        )
{
  counter := counter_in;

  r := true;
  var P':Set<int>; P', counter := P.Copy(counter);
  var P'Empty:bool; P'Empty, counter := P.Empty(counter);
  while (!P'Empty)
    decreases P'.Cardinality()
    invariant in_universe_Set(P', P)
  {
    var p:int; p, counter := P.Pick(counter);

    var f':Map_Map_T<int, bool, bool>; f', counter := f.Copy(counter);
    var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
    var numPriv:int := 0;
    var numTotal:int := 0;
    
    while (!f'Empty)
      decreases f'.Cardinality()
      invariant in_universe_Map_Map_T(f', f)
      invariant numTotal == (f.Cardinality() - f'.Cardinality())
      invariant numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys()) && privCand[p] :: privCand)|
    {
      ghost var f'prev := f';
      var cand:Map<int, bool>; cand, counter := f'.PickKey(counter);
      f', counter := f'.Remove(cand, counter);
      var isPrivate:bool; isPrivate, counter := cand.Get(p, counter);
      if (isPrivate) {
        numPriv := numPriv + 1;
      }

      assert numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys()) && privCand[p] :: privCand)| by {
        assert f'prev.Keys() == (f'.Keys() + {cand.Model()});
        assert (f.Keys() - (f'.Keys() + {cand.Model()})) == (f.Keys() - f'.Keys() - {cand.Model()});
        assert if isPrivate then numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys() - {cand.Model()}) && privCand[p] :: privCand)| + 1
              else           numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys() - {cand.Model()}) && privCand[p] :: privCand)|;
        lemma_card_priv_set_when_remove_element(f.Model(), f.Keys() - f'.Keys(), cand.Model(), p);
      }

      
      numTotal := numTotal + 1;
      var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
    }

    var privateRatio:real := (numPriv as real) / (numTotal as real);

    assert forall p:int | p in P.Model() ::
          (
            var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
            a <= privateRatio <= b
          );

    r := r && (a <= privateRatio <= b);
  }

  return r, counter;
}


method candidates_with_same_answer<T>(f:Map_Map_T<int, bool, T>, question:int, answer:bool, ghost counter_in:nat) returns (f':Map_Map_T<int, bool, T>, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c
  ensures f'.Model() == (map c:candidate | c in f.Keys() && c[question] == answer :: f.Model()[c])


lemma lemma_card_apt_set_when_remove_element(f:map<candidate, bool>, cands:set<candidate>, cand:candidate)
  requires cand in cands
  requires cands <= f.Keys
  ensures if f[cand] then
            (|(set aptCand:candidate | aptCand in cands && f[aptCand] :: aptCand)|
            ==
            |(set aptCand:candidate | aptCand in (cands - {cand}) && f[aptCand] :: aptCand)| + 1)
          else
            |(set aptCand:candidate | aptCand in cands && f[aptCand] :: aptCand)|
            ==
            |(set aptCand:candidate | aptCand in (cands - {cand}) && f[aptCand] :: aptCand)|
{
  if f[cand] {
    assert (set aptCand:candidate | aptCand in (cands - {cand}) && f[aptCand] :: aptCand) + {cand}
            ==
            (set aptCand:candidate | aptCand in cands && f[aptCand] :: aptCand);
  }
  else {
    assert (set aptCand:candidate | aptCand in (cands - {cand}) && f[aptCand] :: aptCand)
            ==
            (set aptCand:candidate | aptCand in cands && f[aptCand] :: aptCand);
  }
}
lemma lemma_card_priv_set_when_remove_element(f:map<candidate, bool>, cands:set<candidate>, cand:candidate, p:int)
  requires cand in cands
  requires cands <= f.Keys
  requires forall c:candidate | c in f.Keys :: p in c.Keys
  ensures if cand[p] then
            (|(set privCand:candidate | privCand in cands && privCand[p] :: privCand)|
            ==
            |(set privCand:candidate | privCand in (cands - {cand}) && privCand[p] :: privCand)| + 1)
          else
            |(set privCand:candidate | privCand in cands && privCand[p] :: privCand)|
            ==
            |(set privCand:candidate | privCand in (cands - {cand}) && privCand[p] :: privCand)|
{
  if cand[p] {
    assert (set privCand:candidate | privCand in (cands - {cand}) && privCand[p] :: privCand) + {cand}
            ==
            (set privCand:candidate | privCand in cands && privCand[p] :: privCand);
  }
  else {
    assert (set privCand:candidate | privCand in (cands - {cand}) && privCand[p] :: privCand)
            ==
            (set privCand:candidate | privCand in cands && privCand[p] :: privCand);
  }
}
