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



method loop_check_that_candidates_have_question(f:Map_Map_T<int, bool, bool>, f':Map_Map_T<int, bool, bool>, question:int, ok:bool, ghost counter_in:nat) returns (f'_out:Map_Map_T<int, bool, bool>, ok_out:bool, ghost counter:nat)
  requires in_universe_Map_Map_T(f', f)
  requires ok == (forall cand:candidate | cand in (f.Keys() - f'.Keys()) :: question in cand.Keys)
  ensures in_universe_Map_Map_T(f'_out, f)
  ensures ok_out == (forall cand:candidate | cand in (f.Keys() - f'_out.Keys()) :: question in cand.Keys)
  ensures f'_out.Cardinality() == f'.Cardinality() - 1
{
  counter := counter_in;
  var cand:Map<int, bool>; cand, counter := f'.PickKey(counter);
  f'_out, counter := f'.Remove(cand, counter);
  
  var candHasQuestion:bool; candHasQuestion, counter := cand.ContainsKey(question, counter);
  ok_out := ok && candHasQuestion;

  return f'_out, ok_out, counter;
}



method correct_apt_ratio(f:Map_Map_T<int, bool, bool>, x:real, y:real, ghost counter_in:nat) returns (r:bool, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= x <= y <= 1.0
  requires f.Cardinality() != 0
  ensures var aptRatio:real := (|(set isApt:candidate | isApt in f.Keys() && f.Model()[isApt] :: isApt)| as real) / (f.Cardinality() as real);
          r == (aptRatio <= x || y <= aptRatio)
{

  counter := counter_in;
  var f':Map_Map_T<int, bool, bool>; f', counter := f.Copy(counter);
  var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
  var numApt:int := 0;
  var numTotal:int := 0;

  while (!f'Empty)
    decreases f'.Cardinality()
    invariant in_universe_Map_Map_T(f', f)
    invariant f'Empty == (f'.Cardinality() == 0)
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
    f'Empty, counter := f'.Empty(counter);

  }
  assert numTotal == f.Cardinality();
  identity_substraction_lemma(f.Keys(), f'.Keys());
  assert numApt == |(set aptCand:candidate | aptCand in (f.Keys()) && f.Model()[aptCand] :: aptCand)|;
  var aptRatio:real := (numApt as real) / (numTotal as real);
  return (aptRatio <= x || y <= aptRatio), counter;
}



method correct_private_ratio(f:Map_Map_T<int, bool, bool>, P:Set<int>, a:real, b:real, ghost counter_in:nat) returns (r:bool, ghost counter:nat)
  requires f.Valid()
  requires P.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= a <= b <= 1.0
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires f.Cardinality() != 0
  ensures r == forall p:int | p in P.Model() ::
                (
                  var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                  a <= privateRatio <= b
                )
{
  counter := counter_in;

  r := true;
  var P':Set<int>; P', counter := P.Copy(counter);
  var P'Empty:bool; P'Empty, counter := P'.Empty(counter);
  while (!P'Empty)
    decreases P'.Cardinality()
    invariant in_universe_Set(P', P)
    invariant P'Empty == (P'.Cardinality() == 0)
    invariant r == forall p:int | p in (P.Model() - P'.Model()) ::
                (
                  var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                  a <= privateRatio <= b
                )
  {
    r, P', P'Empty, counter := correct_private_ratio_outer_loop(f, P, P', a, b, r, counter);
  }
  identity_substraction_lemma(P.Model(), P'.Model());

  return r, counter;
}


method correct_private_ratio_outer_loop(f:Map_Map_T<int, bool, bool>, P:Set<int>, P':Set<int>, a:real, b:real, r:bool, ghost counter_in:nat) returns (r_out:bool, P'_out:Set<int>, P'Empty:bool, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= a <= b <= 1.0
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires f.Cardinality() != 0

  requires in_universe_Set(P', P)
  requires P'.Cardinality() != 0
  requires r == forall p:int | p in (P.Model() - P'.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              )
  
  ensures P'_out.Cardinality() < P'.Cardinality()
  ensures in_universe_Set(P'_out, P)
  ensures P'Empty == (P'_out.Cardinality() == 0)
  ensures r_out == forall p:int | p in (P.Model() - P'_out.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              )

{
  counter := counter_in;
  var p:int; p, counter := P'.Pick(counter);
  
  P'_out, counter := P'.Remove(p, counter);

  var f':Map_Map_T<int, bool, bool>; f', counter := f.Copy(counter);
  var numPriv:int := 0;
  var numTotal:int := 0;
  var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
  
  while (!f'Empty)
    decreases f'.Cardinality()
    invariant in_universe_Map_Map_T(f', f)
    invariant numTotal == (f.Cardinality() - f'.Cardinality())
    invariant numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys()) && privCand[p] :: privCand)|
    invariant f'Empty == (f'.Cardinality() == 0)
  {
    f', f'Empty, numTotal, numPriv, counter := correct_private_ratio_inner_loop(f, f', p, numTotal, numPriv, counter);
  }
  identity_substraction_lemma(f.Keys(), f'.Keys());
  var privateRatio:real := (numPriv as real) / (numTotal as real);

  r_out := r && (a <= privateRatio <= b);
  P'Empty, counter := P'_out.Empty(counter);


  assert privateRatio == (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real) by {
    assert (numTotal as real) == (f.Cardinality() as real);
    assert (numPriv as real) == (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real);
  }
  lemma_private_ratio(f, P, P', P'_out, a, b, r, r_out, p, privateRatio);
  
  return r_out, P'_out, P'Empty, counter;
}


method correct_private_ratio_inner_loop(f:Map_Map_T<int, bool, bool>, f':Map_Map_T<int, bool, bool>, p:int, numTotal:int, numPriv:int, ghost counter_in:nat) returns (f'_out:Map_Map_T<int, bool, bool>, f'_Empty:bool, numTotal':int, numPriv':int, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate | c in f.Keys() :: (p in c.Keys)
  requires f.Cardinality() != 0
  
  requires in_universe_Map_Map_T(f', f)
  requires numTotal == (f.Cardinality() - f'.Cardinality())
  requires numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys()) && privCand[p] :: privCand)|
  
  ensures f'_out.Cardinality() < f'.Cardinality()
  
  ensures in_universe_Map_Map_T(f'_out, f)
  ensures numTotal' == (f.Cardinality() - f'_out.Cardinality())
  ensures numPriv' == |(set privCand:candidate | privCand in (f.Keys() - f'_out.Keys()) && privCand[p] :: privCand)|
  ensures f'_Empty == (f'_out.Cardinality() == 0)
{
  counter := counter_in;
  numPriv' := numPriv;

  var cand:Map<int, bool>; cand, counter := f'.PickKey(counter);
  f'_out, counter := f'.Remove(cand, counter);
  var isPrivate:bool; isPrivate, counter := cand.Get(p, counter);
  if (isPrivate) {
    numPriv' := numPriv + 1;
  }

  assert numPriv' == |(set privCand:candidate | privCand in (f.Keys() - f'_out.Keys()) && privCand[p] :: privCand)| by {
    assert f'.Keys() == (f'_out.Keys() + {cand.Model()});
    assert (f.Keys() - (f'_out.Keys() + {cand.Model()})) == (f.Keys() -f'_out.Keys() - {cand.Model()});
    assert if isPrivate then numPriv' == |(set privCand:candidate | privCand in (f.Keys() - f'_out.Keys() - {cand.Model()}) && privCand[p] :: privCand)| + 1
            else           numPriv' == |(set privCand:candidate | privCand in (f.Keys() - f'_out.Keys() - {cand.Model()}) && privCand[p] :: privCand)|;
    lemma_card_priv_set_when_remove_element(f.Model(), f.Keys() - f'_out.Keys(), cand.Model(), p);
  }
  
  numTotal' := numTotal + 1;
  f'_Empty, counter := f'_out.Empty(counter);

  return f'_out, f'_Empty, numTotal', numPriv', counter;
}



method candidates_with_same_answer<T>(f:Map_Map_T<int, bool, T>, question:int, answer:bool, ghost counter_in:nat) returns (f_out:Map_Map_T<int, bool, T>, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c
  ensures f_out.Model() == (map c:candidate | c in f.Keys() && c[question] == answer :: f.Model()[c])
{
  counter := counter_in;

  var f':Map_Map_T<int, bool, T>; f', counter := f.Copy(counter);
  f_out, counter := New_Map_Map_T_params(f.Model(), f.UBSize_Keys(), counter_in);

  var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
  
  while (!f'Empty)
    decreases f'.Cardinality()
    invariant in_universe_Map_Map_T(f', f)
    invariant in_universe_Map_Map_T(f_out, f)
    invariant f'Empty == (f'.Cardinality() == 0)
    invariant f_out.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])
  {
    f', f_out, f'Empty, counter := candidates_with_same_answer_loop(f, f', f_out, question, answer, counter);
  }
  identity_substraction_lemma(f.Keys(), f'.Keys());

  return f_out, counter;
}


method candidates_with_same_answer_loop<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>, f'':Map_Map_T<int, bool, T>, question:int, answer:bool, ghost counter_in:nat) returns (f'_out:Map_Map_T<int, bool, T>, f''_out:Map_Map_T<int, bool, T>, f'Empty:bool, ghost counter:nat)
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c

  requires in_universe_Map_Map_T(f', f)
  requires in_universe_Map_Map_T(f'', f)
  requires f'.Cardinality() != 0
  requires f''.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])

  ensures f'_out.Cardinality() < f'.Cardinality()

  ensures in_universe_Map_Map_T(f'_out, f)
  ensures in_universe_Map_Map_T(f''_out, f)
  ensures f'Empty == (f'_out.Cardinality() == 0)
  
  ensures f''_out.Model() == (map c:candidate | c in (f.Keys() - f'_out.Keys()) && c[question] == answer :: f.Model()[c])
{
  counter := counter_in;
  var cand:Map<int, bool>; cand, counter := f'.PickKey(counter);
  f'_out, counter := f'.Remove(cand, counter);

  var cand_answer:bool; cand_answer, counter := cand.Get(question, counter);
  if (cand_answer == answer) {
    var f_cand:T; f_cand, counter := f.Get(cand, counter);
    f''_out, counter := f''.Insert(cand, f_cand, counter);

    assert (forall k | k in f''.Universe().Keys :: f''_out.Universe()[k] == f.Model()[k]);
    candidates_with_same_answer_lemma_1<T>(f, f',  f'', f'_out, f''_out, cand, question, answer);
  }
  else {
    f''_out, counter := f''.Copy(counter);
    candidates_with_same_answer_lemma_2(f, f',  f'', f'_out, f''_out, cand, question, answer);
  }

  f'Empty, counter := f'_out.Empty(counter);

  return f'_out, f''_out, f'Empty, counter;
}



// LEMMAS



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



lemma lemma_private_ratio(f:Map_Map_T<int, bool, bool>, P:Set<int>, P':Set<int>, P'':Set<int>, a:real, b:real, r:bool, r':bool, p:int, privateRatio:real)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= a <= b <= 1.0
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires f.Cardinality() != 0

  requires in_universe_Set(P', P)
  requires P'.Cardinality() != 0
  requires r == forall p:int | p in (P.Model() - P'.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              )
  

  requires P'.Model() == (P''.Model() + {p})
  requires p !in P''.Model()
  requires privateRatio == (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real)
  requires r' == (r && (a <= privateRatio <= b))

  ensures r' == forall p:int | p in (P.Model() - P''.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              )

{
  assert r == forall p:int | p in (P.Model() - P'.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              );
  assert r' == ((forall p:int | p in (P.Model() - P'.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              ))
              &&
              (a <= privateRatio <= b))
              ;
  assert (P.Model() - P''.Model()) == ((P.Model() - P'.Model()) + {p});
}



lemma candidates_with_same_answer_lemma_1<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>,  f'':Map_Map_T<int, bool, T>, f'_out:Map_Map_T<int, bool, T>, f''_out:Map_Map_T<int, bool, T>, cand:Map<int, bool>, question:int, answer:bool)
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c
  requires in_universe_Map_Map_T(f', f)
  requires in_universe_Map_Map_T(f'', f)
  requires f'.Cardinality() != 0
  requires f''.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])

  requires f'_out.Keys() == f'.Keys() - {cand.Model()}
  requires cand.Model() in f'.Model()
  requires cand.Model()[question] == answer
  requires f''_out.Model() == f''.Model()[cand.Model() := f.Model()[cand.Model()]]

  ensures f''_out.Model() == (map c:candidate | c in (f.Keys() - f'_out.Keys()) && c[question] == answer :: f.Model()[c])
{
  assert f''_out.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])[cand.Model() := f.Model()[cand.Model()]];
  candidates_with_same_answer_lemma_1_aux(f, f', cand, question, answer);
  assert f''_out.Model() == (map c:candidate | c in (f.Keys() - f'.Keys() + {cand.Model()}) && c[question] == answer :: f.Model()[c]);

  assert f'_out.Keys() == f'.Keys() - {cand.Model()};
  assert (f.Keys() - f'.Keys() + {cand.Model()}) == (f.Keys() - f'_out.Keys());
}


lemma candidates_with_same_answer_lemma_2<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>,  f'':Map_Map_T<int, bool, T>, f'_out:Map_Map_T<int, bool, T>, f''_out:Map_Map_T<int, bool, T>, cand:Map<int, bool>, question:int, answer:bool)
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c
  requires in_universe_Map_Map_T(f', f)
  requires in_universe_Map_Map_T(f'', f)
  requires f'.Cardinality() != 0
  requires f''.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])

  requires f'_out.Keys() == f'.Keys() - {cand.Model()}
  requires cand.Model() in f'.Model()
  requires cand.Model()[question] != answer
  requires f''_out.Model() == f''.Model()

  ensures f''_out.Model() == (map c:candidate | c in (f.Keys() - f'_out.Keys()) && c[question] == answer :: f.Model()[c])
{
  assert f''_out.Model() == f''.Model();
  assert f''_out.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c]);
  candidates_with_same_answer_lemma_2_aux(f, f'_out, cand, question, answer);
  assert f''_out.Model() == (map c:candidate | c in (f.Keys() - f'_out.Keys() - {cand.Model()}) && c[question] == answer :: f.Model()[c]);
  assert forall c:candidate | c in (f.Keys() - f'_out.Keys() - {cand.Model()}) && c[question] == answer :: c !in {cand.Model()};
  assert forall c:candidate | c in (f.Keys() - f'_out.Keys() - {cand.Model()}) && c[question] == answer :: c in (f.Keys() - f'_out.Keys());

  assert (map c:candidate | c in (f.Keys() - f'_out.Keys() - {cand.Model()}) && c[question] == answer :: f.Model()[c]) ==
          (map c:candidate | c in (f.Keys() - f'_out.Keys()) && c[question] == answer :: f.Model()[c]);
}


lemma candidates_with_same_answer_lemma_1_aux<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>, cand:Map<int, bool>, question:int, answer:bool)
  requires forall c:candidate |  c in f.Keys() :: question in c
  requires cand.Model() in f.Model()
  requires cand.Model()[question] == answer

  ensures 
          (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])[cand.Model() := f.Model()[cand.Model()]]
          ==
          (map c:candidate | c in (f.Keys() - f'.Keys() + {cand.Model()}) && c[question] == answer :: f.Model()[c])
{}

lemma candidates_with_same_answer_lemma_2_aux<T>(f:Map_Map_T<int, bool, T>, f'_out:Map_Map_T<int, bool, T>, cand:Map<int, bool>, question:int, answer:bool)
  requires forall c:candidate |  c in f.Keys() :: question in c
  requires cand.Model() in f.Model()
  requires cand.Model()[question] != answer

  ensures (map c:candidate | c in (f.Keys() - f'_out.Keys() - {cand.Model()}) && c[question] == answer :: f.Model()[c]) ==
          (map c:candidate | c in (f.Keys() - f'_out.Keys()) && c[question] == answer :: f.Model()[c])
{}
