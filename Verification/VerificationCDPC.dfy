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
    var cands_have_question:bool := true;
    var exists_answer_true:bool := false;
    var exists_answer_false:bool := false;
    
    while (!f'Empty && cands_have_question)
      decreases f'.Cardinality()
      invariant in_universe_Map_Map_T(f', f)
      invariant cands_have_question == (forall cand:candidate | cand in (f.Keys() - f'.Keys()) :: question in cand.Keys)
      invariant cands_have_question ==> (exists_answer_true == (exists cand:candidate | cand in (f.Keys() - f'.Keys()) :: cand[question] == true))
      invariant cands_have_question ==> (exists_answer_false == (exists cand:candidate | cand in (f.Keys() - f'.Keys()) :: cand[question] == false))
      invariant f'Empty == (f'.Cardinality() == 0)
    {
      f', f'Empty, cands_have_question, exists_answer_true, exists_answer_false, counter := loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f, f', question, exists_answer_true, exists_answer_false, counter);
      assert cands_have_question ==> (exists_answer_true == (exists cand:candidate | cand in (f.Keys() - f'.Keys()) :: cand[question] == true));
      assert cands_have_question ==> (exists_answer_false == (exists cand:candidate | cand in (f.Keys() - f'.Keys()) :: cand[question] == false));
    }

    var question_is_valid_and_not_trivial:bool := cands_have_question && exists_answer_true && exists_answer_false;

    assert question_is_valid_and_not_trivial ==
      ((forall cand:candidate | cand in f.Keys() :: question in cand.Keys) &&
      (exists cand:candidate | cand in f.Keys() :: cand[question] == true) &&
      (exists cand:candidate | cand in f.Keys() :: cand[question] == false));

    if question_is_valid_and_not_trivial {
      var f_true:Map_Map_T<int, bool, bool>; f_true, counter := candidates_with_same_answer(f, question, true, counter);
      var f_false:Map_Map_T<int, bool, bool>; f_false, counter := candidates_with_same_answer(f, question, false, counter);
      var g_true:Map_Map_T<int, bool, int>; g_true, counter := candidates_with_same_answer(g, question, true, counter);
      var g_false:Map_Map_T<int, bool, int>; g_false, counter := candidates_with_same_answer(g, question, false, counter);
      
      var iv_true:Interview; iv_true, counter := iv.Get(true, counter);
      var iv_false:Interview; iv_false, counter := iv.Get(false, counter);

      var recursive_true:bool; recursive_true, counter := verifyCDPC(f_true, g_true, P, a, b, x, y, iv_true, counter);
      var recursive_false:bool; recursive_false, counter := verifyCDPC(f_false, g_false, P, a, b, x, y, iv_false, counter);
      var ok:bool := question_is_valid_and_not_trivial && recursive_true && recursive_false;

      /*assert recursive_true == certificateCDPC(
        (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c]),
        (map c:candidate | c in g.Keys() && c[question] == true :: g.Model()[c]),
        P.Model(), a, b, x, y, iv.Model().True
      );
      assert recursive_false == certificateCDPC(
        (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c]),
        (map c:candidate | c in g.Keys() && c[question] == false :: g.Model()[c]),
        P.Model(), a, b, x, y, iv.Model().False
      );*/



      
      // Problem preconditions
      assert f.Valid() && g.Valid() && P.Valid() && iv.Valid();
      assert forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys;
      assert f.Keys() == g.Keys();
      assert forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys);
      assert 0.0 <= a <= b <= 1.0;
      assert 0.0 <= x <= y <= 1.0;
      // Information regarding the branch of the demonstration that we are focusing on
      assert iv.Model() != Null;
      assert question_is_valid_and_not_trivial == true;
      // Variables that have been calculated
      assert question == iv.Model().Key;
      assume false;
      assert question_is_valid_and_not_trivial ==
        ((forall cand:candidate | cand in f.Keys() :: question in cand.Keys) &&
        (exists cand:candidate | cand in f.Keys() :: cand[question] == true) &&
        (exists cand:candidate | cand in f.Keys() :: cand[question] == false));
      assert recursive_true ==
        certificateCDPC(
          (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c]),
          (map c:candidate | c in g.Keys() && c[question] == true :: g.Model()[c]),
          P.Model(), a, b, x, y, iv.Model().True
        );
      assert recursive_false ==
        certificateCDPC(
          (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c]),
          (map c:candidate | c in g.Keys() && c[question] == false :: g.Model()[c]),
          P.Model(), a, b, x, y, iv.Model().False
        );
      assert ok == question_is_valid_and_not_trivial && recursive_true && recursive_false;
      assume false;
      postcondition_verifyCDPC(f, g, P, a, b, x, y, iv, question, question_is_valid_and_not_trivial, recursive_true, recursive_false, ok);

      /*
      assume ok ==
        ((forall cand:candidate | cand in f.Keys() :: question in cand.Keys) &&
        (exists cand:candidate | cand in f.Keys() :: cand[question] == true) &&
        (exists cand:candidate | cand in f.Keys() :: cand[question] == false))
        &&
        certificateCDPC(
          (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c]),
          (map c:candidate | c in g.Keys() && c[question] == true :: g.Model()[c]),
          P.Model(), a, b, x, y, iv.Model().True
        )
        &&
        certificateCDPC(
          (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c]),
          (map c:candidate | c in g.Keys() && c[question] == false :: g.Model()[c]),
          P.Model(), a, b, x, y, iv.Model().False
        );
      assume ok ==
        (forall cand:candidate | cand in f.Keys() :: question in cand.Keys) &&
        (exists cand:candidate | cand in f.Keys() :: cand[question] == true) &&
        (exists cand:candidate | cand in f.Keys() :: cand[question] == false)
        &&
        certificateCDPC(
          (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c]),
          (map c:candidate | c in g.Keys() && c[question] == true :: g.Model()[c]),
          P.Model(), a, b, x, y, iv.Model().True
        )
        &&
        certificateCDPC(
          (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c]),
          (map c:candidate | c in g.Keys() && c[question] == false :: g.Model()[c]),
          P.Model(), a, b, x, y, iv.Model().False
        );
      assume r == certificateCDPC(f.Model(), g.Model(), P.Model(), a, b, x, y, iv.Model());
      */
      assume false;
      return ok, counter;
    }

    return false, counter;
  }
}



method loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f:Map_Map_T<int, bool, bool>, f'_in:Map_Map_T<int, bool, bool>, question:int, exists_answer_true:bool, exists_answer_false:bool, ghost counter_in:nat) returns (f':Map_Map_T<int, bool, bool>, f'_inEmpty:bool, cands_have_question:bool, exists_answer_true_out:bool, exists_answer_false_out:bool, ghost counter:nat)
  requires in_universe_Map_Map_T(f'_in, f)
  requires (forall cand:candidate | cand in (f.Keys() - f'_in.Keys()) :: question in cand.Keys)
  requires exists_answer_true == (exists cand:candidate | cand in (f.Keys() - f'_in.Keys()) :: cand[question] == true)
  requires exists_answer_false == (exists cand:candidate | cand in (f.Keys() - f'_in.Keys()) :: cand[question] == false)
  requires 0 < f'_in.Cardinality()
  ensures in_universe_Map_Map_T(f', f)
  ensures cands_have_question == (forall cand:candidate | cand in (f.Keys() - f'.Keys()) :: question in cand.Keys)
  ensures cands_have_question ==> (exists_answer_true_out == (exists cand:candidate | cand in (f.Keys() - f'.Keys()) :: cand[question] == true))
  ensures cands_have_question ==> (exists_answer_false_out == (exists cand:candidate | cand in (f.Keys() - f'.Keys()) :: cand[question] == false))
  ensures f'.Cardinality() == f'_in.Cardinality() - 1
  ensures f'_inEmpty == (f'.Cardinality() == 0)
  ensures counter <= counter_in + poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f)
{
  counter := counter_in;
  in_universe_lemma_Map_Map_T(f'_in, f);
  var cand:Map<int, bool>; cand, counter := f'_in.PickKey(counter);
  assert counter <= counter_in + f.UBSize_Keys();
  f', counter := f'_in.Remove(cand, counter);
  
  cands_have_question, counter := cand.ContainsKey(question, counter);
  
  if cands_have_question {
    var cand_answer:bool; cand_answer, counter := cand.Get(question, counter);
    exists_answer_true_out := exists_answer_true || cand_answer;
    exists_answer_false_out := exists_answer_false || !cand_answer;
  }
  else {
    exists_answer_true_out := exists_answer_true;
    exists_answer_false_out := exists_answer_false;
  }

  f'_inEmpty, counter := f'.Empty(counter);

  return f', f'_inEmpty, cands_have_question, exists_answer_true_out, exists_answer_false_out, counter;
}



method correct_apt_ratio(f:Map_Map_T<int, bool, bool>, x:real, y:real, ghost counter_in:nat) returns (r:bool, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= x <= y <= 1.0
  requires f.Cardinality() != 0
  ensures var aptRatio:real := (|(set isApt:candidate | isApt in f.Keys() && f.Model()[isApt] :: isApt)| as real) / (f.Cardinality() as real);
          r == (aptRatio <= x || y <= aptRatio)
  ensures counter <= counter_in + poly_correct_apt_ratio(f)
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
    invariant counter <= counter_in + f.UBSize() + 1 + (f.Cardinality() - f'.Cardinality())*poly_correct_apt_ratio_loop(f)
  {
    f', f'Empty, numApt, numTotal, counter := correct_apt_ratio_loop(f, f', numApt, numTotal, counter);
  }
  assert numTotal == f.Cardinality();
  identity_substraction_lemma(f.Keys(), f'.Keys());
  assert numApt == |(set aptCand:candidate | aptCand in (f.Keys()) && f.Model()[aptCand] :: aptCand)|;
  var aptRatio:real := (numApt as real) / (numTotal as real);

  return (aptRatio <= x || y <= aptRatio), counter;
}

method correct_apt_ratio_loop(f:Map_Map_T<int, bool, bool>, f'_in:Map_Map_T<int, bool, bool>, numApt_in:int, numTotal_in:int, ghost counter_in:nat) returns (f':Map_Map_T<int, bool, bool>, f'Empty:bool, numApt:int, numTotal:int, ghost counter:nat)
  requires in_universe_Map_Map_T(f'_in, f)
  requires f'_in.Cardinality() != 0
  requires numTotal_in == (f.Cardinality() - f'_in.Cardinality())
  requires numApt_in == |(set aptCand:candidate | aptCand in (f.Keys() - f'_in.Keys()) && f.Model()[aptCand] :: aptCand)|

  ensures f'.Cardinality() == f'_in.Cardinality() - 1
  ensures in_universe_Map_Map_T(f', f)
  ensures f'Empty == (f'.Cardinality() == 0)
  ensures numTotal == (f.Cardinality() - f'.Cardinality())
  ensures numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys()) && f.Model()[aptCand] :: aptCand)|
  ensures counter <= counter_in + poly_correct_apt_ratio_loop(f)
{
  counter := counter_in;
  in_universe_lemma_Map_Map_T(f'_in, f);
  numApt := numApt_in;
  numTotal := numTotal_in;
  var cand:Map<int, bool>; cand, counter := f'_in.PickKey(counter);
  assert counter <= counter_in + f.UBSize_Keys();
  f', counter := f'_in.Remove(cand, counter);
  var isApt:bool; isApt, counter := f.Get(cand, counter);
  if (isApt) {
    numApt := numApt + 1;
  }
  lemma_card_apt_set_when_remove_element(f.Model(), f.Keys() - f'.Keys(), cand.Model());
  assert numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys()) && f.Model()[aptCand] :: aptCand)| by {
    assert f'_in.Keys() == (f'.Keys() + {cand.Model()});
    assert (f.Keys() - (f'.Keys() + {cand.Model()})) == (f.Keys() - f'.Keys() - {cand.Model()});
    assert if isApt then numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys() - {cand.Model()}) && f.Model()[aptCand] :: aptCand)| + 1
          else           numApt == |(set aptCand:candidate | aptCand in (f.Keys() - f'.Keys() - {cand.Model()}) && f.Model()[aptCand] :: aptCand)|;
    lemma_card_apt_set_when_remove_element(f.Model(), f.Keys() - f'.Keys(), cand.Model());
  }

  numTotal := numTotal + 1;
  f'Empty, counter := f'.Empty(counter);
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
  ensures counter <= counter_in + poly_correct_private_ratio(f, P)
{
  counter := counter_in;

  r := true;
  var P':Set<int>; P', counter := P.Copy(counter);
  var P'Empty:bool; P'Empty, counter := P'.Empty(counter);
  assert counter <= counter_in + P.UBSize0() + 1;
  while (!P'Empty)
    decreases P'.Cardinality()
    invariant in_universe_Set(P', P)
    invariant P'Empty == (P'.Cardinality() == 0)
    invariant r == forall p:int | p in (P.Model() - P'.Model()) ::
                (
                  var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                  a <= privateRatio <= b
                )
    invariant counter <= counter_in + P.UBSize0() + 1 + (P.Cardinality() - P'.Cardinality())*poly_correct_private_ratio_outer_loop(f, P)
  {
    r, P', P'Empty, counter := correct_private_ratio_outer_loop(f, P, P', a, b, r, counter);
  }
  identity_substraction_lemma(P.Model(), P'.Model());

  return r, counter;
}


method correct_private_ratio_outer_loop(f:Map_Map_T<int, bool, bool>, P:Set<int>, P'_in:Set<int>, a:real, b:real, r_in:bool, ghost counter_in:nat) returns (r:bool, P':Set<int>, P'Empty:bool, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires 0.0 <= a <= b <= 1.0
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires f.Cardinality() != 0

  requires in_universe_Set(P'_in, P)
  requires P'_in.Cardinality() != 0
  requires r_in == forall p:int | p in (P.Model() - P'_in.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              )
  
  ensures P'.Cardinality() == P'_in.Cardinality() - 1
  ensures in_universe_Set(P', P)
  ensures P'Empty == (P'.Cardinality() == 0)
  ensures r == forall p:int | p in (P.Model() - P'.Model()) ::
              (
                var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real);
                a <= privateRatio <= b
              )
  ensures counter <= counter_in + poly_correct_private_ratio_outer_loop(f, P)
{
  counter := counter_in;
  var p:int; p, counter := P'_in.Pick(counter);
  
  P', counter := P'_in.Remove(p, counter);
  in_universe_lemma_Set(P'_in, P);
  in_universe_lemma_Set(P', P);

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
    invariant counter <= counter_in + f.UBSize() + P.UBSize0() + 2 + (f.Cardinality() - f'.Cardinality())*poly_correct_private_ratio_inner_loop(f)
  {
    //ghost var f'_prev := f';
    f', f'Empty, numTotal, numPriv, counter := correct_private_ratio_inner_loop(f, f', p, numTotal, numPriv, counter);
    //correct_private_ratio_outer_loop_restore_counter_invariant(f, f', f'_prev, P, counter, counter_in);
    //restore_counter_invariant(f.Cardinality(), f'.Cardinality(), f'_prev.Cardinality(), f.UBSize() + P.UBSize0() + 2, poly_correct_private_ratio_inner_loop(f), counter, counter_in);
  }
  identity_substraction_lemma(f.Keys(), f'.Keys());
  var privateRatio:real := (numPriv as real) / (numTotal as real);

  r := r_in && (a <= privateRatio <= b);
  P'Empty, counter := P'.Empty(counter);


  assert privateRatio == (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real) / (f.Cardinality() as real) by {
    assert (numTotal as real) == (f.Cardinality() as real);
    assert (numPriv as real) == (|(set isPrivate:candidate | isPrivate in f.Keys() && isPrivate[p] :: isPrivate)| as real);
  }
  lemma_private_ratio(f, P, P'_in, P', a, b, r_in, r, p, privateRatio);
  
  return r, P', P'Empty, counter;
}


method correct_private_ratio_inner_loop(f:Map_Map_T<int, bool, bool>, f'_in:Map_Map_T<int, bool, bool>, p:int, numTotal_in:int, numPriv_in:int, ghost counter_in:nat) returns (f':Map_Map_T<int, bool, bool>, f'Empty:bool, numTotal:int, numPriv:int, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate | c in f.Keys() :: (p in c.Keys)
  requires f.Cardinality() != 0
  requires f'_in.Cardinality() != 0
  
  requires in_universe_Map_Map_T(f'_in, f)
  requires numTotal_in == (f.Cardinality() - f'_in.Cardinality())
  requires numPriv_in == |(set privCand:candidate | privCand in (f.Keys() - f'_in.Keys()) && privCand[p] :: privCand)|
  
  ensures f'.Cardinality() == f'_in.Cardinality() - 1
  
  ensures in_universe_Map_Map_T(f', f)
  ensures numTotal == (f.Cardinality() - f'.Cardinality())
  ensures numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys()) && privCand[p] :: privCand)|
  ensures f'Empty == (f'.Cardinality() == 0)
  ensures counter <= counter_in + poly_correct_private_ratio_inner_loop(f)
{
  counter := counter_in;
  numPriv := numPriv_in;

  var cand:Map<int, bool>; cand, counter := f'_in.PickKey(counter);
  f', counter := f'_in.Remove(cand, counter);
  in_universe_lemma_Map_Map_T(f'_in, f);
  in_universe_lemma_Map_Map_T(f', f);
  var isPrivate:bool; isPrivate, counter := cand.Get(p, counter);
  if (isPrivate) {
    numPriv := numPriv_in + 1;
  }

  assert numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys()) && privCand[p] :: privCand)| by {
    assert f'_in.Keys() == (f'.Keys() + {cand.Model()});
    assert (f.Keys() - (f'.Keys() + {cand.Model()})) == (f.Keys() -f'.Keys() - {cand.Model()});
    assert if isPrivate then numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys() - {cand.Model()}) && privCand[p] :: privCand)| + 1
            else           numPriv == |(set privCand:candidate | privCand in (f.Keys() - f'.Keys() - {cand.Model()}) && privCand[p] :: privCand)|;
    lemma_card_priv_set_when_remove_element(f.Model(), f.Keys() - f'.Keys(), cand.Model(), p);
  }
  
  numTotal := numTotal_in + 1;
  f'Empty, counter := f'.Empty(counter);

  return f', f'Empty, numTotal, numPriv, counter;
}



method candidates_with_same_answer<T>(f:Map_Map_T<int, bool, T>, question:int, answer:bool, ghost counter_in:nat) returns (f_out:Map_Map_T<int, bool, T>, ghost counter:nat)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c
  ensures f_out.Valid()
  ensures f_out.Model() == (map c:candidate | c in f.Keys() && c[question] == answer :: f.Model()[c])
  ensures counter <= counter_in + poly_candidates_with_same_answer(f)
{
  counter := counter_in;

  var f':Map_Map_T<int, bool, T>; f', counter := f.Copy(counter);
  f_out, counter := New_Map_Map_T_params(f.Model(), f.UBSize_Keys(), counter_in);
  in_universe_lemma_Map_Map_T(f', f);
  in_universe_lemma_Map_Map_T(f_out, f);

  var f'Empty:bool; f'Empty, counter := f'.Empty(counter);
  
  assert counter <= counter_in + f.UBSize() + 2 + (f.Cardinality() - f'.Cardinality())*poly_candidates_with_same_answer_loop(f) by {
    assert (f.Cardinality() - f'.Cardinality()) == 0;
    assert (f.Cardinality() - f'.Cardinality())*poly_candidates_with_same_answer_loop(f) == 0;
  }
  while (!f'Empty)
    decreases f'.Cardinality()
    invariant in_universe_Map_Map_T(f', f)
    invariant in_universe_Map_Map_T(f_out, f)
    invariant f'Empty == (f'.Cardinality() == 0)
    invariant f_out.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])
    invariant counter <= counter_in + f.UBSize() + 2 + (f.Cardinality() - f'.Cardinality())*poly_candidates_with_same_answer_loop(f)
    invariant f'Empty == (f'.Cardinality() == 0)
  {
    ghost var f'_prev := f';
    f', f_out, f'Empty, counter := candidates_with_same_answer_loop(f, f', f_out, question, answer, counter);
    candidates_with_same_answer_restore_counter_invariant(f, f', f'_prev, counter, counter_in);
  }
  candidates_with_same_answer_counter_simplification(f, f', counter, counter_in);
  assert counter <= counter_in + poly_candidates_with_same_answer(f);

  return f_out, counter;
}


method candidates_with_same_answer_loop<T>(f:Map_Map_T<int, bool, T>, f'_in:Map_Map_T<int, bool, T>, f''_in:Map_Map_T<int, bool, T>, question:int, answer:bool, ghost counter_in:nat) returns (f':Map_Map_T<int, bool, T>, f'':Map_Map_T<int, bool, T>, f'Empty:bool, ghost counter:nat)
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c

  requires in_universe_Map_Map_T(f'_in, f)
  requires in_universe_Map_Map_T(f''_in, f)
  requires f'_in.Cardinality() != 0
  requires f''_in.Model() == (map c:candidate | c in (f.Keys() - f'_in.Keys()) && c[question] == answer :: f.Model()[c])

  ensures f'.Cardinality() == f'_in.Cardinality() - 1

  ensures in_universe_Map_Map_T(f', f)
  ensures in_universe_Map_Map_T(f'', f)
  ensures f'Empty == (f'.Cardinality() == 0)
  
  ensures f''.Model() == (map c:candidate | c in (f.Keys() - f'.Keys()) && c[question] == answer :: f.Model()[c])
  ensures counter <= counter_in + poly_candidates_with_same_answer_loop(f)
{
  in_universe_lemma_Map_Map_T(f'_in, f);
  in_universe_lemma_Map_Map_T(f''_in, f);

  counter := counter_in;
  var cand:Map<int, bool>; cand, counter := f'_in.PickKey(counter);
  f', counter := f'_in.Remove(cand, counter);

  var cand_answer:bool; cand_answer, counter := cand.Get(question, counter);

  if (cand_answer == answer) {
    var f_cand:T; f_cand, counter := f.Get(cand, counter);
    f'', counter := f''_in.Insert(cand, f_cand, counter);

    assert (forall k | k in f''_in.Universe().Keys :: f''.Universe()[k] == f.Universe()[k]);
    candidates_with_same_answer_lemma_1<T>(f, f'_in, f''_in, f', f'', cand, question, answer);
    //assert counter <= counter_in + 3*f.UBSize() + 2*f.UBSize_Keys();
  }
  else {
    f'', counter := f''_in.Copy(counter);
    candidates_with_same_answer_lemma_2(f, f'_in,  f''_in, f', f'', cand, question, answer);
    //assert counter <= counter_in + 2*f.UBSize() + 2*f.UBSize_Keys();
  }

  f'Empty, counter := f'.Empty(counter);

  return f', f'', f'Empty, counter;
}





// POLYNOMIALS





ghost function poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial<T>(f:Map_Map_T<int, bool, T>) : (o:nat)
{
  f.UBSize() + 3*f.UBSize_Keys() + 1
}

ghost function poly_correct_apt_ratio<T>(f:Map_Map_T<int, bool, T>) : (o:nat)
  ensures f.UBSize() + 1 + f.Cardinality()*poly_correct_apt_ratio_loop(f) <= o
{
  /*calc == {
    f.UBSize() + 1 + f.Cardinality()*poly_correct_apt_ratio_loop(f);
    f.UBSize() + 1 + f.Cardinality()*(2*f.UBSize() + f.UBSize_Keys() + 1);
    f.UBSize() + 1 + (2*f.UBSize()*f.Cardinality() + f.UBSize_Keys()*f.Cardinality() + f.Cardinality());
    f.UBSize() + 1 + (2*f.UBSize()*f.Cardinality() + f.UBSize() + f.Cardinality());
    2*f.UBSize()*f.Cardinality() + 2*f.UBSize() + f.Cardinality() + 1;
  }*/
  2*f.UBSize()*f.Cardinality() + 2*f.UBSize() + f.Cardinality() + 1
}

ghost function poly_correct_apt_ratio_loop<T>(f:Map_Map_T<int, bool, T>) : (o:nat)
{
  2*f.UBSize() + f.UBSize_Keys() + 1
}

ghost function poly_correct_private_ratio<T>(f:Map_Map_T<int, bool, T>, P:Set<int>) : (o:nat)
  ensures P.UBSize0() + 1 + P.Cardinality()*poly_correct_private_ratio_outer_loop(f, P) <= o
{
  /*calc == {
    P.UBSize0() + 1 + P.Cardinality()*poly_correct_private_ratio_outer_loop(f, P);
    P.UBSize0() + 1 + P.Cardinality()*(f.UBSize()*f.Cardinality() + 3*f.UBSize() + f.Cardinality() + P.UBSize0() + 3);
    P.UBSize0() + 1 + (f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality());
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0() + 1;
  }*/
  f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0() + 1
}

ghost function poly_correct_private_ratio_outer_loop<T>(f:Map_Map_T<int, bool, T>, P:Set<int>) : (o:nat)
  ensures f.UBSize() + P.UBSize0() + 3 + f.Cardinality()*poly_correct_private_ratio_inner_loop(f) <= o
{
  /*calc == {
    f.UBSize() + P.UBSize0() + 3 + f.Cardinality()*poly_correct_private_ratio_inner_loop(f);
    f.UBSize() + P.UBSize0() + 3 + f.Cardinality()*(f.UBSize() + 2*f.UBSize_Keys() + 1);
    f.UBSize() + P.UBSize0() + 3 + (f.UBSize()*f.Cardinality() + 2*f.UBSize_Keys()*f.Cardinality() + f.Cardinality());
    f.UBSize() + f.UBSize()*f.Cardinality() + 2*f.UBSize_Keys()*f.Cardinality() + f.Cardinality() + P.UBSize0() + 3;
    f.UBSize() + f.UBSize()*f.Cardinality() + 2*f.UBSize() + f.Cardinality() + P.UBSize0() + 3;
    f.UBSize()*f.Cardinality() + 3*f.UBSize() + f.Cardinality() + P.UBSize0() + 3;
  }*/
  f.UBSize()*f.Cardinality() + 3*f.UBSize() + f.Cardinality() + P.UBSize0() + 3
}

ghost function poly_correct_private_ratio_inner_loop<T>(f:Map_Map_T<int, bool, T>) : (o:nat)
{
  f.UBSize() + 2*f.UBSize_Keys() + 1
}

ghost function poly_candidates_with_same_answer<T>(f:Map_Map_T<int, bool, T>) : (o:nat)
{
  /*calc == {
    f.UBSize() + 2 + f.Cardinality()*poly_candidates_with_same_answer_loop(f);
    f.UBSize() + 2 + f.Cardinality()*(3*f.UBSize() + 2*f.UBSize_Keys() + 1);
    f.UBSize() + 2 + (3*f.UBSize()*f.Cardinality() + 2*f.UBSize_Keys()*f.Cardinality() + f.Cardinality());
    3*f.UBSize()*f.Cardinality() + 2*f.UBSize_Keys()*f.Cardinality() + f.UBSize() + f.Cardinality() + 2;
  }*/
  3*f.UBSize()*f.Cardinality() + 2*f.UBSize_Keys()*f.Cardinality() + f.UBSize() + f.Cardinality() + 2
}

ghost function poly_candidates_with_same_answer_loop<T>(f:Map_Map_T<int, bool, T>) : (o:nat)
{
  3*f.UBSize() + 2*f.UBSize_Keys() + 1
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

lemma candidates_with_same_answer_restore_counter_invariant<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>, f'_prev:Map_Map_T<int, bool, T>, counter:nat, counter_in:nat)
requires counter <= counter_in + f.UBSize() + 2 + (f.Cardinality() - f'_prev.Cardinality())*poly_candidates_with_same_answer_loop(f) + poly_candidates_with_same_answer_loop(f)
requires f'_prev.Cardinality() == (f'.Cardinality() + 1)
ensures counter <= counter_in + f.UBSize() + 2 + (f.Cardinality() - f'.Cardinality())*poly_candidates_with_same_answer_loop(f)
{
  /*assert (f.Cardinality() - f'_prev.Cardinality()) == (f.Cardinality() - (f'.Cardinality() + 1));
  assert (f.Cardinality() - f'_prev.Cardinality())*poly_candidates_with_same_answer_loop(f) == (f.Cardinality() - (f'.Cardinality() + 1))*poly_candidates_with_same_answer_loop(f);
  assert counter <= counter_in + f.UBSize() + 2 + (f.Cardinality() - (f'.Cardinality() + 1))*poly_candidates_with_same_answer_loop(f) + poly_candidates_with_same_answer_loop(f);*/
}

/*lemma correct_private_ratio_outer_loop_restore_counter_invariant<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>, f'_prev:Map_Map_T<int, bool, T>, P:Set<int>, counter:nat, counter_in:nat)
requires counter <= counter_in + f.UBSize() + P.UBSize0() + 2 + (f.Cardinality() - f'_prev.Cardinality())*poly_correct_private_ratio_inner_loop(f) + poly_correct_private_ratio_inner_loop(f)
requires f'_prev.Cardinality() == (f'.Cardinality() + 1)
ensures counter <= counter_in + f.UBSize() + P.UBSize0() + 2 + (f.Cardinality() - f'.Cardinality())*poly_correct_private_ratio_inner_loop(f)
{
}

lemma restore_counter_invariant(card:nat, card':nat, card'_prev:nat, counter_before:nat, counter_loop:nat, counter:nat, counter_in:nat)
requires counter <= counter_in + counter_before + (card - card'_prev)*counter_loop + counter_loop
requires card'_prev == (card' + 1)
ensures counter <= counter_in + counter_before + (card - card')*counter_loop
{
}*/

lemma candidates_with_same_answer_counter_simplification<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>, counter:nat, counter_in:nat)
  requires f'.Cardinality() == 0
  requires counter <= counter_in + f.UBSize() + 2 + (f.Cardinality() - f'.Cardinality())*poly_candidates_with_same_answer_loop(f)
  ensures counter <= counter_in + poly_candidates_with_same_answer(f)
{
  //identity_substraction_lemma(f.Keys(), f'.Keys());
  //assert counter <= counter_in + f.UBSize() + 2 + f.Cardinality()*poly_candidates_with_same_answer_loop(f);
}

lemma postcondition_verifyCDPC(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview, question:int, question_is_valid_and_not_trivial:bool, recursive_true:bool, recursive_false:bool, ok:bool)
  // Problem preconditions
  requires f.Valid() && g.Valid() && P.Valid() && iv.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires f.Keys() == g.Keys()
  requires forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
  // Information regarding the branch of the demonstration that we are focusing on
  requires iv.Model() != Null
  requires question_is_valid_and_not_trivial == true
  // Variables that have been calculated
  requires question == iv.Model().Key
  requires question_is_valid_and_not_trivial ==
    ((forall cand:candidate | cand in f.Keys() :: question in cand.Keys) &&
    (exists cand:candidate | cand in f.Keys() :: cand[question] == true) &&
    (exists cand:candidate | cand in f.Keys() :: cand[question] == false))
  requires recursive_true ==
    certificateCDPC(
      (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c]),
      (map c:candidate | c in g.Keys() && c[question] == true :: g.Model()[c]),
      P.Model(), a, b, x, y, iv.Model().True
    )
  requires recursive_false ==
    certificateCDPC(
      (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c]),
      (map c:candidate | c in g.Keys() && c[question] == false :: g.Model()[c]),
      P.Model(), a, b, x, y, iv.Model().False
    )
  requires ok == question_is_valid_and_not_trivial && recursive_true && recursive_false
  // Postcondition
  ensures ok == certificateCDPC(f.Model(), g.Model(), P.Model(), a, b, x, y, iv.Model())
{}


ghost predicate pred_problem_preconditions(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview)
{
  (f.Valid() && g.Valid() && P.Valid() && iv.Valid()) &&
  (forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys) &&
  (f.Keys() == g.Keys()) &&
  (forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)) &&
  (0.0 <= a <= b <= 1.0) &&
  (0.0 <= x <= y <= 1.0)
}

ghost predicate pred_branch_info(iv:Interview, question_is_valid_and_not_trivial:bool)
{
  (iv.Model() != Null) &&
  (question_is_valid_and_not_trivial == true)
}

ghost predicate pred_calc_variables(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview, question:int, question_is_valid_and_not_trivial:bool, recursive_true:bool, recursive_false:bool, ok:bool)
  requires pred_problem_preconditions(f, g, P, a, b, x, y, iv) && pred_branch_info(iv, question_is_valid_and_not_trivial)
{
  (question == iv.Model().Key) &&
  (question_is_valid_and_not_trivial ==
    ((forall cand:candidate | cand in f.Keys() :: question in cand.Keys) &&
    (exists cand:candidate | cand in f.Keys() :: cand[question] == true) &&
    (exists cand:candidate | cand in f.Keys() :: cand[question] == false))
  ) &&
  (recursive_true ==
    certificateCDPC(
      (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c]),
      (map c:candidate | c in g.Keys() && c[question] == true :: g.Model()[c]),
      P.Model(), a, b, x, y, iv.Model().True
    )
  ) &&
  (recursive_false ==
    certificateCDPC(
      (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c]),
      (map c:candidate | c in g.Keys() && c[question] == false :: g.Model()[c]),
      P.Model(), a, b, x, y, iv.Model().False
    )
  ) &&
  (ok == question_is_valid_and_not_trivial && recursive_true && recursive_false)
}


