include "../Problems/CDPC.dfy"
include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"
include "../Auxiliary/Interview.dfy"



// POLYNOMIALS



ghost opaque function poly_verifyCDPC(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, iv:Interview) : (o:nat)
{
  (|iv.Questions()|*f.Cardinality() + 1)*poly_verifyCDPC_node(f, g, P, iv)
}

ghost opaque function poly_verifyCDPC_node(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, iv:Interview) : (o:nat)
  ensures poly_verifyCDPC_base_case(f, g, P, iv) + 1 <= o
  ensures f.UBSize() + 3 + f.Cardinality()*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) <= o
  ensures f.UBSize() + 3 + f.Cardinality()*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) + 2*poly_candidates_with_same_answer(f) + 2*poly_candidates_with_same_answer(g) + 2*iv.UBSize() <= o
{
  calc <= {
    f.UBSize() + 3 + f.Cardinality()*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) + 2*poly_candidates_with_same_answer(f) + 2*poly_candidates_with_same_answer(g) + 2*iv.UBSize();
    
    f.UBSize() + 3 + f.Cardinality()*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) +
      6*f.UBSize()*f.Cardinality() + 4*f.UBSize_Keys()*f.Cardinality() + 2*f.UBSize() + 2*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 4*g.UBSize_Keys()*g.Cardinality() + 2*g.UBSize() + 2*g.Cardinality() + 2*iv.UBSize() + 8;
    
    f.Cardinality()*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) +
      6*f.UBSize()*f.Cardinality() + 7*f.UBSize() + 2*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + 2*iv.UBSize() + 11;
    
    f.Cardinality()*(f.UBSize() + 3*f.UBSize_Keys() + 1) +
      6*f.UBSize()*f.Cardinality() + 7*f.UBSize() + 2*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + 2*iv.UBSize() + 11;
    
    f.UBSize()*f.Cardinality() + 3*f.UBSize() + f.Cardinality() +
      6*f.UBSize()*f.Cardinality() + 7*f.UBSize() + 2*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + 2*iv.UBSize() + 11;
    
    7*f.UBSize()*f.Cardinality() + 10*f.UBSize() + 3*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + 2*iv.UBSize() + 11;
  }
  calc <= {
    poly_verifyCDPC_base_case(f, g, P, iv) + f.UBSize() + 3 + f.Cardinality()*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) + 2*poly_candidates_with_same_answer(f) + 2*poly_candidates_with_same_answer(g) + 2*iv.UBSize();

    poly_verifyCDPC_base_case(f, g, P, iv) +
      7*f.UBSize()*f.Cardinality() + 10*f.UBSize() + 3*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + 2*iv.UBSize() + 11;

    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality() + 2*f.UBSize()*f.Cardinality() + 2*f.UBSize() + f.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0() + 5 +
      7*f.UBSize()*f.Cardinality() + 10*f.UBSize() + 3*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + 2*iv.UBSize() + 11;
    
    
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality()
      + 9*f.UBSize()*f.Cardinality() + 12*f.UBSize() + 4*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv.UBSize() + 16;
  }

  assert 0 <= poly_verifyCDPC_base_case(f, g, P, iv);
  assert 0 <= f.UBSize() + 3 + f.Cardinality()*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) + 2*poly_candidates_with_same_answer(f) + 2*poly_candidates_with_same_answer(g) + 2*iv.UBSize();

  assert 0 <= 2*poly_candidates_with_same_answer(f) + 2*poly_candidates_with_same_answer(g) + 2*iv.UBSize();

  f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality()
  + 9*f.UBSize()*f.Cardinality() + 12*f.UBSize() + 4*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv.UBSize() + 16
}

ghost function poly_verifyCDPC_base_case(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, iv:Interview) : (o:nat)
  ensures poly_correct_apt_ratio(f) + poly_correct_private_ratio(f, P) + 2 <= o
{
  f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality() + 2*f.UBSize()*f.Cardinality() + 2*f.UBSize() + f.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0() + 4
}

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


/*
// g.UBSize()*g.Cardinality() <= 6*g'.UBSize()*g'.Cardinality()

ghost opaque function {:only} poly_Map_Map_T(f:Map_Map_T<int, bool, int>) : (r:(nat, nat, nat))
 ensures forall f' | in_universe_Map_Map_T(f', f) :: poly_Map_Map_T(f').0 <= r.0
{
  (f.UBSize(), f.Cardinality(), f.UBSize_Keys())
}
*/


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

lemma verifyCDPC_restore_counter_invariant<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>, f'_prev:Map_Map_T<int, bool, T>, counter:nat, counter_in:nat)
  requires counter <= counter <= counter_in + f.UBSize() + 3 + (f.Cardinality() - f'_prev.Cardinality())*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f) + poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f)
  requires f'_prev.Cardinality() == (f'.Cardinality() + 1)
  ensures counter <= counter_in + f.UBSize() + 3 + (f.Cardinality() - f'.Cardinality())*poly_loop_check_that_candidates_have_question_and_that_it_isnt_trivial(f)
{}


lemma verifyCDPC_restore_counter_base_case(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, iv:Interview, nodes:nat, counter:nat, counter_in:nat)
  requires pred_nodes(iv, f, nodes)
  requires counter <= counter_in + poly_verifyCDPC_base_case(f, g, P, iv)
  ensures counter <= counter_in + nodes*poly_verifyCDPC_node(f, g, P, iv)
{
  assert counter <= counter_in + poly_verifyCDPC_node(f, g, P, iv);
  reveal pred_nodes(iv, f, nodes);
  mult_preserves_order(1, poly_verifyCDPC_node(f, g, P, iv), nodes, poly_verifyCDPC_node(f, g, P, iv));
  assert poly_verifyCDPC_node(f, g, P, iv) <= nodes*poly_verifyCDPC_node(f, g, P, iv);
  assert counter <= counter_in + nodes*poly_verifyCDPC_node(f, g, P, iv);
}


lemma candidates_with_same_answer_counter_simplification<T>(f:Map_Map_T<int, bool, T>, f':Map_Map_T<int, bool, T>, counter:nat, counter_in:nat)
  requires f'.Cardinality() == 0
  requires counter <= counter_in + f.UBSize() + 2 + (f.Cardinality() - f'.Cardinality())*poly_candidates_with_same_answer_loop(f)
  ensures counter <= counter_in + poly_candidates_with_same_answer(f)
{
  //identity_substraction_lemma(f.Keys(), f'.Keys());
  //assert counter <= counter_in + f.UBSize() + 2 + f.Cardinality()*poly_candidates_with_same_answer_loop(f);
}


lemma postcondition_verifyCDPC(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview, question:int, question_is_valid_and_not_trivial:bool, recursive_true:bool, recursive_false:bool, r:bool)
  requires pred_problem_preconditions(f, g, P, a, b, x, y, iv)
  requires pred_branch_info(iv, question_is_valid_and_not_trivial, question)
  requires pred_variables_lemma(f, g, P, a, b, x, y, iv, question, question_is_valid_and_not_trivial, recursive_true, recursive_false, r)
  ensures reveal pred_problem_preconditions(f, g, P, a, b, x, y, iv);
          reveal pred_branch_info(iv, question_is_valid_and_not_trivial);
          reveal pred_variables_lemma(f, g, P, a, b, x, y, iv, question, question_is_valid_and_not_trivial, recursive_true, recursive_false, r);
          r == certificateCDPC(f.Model(), g.Model(), P.Model(), a, b, x, y, iv.Model())
{
  reveal pred_problem_preconditions(f, g, P, a, b, x, y, iv);
  reveal pred_branch_info(iv, question_is_valid_and_not_trivial);
  reveal pred_variables_lemma(f, g, P, a, b, x, y, iv, question, question_is_valid_and_not_trivial, recursive_true, recursive_false, r);
}


lemma poly_verifyCDPC_node_preserves_order(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, iv:Interview, f':Map_Map_T<int, bool, bool>, g':Map_Map_T<int, bool, int>, iv':Interview, P:Set<int>)
  requires f.UBSize() <= f'.UBSize()
  requires f.Cardinality() <= f'.Cardinality()
  requires f.UBSize_Keys() <= f'.UBSize_Keys()
  requires g.UBSize() <= g'.UBSize()
  requires g.Cardinality() <= g'.Cardinality()
  requires g.UBSize_Keys() <= g'.UBSize_Keys()
  
  requires iv.UBSize() <= iv'.UBSize()
  ensures poly_verifyCDPC_node(f, g, P, iv) <= poly_verifyCDPC_node(f', g', P, iv')
{
  reveal poly_verifyCDPC_node(f, g, P, iv);
  reveal poly_verifyCDPC_node(f', g', P, iv');
  calc <= {
    poly_verifyCDPC_node(f, g, P, iv);
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality()
    + 9*f.UBSize()*f.Cardinality() + 12*f.UBSize() + 4*f.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g.UBSize() + 2*g.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv.UBSize() + 16;
    
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality()
    + 9*f.UBSize()*f.Cardinality() + 12*f'.UBSize() + 4*f'.Cardinality() + 6*g.UBSize()*g.Cardinality() + 6*g'.UBSize() + 2*g'.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv'.UBSize() + 16;
    
      assert 6*g.UBSize()*g.Cardinality() <= 6*g'.UBSize()*g'.Cardinality() by {
        mult_preserves_order_3(6, g.UBSize(), g.Cardinality(), 6, g'.UBSize(),g'.Cardinality());
      }
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality()
    + 9*f.UBSize()*f.Cardinality() + 12*f'.UBSize() + 4*f'.Cardinality() + 6*g'.UBSize()*g'.Cardinality() + 6*g'.UBSize() + 2*g'.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv'.UBSize() + 16;
    
      assert 9*f.UBSize()*f.Cardinality() <= 9*f'.UBSize()*f'.Cardinality() by {
        mult_preserves_order_3(9, f.UBSize(), f.Cardinality(), 9, f'.UBSize(), f'.Cardinality());
      }
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f.Cardinality()*P.Cardinality()
    + 9*f'.UBSize()*f'.Cardinality() + 12*f'.UBSize() + 4*f'.Cardinality() + 6*g'.UBSize()*g'.Cardinality() + 6*g'.UBSize() + 2*g'.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv'.UBSize() + 16;
    
      assert f.Cardinality()*P.Cardinality() <= f'.Cardinality()*P.Cardinality() by {
        mult_preserves_order(f.Cardinality(), P.Cardinality(), f'.Cardinality(), P.Cardinality());
      }
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f.UBSize()*P.Cardinality() + f'.Cardinality()*P.Cardinality()
    + 9*f'.UBSize()*f'.Cardinality() + 12*f'.UBSize() + 4*f'.Cardinality() + 6*g'.UBSize()*g'.Cardinality() + 6*g'.UBSize() + 2*g'.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv'.UBSize() + 16;
    
      assert f.UBSize()*P.Cardinality() <= f'.UBSize()*P.Cardinality() by {
        mult_preserves_order(f.UBSize(), P.Cardinality(), f'.UBSize(), P.Cardinality());
      }
    f.UBSize()*f.Cardinality()*P.Cardinality() + 3*f'.UBSize()*P.Cardinality() + f'.Cardinality()*P.Cardinality()
    + 9*f'.UBSize()*f'.Cardinality() + 12*f'.UBSize() + 4*f'.Cardinality() + 6*g'.UBSize()*g'.Cardinality() + 6*g'.UBSize() + 2*g'.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv'.UBSize() + 16;
    
      assert f.UBSize()*f.Cardinality()*P.Cardinality() <= f'.UBSize()*f'.Cardinality()*P.Cardinality() by {
        mult_preserves_order_3(f.UBSize(), f.Cardinality(), P.Cardinality(), f'.UBSize(), f'.Cardinality(), P.Cardinality());
      }
    f'.UBSize()*f'.Cardinality()*P.Cardinality() + 3*f'.UBSize()*P.Cardinality() + f'.Cardinality()*P.Cardinality()
    + 9*f'.UBSize()*f'.Cardinality() + 12*f'.UBSize() + 4*f'.Cardinality() + 6*g'.UBSize()*g'.Cardinality() + 6*g'.UBSize() + 2*g'.Cardinality() + P.UBSize0()*P.Cardinality() + 3*P.Cardinality() + P.UBSize0()+ 2*iv'.UBSize() + 16;
    poly_verifyCDPC_node(f', g', P, iv');
  }
}


lemma verifyCDPC_restore_counter_aux(nodes_true:nat, nodes_false:nat, poly:nat)
  ensures poly + nodes_true*poly + nodes_false*poly <= (nodes_true + nodes_false + 1)*poly
{}

lemma candidates_with_same_answer_lemma<T>(f:Map_Map_T<int, bool, T>, f_true:Map_Map_T<int, bool, T>, f_false:Map_Map_T<int, bool, T>, question:int)
  requires f.Valid()
  requires forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys
  requires forall c:candidate |  c in f.Keys() :: question in c

  requires f_true.Model() == (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c])
  requires f_false.Model() == (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c])

  ensures f_true.Cardinality() + f_false.Cardinality() == f.Cardinality()
{
  assert f_true.Model().Keys + f_false.Model().Keys == f.Model().Keys;
  assert f_true.Model().Keys !! f_false.Model().Keys;
}


lemma verifyCDPC_restore_counter(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, iv:Interview, nodes:nat, f_true:Map_Map_T<int, bool, bool>, f_false:Map_Map_T<int, bool, bool>, g_true:Map_Map_T<int, bool, int>, g_false:Map_Map_T<int, bool, int>, nodes_true:nat, nodes_false:nat, iv_true:Interview, iv_false:Interview, counter:nat, counter_in:nat)
  requires counter <= counter_in + poly_verifyCDPC_node(f, g, P, iv) + nodes_true*poly_verifyCDPC_node(f_true, g_true, P, iv_true) + nodes_false*poly_verifyCDPC_node(f_false, g_false, P, iv_false)

  requires 0 <= poly_verifyCDPC_node(f, g, P, iv)

  
  requires 0 <= f_true.UBSize() <= f.UBSize()
  requires 0 < f_true.Cardinality() <= f.Cardinality()
  requires f_true.UBSize_Keys() <= f.UBSize_Keys()
  requires 0 <= g_true.UBSize() <= g.UBSize()
  requires 0 < g_true.Cardinality() <= g.Cardinality()
  requires g_true.UBSize_Keys() <= g.UBSize_Keys()
  //requires in_universe_Map_Map_T(f_true, f)
  //requires in_universe_Map_Map_T(g_true, g)
  requires 0 <= iv_true.UBSize() <= iv.UBSize()
  
  requires 0 <= f_false.UBSize() <= f.UBSize()
  requires 0 < f_false.Cardinality() <= f.Cardinality()
  requires f_false.UBSize_Keys() <= f.UBSize_Keys()
  requires 0 <= g_false.UBSize() <= g.UBSize()
  requires 0 < g_false.Cardinality() <= g.Cardinality()
  requires g_false.UBSize_Keys() <= g.UBSize_Keys()
  //requires in_universe_Map_Map_T(f_false, f)
  //requires in_universe_Map_Map_T(g_false, g)
  requires 0 <= iv_false.UBSize() <= iv.UBSize()

  requires (|iv_true.Questions()| < |iv.Questions()|) && (|iv_false.Questions()| < |iv.Questions()|)
  requires f_true.Cardinality() + f_false.Cardinality() == f.Cardinality()

  requires nodes == |iv.Questions()|*f.Cardinality() + 1
  requires nodes_true == |iv_true.Questions()|*f_true.Cardinality() + 1
  requires nodes_false == |iv_false.Questions()|*f_false.Cardinality() + 1
  requires 0 <= nodes_true < nodes
  requires 0 <= nodes_false < nodes

  ensures counter <= counter_in + nodes*poly_verifyCDPC_node(f, g, P, iv)
{
  //in_universe_lemma_Map_Map_T(f_true, f);
  //in_universe_lemma_Map_Map_T(g_true, g);
  //in_universe_lemma_Map_Map_T(f_false, f);
  //in_universe_lemma_Map_Map_T(g_false, g);
  assert counter <= counter_in + (nodes_true + nodes_false + 1)*poly_verifyCDPC_node(f, g, P, iv) by {
    assert counter <= counter_in + poly_verifyCDPC_node(f, g, P, iv) + nodes_true*poly_verifyCDPC_node(f_true, g_true, P, iv_true) + nodes_false*poly_verifyCDPC_node(f_false, g_false, P, iv_false);
    poly_verifyCDPC_node_preserves_order(f_true, g_true, iv_true, f, g, iv, P);
    poly_verifyCDPC_node_preserves_order(f_false, g_false, iv_false, f, g, iv, P);
    assert poly_verifyCDPC_node(f_true, g_true, P, iv_true) <= poly_verifyCDPC_node(f, g, P, iv);
    assert poly_verifyCDPC_node(f_false, g_false, P, iv_false) <= poly_verifyCDPC_node(f, g, P, iv);
    
    mult_preserves_order(nodes_true, poly_verifyCDPC_node(f_true, g_true, P, iv_true), nodes_true, poly_verifyCDPC_node(f, g, P, iv));
    mult_preserves_order(nodes_false, poly_verifyCDPC_node(f_false, g_false, P, iv_false), nodes_false, poly_verifyCDPC_node(f, g, P, iv));
    assert counter <= counter_in + poly_verifyCDPC_node(f, g, P, iv) + nodes_true*poly_verifyCDPC_node(f, g, P, iv) + nodes_false*poly_verifyCDPC_node(f, g, P, iv);
    
    verifyCDPC_restore_counter_aux(nodes_true, nodes_false, poly_verifyCDPC_node(f, g, P, iv));
  }
  assert (nodes_true + nodes_false + 1) <= nodes by {
    reveal pred_nodes(iv, f, nodes);
    assert nodes_true == |iv_true.Questions()|*f_true.Cardinality() + 1;
    assert nodes_false == |iv_false.Questions()|*f_false.Cardinality() + 1;
    assert (|iv_true.Questions()| < |iv.Questions()|) && (|iv_false.Questions()| < |iv.Questions()|);
    assert f_true.Cardinality() + f_false.Cardinality() == f.Cardinality();

    ghost var Q := |iv.Questions()|;
    ghost var C := f.Cardinality();
    ghost var A := C - f_true.Cardinality();
    
    assert nodes == Q*C + 1;
    assert nodes_true <= (Q - 1)*(C - A) + 1 by {
      mult_preserves_order(|iv_true.Questions()|, f_true.Cardinality(), (Q - 1), (C - A));
    }
    assert nodes_false <= (Q - 1)*(A) + 1 by {
      mult_preserves_order(|iv_false.Questions()|, f_false.Cardinality(), (Q - 1), (A));
    }
    calc <= {
      ((Q - 1)*(C - A) + 1) + ((Q - 1)*(A) + 1) + 1;
      (Q*C - Q*A - C + A + 1) + ((Q - 1)*(A) + 1) + 1;
      (Q*C - Q*A - C + A + 1) + (Q*A - A + 1) + 1;
      Q*C - Q*A - C + A + 1 + Q*A - A + 1 + 1;
      Q*C - C + 3;
      assert 2 <= f.Cardinality() by {
        assert f_true.Cardinality() + f_false.Cardinality() == f.Cardinality();
        assert 0 < f_true.Cardinality();
        assert 0 < f_false.Cardinality();
      }
      Q*C + 1;
    }
  }
  mult_preserves_order((nodes_true + nodes_false + 1), poly_verifyCDPC_node(f, g, P, iv), nodes, poly_verifyCDPC_node(f, g, P, iv));
}



// PREDICATES



ghost opaque predicate pred_problem_preconditions(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview)
{
  (f.Valid() && g.Valid() && P.Valid() && iv.Valid()) &&
  (forall c1, c2:candidate |  c1 in f.Keys() && c2 in f.Keys() :: c1.Keys == c2.Keys) &&
  (f.Keys() == g.Keys()) &&
  (forall c:candidate | c in f.Keys() :: (P.Model() <= c.Keys)) &&
  (0.0 <= a <= b <= 1.0) &&
  (0.0 <= x <= y <= 1.0)
}

ghost opaque predicate pred_nodes(iv:Interview, f:Map_Map_T<int, bool, bool>, nodes:nat)
{
  0 < nodes == |iv.Questions()|*f.Cardinality() + 1   // |iv.Questions()|*|iv.Candidates()| + 1
}

ghost opaque predicate pred_branch_info(iv:Interview, question_is_valid_and_not_trivial:bool, question:int)
{
  (iv.Model() != Null) &&
  (question_is_valid_and_not_trivial == true) &&
  (iv.Model().Key == question)
}

ghost opaque predicate pred_variables_lemma(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview, question:int, question_is_valid_and_not_trivial:bool, recursive_true:bool, recursive_false:bool, ok:bool)
  requires pred_problem_preconditions(f, g, P, a, b, x, y, iv)
  requires pred_branch_info(iv, question_is_valid_and_not_trivial, question)
{
  reveal pred_problem_preconditions(f, g, P, a, b, x, y, iv); reveal pred_branch_info(iv, question_is_valid_and_not_trivial);
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
  (ok == (question_is_valid_and_not_trivial && recursive_true && recursive_false))
}

ghost opaque predicate pred_ok_definition(question_is_valid_and_not_trivial:bool, recursive_true:bool, recursive_false:bool, ok:bool)
{
  (ok == (question_is_valid_and_not_trivial && recursive_true && recursive_false))
}

ghost opaque predicate pred_variables_inductive_step(f:Map_Map_T<int, bool, bool>, g:Map_Map_T<int, bool, int>, P:Set<int>, a:real, b:real, x:real, y:real, iv:Interview, question:int, question_is_valid_and_not_trivial:bool,
                                                     f_true:Map_Map_T<int, bool, bool>, g_true:Map_Map_T<int, bool, int>, iv_true:Interview, nodes_true:nat,
                                                     f_false:Map_Map_T<int, bool, bool>, g_false:Map_Map_T<int, bool, int>, iv_false:Interview, nodes_false:nat)
  requires pred_problem_preconditions(f, g, P, a, b, x, y, iv)
  requires pred_branch_info(iv, question_is_valid_and_not_trivial, question)
{
  reveal pred_problem_preconditions(f, g, P, a, b, x, y, iv); reveal pred_branch_info(iv, question_is_valid_and_not_trivial, question);
  (f_true.Valid() && f_false.Valid() && g_true.Valid() && g_false.Valid() && iv_true.Valid() && iv_false.Valid()) &&
  (question_is_valid_and_not_trivial == (
    (forall cand:candidate | cand in f.Keys() :: question in cand.Keys) &&    // candidates have question
    (exists cand:candidate | cand in f.Keys() :: cand[question] == true) &&   // exists answer true
    (exists cand:candidate | cand in f.Keys() :: cand[question] == false))    // exists answer false
  ) &&
  (f_true.Model() == (map c:candidate | c in f.Keys() && c[question] == true :: f.Model()[c])) &&
  (f_false.Model() == (map c:candidate | c in f.Keys() && c[question] == false :: f.Model()[c])) &&
  (g_true.Model() == (map c:candidate | c in g.Keys() && c[question] == true :: g.Model()[c])) &&
  (g_false.Model() == (map c:candidate | c in g.Keys() && c[question] == false :: g.Model()[c])) &&
  ((iv_true.Model() == iv.Model().True) && iv_true.Questions() == iv.Questions() - {iv.Model().Key}) &&
  ((iv_false.Model() == iv.Model().False) && iv_false.Questions() == iv.Questions() - {iv.Model().Key}) &&
  (nodes_true == |iv_true.Questions()|*f_true.Cardinality() + 1) &&
  (nodes_false == |iv_false.Questions()|*f_false.Cardinality() + 1)
}

