// "Question" representa a las preguntas de CDPC o a los tests de D-ATDP
// "Answer" representa a las respuestas de CDPC o a los comportamientos de D-ATDP
datatype Question = CharacteristicQ(int)
datatype Answer = CharacteristicA(int) | T

datatype Interview = Empty | Node ( Key:Question, Children:map<Answer, Interview>)

/*
No exhaustivo: Las funciones f y g son parciales
Interactivo: Las preguntas pueden cambiar en función de las respuestas (la entrevista es adaptativa)
Sin límite de preguntas: Las ramas de la entrevista adaptativa pueden tener todas las preguntas posibles
Parcial: No es necesario poder discernir con certeza absoluta la aptitud de la población; es suficiente con asegurar que está en un determinado rango
*/
ghost predicate CDPC(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, x:real, y:real, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
{
  CDPCrec(f, g, P, a, b, x, y, |Q|, Q)
}

ghost predicate CDPCrec(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, x:real, y:real, k:int, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
  requires 0 <= k <= |Q|
{
  okPrivate(f, g, P, a, b, Q) &&
  if k == 0 then
    okFitnessPartial(f, g, Q, x, y)
  else
    okFitnessPartial(f, g, Q, x, y) ||
    exists i:Question | i in Q ::
      forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
        CDPCrec(
          (map m:map<Question, Answer> | m in f.Keys && m[i] == o :: f[m]),
          (map m:map<Question, Answer> | m in g.Keys && m[i] == o :: g[m]),
          P, a, b, x, y, k - 1, Q
        )
}

// Comprueba que no se ha inferido más información privada que la permitida
ghost predicate okPrivate(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  //requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= 1.0
  requires 0.0 <= b <= 1.0
  requires a <= b
{
  forall i:Question | i in P ::
    var nC:real := nCandidates(g, Q) as real;
    var nP:real := nPrivate(g, Q, i, T) as real;
    if nC == 0.0 then
      true
    else
      a <= nP / nC <= b
}