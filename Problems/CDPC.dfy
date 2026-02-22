include "../Auxiliary/Definitions.dfy"

//datatype Question = CharacteristicQ(int)
//datatype Answer = CharacteristicA(int) | T

/*
No exhaustivo: Las funciones f y g son parciales
Interactivo: Las preguntas pueden cambiar en función de las respuestas (la entrevista es adaptativa)
Sin límite de preguntas: Las ramas de la entrevista adaptativa pueden tener todas las preguntas posibles
Parcial: No es necesario poder discernir con certeza absoluta la aptitud de la población; es suficiente con asegurar que está en un determinado rango
Cambiado para que las respuestas sean booleanas (es suficiente para la reducción)
*/
ghost predicate CDPC(f:map<candidate, bool>, g:map<candidate, int>, P:set<int>, a:real, b:real, x:real, y:real)
  requires forall c1, c2:candidate |  c1 in f.Keys && c2 in f.Keys :: c1.Keys == c2.Keys
  requires f.Keys == g.Keys
  requires forall c:candidate | c in f.Keys :: (P <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
{
  exists iv:interview :: certificateCDPC(f, g, P, a, b, x, y, iv)
}

ghost predicate certificateCDPC(f:map<candidate, bool>, g:map<candidate, int>, P:set<int>, a:real, b:real, x:real, y:real, iv:interview)
  requires forall c1, c2:candidate |  c1 in f.Keys && c2 in f.Keys :: c1.Keys == c2.Keys
  requires f.Keys == g.Keys
  requires forall c:candidate | c in f.Keys :: (P <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
{
  if iv == Null then

  // * Caso base
  |f| == 0 ||
  (
    // Se ha obtenido la información necesaria según x e y
    var aptRatio:real := (|(set isApt:candidate | isApt in f.Keys && f[isApt] :: isApt)| as real) / (|f| as real);
    (aptRatio <= x || y <= aptRatio) &&
    // Por cada caractrística privada, no se ha inferido más información que la permitida por a y b
    forall p:int | p in P ::
    (
      var privateRatio:real := (|(set isPrivate:candidate | isPrivate in f.Keys && isPrivate[p] :: isPrivate)| as real) / (|f| as real);
      a <= privateRatio <= b
    )
  )

  else

  // * Caso recursivo
  var question:int := iv.Key;
  // Pregunta válida y no trivial
  (forall cand:candidate | cand in f.Keys :: question in cand.Keys) &&
  //(exists cand:candidate | cand in f.Keys :: cand[question] == true) &&
  //(exists cand:candidate | cand in f.Keys :: cand[question] == false) &&
  // Casos recursivos (candidatos que responden que sí y que no)
  certificateCDPC(
    (map c:candidate | c in f.Keys && c[question] == true :: f[c]),
    (map c:candidate | c in g.Keys && c[question] == true :: g[c]),
    P, a, b, x, y, iv.True
  )
  &&
  certificateCDPC(
    (map c:candidate | c in f.Keys && c[question] == false :: f[c]),
    (map c:candidate | c in g.Keys && c[question] == false :: g[c]),
    P, a, b, x, y, iv.False
  )
}
