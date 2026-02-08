
//datatype Question = CharacteristicQ(int)
//datatype Answer = CharacteristicA(int) | T

datatype Interview = Empty | Node (Key:int, True:Interview, False:Interview)
type Candidate = map<int, bool>

/*
No exhaustivo: Las funciones f y g son parciales
Interactivo: Las preguntas pueden cambiar en función de las respuestas (la entrevista es adaptativa)
Sin límite de preguntas: Las ramas de la entrevista adaptativa pueden tener todas las preguntas posibles
Parcial: No es necesario poder discernir con certeza absoluta la aptitud de la población; es suficiente con asegurar que está en un determinado rango
Cambiado para que las respuestas sean booleanas (es suficiente para la reducción)
*/
ghost predicate CDPC(f:map<Candidate, bool>, g:map<Candidate, int>, P:set<int>, a:real, b:real, x:real, y:real)
  requires f.Keys == g.Keys
  requires forall c:Candidate | c in f.Keys :: (P <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
{
  exists interview:Interview :: certificateCDPC(f, g, P, a, b, x, y, interview)
}

ghost predicate certificateCDPC(f:map<Candidate, bool>, g:map<Candidate, int>, P:set<int>, a:real, b:real, x:real, y:real, interview:Interview)
  decreases f.Keys
  requires f.Keys == g.Keys
  requires forall c:Candidate | c in f.Keys :: (P <= c.Keys)
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
{
  if interview == Empty then

  // * Caso base
  |f| == 0 ||
  (
    // Se ha obtenido la información necesaria según x e y
    var aptPercentage:real := (|(set isApt:Candidate | isApt in f.Keys :: f[isApt] == true)| as real) / (|f| as real);
    (aptPercentage <= x || y <= aptPercentage) &&
    // Por cada caractrística privada, no se ha inferido más información que la permitida por a y b
    forall p:int | p in P ::
    (
      var privatePercentage:real := (|(set isPrivate:Candidate | isPrivate in f.Keys :: isPrivate[p] == true)| as real) / (|f| as real);
      a <= privatePercentage <= b
    )
  )

  else

  // * Caso recursivo
  var question:int := interview.Key;
  // Pregunta válida y no trivial
  (forall candidate:Candidate | candidate in f.Keys :: question in candidate.Keys) &&
  (exists candidate:Candidate | candidate in f.Keys :: candidate[question] == true) &&
  (exists candidate:Candidate | candidate in f.Keys :: candidate[question] == false) &&
  // Casos recursivos (candidatos que responden que sí y que no)
  certificateCDPC(
    (map c:Candidate | c in f.Keys && c[question] == true :: f[c]),
    (map c:Candidate | c in g.Keys && c[question] == true :: g[c]),
    P, a, b, x, y, interview.True
  )
  &&
  certificateCDPC(
    (map c:Candidate | c in f.Keys && c[question] == false :: f[c]),
    (map c:Candidate | c in g.Keys && c[question] == false :: g[c]),
    P, a, b, x, y, interview.False
  )
}
