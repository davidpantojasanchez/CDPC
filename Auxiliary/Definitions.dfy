
datatype interview = Null | Node (Key:int, True:interview, False:interview)
type candidate = map<int, bool>


ghost function max(a:nat, b:nat) : nat
{
    if a > b then a else b
}


ghost function Depth(iv:interview) : nat
{
  if iv == Null then 0 else 1 + max(Depth(iv.True), Depth(iv.False))
}

ghost function AllKeysIn(iv: interview, S: set<int>): bool
{
  match iv
    case Null => true
    case Node(k, t, f) =>
      k in S &&
      AllKeysIn(t, S) &&
      AllKeysIn(f, S)
}

ghost function EveryPathHasCandidate(iv: interview,
                                     Candidates: set<map<int,bool>>): bool
{
  PathMatches(iv, Candidates, map[])
}
ghost function PathMatches(iv: interview,
                          Candidates: set<map<int,bool>>,
                          prefix: map<int,bool>): bool
{
  match iv
    case Null =>
      exists c | c in Candidates :: Consistent(c, prefix)

    case Node(k, t, f) =>
      PathMatches(t, Candidates, prefix[k := true]) &&
      PathMatches(f, Candidates, prefix[k := false])
}
ghost function Consistent(c: map<int,bool>, prefix: map<int,bool>): bool
{
  forall k | k in prefix.Keys :: k in c.Keys && c[k] == prefix[k]
}
