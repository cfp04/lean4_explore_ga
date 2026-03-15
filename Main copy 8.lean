import Ga

inductive R where
  | var: String -> R
  | add: R -> R -> R
  | mul: R -> R -> R
  | neg : R -> R
  deriving Repr, Inhabited
instance : Add R where
  add := R.add
instance : Mul R where
  mul := R.mul
instance : Neg R where
  neg := R.neg

inductive B (p:Nat) (q:Nat) (r:Nat) where
  | ez : Fin r -> B p q r
  | en : Fin q -> B p q r
  | ep : Fin p -> B p q r
  deriving Repr, Ord, BEq

structure BE p q r where
  prod : List (B p q r)
  deriving Repr, Ord, BEq, Inhabited
instance : Mul (BE p q r) where
  mul x y := ⟨x.prod ++ y.prod⟩

inductive Sign where
  | neg: Sign
  | pos: Sign
  deriving Repr
instance : Mul Sign where
  mul a b := match a, b with
  | .neg, .neg => .pos
  | .pos, .neg => .neg
  | .neg, .pos => .neg
  | .pos, .pos => .pos

abbrev SBE(p)(q)(r) := Sign × (BE p q r)
abbrev OSBE(p)(q)(r) := Option (SBE p q r)

instance: Mul (OSBE p q r) where
  mul x y := do
    let (s1, be1) <- x
    let (s2, be2) <- y
    return (s1*s2, be1*be2)

inductive Expr p q r where
 | coef: R -> OSBE p q r -> Expr p q r
 | add: Expr p q r -> Expr p q r -> Expr p q r
 | mul: Expr p q r -> Expr p q r -> Expr p q r
 deriving Repr
instance : Add (Expr p q r) where
  add := Expr.add
instance : Mul (Expr p q r) where
  mul := Expr.mul

def m_one : BE 3 0 1 := ⟨[]⟩

def e0 : BE 3 0 1 := ⟨[B.ez 0]⟩

def e1 : BE 3 0 1 := ⟨[B.ep 0]⟩
def e2 : BE 3 0 1 := ⟨[B.ep 1]⟩
def e3 : BE 3 0 1 := ⟨[B.ep 2]⟩

def first_two_good (bs: List (B p q r)): Bool :=
  match bs with
    | [] => true
    | [_] => false
    | (a :: b :: _) => compare a b == .lt

partial def simplify_be_2 (obe: OSBE p q r): (OSBE p q r) := do
  let (sign, ⟨be⟩) <- obe
  match be with
    | [] => obe
    | [_] => obe
    | (a :: b :: rest) => match compare a b with
      | .lt => do
        let (sign', ⟨be'⟩) <- simplify_be_2 $ Option.some (sign, ⟨b :: rest⟩)
        let a_be' :=  a :: be'
        let obe2 := (sign', ⟨a_be'⟩)
        if first_two_good a_be'
          then return obe2
          else simplify_be_2 $ return obe2
      | .gt => do
        let (sign', ⟨be'⟩) <- simplify_be_2 $ Option.some (.neg * sign, ⟨a :: rest⟩)
        simplify_be_2 $ Option.some (sign', ⟨b :: be'⟩)
      | .eq => match a, b with
        | .ez _, .ez _ => Option.none
        | .ep _, .ep _ => return (sign * .pos, ⟨rest⟩)
        | .en _, .en _ => return (sign * .neg, ⟨rest⟩)
        | o1, o2 => sorry

def basis: Vector (BE 3 0 1) ((3+0+1)^2) :=
  #v[
    m_one,

    e0,
    e1,
    e2,
    e3,

    e0 * e1,
    e0 * e2,
    e0 * e3,
    e1 * e2,
    e2 * e3,
    e3 * e1,

    e0 * e1 * e2,
    e0 * e2 * e3,
    e0 * e3 * e1,
    e1 * e2 * e3,

    e0 * e1 * e2 * e3
  ]

def from_coefs (basis: Vector (BE p q r) ((p + q + r)^2)) (names: Vector String ((p + q + r)^2)) :=
  List.foldr Expr.add (Expr.coef (.var "asdf") .none) $
    List.zipWith (fun name base => Expr.coef (.var name) base)
    (names.toList)
    (basis.toList.map fun x => Option.some (.pos, x))

def this_names :=
#v[
  "data[0]",
  "data[1]",
  "data[2]",
  "data[3]",
  "data[4]",
  "data[5]",
  "data[6]",
  "data[7]",
  "data[8]",
  "data[9]",
  "data[10]",
  "data[11]",
  "data[12]",
  "data[13]",
  "data[14]",
  "data[15]",
]

def other_names :=
#v[
  "other.data[0]",
  "other.data[1]",
  "other.data[2]",
  "other.data[3]",
  "other.data[4]",
  "other.data[5]",
  "other.data[6]",
  "other.data[7]",
  "other.data[8]",
  "other.data[9]",
  "other.data[10]",
  "other.data[11]",
  "other.data[12]",
  "other.data[13]",
  "other.data[14]",
  "other.data[15]",
]

def res_names :=
#v[
  "res.data[0]",
  "res.data[1]",
  "res.data[2]",
  "res.data[3]",
  "res.data[4]",
  "res.data[5]",
  "res.data[6]",
  "res.data[7]",
  "res.data[8]",
  "res.data[9]",
  "res.data[10]",
  "res.data[11]",
  "res.data[12]",
  "res.data[13]",
  "res.data[14]",
  "res.data[15]",
]

def this: Expr 3 0 1 := from_coefs basis this_names
def other: Expr 3 0 1 := from_coefs basis other_names

def count_muls (e: Expr p q r): Nat := match e with
  | x * y => count_muls x + count_muls y + 1
  | _ => 0

-- partial def simplify (e: Expr p q r): Expr p q r := match e with
--   | _ * (.coef r .none) => (.coef r .none)
--   | (.coef r .none) * _ => (.coef r .none)
--   | x + (.coef _ .none) => x
--   | (.coef _ .none) + y => y

--   | x + (y + z) => simplify (simplify (x + y) + simplify z)
--   | (x + y) * z => simplify (simplify (x * z) + simplify (y * z))
--   | x * (y + z) => simplify (simplify (x * y) + simplify (x * z))

--   | (.coef r1 b1) * (.coef r2 b2) => simplify (.coef (r1*r2) (simplify_be_2 (b1*b2)))
--   | (.coef r1 b1) * y =>  simplify $ (.coef r1 b1) * (simplify y)
--   | x * (.coef r2 b2) =>  simplify $ (simplify x) * (.coef r2 b2)

--   | (x + y) =>  (simplify x + simplify y)
--   | (x * y) =>  (simplify x * simplify y)

--   | (.coef r b) => (.coef r $ simplify_be_2 b)

abbrev MultiAdd(p)(q)(r) := List (R × BE p q r)
instance: Ord (R × BE p q r) where
  compare a b :=
    let (_, x) := a
    let (_, y) := b
    compare x y

partial def simplify2 (e: Expr p q r): MultiAdd p q r := match e with
  -- Associate everything to the left
  | x + (y + z) => simplify2 (x + y) ++ simplify2 z
  | x * (y * z) => simplify2 (x * y) ++ simplify2 z

  -- Distribute
  | (x + y) * z => simplify2 (x * z) ++ simplify2 (y * z)
  | x * (y + z) => simplify2 (x * y) ++ simplify2 (x * z)

  -- Move scalars to the left of basis words
  | (.mul a b) * (.coef r2 b2) => simplify2 $ (.coef r2 b2) * (.mul a b)
  -- Combine basis words
  | (.coef r1 b1) * (.coef r2 b2) => simplify2 $ (.coef (r1*r2) (simplify_be_2 (b1*b2)))

  -- Straightforward, put things in the add list
  | (x + y) => simplify2 x ++ simplify2 y
  | (.coef r b) => match simplify_be_2 b with
    | .none => []
    | .some (.neg, b') => [(-r, b')]
    | .some (.pos, b') => [(r, b')]

partial def combine_terms_helper (ma: MultiAdd p q r): MultiAdd p q r :=
  match ma with
  | [] => []
  | [a] => [a]
  | (a :: b :: rest) =>
    let (r1, bws1) := a
    let (r2, bws2) := b
    match compare bws1 bws2 with
    | .eq => combine_terms_helper $ (r1+r2, bws1) :: rest
    | _ => a :: combine_terms_helper (b :: rest)

def combine_terms (ma: MultiAdd p q r): MultiAdd p q r :=
  let sorted := List.mergeSort ma (fun a b => (compare a b == .lt))
  combine_terms_helper sorted

def pp_r (r: R): String :=
  match r with
  | .add a b => s!"({pp_r a} + {pp_r b})"
  | .mul a b => s!"({pp_r a} * {pp_r b})"
  | .neg a => s!"-{pp_r a}"
  | .var s => s

-- def pp_bw (bw: B p q r): String :=
--   let (met, idx) := match bw with
--   | .ez i => ("0", s!"{i}")
--   | .en i => ("-1", s!"{i}")
--   | .ep i => ("1", s!"{i}")
--   s!"√{met}_{idx}"


def pad (s: String) (n:Nat) : String :=
  String.pushn s ' ' (n - String.length s)

-- for R301 specifically! notation from the forque paper
def pp_bws (bws: List (B 3 0 1)): String :=
  let nicelist := List.map
    fun b => match b with
    | .ez 0 => "0"
    | .ep 0 => "1"
    | .ep 1 => "2"
    | .ep 2 => "3"
    bws
  let idxlist := List.foldr (fun a b => a ++ b) "" nicelist
  let res := if String.length idxlist == 0
    then "𝟙"
    else s!"e_{idxlist}"
  pad res 6

def pp_add (ma: MultiAdd 3 0 1): String :=
  let nicelist := List.map (fun (r, ⟨bws⟩) => s!"storage[{pp_bws bws}] = {pp_r r}") ma
  List.foldr (fun a b => a ++ "\n" ++ b) "" nicelist

def extract_to_basis (ma: MultiAdd p q r) (mbasis: Vector (BE p q r) ((p + q + r)^2)) (resnames: Vector (String) ((p + q + r)^2)) :=
  Vector.map
    (fun basis_and_name =>
      let elt := List.find? (fun elt => Prod.snd elt == Prod.fst basis_and_name) ma
      match elt with
      | .none => panic! "ERROR!" -- This doesn't seem to trigger, despite this branch being followed. maybe its a bug?
      | .some elt => s!"{Prod.snd basis_and_name} = {pp_r elt.fst};"
      -- {pp_r $ repr $ elt.map Prod.fst}
    )
    (Vector.zip mbasis resnames)

def main : IO Unit := do
  let unsimped := (this * other)
  let simped := simplify2 unsimped
  let combined := combine_terms simped
  assert! List.length combined <= 2^(3 + 0 + 1)
  let pretty := pp_add combined
  -- IO.println $ pretty
  let extracted_basis := extract_to_basis combined basis res_names
  let pretty_extracted := extracted_basis.foldr (fun x y => s!"{x}\n{y}") ""
  IO.println $ pretty_extracted
