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

partial def simplify_be_2  (is_outer: Bool) (obe: OSBE p q r): (OSBE p q r) := do
  let (sign, ⟨be⟩) <- obe
  match be with
    | [] => obe
    | [_] => obe
    | (a :: b :: rest) => match compare a b with
      | .lt => do
        let (sign', ⟨be'⟩) <- simplify_be_2 is_outer $ Option.some (sign, ⟨b :: rest⟩)
        let a_be' :=  a :: be'
        let obe2 := (sign', ⟨a_be'⟩)
        if first_two_good a_be'
          then return obe2
          else simplify_be_2 is_outer $ return obe2
      | .gt => do
        let (sign', ⟨be'⟩) <- simplify_be_2 is_outer $ Option.some (.neg * sign, ⟨a :: rest⟩)
        simplify_be_2 is_outer $ Option.some (sign', ⟨b :: be'⟩)
      | .eq => match a, b with
        | .ez _, .ez _ => Option.none
        | .ep _, .ep _ => if is_outer then Option.none else return (sign * .pos, ⟨rest⟩)
        | .en _, .en _ => if is_outer then Option.none else return (sign * .neg, ⟨rest⟩)
        | o1, o2 => sorry

abbrev MultiBasis(p)(q)(r) := Vector (BE p q r) (2^(p+q+r))
abbrev MultiBasisNames(p)(q)(r) := Vector String (2^(p+q+r))

def weird_basis: MultiBasis 3 0 1 :=
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

def basis: MultiBasis 3 0 1 :=
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
    e1 * e3,

    e0 * e1 * e2,
    e0 * e2 * e3,
    e0 * e1 * e3,
    e1 * e2 * e3,

    e0 * e1 * e2 * e3
  ]

def from_coefs (basis: MultiBasis p q r) (names: MultiBasisNames p q r) :=
  List.foldr Expr.add (Expr.coef (.var "asdf") .none) $
    List.zipWith (fun name base => Expr.coef (.var name) base)
    (names.toList)
    (basis.toList.map fun x => Option.some (.pos, x))


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

partial def simplify2 (is_outer: Bool) (e: Expr p q r): MultiAdd p q r :=
  let simp2 := simplify2 is_outer
  match e with
    -- Associate everything to the left
    | x + (y + z) => simp2 (x + y) ++ simp2 z
    | x * (y * z) => simp2 (x * y) ++ simp2 z

    -- Distribute
    | (x + y) * z => simp2 (x * z) ++ simp2 (y * z)
    | x * (y + z) => simp2 (x * y) ++ simp2 (x * z)

    -- Move scalars to the left of basis words
    | (.mul a b) * (.coef r2 b2) => simp2 $ (.coef r2 b2) * (.mul a b)
    -- Combine basis words
    | (.coef r1 b1) * (.coef r2 b2) => simp2 $ (.coef (r1*r2) (simplify_be_2 is_outer (b1*b2)))

    -- Straightforward, put things in the add list
    | (x + y) => simp2 x ++ simp2 y
    | (.coef r b) => match simplify_be_2 is_outer b with
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

def extract_to_basis (ma: MultiAdd p q r) (mbasis: MultiBasis p q r) (resnames: MultiBasisNames p q r) :=
  Vector.map
    (fun basis_and_name =>
      let elt := List.find? (fun elt => Prod.snd elt == Prod.fst basis_and_name) ma
      match elt with
      | .none => "ERROR! couldn't find bw"
      | .some elt => s!"{Prod.snd basis_and_name} = {pp_r elt.fst};"
      -- {pp_r $ repr $ elt.map Prod.fst}
    )
    (Vector.zip mbasis resnames)

def extract_flops (is_outer: Bool) (mbasis: MultiBasis p q r) (m1 m2 res: MultiBasisNames p q r): String :=
  let unsimped := (from_coefs mbasis m1 * from_coefs mbasis m2)
  let simped := simplify2 is_outer unsimped
  let combined := combine_terms simped
  assert! List.length combined <= 2^(p + q + r)
  let extracted_basis := extract_to_basis combined mbasis res
  let pretty_extracted := extracted_basis.foldr (fun x y => s!"{x}\n{y}") ""
  pretty_extracted


def access_float16_data (field: String) (index: String): String := s!"{field}{index}"

def float16_indices := #v[
  "[0]",
  "[1]",
  "[2]",
  "[3]",
  "[4]",
  "[5]",
  "[6]",
  "[7]",
  "[8]",
  "[9]",
  "[10]",
  "[11]",
  "[12]",
  "[13]",
  "[14]",
  "[15]",
]

def mat44_indices := #v[
  "[0][0]",
  "[0][1]",
  "[0][2]",
  "[0][3]",
  "[1][0]",
  "[1][1]",
  "[1][2]",
  "[1][3]",
  "[2][0]",
  "[2][1]",
  "[2][2]",
  "[2][3]",
  "[3][0]",
  "[3][1]",
  "[3][2]",
  "[3][3]",
]

def float16_flops: IO Unit := do
  let this_names := float16_indices.map (fun i => s!"data{i}")
  let other_names := float16_indices.map (fun i => s!"other.data{i}")
  let res_names := float16_indices.map (fun i => s!"res.data{i}")

  IO.println "R301 geo product:"
  IO.println $ extract_flops false basis this_names other_names res_names

  IO.println "R301 out product:"
  IO.println $ extract_flops true basis this_names other_names res_names

def mat44_flops: IO Unit := do
  let this_names := mat44_indices.map (fun i => s!"a{i}")
  let other_names := mat44_indices.map (fun i => s!"b{i}")
  let res_names := mat44_indices.map (fun i => s!"res{i}")

  IO.println "R301 geo product:"
  IO.println $ extract_flops false basis this_names other_names res_names

  IO.println "R301 out product:"
  IO.println $ extract_flops true basis this_names other_names res_names

def inverse_equations: IO Unit := do
  let this_names := (Vector.range 16).map (fun i => s!"x_{i}")
  let other_names := (Vector.range 16).map (fun i => s!"y_{i}")
  let res_names := (Vector.range 16).map (fun i => if i == 0 then "1" else "0")

  IO.println "R301 geo product fixed x_i, inverses y_i"
  IO.println $ extract_flops false basis this_names other_names res_names

structure Matrix (Elt: Type) (rows: Nat) (cols: Nat) where
  index: (Fin rows) × (Fin cols) -> Elt

def extract2 (ma: MultiAdd p q r) (mbasis: MultiBasis p q r) :=
  Vector.map
    (fun basis =>
      let elt := List.find? (fun elt => Prod.snd elt == basis) ma
      match elt with
      | .none => panic! "ERROR!"
      | .some elt => elt.fst
      -- {pp_r $ repr $ elt.map Prod.fst}
    )
    mbasis


inductive FlatR where
  | var: String -> FlatR
  | mul: FlatR -> FlatR -> FlatR
  deriving Repr, Inhabited
abbrev SFlatR := Sign × FlatR

def flatten_r (r: R): List SFlatR :=
  match r with
  | .var name => [(.pos, .var name)]
  | (r1 + r2) => flatten_r r1 ++ flatten_r r2
  | (-r1) => (flatten_r r1).map (fun (s,rf) => (s * .neg, rf))
  | (r1 * r2) => (flatten_r r1).flatMap (fun (s1, rf1) => (flatten_r r2).map (fun (s2, rf2) => (s1*s2, .mul rf1 rf2)))

def build_matrix (is_outer: Bool) (mbasis: MultiBasis p q r) (this inverted: MultiBasisNames p q r): Matrix SFlatR (2^(p+q+r)) (2^(p+q+r)) :=
  let unsimped := (from_coefs mbasis this * from_coefs mbasis inverted)
  let simped := simplify2 is_outer unsimped
  let combined := combine_terms simped
  -- assert! List.length combined <= 2^(p + q + r)
  let extracted_basis := extract2 combined mbasis
  let yay := extracted_basis.map flatten_r
  -- let yay2 := yay.map (fun x => x.mergeSort (fun (s1,r1) (s2,r2) => sorry))

  ⟨fun (r, c) => (yay.get r).getD c (.pos, .var "zilch") ⟩

def inverse_equations2 :=
  let this_names := (Vector.range 16).map (fun i => s!"x_{i}")
  let inv_names := (Vector.range 16).map (fun i => s!"y_{i}")
  --let res_names := (Vector.range 16).map (fun i => if i == 0 then "1" else "0")

  --IO.println "R301 geo product fixed x_i, inverses y_i"
  --IO.println $ extract_flops false basis this_names other_names res_names
  build_matrix false basis this_names inv_names

def pretty_flatr: FlatR -> String := fun rf => match rf with
  | .var name => name
  | .mul r1 r2 => s!"{pretty_flatr r1} * {pretty_flatr r2}"

def pretty_sflatr: SFlatR -> String :=
  fun (s, rf) =>
    let sp := match s with
      | .pos => ""
      | .neg => "-"
    s!"{sp}{pretty_flatr rf}"

def main : IO Unit := do
  -- float16_flops
  -- mat44_flops
  -- inverse_equations
  -- IO.println $ repr $ inverse_equations2

  let mat := inverse_equations2
  let print_row(r) :=
    Vector.foldr
      (fun x y => x ++ "" ++ y)
      ""
      (
        (Vector.range 16).map $ fun c =>
          let elt := mat.index (⟨r, sorry⟩,⟨c, sorry⟩)
          pad (pretty_sflatr elt) 20
      )

  IO.println $ Vector.foldr (fun x y => x ++ "\n" ++ y) "" ((Vector.range 16).map print_row)
