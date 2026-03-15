import Ga

inductive R where
  | var: String -> R
  | plus: R -> R -> R
  | mul: R -> R -> R
  deriving Repr
instance : Add R where
  add := R.plus
instance : Mul R where
  mul := R.mul

inductive B (p:Nat) (q:Nat) (r:Nat) where
  | ez : Fin r -> B p q r
  | en : Fin q -> B p q r
  | ep : Fin p -> B p q r
  deriving Repr, Ord

structure BE p q r where
  prod : List (B p q r)
  deriving Repr
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

inductive SBE p q r where
  | zero: SBE p q r
  | signed: Sign -> BE p q r -> SBE p q r
  deriving Repr
instance: Mul (SBE p q r) where
  mul x y := match x,y with
  | .zero, _ => .zero
  | _, .zero => .zero
  | .signed s1 be1, .signed s2 be2 => .signed (s1*s2) (be1*be2)

inductive Expr p q r where
 | coef: R -> SBE p q r -> Expr p q r
 | add: Expr p q r -> Expr p q r -> Expr p q r
 | mul: Expr p q r -> Expr p q r -> Expr p q r
 deriving Repr
instance : Add (Expr p q r) where
  add := Expr.add
instance : Mul (Expr p q r) where
  mul := Expr.mul

def m_one : SBE 3 0 1 := .signed .pos ⟨[]⟩

def e0 : SBE 3 0 1 := .signed .pos ⟨[B.ez 0]⟩

def e1 : SBE 3 0 1 := .signed .pos ⟨[B.ep 0]⟩
def e2 : SBE 3 0 1 := .signed .pos ⟨[B.ep 1]⟩
def e3 : SBE 3 0 1 := .signed .pos ⟨[B.ep 2]⟩

partial def simplify_be (sbe : SBE p q r): SBE p q r :=
  match sbe with
    | .signed sign be =>
      match be.prod with
      | [] => sbe
      | [_] => sbe
      | [a, b] => match compare a b with
        | .lt => sbe
        | .gt => .signed (sign * .neg) ⟨[b, a]⟩
        | .eq => match a, b with
          | .ez _, .ez _ => .zero
          | .ep _, .ep _ => .signed (sign * .pos) ⟨[]⟩
          | .en _, .en _ => .signed (sign * .neg) ⟨[]⟩
          | o1, o2 => sorry
      | (a :: rest) =>
        match simplify_be $ .signed sign ⟨rest⟩ with
          | .zero => .zero
          | .signed sign' rest' => (.signed sign ⟨[a]⟩) * (.signed sign' rest')
      -- | (a :: b :: rest) =>
      --   match simplify_be $ .signed sign ⟨[a,b]⟩ with
      --     | .zero => .zero
      --     | res@(.signed sign' rest') =>
      --       let asdf := res * (.signed sign' rest')
      --       let (a' :: restttt) := asdf
      -- TODO think more about this. this is the key area
    | .zero => .zero

partial def simplify_be_2 (obe: Option (Sign × BE p q r)): (Option (Sign × BE p q r)) := do
  let (sign, ⟨be⟩) <- obe
  match be with
    | [] => obe
    | [_] => obe
    | (a :: b :: rest) => match compare a b with
      | .lt => obe
      | .gt => do
        let (sign', ⟨be'⟩) <- simplify_be_2 $ Option.some (.pos, ⟨b :: rest⟩)
        simplify_be_2 $ Option.some (.neg * sign * sign', ⟨a :: be'⟩)
      | .eq => match a, b with
        | .ez _, .ez _ => Option.none
        | .ep _, .ep _ => return (sign * .pos, ⟨[]⟩)
        | .en _, .en _ => return (sign * .neg, ⟨[]⟩)
        | o1, o2 => sorry

def basis: List (SBE 3 0 1) :=
  [
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

def from_coefs (names: List String) :=
  List.foldr Expr.add (Expr.coef (.var "asdf") .zero) $
    List.zipWith (fun name base => .coef (.var name) base)
    names
    basis

def this_names :=
[
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
[
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

def this := from_coefs this_names
def other := from_coefs other_names

def count_muls (e: Expr p q r): Nat := match e with
  | x * y => count_muls x + count_muls y + 1
  | _ => 0

partial def simplify (e: Expr p q r): Expr p q r := match e with
  | _ * (.coef r .zero) => (.coef r .zero)
  | (.coef r .zero) * _ => (.coef r .zero)
  | x + (.coef _ .zero) => x
  | (.coef _ .zero) + y => y

  | x + (y + z) => simplify (simplify (x + y) + simplify z)
  | (x + y) * z => simplify (simplify (x * z) + simplify (y * z))
  | x * (y + z) => simplify (simplify (x * y) + simplify (x * z))

  | (.coef r1 b1) * (.coef r2 b2) => simplify (.coef (r1*r2) (simplify_be (b1*b2)))
  | (.coef r1 b1) * y =>  simplify $ (.coef r1 b1) * (simplify y)
  | x * (.coef r2 b2) =>  simplify $ (simplify x) * (.coef r2 b2)

  | (x + y) =>  (simplify x + simplify y)
  | (x * y) =>  (simplify x * simplify y)

  | (.coef r b) => (.coef (.var "asdfasdfasdf") $ simplify_be b)

def main : IO Unit :=
  let unsimped := (this * other)
  let zeh : B 3 0 1 := B.ez 0
  let unsimped := Expr.coef (.var "hi") ((SBE.signed (Sign.pos) { prod := [zeh, B.ep 0, B.ep 1, B.ep 2, B.ez 0, B.ep 0, B.ep 1, B.ep 2] }))
  let simped := simplify unsimped
  IO.println $ repr simped
