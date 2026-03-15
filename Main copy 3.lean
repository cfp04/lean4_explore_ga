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
  | ep : Fin p -> B p q r
  | en : Fin q -> B p q r
  | ez : Fin r -> B p q r
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
      | (a :: b :: rest) => match compare a b with
        | .lt => match simplify_be $ .signed sign ⟨b :: rest⟩ with
            | .zero => .zero
            | .signed sign2 ⟨brest⟩ => .signed sign2 ⟨a :: brest⟩
        | .gt => simplify_be $ .signed (sign * .neg) ⟨b :: a :: rest⟩
        | .eq => match a, b with
          | .ez _, .ez _ => .zero
          | .ep _, .ep _ => simplify_be $ .signed sign ⟨rest⟩
          | .en _, .en _ => simplify_be $ .signed (sign * .neg) ⟨rest⟩
          | o1, o2 => sorry
      | other => sbe
    | .zero => .zero

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
  List.foldr Expr.add (Expr.coef (.var "zero") (e0*e0)) $
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
  | x + (y + z) => simplify (simplify (x + y) + simplify z)
  | (x + y) * z => simplify (simplify (x * z) + simplify (y * z))
  | x * (y + z) => simplify (simplify (x * y) + simplify (x * z))

  | (.coef r1 b1) * (.coef r2 b2) => simplify (.coef (r1*r2) (simplify_be (b1*b2)))

  | _ * (.coef r .zero) => (.coef r .zero)
  | (.coef r .zero) * _ => (.coef r .zero)
  | x + (.coef _ .zero) => x
  | (.coef _ .zero) + y => y

  | other => other

def main : IO Unit :=
  let unsimped := (this * other)
  let simped := simplify unsimped
  IO.println $ repr simped
