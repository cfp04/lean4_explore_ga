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

inductive B where
  | one: B
  | e0 : B
  | e1 : B
  | e2 : B
  | e3 : B
  | mul : B -> B -> B
  deriving Repr
instance : Mul B where
  mul := B.mul

inductive Expr where
 | coef: R -> B -> Expr
 | add: Expr -> Expr -> Expr
 | mul: Expr -> Expr -> Expr
 deriving Repr
instance : Add Expr where
  add := Expr.add
instance : Mul Expr where
  mul := Expr.mul

def basis: List B :=
  [
    .one,

    .e0,
    .e1,
    .e2,
    .e3,

    .e0 * .e1,
    .e0 * .e2,
    .e0 * .e3,
    .e1 * .e2,
    .e2 * .e3,
    .e3 * .e1,

    .e0 * .e1 * .e2,
    .e0 * .e2 * .e3,
    .e0 * .e3 * .e1,
    .e1 * .e2 * .e3,

    .e0 * .e1 * .e2 * .e3
  ]

def from_coefs (names: List String) :=
  List.foldr Expr.add (Expr.coef (.var "zero") (.e0*.e0)) $
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

def count_muls (e: Expr): Nat := match e with
  | x * y => count_muls x + count_muls y + 1
  | _ => 0

partial def simplify (e: Expr): Expr := match e with
  | x + (y + z) => simplify (simplify (x + y) + simplify z)
  | (x + y) * z => simplify (simplify (x * z) + simplify (y * z))
  | x * (y + z) => simplify (simplify (x * y) + simplify (x * z))

  | (.coef r (b1 * (b2 * b3))) => simplify (.coef r ((b1 * b2) * b3))

  | (x + (.coef r (.e0 * .e0))) => x
  | ((.coef r (.e0 * .e0)) + y) => y

  | (_ * (.coef r (.e0 * .e0))) => (.coef r (.e0 * .e0))
  | ((.coef r (.e0 * .e0)) *_y) => (.coef r (.e0 * .e0))

  | (.coef r1 b1) * (.coef r2 b2) => simplify (.coef (r1*r2) (b1*b2))
  | other => other

def main : IO Unit :=
  let unsimped := (this * other)
  let simped := simplify unsimped
  IO.println $ repr simped
