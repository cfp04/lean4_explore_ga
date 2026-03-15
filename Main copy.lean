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
 | add: List Expr -> Expr
 | mul: List Expr -> Expr
 deriving Repr
instance : Add Expr where
  add x y := Expr.add [x, y]
instance : Mul Expr where
  mul x y := Expr.mul [x, y]

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
  Expr.add $
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

def simplify (e: Expr) := match e with
  | Expr.mul list => 1
  | Expr.add list => 1
  | Expr.coef r b => 1

def main : IO Unit :=
  let unsimped := repr (this * other)
  IO.println s!"Hello, {unsimped}!"
