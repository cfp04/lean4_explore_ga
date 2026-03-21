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

structure Ringish where
  elt: Type u
  zero: elt
  add: elt -> elt -> elt
  mul: elt -> elt -> elt

structure FreeAlgebraElt (Scalar: Ringish) (Basis) [BEq Basis] where
  elt: List Basis -> Scalar.elt
  nonzero: List (List Basis)
  pf: (bw: List Basis) -> bw ∉ nonzero -> elt bw = Scalar.zero

structure FreeAlgebraElt2 (Scalar: Ringish) (Basis) [BEq Basis] where
  elt: List (Scalar.elt × List Basis)

def f{S}{B}[BEq B] (a: FreeAlgebraElt S B): FreeAlgebraElt2 S B :=
  ⟨a.nonzero.map fun x => (a.elt x, x)⟩

def g{S}{B}[BEq B] (a: FreeAlgebraElt2 S B): FreeAlgebraElt S B :=
  let elt := fun bw => ((a.elt.find? (fun (x,y) => y == bw)).map (Prod.fst)).getD S.zero
  let elt2 := fun bw => ((a.elt.find? (fun (x,y) => y == bw)).map (Prod.fst)).getD (S.zero)
  let elt3 := fun bw => (elt2 bw).fst
  ⟨
    elt,
    a.elt.map (Prod.snd),
    fun bw bwnz => by
      let x := elt bw
      let asdf := ((a.elt.find? (fun (x,y) => y == bw)).map (Prod.fst)).getD S.zero
      sorry
  ⟩

def expand{R}{B} (basis_simp: List B -> (R.elt -> Option (R.elt × B))) (inp: FreeAlgebraElt R B): FreeAlgebraElt R B :=
  for a in inp.nonzero do {
    sorry
  }


inductive Expr p q r where
 | coef: R -> OSBE p q r -> Expr p q r
 | add: Expr p q r -> Expr p q r -> Expr p q r
 | mul: Expr p q r -> Expr p q r -> Expr p q r
 deriving Repr
instance : Add (Expr p q r) where
  add := Expr.add
instance : Mul (Expr p q r) where
  mul := Expr.mul
