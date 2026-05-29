{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-arity" "2" "-internal" "-direction" "p,refl,Lrel,ab") -*- `}

  ` currently need to define equality this way since the observational thing is now a bridge type
def Eq (A : Type) : A → A → Type ≔ data [ erefl. : (a : A) → Eq A a a ]


  ` and without an Id type, funext is independent
axiom funext
  : (A : Type) (B : A → Type) (f0 f1 : (a : A) → B a)
    (ptEq : (a : A) → Eq (B a) (f0 a) (f1 a))
    → Eq ((a : A) → B a) f0 f1


`------------------------ work



def Gel (A0 A1 : Type) : (R : A0 → A1 → Type) → Lrel Type A0 A1
  ≔ R ↦ sig a0 a1 ↦ (
  ungel : R a0 a1 )


def GelInv (A0 A1 : Type) : Lrel Type A0 A1 → (A0 → A1 → Type)
  ≔ Rsig a0 a1 ↦ Rsig a0 a1

` up to funext
def RelRoundtrip (A0 A1 : Type) (R : A0 → A1 → Type) (a0 : A0) (a1 : A1)
  : Eq Type (GelInv A0 A1 (Gel A0 A1 R) a0 a1) (R a0 a1)
  ≔ ¿erefl. (R a0 a1)ʔ



{`
Eq (A0 → A1 → Type) (GelInv (Gel R)) R
  ≔ ¿funext A0 (_ |-> A1 -> Type)ʔ
 `}
