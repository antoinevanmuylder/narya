{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-arity" "2" "-internal" "-direction" "p,refl,Lrel,ab") -*- `}

` in order to reload flags:
` use C-c C-x to kill Narya + revert buffer




  ` currently need to define equality this way since the observational thing is now a bridge type
def Eq (A : Type) : A → A → Type ≔ data [ erefl. : (a : A) → Eq A a a ]


  ` and without an Id type, funext is independent
axiom funext
  : (A : Type) (B : A → Type) (f0 f1 : (a : A) → B a)
    (ptEq : (a : A) → Eq (B a) (f0 a) (f1 a))
    → Eq ((a : A) → B a) f0 f1






def Bool : Type ≔ data [ false. : Bool | true. : Bool ]


def Church : Type ≔ (A : Type) → A → A → A


def toChurch : Bool → Church ≔ [
| false. ↦ A a0 a1 ↦ a0
| true. ↦ A a0 a1 ↦ a1]


def toBool : Church → Bool ≔ k ↦ k Bool false. true.




def roundtripBool : (b : Bool) → Eq Bool (toBool (toChurch b)) b ≔ [
| false. ↦ erefl. false.
| true. ↦ erefl. true.]


def Gel (A0 A1 : Type) (R : A0 → A1 → Type) : Lrel Type A0 A1
  ≔ sig a0 a1 ↦ (
  unRel : R a0 a1 )

def gel (A0 A1 : Type) (R : A0 → A1 → Type) (a0 : A0) (a1 : A1)
  (a2 : R a0 a1)
  : Gel A0 A1 R a0 a1
  ≔ (unRel ≔ a2)

def globalFreeThm (k : (A : Type) → A → A → A) (A0 A1 : Type)
  (R : A0 → A1 → Type) (af0 : A0) (af1 : A1) (af2 : R af0 af1) (at0 : A0)
  (at1 : A1) (at2 : R at0 at1)
  : R (k A0 af0 at0) (k A1 af1 at1)
  ≔ (refl k (Gel A0 A1 R) (gel A0 A1 R af0 af1 af2)
       (gel A0 A1 R at0 at1 at2)) .unRel

` up to funext.
def roundtripChurch (k : (A : Type) → A → A → A) (A : Type) (af at : A)
  : Eq A (toChurch (toBool k) A af at) (k A af at)
  ≔ globalFreeThm k Bool A (b a ↦ Eq A (toChurch b A af at) a) false. af
      (erefl. af) true. at (erefl. at)
