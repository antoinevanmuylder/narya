{`
some basic narya-emacs commands
advance: C-c C-n
advance to point: C-c C-enter
synth type for term written in hole : C-:
synth normalized type for term writen in hold : C-;
refine (split or introduce): C-c C-y
 `}


{` ----------------simple example `}

def List : Type → Type ≔ A ↦ data [
| nil. : List A
| cons. : A → List A → List A ]

` Right-associative cons notation
notation(1) x "::" xs … ≔ cons. x xs

def remLast (A : Type) (as : List A) : List A ≔ match as [
| nil. ↦ nil.
| a :: nil. ↦ nil.
| a0 :: a1 :: as ↦ a0 :: (remLast A (a1 :: as))]



def Nat : Type ≔ data [ zero. : Nat | suc. : Nat → Nat ]

def one : Nat ≔ suc. zero.
def two : Nat ≔ suc. one
def three : Nat ≔ suc. two

def expl ≔ remLast Nat (zero. :: one :: two :: nil.)
echo expl

def eqExpl : Id (List Nat) expl (zero. :: one :: nil.) ≔ refl expl


{` ----------------using the ap (?)primitive `}
def remNatPreserves
  : (ns0 ns1 : List Nat) (ns2 : Id (List Nat) ns0 ns1)
    → Id (List Nat) (remLast Nat ns0) (remLast Nat ns1)
  ≔ ns0 ns1 ns2 ↦ ap (remLast Nat) ns2

{`
ap (x ↦ x) a₂ ≡ a₂
ap (_ ↦ b) a₂ ≡ refl b
ap (g ∘ f) a₂ ≡ ap g (ap f a₂)
ap f (refl a) ≡ refl (f a)
 `}




{`
--------------------Id on a record type
------------------- (record are by def. non-recursive, eta, dependent)
 `}

def Prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

axiom A : Type
axiom B : Type
axiom a0 : A
axiom a1 : A
axiom b0 : B
axiom b1 : B


def ObsIdPairs : Type ≔ sig (
  fstCompEq : Id A a0 a1,
  sndCompEq : Id B b0 b1 )

` Id (Prod A B) should be ObsIdPairs up to definitional iso
def toObs (ab2 : Id (Prod A B) (a0, b0) (a1, b1)) : ObsIdPairs ≔ (
  ab2 .fst,
  ab2 .snd)

def fromObs (oid : ObsIdPairs) : Id (Prod A B) (a0, b0) (a1, b1) ≔ (
  fst ≔ oid .fstCompEq,
  snd ≔ oid .sndCompEq)

def roundtripObsIdPairs (oid : ObsIdPairs)
  : Id ObsIdPairs (toObs (fromObs oid)) oid
  ≔ (fstCompEq ≔ refl _, sndCompEq ≔ refl _)

def roundtripIdProd (ab2 : Id (Prod A B) (a0, b0) (a1, b1)) : ObsIdPairs
  ≔ (fstCompEq ≔ ab2 .fst, sndCompEq ≔ ab2 .snd)


{` ----------------------Id on a codata type `}

def Stream (A : Type) : Type ≔ codata [ _ .hd : A | _ .tl : Stream A ]

def nats (n : Nat) : Stream Nat ≔ [ .hd ↦ n | .tl ↦ nats (suc. n) ]

` todo write example


{` --------------------- encode decode for Nat `}
def ObsEqNat : Nat → Nat → Type ≔ data [
| myzero. : ObsEqNat zero. zero.
| mysuc. : (m0 m1 : Nat) → ObsEqNat (suc. m0) (suc. m1) ]

def encode (n0 n1 : Nat) : Id Nat n0 n1 → ObsEqNat n0 n1 ≔ n2 ↦ match n2 [
| zero. ⤇ myzero.
| suc. x ⤇ mysuc. x.0 x.1] ` endpoint syntax. see "Cubes of variables"

def decode (n0 n1 : Nat) : ObsEqNat n0 n1 → Id Nat n0 n1
  ≔ oid ↦ match oid [ myzero. ↦ zero. | mysuc. m0 m1 ↦ ¿ʔ ]






{` ----------------Id on a data type `}


axiom nlist0 : List Nat
axiom nlist1 : List Nat

` does not compute to false
` but does compute to a data type called List^(e)
echo Id (List Nat) (zero. :: nlist0) (one :: nlist1) : Type
echo Id Nat zero. one

{`
| nil. : List⁽ᵉ⁾ (Id A) nil. nil.
| cons. {x₀ x₁ : A} (x₂ : Id A x₀ x₁) {xs₀ xs₁ : List A} (xs₂ : List⁽ᵉ⁾ (Id A) xs₀ xs₁)
    : List⁽ᵉ⁾ (Id A) (cons. x₀ xs₀) (cons. x₁ xs₁)
 `}


def Empty : Type ≔ data []


def isEmpty : (Id (List Nat) (zero. :: nlist0) (one :: nlist1)) → Empty
  ≔ nlist2 ↦ match nlist2 [ nil. ⤇ ¿  ʔ | x :: y ⤇ ¿ ʔ ]
