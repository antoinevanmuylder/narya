
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


{` reviewing Id `}

axiom nlist0 : List Nat
axiom nlist1 : List Nat

` this doesnt compute to false apparently
echo Id (List Nat) (zero. :: nlist0) (one :: nlist1) : Type
echo Id Nat zero. one


` using the ap (?)primitive
def remNatPreserves
  : (ns0 ns1 : List Nat) (ns2 : Id (List Nat) ns0 ns1)
    → Id (List Nat) (remLast Nat ns0) (remLast Nat ns1)
  ≔ ns0 ns1 ns2 ↦ ap (remLast Nat) ns2
