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

echo remLast Nat (zero. :: one :: two :: nil.)
