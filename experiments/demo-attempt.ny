{`
some basic narya-emacs commands
advance: C-c C-n
advance to point: C-c C-enter
synth type for term written in hole : C-:
synth normalized type for term writen in hold : C-;
refine (split or introduce): C-c C-y
 `}


{`

- narya doc index


- Id (Prod A B) is what you expect
- encode decode for Nat
- church bool








`}

` Id = refl, ap = refl,
` def refl : { A : Type }    (a : A) → Id A a a ≔ A a ↦ refl a
` Id (B : Type)b 0 :



def Prod : Type → Type → Type ≔ A B ↦ sig ( fst : A, snd : B )

axiom A : Type
axiom B : Type
axiom a0 : A
axiom a1 : A
axiom b0 : B
axiom b1 : B





def EqPairs : Type ≔ sig ( fstCompEq : Id A a0 a1, sndCompEq : Id B b0 b1 )

` Id (Prod A B) (a0 , b0) (a1 , b1)

echo (refl Prod)

def toId : EqPairs → Id (Prod A B) (a0, b0) (a1, b1) ≔ eqpairs ↦ (
  fst ≔ eqpairs .fstCompEq,
  snd ≔ eqpairs .sndCompEq)

def toEqPairs (ab2 : Id (Prod A B) (a0, b0) (a1, b1)) : EqPairs ≔ (
  fstCompEq ≔ ab2 .fst,
  sndCompEq ≔ ab2 .snd)

def Nat : Type ≔ data [ zero. : Nat | suc. : Nat → Nat ]

def thing : Type ≔ Type → data []

` data []
` sig ()

def Code : Nat → Nat → Type ≔ n0 ↦ match n0 [
| zero. ↦ [ zero. ↦ sig () | suc. n1 ↦ data [] ]
| suc. n0 ↦ [ zero. ↦ data [] | suc. n1 ↦ Code n0 n1 ]]


` Id Nat n0 n1
def encode (n0 n1 : Nat) : (n2 : Id Nat n0 n1) → Code n0 n1
  ≔ n2 ↦ match n2 [ zero. ⤇ () | suc. x ⤇ encode x.0 x.1 x.2 ]

` x |=> M    {x.0 x.1 } x.2 |-> M `}
{` `}


def decode (n0 n1 : Nat) : (c : Code n0 n1) → Id Nat n0 n1 ≔ match n0 [
| zero. ↦ match n1 [ zero. ↦ c ↦ refl 0 | suc. n1 ↦ [ ] ]
| suc. n0 ↦ match n1 [ zero. ↦ [ ] | suc. n1 ↦ c ↦ suc. (decode n0 n1 c) ]]

` def Eq (A : Type) : A → A → Type ≔ data [ erefl. : (a : A) → Eq A a a ]

{`
def Eqj (A : Type) (a : A) : A -> Type := data [
|  ejrefl :
]
 `}
