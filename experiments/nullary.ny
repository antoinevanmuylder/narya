{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-arity" "0" "-internal" "-direction" "w,refl,Br,ab") -*- `}

` in order to reload flags:
` use C-c C-x to kill Narya + revert buffer


def Unit : Type ≔ sig ()

def Mb (N : Type) : Type ≔ data [ none. : Mb N | just. : N → Mb N ]


axiom Nm : Type


` Gel (A0 A1 : Type) (R : A0 -> A1 -> Type) : Br Type A0 A1
` := sig a0 a1 |-> (ungel : R a0 a1)
def GelNm : Br Type . ≔ sig ( ungel : Nm )

def Gel (N : Type) : Br Type . ≔ sig ( ungel : N )
def InvGel (B : Br Type .) : Type ≔ B .

axiom myN : Type
axiom myB : Br Type .

echo InvGel (Gel myN)
echo Gel (InvGel myB)

` Id Bool : Id Type Bool Bool
def Bool : Type ≔ data [ false. | true. ]


echo Br (Nm → Bool)
echo Br (Nm → Bool) .
echo Bool⁽ʷ⁾ .

def ReflNm : Br Type . ≔ sig ( obs : Mb Nm )
def something : ReflNm . ≔ (obs ≔ none.)

echo refl Type
` Type⁽ʷ⁾ : Type⁽ʷ⁾
echo refl Type .
` Type⁽ʷ⁾ .  : Type
