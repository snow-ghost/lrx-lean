module

public import LRX.PermutationCode

@[expose] public section

namespace LRX

/-- A compact representation of literal generator words. The natural
number is data only; semantics is always checked by the Lean kernel. -/
def unpackWord (k : ℕ) : List Letter :=
  if h : k=0 then [] else
    (if k%4=1 then Letter.l else if k%4=2 then Letter.r else Letter.x)::unpackWord (k/4)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

end LRX
