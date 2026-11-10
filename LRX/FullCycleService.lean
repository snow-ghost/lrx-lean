module

public import LRX.BufferItinerary
public import LRX.BufferBalance

@[expose] public section

/-! An actual buffer-service word for a supplied complete cyclic order of labels.
The order follows the physical target permutation. Correctness, closed integer
cursor, every integer endpoint, and exact rotation price are proved. The raw X
count is not reduced to affine inversion length here. -/
namespace LRX.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def logicalDelta (d : Fin n → ℤ) (i : Fin n) : ℤ :=
  PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i) - PeriodicBuffer.contract (n : ℤ) (i : ℤ)

def Follows (p : State n) : List (Fin n) → Prop
  | [] => True
  | a :: rest => match rest with
    | [] => True
    | b :: _ => p.symm a=b ∧ Follows p rest

theorem follows_compatible {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (path : List (Fin n)) (hp : Follows p path) :
    Compatible (initialLogical (n := n)).coord (logicalDelta d) path := by
  induction path with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest =>
      refine ⟨?_, ih hp.2⟩
      have hm : Int.ModEq (n : ℤ) ((a : ℤ)+d a) (b : ℤ) := by
        simpa only [hp.1, add_zero] using hd.2 a
      have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
      have hh := PeriodicBuffer.contract_modEq hn0 hm
      change Int.ModEq (BufferMachine.slots n)
        (PeriodicBuffer.contract (n : ℤ) (a : ℤ) +
          (PeriodicBuffer.contract (n : ℤ) ((a : ℤ)+d a)-PeriodicBuffer.contract (n : ℤ) (a : ℤ)))
        (PeriodicBuffer.contract (n : ℤ) (b : ℤ))
      convert hh using 1
      ring

#print axioms follows_compatible
end LRX.BufferProgram
