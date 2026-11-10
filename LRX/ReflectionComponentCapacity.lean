module

public import LRX.TwoBlockReflectionBarrier
public import LRX.LoadComponentCardRecenter

@[expose] public section

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- A strictly short lift of the equality reflection has no large load component. -/
theorem reflection_component_card (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (href : ∀ i : Fin n, p.symm i= -i-((((n-1)/2 : ℕ) : ℤ) : Fin n))
    (a : Fin n) : (CycleFootprint.component d a).card ≤ n-n/2 := by
  have hcan := reflection_recenter_one_canonical hn hd hshort href
  have hb := two_block_reflection_component_card hn (localTarget p 0 1)
    (reflection_recenter_one_two_blocks hn p href) (a-1)
  rw [← hcan,load_component_card_recenter,sub_add_cancel] at hb
  exact hb

/-- Equality in the inversion capacity restricts every actual component to ceil(n/2). -/
theorem capacity_equality_component_card (hn : 2 ≤ n)
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (hinheritNeg : ∀ i, d i= -(((n-1)/2 : ℕ) : ℤ) → original i= -(((n-1)/2 : ℕ) : ℤ))
    (hinheritPos : ∀ i, d i= (((n-1)/2 : ℕ) : ℤ) → original i= (((n-1)/2 : ℕ) : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ))
    (a : Fin n) : (CycleFootprint.component d a).card ≤ n-n/2 := by
  obtain ⟨r,href⟩ := strict_capacity_equality_reflection horiginal hmaj hd hshort
    hinheritNeg hinheritPos heq
  have hdlocal := recentered_lift (0 : Fin n) r (by simpa using hd)
  have hb := reflection_component_card hn hdlocal
    (fun i => hshort ((L n^r.val) i)) href (a-r)
  rw [load_component_card_recenter,sub_add_cancel] at hb
  exact hb

/-- The strict part of Lemma 12 for a real completed lift with an actual large component. -/
theorem strict_capacity_of_large_component (hn : 2 ≤ n)
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (hinheritNeg : ∀ i, d i= -(((n-1)/2 : ℕ) : ℤ) → original i= -(((n-1)/2 : ℕ) : ℤ))
    (hinheritPos : ∀ i, d i= (((n-1)/2 : ℕ) : ℤ) → original i= (((n-1)/2 : ℕ) : ℤ))
    (a : Fin n) (hlarge : n-n/2 < (CycleFootprint.component d a).card) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-1 := by
  have hcap := strict_band_inversion_capacity hd hshort
  by_contra hnot
  have heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by omega
  have hsmall := capacity_equality_component_card hn horiginal hmaj hd hshort
    hinheritNeg hinheritPos heq a
  omega

#print axioms reflection_component_card
#print axioms capacity_equality_component_card
#print axioms strict_capacity_of_large_component
end LRX.FiniteCuts
