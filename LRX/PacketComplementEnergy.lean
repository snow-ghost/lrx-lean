import LRX.GapComplementCoordinates

/-! The complementary interval of a packet gap bounds the packet energy by
2*l*(n-b-l), with l the half-size of the actual packet support. -/
namespace LRX.FiniteCoordinates
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem card_le_of_coordinates (S : Finset α) (f : α → ℤ) (L : ℕ)
    (hf : Set.InjOn f S) (hlo : ∀ i ∈ S, 0 ≤ f i) (hhi : ∀ i ∈ S, f i < L) : S.card ≤ L := by
  classical
  let e : {i // i ∈ S} → Fin L := fun i => ⟨(f i.val).toNat,by
    have := hlo i.val i.property
    have := hhi i.val i.property
    omega⟩
  have hinj : Function.Injective e := by
    intro i j he
    apply Subtype.ext
    apply hf i.property j.property
    have hv := congrArg Fin.val he
    change (f i.val).toNat=(f j.val).toNat at hv
    have := hlo i.val i.property
    have := hlo j.val j.property
    omega
  have h := Fintype.card_le_of_injective e hinj
  simpa using h

#print axioms card_le_of_coordinates
end LRX.FiniteCoordinates
