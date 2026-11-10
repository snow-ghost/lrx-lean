module

public import LRX.SmallExteriorCatalogue

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow

def LocalPairSignConstraints {b c : ℕ} (σ : State b) (τ : State c) (parity eps xp xm : ℤ) : Prop :=
  (∀ (S : Finset (Fin b)) (T : Finset (Fin c)),
    (∀ i ∈ S, 0 < displacement σ i) →
    (∀ i ∈ T, 0 < displacement τ i) →
    (xp+(S.card : ℤ)+(T.card : ℤ))*(xp+(S.card : ℤ)+(T.card : ℤ)+parity) ≤
      eps+2*((∑ i ∈ S, |displacement σ i|)+(∑ i ∈ T, |displacement τ i|))) ∧
  (∀ (S : Finset (Fin b)) (T : Finset (Fin c)),
    (∀ i ∈ S, displacement σ i < 0) →
    (∀ i ∈ T, displacement τ i < 0) →
    (xm+(S.card : ℤ)+(T.card : ℤ))*(xm+(S.card : ℤ)+(T.card : ℤ)+parity) ≤
      eps+2*((∑ i ∈ S, |displacement σ i|)+(∑ i ∈ T, |displacement τ i|)))

instance {b c : ℕ} (σ : State b) (τ : State c) (parity eps xp xm : ℤ) :
    Decidable (LocalPairSignConstraints σ τ parity eps xp xm) := by
  unfold LocalPairSignConstraints
  infer_instance

def localPairSignCheck {b c : ℕ} (σ : State b) (τ : State c)
    (parity eps xp xm : ℤ) : Bool :=
  decide (LocalPairSignConstraints σ τ parity eps xp xm)

theorem local_pair_check_iff {b c : ℕ} (σ : State b) (τ : State c)
    (parity eps xp xm : ℤ) :
    localPairSignCheck σ τ parity eps xp xm=true ↔ LocalPairSignConstraints σ τ parity eps xp xm := by
  exact decide_eq_true_iff

#print axioms local_pair_check_iff
end LRX.FiniteCuts
