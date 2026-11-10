module

public import LRX.ShallowSignOrientation

@[expose] public section

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {r n : ℕ}

theorem ambient_physical_short {d : Fin n → ℤ} (hd : ∑ i, d i=0)
    (hm : AffineLift.Majorized d) (P : State (r+1)) (f : Fin (r+1) → ℤ)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i) :
    ∀ i, |f (P i)-f i| ≤ ((n : ℤ)-1)/2 := by
  intro i
  have hh := AffineLift.short_coordinates hd hm (emb i)
  rw [hδ] at hh
  simp only [abs_eq_max_neg]
  omega

/-- (30) with sign orientation and original shortness derived. -/
theorem geometric_internal_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (gap : Fin r) (l η j s b c outside : ℕ)
    (hr : r+1=2*l+η) (hη : η ≤ 1) (hn : n=r+1+s) (hslots : s=b+c+outside)
    (hgap : f gap.succ-f gap.castSucc-1=b) (hholes : holeMass f=(b : ℤ)+c)
    (hj : (j : ℤ)=(2*(b : ℤ)-s-η)/2) :
    (2*(b : ℤ)-s-η)^2-(2*(b : ℤ)-s-η)%2+8*j*outside ≤ 4*shellDeficit n l P f := by
  let h : ℤ := ((n : ℤ)-1)/2
  have hshort : ∀ x, |f (P x)-f x| ≤ h := ambient_physical_short hd hm P f emb hδ
  have hhalf : 2*h < n := by dsimp [h]; omega
  rcases oriented_sign_counts P hfull l η hr hη with ⟨t,hpos,hneg⟩ | ⟨t,hpos,hneg⟩
  · exact dominant_hole_quadratic_deficit P hp hs hfull f hf hd hm emb hδ h hshort hhalf
      gap l η t j s b c outside hr hn hslots hgap hholes hpos hneg hj
  · have hd' : (∑ i, -d i)=0 := by rw [Finset.sum_neg_distrib,hd,neg_zero]
    have hf' : Equiv.Perm.support P.symm=Finset.univ := by
      change (P⁻¹).support=Finset.univ
      rwa [Equiv.Perm.support_inv]
    have hc := dominant_hole_quadratic_deficit P.symm (Equiv.Perm.isCycle_inv.mpr hp)
      (FiniteCuts.shallow_inverse P hs) hf' f hf hd' (AffineLift.majorized_neg hd hm)
      (P.symm.toEmbedding.trans emb) (inverse_original_match P f d emb hδ) h
      (physical_short_inverse P f h hshort) hhalf
      gap l η t j s b c outside hr hn hslots hgap hholes hpos hneg hj
    simpa only [shellDeficit,physical_mass_inverse] using hc

/-- The physical width of a large component ensures that ordinary contractions
can reach the thresholds used for its exterior-hole estimate. -/
theorem exterior_threshold_size (f : Fin (r+1) → ℤ) (n s c outside j η : ℕ)
    (hn : n=r+1+s) (hslots : s=c+outside) (hholes : holeMass f=c)
    (hwide : (n : ℤ) ≤ 2*(f (Fin.last r)-f 0))
    (hj : (j : ℤ)=((outside : ℤ)-c-η)/2) : 2*j+η < r+1 := by
  have he := holeMass_span f
  rw [hholes] at he
  omega

/-- (32) with both orientation and threshold size derived from geometric data. -/
theorem geometric_exterior_deficit (P : State (r+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (r+1) → ℤ) (hf : StrictMono f)
    {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d)
    (emb : Fin (r+1) ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i)
    (l η j s c outside : ℕ) (hr : r+1=2*l+η) (hη : η ≤ 1)
    (hn : n=r+1+s) (hslots : s=c+outside) (hholes : holeMass f=c)
    (hwide : (n : ℤ) ≤ 2*(f (Fin.last r)-f 0))
    (hj : (j : ℤ)=((outside : ℤ)-c-η)/2) :
    ((outside : ℤ)-c-η)^2/4 ≤ shellDeficit n l P f := by
  have hsize := exterior_threshold_size f n s c outside j η hn hslots hholes hwide hj
  rcases oriented_sign_counts P hfull l η hr hη with ⟨t,hpos,hneg⟩ | ⟨t,hpos,hneg⟩
  · exact exterior_hole_quadratic_deficit P hp hs hfull f hf hd hm emb hδ
      l η t j s c outside hr hn hslots hholes hpos hneg hsize hj
  · have hd' : (∑ i, -d i)=0 := by rw [Finset.sum_neg_distrib,hd,neg_zero]
    have hf' : Equiv.Perm.support P.symm=Finset.univ := by
      change (P⁻¹).support=Finset.univ
      rwa [Equiv.Perm.support_inv]
    have hc := exterior_hole_quadratic_deficit P.symm (Equiv.Perm.isCycle_inv.mpr hp)
      (FiniteCuts.shallow_inverse P hs) hf' f hf hd' (AffineLift.majorized_neg hd hm)
      (P.symm.toEmbedding.trans emb) (inverse_original_match P f d emb hδ)
      l η t j s c outside hr hn hslots hholes hpos hneg hsize hj
    simpa only [shellDeficit,physical_mass_inverse] using hc

#print axioms geometric_internal_deficit
#print axioms geometric_exterior_deficit
end LRX.ContractionBlocks.System
