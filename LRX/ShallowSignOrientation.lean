import LRX.ExteriorHoleDeficit

namespace LRX.FiniteCuts
variable {r : ℕ}
theorem shallow_inverse (P : State (r+1)) (hs : Shallow P) : Shallow P.symm := by
  rw [shallow_iff_direct] at hs ⊢
  rw [displacement_mass_inverse]
  change _-(inversionNumber P⁻¹ : ℤ)=((P⁻¹).support.card : ℤ)-1
  rwa [inversion_number_inverse,Equiv.Perm.support_inv]
end LRX.FiniteCuts

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {r : ℕ}

theorem source_signs_card (P : State r) (hf : P.support=Finset.univ) :
    (positiveSources P).card+(negativeSources P).card=r := by
  have hu : positiveSources P ∪ negativeSources P=Finset.univ := by
    ext x
    simp only [positiveSources,negativeSources,Finset.mem_union,Finset.mem_filter,
      Finset.mem_univ,true_and,iff_true]
    have hne : P x ≠ x := Equiv.Perm.mem_support.mp (by simp [hf])
    have hn : (P x).val ≠ x.val := fun h => hne (Fin.ext h)
    omega
  have hd : Disjoint (positiveSources P) (negativeSources P) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hp := (Finset.mem_filter.mp hx).2
    have hn := (Finset.mem_filter.mp hy).2
    omega
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  simpa using hc.symm

theorem inverse_positive_sources (P : State r) :
    positiveSources P.symm=(negativeSources P).image P := by
  ext x
  simp only [positiveSources,negativeSources,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image]
  constructor
  · intro hx
    exact ⟨P.symm x,by simpa using hx,P.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa using hy

theorem inverse_positive_card (P : State r) :
    (positiveSources P.symm).card=(negativeSources P).card := by
  rw [inverse_positive_sources,Finset.card_image_of_injective _ P.injective]

theorem sign_counts_from_large_positive (P : State r) (hf : P.support=Finset.univ)
    (l η : ℕ) (hr : r=2*l+η) (hl : l+η ≤ (positiveSources P).card) :
    ∃ t : ℕ, (positiveSources P).card=l+η+t ∧ (negativeSources P).card=l-t := by
  have hc := source_signs_card P hf
  refine ⟨(positiveSources P).card-(l+η),?_,?_⟩ <;> omega

theorem oriented_sign_counts (P : State r) (hf : P.support=Finset.univ)
    (l η : ℕ) (hr : r=2*l+η) (hη : η ≤ 1) :
    (∃ t : ℕ, (positiveSources P).card=l+η+t ∧ (negativeSources P).card=l-t) ∨
    (∃ t : ℕ, (positiveSources P.symm).card=l+η+t ∧ (negativeSources P.symm).card=l-t) := by
  have hc := source_signs_card P hf
  by_cases hl : l+η ≤ (positiveSources P).card
  · exact Or.inl (sign_counts_from_large_positive P hf l η hr hl)
  · right
    apply sign_counts_from_large_positive P.symm (by change (P⁻¹).support=Finset.univ; rwa [Equiv.Perm.support_inv]) l η hr
    rw [inverse_positive_card]
    omega

theorem physical_mass_inverse (P : State r) (f : Fin r → ℤ) :
    physicalMass P.symm f=physicalMass P f := by
  have he := Equiv.sum_comp P (fun x => |f (P.symm x)-f x|)
  simpa only [physicalMass,Equiv.symm_apply_apply,abs_sub_comm] using he.symm

theorem inverse_original_match {n : ℕ} (P : State r) (f : Fin r → ℤ)
    (d : Fin n → ℤ) (emb : Fin r ↪ Fin n) (hδ : ∀ i, d (emb i)=f (P i)-f i) :
    ∀ i, -d ((P.symm.toEmbedding.trans emb) i)=f (P.symm i)-f i := by
  intro i
  change -d (emb (P.symm i))=f (P.symm i)-f i
  rw [hδ,Equiv.apply_symm_apply]
  ring

theorem physical_short_inverse (P : State r) (f : Fin r → ℤ) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h) : ∀ x, |f (P.symm x)-f x| ≤ h := by
  intro x
  have he := hshort (P.symm x)
  simpa only [Equiv.apply_symm_apply,abs_sub_comm] using he

#print axioms oriented_sign_counts
#print axioms physical_mass_inverse
end LRX.ContractionBlocks.System
