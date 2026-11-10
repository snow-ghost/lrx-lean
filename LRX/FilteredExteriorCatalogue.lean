import LRX.LocalPairSignCheck
import LRX.FinitePeakEnumeration

namespace LRX.FiniteCuts

abbrev SmallExteriorMap := Σ b : ℕ, State b

def compatibleSignOffsets (A B : SmallExteriorMap) (parity fixed eps : ℤ) : Bool :=
  (FinitePeak.integerInterval (-eps-2) (eps+2)).any fun xp =>
    decide (-eps-2 ≤ fixed-parity-xp ∧ fixed-parity-xp ≤ eps+2) &&
      localPairSignCheck A.2 B.2 parity eps xp (fixed-parity-xp)

theorem compatible_sign_offsets_iff (A B : SmallExteriorMap) (parity fixed eps : ℤ) :
    compatibleSignOffsets A B parity fixed eps=true ↔
    ∃ xp xm : ℤ, xp+xm=fixed-parity ∧
      (-eps-2 ≤ xp ∧ xp ≤ eps+2) ∧ (-eps-2 ≤ xm ∧ xm ≤ eps+2) ∧
      LocalPairSignConstraints A.2 B.2 parity eps xp xm := by
  constructor
  · intro h
    obtain ⟨xp,hxp,hc⟩ := List.any_eq_true.mp h
    rw [Bool.and_eq_true] at hc
    obtain ⟨hxm,hcheck⟩ := hc
    exact ⟨xp,fixed-parity-xp,by ring,
      (FinitePeak.mem_integerInterval _ _ _).mp hxp,of_decide_eq_true hxm,
      (local_pair_check_iff _ _ _ _ _ _).mp hcheck⟩
  · rintro ⟨xp,xm,hs,hxp,hxm,hcheck⟩
    have he : xm=fixed-parity-xp := by omega
    rw [he] at hxm hcheck
    apply List.any_eq_true.mpr
    refine ⟨xp,(FinitePeak.mem_integerInterval _ _ _).mpr hxp,?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hxm,(local_pair_check_iff _ _ _ _ _ _).mpr hcheck⟩

def filteredExteriorCatalogue (parity eps : ℤ) (fixed isolated width : ℕ) :
    List (SmallExteriorMap × SmallExteriorMap) :=
  (SProd.sprod smallExteriorCatalogue smallExteriorCatalogue).filter fun z =>
    decide (z.1.1+z.2.1=width ∧
      (z.1.1-z.1.2.support.card)+(z.2.1-z.2.2.support.card)+isolated ≤ fixed) &&
    compatibleSignOffsets z.1 z.2 parity fixed eps

theorem filtered_catalogue_mem_iff (A B : SmallExteriorMap) (parity eps : ℤ)
    (fixed isolated width : ℕ) :
    (A,B) ∈ filteredExteriorCatalogue parity eps fixed isolated width ↔
    A ∈ smallExteriorCatalogue ∧ B ∈ smallExteriorCatalogue ∧
    (A.1+B.1=width ∧ (A.1-A.2.support.card)+(B.1-B.2.support.card)+isolated ≤ fixed) ∧
    compatibleSignOffsets A B parity fixed eps=true := by
  simp only [filteredExteriorCatalogue,List.mem_filter,List.mem_product,Bool.and_eq_true,
    decide_eq_true_eq,Prod.fst,Prod.snd]
  tauto

#print axioms compatible_sign_offsets_iff
#print axioms filtered_catalogue_mem_iff
end LRX.FiniteCuts
