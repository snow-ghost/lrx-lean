module

public import LRX.ComponentCutExtraction

@[expose] public section

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Singleton load components force the original permutation to be the identity. -/
theorem eq_one_of_singleton_components (p : State n)
    (hcap : ∀ i, (componentSet p i).card ≤ 1) : p = 1 := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hfix (i : Fin n) : p.symm i = i := by
    apply (Finset.card_le_one.mp (hcap i))
    · exact (CycleFootprint.mem_component _ _ _).mpr
        (CycleFootprint.arrow_target_load_path hd i)
    · exact (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl
  apply Equiv.ext
  intro i
  have h := hfix (p i)
  simpa only [Equiv.symm_apply_apply, Equiv.Perm.one_apply] using h.symm

/-- The entire small-component branch: the cut, cap and actual word are derived
from the original canonical load graph, for arbitrary cursor positions. -/
theorem small_components_sharp_word (hn : 4 ≤ n) (p : State n)
    (hsmall : ∀ i, (componentSet p i).card ≤ (n+1)/2) (start finish : Fin n) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹ * p * rotation finish ∧
      w.length ≤ n.choose 2 := by
  classical
  obtain ⟨a,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => (componentSet p i).card) ⟨0,Finset.mem_univ _⟩
  have hcap (i : Fin n) : (componentSet p i).card ≤ (componentSet p a).card :=
    hmax i (Finset.mem_univ _)
  by_cases htwo : 2 ≤ (componentSet p a).card
  · let r := componentLeft p a
    let q := localTarget p 0 r
    obtain ⟨hcut,hcards⟩ := component_recenter_cut p a
    have hqcap (i : Fin n) : (componentSet q i).card ≤ (componentSet p a).card := by
      change (componentSet (localTarget p 0 (componentLeft p a)) i).card ≤ _
      rw [hcards]
      exact hcap _
    have hw : ∃ w : List Letter, eval w = (rotation (start-r))⁻¹ * q * rotation (finish-r) ∧
        w.length ≤ n.choose 2 := by
      by_cases hhalf : (componentSet p a).card ≤ n/2
      · exact two_block_sharp_word_of_component_cap _ htwo hhalf q hcut hqcap _ _
      · have hsize : (componentSet p a).card = n/2+1 := by have := hsmall a; omega
        have hodd : n = 2*(n/2)+1 := by have := hsmall a; omega
        have hc : ∀ i : Fin n, (q i).val < n/2+1 ↔ i.val < n/2+1 := by
          simpa only [hsize] using hcut
        exact two_block_sharp_word_odd (n/2) (by omega) hodd q hc _ _
    obtain ⟨w,he,hl⟩ := hw
    exact ⟨w,he.trans (shifted_word_target p r start finish),hl⟩
  · have hp : p = 1 := eq_one_of_singleton_components p (fun i => by have := hcap i; omega)
    refine ⟨toPort (finish-start),?_,?_⟩
    · rw [toPort_eval_rotation,rotation_sub,hp,mul_one]
    · have hl := toPort_length_le (finish-start)
      have hc := twice_choose_two_int n
      have hmul : (n : ℤ) ≤ (n : ℤ)*((n : ℤ)-1) := by nlinarith
      have hh : (n/2 : ℕ) ≤ n.choose 2 := by omega
      exact hl.trans hh

#print axioms eq_one_of_singleton_components
#print axioms small_components_sharp_word
end LRX.FiniteCuts
