module

public import LRX.TwoArcCoreWord
public import LRX.PartitionGapSharpWord

@[expose] public section

namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

def BothCoreArcs (S : Finset (Fin n)) (start finish : Fin n) : Prop :=
  ∀ dir : Bool, ∃ r ∈ S, (arcCoordinate dir start r).val ≤ (arcCoordinate dir start finish).val

def CommonGap (S : Finset (Fin n)) (start finish : Fin n) : Prop :=
  ∃ a ∈ S, (a.val ≤ start.val ∧ start.val < next S a) ∧
    (a.val ≤ finish.val ∧ finish.val < next S a)

theorem ordered_mark_arc_coverage (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S)
    (s t r : Fin n) (hr : r ∈ S) (hst : s.val < t.val)
    (hsr : s.val ≤ r.val) (hrt : r.val ≤ t.val) :
    BothCoreArcs S s t ∧ BothCoreArcs S t s := by
  constructor
  · intro dir
    cases dir
    · refine ⟨0,hzero,?_⟩
      simp only [arcCoordinate,Bool.false_eq_true,ite_false,sub_zero]
      rw [Fin.coe_sub_iff_lt.mpr hst]
      have ht := t.isLt
      omega
    · refine ⟨r,hr,?_⟩
      simp only [arcCoordinate,ite_true]
      rw [Fin.sub_val_of_le hsr,Fin.sub_val_of_le (le_of_lt hst)]
      omega
  · intro dir
    cases dir
    · refine ⟨r,hr,?_⟩
      simp only [arcCoordinate,Bool.false_eq_true,ite_false]
      rw [Fin.sub_val_of_le hrt,Fin.sub_val_of_le (le_of_lt hst)]
      omega
    · refine ⟨0,hzero,?_⟩
      simp only [arcCoordinate,ite_true]
      rw [Fin.coe_sub_iff_lt.mpr (show (0 : Fin n) < t by change 0 < t.val; omega),
        Fin.coe_sub_iff_lt.mpr hst]
      simp only [Fin.val_zero]
      have ht := t.isLt
      omega

theorem ordered_cursor_dichotomy (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S)
    (s t : Fin n) (hst : s.val ≤ t.val) :
    (BothCoreArcs S s t ∧ BothCoreArcs S t s) ∨ CommonGap S s t := by
  classical
  by_cases hmark : ∃ r ∈ S, s.val ≤ r.val ∧ r.val ≤ t.val
  · obtain ⟨r,hr,hsr,hrt⟩ := hmark
    left
    by_cases he : s=t
    · subst t
      have her : r=s := Fin.ext (by omega)
      subst r
      constructor <;> intro dir <;> exact ⟨s,hr,le_rfl⟩
    · exact ordered_mark_arc_coverage S hzero s t r hr
        (by have hne : s.val ≠ t.val := fun h => he (Fin.ext h); omega) hsr hrt
  · have hsnot : s ∉ S := fun hs => hmark ⟨s,hs,le_rfl,hst⟩
    obtain ⟨a,ha,hgap⟩ := outside_in_gap S hzero s hsnot
    obtain ⟨has',hsn⟩ := (mem_positions S a s).mp hgap
    have htn : t.val < next S a := by
      by_contra h
      have hn : next S a<n := by have := t.isLt; omega
      obtain ⟨r,hr,he⟩ := next_is_member S a hn
      exact hmark ⟨r,hr,by omega,by omega⟩
    exact Or.inr ⟨a,ha,⟨le_of_lt has',hsn⟩,⟨by omega,htn⟩⟩

theorem cursor_dichotomy (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S)
    (start finish : Fin n) : BothCoreArcs S start finish ∨ CommonGap S start finish := by
  by_cases h : start.val ≤ finish.val
  · rcases ordered_cursor_dichotomy S hzero start finish h with ha | hg
    · exact Or.inl ha.1
    · exact Or.inr hg
  · rcases ordered_cursor_dichotomy S hzero finish start (by omega) with ha | hg
    · exact Or.inl ha.2
    · obtain ⟨a,ha,hf,hs⟩ := hg
      exact Or.inr ⟨a,ha,hs,hf⟩

#print axioms cursor_dichotomy
end LRX.FiniteGaps
