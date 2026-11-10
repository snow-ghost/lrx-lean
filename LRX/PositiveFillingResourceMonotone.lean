import LRX.FillingFamilyResource
import LRX.SourceGapReversalFamily

/-! The prefix and whole-map window families use the same actual fillings.
Their independently chosen restrictions agree by matching the original map. -/
namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem positive_source_filling_eq (p : State n) (L M : ℕ)
    (u : {u // u ∈ positiveSourceGapStarts p L})
    (v : {v // v ∈ positiveSourceGapStarts p M}) (he : u.val=v.val) :
    positiveSourceFilling p L u=positiveSourceFilling p M v := by
  obtain ⟨i,hi⟩ := u
  obtain ⟨j,hj⟩ := v
  change i=j at he
  subst j
  have hf : Classical.choose (positive_source_gap_filling_exists p L ⟨i,hi⟩)=
      Classical.choose (positive_source_gap_filling_exists p M ⟨i,hj⟩) := by
    apply Equiv.ext
    intro x
    apply embed_injective (FiniteGaps.window (sourcePackets p) i)
    exact (Classical.choose_spec (positive_source_gap_filling_exists p L ⟨i,hi⟩) x).symm.trans
      (Classical.choose_spec (positive_source_gap_filling_exists p M ⟨i,hj⟩) x)
  unfold positiveSourceFilling
  rw [hf]

theorem positive_source_family_nodup (p : State n) (L : ℕ) : (positiveSourceFamily p L).Nodup := by
  classical
  apply List.Nodup.map ?_ (Finset.nodup_toList _)
  intro u v he
  have hh := congrArg (fun A : FillingWindow n => A.window.offset) he
  change u.val.val+1=v.val.val+1 at hh
  apply Subtype.ext
  apply Fin.ext
  omega

theorem positive_source_family_subset (p : State n) (L M : ℕ) (hLM : L ≤ M) :
    positiveSourceFamily p L ⊆ positiveSourceFamily p M := by
  intro A hA
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hA
  have hu := (mem_positive_source_gap_starts p L u.val).mp u.property
  have hv : u.val ∈ positiveSourceGapStarts p M :=
    (mem_positive_source_gap_starts p M u.val).mpr ⟨hu.1,hu.2.1,hu.2.2.1.trans hLM,hu.2.2.2⟩
  apply List.mem_map.mpr
  refine ⟨⟨u.val,hv⟩,?_,?_⟩
  · exact Finset.mem_toList.mpr (Finset.mem_attach _ _)
  · exact (positive_source_filling_eq p L M u ⟨u.val,hv⟩ rfl).symm

theorem positive_filling_resource_mono (p : State n) (L M : ℕ) (hLM : L ≤ M) :
    ((positiveSourceFamily p L).map FillingWindow.resource).sum ≤
      ((positiveSourceFamily p M).map FillingWindow.resource).sum := by
  classical
  have hsub : (positiveSourceFamily p L).toFinset ⊆ (positiveSourceFamily p M).toFinset := by
    intro A hA
    exact List.mem_toFinset.mpr (positive_source_family_subset p L M hLM (List.mem_toFinset.mp hA))
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := FillingWindow.resource) (fun A _ _ => by
      have h := filling_resource_half_width A.filling
      change 0 ≤ fillingResource A.filling
      omega)
  rw [List.sum_toFinset _ (positive_source_family_nodup p L),
    List.sum_toFinset _ (positive_source_family_nodup p M)] at hh
  exact hh

#print axioms positive_source_filling_eq
#print axioms positive_filling_resource_mono
end LRX.FiniteCuts
