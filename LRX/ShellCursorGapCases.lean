module

public import LRX.ShellExteriorWindowData
public import LRX.EnclosingCursorCases

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- Every consecutive gap of the new root is an actual old internal
window, the exterior remainder, or the empty joining boundary. -/
theorem shell_cursor_gap_cases (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (C : State n)
    (hCs : C.support=insert (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n)
      (insert (⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩ : Fin n)
        (prefixSourceCore p)))
    (start finish : Fin n) (hcursor : EnclosingCursorGap C start finish) :
    (∃ B ∈ positiveSourceFamily p (componentSet p 0).card,
      B.window.offset ≤ min start.val finish.val+1 ∧
        max start.val finish.val < B.window.offset+B.size) ∨
    ((componentSet p 0).card ≤ min start.val finish.val ∧ max start.val finish.val < n-1) ∨
    (start=componentRight p 0 ∧ finish=componentRight p 0) := by
  classical
  let L := (componentSet p 0).card
  let V : Fin n := ⟨L,component_card_lt_of_multiple_roots p hm 0⟩
  have hproper := component_card_lt_of_multiple_roots p hm 0
  obtain ⟨_,hright,hwidth⟩ := prefix_component_source_ends p hc hproper
  have hrightC : componentRight p 0 ∈ C.support := by
    rw [hCs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hright,by omega⟩))
  have hVC : V ∈ C.support := by
    rw [hCs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcases (i : Fin n) (hi : i ∈ C.support) : i.val < L ∨ i.val=L ∨ i.val=n-1 := by
    rw [hCs] at hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (Finset.mem_filter.mp hi).2
  have hsource (i : Fin n) (hi : i ∈ C.support) (hiL : i.val < L) : i ∈ sourcePackets p := by
    rw [hCs] at hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · dsimp only [L] at hiL; omega
    · change L < L at hiL; omega
    · exact (Finset.mem_filter.mp hi).1
  obtain ⟨u,hu,v,hv,huv,hgap,hus,hsv,huf,hfv⟩ := hcursor
  by_cases hvL : v.val < L
  · have huL : u.val < L := by omega
    have hug := hsource u hu huL
    have hvg := hsource v hv hvL
    have hgap' : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p := by
      intro x hux hxv hx
      apply hgap x hux hxv
      rw [hCs]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨hx,by dsimp only [L] at hvL; omega⟩))
    have hpos : 0 < portLoad (displacement p.symm) u :=
      load_path_crossed_port_positive p (component_right_path p 0) u (by simp)
        (by dsimp only [L] at hvL; omega)
    obtain ⟨hnext,hsel⟩ := consecutive_positive_gap_selected p L u v hug hvg huv hgap' hpos (by omega)
    let B := positiveSourceFilling p L ⟨u,hsel⟩
    have hB : B ∈ positiveSourceFamily p L := by
      apply List.mem_map.mpr
      exact ⟨⟨u,hsel⟩,by simp,rfl⟩
    have hBo : B.window.offset=u.val+1 := rfl
    have hBe : B.window.offset+B.size=v.val := by
      change u.val+1+(FiniteGaps.next (sourcePackets p) u-u.val-1)=v.val
      omega
    exact Or.inl ⟨B,hB,by rw [hBo]; omega,by rw [hBe]; omega⟩
  · by_cases huL : u.val < L
    · have hru : (componentRight p 0).val ≤ u.val := by
        by_contra h
        exact hgap _ (by omega) (by dsimp only [L] at hvL; omega) hrightC
      have hvle : v.val ≤ L := by
        by_contra h
        exact hgap V (by change u.val < L; omega) (by change L < v.val; omega) hVC
      have hs : start=componentRight p 0 := by apply Fin.ext; dsimp only [L] at *; omega
      have hf : finish=componentRight p 0 := by apply Fin.ext; dsimp only [L] at *; omega
      exact Or.inr (Or.inr ⟨hs,hf⟩)
    · have huEq : u.val=L := by have hh := hcases u hu; have := v.isLt; omega
      have hvEq : v.val=n-1 := by have hh := hcases v hv; omega
      exact Or.inr (Or.inl ⟨by dsimp only [L] at huEq; omega,by omega⟩)

#print axioms shell_cursor_gap_cases
end LRX.FiniteCuts
