import LRX.EnclosingSelectedArcWord
import LRX.EnclosingCycleLoads

namespace LRX.FiniteCuts
open scoped BigOperators Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem enclosing_root_cursor_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G) (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by omega⟩ : Fin n) ∈ C.support)
    (r : Fin n) (hr : r ∈ C.support) :
    ∃ w : List Letter, eval w=(rotation r)⁻¹*p*rotation r ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-
        portLoad (displacement C) r := by
  have hlow : FiniteRankOrder.Below p G.symm := by
    simpa only [Equiv.symm_symm,Equiv.Perm.inv_def] using
      (FiniteRankOrder.below_inverse_iff p.symm G).mpr hbelow
  obtain ⟨w,hw,hl⟩ := enclosing_selected_arc_word hn p G C hlow hC hzero hlast []
    (by simp) (by intro a ha; simp at ha)
    (by intro i hi; simp at hi) (by intro i; right; simp)
    (fun _ => 0) (by simp) r r hr (Or.inl rfl) true r r le_rfl (by simp)
  refine ⟨w,hw,?_⟩
  simpa only [List.map_nil,List.sum_nil,sub_zero,arcCoordinate,ite_true,
    sub_self,Fin.val_zero,Nat.cast_zero,add_zero] using hl

/-- The outer coincident cursor needs only one step to zero and one back.
The root discount pays both steps. -/
theorem enclosing_last_cursor_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G) (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by omega⟩ : Fin n) ∈ C.support)
    (start finish : Fin n) (hs : start.val=n-1) (hf : finish.val=n-1) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|) := by
  obtain ⟨w,hw,hl⟩ := enclosing_root_cursor_word hn p G C hbelow hC hzero hlast 0 hzero
  have he : eval w=p := by simpa [RotationWords.rotation] using hw
  have hload := enclosing_cycle_port_load_ge_two C
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hC).1 hzero hlast 0 (by simp; omega)
  have hpreval : ((0 : Fin n)-start).val=1 := by
    rw [Fin.coe_sub_iff_lt.mpr (show (0 : Fin n) < start by change 0 < start.val; omega)]
    simp only [Fin.val_zero]
    omega
  have hpre : (toPort ((0 : Fin n)-start)).length ≤ 1 := by
    rw [toPort_length,hpreval]
    exact min_le_left _ _
  have hpost : (toPort (finish-(0 : Fin n))).length ≤ 1 := by
    rw [sub_zero,toPort_length,hf]
    have hh := min_le_right (n-1) (n-(n-1))
    omega
  refine ⟨toPort ((0 : Fin n)-start)++w++toPort (finish-(0 : Fin n)),?_,?_⟩
  · rw [eval_append,eval_append,toPort_eval_rotation,toPort_eval_rotation,rotation_sub,rotation_sub,he]
    simp [RotationWords.rotation,mul_assoc]
  · simp only [List.length_append,Nat.cast_add]
    have hpre' : ((toPort ((0 : Fin n)-start)).length : ℤ) ≤ 1 := by exact_mod_cast hpre
    have hpost' : ((toPort (finish-(0 : Fin n))).length : ℤ) ≤ 1 := by exact_mod_cast hpost
    linarith

#print axioms enclosing_root_cursor_word
#print axioms enclosing_last_cursor_word
end LRX.FiniteCuts
