import LRX.EnclosingWindowLeftRoute
import LRX.WindowRightCycleSelection

namespace LRX.FiniteWindow
open scoped BigOperators Fin.CommRing
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n]

theorem enclosing_window_right_route (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (W : Window n b) (f : State b)
    (hmatch : ∀ i, G (embed W i)=embed W (f i))
    (havoid : ∀ i ∈ C.support, ¬Contains W i)
    (r : Fin n) (hr : r ∈ C.support) (hr0 : r ≠ 0)
    (hoff : W.offset+b=r.val)
    (start finish : Fin n) (hs : start.val ≤ (r-1 : Fin n).val)
    (hf : finish.val ≤ (r-1 : Fin n).val)
    (x : ℕ) (hx : x ≤ b) (hstart : min start.val finish.val+1 ≤ W.offset+x) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-
        portLoad (displacement C) (r-1)-cycleRightLoad f x+
        2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  let l := availableRightCycles f x
  obtain ⟨hc,hd,hparts,hpos⟩ := available_right_spec f x
  obtain ⟨ss,ht,hdisp,hports,hprice⟩ := right_window_family hn W l hc x hx hpos
  have hcan := window_family_canonical W l ss ht hdisp
  have hsdis := window_family_disjoint W l hd ss ht
  have hpart : CyclePart.IsPart (ss.map (fun a => a.service.target)).prod G.symm := by
    rw [ht]
    apply CyclePart.product _ G.symm
      (List.pairwise_map.mpr (hd.imp (fun h => (permutation_disjoint W _ _ h).inv_left.inv_right)))
    intro q hq
    obtain ⟨q0,hq0,rfl⟩ := List.mem_map.mp hq
    exact CyclePart.inverse (CyclePart.trans (CyclePart.window W (hparts q0 hq0))
      (CyclePart.window_part W f G hmatch))
  have houtside : C.Disjoint (ss.map (fun a => a.service.target)).prod := by
    rw [ht]
    apply Equiv.Perm.disjoint_prod_right
    intro q hq
    obtain ⟨q0,_,rfl⟩ := List.mem_map.mp hq
    intro i
    by_cases hi : i ∈ C.support
    · right
      change (permutation W q0).symm i=i
      rw [permutation_symm]
      exact permutation_outside W q0.symm i (havoid i hi)
    · exact Or.inl (Equiv.Perm.notMem_support.mp hi)
  have htotal : (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum ≤
      (ss.map (fun a => ∑ i, |a.displacement i|)).sum-cycleRightLoad f x := by
    rw [hprice,sum_price,window_family_mass W l ss hdisp]
    rw [show 2*(l.map (fun q => (rightPeak q x : ℤ))).sum=cycleRightLoad f x from
      available_right_discount f x]
  have hlow : FiniteRankOrder.Below p G.symm := by
    simpa only [Equiv.symm_symm,Equiv.Perm.inv_def] using
      (FiniteRankOrder.below_inverse_iff p.symm G).mpr hbelow
  have hrv : (r-1 : Fin n).val=r.val-1 := Fin.val_sub_one_of_ne_zero hr0
  obtain ⟨w,hw,hl⟩ := enclosing_selected_span_word hn p G C hlow hC hzero hlast
    ss hsdis hcan hpart houtside (cycleRightLoad f x) htotal r (r-1) hr
    (Or.inr (by ring)) true start finish hs hf (by
      intro a ha
      obtain ⟨hlo,hhi⟩ := hports a ha
      change min start.val finish.val ≤ a.service.port.val ∧ a.service.port.val ≤ (r-1 : Fin n).val
      constructor <;> omega)
  simp only [ite_true] at hl
  exact ⟨w,hw,by linarith⟩

#print axioms enclosing_window_right_route
end LRX.FiniteWindow
