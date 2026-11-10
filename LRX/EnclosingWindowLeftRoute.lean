module

public import LRX.EnclosingSpanRoute
public import LRX.WindowFamilyBridge
public import LRX.WindowCycleSelection

@[expose] public section

namespace LRX.FiniteWindow
open scoped BigOperators Fin.CommRing
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n]

/-- The left gap-boundary route for a genuine invariant window of an upper
map. All available child cycles and their exact services are selected here;
rank transfer constructs a word of the original lower map. -/
theorem enclosing_window_left_route (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (W : Window n b) (f : State b)
    (hmatch : ∀ i, G (embed W i)=embed W (f i))
    (havoid : ∀ i ∈ C.support, ¬Contains W i)
    (r : Fin n) (hr : r ∈ C.support) (hoff : W.offset=r.val+1)
    (start finish : Fin n) (hs : r.val ≤ start.val) (hf : r.val ≤ finish.val)
    (y : ℕ) (hy : y ≤ b) (hfinish : W.offset+y ≤ max start.val finish.val+1) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-
        portLoad (displacement C) r-cycleLeftLoad f y+
        (start.val : ℤ)+(finish.val : ℤ)-2*(r.val : ℤ) := by
  let l := availableLeftCycles f y
  obtain ⟨hc,hd,hparts,hpos⟩ := available_left_spec f y
  obtain ⟨ss,ht,hdisp,hports,hprice⟩ := left_window_family hn W l hc y hy hpos
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
      (ss.map (fun a => ∑ i, |a.displacement i|)).sum-cycleLeftLoad f y := by
    rw [hprice,sum_price,window_family_mass W l ss hdisp]
    rw [show 2*(l.map (fun q => (leftPeak q y : ℤ))).sum=cycleLeftLoad f y from
      available_left_discount f y]
  have hlow : FiniteRankOrder.Below p G.symm := by
    simpa only [Equiv.symm_symm,Equiv.Perm.inv_def] using
      (FiniteRankOrder.below_inverse_iff p.symm G).mpr hbelow
  obtain ⟨w,hw,hl⟩ := enclosing_selected_span_word hn p G C hlow hC hzero hlast
    ss hsdis hcan hpart houtside (cycleLeftLoad f y) htotal r r hr (Or.inl rfl)
    false start finish hs hf (by
      intro a ha
      obtain ⟨hlo,hhi⟩ := hports a ha
      change r.val ≤ a.service.port.val ∧ a.service.port.val ≤ max start.val finish.val
      constructor <;> omega)
  simp only [Bool.false_eq_true,ite_false] at hl
  exact ⟨w,hw,by linarith⟩

#print axioms enclosing_window_left_route
end LRX.FiniteWindow
