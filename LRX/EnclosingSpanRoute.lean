import LRX.EnclosingBoundaryRoute
import LRX.SpanRankTransfer

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Either boundary turn, serving the entire span up to the larger cursor
or from the smaller cursor. Both cursor orders use the same retained-root
family and preserve the lower map's inversion count. -/
theorem enclosing_selected_span_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p G.symm)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hpart : CyclePart.IsPart (ss.map (fun a => a.service.target)).prod G.symm)
    (houtside : C.Disjoint (ss.map (fun a => a.service.target)).prod)
    (discount : ℤ)
    (hprice : (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum ≤
      (ss.map (fun a => ∑ i, |a.displacement i|)).sum-discount)
    (r boundary : Fin n) (hr : r ∈ C.support)
    (hp : boundary=r ∨ boundary+1=r)
    (right : Bool) (start finish : Fin n)
    (hs : if right then start.val ≤ boundary.val else boundary.val ≤ start.val)
    (hf : if right then finish.val ≤ boundary.val else boundary.val ≤ finish.val)
    (hports : ∀ a ∈ ss,
      (if right then min start.val finish.val else boundary.val) ≤ a.service.port.val ∧
      a.service.port.val ≤ (if right then boundary.val else max start.val finish.val)) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-
        portLoad (displacement C) boundary-discount+
        (if right then 2*(boundary.val : ℤ)-(start.val : ℤ)-(finish.val : ℤ)
          else (start.val : ℤ)+(finish.val : ℤ)-2*(boundary.val : ℤ)) := by
  let saving : ExactService n → ℤ := fun a =>
    (∑ i, |a.displacement i|)-(BufferProgram.rotations a.service.word : ℤ)
  have hsave : discount ≤ (ss.map saving).sum := by
    dsimp only [saving]
    rw [service_savings_sum]
    linarith
  obtain ⟨a,ha,hcanonical,hpair,hprod,hrot⟩ := enclosing_selected_family hn G C
    hC hzero hlast ss hdis hcan hpart houtside saving
    (fun a _ => by dsimp [saving]; omega) r boundary hr hp
  have hlow : FiniteRankOrder.Below p (((a::ss).map (fun b => b.service.target)).prod) := by
    rw [hprod]
    exact hbelow
  cases right with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at hs hf hports ⊢
    obtain ⟨w,hw,hl⟩ := left_span_rank_transfer hn p boundary start finish hs hf
      (a::ss) hpair hcanonical hlow (by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [ha]; omega
        · exact hports b hb)
    exact ⟨w,hw,by linarith⟩
  | true =>
    simp only [ite_true] at hs hf hports ⊢
    obtain ⟨w,hw,hl⟩ := right_span_rank_transfer hn p boundary start finish hs hf
      (a::ss) hpair hcanonical hlow (by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [ha]; omega
        · exact hports b hb)
    exact ⟨w,hw,by linarith⟩

#print axioms enclosing_selected_span_word
end LRX.FiniteCuts
