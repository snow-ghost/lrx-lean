module

public import LRX.EnclosingSelectedFamily
public import LRX.EnclosingCycleIncidentService
public import LRX.WeightedPacketAssembly
public import LRX.CircularRankTransfer

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- A selected arc services any disjoint family outside an enclosing cycle.
Unselected cycles are absorbed into the root service before rank transfer. -/
theorem enclosing_selected_arc_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p G.symm)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hpart : CyclePart.IsPart (ss.map (fun a => a.service.target)).prod G.symm)
    (houtside : C.Disjoint (ss.map (fun a => a.service.target)).prod)
    (saving : ExactService n → ℤ)
    (hprice : ∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ) ≤
      (∑ i, |a.displacement i|)-saving a)
    (r port : Fin n) (hr : r ∈ C.support) (hp : port=r ∨ port+1=r)
    (dir : Bool) (start finish : Fin n)
    (hrootport : (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val)
    (hports : ∀ a ∈ ss, (arcCoordinate dir start a.service.port).val ≤
      (arcCoordinate dir start finish).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-
        portLoad (displacement C) port-(ss.map saving).sum+
        ((arcCoordinate dir start finish).val : ℤ) := by
  obtain ⟨a,ha,hcanonical,hpair,hprod,hrot⟩ := enclosing_selected_family hn G C
    hC hzero hlast ss hdis hcan hpart houtside saving hprice r port hr hp
  obtain ⟨w,hw,hlen⟩ := circular_rank_transfer_route hn p dir start finish
    (a::ss) hpair hcanonical (by rw [hprod]; exact hbelow) (by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa only [ha] using hrootport
      · exact hports b hb)
  have hlen' : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
      (((a::ss).map (fun b => BufferProgram.rotations b.service.word)).sum : ℤ)+
      ((arcCoordinate dir start finish).val : ℤ) := by exact_mod_cast hlen
  exact ⟨w,hw,by linarith⟩

#print axioms enclosing_selected_arc_word
end LRX.FiniteCuts
