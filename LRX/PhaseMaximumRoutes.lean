module

public import LRX.PhaseDisconnectedWindow

@[expose] public section

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The disconnected branch of the original phase lift reaches a majorized
canonical route certificate at an actual maximum separator. Sharp payment
and alternative routes in unpaid cases remain outside this theorem. -/
theorem phase_disconnected_maximum_routes (hn : 2 ≤ n) (p : State n) (c : Fin n) (d : Fin n → ℤ)
    (hd : AffineLift.IsLift p (c : ℤ) d) (hmaj : AffineLift.Majorized d)
    (a b : Fin n) (ha : d a ≠ 0) (hb : d b ≠ 0) (hnot : ¬CycleFootprint.LoadPath d a b) :
    ∃ (q : State n) (m : ℕ) (hm : 0 < m) (hcm : (componentRoots q).card=m+1),
      AffineLift.Majorized (displacement q.symm) ∧ MaximalZeroCut q ∧
      (∀ i : Fin m, (bridgeEndpoints q hcm i).2.val-(bridgeEndpoints q hcm i).1.val ≤
        n+(outerLeft q hcm).val-(outerRight q hcm).val) ∧
      ∃ (start finish : Fin n) (w : List Letter),
        (RotationWords.rotation start)⁻¹*q*RotationWords.rotation finish=p ∧
        eval w=p ∧ CanonicalRouteCertificate q hcm start finish w := by
  obtain ⟨z0,hz0⟩ := disconnected_load_zero_port d a b hnot
  let r0 := z0+1
  let q0 := localTarget p c r0
  have hcount := phase_zero_cut_multiple_components p c d hd a b z0 ha hb hnot hz0
  let k0 := (componentRoots q0).card-1
  have hk0 : 0 < k0 := by dsimp [k0,q0,r0]; omega
  have hc0 : (componentRoots q0).card=k0+1 := by dsimp [k0,q0,r0]; omega
  have hmaj0 := phase_zero_cut_majorized c z0 hd hmaj hz0
  obtain ⟨z1,hz1,m,hm,hcm,hmax,hqm,hbridges,hroutes⟩ := maximum_cut_routes hn q0 hc0 hk0 hmaj0
  obtain ⟨w,he,hcert⟩ := hroutes (-r0) (c-r0)
  refine ⟨localTarget q0 0 (z1+1),m,hm,hcm,hqm,hmax,hbridges,
    -r0-(z1+1),(c-r0)-(z1+1),w,?_,?_,hcert⟩
  · exact (shifted_word_target q0 (z1+1) (-r0) (c-r0)).trans (phase_local_word_target p c r0)
  · exact he.trans (phase_local_word_target p c r0)

#print axioms phase_disconnected_maximum_routes
end LRX.FiniteCuts
