import LRX.ZeroCutComponents

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- A maximal actual separator is chosen before building the complete route
certificate. Every internal separator is at most the outside width. -/
theorem maximum_cut_routes (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (hmaj : AffineLift.Majorized (displacement p.symm)) :
    ∃ z : Fin n, portLoad (displacement p.symm) z=0 ∧
      ∃ (m : ℕ) (hm : 0 < m) (hcm : (componentRoots (localTarget p 0 (z+1))).card=m+1),
        MaximalZeroCut (localTarget p 0 (z+1)) ∧
        AffineLift.Majorized (displacement (localTarget p 0 (z+1)).symm) ∧
        (∀ i : Fin m, (bridgeEndpoints (localTarget p 0 (z+1)) hcm i).2.val-
          (bridgeEndpoints (localTarget p 0 (z+1)) hcm i).1.val ≤
          n+(outerLeft (localTarget p 0 (z+1)) hcm).val-(outerRight (localTarget p 0 (z+1)) hcm).val) ∧
        (∀ start finish : Fin n, ∃ w : List Letter,
          eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
          CanonicalRouteCertificate (localTarget p 0 (z+1)) hcm (start-(z+1)) (finish-(z+1)) w) := by
  obtain ⟨z,hz,hmax⟩ := exists_maximum_zero_cut p
  let q := localTarget p 0 (z+1)
  have hmcount := zero_cut_multiple_components p hc hk z hz
  let m := (componentRoots q).card-1
  have hm : 0 < m := by dsimp [m,q]; omega
  have hcm : (componentRoots q).card=m+1 := by dsimp [m,q]; omega
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hqm := phase_zero_cut_majorized 0 z hd hmaj hz
  refine ⟨z,hz,m,hm,hcm,hmax,hqm,?_,?_⟩
  · intro i
    have hh := maximal_cut_bridge_width q hmax hcm i
    rw [external_width_eq_outer hn q hcm hm] at hh
    exact hh
  · intro start finish
    obtain ⟨w,he,hcert⟩ := canonical_multi_component_routes hn q hcm hm (start-(z+1)) (finish-(z+1))
    refine ⟨w,?_,hcert⟩
    exact he.trans (shifted_word_target p (z+1) start finish)

#print axioms maximum_cut_routes
end LRX.FiniteCuts
