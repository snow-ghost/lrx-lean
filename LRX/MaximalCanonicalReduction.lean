import LRX.PhaseMaximumRoutes
import LRX.ConnectedLoadSharpWord
import LRX.UpperReduction

namespace LRX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords

/-- Remaining sharp routing obligation on majorized canonical finite maps at
maximum zero cuts. A proof may replace the baseline route certificate by a
special route in any case where the baseline estimate is not paid. -/
def MaximalCanonicalSharpRouting : Prop :=
  ∀ (n : ℕ) [NeZero n], 4 ≤ n → ∀ (q : State n) (m : ℕ),
    0 < m → (FiniteCuts.componentRoots q).card=m+1 →
    AffineLift.Majorized (FiniteCuts.displacement q.symm) → FiniteCuts.MaximalZeroCut q →
    ∀ start finish : Fin n, ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*q*RotationWords.rotation finish ∧ w.length ≤ n.choose 2

theorem nonzero_routing_of_maximal_canonical (pay : MaximalCanonicalSharpRouting) : NonzeroLiftRouting := by
  intro n _ hn p c d hd hmaj hnonzero
  classical
  obtain ⟨a,ha⟩ := hnonzero
  let q0 := localTarget p c 0
  have hd0 : localDisplacement d 0=d := by funext i; simp [localDisplacement]
  have hphys : AffineLift.IsLift q0 0 d := by simpa only [hd0] using recentered_lift c 0 hd
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have hh := FiniteWindow.majorized_short hphys hmaj i
    have := abs_nonneg (d i)
    omega
  have ham : q0.symm a ≠ a := by
    intro hh
    exact ha (BufferProgram.fixed_short_displacement hphys a (hshort a) hh)
  by_cases hconn : ∀ b : CycleFootprint.Active q0, CycleFootprint.LoadPath d a b.val
  · obtain ⟨w,he,hl⟩ := CycleFootprint.connected_load_sharp_word hn hphys hmaj ⟨a,ham⟩ hconn 0 c
    refine ⟨w,?_,hl⟩
    simpa [q0,localTarget,RotationWords.rotation,mul_assoc] using he
  · push_neg at hconn
    obtain ⟨b,hnot⟩ := hconn
    have hb : d b.val ≠ 0 := by
      intro hz
      have hh := AffineLift.lift_residue hphys b.val
      simp only [hz,Int.cast_zero,add_zero] at hh
      exact b.property hh.symm
    obtain ⟨q,m,hm,hcm,hqm,hmax,_,s,t,_,htarget,_,_⟩ :=
      FiniteCuts.phase_disconnected_maximum_routes (by omega) p c d hd hmaj a b.val ha hb hnot
    obtain ⟨w,he,hl⟩ := pay n hn q m hm hcm hqm hmax s t
    exact ⟨w,he.trans htarget,hl⟩

#print axioms nonzero_routing_of_maximal_canonical
end LRX
