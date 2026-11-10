module

public import LRX.FiniteRootStar
public import LRX.ReflectedRootStar
public import LRX.ZeroGapCycleRoots
public import LRX.FiniteCycleLoads
public import LRX.CyclePart

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Removing cycles disjoint from the enclosing cycle retains that exact
cycle in the inverse target used by the service compiler. -/
theorem retained_enclosing_cycle (G C selected : State n)
    (hpart : CyclePart.IsPart selected G.symm)
    (hC : C ∈ G.cycleFactorsFinset) (hdis : C.Disjoint selected) :
    C ∈ Equiv.Perm.cycleFactorsFinset (CyclePart.remaining selected G.symm hpart).symm := by
  classical
  obtain ⟨hc,hact⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hC
  apply Equiv.Perm.mem_cycleFactorsFinset_iff.mpr
  refine ⟨hc,?_⟩
  intro i hi
  have hfix : selected i=i := (hdis i).resolve_left (Equiv.Perm.mem_support.mp hi)
  have hout : i ∈ selected.supportᶜ := by simpa using hfix
  simp only [CyclePart.remaining,PrunedLift.permutation_symm_apply,ite_eq_left hout,
    Equiv.symm_symm]
  exact hact i hi

/-- A retained target containing an enclosing cycle has a service at either
incident port of any vertex of that cycle. Its discount is at least the
load of the enclosing cycle, even when other cycles remain in the target. -/
theorem enclosing_cycle_incident_service (hn : 2 ≤ n) (R C : State n)
    (hC : C ∈ Equiv.Perm.cycleFactorsFinset R.symm)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (r port : Fin n) (hr : r ∈ C.support) (hp : port=r ∨ port+1=r) :
    ∃ a : ExactService n, a.service.port=port ∧ a.service.target=R ∧
      a.displacement=displacement R.symm ∧
      (BufferProgram.rotations a.service.word : ℤ) ≤
        (∑ i, |displacement R.symm i|)-portLoad (displacement C) port := by
  classical
  have hrR : r ∈ Equiv.Perm.support R.symm := Equiv.Perm.mem_cycleFactorsFinset_support_le hC hr
  have hmove : displacement R.symm r ≠ 0 :=
    displacement_ne_of_moved R.symm r (Equiv.Perm.mem_support.mp hrR)
  have hd : AffineLift.IsLift R 0 (displacement R.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift R.symm
  have hsame (i : Fin n) (hi : i ∈ C.support) : Equiv.Perm.SameCycle R.symm r i :=
    (ZeroGap.cycle_root_same_cycle hC hr).symm.trans (ZeroGap.cycle_root_same_cycle hC hi)
  have hstar : PrunedLift.RootStar R (displacement R.symm) r := by
    apply PrunedLift.enclosing_cycle_root_star R r 0 ⟨n-1,by omega⟩
    · exact hsame 0 hzero
    · exact hsame _ hlast
    · intro i _
      have := i.isLt
      simp only [Fin.val_zero]
      omega
  have hload : portLoad (displacement C) port ≤ portLoad (displacement R.symm) port := by
    rw [port_load_eq_twice_half,port_load_eq_twice_half]
    have hh : halfLoad C (port.val+1) ≤ halfLoad R.symm (port.val+1) := by
      rw [half_load_cycle_sum R.symm]
      exact Finset.single_le_sum (f := fun q : State n => halfLoad q (port.val+1))
        (fun _ _ => Nat.zero_le _) hC
    exact_mod_cast Nat.mul_le_mul_left 2 hh
  have hs : ∃ a : ExactService n, a.service.port=port ∧ a.service.target=R ∧
      a.displacement=displacement R.symm ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |displacement R.symm i|)-portLoad (displacement R.symm) port := by
    rcases hp with hp | hp
    · subst port
      exact root_star_exact_service hn hd (displacement_short R.symm) r hmove hstar
    · have he : port=r-1 := by linear_combination hp
      simpa only [he] using WordReflection.root_star_exact_left_service hn hd
        (displacement_short R.symm) r hmove hstar
  obtain ⟨a,ha,ht,hd',hc⟩ := hs
  exact ⟨a,ha,ht,hd',by omega⟩

#print axioms retained_enclosing_cycle
#print axioms enclosing_cycle_incident_service
end LRX.FiniteCuts
