module

public import LRX.UnitEnergyAllComponentSources
public import LRX.MatchedWindowPeakBound

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

private theorem nonunit_window_size_energy (p : State n) (A : FillingWindow n)
    (hsize : 2 ≤ A.size) (hm : A.Matches p)
    (hno : ∀ i, Contains A.window i → 2 ≤ |displacement p i|)
    (hpeak : leftPeak p n ≤ 2) :
    A.filling.support=Finset.univ ∧ 4 ≤ A.size ∧
      (∑ i, |displacement A.filling i|) ≤ 4*((A.size : ℤ)-2) := by
  have hmin (i : Fin A.size) : 2 ≤ |displacement A.filling i| := by
    rw [← matching_window_displacement A.window p A.filling hm i]
    exact hno _ (contains_embed A.window i)
  have hfull : A.filling.support=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    apply Equiv.Perm.mem_support.mpr
    intro hi
    have hh := hmin i
    simp only [displacement,hi,sub_self,abs_zero] at hh
    omega
  have hfour : 4 ≤ A.size := by
    by_contra hbad
    let i : Fin A.size := ⟨1,by omega⟩
    have hh := hmin i
    change 2 ≤ |((A.filling i).val : ℤ)-1| at hh
    have hv := (A.filling i).isLt
    have habs : |((A.filling i).val : ℤ)-1| ≤ 1 := abs_le.mpr ⟨by omega,by omega⟩
    omega
  have hlocal : leftPeak A.filling A.size ≤ 2 :=
    (matched_window_peak_le A.window p A.filling hm).trans hpeak
  have henergy := finite_energy_peak_upper A.filling 2 hlocal (by omega)
  norm_num only [Nat.cast_ofNat] at henergy
  exact ⟨hfull,hfour,henergy⟩

/-- The final unit-energy peak structure is impossible: saturated component
and packet defects remove fillings, after which peak-two energy cannot reach
one below the balanced global maximum. -/
theorem unit_energy_defect_four_peak_two_impossible (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (hf : n-p.support.card=2)
    (he : canonicalEnergyDeficit p=1) (hZ : cycleDefect p=4)
    (hfixed : isolatedVertices p=p.supportᶜ) (hU : sourceHalfPeak p=2)
    (hK : p.cycleFactorsFinset.card=(fillingCycles p).card+4) : False := by
  classical
  have hsource := unit_energy_all_component_sources hn p hmaj hc hf he hZ hfixed hK
  have hall : ∀ i ∈ p.support, i ∈ sourcePackets p := by
    intro i hi
    obtain ⟨root,hr,hpath⟩ := component_roots_cover p i ((mem_support_inverse p i).mp hi)
    exact hsource root (component_root_card_ge_two p root hr) i ((CycleFootprint.mem_component _ _ _).mpr hpath)
  have htarget : sourceTarget p=p := by
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ p.support
    · simp [sourceTarget,PrunedLift.permutation_apply,hall i hi]
    · have hfix : p i=i := Equiv.Perm.notMem_support.mp hi
      simp [sourceTarget,PrunedLift.permutation_apply,hfix]
  have hpeak : leftPeak p.symm n ≤ 2 := by
    change leftPeak (sourceTarget p).symm n=2 at hU
    rw [htarget] at hU
    omega
  have hgeom := unit_energy_defect_four_component_windows p hmaj hc hf he hZ hfixed
  obtain ⟨a,b,A,B,_,hroots,hAs,hBs,hAw,hBw,hapart,hAm,hBm,hprod,_,_⟩ := hgeom
  have ha : a ∈ componentRoots p := by rw [hroots]; simp
  have hb : b ∈ componentRoots p := by rw [hroots]; simp
  have hac := component_root_card_ge_two p a ha
  have hbc := component_root_card_ge_two p b hb
  have hno (root : Fin n) (hcard : 2 ≤ (componentSet p root).card)
      (i : Fin n) (hi : i ∈ componentSet p root) : 2 ≤ |displacement p.symm i| := by
    have hs := hsource root hcard i hi
    have hmove := ((mem_source_packets p i).mp hs).1
    have hnon : displacement p.symm i ≠ 0 := by
      intro hz
      apply hmove
      apply Fin.ext
      unfold displacement at hz
      omega
    have hunit := unit_energy_two_fixed_no_unit_arrow p hmaj hf he i
    have hapos := abs_pos.mpr hnon
    omega
  obtain ⟨hAfull,hAfour,hAE⟩ := nonunit_window_size_energy p.symm A (by omega) hAm
    (fun i hi => hno a hac i ((hAw i).mp hi)) hpeak
  obtain ⟨hBfull,hBfour,hBE⟩ := nonunit_window_size_energy p.symm B (by omega) hBm
    (fun i hi => hno b hbc i ((hBw i).mp hi)) hpeak
  let u := permutation A.window A.filling
  let v := permutation B.window B.filling
  have hdis : u.Disjoint v := by
    intro i
    by_cases hi : Contains A.window i
    · right
      exact permutation_outside B.window B.filling i (hapart i hi)
    · left
      exact permutation_outside A.window A.filling i hi
  have hsupport : p.support.card=A.size+B.size := by
    have hh := hdis.card_support_mul
    rw [permutation_support_card,permutation_support_card,hAfull,hBfull,Finset.card_univ,Finset.card_univ,Fintype.card_fin,Fintype.card_fin] at hh
    change (permutation A.window A.filling*permutation B.window B.filling).support.card=_ at hh
    rw [← hprod] at hh
    have hps : Equiv.Perm.support p.symm=p.support := Equiv.Perm.support_inv p
    rw [hps] at hh
    exact hh
  have hmass : (∑ i, |displacement p.symm i|)=
      (∑ i, |displacement A.filling i|)+(∑ i, |displacement B.filling i|) := by
    rw [hprod]
    change (∑ i, |displacement (u*v) i|)=_
    simp_rw [abs_displacement_mul u v hdis]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (displacement_mass A.window A.filling) (displacement_mass B.window B.filling)
  have hn4 := unit_energy_reserve_size_mod_four p he
  have hsize : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by omega
  have htotal : (A.size : ℤ)+B.size=(n : ℤ)-2 := by omega
  have hsq := sq_nonneg (((n/2 : ℕ) : ℤ)-4)
  unfold canonicalEnergyDeficit at he
  rw [hmass] at he
  nlinarith

#print axioms unit_energy_defect_four_peak_two_impossible
end LRX.FiniteCuts
