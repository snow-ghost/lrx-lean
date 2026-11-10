module

public import LRX.OriginalEnvelopeFilters

@[expose] public section

/-! The remaining two scalar envelope transitions used by the research search:
exact-energy density and C9 with the piecewise J(x) bound. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

/-- Keep the exact selected energy in the core-density decomposition. -/
theorem prefix_exact_energy_density (p : State n)
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n) :
    let L := (componentSet p 0).card
    let U : ℤ := sourceHalfPeak p
    2*(∑ i, |displacement p.symm i|) ≤ 4*U*((L : ℤ)-U)+
      2*((areaWindowFamily p L).map (fun A => ∑ i, |displacement A.filling i|)).sum := by
  have hsize : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hwidth := large_component_source_peak_capacity p 0 hlarge
  have hcore := prefix_core_energy_bound p hwidth
  have hsplit := area_core_energy_partition p hsize hproper
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val<(componentSet p 0).card ↔ i.val<(componentSet p 0).card := by
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  obtain ⟨hm,ha⟩ := area_window_family_spec p _ hproper.le hcut
  rw [window_family_selected_mass _ _ hm ha] at hsplit
  dsimp only at hcore ⊢
  linarith only [hcore,hsplit]

/-- The direct energy rejection used before the x-loop in the scalar search. -/
theorem original_unpaid_energy_density_filter (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
    let a := (singletonSuffixComponents q L).card
    let f := n-p.support.card
    let T := scalarFillingBudget p root
    let U : ℤ := sourceHalfPeak p
    2*(∑ i, |displacement p.symm i|)-4*U*((L : ℤ)-U) ≤
      exteriorSquareBound t v-(v%2 : ℕ)+4*T*(T+if a<f then 1 else 0) := by
  let q := localTarget p 0 (componentLeft p root)
  have hzero : (componentSet q 0).card=(componentSet p root).card := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← he] at hh
  have hproper := component_card_lt_of_multiple_roots p (by omega) root
  have hd := prefix_exact_energy_density q (by omega) (by omega)
  dsimp only at hd
  rw [hzero] at hd
  dsimp only [q] at hd
  rw [component_cut_source_half_peak,component_cut_displacement_mass] at hd
  simp only [areaWindowFamily,List.map_append,List.sum_append] at hd
  have hi := original_unpaid_prefix_energy_indicator hn p hmaj hmax hc hk root hlarge hpos
  have he := (suffix_component_square_energy_bounds q (componentSet p root).card).2
  dsimp only [q] at he
  dsimp only at hi he ⊢
  linarith only [hd,hi,he]

/-- C9 with J(x), the final density check inside the scalar x-loop. -/
theorem original_unpaid_j_area_filter (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let x := L-(prefixSourceCore q).card
    let t := (nontrivialSuffixComponents q L).card
    let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
    let a := (singletonSuffixComponents q L).card
    let f := n-p.support.card
    let eps : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    let h : ℤ := ((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-2
    ((x : ℤ)+(v : ℤ))^2-2*(internalSquareBound h x+exteriorSquareBound t v)+
      2*((x : ℤ)+(v : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
        2*(2*eps+(n%2 : ℕ)-(f : ℤ)) := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let x := L-(prefixSourceCore q).card
  let t := (nontrivialSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let a := (singletonSuffixComponents q L).card
  let f := n-p.support.card
  let eps : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  let h : ℤ := ((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-2
  let Si := ((positiveSourceFamily q L).map (fun A => (A.size : ℤ)^2)).sum
  let Se := ((suffixComponentFamily q L).map (fun A => (A.size : ℤ)^2)).sum
  let V := ((areaWindowFamily q L).map (fun A => A.size)).sum
  have hx := (original_unpaid_filling_scalar_filters hn p hmaj hmax hc hk root hlarge hpos).1
  change ((positiveSourceFamily q L).map (fun A => A.size)).sum=x at hx
  have hv := suffix_component_family_size_sum q L
  change ((suffixComponentFamily q L).map (fun A => A.size)).sum=v at hv
  have hV : (V : ℤ)=(x : ℤ)+(v : ℤ) := by
    have he : V=x+v := by simp only [V,areaWindowFamily,List.map_append,List.sum_append,hx,hv]
    exact_mod_cast he
  have hproper := component_card_lt_of_multiple_roots p (by omega) root
  have hJ := (original_internal_square_envelope p hmaj root hlarge hproper).2.2.2
  change Si ≤ internalSquareBound h x at hJ
  have hE := (suffix_component_square_energy_bounds q L).1
  change Se ≤ exteriorSquareBound t v at hE
  have hs : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hm : (∑ i, |displacement q.symm i|)=(∑ i, |displacement p.symm i|) :=
    component_cut_displacement_mass p root
  have ha := component_area_deficit p hmaj root (by omega) hproper
  dsimp only at ha
  change (V : ℤ)^2-2*((areaWindowFamily q L).map (fun A => (A.size : ℤ)^2)).sum+
    2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
    2*(2*(((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement q.symm i|))+
      (n%2 : ℕ)-((n-q.support.card : ℕ) : ℤ)) at ha
  rw [hs,hm] at ha
  simp only [areaWindowFamily,List.map_append,List.sum_append] at ha
  change (V : ℤ)^2-2*(Si+Se)+2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
    2*(2*eps+(n%2 : ℕ)-(f : ℤ)) at ha
  rw [hV] at ha
  change ((x : ℤ)+(v : ℤ))^2-2*(internalSquareBound h x+exteriorSquareBound t v)+
    2*((x : ℤ)+(v : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
      2*(2*eps+(n%2 : ℕ)-(f : ℤ))
  linarith only [ha,hJ,hE]

#print axioms original_unpaid_energy_density_filter
#print axioms original_unpaid_j_area_filter
end LRX.FiniteCuts
