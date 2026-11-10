import LRX.ExternalFillingEnvelope
import LRX.WindowFamilyExactEnergy
import LRX.OriginalFillingScalarFilters
import LRX.InternalFillingEnvelope

/-! M4: joint scalar filters from actual internal/external windows, C9/C10,
and exact selected energy, all in the original unpaid-map coordinates. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

set_option maxHeartbeats 800000 in
theorem original_unpaid_envelope_filters (hn : 2 ≤ n) (p : State n)
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
    let U : ℤ := sourceHalfPeak p
    let T := scalarFillingBudget p root
    let E2 := exteriorSquareBound t v
    2*(∑ i, |displacement p.symm i|)-4*U*((L : ℤ)-U) ≤ (x : ℤ)+4*T^2+2*T+E2 ∧
    ((x : ℤ)+(v : ℤ)+(a : ℤ)-1)^2+2*(v : ℤ)-1+(n%2 : ℕ)-2*(4*T^2+2*T+E2) ≤
      2*(2*eps+(n%2 : ℕ)-(f : ℤ)) ∧
    ((x : ℤ)+(v : ℤ)+(a : ℤ))^2 ≤ 4*eps+(n%2 : ℕ)+
      8*T*(T+if a<f then 1 else 0)+2*(E2-(v%2 : ℕ)) := by
  classical
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let x := L-(prefixSourceCore q).card
  let t := (nontrivialSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let a := (singletonSuffixComponents q L).card
  let f := n-p.support.card
  let eps : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  let U : ℤ := sourceHalfPeak p
  let T := scalarFillingBudget p root
  let E2 := exteriorSquareBound t v
  let Si := ((positiveSourceFamily q L).map (fun A => (A.size : ℤ)^2)).sum
  let Se := ((suffixComponentFamily q L).map (fun A => (A.size : ℤ)^2)).sum
  let Ei := ((positiveSourceFamily q L).map (fun A => ∑ i, |displacement A.filling i|)).sum
  let Ee := ((suffixComponentFamily q L).map (fun A => ∑ i, |displacement A.filling i|)).sum
  let V := ((areaWindowFamily q L).map (fun A => A.size)).sum
  obtain ⟨hx,_,_,hiE,hiS⟩ := original_unpaid_filling_scalar_filters hn p hmaj hmax hc hk root hlarge hpos
  change ((positiveSourceFamily q L).map (fun A => A.size)).sum=x at hx
  change Ei ≤ 2*T*(T+if a<f then 1 else 0) at hiE
  change Si ≤ 4*T^2+2*T+(x : ℤ) at hiS
  obtain ⟨heS,heE⟩ := suffix_component_square_energy_bounds q L
  change Se ≤ E2 at heS
  change 2*Ee ≤ E2-(v%2 : ℕ) at heE
  have hv := suffix_component_family_size_sum q L
  change ((suffixComponentFamily q L).map (fun A => A.size)).sum=v at hv
  have hV : (V : ℤ)=(x : ℤ)+(v : ℤ) := by
    have he : V=x+v := by simp only [V,areaWindowFamily,List.map_append,List.sum_append,hx,hv]
    exact_mod_cast he
  have hproper : L<n := component_card_lt_of_multiple_roots p (by omega) root
  have hzero : (componentSet q 0).card=L := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← he] at hh
  have hqsupport : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hd := component_density_bound p root hlarge hproper
  dsimp only at hd
  rw [component_cut_source_half_peak,component_cut_displacement_mass] at hd
  simp only [areaWindowFamily,List.map_append,List.sum_append] at hd
  change 2*(∑ i, |displacement p.symm i|) ≤ 4*U*((L : ℤ)-U)+(Si+Se) at hd
  have ha := component_area_deficit p hmaj root (by omega) hproper
  dsimp only at ha
  change (V : ℤ)^2-2*((areaWindowFamily q L).map (fun A => (A.size : ℤ)^2)).sum+
    2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
    2*(2*(((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement q.symm i|))+
      (n%2 : ℕ)-((n-q.support.card : ℕ) : ℤ)) at ha
  rw [hqsupport] at ha
  have hmass : (∑ i, |displacement q.symm i|)=(∑ i, |displacement p.symm i|) :=
    component_cut_displacement_mass p root
  rw [hmass] at ha
  simp only [areaWindowFamily,List.map_append,List.sum_append] at ha
  change (V : ℤ)^2-2*(Si+Se)+2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
    2*(2*eps+(n%2 : ℕ)-(f : ℤ)) at ha
  rw [hV] at ha
  have hcut : ∀ i : Fin n, (q i).val<L ↔ i.val<L := (component_recenter_cut p root).1
  obtain ⟨hm,hapart⟩ := area_window_family_spec q L hproper.le hcut
  have henergy := window_family_exact_energy_deficit (areaWindowFamily q L) q.symm hqm hm hapart
  have hfixed := area_fixed_complement_card q (by omega) (by omega)
  rw [hzero] at hfixed
  dsimp only at henergy
  rw [hfixed,hmass] at henergy
  change ((V : ℤ)+(a : ℤ))^2 ≤
    4*(eps+((areaWindowFamily q L).map (fun A => ∑ i, |displacement A.filling i|)).sum)+(n%2 : ℕ) at henergy
  simp only [areaWindowFamily,List.map_append,List.sum_append] at henergy
  change ((V : ℤ)+(a : ℤ))^2 ≤ 4*(eps+(Ei+Ee))+(n%2 : ℕ) at henergy
  rw [hV] at henergy
  change 2*(∑ i, |displacement p.symm i|)-4*U*((L : ℤ)-U) ≤ (x : ℤ)+4*T^2+2*T+E2 ∧
    ((x : ℤ)+(v : ℤ)+(a : ℤ)-1)^2+2*(v : ℤ)-1+(n%2 : ℕ)-2*(4*T^2+2*T+E2) ≤
      2*(2*eps+(n%2 : ℕ)-(f : ℤ)) ∧
    ((x : ℤ)+(v : ℤ)+(a : ℤ))^2 ≤ 4*eps+(n%2 : ℕ)+
      8*T*(T+if a<f then 1 else 0)+2*(E2-(v%2 : ℕ))
  exact ⟨by linarith,by nlinarith,by nlinarith⟩

/-- The second density envelope retains the exact internal J(x) bound. -/
theorem original_j_density_filter (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hproper : (componentSet p root).card < n) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let x := L-(prefixSourceCore q).card
    let t := (nontrivialSuffixComponents q L).card
    let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
    let h : ℤ := ((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-2
    let U : ℤ := sourceHalfPeak p
    2*(∑ i, |displacement p.symm i|)-4*U*((L : ℤ)-U) ≤
      internalSquareBound h x+exteriorSquareBound t v := by
  have hJ := (original_internal_square_envelope p hmaj root hlarge hproper).2.2.2
  have hE := (suffix_component_square_energy_bounds
    (localTarget p 0 (componentLeft p root)) (componentSet p root).card).1
  have hd := component_density_bound p root hlarge hproper
  dsimp only at hJ hE hd ⊢
  rw [component_cut_source_half_peak,component_cut_displacement_mass] at hd
  simp only [areaWindowFamily,List.map_append,List.sum_append] at hd
  linarith only [hd,hJ,hE]

#print axioms original_unpaid_envelope_filters
#print axioms original_j_density_filter
end LRX.FiniteCuts
