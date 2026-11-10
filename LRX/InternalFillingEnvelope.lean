module

public import LRX.PrefixFillingSize
public import LRX.ComponentAreaSizeBounds
public import LRX.TwoCapWindowEnvelope
public import LRX.AreaWindowSplitSquare

@[expose] public section

/-! M4: the exact J(x) envelope for actual internal windows, using the strict
positive-boundary width rather than the coarser common area-window cap. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

def internalSquareBound (h : ℤ) (x : ℕ) : ℤ :=
  if (x : ℤ) ≤ h then (x : ℤ)^2 else h^2+((x : ℤ)-h)^2

theorem original_internal_square_envelope (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hproper : (componentSet p root).card < n) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let As := positiveSourceFamily q L
    let x := L-(prefixSourceCore q).card
    let h : ℤ := ((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-2
    0 ≤ h ∧ (x : ℤ)<2*h ∧ (∀ A ∈ As, (A.size : ℤ) ≤ h) ∧
      (As.map (fun A => (A.size : ℤ)^2)).sum ≤ internalSquareBound h x := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let As := positiveSourceFamily q L
  let x := L-(prefixSourceCore q).card
  let h : ℤ := ((n/2 : ℕ) : ℤ)+(n%2 : ℕ)-2
  have hR := (component_area_size_bounds p hmaj root hlarge hproper).1
  change 4 ≤ (prefixSourceCore q).card at hR
  have hzero : (componentSet q 0).card=L := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p (componentLeft p root) :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p (componentLeft p root)).card at hh
    rwa [← he] at hh
  have hp := prefix_internal_size_partition q (by omega) (by omega)
  rw [hzero] at hp
  change (As.map (fun A => A.size)).sum+(prefixSourceCore q).card=L at hp
  have hx : (As.map (fun A => A.size)).sum=x := by dsimp only [x]; omega
  have hxI : (As.map (fun A => (A.size : ℤ))).sum=(x : ℤ) := by
    have hh := congrArg (fun z : ℕ => (z : ℤ)) hx
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hh
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hqshort := FiniteWindow.majorized_short (canonical_lift q.symm) hqm
  have hnpar : n=2*(n/2)+n%2 := by omega
  have hh : 0 ≤ h := by dsimp only [h]; dsimp only [L] at hp; omega
  have hxcap : (x : ℤ)<2*h := by dsimp only [x,h]; dsimp only [L] at hp; omega
  have hcap : ∀ A ∈ As, (A.size : ℤ) ≤ h := by
    intro A hA
    have hspec := positive_source_family_spec q L
    obtain ⟨r,hr,hrpos⟩ := hspec.2.2.2 A hA
    have hw := positive_boundary_window_width A.window q.symm A.filling (hspec.1 A hA) hqshort r hr hrpos
    dsimp only [h]
    omega
  have hsmall := window_square_sum_le_total_square As
  rw [hxI] at hsmall
  have htwo := window_two_cap_envelope As h hh hcap (by rw [hxI]; omega)
  rw [hxI] at htwo
  refine ⟨hh,hxcap,hcap,?_⟩
  change _ ≤ internalSquareBound h x
  unfold internalSquareBound
  split_ifs
  · exact hsmall
  · exact htwo

#print axioms original_internal_square_envelope
end LRX.FiniteCuts
