module

public import LRX.TwoWindowSignedSelection
public import LRX.ActualTwoSizeCutoff

@[expose] public section

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords FiniteWindow
variable {n k : ℕ} [NeZero n]

/-- Every choice of arrows in the two local maps is tested against common
original sign offsets, not against independent local majorization. -/
def ExteriorPairSignConstraints (A B : FillingWindow n) (parity eps xp xm : ℤ) : Prop :=
  (∀ (S : Finset (Fin A.size)) (T : Finset (Fin B.size)),
    (∀ i ∈ S, 0 < displacement A.filling i) →
    (∀ i ∈ T, 0 < displacement B.filling i) →
    (xp+(S.card : ℤ)+(T.card : ℤ))*(xp+(S.card : ℤ)+(T.card : ℤ)+parity) ≤
      eps+2*((∑ i ∈ S, |displacement A.filling i|)+(∑ i ∈ T, |displacement B.filling i|))) ∧
  (∀ (S : Finset (Fin A.size)) (T : Finset (Fin B.size)),
    (∀ i ∈ S, displacement A.filling i < 0) →
    (∀ i ∈ T, displacement B.filling i < 0) →
    (xm+(S.card : ℤ)+(T.card : ℤ))*(xm+(S.card : ℤ)+(T.card : ℤ)+parity) ≤
      eps+2*((∑ i ∈ S, |displacement A.filling i|)+(∑ i ∈ T, |displacement B.filling i|)))

set_option maxHeartbeats 800000 in
/-- Extract the genuine two-window sign model from the original unpaid map. -/
theorem actual_unpaid_exterior_pair_signs (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (hpos : 1 ≤ peakExcess p hc) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let eps := canonicalEnergyDeficit p
    ∃ (A B : FillingWindow n) (xp xm : ℤ),
      suffixComponentFamily q L=[A,B] ∧
      (2 ≤ A.size ∧ A.size ≤ 5) ∧ (2 ≤ B.size ∧ B.size ≤ 5) ∧
      A.size+B.size=(∑ C ∈ nontrivialSuffixComponents q L, C.card : ℕ) ∧
      A.Matches q.symm ∧ B.Matches q.symm ∧ A.Apart B ∧
      (L ≤ A.window.offset ∧ L ≤ B.window.offset) ∧
      xp+xm=((n-p.support.card : ℕ) : ℤ)-(n%2 : ℕ) ∧
      (-eps-2 ≤ xp ∧ xp ≤ eps+2) ∧ (-eps-2 ≤ xm ∧ xm ≤ eps+2) ∧
      ExteriorPairSignConstraints A B (n%2 : ℕ) eps xp xm := by
  classical
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hb := original_unpaid_two_size_cutoff hn p hmaj hmax hc hk root hlarge ht hpos
  have hlen := (suffix_component_window_sizes q L).1
  have ht2 : (nontrivialSuffixComponents q L).card=2 := hb.1
  rw [ht2] at hlen
  obtain ⟨A,B,hAB⟩ := List.length_eq_two.mp hlen
  have hA : A ∈ suffixComponentFamily q L := by rw [hAB]; simp
  have hB : B ∈ suffixComponentFamily q L := by rw [hAB]; simp
  have hLn : L ≤ n := by simpa only [L,Fintype.card_fin] using Finset.card_le_univ (componentSet p root)
  obtain ⟨hm,hd,hboundary⟩ := suffix_component_family_spec q L hLn (component_recenter_cut p root).1
  have hsizeSum := suffix_component_family_size_sum q L
  rw [hAB] at hsizeSum
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hsizeSum
  have hAm := hm A hA
  have hBm := hm B hB
  have hApart : A.Apart B := by
    rw [hAB] at hd
    exact (List.pairwise_cons.mp hd).1 B (by simp)
  have hAsize := original_unpaid_external_window_size hn p hmaj hmax hc hk root hlarge ht hpos A hA
  have hBsize := original_unpaid_external_window_size hn p hmaj hmax hc hk root hlarge ht hpos B hB
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← component_cut_canonical_displacement]
    exact majorized_recenter hmaj _
  have hqsupport : q.support.card=p.support.card := by
    dsimp only [q]
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  have heps : canonicalEnergyDeficit q=canonicalEnergyDeficit p := by
    unfold canonicalEnergyDeficit
    dsimp only [q]
    rw [component_cut_displacement_mass]
  have hsum := signed_offsets_sum q
  rw [hqsupport] at hsum
  have hbounds := actual_sign_offset_bounds q hqm
  rw [heps] at hbounds
  refine ⟨A,B,positiveSignOffset q,negativeSignOffset q,hAB,hAsize,hBsize,hsizeSum,hAm,hBm,hApart,⟨hboundary A hA,hboundary B hB⟩,
    hsum,hbounds.1,hbounds.2,?_⟩
  constructor
  · intro S T hS hT
    have h := two_window_positive_selection A B q hqm hAm hBm hApart S T hS hT
    rwa [heps] at h
  · intro S T hS hT
    have h := two_window_negative_selection A B q hqm hAm hBm hApart S T hS hT
    rwa [heps] at h

#print axioms actual_unpaid_exterior_pair_signs
end LRX.FiniteCuts
