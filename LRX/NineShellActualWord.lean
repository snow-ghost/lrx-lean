module

public import LRX.NineShellCertificate
public import LRX.NineShellShape
public import LRX.TwoPrunedPartsDefect

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators

private theorem exterior_code_checked : ∀ c : PermCode 3,
    (decode (n := 3) c).support.card=2 →
    (∑ i, |displacement (decode (n := 3) c) i|)=4 → decode c=Fin.revPerm := by
  decide +kernel

/-- The finite certificate is applied to the restriction of the actual
permutation, not to a hypothetical or separately supplied six-point model. -/
theorem prefix_nine_shell_actual_word (p : State 9)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (hz : cycleDefect p=0)
    (he : canonicalEnergyDeficit p=0) (hfix : 9-p.support.card=1)
    (hL : (componentSet p 0).card=6) (hR : (prefixSourceCore p).card=6) (hH : shellH p=2)
    (start finish : Fin 9) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ Nat.choose 9 2 := by
  classical
  let W := NineShellCertificate.prefixWindow
  let V := NineShellCertificate.exterior
  have hc : 2 ≤ (componentSet p 0).card := by omega
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin 9) : (p.symm i).val < 6 ↔ i.val < 6 := by
    have hh := CycleFootprint.component_invariant hd 0 (p.symm i)
    simp only [Equiv.apply_symm_apply] at hh
    change (i ∈ componentSet p 0 ↔ p.symm i ∈ componentSet p 0) at hh
    rw [zero_component_prefix,zero_component_prefix,hL] at hh
    exact hh.symm
  obtain ⟨f,hf⟩ := exists_restriction_of_inverse_closed W p (by
    intro i hi
    change 0 ≤ (p.symm i).val ∧ (p.symm i).val < 6
    have hi' : i.val < 6 := hi.2
    exact ⟨Nat.zero_le _,(hcut i).mpr hi'⟩)
  obtain ⟨g,hg⟩ := exists_restriction_of_inverse_closed V p (by
    intro i hi
    change 6 ≤ (p.symm i).val ∧ (p.symm i).val < 9
    have hi' : 6 ≤ i.val := hi.1
    have hh := hcut i
    have hp := (p.symm i).isLt
    exact ⟨by omega,hp⟩)
  let A : FillingWindow 9 := ⟨6,W,f⟩
  let B : FillingWindow 9 := ⟨3,V,g⟩
  have hSC : prefixSourceCore p=componentSet p 0 := Finset.eq_of_subset_of_card_le
    (by intro i hi; exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2) (by omega)
  have hWC : windowPositions W=componentSet p 0 := by
    ext i
    simp only [windowPositions,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [zero_component_prefix,hL]
    change (0 ≤ i.val ∧ i.val < 6) ↔ i.val < 6
    omega
  have hWS : windowPositions W=prefixSourceCore p := hWC.trans hSC.symm
  have hfull : f.support=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    apply Equiv.Perm.mem_support.mpr
    intro hfixj
    have his : embed W j ∈ prefixSourceCore p := by
      rw [← hWS]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,contains_embed W j⟩
    have hmove := ((mem_source_packets p _).mp (Finset.mem_filter.mp his).1).1
    have hh := hf j
    rw [hfixj] at hh
    exact hmove hh
  have hmassCore : (∑ i ∈ prefixSourceCore p, |displacement p.symm i|)=16 := by
    have hh := hH
    dsimp only [shellH] at hh
    rw [hR] at hh
    norm_num at hh
    omega
  have hfmass : (∑ i, |displacement f i|)=16 := by
    calc
      _ = ∑ j, |displacement p.symm (embed W j)| := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg abs (matching_window_displacement W p.symm f hf j).symm
      _ = ∑ i ∈ windowPositions W, |displacement p.symm i| := (sum_window_positions W (fun i : Fin 9 => |displacement p.symm i|)).symm
      _ = 16 := by rw [hWS]; exact hmassCore
  let Q := canonicalRootPacket p 0
  have hpruned : PrunedLift.permutation p (windowPositions W)
      (matched_window_positions_invariant p A hf)=Q := by
    apply Equiv.ext
    intro i
    simp only [Q,canonicalRootPacket,PrunedLift.permutation_apply,prefix_root_core_eq p hm hc,hWS]
  have hInv := matched_window_pruned_inverse p A hf
  rw [hpruned] at hInv
  have hsource0 := (prefix_component_source_ends p hc (component_card_lt_of_multiple_roots p hm 0)).1
  have hr0 : (0 : Fin 9) ∈ p.support := (mem_support_inverse p 0).mpr ((mem_source_packets p 0).mp hsource0).1
  have hcy : Q.IsCycle := (canonical_root_packet_shallow_of_zero_defect p hmaj 0 hr0 hz).1
  have hQCount : (Equiv.Perm.cycleFactorsFinset Q.symm).card=1 := by
    have hh : Equiv.Perm.cycleFactorsFinset Q.symm={Q.symm} := hcy.inv.cycleFactorsFinset_eq_singleton
    rw [hh,Finset.card_singleton]
  have hFCount := (congrArg (fun q : State 9 => q.cycleFactorsFinset.card) hInv).symm
  change (permutation W f).cycleFactorsFinset.card=(Equiv.Perm.cycleFactorsFinset Q.symm).card at hFCount
  rw [permutation_cycle_count,hQCount] at hFCount
  have hQZ : cycleDefect Q=0 := zero_defect_pruned_factor p
    (PrunedLift.core p (displacement p.symm) 0) (PrunedLift.core_invariant p (displacement p.symm) 0) hz
  have hFZ := matched_window_pruned_defect p A hf
  rw [hpruned,hQZ] at hFZ
  change 0=cycleDefect f at hFZ
  unfold cycleDefect at hFZ
  rw [hfmass,hfull,Finset.card_univ,Fintype.card_fin,hFCount] at hFZ
  have hFI : inversionNumber f=11 := by omega
  have hapart : A.Apart B := by
    intro i hi hj
    change 0 ≤ i.val ∧ i.val < 6 at hi
    change 6 ≤ i.val ∧ i.val < 9 at hj
    omega
  have hprod := two_matched_windows_product p.symm A B hapart hf hg (by
    intro i _
    by_cases hi : i.val < 6
    · left; change 0 ≤ i.val ∧ i.val < 6; exact ⟨Nat.zero_le _,hi⟩
    · right; change 6 ≤ i.val ∧ i.val < 9; have := i.isLt; exact ⟨by omega,this⟩)
  let u := permutation W f
  let v := permutation V g
  have hdis : u.Disjoint v := by
    intro i
    by_cases hi : Contains W i
    · right; exact permutation_outside V g i (hapart i hi)
    · left; exact permutation_outside W f i hi
  have hsupport := hdis.card_support_mul
  rw [permutation_support_card,permutation_support_card,hfull,Finset.card_univ,Fintype.card_fin] at hsupport
  change (permutation W f*permutation V g).support.card=6+g.support.card at hsupport
  change p.symm=permutation W f*permutation V g at hprod
  rw [← hprod] at hsupport
  have hps : Equiv.Perm.support p.symm=p.support := Equiv.Perm.support_inv p
  rw [hps] at hsupport
  have hgsupport : g.support.card=2 := by omega
  have hmass : (∑ i, |displacement p.symm i|)=(∑ i, |displacement f i|)+(∑ i, |displacement g i|) := by
    rw [hprod]
    change (∑ i, |displacement (u*v) i|)=_
    simp_rw [abs_displacement_mul u v hdis]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (displacement_mass W f) (displacement_mass V g)
  have hpmass : (∑ i, |displacement p.symm i|)=20 := by
    norm_num [canonicalEnergyDeficit] at he
    omega
  have hgmass : (∑ i, |displacement g i|)=4 := by omega
  have hgrev : g=Fin.revPerm := by
    have hh := exterior_code_checked (encode g) (by simpa only [decode_encode] using hgsupport)
      (by simpa only [decode_encode] using hgmass)
    simpa only [decode_encode] using hh
  rw [hgrev] at hprod
  change p⁻¹=permutation W f*permutation V Fin.revPerm at hprod
  have htarget : p=NineShellCertificate.target f := by
    have hh := congrArg (fun q : State 9 => q⁻¹) hprod
    simpa only [inv_inv,NineShellCertificate.target,W,V] using hh
  obtain ⟨w,hw,hl⟩ := NineShellCertificate.sharp_word f ⟨hfull,hfmass,hFI⟩ start finish
  refine ⟨w,?_,?_⟩
  · rw [htarget]; exact hw
  · simpa [Nat.choose_two_right] using hl

#print axioms prefix_nine_shell_actual_word
end LRX.FiniteCuts
