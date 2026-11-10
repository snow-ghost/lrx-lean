import LRX.PrefixRankGaps
import LRX.ActualShallowExteriorDeficit

namespace LRX.FiniteCuts
open ContractionBlocks.System
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Every internal rank gap of the real zero-defect source packet is an
actual selected filling and obeys the geometric deficit bound with its
physical width. All hole and threshold parameters are derived internally. -/
theorem prefix_zero_defect_internal_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0) :
    ∃ (r : ℕ) (emb : Fin (r+1) ↪o Fin n),
      r+1=(prefixSourceCore p).card ∧
      (∀ i, i ∈ prefixSourceCore p ↔ ∃ j, emb j=i) ∧
      ∀ gap : Fin r,
        FiniteGaps.next (sourcePackets p) (emb gap.castSucc)=(emb gap.succ).val ∧
        emb gap.castSucc ∈ positiveSourceGapStarts p (componentSet p 0).card ∧
        (let b := (emb gap.succ).val-(emb gap.castSucc).val-1
         let R := (prefixSourceCore p).card
         let l := R/2
         let T : ℤ := max 0 (2*(b : ℤ)-((n-R : ℕ) : ℤ)-(R%2 : ℕ))
         T^2-T%2+8*(T/2)*((n-(componentSet p 0).card : ℕ) : ℤ) ≤
           4*((l : ℤ)*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|))) := by
  classical
  obtain ⟨r,P,emb,hP,hsh,hfull,hcard,hδ,hmono,he0,heR,hwide,hmass,himage⟩ :=
    prefix_zero_defect_physical_model p hmaj hm hlarge hz
  refine ⟨r,emb,hcard,himage,?_⟩
  intro gap
  have hsel := prefix_rank_gap_selected p emb himage gap
  refine ⟨hsel.1,hsel.2,?_⟩
  let f := fun i => (emb i : ℤ)
  let L := (componentSet p 0).card
  let R := (prefixSourceCore p).card
  let l := R/2
  let eta := R%2
  let s := n-R
  let outside := n-L
  let b := (emb gap.succ).val-(emb gap.castSucc).val-1
  let c := L-R-b
  let T : ℤ := 2*(b : ℤ)-(s : ℤ)-(eta : ℤ)
  have hRL : R ≤ L := by
    apply Finset.card_le_card
    intro i hi
    exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2
  have hLn : L ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ (componentSet p 0)
  have hR : r+1=R := hcard
  have hsplit : R=2*l+eta := by dsimp only [l,eta]; omega
  have hsize : n=r+1+s := by dsimp only [s]; omega
  have hpar : eta ≤ 1 := by dsimp only [eta]; omega
  have hgapMono (j : Fin r) : (emb j.castSucc).val < (emb j.succ).val :=
    emb.strictMono (by change j.val < j.val+1; omega)
  have hnon (j : Fin r) : 0 ≤ f j.succ-f j.castSucc-1 := by
    have hh := hgapMono j
    dsimp only [f]
    omega
  have hb : f gap.succ-f gap.castSucc-1=(b : ℤ) := by
    have hh := hgapMono gap
    dsimp only [f,b]
    omega
  have hholesTotal : holeMass f=((L-R : ℕ) : ℤ) := by
    rw [holeMass_span]
    dsimp only [f]
    rw [he0,heR]
    have hc0 : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
    have hw : (componentRight p 0).val+1=L := (prefix_root_packet_extremes p hm hc0).2.2
    norm_num only [Fin.val_zero,Nat.cast_zero,sub_zero]
    omega
  have hbnd : b ≤ L-R := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin r => f j.succ-f j.castSucc-1)
      (fun j _ => hnon j) (Finset.mem_univ gap)
    change f gap.succ-f gap.castSucc-1 ≤ holeMass f at hh
    rw [hb,hholesTotal] at hh
    exact_mod_cast hh
  have hholes : holeMass f=(b : ℤ)+(c : ℤ) := by
    rw [hholesTotal]
    dsimp only [c]
    omega
  have hslots : s=b+c+outside := by dsimp only [s,c,outside]; omega
  change (max 0 T)^2-(max 0 T)%2+8*((max 0 T)/2)*(outside : ℤ) ≤
    4*((l : ℤ)*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|))
  by_cases hT : 0 ≤ T
  · let j := (T/2).toNat
    have hj : (j : ℤ)=(2*(b : ℤ)-(s : ℤ)-(eta : ℤ))/2 :=
      Int.toNat_of_nonneg (Int.ediv_nonneg hT (by decide))
    have hd := canonical_lift p.symm
    have hh := geometric_internal_deficit P hP hsh hfull f hmono hd.1 hmaj emb.toEmbedding hδ
      gap l eta j s b c outside (by omega) hpar hsize hslots hb hholes hj
    unfold shellDeficit at hh
    rw [hmass] at hh
    rw [max_eq_right hT]
    dsimp only [T] at *
    rw [hj] at hh
    exact hh
  · have hb := prefix_core_balanced_energy_bound p hmaj
    change (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤ (l : ℤ)*((n : ℤ)-l) at hb
    rw [max_eq_left (by omega)]
    norm_num only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,Int.zero_emod,Int.zero_ediv,
      sub_self,mul_zero,zero_mul,zero_add]
    linarith only [hb]

#print axioms prefix_zero_defect_internal_deficit
end LRX.FiniteCuts
