import LRX.PrefixShallowPhysicalModel

namespace LRX.FiniteCuts
open ContractionBlocks.System
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The external-hole estimate for the actual initial zero-defect packet.
The positive part removes the research lemma's implicit nonnegative-threshold
restriction; the other branch uses actual balanced-core capacity. -/
theorem prefix_zero_defect_exterior_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0) :
    let L := (componentSet p 0).card
    let l := (prefixSourceCore p).card/2
    (max 0 ((n : ℤ)-2*(L : ℤ)+2*(l : ℤ)))^2/4 ≤
      (l : ℤ)*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|) := by
  classical
  let L := (componentSet p 0).card
  let R := (prefixSourceCore p).card
  let l := R/2
  let eta := R%2
  let c := L-R
  let outside := n-L
  let s := n-R
  let T : ℤ := (n : ℤ)-2*(L : ℤ)+2*(l : ℤ)
  have hRL : R ≤ L := by
    apply Finset.card_le_card
    intro i hi
    exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2
  have hLn : L ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ (componentSet p 0)
  change (max 0 T)^2/4 ≤ (l : ℤ)*((n : ℤ)-l)-_
  by_cases hT : 0 ≤ T
  · obtain ⟨r,P,emb,hP,hsh,hfull,hcard,hδ,hmono,he0,heR,hwide,hmass,_⟩ :=
      prefix_zero_defect_physical_model p hmaj hm hlarge hz
    have hc0 : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
    have hends := prefix_root_packet_extremes p hm hc0
    have hR : r+1=R := hcard
    have hsplit : R=2*l+eta := by dsimp only [l,eta]; omega
    have hslots : s=c+outside := by dsimp only [s,c,outside]; omega
    have hsize : n=r+1+s := by dsimp only [s]; omega
    have hpar : eta ≤ 1 := by dsimp only [eta]; omega
    have hholes : holeMass (fun i => (emb i : ℤ))=(c : ℤ) := by
      rw [holeMass_span,he0,heR]
      have hw : (componentRight p 0).val+1=L := hends.2.2
      dsimp only [c]
      norm_num only [Fin.val_zero,Nat.cast_zero,sub_zero]
      omega
    have hdiff : (outside : ℤ)-(c : ℤ)-(eta : ℤ)=T := by
      dsimp only [outside,c,T]
      omega
    let j := (T/2).toNat
    have hj : (j : ℤ)=((outside : ℤ)-(c : ℤ)-(eta : ℤ))/2 := by
      rw [hdiff]
      exact Int.toNat_of_nonneg (Int.ediv_nonneg hT (by decide))
    have hd := canonical_lift p.symm
    have hh := geometric_exterior_deficit P hP hsh hfull (fun i => (emb i : ℤ)) hmono
      hd.1 hmaj emb.toEmbedding hδ l eta j s c outside
      (by omega) hpar hsize hslots hholes hwide hj
    rw [hdiff] at hh
    unfold shellDeficit at hh
    rw [hmass] at hh
    rw [max_eq_right hT]
    exact hh
  · have hb := prefix_core_balanced_energy_bound p hmaj
    change (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤ (l : ℤ)*((n : ℤ)-l) at hb
    rw [max_eq_left (by omega)]
    norm_num only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,Int.zero_ediv]
    linarith only [hb]

#print axioms prefix_zero_defect_exterior_deficit
end LRX.FiniteCuts
