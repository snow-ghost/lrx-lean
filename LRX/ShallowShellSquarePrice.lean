module

public import LRX.ShallowShellRankWord
public import LRX.FiniteRankInversionMonotonicity

@[expose] public section

namespace LRX.FiniteWindow
open scoped BigOperators
variable {n : ℕ}

theorem window_square_price_sum (As : List (FillingWindow n)) :
    (As.map (fun B => (B.size : ℤ)^2-((B.size+1)/2 : ℕ))).sum-
      (((As.map (fun B => B.size/2)).sum : ℕ) : ℤ)=
    (As.map (fun B => (B.size : ℤ)^2)).sum-
      (((As.map (fun B => B.size)).sum : ℕ) : ℤ) := by
  induction As with
  | nil => simp
  | cons B As ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    have hh : (((B.size+1)/2 : ℕ) : ℤ)+((B.size/2 : ℕ) : ℤ)=(B.size : ℤ) := by omega
    linarith

end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem prefix_root_packet_mass (p : State n) (hm : 2 ≤ (componentRoots p).card)
    (hc : 2 ≤ (componentSet p 0).card) :
    (∑ i, |displacement ((canonicalRootPacket p 0)⁻¹) i|)=
      ∑ i ∈ prefixSourceCore p, |displacement p.symm i| := by
  classical
  have he := canonical_pruned_displacement p (PrunedLift.core p (displacement p.symm) 0)
    (PrunedLift.core_invariant p (displacement p.symm) 0)
  change displacement ((canonicalRootPacket p 0)⁻¹)=_ at he
  rw [he,prefix_root_core_eq p hm hc]
  simp [PrunedLift.displacement,apply_ite,abs_zero]

/-- The all-cursor shell word has a price depending only on the actual
core mass and actual internal/external window sizes. -/
theorem exists_shell_square_price_word (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (start finish : Fin n) :
    let L := (componentSet p 0).card
    let U := leftPeak ((canonicalRootPacket p 0)⁻¹) n
    let D := ∑ i ∈ prefixSourceCore p, |displacement p.symm i|
    let squares := ((positiveSourceFamily p L).map (fun B => (B.size : ℤ)^2)).sum+
      ((n-L : ℕ) : ℤ)^2
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ 2*D-(n : ℤ)+3+(n/2 : ℕ)-(U : ℤ)+squares := by
  classical
  let L := (componentSet p 0).card
  obtain ⟨E,Q,C,w,hEo,hEs,hrev,hapart,hcover,hbelow,hbelowG,hC,hCs,hpeak,hact,hfac,
    hother,hcount,hdiscount,hpairsCount,htwo,hgap,hgapExt,hstar,hIQ,hMassQ,hcombined,hI,hMass,hw,hlen⟩ :=
    exists_shell_joined_rank_word p hmaj hm hlarge hz start finish
  have hmono := FiniteRankOrder.below_inversion_mono p.symm Q hbelow
  have hinv : inversionNumber p.symm=inversionNumber p := inversion_number_inverse p
  rw [hinv] at hmono
  have hmono' : (inversionNumber p : ℤ) ≤ (inversionNumber Q : ℤ) := by exact_mod_cast hmono
  let As := positiveSourceFamily p L++[E]
  have hsize := apart_family_positions_card As hapart
  rw [hcover,Finset.card_compl,Fintype.card_fin] at hsize
  have hRle : (prefixSourceCore p).card ≤ n := by simpa using Finset.card_le_univ (prefixSourceCore p)
  have hsize' : (((As.map (fun B => B.size)).sum : ℕ) : ℤ)=
      (n : ℤ)-((prefixSourceCore p).card : ℤ) := by omega
  have hsum := window_square_price_sum As
  have hmassCore := prefix_root_packet_mass p hm (by have := NeZero.pos n; omega)
  rw [hmassCore] at hcombined
  have hsquares : (As.map (fun B => (B.size : ℤ)^2)).sum=
      ((positiveSourceFamily p L).map (fun B => (B.size : ℤ)^2)).sum+((n-L : ℕ) : ℤ)^2 := by
    simp only [As,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,hEs,L]
  refine ⟨w,hw,?_⟩
  change (w.length : ℤ) ≤ 2*(∑ i ∈ prefixSourceCore p, |displacement p.symm i|)-(n : ℤ)+3+
    (n/2 : ℕ)-(leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)+
    (((positiveSourceFamily p L).map (fun B => (B.size : ℤ)^2)).sum+((n-L : ℕ) : ℤ)^2)
  rw [hMass] at hlen
  dsimp only [As,L] at hsum hsize' hsquares
  linarith

#print axioms prefix_root_packet_mass
#print axioms exists_shell_square_price_word
end LRX.FiniteCuts
