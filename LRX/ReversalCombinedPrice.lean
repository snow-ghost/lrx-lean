import LRX.ReversalPairCostSum
import LRX.ReversedWindowInversionPrice
import LRX.ShallowContraction

namespace LRX.FiniteCuts
open scoped BigOperators

theorem reversal_mass_choose (n : ℕ) :
    (∑ i : Fin n, |displacement Fin.revPerm i|)=(n.choose 2 : ℤ)+(n/2 : ℕ) := by
  have hm := displacement_mass_list_prod (reversalPairs n) (reversal_pairs_pairwise n)
  rw [reversal_pairs_product] at hm
  simp only [reversalPairs,List.map_ofFn,List.sum_ofFn,Function.comp_def] at hm
  have hpoint (i : Fin (n/2)) : (∑ j : Fin n, |displacement (reversalPair i) j|)=
      2*(((reversalLeft i).rev : ℤ)-(reversalLeft i : ℤ)) :=
    swap_displacement_mass _ _ (reversal_left_lt_right i)
  simp_rw [hpoint] at hm
  have hp := reversal_pair_rotation_sum n
  rw [Finset.sum_sub_distrib] at hp
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hp
  omega

theorem reversal_combined_price (n : ℕ) :
    (n.choose 2 : ℤ)+(∑ i : Fin n, |displacement Fin.revPerm i|)=
      (n : ℤ)^2-((n+1)/2 : ℕ) := by
  rw [reversal_mass_choose]
  have hchoose := twice_choose_two_int n
  have hhalf : ((n/2 : ℕ) : ℤ)+(( (n+1)/2 : ℕ) : ℤ)=(n : ℤ) := by omega
  nlinarith

theorem reversal_mass_half_square (n : ℕ) :
    (∑ i : Fin n, |displacement Fin.revPerm i|)=(n*n/2 : ℕ) := by
  rw [reversal_mass_choose]
  have hchoose := twice_choose_two_int n
  have hmod : n*n%2=n%2 := by
    rw [Nat.mul_mod]
    rcases (show n%2=0 ∨ n%2=1 by omega) with h | h <;> simp [h]
  have he : (n*n/2)*2+n%2=n*n := by omega
  have he' : ((n*n/2 : ℕ) : ℤ)*2+(n%2 : ℕ)=(n : ℤ)*(n : ℤ) := by exact_mod_cast he
  have hn' : ((n/2 : ℕ) : ℤ)*2+(n%2 : ℕ)=(n : ℤ) := by omega
  nlinarith

end LRX.FiniteCuts

namespace LRX.FiniteWindow
open FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem reversed_shallow_combined_price (As : List (FillingWindow n)) (P Q : State n)
    (hshallow : (∑ i, |displacement P i|)-(inversionNumber P : ℤ)=(P.support.card : ℤ)-1)
    (hI : inversionNumber Q=inversionNumber P+(As.map (fun A => A.size.choose 2)).sum)
    (hM : (∑ i, |displacement Q i|)=(∑ i, |displacement P i|)+
      (As.map (fun A => ∑ i : Fin A.size, |displacement Fin.revPerm i|)).sum) :
    (inversionNumber Q : ℤ)+(∑ i, |displacement Q i|)=
      2*(∑ i, |displacement P i|)-(P.support.card : ℤ)+1+
        (As.map (fun A => (A.size : ℤ)^2-((A.size+1)/2 : ℕ))).sum := by
  have hsum : (((As.map (fun A => A.size.choose 2)).sum : ℕ) : ℤ)+
      (As.map (fun A => ∑ i : Fin A.size, |displacement Fin.revPerm i|)).sum=
        (As.map (fun A => (A.size : ℤ)^2-((A.size+1)/2 : ℕ))).sum := by
    clear hI hM
    induction As with
    | nil => simp
    | cons A As ih =>
      simp only [List.map_cons,List.sum_cons,Nat.cast_add]
      have hh := reversal_combined_price A.size
      linarith
  rw [hI,hM,Nat.cast_add]
  linarith

#print axioms reversed_shallow_combined_price
end LRX.FiniteWindow
