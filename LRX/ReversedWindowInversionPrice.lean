import LRX.ReversalFamilyRank
import LRX.WindowFamilySelectedEnergy
import LRX.FiniteWindowLoad
import LRX.FiniteDisplacementSum

namespace LRX.FiniteWindow
open FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Inserting reversals into disjoint windows fixed by the core adds
exactly the local reversal inversion counts. The upper map is specified
by its actual arrows, rather than by a particular construction term. -/
theorem reversed_window_prices (As : List (FillingWindow n)) (P Q : State n)
    (hd : As.Pairwise FillingWindow.Apart)
    (hfix : ∀ A ∈ As, ∀ i, P (embed A.window i)=embed A.window i)
    (hrev : ∀ A ∈ As, ∀ i, Q (embed A.window i)=embed A.window (Fin.revPerm i))
    (hout : ∀ i, i ∉ familyPositions As → Q i=P i) :
    inversionNumber Q=inversionNumber P+(As.map (fun A => A.size.choose 2)).sum ∧
    (∑ i, |displacement Q i|)=(∑ i, |displacement P i|)+
      (As.map (fun A => ∑ i : Fin A.size, |displacement Fin.revPerm i|)).sum := by
  classical
  induction As generalizing Q with
  | nil =>
    have he : Q=P := Equiv.ext (fun i => hout i (by simp [familyPositions]))
    simp [he]
  | cons A As ih =>
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hd
    have hmatch := hrev A (List.mem_cons_self ..)
    let R := outsideFactor A.window Q Fin.revPerm
    have hRfix : ∀ i, R (embed A.window i)=embed A.window i :=
      outside_factor_embed A.window Q Fin.revPerm hmatch
    have hRrev : ∀ B ∈ As, ∀ i,
        R (embed B.window i)=embed B.window (Fin.revPerm i) := by
      intro B hB i
      rw [outside_factor_outside A.window Q Fin.revPerm _ (by
        intro hi
        exact hA B hB _ hi (contains_embed B.window i))]
      exact hrev B (List.mem_cons_of_mem _ hB) i
    have hRout : ∀ i, i ∉ familyPositions As → R i=P i := by
      intro i hi
      by_cases hin : Contains A.window i
      · obtain ⟨j,rfl⟩ := (contains_iff A.window i).mp hin
        rw [hRfix,hfix A (List.mem_cons_self ..) j]
      · rw [outside_factor_outside A.window Q Fin.revPerm i hin]
        apply hout i
        simp only [familyPositions,Finset.mem_union,not_or]
        exact ⟨fun hh => hin (Finset.mem_filter.mp hh).2,hi⟩
    have htail := ih R hAs (fun B hB => hfix B (List.mem_cons_of_mem _ hB)) hRrev hRout
    have hprice := inversion_number_mul_window A.window R Fin.revPerm hRfix
    rw [outside_factor_recover,inversion_number_reversal] at hprice
    have hmass : (∑ i, |displacement Q i|)=(∑ i, |displacement R i|)+
        (∑ i : Fin A.size, |displacement Fin.revPerm i|) := by
      have hdis := outside_factor_disjoint A.window Q Fin.revPerm Fin.revPerm hmatch
      have hh := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin n))=Finset.univ)
        (fun i _ => abs_displacement_mul R (permutation A.window Fin.revPerm) hdis i)
      rw [outside_factor_recover,Finset.sum_add_distrib,displacement_mass] at hh
      exact hh
    simp only [List.map_cons,List.sum_cons]
    exact ⟨by omega,by rw [hmass,htail.2]; ring⟩

#print axioms reversed_window_prices
end LRX.FiniteWindow
