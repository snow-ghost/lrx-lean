import LRX.ExternalUnitPairsNoUnit

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Two unit arrows exhaust the small-arrow capacity of their sign:
a further arrow of length two would require 9<=8. -/
theorem zero_energy_unit_pair_no_double (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (a b : Fin n) (hab : a ≠ b) (sign : ℤ) (hsign : sign=1 ∨ sign= -1)
    (ha : displacement p.symm a=sign) (hb : displacement p.symm b=sign)
    (i : Fin n) : displacement p.symm i ≠ 2*sign := by
  classical
  intro hi
  have hsne : sign ≠ 0 := by rcases hsign with h | h <;> omega
  have hia : i ≠ a := by
    intro h
    rw [h,ha] at hi
    exact hsne (by omega)
  have hib : i ≠ b := by
    intro h
    rw [h,hb] at hi
    exact hsne (by omega)
  have hcard : ({a,b,i} : Finset (Fin n)).card=3 := by simp [hab,hia.symm,hib.symm]
  have hmass : (∑ j ∈ ({a,b,i} : Finset (Fin n)), |displacement p.symm j|)=4 := by
    rcases hsign with hs | hs <;> simp [hab,hia.symm,hib.symm,ha,hb,hi,hs]
  obtain ⟨hP,hN⟩ := zero_energy_even_sign_offsets p hmaj he hp
  rcases hsign with hs | hs
  · have hsub : {a,b,i} ⊆ positiveArrowPositions p := by
      intro j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> norm_num [ha,hb,hi,hs]
    have h := positive_selection_deficit p hmaj {a,b,i} hsub
    rw [hP,he,hp,hcard,hmass] at h
    norm_num at h
  · have hsub : {a,b,i} ⊆ negativeArrowPositions p := by
      intro j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> norm_num [ha,hb,hi,hs]
    have h := negative_selection_deficit p hmaj {a,b,i} hsub
    rw [hN,he,hp,hcard,hmass] at h
    norm_num at h

end LRX.FiniteCuts

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Once two unit windows exist, no length-two arrow occurs anywhere. -/
theorem two_unit_windows_no_two (A B : FillingWindow n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (ha : A.Matches p.symm) (hb : B.Matches p.symm) (hab : A.Apart B)
    (hA : (⟨A.size,A.filling⟩ : SmallExteriorMap)=unitExteriorMap)
    (hB : (⟨B.size,B.filling⟩ : SmallExteriorMap)=unitExteriorMap)
    (i : Fin n) : |displacement p.symm i| ≠ 2 := by
  obtain ⟨ap,am,hap,ham,hapd,hamd⟩ := unit_window_arrow_positions A p.symm ha hA
  obtain ⟨bp,bm,hbp,hbm,hbpd,hbmd⟩ := unit_window_arrow_positions B p.symm hb hB
  have hpne : ap ≠ bp := by intro h; apply hab ap hap; rwa [h]
  have hmne : am ≠ bm := by intro h; apply hab am ham; rwa [h]
  intro hi
  by_cases hpos : 0 ≤ displacement p.symm i
  · rw [abs_of_nonneg hpos] at hi
    exact zero_energy_unit_pair_no_double p hmaj he hp ap bp hpne 1 (Or.inl rfl)
      hapd hbpd i (by simpa using hi)
  · rw [abs_of_neg (by omega)] at hi
    exact zero_energy_unit_pair_no_double p hmaj he hp am bm hmne (-1) (Or.inr rfl)
      hamd hbmd i (by omega)

#print axioms LRX.FiniteCuts.zero_energy_unit_pair_no_double
#print axioms two_unit_windows_no_two
end LRX.FiniteWindow
