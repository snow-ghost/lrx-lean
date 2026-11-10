module

public import LRX.AreaWindowSplitSquare

@[expose] public section

/-! M4: exact exterior square and energy envelopes for the actual nontrivial
component windows, using only their real sizes and the lower bound two. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ}

theorem nontrivial_window_square_envelope (As : List (FillingWindow n))
    (hw : ∀ A ∈ As, 2 ≤ A.size) :
    2*(As.length : ℤ) ≤ (As.map (fun A => (A.size : ℤ))).sum ∧
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      ((As.map (fun A => (A.size : ℤ))).sum-2*(As.length : ℤ)+2)^2+4*((As.length : ℤ)-1) := by
  induction As with
  | nil => norm_num
  | cons A As ih =>
    have hA := hw A (by simp)
    obtain ⟨hv,hq⟩ := ih (fun B hB => hw B (List.mem_cons_of_mem _ hB))
    have hcross := mul_nonneg
      (show 0 ≤ (As.map (fun A => (A.size : ℤ))).sum-2*(As.length : ℤ) by omega)
      (show 0 ≤ (A.size : ℤ)-2 by omega)
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact ⟨by omega,by nlinarith⟩

theorem window_family_energy_le_square (As : List (FillingWindow n)) :
    2*(As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤
      (As.map (fun A => (A.size : ℤ)^2)).sum := by
  induction As with
  | nil => simp
  | cons A As ih =>
    have he := finite_energy_fixed_square A.filling
    simp only [List.map_cons,List.sum_cons]
    nlinarith [sq_nonneg (((A.size-A.filling.support.card : ℕ) : ℤ))]

/-- The largest member has only the excess over the mandatory size-two tail. -/
theorem nontrivial_window_member_size (As : List (FillingWindow n))
    (hw : ∀ A ∈ As, 2 ≤ A.size) (A : FillingWindow n) (hA : A ∈ As) :
    (A.size : ℤ) ≤ (As.map (fun B => (B.size : ℤ))).sum-2*(As.length : ℤ)+2 := by
  have hsum : (As.map (fun B => (B.size : ℤ)-2)).sum=
      (As.map (fun B => (B.size : ℤ))).sum-2*(As.length : ℤ) := by
    clear hw hA
    induction As with
    | nil => simp
    | cons B As ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,ih]
      ring
  have hh : (A.size : ℤ)-2 ≤ (As.map (fun B => (B.size : ℤ)-2)).sum := by
    apply List.single_le_sum
    · intro x hx
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hx
      have hh := hw B hB
      omega
    · exact List.mem_map.mpr ⟨A,hA,rfl⟩
  rw [hsum] at hh
  omega
end LRX.FiniteWindow

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow
variable {n : ℕ} [NeZero n]

noncomputable def exteriorSquareBound (t v : ℕ) : ℤ :=
  ((v : ℤ)-2*(t : ℤ)+2)^2+4*((t : ℤ)-1)

/-- The exact integer envelope has the parity of v. -/
theorem exterior_square_bound_parity (t v : ℕ) :
    exteriorSquareBound t v % 2=(v%2 : ℕ) := by
  have hv : (v : ℤ)%2=0 ∨ (v : ℤ)%2=1 := by omega
  have hcast : ((v%2 : ℕ) : ℤ)=(v : ℤ)%2 := by omega
  rw [hcast]
  rcases hv with hv | hv <;>
    norm_num [exteriorSquareBound,pow_two,Int.add_emod,Int.sub_emod,Int.mul_emod,hv]

theorem suffix_component_window_sizes (p : State n) (L : ℕ) :
    (suffixComponentFamily p L).length=(nontrivialSuffixComponents p L).card ∧
    (∀ A ∈ suffixComponentFamily p L, 2 ≤ A.size) := by
  classical
  constructor
  · simp [suffixComponentFamily]
  · intro A hA
    obtain ⟨C,_,rfl⟩ := List.mem_map.mp hA
    rw [(suffix_component_filling_spec p L C).1]
    exact (Finset.mem_filter.mp C.property).2

/-- External M4 filters with the actual t,v and actual filling permutations. -/
theorem suffix_component_square_energy_bounds (p : State n) (L : ℕ) :
    let As := suffixComponentFamily p L
    let t := (nontrivialSuffixComponents p L).card
    let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ exteriorSquareBound t v ∧
    2*(As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤
      exteriorSquareBound t v-(v%2 : ℕ) := by
  obtain ⟨hlen,hsize⟩ := suffix_component_window_sizes p L
  have hs := congrArg (fun z : ℕ => (z : ℤ)) (suffix_component_family_size_sum p L)
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def] at hs
  have hq := (nontrivial_window_square_envelope (suffixComponentFamily p L) hsize).2
  rw [hlen,hs] at hq
  change _ ≤ exteriorSquareBound _ _ at hq
  have he := window_family_energy_le_square (suffixComponentFamily p L)
  have hp := exterior_square_bound_parity (nontrivialSuffixComponents p L).card
    (∑ C ∈ nontrivialSuffixComponents p L, C.card)
  dsimp only
  exact ⟨hq,by omega⟩

theorem suffix_component_member_size_bound (p : State n) (L : ℕ)
    (A : FillingWindow n) (hA : A ∈ suffixComponentFamily p L) :
    (A.size : ℤ) ≤ ((∑ C ∈ nontrivialSuffixComponents p L, C.card : ℕ) : ℤ)-
      2*((nontrivialSuffixComponents p L).card : ℤ)+2 := by
  obtain ⟨hlen,hsize⟩ := suffix_component_window_sizes p L
  have hs := congrArg (fun z : ℕ => (z : ℤ)) (suffix_component_family_size_sum p L)
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def] at hs
  have h := nontrivial_window_member_size (suffixComponentFamily p L) hsize A hA
  rwa [hlen,hs] at h

#print axioms suffix_component_square_energy_bounds
#print axioms suffix_component_member_size_bound
end LRX.FiniteCuts
