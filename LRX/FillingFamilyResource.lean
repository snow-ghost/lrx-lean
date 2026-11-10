import LRX.FiniteFillingResource
import LRX.ReversalWindowFamily

/-! M4 resource filters summed over actual finite filling windows.
The sole external numerical input is the upper budget on this same family. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ}

noncomputable def FillingWindow.resource (A : FillingWindow n) : ℤ := fillingResource A.filling

theorem filling_resource_sum_nonneg (As : List (FillingWindow n)) :
    0 ≤ (As.map FillingWindow.resource).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨A,_,rfl⟩ := List.mem_map.mp hx
  have h := filling_resource_half_width A.filling
  change 0 ≤ fillingResource A.filling
  omega

/-- One and the same actual family supplies all three bounds. -/
theorem filling_family_resource_sum_bounds (As : List (FillingWindow n)) :
    let K := (As.map FillingWindow.resource).sum
    (As.map (fun A => (A.size : ℤ))).sum ≤ 2*K+
      (As.map (fun A => ((A.size-A.filling.support.card : ℕ) : ℤ))).sum-
      2*(As.map (fun A => cycleDefect A.filling)).sum ∧
    (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤ 2*K*(K+1) ∧
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ 4*K^2+2*K+
      (As.map (fun A => (A.size : ℤ))).sum := by
  induction As with
  | nil => norm_num
  | cons A As ih =>
    have hw := filling_resource_width_defect A.filling
    have he := filling_resource_energy A.filling
    have hq := filling_resource_square_width A.filling
    have hk : 0 ≤ A.resource := by
      have h := filling_resource_half_width A.filling
      change 0 ≤ fillingResource A.filling
      omega
    have hK := filling_resource_sum_nonneg As
    change _ ≤ 2*A.resource+_-2*_ at hw
    change _ ≤ 2*A.resource*(A.resource+1) at he
    change _ ≤ 4*A.resource^2+2*A.resource+_ at hq
    dsimp only at ih ⊢
    simp only [List.map_cons,List.sum_cons]
    rcases ih with ⟨ihw,ihe,ihq⟩
    refine ⟨by omega,?_,?_⟩ <;> nlinarith [mul_nonneg hk hK]

/-- The numerical M4 filters, with width, fixed positions and defects
computed from this family rather than supplied independently. -/
theorem filling_family_resource_budget (As : List (FillingWindow n)) (T : ℤ)
    (hbudget : (As.map FillingWindow.resource).sum ≤ T) :
    (As.map (fun A => (A.size : ℤ))).sum ≤ 2*T+
      (As.map (fun A => ((A.size-A.filling.support.card : ℕ) : ℤ))).sum-
      2*(As.map (fun A => cycleDefect A.filling)).sum ∧
    (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤ 2*T*(T+1) ∧
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ 4*T^2+2*T+
      (As.map (fun A => (A.size : ℤ))).sum := by
  obtain ⟨hw,he,hq⟩ := filling_family_resource_sum_bounds As
  have hK := filling_resource_sum_nonneg As
  have hdiff := mul_nonneg (show 0 ≤ T-(As.map FillingWindow.resource).sum by omega)
    (show 0 ≤ T+(As.map FillingWindow.resource).sum by omega)
  refine ⟨by omega,?_,?_⟩ <;> nlinarith

/-- The defect-corrected resources are nonnegative and pay fixed-free energy. -/
theorem fixed_free_filling_family_energy (As : List (FillingWindow n))
    (hf : ∀ A ∈ As, A.filling.support.card=A.size) :
    let H := (As.map (fun A => A.resource-cycleDefect A.filling)).sum
    0 ≤ H ∧ (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤ 2*H^2 := by
  induction As with
  | nil => norm_num
  | cons A As ih =>
    obtain ⟨hA,he⟩ := filling_resource_fixed_free_energy A.filling (hf A (by simp))
    obtain ⟨hAs,ih⟩ := ih (fun B hB => hf B (List.mem_cons_of_mem _ hB))
    change 0 ≤ A.resource-cycleDefect A.filling at hA
    change _ ≤ 2*(A.resource-cycleDefect A.filling)^2 at he
    dsimp only at hAs ih ⊢
    simp only [List.map_cons,List.sum_cons]
    exact ⟨by omega,by nlinarith [mul_nonneg hA hAs]⟩

/-- Stronger M4 energy filter when the actual fillings have no fixed positions. -/
theorem fixed_free_filling_family_budget (As : List (FillingWindow n)) (T : ℤ)
    (hf : ∀ A ∈ As, A.filling.support.card=A.size)
    (hbudget : (As.map FillingWindow.resource).sum ≤ T) :
    (As.map (fun A => ∑ i, |displacement A.filling i|)).sum ≤
      2*(T-(As.map (fun A => cycleDefect A.filling)).sum)^2 ∧
    2*(T-(As.map (fun A => cycleDefect A.filling)).sum)^2 ≤ 2*T^2 := by
  obtain ⟨hH,he⟩ := fixed_free_filling_family_energy As hf
  have hsplit : (As.map (fun A => A.resource-cycleDefect A.filling)).sum=
      (As.map FillingWindow.resource).sum-(As.map (fun A => cycleDefect A.filling)).sum := by
    clear hf hbudget hH he
    induction As with
    | nil => simp
    | cons A As ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih]
      ring
  rw [hsplit] at hH he
  have hZ : 0 ≤ (As.map (fun A => cycleDefect A.filling)).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨A,_,rfl⟩ := List.mem_map.mp hz
    have hh := finite_depth_rank A.filling
    unfold cycleDefect
    omega
  have hK := filling_resource_sum_nonneg As
  constructor
  · have h := mul_nonneg
      (show 0 ≤ T-(As.map FillingWindow.resource).sum by omega)
      (show 0 ≤ T+(As.map FillingWindow.resource).sum-
        2*(As.map (fun A => cycleDefect A.filling)).sum by omega)
    nlinarith
  · have h := mul_nonneg hZ
      (show 0 ≤ 2*T-(As.map (fun A => cycleDefect A.filling)).sum by omega)
    nlinarith

#print axioms filling_family_resource_budget
#print axioms fixed_free_filling_family_budget
end LRX.FiniteWindow
