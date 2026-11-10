module

public import LRX.PeakProfileFour

@[expose] public section

namespace LRX.FinitePeak

/-- Necessary exterior data at t=3; no m or x is inspected. -/
def ThreeOuter (p f e a U v : ℤ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ f ∧ f ≤ 8 ∧ 0 ≤ e ∧ e ≤ 15 ∧
  0 ≤ a ∧ a ≤ f ∧ 1 ≤ U ∧ U ≤ 10 ∧ 6 ≤ v ∧
  f^2 ≤ 4*e+p ∧ 0 ≤ 2*e+p-f ∧
  1 ≤ 2*(if a=0 then 3 else a+2)+3-U-(2*e+p-f) ∧
  2*f+9-2*(v-3) ≤ e ∧
  (7+2*a)*v ≤ 4*(if a=0 then 3 else a+2)+6*U+19-2*p-
    2*(a.toNat.choose 2 : ℤ)+f-a-2*e

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem three_outer_bounds (p f e a U v : ℤ) (h : ThreeOuter p f e a U v) :
    a=0 ∧ f ≤ 2 ∧ e ≤ 2 ∧ 4 ≤ U ∧ U ≤ 8 ∧ 7 ≤ v ∧ v ≤ 11 := by
  obtain ⟨hp0,hp1,hf0,hf8,he0,he15,ha0,haf,hU0,hU10,hv6,hact,hcredit,hfirst,htail,hext⟩ := h
  interval_cases p <;> interval_cases f <;> interval_cases e <;>
    norm_num at hact <;> try omega
  all_goals
    interval_cases a <;> norm_num at hfirst hext <;> omega

theorem admissible_three_outer (r : Profile) (hr : r.Admissible)
    (hcore : r.CoreBound) (ht : r.t=3) :
    ThreeOuter r.parity r.fixed r.eps r.isolated r.peak r.exterior := by
  have hext := Profile.admissible_core_exterior_filter r hr hcore
  obtain ⟨hd,hs,_⟩ := hr
  obtain ⟨_,_,hp0,hp1,hf0,hf8,he0,he15,ha0,haf,hU0,hU10,_,_,hv6,_⟩ := hd
  obtain ⟨hact,hcredit,hfirst,htail,_⟩ := hs
  have hB : r.B=(if r.isolated=0 then 3 else r.isolated+2) := by
    unfold Profile.B
    rw [ht]
    split_ifs <;> ring
  rw [ht,hB] at hfirst hext
  rw [ht] at htail
  norm_num at htail hext
  exact ⟨hp0,hp1,hf0,by omega,he0,by omega,ha0,haf,hU0,by omega,by omega,
    hact,hcredit,hfirst,by linarith only [htail],by split_ifs at hext ⊢ <;> nlinarith only [hext]⟩

#print axioms three_outer_bounds
end LRX.FinitePeak
