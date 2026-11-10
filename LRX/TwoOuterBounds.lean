import LRX.PeakProfileFour

namespace LRX.FinitePeak

/-- Necessary exterior data at t=2, including the separate energy filter. -/
def TwoOuter (p f e a U v : ℤ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ f ∧ f ≤ 7 ∧ 0 ≤ e ∧ e ≤ 12 ∧
  0 ≤ a ∧ a ≤ f ∧ 1 ≤ U ∧ U ≤ 7 ∧ 4 ≤ v ∧
  f^2 ≤ 4*e+p ∧ 0 ≤ 2*e+p-f ∧
  1 ≤ 2*(if a=0 then 2 else a+1)+2-U-(2*e+p-f) ∧
  2*f+4-2*(v-2) ≤ e ∧
  (3+2*a)*v ≤ 4*(if a=0 then 2 else a+1)+6*U+3-2*p-
    2*(a.toNat.choose 2 : ℤ)+f-a-2*e ∧
  v^2 ≤ 4*e+p+2*((v-2)^2+4-v%2)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem two_outer_bounds (p f e a U v : ℤ) (h : TwoOuter p f e a U v) :
    f ≤ 3 ∧ e ≤ 3 ∧ a ≤ 2 ∧ v ≤ 13 := by
  obtain ⟨hp0,hp1,hf0,hf7,he0,he12,ha0,haf,hU0,hU7,hv4,hact,hcredit,hfirst,htail,hext,_⟩ := h
  interval_cases p <;> interval_cases f <;> interval_cases e <;>
    norm_num at hact <;> try omega
  all_goals
    interval_cases a <;> norm_num at hfirst hext <;> omega

theorem admissible_two_outer (r : Profile) (hr : r.Admissible)
    (hcore : r.CoreBound) (ht : r.t=2)
    (he : r.exterior^2 ≤ 4*r.eps+r.parity+2*(r.E2-r.exterior%2)) :
    TwoOuter r.parity r.fixed r.eps r.isolated r.peak r.exterior := by
  have hext := Profile.admissible_core_exterior_filter r hr hcore
  obtain ⟨hd,hs,_⟩ := hr
  obtain ⟨_,_,hp0,hp1,hf0,hf7,he0,he12,ha0,haf,hU0,hU7,_,_,hv4,_⟩ := hd
  obtain ⟨hact,hcredit,hfirst,htail,_⟩ := hs
  have hB : r.B=(if r.isolated=0 then 2 else r.isolated+1) := by
    unfold Profile.B
    rw [ht]
    split_ifs <;> ring
  rw [ht,hB] at hfirst hext
  rw [ht] at htail
  norm_num at htail hext
  unfold Profile.E2 at he
  rw [ht] at he
  exact ⟨hp0,hp1,hf0,by omega,he0,by omega,ha0,haf,hU0,by omega,by omega,
    hact,hcredit,hfirst,by linarith only [htail],
    by split_ifs at hext ⊢ <;> nlinarith only [hext],by nlinarith only [he]⟩

#print axioms two_outer_bounds
#print axioms admissible_two_outer
end LRX.FinitePeak
