import LRX.FinitePeakProfile

namespace LRX.FinitePeak

theorem energy_one_profile_parity (r : Profile) (hr : r.Admissible) (he : r.eps=1) :
    r.parity=0 ∧ r.m%2=1 ∧ r.fixed ≤ 2 := by
  obtain ⟨hd,hres,_⟩ := hr
  obtain ⟨_,_,hp0,hp1,hf0,_,_,_,_,_,_,_,_,_,_,_,_,henergy,_,_,_⟩ := hd
  have hmod : r.m%2=0 ∨ r.m%2=1 := by omega
  have hcases : r.parity=0 ∨ r.parity=1 := by omega
  have hpm : r.parity=0 ∧ r.m%2=1 := by
    rcases hcases with hp | hp <;> rcases hmod with hm | hm
    · norm_num [Profile.energy,he,hp,Int.sub_emod,Int.mul_emod,hm] at henergy
    · exact ⟨hp,hm⟩
    · norm_num [Profile.energy,he,hp,Int.sub_emod,Int.mul_emod,Int.add_emod,hm] at henergy
    · norm_num [Profile.energy,he,hp,Int.sub_emod,Int.mul_emod,Int.add_emod,hm] at henergy
  have hfixed := hres.1
  rw [he,hpm.1] at hfixed
  refine ⟨hpm.1,hpm.2,?_⟩
  by_contra hh
  have hf3 : 3 ≤ r.fixed := by omega
  nlinarith [sq_nonneg (r.fixed-2)]

#print axioms energy_one_profile_parity
end LRX.FinitePeak
