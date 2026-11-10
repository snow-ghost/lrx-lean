module

public import LRX.FinitePeakProfile

@[expose] public section

namespace LRX.FinitePeak

/-- With the D3 holes eliminated, the critical scalar profile has only
the two sizes served by the existing exceptional route. -/
theorem peak_four_zero_holes_sizes (r : Profile) (hr : r.Admissible)
    (ht : r.t=2) (hp : r.parity=0) (hf : r.fixed=0) (he : r.eps=0)
    (ha : r.isolated=0) (hU : r.peak=4) (hv : r.exterior=4) (hx : r.holes=0) :
    r.m=8 ∨ r.m=10 := by
  obtain ⟨hd,hres,hfilters⟩ := hr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hpar,_,_,_⟩ := hd
  obtain ⟨_,_,_,_,hT,_,hcap,_⟩ := hres
  have henergy := hfilters.1
  norm_num [Profile.T,Profile.B,Profile.M,ht,hp,hf,he,ha,hU,hv] at hT
  have hm : 7 ≤ r.m := by omega
  have hc : 0 ≤ r.m-2 := by omega
  norm_num [Profile.need,Profile.energy,Profile.L,Profile.n,Profile.E2,
    Profile.J,Profile.cap,ht,hp,hf,he,ha,hU,hv,hx,hc] at henergy
  have hm2 : 2 ≤ r.m := by omega
  rw [if_pos hm2] at henergy
  have hupper : r.m ≤ 10 := by nlinarith
  have hcases : r.m=7 ∨ r.m=8 ∨ r.m=9 ∨ r.m=10 := by omega
  rcases hcases with h | h | h | h
  · norm_num [Profile.energy,h,hp,he] at hpar
  · exact Or.inl h
  · norm_num [Profile.energy,h,hp,he] at hpar
  · exact Or.inr h

#print axioms peak_four_zero_holes_sizes
end LRX.FinitePeak
