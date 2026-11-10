module

public import LRX.ThreeOuterBounds

@[expose] public section

namespace LRX.FinitePeak

/-- Exterior energy already contradicts the whole t=3 outer domain. -/
theorem three_outer_energy_impossible (p f e a U v : ℤ)
    (h : ThreeOuter p f e a U v)
    (he : v^2 ≤ 4*e+p+2*((v-4)^2+8-v%2)) : False := by
  obtain ⟨ha,hf2,he2,hU4,hU8,hv7,hv11⟩ := three_outer_bounds p f e a U v h
  obtain ⟨hp0,hp1,hf0,_,he0,_,_,_,_,_,_,_,_,hfirst,htail,hext⟩ := h
  subst a
  norm_num at hfirst hext
  interval_cases v <;> norm_num at he hext htail <;> omega

#print axioms three_outer_energy_impossible
end LRX.FinitePeak
