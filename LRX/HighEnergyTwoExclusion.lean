module

public import LRX.HighEnergyTwoChunks.Chunk0
public import LRX.HighEnergyTwoChunks.Chunk1
public import LRX.HighEnergyTwoChunks.Chunk2
public import LRX.HighEnergyTwoChunks.Chunk3
public import LRX.HighEnergyTwoChunks.Chunk4
public import LRX.HighEnergyTwoChunks.Chunk5
public import LRX.HighEnergyTwoChunks.Chunk6

@[expose] public section

namespace LRX.FinitePeak

theorem high_energy_two_check : highEnergyTwoRows.all (fun o => decide (∀ m : Fin 37, ∀ x : Fin 70,
      ¬(twoProfileOfOuter o (m.val : ℤ) (x.val : ℤ)).Admissible))=true := by
  have hparts : highEnergyTwoRows=
    ((highEnergyTwoRows.drop 0).take 3) ++
    ((highEnergyTwoRows.drop 3).take 3) ++
    ((highEnergyTwoRows.drop 6).take 3) ++
    ((highEnergyTwoRows.drop 9).take 3) ++
    ((highEnergyTwoRows.drop 12).take 3) ++
    ((highEnergyTwoRows.drop 15).take 3) ++
    ((highEnergyTwoRows.drop 18).take 3) := by decide +kernel
  rw [hparts]
  simp only [List.all_append,high_energy_two_chunk_0,high_energy_two_chunk_1,high_energy_two_chunk_2,high_energy_two_chunk_3,high_energy_two_chunk_4,high_energy_two_chunk_5,high_energy_two_chunk_6,Bool.and_self]

theorem high_energy_two_profile_impossible (r : Profile) (hr : r.Admissible)
    (hcore : r.CoreBound) (ht : r.t=2)
    (hext : r.exterior^2 ≤ 4*r.eps+r.parity+2*(r.E2-r.exterior%2))
    (hm0 : 0 ≤ r.m) (hm36 : r.m ≤ 36) (hx0 : 0 ≤ r.holes) (hx69 : r.holes ≤ 69)
    (he : 2 ≤ r.eps) (hv : r.exterior ≤ 7) : False := by
  have ho := admissible_two_mem_table r hr hcore ht hext
  have hmem : (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior) ∈ highEnergyTwoRows := by
    apply List.mem_filter.mpr
    exact ⟨ho,decide_eq_true ⟨he,hv⟩⟩
  have hh := of_decide_eq_true (List.all_eq_true.mp high_energy_two_check _ hmem)
  let mm : Fin 37 := ⟨r.m.toNat,by omega⟩
  let xx : Fin 70 := ⟨r.holes.toNat,by omega⟩
  have hmm : (mm.val : ℤ)=r.m := by dsimp only [mm]; omega
  have hxx : (xx.val : ℤ)=r.holes := by dsimp only [xx]; omega
  have hn := hh mm xx
  rw [hmm,hxx] at hn
  have heq : twoProfileOfOuter (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior) r.m r.holes=r := by
    cases r
    simp_all [twoProfileOfOuter]
  rw [heq] at hn
  exact hn hr

#print axioms high_energy_two_check
#print axioms high_energy_two_profile_impossible
end LRX.FinitePeak
