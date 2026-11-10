module

public import LRX.EnergyOneChunks.Chunk0
public import LRX.EnergyOneChunks.Chunk1
public import LRX.EnergyOneChunks.Chunk2
public import LRX.EnergyOneChunks.Chunk3
public import LRX.EnergyOneChunks.Chunk4
public import LRX.EnergyOneChunks.Chunk5
public import LRX.EnergyOneChunks.Chunk6
public import LRX.EnergyOneChunks.Chunk7
public import LRX.EnergyOneChunks.Chunk8
public import LRX.EnergyOneChunks.Chunk9
public import LRX.EnergyOneChunks.Chunk10
public import LRX.EnergyOneChunks.Chunk11
public import LRX.EnergyOneChunks.Chunk12
public import LRX.EnergyOneChunks.Chunk13
public import LRX.EnergyOneChunks.Chunk14
public import LRX.EnergyOneChunks.Chunk15
public import LRX.EnergyOneChunks.Chunk16
public import LRX.EnergyOneChunks.Chunk17
public import LRX.EnergyOneChunks.Chunk18

@[expose] public section

namespace LRX.FinitePeak

theorem energy_one_outer_coverage_check : boundedEnergyOneRows.all (fun o => decide
    (o ∈ energyOneOuterRows ∨ ∀ m : Fin 37,
      ¬TwoSizeNecessary (twoProfileOfOuter o (m.val : ℤ) 0) ∨
      ∀ x : Fin 70, ¬(twoProfileOfOuter o (m.val : ℤ) (x.val : ℤ)).Admissible))=true := by
  have hparts : boundedEnergyOneRows=
    ((boundedEnergyOneRows.drop 0).take 3) ++
    ((boundedEnergyOneRows.drop 3).take 3) ++
    ((boundedEnergyOneRows.drop 6).take 3) ++
    ((boundedEnergyOneRows.drop 9).take 3) ++
    ((boundedEnergyOneRows.drop 12).take 3) ++
    ((boundedEnergyOneRows.drop 15).take 3) ++
    ((boundedEnergyOneRows.drop 18).take 3) ++
    ((boundedEnergyOneRows.drop 21).take 3) ++
    ((boundedEnergyOneRows.drop 24).take 3) ++
    ((boundedEnergyOneRows.drop 27).take 3) ++
    ((boundedEnergyOneRows.drop 30).take 3) ++
    ((boundedEnergyOneRows.drop 33).take 3) ++
    ((boundedEnergyOneRows.drop 36).take 3) ++
    ((boundedEnergyOneRows.drop 39).take 3) ++
    ((boundedEnergyOneRows.drop 42).take 3) ++
    ((boundedEnergyOneRows.drop 45).take 3) ++
    ((boundedEnergyOneRows.drop 48).take 3) ++
    ((boundedEnergyOneRows.drop 51).take 3) ++
    ((boundedEnergyOneRows.drop 54).take 3) := by decide +kernel
  rw [hparts]
  simp only [List.all_append,energy_one_outer_chunk_0,energy_one_outer_chunk_1,energy_one_outer_chunk_2,energy_one_outer_chunk_3,energy_one_outer_chunk_4,energy_one_outer_chunk_5,energy_one_outer_chunk_6,energy_one_outer_chunk_7,energy_one_outer_chunk_8,energy_one_outer_chunk_9,energy_one_outer_chunk_10,energy_one_outer_chunk_11,energy_one_outer_chunk_12,energy_one_outer_chunk_13,energy_one_outer_chunk_14,energy_one_outer_chunk_15,energy_one_outer_chunk_16,energy_one_outer_chunk_17,energy_one_outer_chunk_18,Bool.and_self]

theorem energy_one_profile_mem_cases (r : Profile) (hr : r.Admissible)
    (hcore : r.CoreBound) (ht : r.t=2)
    (hext : r.exterior^2 ≤ 4*r.eps+r.parity+2*(r.E2-r.exterior%2))
    (hm0 : 0 ≤ r.m) (hm36 : r.m ≤ 36) (hx0 : 0 ≤ r.holes) (hx69 : r.holes ≤ 69)
    (he : r.eps=1) (hv : r.exterior ≤ 7) :
    (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior) ∈ energyOneOuterRows := by
  have ho := admissible_two_mem_table r hr hcore ht hext
  have hmem : (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior) ∈ boundedEnergyOneRows := by
    apply List.mem_filter.mpr
    exact ⟨ho,decide_eq_true ⟨he,hv⟩⟩
  have hh := of_decide_eq_true (List.all_eq_true.mp energy_one_outer_coverage_check _ hmem)
  rcases hh with hdone | hrest
  · exact hdone
  let o : OuterRow := (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior)
  let mm : Fin 37 := ⟨r.m.toNat,by omega⟩
  let xx : Fin 70 := ⟨r.holes.toNat,by omega⟩
  have hmm : (mm.val : ℤ)=r.m := by dsimp only [mm]; omega
  have hxx : (xx.val : ℤ)=r.holes := by dsimp only [xx]; omega
  have heq : twoProfileOfOuter o r.m r.holes=r := by
    dsimp only [o]
    cases r
    simp_all [twoProfileOfOuter]
  have hn := hrest mm
  rw [hmm] at hn
  rcases hn with hn | hn
  · have hnec := admissible_two_size_necessary r hr ht
    rw [← heq] at hnec
    have hzero : TwoSizeNecessary (twoProfileOfOuter o r.m 0) := hnec
    exact False.elim (hn hzero)
  · have hbad := hn xx
    rw [hxx] at hbad
    change ¬(twoProfileOfOuter o r.m r.holes).Admissible at hbad
    rw [heq] at hbad
    exact False.elim (hbad hr)

#print axioms energy_one_outer_coverage_check
#print axioms energy_one_profile_mem_cases
end LRX.FinitePeak
