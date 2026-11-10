module

public import LRX.TwoSizeCertificate

@[expose] public section

namespace LRX.FinitePeak

/-- Remaining exterior geometries after the complete scalar exclusion. -/
def energyOneOuterRows : List OuterRow := [
  (0,0,1,0,3,4), (0,1,1,0,4,5), (0,1,1,0,4,6),
  (0,2,1,0,4,6), (0,2,1,0,5,6), (0,2,1,0,5,7)]

def boundedEnergyOneRows : List OuterRow :=
  twoOuterRows.filter (fun o => decide (o.2.2.1=1 ∧ o.2.2.2.2.2 ≤ 7))

end LRX.FinitePeak
