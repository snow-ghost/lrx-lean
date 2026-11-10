import LRX.TwoSizeCertificate

namespace LRX.FinitePeak

def highEnergyTwoRows : List OuterRow :=
  twoOuterRows.filter (fun o => decide (2 ≤ o.2.2.1 ∧ o.2.2.2.2.2 ≤ 7))

end LRX.FinitePeak
