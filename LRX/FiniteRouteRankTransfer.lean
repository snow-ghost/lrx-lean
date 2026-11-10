import LRX.FiniteServiceRankTransfer
import LRX.ExactServiceRoute
import LRX.FiniteDisplacementSum
import LRX.FiniteCycleScan

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem exact_canonical_route_displacement (ss : List (ExactService n))
    (hd : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : ∀ a ∈ ss, ∀ i, a.displacement i=(a.service.target.symm i : ℤ)-(i : ℤ)) (i : Fin n) :
    (ss.map (fun a => a.displacement i)).sum=
      (((ss.map (fun a : ExactService n => a.service.target)).prod.symm i : Fin n) : ℤ)-(i : ℤ) := by
  let l := ss.map (fun a : ExactService n => a.service.target)
  have hdis : l.Pairwise Equiv.Perm.Disjoint := List.pairwise_map.mpr hd
  have hc := FiniteCuts.displacement_list_prod (l.map (fun p => p⁻¹))
    (FiniteCuts.inverse_targets_disjoint l hdis) i
  rw [FiniteCuts.inverse_cycle_product l hdis] at hc
  have he : ss.map (fun a => a.displacement i)=
      ss.map (fun a => FiniteCuts.displacement a.service.target⁻¹ i) := by
    apply List.map_congr_left
    intro a ha
    exact hcan a ha i
  rw [he]
  simpa only [l,List.map_map,Function.comp_def,FiniteCuts.displacement,Equiv.Perm.inv_def] using hc.symm

end LRX.RotationWords
