import LRX.ShallowShellSquarePrice
import LRX.ShellPriceIdentity

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def shellH (p : State n) : ℤ :=
  let l := (prefixSourceCore p).card/2
  (l : ℤ)*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|)

noncomputable def shellT (p : State n) : ℤ :=
  let L := (componentSet p 0).card
  let l := (prefixSourceCore p).card/2
  2*(((n : ℤ)-2*(l : ℤ))^2/4)-
    (((positiveSourceFamily p L).map (fun B => (B.size : ℤ)^2)).sum+((n-L : ℕ) : ℤ)^2)

noncomputable def shellE (p : State n) : ℤ :=
  3-(leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)-2*shellH p-(n%2 : ℕ)-shellT p

/-- Manuscript shellE bounds the excess of an actual word of the original
map for every cursor pair. No hypothetical word-price premise is required. -/
theorem exists_shell_excess_word (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ)-(n.choose 2 : ℤ) ≤ shellE p := by
  obtain ⟨w,hw,hl⟩ := exists_shell_square_price_word p hmaj hm hlarge hz start finish
  have he := shell_price_identity n ((prefixSourceCore p).card/2) (NeZero.pos n)
    (∑ i ∈ prefixSourceCore p, |displacement p.symm i|)
    (leftPeak ((canonicalRootPacket p 0)⁻¹) n : ℤ)
    (((positiveSourceFamily p (componentSet p 0).card).map (fun B => (B.size : ℤ)^2)).sum+
      ((n-(componentSet p 0).card : ℕ) : ℤ)^2)
  change _=shellE p at he
  exact ⟨w,hw,by linarith⟩

theorem shell_sharp_word_of_nonpos (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (hpaid : shellE p ≤ 0) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      w.length ≤ n.choose 2 := by
  obtain ⟨w,hw,hl⟩ := exists_shell_excess_word p hmaj hm hlarge hz start finish
  exact ⟨w,hw,by omega⟩

#print axioms exists_shell_excess_word
#print axioms shell_sharp_word_of_nonpos
end LRX.FiniteCuts
