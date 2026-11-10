import LRX.NineShellChunks.Prefix00
import LRX.NineShellChunks.Prefix01
import LRX.NineShellChunks.Prefix02
import LRX.NineShellChunks.Prefix03
import LRX.NineShellChunks.Prefix04
import LRX.NineShellChunks.Prefix10
import LRX.NineShellChunks.Prefix11
import LRX.NineShellChunks.Prefix12
import LRX.NineShellChunks.Prefix13
import LRX.NineShellChunks.Prefix14
import LRX.NineShellChunks.Prefix20
import LRX.NineShellChunks.Prefix21
import LRX.NineShellChunks.Prefix22
import LRX.NineShellChunks.Prefix23
import LRX.NineShellChunks.Prefix24
import LRX.NineShellChunks.Prefix30
import LRX.NineShellChunks.Prefix31
import LRX.NineShellChunks.Prefix32
import LRX.NineShellChunks.Prefix33
import LRX.NineShellChunks.Prefix34
import LRX.NineShellChunks.Prefix40
import LRX.NineShellChunks.Prefix41
import LRX.NineShellChunks.Prefix42
import LRX.NineShellChunks.Prefix43
import LRX.NineShellChunks.Prefix44
import LRX.NineShellChunks.Prefix50
import LRX.NineShellChunks.Prefix51
import LRX.NineShellChunks.Prefix52
import LRX.NineShellChunks.Prefix53
import LRX.NineShellChunks.Prefix54

namespace LRX.NineShellCertificate
open FiniteCuts FiniteWindow RotationWords
open scoped BigOperators
theorem checked : ∀ c : PermCode 6, Eligible (decode c) → ∀ start finish : Fin 9,
    eval (table c start finish)=(rotation start)⁻¹*target (decode c)*rotation finish ∧
      (table c start finish).length ≤ 36 := by
  rintro ⟨i,j,c⟩
  fin_cases i <;> fin_cases j
  · exact code_prefix_0_0 c
  · exact code_prefix_0_1 c
  · exact code_prefix_0_2 c
  · exact code_prefix_0_3 c
  · exact code_prefix_0_4 c
  · exact code_prefix_1_0 c
  · exact code_prefix_1_1 c
  · exact code_prefix_1_2 c
  · exact code_prefix_1_3 c
  · exact code_prefix_1_4 c
  · exact code_prefix_2_0 c
  · exact code_prefix_2_1 c
  · exact code_prefix_2_2 c
  · exact code_prefix_2_3 c
  · exact code_prefix_2_4 c
  · exact code_prefix_3_0 c
  · exact code_prefix_3_1 c
  · exact code_prefix_3_2 c
  · exact code_prefix_3_3 c
  · exact code_prefix_3_4 c
  · exact code_prefix_4_0 c
  · exact code_prefix_4_1 c
  · exact code_prefix_4_2 c
  · exact code_prefix_4_3 c
  · exact code_prefix_4_4 c
  · exact code_prefix_5_0 c
  · exact code_prefix_5_1 c
  · exact code_prefix_5_2 c
  · exact code_prefix_5_3 c
  · exact code_prefix_5_4 c

theorem sharp_word (f : State 6) (hf : Eligible f) (start finish : Fin 9) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*target f*rotation finish ∧ w.length ≤ 36 := by
  obtain ⟨he,hl⟩ := checked (encode f) (by simpa only [decode_encode] using hf) start finish
  exact ⟨table (encode f) start finish,by simpa only [decode_encode] using he,hl⟩

#print axioms sharp_word
end LRX.NineShellCertificate
