import LRX.PackedSmall8.Block00
import LRX.PackedSmall8.Block01
import LRX.PackedSmall8.Block02
import LRX.PackedSmall8.Block03
import LRX.PackedSmall8.Block04
import LRX.PackedSmall8.Block05
import LRX.PackedSmall8.Block06
import LRX.PackedSmall8.Block07
import LRX.PackedSmall8.Block08
import LRX.PackedSmall8.Block09
import LRX.PackedSmall8.Block10
import LRX.PackedSmall8.Block11
import LRX.PackedSmall8.Block12
import LRX.PackedSmall8.Block13
import LRX.PackedSmall8.Block14
import LRX.PackedSmall8.Block15
import LRX.PackedSmall8.Block16
import LRX.PackedSmall8.Block17
import LRX.PackedSmall8.Block18
import LRX.PackedSmall8.Block19
import LRX.PackedSmall8.Block20
import LRX.PackedSmall8.Block21
import LRX.PackedSmall8.Block22
import LRX.PackedSmall8.Block23
import LRX.PackedSmall8.Block24
import LRX.PackedSmall8.Block25
import LRX.PackedSmall8.Block26
import LRX.PackedSmall8.Block27
import LRX.PackedSmall8.Block28
import LRX.PackedSmall8.Block29
import LRX.PackedSmall8.Block30
import LRX.PackedSmall8.Block31
import LRX.PackedSmall8.Block32
import LRX.PackedSmall8.Block33
import LRX.PackedSmall8.Block34
import LRX.PackedSmall8.Block35
import LRX.PackedSmall8.Block36
import LRX.PackedSmall8.Block37
import LRX.PackedSmall8.Block38
import LRX.PackedSmall8.Block39
import LRX.PackedSmall8.Block40
import LRX.PackedSmall8.Block41
import LRX.PackedSmall8.Block42
import LRX.PackedSmall8.Block43
import LRX.PackedSmall8.Block44
import LRX.PackedSmall8.Block45
import LRX.PackedSmall8.Block46
import LRX.PackedSmall8.Block47
import LRX.PackedSmall8.Block48
import LRX.PackedSmall8.Block49
import LRX.PackedSmall8.Block50
import LRX.PackedSmall8.Block51
import LRX.PackedSmall8.Block52
import LRX.PackedSmall8.Block53
import LRX.PackedSmall8.Block54
import LRX.PackedSmall8.Block55

namespace LRX.PackedSmall8

def table (c : PermCode 8) : List Letter :=
  match c.1.val, c.2.1.val with
  | 0, 0 => Block00.table c.2.2
  | 0, 1 => Block01.table c.2.2
  | 0, 2 => Block02.table c.2.2
  | 0, 3 => Block03.table c.2.2
  | 0, 4 => Block04.table c.2.2
  | 0, 5 => Block05.table c.2.2
  | 0, 6 => Block06.table c.2.2
  | 1, 0 => Block07.table c.2.2
  | 1, 1 => Block08.table c.2.2
  | 1, 2 => Block09.table c.2.2
  | 1, 3 => Block10.table c.2.2
  | 1, 4 => Block11.table c.2.2
  | 1, 5 => Block12.table c.2.2
  | 1, 6 => Block13.table c.2.2
  | 2, 0 => Block14.table c.2.2
  | 2, 1 => Block15.table c.2.2
  | 2, 2 => Block16.table c.2.2
  | 2, 3 => Block17.table c.2.2
  | 2, 4 => Block18.table c.2.2
  | 2, 5 => Block19.table c.2.2
  | 2, 6 => Block20.table c.2.2
  | 3, 0 => Block21.table c.2.2
  | 3, 1 => Block22.table c.2.2
  | 3, 2 => Block23.table c.2.2
  | 3, 3 => Block24.table c.2.2
  | 3, 4 => Block25.table c.2.2
  | 3, 5 => Block26.table c.2.2
  | 3, 6 => Block27.table c.2.2
  | 4, 0 => Block28.table c.2.2
  | 4, 1 => Block29.table c.2.2
  | 4, 2 => Block30.table c.2.2
  | 4, 3 => Block31.table c.2.2
  | 4, 4 => Block32.table c.2.2
  | 4, 5 => Block33.table c.2.2
  | 4, 6 => Block34.table c.2.2
  | 5, 0 => Block35.table c.2.2
  | 5, 1 => Block36.table c.2.2
  | 5, 2 => Block37.table c.2.2
  | 5, 3 => Block38.table c.2.2
  | 5, 4 => Block39.table c.2.2
  | 5, 5 => Block40.table c.2.2
  | 5, 6 => Block41.table c.2.2
  | 6, 0 => Block42.table c.2.2
  | 6, 1 => Block43.table c.2.2
  | 6, 2 => Block44.table c.2.2
  | 6, 3 => Block45.table c.2.2
  | 6, 4 => Block46.table c.2.2
  | 6, 5 => Block47.table c.2.2
  | 6, 6 => Block48.table c.2.2
  | 7, 0 => Block49.table c.2.2
  | 7, 1 => Block50.table c.2.2
  | 7, 2 => Block51.table c.2.2
  | 7, 3 => Block52.table c.2.2
  | 7, 4 => Block53.table c.2.2
  | 7, 5 => Block54.table c.2.2
  | 7, 6 => Block55.table c.2.2
  | _, _ => []

theorem checked : ∀ c : PermCode 8,
    eval (table c)=decode c ∧ (table c).length ≤ Nat.choose 8 2 := by
  intro c
  rcases c with ⟨i0, i1, c⟩
  fin_cases i0 <;> fin_cases i1
  · simpa [table] using Block00.checked c
  · simpa [table] using Block01.checked c
  · simpa [table] using Block02.checked c
  · simpa [table] using Block03.checked c
  · simpa [table] using Block04.checked c
  · simpa [table] using Block05.checked c
  · simpa [table] using Block06.checked c
  · simpa [table] using Block07.checked c
  · simpa [table] using Block08.checked c
  · simpa [table] using Block09.checked c
  · simpa [table] using Block10.checked c
  · simpa [table] using Block11.checked c
  · simpa [table] using Block12.checked c
  · simpa [table] using Block13.checked c
  · simpa [table] using Block14.checked c
  · simpa [table] using Block15.checked c
  · simpa [table] using Block16.checked c
  · simpa [table] using Block17.checked c
  · simpa [table] using Block18.checked c
  · simpa [table] using Block19.checked c
  · simpa [table] using Block20.checked c
  · simpa [table] using Block21.checked c
  · simpa [table] using Block22.checked c
  · simpa [table] using Block23.checked c
  · simpa [table] using Block24.checked c
  · simpa [table] using Block25.checked c
  · simpa [table] using Block26.checked c
  · simpa [table] using Block27.checked c
  · simpa [table] using Block28.checked c
  · simpa [table] using Block29.checked c
  · simpa [table] using Block30.checked c
  · simpa [table] using Block31.checked c
  · simpa [table] using Block32.checked c
  · simpa [table] using Block33.checked c
  · simpa [table] using Block34.checked c
  · simpa [table] using Block35.checked c
  · simpa [table] using Block36.checked c
  · simpa [table] using Block37.checked c
  · simpa [table] using Block38.checked c
  · simpa [table] using Block39.checked c
  · simpa [table] using Block40.checked c
  · simpa [table] using Block41.checked c
  · simpa [table] using Block42.checked c
  · simpa [table] using Block43.checked c
  · simpa [table] using Block44.checked c
  · simpa [table] using Block45.checked c
  · simpa [table] using Block46.checked c
  · simpa [table] using Block47.checked c
  · simpa [table] using Block48.checked c
  · simpa [table] using Block49.checked c
  · simpa [table] using Block50.checked c
  · simpa [table] using Block51.checked c
  · simpa [table] using Block52.checked c
  · simpa [table] using Block53.checked c
  · simpa [table] using Block54.checked c
  · simpa [table] using Block55.checked c

theorem sharp_words : SharpWordBound 8 := words_of_code_certificate table checked

theorem sharp_ediam : (graph 8).ediam ≤ (Nat.choose 8 2 : ℕ∞) :=
  sharp_ediam_of_words sharp_words

#print axioms sharp_words
#print axioms sharp_ediam
end LRX.PackedSmall8
