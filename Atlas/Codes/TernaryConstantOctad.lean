import Atlas.Codes.TernaryBinaryOctadLift
import Atlas.Codes.TernaryGolayConstantGenerators

namespace Atlas.Codes

/-- The point in the complementary dodecad associated to the all-one ternary word. -/
def ternaryConstantPoint : Omega := ((2,0),0)

def TernaryConstantSign (w : TernaryWord) : Prop :=
  (∀ i, w i = 0 ∨ w i = 1) ∨ (∀ i, w i = 0 ∨ w i = -1)

instance (w : TernaryWord) : Decidable (TernaryConstantSign w) := inferInstanceAs
  (Decidable ((∀ i, w i = 0 ∨ w i = 1) ∨ (∀ i, w i = 0 ∨ w i = -1)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- A marked comparison of the 264 weight-six codewords with their actual binary octads.
theorem ternaryConstantOctad_check : ∀ p : TernaryParameters,
    ternaryWeight (ternaryEncoder p) = 6 →
      (ternaryBinaryOctadWord (ternaryEncoder p) ternaryConstantPoint = 1 ↔
        TernaryConstantSign (ternaryEncoder p)) := by
  decide +kernel

theorem ternaryConstantOctad_iff (w : TernaryWord) (hw : w ∈ ternaryGolay)
    (h6 : ternaryWeight w = 6) :
    ternaryBinaryOctadWord w ternaryConstantPoint = 1 ↔ TernaryConstantSign w := by
  obtain ⟨p,rfl⟩ := hw
  exact ternaryConstantOctad_check p h6

def ternarySupportIndicator (B : Finset (Fin 12)) : TernaryWord :=
  fun i => if i ∈ B then 1 else 0

theorem ternarySupportIndicator_support (B : Finset (Fin 12)) :
    ternarySupport (ternarySupportIndicator B) = B := by
  ext i
  simp [ternarySupportIndicator, ternarySupport]

theorem ternarySupportIndicator_weight (B : Finset (Fin 12)) :
    ternaryWeight (ternarySupportIndicator B) = B.card := by
  rw [← ternarySupport_card, ternarySupportIndicator_support]

theorem ternarySupportIndicator_constant (B : Finset (Fin 12)) :
    TernaryConstantSign (ternarySupportIndicator B) := by
  left
  intro i
  simp only [ternarySupportIndicator]
  split_ifs <;> simp

theorem ternaryConstantSign_indicator (w : TernaryWord) (hw : w ∈ ternaryGolay)
    (hc : TernaryConstantSign w) : ternarySupportIndicator (ternarySupport w) ∈ ternaryGolay := by
  rcases hc with hc | hc
  · have he : ternarySupportIndicator (ternarySupport w) = w := by
      funext i
      rcases hc i with h | h <;> simp [ternarySupportIndicator, ternarySupport,h]
    rw [he]; exact hw
  · have he : ternarySupportIndicator (ternarySupport w) = -w := by
      funext i
      rcases hc i with h | h <;> simp [ternarySupportIndicator, ternarySupport,h]
    rw [he]; exact ternaryGolay.neg_mem hw

end Atlas.Codes
