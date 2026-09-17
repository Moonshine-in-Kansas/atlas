import Atlas.Codes.TernaryGolay

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Codes

def ternaryDiagonal (d w : TernaryWord) : TernaryWord := fun i => d i * w i

theorem ternaryGolay_mem_iff_decode (w : TernaryWord) :
    w ∈ ternaryGolay ↔ ternaryEncoder (ternaryDecoder w) = w := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [ternary_decode_encode]
  · intro h
    exact ⟨ternaryDecoder w, h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A bounded six-basis-word calculation identifies all diagonal code endomorphisms. -/
theorem ternaryDiagonal_basis_check : ∀ p : TernaryParameters,
    (∀ j : Fin 6, ternaryEncoder (ternaryDecoder (ternaryDiagonal (ternaryEncoder p)
      (ternaryEncoder (Pi.single j 1)))) = ternaryDiagonal (ternaryEncoder p)
      (ternaryEncoder (Pi.single j 1))) →
    ∀ i : Fin 12, ternaryEncoder p i = ternaryEncoder p 0 := by
  decide +kernel

theorem ternaryDiagonal_preserves_iff (d : TernaryWord) :
    (∀ w ∈ ternaryGolay, ternaryDiagonal d w ∈ ternaryGolay) ↔
      ∃ a : ZMod 3, d = fun _ => a := by
  constructor
  · intro h
    have hd : d ∈ ternaryGolay := by
      have he : ternaryDiagonal d (fun _ => 1) = d := by
        funext i; simp [ternaryDiagonal]
      exact he ▸ h (fun _ => 1) ternaryGolay_one
    obtain ⟨p, rfl⟩ := hd
    refine ⟨ternaryEncoder p 0, funext (ternaryDiagonal_basis_check p ?_)⟩
    intro j
    exact (ternaryGolay_mem_iff_decode _).mp
      (h _ (show ternaryEncoder (Pi.single j 1) ∈ ternaryGolay from ⟨_, rfl⟩))
  · rintro ⟨a, rfl⟩ w hw
    exact ternaryGolay.smul_mem a hw

theorem ternaryDiagonal_automorphism_scalars (d : TernaryWord)
    (hn : ∀ i, d i ≠ 0)
    (hp : ∀ w ∈ ternaryGolay, ternaryDiagonal d w ∈ ternaryGolay) :
    d = (fun _ => 1) ∨ d = (fun _ => -1) := by
  obtain ⟨a, rfl⟩ := (ternaryDiagonal_preserves_iff d).mp hp
  have h : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
  rcases h a (hn 0) with h | h <;> simp [h]

end Atlas.Codes
