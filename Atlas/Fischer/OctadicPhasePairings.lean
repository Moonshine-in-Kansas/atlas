import Atlas.Fischer.OctadicExteriorPairings

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Full shortened-code orthogonality for arbitrary actual additive characters. -/
theorem octadicCharacter_pair_sum (O : Octad) (χ ψ : OctadicCharacter O) :
    (∑ b : octadShortenedCode O, parkerScalarSign (χ b)*parkerScalarSign (ψ b)) =
      if χ=ψ then (32 : Scalar) else 0 := by
  have hz : (χ+ψ).toAddMonoidHom=0 ↔ χ=ψ := by
    constructor
    · intro h
      ext b
      have hb := congrArg (fun f : octadShortenedCode O →+ Bit => f b) h
      change χ b+ψ b=0 at hb
      exact (show ∀ a b : Bit, a+b=0 → a=b from by decide) _ _ hb
    · intro h; subst ψ
      ext b
      exact CharTwo.add_self_eq_zero (χ b)
  simp_rw [← parkerScalarSign_add]
  change (∑ b,parkerScalarSign ((χ+ψ).toAddMonoidHom b))=_
  rw [parkerScalarSign_sum]
  have hc : Fintype.card (octadShortenedCode O)=32 := by
    rw [← Nat.card_eq_fintype_card,octadShortenedCode_card]
  norm_num only [hz,hc,Nat.cast_ofNat]

theorem octadicCharacter_hyperplane_pair_sum (O : Octad) (χ ψ : OctadicCharacter O) :
    (∑ b : OctadShortenedHyperplane O, parkerScalarSign (χ b.val)*parkerScalarSign (ψ b.val)) =
      (if χ=ψ then (32 : Scalar) else 0)-1-
        parkerScalarSign (χ (octadShortenedOne O)+ψ (octadShortenedOne O)) := by
  let F (b : octadShortenedCode O) := parkerScalarSign (χ b)*parkerScalarSign (ψ b)
  have he : (∑ b : OctadShortenedHyperplane O,F b.val)=
      ∑ b ∈ ({0,octadShortenedOne O}ᶜ : Finset (octadShortenedCode O)),F b := by
    symm
    apply Finset.sum_subtype
    intro b
    simp only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or]
  change (∑ b : OctadShortenedHyperplane O,F b.val)=_
  rw [he]
  have ht := Finset.sum_compl_add_sum (s := {0,octadShortenedOne O}) F
  have hn : (0 : octadShortenedCode O) ∉ ({octadShortenedOne O} : Finset _) := by
    simpa only [Finset.mem_singleton] using Ne.symm (octadShortenedOne_ne_zero O)
  rw [Finset.sum_insert hn,Finset.sum_singleton] at ht
  have hz : F 0=1 := by simp [F,parkerScalarSign]
  have hX : F (octadShortenedOne O)=
      parkerScalarSign (χ (octadShortenedOne O)+ψ (octadShortenedOne O)) :=
    (parkerScalarSign_add _ _).symm
  have hf : (∑ b,F b)=if χ=ψ then (32 : Scalar) else 0 := octadicCharacter_pair_sum O χ ψ
  rw [hz,hX,hf] at ht
  linear_combination ht

/-- Exact pairing of the actual octadic roots: parity controls all off-diagonal
entries. Derived from the literal coordinate formula and character sums. -/
theorem octadicRoot_pairing {O : Octad} (Q : OctadCalibration O) (χ ψ : OctadicCharacter O) :
    hermitian (octadicRoot Q χ) (octadicRoot Q ψ)=
      if χ=ψ then 9 else if χ (octadShortenedOne O)=ψ (octadShortenedOne O) then 1 else 0 := by
  by_cases he : χ=ψ
  · subst ψ
    rw [if_pos rfl,octadicRoot_norm]
  rw [if_neg he]
  let T (χ : OctadicCharacter O) :=
    (theta*parkerScalarSign (χ (octadShortenedOne O))) • signedOctadVector Q.octadLift
  have hUT (χ : OctadicCharacter O) : hermitian (octadicAxisPart O) (T χ)=0 := by
    simp only [T,hermitian_smul_right,hermitian_octadicAxis_signedOctad,mul_zero]
  have hTY (χ ψ : OctadicCharacter O) : hermitian (T χ) (octadicHyperplanePart Q ψ)=0 := by
    dsimp only [T]
    rw [hermitian_smul_left,hermitian_octad_hyperplanePart,mul_zero]
  have hTU (χ : OctadicCharacter O) : hermitian (T χ) (octadicAxisPart O)=0 := by
    rw [← hermitian_star,hUT,star_zero]
  have hYU (χ : OctadicCharacter O) : hermitian (octadicHyperplanePart Q χ) (octadicAxisPart O)=0 := by
    rw [← hermitian_star,hermitian_octadicAxis_hyperplanePart,star_zero]
  have hYT (χ ψ : OctadicCharacter O) : hermitian (octadicHyperplanePart Q χ) (T ψ)=0 := by
    rw [← hermitian_star,hTY,star_zero]
  change hermitian ((1/2 : Scalar) • (octadicAxisPart O+T χ+octadicHyperplanePart Q χ))
    ((1/2 : Scalar) • (octadicAxisPart O+T ψ+octadicHyperplanePart Q ψ))=_
  rw [hermitian_smul_left,hermitian_smul_right]
  simp only [hermitian_add_left,hermitian_add_right,hUT,hTU,hTY,hYT,hYU,
    hermitian_octadicAxis_hyperplanePart,octadicAxisPart_norm,hermitian_hyperplanePart_pair,
    octadicCharacter_hyperplane_pair_sum,he,ite_false]
  simp only [T,hermitian_smul_left,hermitian_smul_right,signedOctadVector_norm,
    star_mul,parkerScalarSign_star,theta_conjugate,mul_one]
  have ht := theta_sq
  have hb : ∀ b : Bit,b=0 ∨ b=1 := by decide
  rcases hb (χ (octadShortenedOne O)) with hχ | hχ <;>
    rcases hb (ψ (octadShortenedOne O)) with hψ | hψ <;>
    norm_num [hχ,hψ,parkerScalarSign] <;> ring_nf <;> norm_num [theta_sq]

end Atlas.Fischer
