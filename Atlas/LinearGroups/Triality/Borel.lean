import Atlas.LinearGroups.Triality.TorusAction

/-! The actual product of the positive unipotent group and diagonal torus. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def borelWord (p : PositiveParameters F K) (h : Kˣ × Fˣ) : O_DPlus 4 K :=
  positiveMatrix F K p * torusMap F K h

theorem borelWord_mul (hdeg : Module.finrank F K = 3)
    (p r : PositiveParameters F K) (h k : Kˣ × Fˣ) :
    borelWord F K p h * borelWord F K r k =
      borelWord F K (positiveCollect F K p (torusScale F K h r)) (h*k) := by
  simp only [borelWord]
  calc
    _ = positiveMatrix F K p * (torusMap F K h * positiveMatrix F K r) * torusMap F K k := by group
    _ = (positiveMatrix F K p * positiveMatrix F K (torusScale F K h r)) *
        (torusMap F K h * torusMap F K k) := by rw [torus_positive_intertwine F K hdeg]; group
    _ = _ := by rw [positiveMatrix_mul F K hdeg, ←map_mul]

theorem borelWord_entry_a (p : PositiveParameters F K) (h : Kˣ × Fˣ) :
    (borelWord F K p h).val (e 0) (.inl 0) = (h.1 : K) := by
  simp [borelWord, positiveMatrix, Subgroup.coe_mul, LinearEquiv.mul_apply,
    positiveWord_apply, positiveAction, torusMap, torusWeights,
    diagonalEmbedding, diagonalLinear, e]

theorem borelWord_entry_b (p : PositiveParameters F K) (h : Kˣ × Fˣ) :
    (borelWord F K p h).val (e 1) (.inl 1) = algebraMap F K (h.2 : F) / (h.1 : K) := by
  simp [borelWord, positiveMatrix, Subgroup.coe_mul, LinearEquiv.mul_apply,
    positiveWord_apply, positiveAction, torusMap, torusWeights,
    diagonalEmbedding, diagonalLinear, baseUnit, e]

theorem borelWord_injective : Function.Injective (fun p : PositiveParameters F K × (Kˣ × Fˣ) =>
    borelWord F K p.1 p.2) := by
  rintro ⟨p,h⟩ ⟨r,k⟩ he
  have ha := congrArg (fun g : O_DPlus 4 K => g.val (e 0) (.inl 0)) he
  simp only [borelWord_entry_a] at ha
  have hb := congrArg (fun g : O_DPlus 4 K => g.val (e 1) (.inl 1)) he
  simp only [borelWord_entry_b,←ha] at hb
  have hk : h=k := by
    apply Prod.ext (Units.ext ha)
    apply Units.ext
    apply (algebraMap F K).injective
    exact (div_left_inj' h.1.ne_zero).mp hb
  subst k
  have hp : p=r := positiveMatrix_injective F K (mul_right_cancel he)
  exact Prod.ext hp rfl

def borelMonoid (hdeg : Module.finrank F K = 3) : Submonoid (O_DPlus 4 K) where
  carrier := Set.range (fun p : PositiveParameters F K × (Kˣ × Fˣ) => borelWord F K p.1 p.2)
  one_mem' := ⟨(⟨0,0,0,0,0,0⟩,1),by simp [borelWord,positiveMatrix_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨⟨p,h⟩,rfl⟩ ⟨⟨r,k⟩,rfl⟩
    exact ⟨(positiveCollect F K p (torusScale F K h r),h*k),(borelWord_mul F K hdeg p r h k).symm⟩

def borel (hdeg : Module.finrank F K = 3) : Subgroup (O_DPlus 4 K) where
  __ := borelMonoid F K hdeg
  inv_mem' := by
    intro g hg
    let S := borelMonoid F K hdeg
    let f : S → S := fun x => ⟨g*x.val,S.mul_mem hg x.property⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    obtain ⟨x,hx⟩ := (Finite.surjective_of_injective hf) (1 : S)
    have he : g*x.val=1 := congrArg Subtype.val hx
    have hi : x.val=g⁻¹ := by
      calc
        x.val = g⁻¹*(g*x.val) := by group
        _ = g⁻¹ := by rw [he,mul_one]
    exact hi ▸ x.property

def borelCoordinates (hdeg : Module.finrank F K = 3) :
    (PositiveParameters F K × (Kˣ × Fˣ)) ≃ borel F K hdeg :=
  Equiv.ofBijective (fun p => ⟨borelWord F K p.1 p.2,⟨p,rfl⟩⟩) ⟨
    fun _ _ h => borelWord_injective F K (congrArg Subtype.val h),
    by rintro ⟨g,p,hp⟩; exact ⟨p,Subtype.ext hp⟩⟩

theorem borel_le_generated (hdeg : Module.finrank F K = 3) :
    borel F K hdeg ≤ generated F K := by
  rintro _ ⟨⟨p,h⟩,rfl⟩
  exact Subgroup.mul_mem _ (positiveWord_mem F K p.a p.b p.c p.d p.u p.v)
    (torus_le_generated F K ⟨h,rfl⟩)

theorem card_borel (hdeg : Module.finrank F K = 3) :
    Nat.card (borel F K hdeg) = Nat.card F^12 * (Nat.card F^3-1) * (Nat.card F-1) := by
  rw [←Nat.card_congr (borelCoordinates F K hdeg),Nat.card_prod,
    Nat.card_congr (unipotentCoordinates F K hdeg),card_unipotent F K hdeg,
    Nat.card_prod,Nat.card_units,Nat.card_units,FiniteCubic.card_extension hdeg]
  ring

end Atlas.Triality
