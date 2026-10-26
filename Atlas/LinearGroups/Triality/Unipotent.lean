import Atlas.LinearGroups.Triality.PositiveCollection

/-! The actual positive unipotent subgroup, with unique parameters and independent order. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def positiveParametersEquiv : PositiveParameters F K ≃ (K × K × K) × (F × F × F) where
  toFun p := ((p.a,p.c,p.d),(p.b,p.u,p.v))
  invFun p := ⟨p.1.1,p.2.1,p.1.2.1,p.1.2.2,p.2.2.1,p.2.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨⟨a,c,d⟩,⟨b,u,v⟩⟩; rfl

theorem positiveMatrix_injective : Function.Injective (positiveMatrix F K) := by
  rintro ⟨a,b,c,d,u,v⟩ ⟨a',b',c',d',u',v'⟩ h
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := positiveWord_injective F K a a' b b' c c' d d' u u' v v' h
  rfl

theorem positiveMatrix_zero : positiveMatrix F K ⟨0,0,0,0,0,0⟩ = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (positiveWord F K 0 0 0 0 0 0).val x = x
  rw [positiveWord_apply]
  ext k
  rcases k with k|k <;> fin_cases k <;> simp [positiveAction]

def positiveMonoid (hdeg : Module.finrank F K = 3) : Submonoid (O_DPlus 4 K) where
  carrier := Set.range (positiveMatrix F K)
  one_mem' := ⟨⟨0,0,0,0,0,0⟩,positiveMatrix_zero F K⟩
  mul_mem' := by
    rintro _ _ ⟨p,rfl⟩ ⟨r,rfl⟩
    exact ⟨positiveCollect F K p r,(positiveMatrix_mul F K hdeg p r).symm⟩

theorem positiveMonoid_inv_mem (hdeg : Module.finrank F K = 3) (g : O_DPlus 4 K)
    (hg : g ∈ positiveMonoid F K hdeg) : g⁻¹ ∈ positiveMonoid F K hdeg := by
  let S := positiveMonoid F K hdeg
  let f : S → S := fun x => ⟨g*x.val, S.mul_mem hg x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h)
  obtain ⟨x,hx⟩ := (Finite.surjective_of_injective hf) (1 : S)
  have he : g*x.val=1 := congrArg Subtype.val hx
  have hi : x.val=g⁻¹ := by
    calc
      x.val = g⁻¹*(g*x.val) := by group
      _ = g⁻¹ := by rw [he,mul_one]
  exact hi ▸ x.property

/-- The carrier consists exactly of the six ordered relative-root factors. -/
def unipotent (hdeg : Module.finrank F K = 3) : Subgroup (O_DPlus 4 K) where
  __ := positiveMonoid F K hdeg
  inv_mem' := positiveMonoid_inv_mem F K hdeg _

def unipotentCoordinates (hdeg : Module.finrank F K = 3) :
    PositiveParameters F K ≃ unipotent F K hdeg :=
  Equiv.ofBijective (fun p => ⟨positiveMatrix F K p,⟨p,rfl⟩⟩) ⟨
    fun _ _ h => positiveMatrix_injective F K (congrArg Subtype.val h),
    by rintro ⟨g,p,hp⟩; exact ⟨p,Subtype.ext hp⟩⟩

theorem unipotent_le_generated (hdeg : Module.finrank F K = 3) :
    unipotent F K hdeg ≤ generated F K := by
  rintro _ ⟨p,rfl⟩
  exact positiveWord_mem F K p.a p.b p.c p.d p.u p.v

/-- Independent positive-unipotent count from the actual matrix coordinates. -/
theorem card_unipotent (hdeg : Module.finrank F K = 3) :
    Nat.card (unipotent F K hdeg) = Nat.card F ^ 12 := by
  rw [← Nat.card_congr (unipotentCoordinates F K hdeg),
    Nat.card_congr (positiveParametersEquiv F K)]
  simp only [Nat.card_prod]
  rw [FiniteCubic.card_extension hdeg]
  ring

end Atlas.Triality
