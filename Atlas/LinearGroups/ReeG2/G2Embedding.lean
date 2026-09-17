import Atlas.LinearGroups.ReeG2.OctonionCoordinates
import Atlas.LinearGroups.ReeG2.StabilizerFlag

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Extend inverse row multiplication by fixing the scalar coordinate. -/
def octonionLinear (g : Ambient F) :
    Atlas.SplitOctonion.Carrier F ≃ₗ[F] Atlas.SplitOctonion.Carrier F :=
  octonionCoordinates.symm.trans
    (((LinearEquiv.refl F F).prodCongr (rowEquiv g⁻¹)).trans octonionCoordinates)

@[simp] theorem octonionLinear_coordinates (g : Ambient F) (s : F) (v : Vector F) :
    octonionLinear g (octonionCoordinates (s,v)) =
      octonionCoordinates (s,rowEquiv g⁻¹ v) := by
  simp [octonionLinear]

/-- The induced automorphism preserves the actual existing split-octonion product. -/
def octonionAutomorphism (m : ℕ) (g : Model F m) : Atlas.G2.Model F :=
  ⟨octonionLinear g.val, by
    intro x y
    obtain ⟨⟨s,v⟩,rfl⟩ := octonionCoordinates.surjective x
    obtain ⟨⟨t,w⟩,rfl⟩ := octonionCoordinates.surjective y
    rw [← octonionCoordinates_mul]
    simp only [octonionLinear_coordinates]
    rw [← octonionCoordinates_mul]
    apply congrArg octonionCoordinates
    apply Prod.ext
    · simp only [generated_preserves_bilinear m g.val⁻¹ ((generated F m).inv_mem g.property)]
    · simp only [map_add,map_smul]
      rw [generated_preserves_crossProduct m ((generated F m).inv_mem g.property) v w]⟩

@[simp] theorem octonionAutomorphism_coordinates (m : ℕ) (g : Model F m)
    (s : F) (v : Vector F) :
    (octonionAutomorphism m g).val (octonionCoordinates (s,v)) =
      octonionCoordinates (s,rowEquiv g.val⁻¹ v) := octonionLinear_coordinates g.val s v

/-- Concrete structural homomorphism into the actual split-octonion G₂ model. -/
def g2Embedding (m : ℕ) : Model F m →* Atlas.G2.Model F where
  toFun := octonionAutomorphism m
  map_one' := by
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    obtain ⟨⟨s,v⟩,rfl⟩ := octonionCoordinates.surjective x
    change (octonionAutomorphism m 1).val (octonionCoordinates (s,v)) = octonionCoordinates (s,v)
    rw [octonionAutomorphism_coordinates]
    change octonionCoordinates (s,rowEquiv (1 : Ambient F) v) = octonionCoordinates (s,v)
    rw [rowEquiv_one]
  map_mul' g h := by
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    obtain ⟨⟨s,v⟩,rfl⟩ := octonionCoordinates.surjective x
    change (octonionAutomorphism m (g*h)).val (octonionCoordinates (s,v)) =
      (octonionAutomorphism m g).val ((octonionAutomorphism m h).val (octonionCoordinates (s,v)))
    simp only [octonionAutomorphism_coordinates,Subgroup.coe_mul,mul_inv_rev,rowEquiv_mul]

theorem g2Embedding_injective (m : ℕ) : Function.Injective (g2Embedding (F := F) m) := by
  intro g h he
  have hi : g.val⁻¹ = h.val⁻¹ := by
    apply Units.ext
    ext i j
    have hv := congrArg (fun k : Atlas.G2.Model F => k.val
      (octonionCoordinates (0,coordinateVector i))) he
    change (octonionAutomorphism m g).val (octonionCoordinates (0,coordinateVector i)) =
      (octonionAutomorphism m h).val (octonionCoordinates (0,coordinateVector i)) at hv
    simp only [octonionAutomorphism_coordinates] at hv
    have hh := congrArg Prod.snd (octonionCoordinates.injective hv)
    simpa only [rowEquiv_coordinateVector] using congrFun hh j
  exact Subtype.ext (inv_inj.mp hi)

end Atlas.ReeG2
