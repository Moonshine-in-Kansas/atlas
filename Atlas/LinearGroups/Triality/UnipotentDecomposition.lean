import Atlas.LinearGroups.Triality.ParabolicGenerators

/-! Decomposition along either simple root and its concrete radical. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def shortRootInUnipotent (t : K) : unipotent F K hdeg :=
  unipotentCoordinates F K hdeg ⟨t,0,0,0,0,0⟩

theorem shortRootInUnipotent_val (t : K) :
    (shortRootInUnipotent F K hdeg t).val = shortRoot F K t :=
  positiveMatrix_short F K t

theorem shortCoordinate_root (t : K) :
    shortCoordinate F K hdeg (shortRootInUnipotent F K hdeg t) = Multiplicative.ofAdd t := by
  simp [shortRootInUnipotent, shortCoordinate, unipotentParameters]

theorem unipotent_short_decomposition (u : unipotent F K hdeg) :
    ∃ t : K, ∃ r : shortRadical F K hdeg, u.val = r.val * shortRoot F K t := by
  let t := (unipotentParameters F K hdeg u).a
  let x := shortRootInUnipotent F K hdeg t
  let r : unipotent F K hdeg := u*x⁻¹
  have hr : r ∈ shortRadicalKernel F K hdeg := by
    change shortCoordinate F K hdeg (u*x⁻¹) = 1
    rw [map_mul,map_inv,shortCoordinate_root]
    change Multiplicative.ofAdd t * (Multiplicative.ofAdd t)⁻¹ = 1
    exact mul_inv_cancel _
  refine ⟨t,⟨r.val,⟨r,hr,rfl⟩⟩,?_⟩
  change u.val = (u.val*x.val⁻¹)*shortRoot F K t
  rw [show x.val = shortRoot F K t from shortRootInUnipotent_val F K hdeg t]
  group

theorem borel_short_decomposition (g : borel F K hdeg) :
    ∃ r : shortRadical F K hdeg, ∃ t : K, ∃ h : Kˣ × Fˣ,
      g.val = r.val * shortRoot F K t * torusMap F K h := by
  obtain ⟨⟨p,h⟩,hp⟩ := g.property
  obtain ⟨t,r,hr⟩ := unipotent_short_decomposition F K hdeg (unipotentCoordinates F K hdeg p)
  refine ⟨r,t,h,?_⟩
  change positiveMatrix F K p = r.val * shortRoot F K t at hr
  rw [← hp]
  change positiveMatrix F K p * torusMap F K h = _
  rw [hr]

def longRootInUnipotent (t : F) : unipotent F K hdeg :=
  unipotentCoordinates F K hdeg ⟨0,t,0,0,0,0⟩

theorem longRootInUnipotent_val (t : F) :
    (longRootInUnipotent F K hdeg t).val = longRoot F K t :=
  positiveMatrix_long F K t

theorem longCoordinate_root (t : F) :
    longCoordinate F K hdeg (longRootInUnipotent F K hdeg t) = Multiplicative.ofAdd t := by
  simp [longRootInUnipotent, longCoordinate, unipotentParameters]

theorem unipotent_long_decomposition (u : unipotent F K hdeg) :
    ∃ t : F, ∃ r : longRadical F K hdeg, u.val = r.val * longRoot F K t := by
  let t := (unipotentParameters F K hdeg u).b
  let x := longRootInUnipotent F K hdeg t
  let r : unipotent F K hdeg := u*x⁻¹
  have hr : r ∈ longRadicalKernel F K hdeg := by
    change longCoordinate F K hdeg (u*x⁻¹) = 1
    rw [map_mul,map_inv,longCoordinate_root]
    change Multiplicative.ofAdd t * (Multiplicative.ofAdd t)⁻¹ = 1
    exact mul_inv_cancel _
  refine ⟨t,⟨r.val,⟨r,hr,rfl⟩⟩,?_⟩
  change u.val = (u.val*x.val⁻¹)*longRoot F K t
  rw [show x.val = longRoot F K t from longRootInUnipotent_val F K hdeg t]
  group

theorem borel_long_decomposition (g : borel F K hdeg) :
    ∃ r : longRadical F K hdeg, ∃ t : F, ∃ h : Kˣ × Fˣ,
      g.val = r.val * longRoot F K t * torusMap F K h := by
  obtain ⟨⟨p,h⟩,hp⟩ := g.property
  obtain ⟨t,r,hr⟩ := unipotent_long_decomposition F K hdeg (unipotentCoordinates F K hdeg p)
  refine ⟨r,t,h,?_⟩
  change positiveMatrix F K p = r.val * longRoot F K t at hr
  rw [← hp]
  change positiveMatrix F K p * torusMap F K h = _
  rw [hr]

end Atlas.Triality
