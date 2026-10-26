import Atlas.LinearGroups.Triality.BruhatIntersectionExact

/-! Bijection for the full Borel intersection, including its torus factor. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def borelIntersection (w : Fin 12) : Subgroup (O_DPlus 4 K) :=
  borel F K hdeg ⊓ (borel F K hdeg).comap (MulAut.conj ((weylLift F K w)⁻¹)).toMonoidHom

theorem mem_borelIntersection (w : Fin 12) (g : O_DPlus 4 K) :
    g ∈ borelIntersection F K hdeg w ↔ g ∈ borel F K hdeg ∧
      (weylLift F K w)⁻¹*g*weylLift F K w ∈ borel F K hdeg := by
  simp [borelIntersection,MulAut.conj_apply]

def borelIntersectionMap (w : Fin 12)
    (p : {p : PositiveParameters F K // SurvivingParameters F K w p} × (Kˣ × Fˣ)) :
    borelIntersection F K hdeg w :=
  ⟨borelWord F K p.1.val p.2, (mem_borelIntersection F K hdeg w _).mpr
    ⟨⟨(p.1.val,p.2),rfl⟩,(borelWord_conjugate_iff F K hdeg w _ _).mpr p.1.property⟩⟩

theorem borelIntersectionMap_bijective (w : Fin 12) :
    Function.Bijective (borelIntersectionMap F K hdeg w) := by
  constructor
  · intro p r he
    have hh := congrArg Subtype.val he
    change borelWord F K p.1.val p.2 = borelWord F K r.1.val r.2 at hh
    have hi : (p.1.val,p.2) = (r.1.val,r.2) := by
      apply borelWord_injective F K
      exact hh
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hi
    · exact congrArg (fun x : PositiveParameters F K × (Kˣ × Fˣ) => x.2) hi
  · intro g
    obtain ⟨hg,hc⟩ := (mem_borelIntersection F K hdeg w g.val).mp g.property
    obtain ⟨⟨p,h⟩,he⟩ := hg
    change borelWord F K p h=g.val at he
    have hp : SurvivingParameters F K w p := by
      apply (borelWord_conjugate_iff F K hdeg w p h).mp
      rw [he]
      exact hc
    exact ⟨(⟨p,hp⟩,h),Subtype.ext he⟩

def borelIntersectionCoordinates (w : Fin 12) :
    ({p : PositiveParameters F K // SurvivingParameters F K w p} × (Kˣ × Fˣ)) ≃
      borelIntersection F K hdeg w :=
  Equiv.ofBijective _ (borelIntersectionMap_bijective F K hdeg w)

end Atlas.Triality
