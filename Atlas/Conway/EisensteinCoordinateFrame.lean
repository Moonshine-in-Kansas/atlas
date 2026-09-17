import Atlas.Conway.EisensteinCoordinateIsometries
import Atlas.Lattices.EisensteinMonomialAxes

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

abbrev eisensteinFrameScale : EisensteinRational := eisensteinToRational (3*eisensteinTheta)

def eisensteinFrameVector (p : Fin 12 × Eisensteinˣ) : EisensteinRationalCoordinates :=
  Pi.single p.1 (eisensteinFrameScale*eisensteinToRational (p.2 : Eisenstein))

def eisensteinCoordinateFrame : Set EisensteinRationalCoordinates := Set.range eisensteinFrameVector

/-- The full stabilizer of the 72 actual coordinate-frame vectors in the full
scalar-linear Hermitian lattice group. No monomial condition enters its definition. -/
def eisensteinCoordinateFrameStabilizer : Subgroup eisensteinHermitianGroup where
  carrier := {f | ∀ z, z ∈ eisensteinCoordinateFrame ↔ f.val z ∈ eisensteinCoordinateFrame}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro f g hf hg z
    exact (hg z).trans (hf (g.val z))
  inv_mem' := by
    intro f hf z
    have h := hf (f.val.symm z)
    change z ∈ eisensteinCoordinateFrame ↔ f.val.symm z ∈ eisensteinCoordinateFrame
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem eisensteinFrameVector_mem_lattice (p : Fin 12 × Eisensteinˣ) :
    eisensteinFrameVector p ∈ rationalEisensteinLattice :=
  (rationalEisensteinLattice_axis_iff _ _).mpr ⟨p.2,rfl⟩

theorem eisensteinFrameVector_injective : Function.Injective eisensteinFrameVector := by
  rintro ⟨i,u⟩ ⟨j,v⟩ h
  have hc (u : Eisensteinˣ) : eisensteinFrameScale*eisensteinToRational (u : Eisenstein) ≠ 0 :=
    mul_ne_zero eisensteinAxisScale_ne_zero ((u.isUnit.map eisensteinToRational).ne_zero)
  have hij : i=j := by
    by_contra hij
    have he := congrFun h i
    have hz : eisensteinFrameScale*eisensteinToRational (u : Eisenstein) = 0 := by
      simpa [eisensteinFrameVector,Pi.single_apply,hij] using he
    exact hc u hz
  subst j
  have huv : u=v := by
    apply Units.ext
    apply eisensteinToRational_injective
    apply mul_left_cancel₀ eisensteinAxisScale_ne_zero
    have he := congrFun h i
    simpa [eisensteinFrameVector] using he
  exact Prod.ext rfl huv

theorem eisensteinCoordinateFrame_card : Nat.card eisensteinCoordinateFrame = 72 := by
  have he := Equiv.ofInjective eisensteinFrameVector eisensteinFrameVector_injective
  change Nat.card (Set.range eisensteinFrameVector) = 72
  rw [← Nat.card_congr he,Nat.card_prod,eisenstein_units_card]
  norm_num [Nat.card_eq_fintype_card]

/-- Every full frame stabilizer is forced to be unit monomial by its images on
the twelve frame axes and scalar linearity. -/
theorem eisensteinCoordinateFrame_is_monomial (f : eisensteinCoordinateFrameStabilizer) :
    ∃ u : Fin 12 → Eisensteinˣ, ∃ σ : Equiv.Perm (Fin 12),
      ∀ z i, f.val.val z i = eisensteinToRational (u i : Eisenstein)*z (σ.symm i) := by
  have himg (i : Fin 12) : ∃ p : Fin 12 × Eisensteinˣ,
      f.val.val (Pi.single i eisensteinFrameScale) = eisensteinFrameVector p := by
    have hmem : Pi.single i eisensteinFrameScale ∈ eisensteinCoordinateFrame := by
      refine ⟨(i,1),?_⟩
      simp [eisensteinFrameVector]
    obtain ⟨p,hp⟩ := (f.prop _).mp hmem
    exact ⟨p,hp.symm⟩
  choose p hp using himg
  have hb (i : Fin 12) : f.val.val (Pi.single i 1) =
      Pi.single (p i).1 (eisensteinToRational ((p i).2 : Eisenstein)) := by
    have hscale : eisensteinFrameScale • Pi.single i (1 : EisensteinRational) =
        Pi.single i eisensteinFrameScale := by
      funext j; by_cases hj : j=i <;> simp [Pi.single_apply,Pi.smul_apply,hj]
    have he := hp i
    rw [← hscale,f.val.prop.1] at he
    funext j
    apply mul_left_cancel₀ eisensteinAxisScale_ne_zero
    have hh := congrFun he j
    simpa [eisensteinFrameVector,Pi.single_apply,Pi.smul_apply,mul_ite] using hh
  have hpi : Function.Injective (fun i => (p i).1) := by
    intro i j hij
    change (p i).1 = (p j).1 at hij
    by_contra hne
    have hfi : f.val.val (eisensteinToRational ((p j).2 : Eisenstein) • Pi.single i 1) =
        f.val.val (eisensteinToRational ((p i).2 : Eisenstein) • Pi.single j 1) := by
      rw [f.val.prop.1,f.val.prop.1,hb i,hb j,hij]
      funext k
      by_cases hk : k=(p j).1 <;> simp [Pi.single_apply,Pi.smul_apply,hk,mul_comm]
    have he := congrFun (f.val.val.injective hfi) i
    have hz : eisensteinToRational ((p j).2 : Eisenstein) = 0 := by
      simpa [Pi.single_apply,Pi.smul_apply,hne] using he
    exact ((p j).2.isUnit.map eisensteinToRational).ne_zero hz
  let σ : Equiv.Perm (Fin 12) := Equiv.ofBijective (fun i => (p i).1)
    ⟨hpi,Finite.surjective_of_injective hpi⟩
  refine ⟨fun i => (p (σ.symm i)).2,σ,?_⟩
  intro z i
  have hz : z = ∑ j : Fin 12, z j • Pi.single j (1 : EisensteinRational) := by
    funext k; simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [hz,map_sum]
  simp_rw [f.val.prop.1,hb]
  change (∑ j : Fin 12, z j * (Pi.single (σ j)
    (eisensteinToRational ((p j).2 : Eisenstein)) : EisensteinRationalCoordinates) i) = _
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp [Pi.single_apply,mul_comm]
  · intro j _ hj
    have hji : i ≠ σ j := by intro h; exact hj (σ.injective (by simpa using h.symm))
    simp [Pi.single_apply,hji]
  · simp

/-- The monomial just forced by the full stabilizer preserves the integral lattice. -/
theorem eisensteinCoordinateFrame_integral_monomial (f : eisensteinCoordinateFrameStabilizer) :
    ∃ d : EisensteinMonomialDatum, ∀ z i,
      f.val.val z i = eisensteinToRational (d.val.1 i : Eisenstein)*z (d.val.2.symm i) := by
  obtain ⟨u,σ,hf⟩ := eisensteinCoordinateFrame_is_monomial f
  have hp : ∀ z ∈ eisensteinLeechModule, eisensteinUnitMonomial u σ z ∈ eisensteinLeechModule := by
    intro z hz
    have he : f.val.val (eisensteinCoordinateEmbedding z) =
        eisensteinCoordinateEmbedding (eisensteinUnitMonomial u σ z) := by
      funext i
      rw [hf]
      exact (map_mul eisensteinToRational _ _).symm
    have hl := (f.val.prop.2.2 _).mp (show eisensteinCoordinateEmbedding z ∈ rationalEisensteinLattice from ⟨z,hz,rfl⟩)
    rw [he] at hl
    obtain ⟨w,hw,hwz⟩ := hl
    have hwz' : w = eisensteinUnitMonomial u σ z := by
      funext i
      exact eisensteinToRational_injective (congrFun hwz i)
    rw [hwz'] at hw
    exact hw
  exact ⟨⟨(u,σ),hp⟩,hf⟩

end Atlas.Conway
