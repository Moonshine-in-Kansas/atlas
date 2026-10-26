import Atlas.Rudvalis.LatticeMonomial
import Mathlib.LinearAlgebra.Pi

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

/-- The union of the four vertices of the 28 coordinate Gaussian crosses. -/
def coordinateShell (v : RationalSpace) : Prop :=
  ∃ i : Coordinate,v=coordinateMinimum i ∨ v= -coordinateMinimum i

theorem rationalDot_coordinate (i j : Coordinate) :
    rationalDot (coordinateMinimum i) (coordinateMinimum j)=if i=j then 4 else 0 := by
  classical
  by_cases h : i=j <;> simp [rationalDot,coordinateMinimum,Pi.single_apply,h,eq_comm] <;> norm_num

theorem coordinate_action_determines (f g : RationalSpace ≃ₗ[ℚ] RationalSpace)
    (h : ∀ i,f (coordinateMinimum i)=g (coordinateMinimum i)) : f=g := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  intro i x
  have he : Pi.single i x=(x/2) • coordinateMinimum i := by
    ext j
    simp [coordinateMinimum,Pi.single_apply]
  rw [he]
  simpa only [LinearEquiv.coe_coe,map_smul] using congrArg ((x/2) • ·) (h i)

/-- An orthogonal map preserving the coordinate vertices is a signed permutation. -/
theorem coordinateShell_preserver_signed
    (f : RationalSpace ≃ₗ[ℚ] RationalSpace)
    (hf : ∀ v w,rationalDot (f v) (f w)=rationalDot v w)
    (ha : ∀ i,coordinateShell (f (coordinateMinimum i))) :
    ∃ g : SignedCoordinates Coordinate,rationalMonomialHom g=f := by
  classical
  have h : ∀i,∃j,∃b : Binary,f (coordinateMinimum i)=liftedSign b (coordinateMinimum j) := by
    intro i
    obtain ⟨j,hj|hj⟩ := ha i
    · exact ⟨j,0,by simpa [liftedSign] using hj⟩
    · exact ⟨j,1,by simpa [liftedSign] using hj⟩
  choose p s hs using h
  have hp : Function.Injective p := by
    intro i j hij
    by_contra hn
    have he := hf (coordinateMinimum i) (coordinateMinimum j)
    rw [hs i,hs j,hij] at he
    have hb : ∀b : Binary,b=0 ∨ b=1 := by decide +kernel
    rcases hb (s i) with hsi|hsi <;> rcases hb (s j) with hsj|hsj <;>
      simp [liftedSign,hsi,hsj,rationalDot,coordinateMinimum,Pi.single_apply,hn,Ne.symm hn] at he
  let e : Equiv.Perm Coordinate := Equiv.ofBijective p ((Finite.injective_iff_bijective).mp hp)
  let g : SignedCoordinates Coordinate := ⟨Multiplicative.ofAdd (s ∘ e.symm),e⟩
  refine ⟨g,coordinate_action_determines _ _ ?_⟩
  intro i
  rw [hs i]
  funext j
  change liftedSign (s (e.symm j)) (coordinateMinimum i (e.symm j))=
    (liftedSign (s i) (coordinateMinimum (p i))) j
  have he : e.symm j=i ↔ j=p i := by
    change e.symm j=i ↔ j=e i
    exact e.symm_apply_eq
  by_cases hj : j=p i
  · have hi := he.mpr hj
    subst j
    by_cases hb : s i=0 <;> simp [hi,coordinateMinimum,Pi.single_apply,liftedSign,hb]
  · have hi := mt he.mp hj
    by_cases hb : s i=0 <;> simp [coordinateMinimum,Pi.single_apply,liftedSign,hj,hi,hb]

theorem coordinateFrame_full_stabilizer
    (f : RationalSpace ≃ₗ[ℚ] RationalSpace)
    (hf : ∀ v w,rationalDot (f v) (f w)=rationalDot v w)
    (hL : ∀v,v∈rudvalisLattice ↔ f v∈rudvalisLattice)
    (ha : ∀i,coordinateShell (f (coordinateMinimum i))) :
    ∃g : codeGroup,rationalMonomialHom g.val=f := by
  obtain ⟨g,rfl⟩ := coordinateShell_preserver_signed f hf ha
  exact ⟨⟨g,(signed_lattice_stabilizer_iff g).mp hL⟩,rfl⟩

end Atlas.Rudvalis
