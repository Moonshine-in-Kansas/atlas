import Atlas.Fischer.RootRayTransportedProduct
import Atlas.Fischer.IntrinsicTraceForm

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A semilinear phase permutation of a full reflecting family is automatically
bijective, multiplicative and compatible with the Hermitian form. -/
theorem reflectingRoot_phasePermutation_criterion {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j = (a.val.val : Scalar) • r i)
    (hc : Fintype.card J = 306936) (b : Bit)
    (g : Coordinates →ₛₗ[(scalarParityAut b).toRingHom] Coordinates)
    (π : Equiv.Perm J) (a : J → Mu3)
    (hg : ∀ j, g (r j) = (a j).val.val • r (π j)) :
    Function.Bijective g ∧
      (∀ x y, g (product x y) = product (g x) (g y)) ∧
      (∀ x y, hermitian (g x) (g y) = scalarParityAut b (hermitian x y)) := by
  let e := rootRayPermutationEquiv r (reflectingRoot_span_top r hr hd hc) b g π a hg
  have he : ∀ x, e x = g x := fun _ => rfl
  have hp : ∀ x y, e (product x y) = product (e x) (e y) := by
    apply reflectingRoot_transport_product r hr hd hc b e
    intro j
    rw [he, hg]
    exact root_phase (r (π j)) (hr (π j)).1 (a j).val.val
      ((mem_rootsOfUnity' _ _).mp (a j).property)
  let A : SemilinearAlgebraAutomorphism :=
    ⟨e.toEquiv, ⟨fun x y => e.map_add x y, hp, b, fun c x => e.map_smulₛₗ c x⟩⟩
  have hpar : semilinearAlgebraParity A = b :=
    semilinearAlgebraParity_unique A b (fun c x => e.map_smulₛₗ c x)
  refine ⟨rootRayPermutation_bijective r (reflectingRoot_span_top r hr hd hc) b g π a hg,
    hp, ?_⟩
  intro x y
  have h := semilinearAlgebraAutomorphism_hermitian A x y
  rw [hpar] at h
  exact h

/-- Permuting the actual three-element cubic-phase rays suffices: invertibility
and preservation of multiplication and metric are conclusions, not premises. -/
theorem reflectingRoot_rayPermutation_criterion {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j = (a.val.val : Scalar) • r i)
    (hc : Fintype.card J = 306936) (b : Bit)
    (g : Coordinates →ₛₗ[(scalarParityAut b).toRingHom] Coordinates)
    (π : Equiv.Perm J)
    (hg : ∀ j, rootRay (g (r j)) = rootRay (r (π j))) :
    Function.Bijective g ∧
      (∀ x y, g (product x y) = product (g x) (g y)) ∧
      (∀ x y, hermitian (g x) (g y) = scalarParityAut b (hermitian x y)) := by
  classical
  have h : ∀ j, ∃ a : Mu3, g (r j) = a.val.val • r (π j) :=
    fun j => (rootRay_eq_iff_mu3 _ _).mp (hg j)
  choose a ha using h
  exact reflectingRoot_phasePermutation_criterion r hr hd hc b g π a ha

end Atlas.Fischer
