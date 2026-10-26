import Atlas.LinearGroups.Chevalley.WeylRootActionComplete
import Atlas.LinearAlgebra.UnitCoordinateLines
import Atlas.LinearGroups.Chevalley.TorusGlobal

/-! Source-only candidate. Actual unit-monomial action on all root coordinates.
No BN-pair, order formula, or abstract root-group conjugation is assumed. -/
noncomputable section
open scoped Matrix
namespace Atlas.Chevalley
open Classical Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- Signed root-coordinate coefficient of the pinned Weyl word at parameter one.
The opposite-simple columns have coefficient one in the Geck convention. -/
def adjointWeylRootSign (i : b.support) (j : ι) : Rˣ :=
  if LinearIndependent ℤ ![P.root i, P.root j]
  then (-1 : Rˣ) ^ P.chainBotCoeff i j else 1

/-- Every root label is reflected; the scalar is always a unit, in every
characteristic. This includes both special columns omitted by the string lemma. -/
theorem adjointWeyl_one_root (i : b.support) (j : ι) :
    (adjointWeyl P b R i 1).val.val *ᵥ rootVector P b R j =
      (adjointWeylRootSign P b R i j).val •
        rootVector P b R (P.reflectionPerm i j) := by
  by_cases h : LinearIndependent ℤ ![P.root i, P.root j]
  · simpa [adjointWeylRootSign, h] using adjointWeyl_one_root_signed P b R i j
  · simpa [adjointWeylRootSign, h, P.chainBotCoeff_of_not_linearIndependent h] using
      adjointWeyl_one_root_signed P b R i j

/-- An actual adjoint matrix realizes a specified permutation of root coordinate
lines. Scalars are units; this definition does not identify root subgroups. -/
def AdjointRootPermutation (g : Adjoint P b R) (w : Equiv.Perm ι) : Prop :=
  ∀ j, ∃ a : Rˣ, g.val.val *ᵥ rootVector P b R j =
    a.val • rootVector P b R (w j)

theorem adjointRootPermutation_one : AdjointRootPermutation P b R 1 1 := by
  intro j
  refine ⟨1, ?_⟩
  change (1 : Matrix (b.support ⊕ ι) _ R) *ᵥ _ = _
  simp only [Matrix.one_mulVec, Equiv.Perm.one_apply, Units.val_one, one_smul]

theorem adjointRootPermutation_mul {g h : Adjoint P b R} {v w : Equiv.Perm ι}
    (hg : AdjointRootPermutation P b R g v)
    (hh : AdjointRootPermutation P b R h w) :
    AdjointRootPermutation P b R (g * h) (v * w) := by
  intro j
  obtain ⟨a, ha⟩ := hh j
  obtain ⟨c, hc⟩ := hg (w j)
  refine ⟨a * c, ?_⟩
  change (g.val.val * h.val.val) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul, hc]
  simp only [smul_smul, Units.val_mul, Equiv.Perm.mul_apply]

theorem adjointRootPermutation_inv {g : Adjoint P b R} {w : Equiv.Perm ι}
    (hg : AdjointRootPermutation P b R g w) :
    AdjointRootPermutation P b R g⁻¹ w⁻¹ := by
  intro j
  obtain ⟨a, ha⟩ := hg (w⁻¹ j)
  have hj : w (w⁻¹ j) = j := w.apply_symm_apply j
  rw [hj] at ha
  have hinv := adjoint_inv_mulVec_eq_of_mulVec_eq P b R g
    (rootVector P b R (w⁻¹ j)) (a.val • rootVector P b R j) ha
  rw [Matrix.mulVec_smul] at hinv
  refine ⟨a⁻¹, ?_⟩
  have hs := congrArg (fun z : b.support ⊕ ι → R => (a⁻¹).val • z) hinv
  simpa only [smul_smul, Units.inv_mul, one_smul] using hs

theorem adjointRootPermutation_weyl (i : b.support) :
    AdjointRootPermutation P b R (adjointWeyl P b R i 1) (P.reflectionPerm i) :=
  fun j => ⟨adjointWeylRootSign P b R i j, adjointWeyl_one_root P b R i j⟩

theorem adjointRootPermutation_torus (i : b.support) (a : Rˣ) :
    AdjointRootPermutation P b R (adjointTorus P b R i a) 1 :=
  fun j => ⟨a ^ P.pairingIn ℤ j i, adjointTorus_root P b R i j a⟩

/-- Literal root coordinates are the indicated coordinate basis vectors. -/
theorem rootVector_eq_single (j : ι) :
    rootVector P b R j = (Pi.single (Sum.inr j) 1 : b.support ⊕ ι → R) := by
  ext row
  by_cases h : row = Sum.inr j <;>
    simp [rootVector, RootPairing.GeckConstruction.v, Function.comp_def, Pi.single_apply, h]

variable [Nontrivial R]

/-- Separate root coordinate vectors remain distinguishable in characteristics
two and three. No claim about distinct torus characters is needed. -/
theorem rootVector_unit_smul_index_unique {j k : ι} (a c : Rˣ)
    (h : a.val • rootVector P b R j = c.val • rootVector P b R k) : j = k := by
  have hs : (Sum.inr j : b.support ⊕ ι) = Sum.inr k :=
    Atlas.LinearAlgebra.unit_smul_single_index_unique a c
      (by simpa only [rootVector_eq_single] using h)
  exact Sum.inr.inj hs

theorem adjointRootPermutation_unique {g : Adjoint P b R} {v w : Equiv.Perm ι}
    (hv : AdjointRootPermutation P b R g v)
    (hw : AdjointRootPermutation P b R g w) : v = w := by
  ext j
  obtain ⟨a, ha⟩ := hv j
  obtain ⟨c, hc⟩ := hw j
  exact rootVector_unit_smul_index_unique P b R a c (ha.symm.trans hc)

/-- Matrices realizing permutations in a fixed root-permutation subgroup.
This provides closure/inverse bookkeeping for the actual N generators. -/
def adjointRootPermutationSubgroup (W : Subgroup (Equiv.Perm ι)) :
    Subgroup (Adjoint P b R) where
  carrier := {g | ∃ w ∈ W, AdjointRootPermutation P b R g w}
  one_mem' := ⟨1, W.one_mem, adjointRootPermutation_one P b R⟩
  mul_mem' := by
    rintro g h ⟨v, hv, hgv⟩ ⟨w, hw, hhw⟩
    exact ⟨v * w, W.mul_mem hv hw, adjointRootPermutation_mul P b R hgv hhw⟩
  inv_mem' := by
    rintro g ⟨w, hw, hgw⟩
    exact ⟨w⁻¹, W.inv_mem hw, adjointRootPermutation_inv P b R hgw⟩

end Atlas.Chevalley
