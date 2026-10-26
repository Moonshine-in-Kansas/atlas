import Atlas.LinearGroups.Chevalley.Comparison.TypeDNaturalBlock
import Atlas.LinearGroups.Chevalley.WeightCompanionLeftInduction
import Atlas.LinearGroups.Orthogonal.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The descended D natural action preserves a genuine split quadratic form.
A diagonal ±1 change of coordinates gives a homomorphism to the existing full
quadratic-isometry carrier. Elementary image and kernel identification are separate. -/
noncomputable section
open scoped Matrix
namespace Atlas.Chevalley.Comparison.TypeD
open Classical

/-- Weighted hyperbolic polynomial; no division by two occurs. -/
def weightedForm (n : ℕ) (R : Type*) [CommRing R] (c : Fin (n+2) → R)
    (v : Index n → R) : R := ∑ i, c i * v (.inl i) * v (.inr i)

private theorem weighted_pair (n : ℕ) (R : Type*) [CommRing R]
    (c : Fin (n+2) → R) (i j : Fin (n+2)) (hij : i≠j) (hc : c i+c j=0)
    (t : R) (v : Index n → R) :
    weightedForm n R c ((1+t • (Matrix.single (.inl i) (.inl j) 1 +
      Matrix.single (.inr j) (.inr i) 1)) *ᵥ v) = weightedForm n R c v := by
  let A : Matrix (Index n) (Index n) R := 1+t •
    (Matrix.single (.inl i) (.inl j) 1+Matrix.single (.inr j) (.inr i) 1)
  let δ := t*v (.inl j)*v (.inr i)
  have he (k : Fin (n+2)) : c k*(A *ᵥ v) (.inl k)*(A *ᵥ v) (.inr k) =
      c k*v (.inl k)*v (.inr k) +
        (if k=i then c i*δ else 0) + (if k=j then c j*δ else 0) := by
    by_cases hi : k=i
    · subst k
      simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
        Matrix.single_mulVec,Function.update_apply,hij,Ne.symm hij,eq_comm] <;> ring
    · by_cases hj : k=j
      · subst k
        simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
          Matrix.single_mulVec,Function.update_apply,hij,Ne.symm hij,eq_comm] <;> ring
      · simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
          Matrix.single_mulVec,Function.update_apply,hi,hj,Ne.symm hi,Ne.symm hj,
          hij,Ne.symm hij,eq_comm] <;> ring
  calc
    _ = weightedForm n R c v+c i*δ+c j*δ := by
      change weightedForm n R c (A *ᵥ v) = _
      simp only [weightedForm,he,Finset.sum_add_distrib]
      simp
    _ = weightedForm n R c v+(c i+c j)*δ := by ring
    _ = _ := by rw [hc,zero_mul,add_zero]

private theorem weighted_sum (n : ℕ) (R : Type*) [CommRing R]
    (c : Fin (n+2) → R) (i j : Fin (n+2)) (hij : i≠j) (hc : c i+c j=0)
    (t : R) (v : Index n → R) :
    weightedForm n R c ((1+t • (Matrix.single (.inl i) (.inr j) 1 +
      Matrix.single (.inl j) (.inr i) 1)) *ᵥ v) = weightedForm n R c v := by
  let A : Matrix (Index n) (Index n) R := 1+t •
    (Matrix.single (.inl i) (.inr j) 1+Matrix.single (.inl j) (.inr i) 1)
  let δ := t*v (.inr i)*v (.inr j)
  have he (k : Fin (n+2)) : c k*(A *ᵥ v) (.inl k)*(A *ᵥ v) (.inr k) =
      c k*v (.inl k)*v (.inr k) +
        (if k=i then c i*δ else 0) + (if k=j then c j*δ else 0) := by
    by_cases hi : k=i
    · subst k
      simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
        Matrix.single_mulVec,Function.update_apply,hij,Ne.symm hij,eq_comm] <;> ring
    · by_cases hj : k=j
      · subst k
        simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
          Matrix.single_mulVec,Function.update_apply,hij,Ne.symm hij,eq_comm] <;> ring
      · simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
          Matrix.single_mulVec,Function.update_apply,hi,hj,Ne.symm hi,Ne.symm hj,
          hij,Ne.symm hij,eq_comm] <;> ring
  calc
    _ = weightedForm n R c v+c i*δ+c j*δ := by
      change weightedForm n R c (A *ᵥ v) = _
      simp only [weightedForm,he,Finset.sum_add_distrib]
      simp
    _ = weightedForm n R c v+(c i+c j)*δ := by ring
    _ = _ := by rw [hc,zero_mul,add_zero]

private theorem weighted_sum_lowering (n : ℕ) (R : Type*) [CommRing R]
    (c : Fin (n+2) → R) (i j : Fin (n+2)) (hij : i≠j) (hc : c i+c j=0)
    (t : R) (v : Index n → R) :
    weightedForm n R c ((1+t • (Matrix.single (.inr i) (.inl j) 1 +
      Matrix.single (.inr j) (.inl i) 1)) *ᵥ v) = weightedForm n R c v := by
  let A : Matrix (Index n) (Index n) R := 1+t •
    (Matrix.single (.inr i) (.inl j) 1+Matrix.single (.inr j) (.inl i) 1)
  let δ := t*v (.inl i)*v (.inl j)
  have he (k : Fin (n+2)) : c k*(A *ᵥ v) (.inl k)*(A *ᵥ v) (.inr k) =
      c k*v (.inl k)*v (.inr k) +
        (if k=i then c i*δ else 0) + (if k=j then c j*δ else 0) := by
    by_cases hi : k=i
    · subst k
      simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
        Matrix.single_mulVec,Function.update_apply,hij,Ne.symm hij,eq_comm] <;> ring
    · by_cases hj : k=j
      · subst k
        simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
          Matrix.single_mulVec,Function.update_apply,hij,Ne.symm hij,eq_comm] <;> ring
      · simp [A,δ,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
          Matrix.single_mulVec,Function.update_apply,hi,hj,Ne.symm hi,Ne.symm hj,
          hij,Ne.symm hij,eq_comm] <;> ring
  calc
    _ = weightedForm n R c v+c i*δ+c j*δ := by
      change weightedForm n R c (A *ᵥ v) = _
      simp only [weightedForm,he,Finset.sum_add_distrib]
      simp
    _ = weightedForm n R c v+(c i+c j)*δ := by ring
    _ = _ := by rw [hc,zero_mul,add_zero]

private theorem adjacent_ne {n : ℕ} (i : Fin (n+1)) : i.castSucc≠i.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc,Fin.val_succ] at hv
  omega

private theorem adjacent_sign (n : ℕ) (R : Type*) [CommRing R] (i : Fin (n+1)) :
    (-1 : R)^i.castSucc.val+(-1 : R)^i.succ.val=0 := by
  simp only [Fin.val_castSucc,Fin.val_succ,pow_succ]
  ring

theorem rawMatrix_X_preserves (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+2)) (t : K) (v : Index n → K) :
    weightedForm n K (fun k => (-1)^k.val)
      (rawMatrixHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i t) *ᵥ v) =
        weightedForm n K (fun k => (-1)^k.val) v := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [matrix_X_sum]
    exact weighted_sum n K _ _ _ (adjacent_ne _) (adjacent_sign n K _) t v
  · rw [matrix_X_pair]
    exact weighted_pair n K _ _ _ (adjacent_ne _) (adjacent_sign n K _) t v

theorem rawMatrix_Y_preserves (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+2)) (t : K) (v : Index n → K) :
    weightedForm n K (fun k => (-1)^k.val)
      (rawMatrixHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i t) *ᵥ v) =
        weightedForm n K (fun k => (-1)^k.val) v := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [matrix_Y_sum]
    exact weighted_sum_lowering n K _ _ _ (adjacent_ne _) (adjacent_sign n K _) t v
  · rw [matrix_Y_pair]
    exact weighted_pair n K _ _ _ (Ne.symm (adjacent_ne j))
      (by simpa only [add_comm] using adjacent_sign n K j) t v

/-- All elements of the actual selected companion preserve the weighted hyperbolic form. -/
theorem rawMatrix_preserves (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (g : SelectedWeightCompanion (.D (n+2) hn) K) :
    ∀ v : Index n → K, weightedForm n K (fun k => (-1)^k.val)
      (rawMatrixHom n hn K g *ᵥ v) = weightedForm n K (fun k => (-1)^k.val) v := by
  apply weightCompanion_induction_left (rootDatum (.D (n+2) hn)).pairing
    (rootDatum (.D (n+2) hn)).base (selectedWeightOrbits (.D (n+2) hn))
    (selectedWeightOrbits_closed (.D (n+2) hn))
    (selectedWeightOrbits_minuscule (.D (n+2) hn)) K ?_ ?_ ?_ g
  · intro v
    rw [map_one,Matrix.one_mulVec]
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.D (n+2) hn)).indexEquiv.surjective j
    change ∀ v, weightedForm n K (fun k => (-1)^k.val)
      (rawMatrixHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i t*h) *ᵥ v) = _
    intro v
    rw [map_mul,← Matrix.mulVec_mulVec]
    exact (rawMatrix_X_preserves n hn K i t _).trans (hh v)
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.D (n+2) hn)).indexEquiv.surjective j
    change ∀ v, weightedForm n K (fun k => (-1)^k.val)
      (rawMatrixHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i t*h) *ᵥ v) = _
    intro v
    rw [map_mul,← Matrix.mulVec_mulVec]
    exact (rawMatrix_Y_preserves n hn K i t _).trans (hh v)

/-- The coordinate correction is a unit sign, also in characteristic two. -/
def frameVector (n : ℕ) (R : Type*) [CommRing R] (v : Index n → R) : Index n → R
  | .inl i => v (.inl i)
  | .inr i => (-1)^i.val*v (.inr i)

theorem frameVector_involutive (n : ℕ) (R : Type*) [CommRing R] :
    Function.Involutive (frameVector n R) := by
  intro v
  funext a
  cases a with
  | inl i => rfl
  | inr i =>
    have hs : (-1 : R)^i.val*(-1 : R)^i.val=1 := by
      rw [← mul_pow]
      simp
    change (-1 : R)^i.val*((-1 : R)^i.val*v (.inr i))=v (.inr i)
    rw [← mul_assoc,hs,one_mul]

def frameEquiv (n : ℕ) (R : Type*) [CommRing R] : (Index n → R) ≃ₗ[R] (Index n → R) where
  toFun := frameVector n R
  invFun := frameVector n R
  left_inv := frameVector_involutive n R
  right_inv := frameVector_involutive n R
  map_add' v w := by
    funext a
    cases a <;> simp [frameVector,mul_add]
  map_smul' t v := by
    funext a
    cases a <;> simp [frameVector,smul_eq_mul,mul_left_comm]

theorem frameVector_form (n : ℕ) (R : Type*) [CommRing R] (v : Index n → R) :
    Atlas.Orthogonal.formD (n+2) R (frameVector n R v) =
      weightedForm n R (fun k => (-1)^k.val) v := by
  rw [Atlas.Orthogonal.formD_apply]
  apply Finset.sum_congr rfl
  intro i _
  change v (.inl i)*((-1 : R)^i.val*v (.inr i)) = (-1 : R)^i.val*v (.inl i)*v (.inr i)
  ring

/-- Conjugate the natural unit matrices by the literal diagonal sign equivalence. -/
def naturalOrthogonalLinearHom (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] :
    SelectedWeightCompanion (.D (n+2) hn) K →* ((Index n → K) ≃ₗ[K] (Index n → K)) where
  toFun g := (frameEquiv n K).trans
    ((Matrix.GeneralLinearGroup.toLin (naturalRepresentation n hn K g)).toLinearEquiv.trans
      (frameEquiv n K))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change frameVector n K (rawMatrixHom n hn K 1 *ᵥ frameVector n K v)=v
    rw [map_one,Matrix.one_mulVec]
    exact frameVector_involutive n K v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change frameVector n K (rawMatrixHom n hn K (g*h) *ᵥ frameVector n K v) =
      frameVector n K (rawMatrixHom n hn K g *ᵥ frameVector n K
        (frameVector n K (rawMatrixHom n hn K h *ᵥ frameVector n K v)))
    rw [map_mul,← Matrix.mulVec_mulVec,frameVector_involutive]

/-- An actual homomorphism to the pre-existing full split quadratic isometry group.
No elementary-image, injectivity or kernel assertion is bundled into this construction. -/
def naturalOrthogonalHom (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] :
    SelectedWeightCompanion (.D (n+2) hn) K →* Atlas.Orthogonal.O_DPlus (n+2) K where
  toFun g := ⟨naturalOrthogonalLinearHom n hn K g, by
    intro v
    change Atlas.Orthogonal.formD (n+2) K
      (frameVector n K (rawMatrixHom n hn K g *ᵥ frameVector n K v)) =
        Atlas.Orthogonal.formD (n+2) K v
    rw [frameVector_form,rawMatrix_preserves,← frameVector_form,frameVector_involutive]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

theorem naturalOrthogonalHom_apply (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (g : SelectedWeightCompanion (.D (n+2) hn) K) (v : Index n → K) :
    (naturalOrthogonalHom n hn K g).val v =
      frameVector n K (rawMatrixHom n hn K g *ᵥ frameVector n K v) := rfl

end Atlas.Chevalley.Comparison.TypeD
