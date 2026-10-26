import Atlas.LinearGroups.Chevalley.Comparison.TypeDNaturalForm
import Atlas.LinearGroups.Orthogonal.CoordinateRootSubgroups

/-! The actual natural D representation lands in the old elementary subgroup.
Each simple generator is identified with a literal coordinate Siegel element.
No group order, surjectivity, simplicity, or full-O identification is used. -/
noncomputable section
open scoped Matrix
namespace Atlas.Chevalley.Comparison.TypeD
open Classical Atlas.Orthogonal Atlas.Quadratic

private theorem polar_ef {r : ℕ} (K : Type*) [Field K]
    (i j : Fin r) (hij : i≠j) (t : K) :
    (formD r K).polarBilin (e i) (t • f j)=0 := by
  rw [map_smul,polarD_f]
  simp [e,Pi.single_apply,hij,Ne.symm hij]

private theorem polar_ee {r : ℕ} (K : Type*) [Field K]
    (i j : Fin r) (t : K) :
    (formD r K).polarBilin (e i) (t • e j)=0 := by
  rw [map_smul,polarD_e]
  simp [e,Pi.single_apply]

private theorem polar_ff {r : ℕ} (K : Type*) [Field K]
    (i j : Fin r) (t : K) :
    (formD r K).polarBilin (f i) (t • f j)=0 := by
  rw [map_smul,polarD_f]
  simp [f,Pi.single_apply]

private theorem adjacent_ne {n : ℕ} (i : Fin (n+1)) : i.castSucc≠i.succ := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castSucc,Fin.val_succ] at this
  omega

private theorem sign_square (K : Type*) [Field K] (m : ℕ) :
    (-1 : K)^m*(-1 : K)^m=1 := by
  rw [← mul_pow]
  simp

private theorem sign_adjacent (K : Type*) [Field K] (m : ℕ) :
    (-1 : K)^m*(-1 : K)^(m+1)= -1 := by
  rw [pow_succ,← mul_assoc,sign_square,one_mul]

theorem naturalOrthogonalHom_X_pair (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+1)) (t : K) :
    naturalOrthogonalHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i.castSucc t) =
      siegelElement (formD (n+2) K) (e i.castSucc) (t • f i.succ)
        (formD_e _) (polar_ef K _ _ (adjacent_ne i) t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [naturalOrthogonalHom_apply,matrix_X_pair]
  change frameVector n K (_ *ᵥ frameVector n K v) =
    siegel (formD (n+2) K) (e i.castSucc) (t • f i.succ) v
  simp only [siegel,map_smul,polarD_e,polarD_f,QuadraticMap.map_smul,
    formD_e,formD_f,mul_zero,smul_zero,zero_smul,sub_zero]
  ext a
  cases a with
  | inl k =>
    simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      Matrix.single_mulVec,Function.update_apply,siegel,polarD_e,polarD_f,
      e,f,Pi.single_apply,smul_eq_mul]
    <;> ring
  | inr k =>
    by_cases hi : k=i.castSucc <;> by_cases hj : k=i.succ
    all_goals simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      Matrix.single_mulVec,Function.update_apply,siegel,polarD_e,polarD_f,
      e,f,Pi.single_apply,smul_eq_mul,hi,hj,adjacent_ne i,Ne.symm (adjacent_ne i)]
    all_goals first
      | ring1
      | linear_combination (v (.inr k)) * sign_square K k.val
      | linear_combination (v (.inr i.castSucc)) * sign_square K i.castSucc.val
      | linear_combination (v (.inr i.succ)) * sign_square K i.succ.val
      | linear_combination (norm := (ring_nf <;> simp only [pow_mul', neg_one_sq, one_pow, Fin.succ_last] <;> ring1)) (v (.inr i.succ)) * sign_square K i.succ.val +
          (t*v (.inr i.castSucc)) * sign_adjacent K i.val

theorem naturalOrthogonalHom_Y_pair (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+1)) (t : K) :
    naturalOrthogonalHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i.castSucc t) =
      siegelElement (formD (n+2) K) (e i.succ) (t • f i.castSucc)
        (formD_e _) (polar_ef K _ _ (Ne.symm (adjacent_ne i)) t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [naturalOrthogonalHom_apply,matrix_Y_pair]
  change frameVector n K (_ *ᵥ frameVector n K v) =
    siegel (formD (n+2) K) (e i.succ) (t • f i.castSucc) v
  simp only [siegel,map_smul,polarD_e,polarD_f,QuadraticMap.map_smul,
    formD_e,formD_f,mul_zero,smul_zero,zero_smul,sub_zero]
  ext a
  cases a with
  | inl k =>
    simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      Matrix.single_mulVec,Function.update_apply,siegel,polarD_e,polarD_f,
      e,f,Pi.single_apply,smul_eq_mul]
    <;> ring
  | inr k =>
    by_cases hi : k=i.castSucc <;> by_cases hj : k=i.succ
    all_goals simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      Matrix.single_mulVec,Function.update_apply,siegel,polarD_e,polarD_f,
      e,f,Pi.single_apply,smul_eq_mul,hi,hj,adjacent_ne i,Ne.symm (adjacent_ne i)]
    all_goals first
      | ring1
      | linear_combination (v (.inr k)) * sign_square K k.val
      | linear_combination (v (.inr i.castSucc)) * sign_square K i.castSucc.val
      | linear_combination (v (.inr i.succ)) * sign_square K i.succ.val
      | linear_combination (norm := (ring_nf <;> simp only [pow_mul', neg_one_sq, one_pow, Fin.succ_last] <;> ring1)) (v (.inr i.castSucc)) * sign_square K i.castSucc.val +
          (t*v (.inr i.succ)) * sign_adjacent K i.val

theorem naturalOrthogonalHom_X_sum (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (t : K) :
    naturalOrthogonalHom n hn K
        (selectedWeightCompanionX (.D (n+2) hn) K (Fin.last (n+1)) t) =
      siegelElement (formD (n+2) K) (e (Fin.last n).castSucc)
        (((-1 : K)^(n+1)*t) • e (Fin.last n).succ)
        (formD_e _) (polar_ee K _ _ _) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [naturalOrthogonalHom_apply,matrix_X_sum]
  change frameVector n K (_ *ᵥ frameVector n K v) =
    siegel (formD (n+2) K) (e (Fin.last n).castSucc)
      (((-1 : K)^(n+1)*t) • e (Fin.last n).succ) v
  simp only [siegel,map_smul,polarD_e,polarD_f,QuadraticMap.map_smul,
    formD_e,formD_f,mul_zero,smul_zero,zero_smul,sub_zero]
  have hlast : (Fin.last n).castSucc ≠ Fin.last (n+1) :=
    Fin.castSucc_ne_last (Fin.last n)
  ext a
  cases a with
  | inl k =>
    by_cases hi : k=(Fin.last n).castSucc <;> by_cases hj : k=(Fin.last n).succ
    all_goals simp only [Fin.succ_last] at hi hj
    all_goals simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
        Matrix.single_mulVec,Function.update_apply,siegel,polarD_e,
        e,Pi.single_apply,smul_eq_mul,hi,hj,hlast,Ne.symm hlast,pow_succ] <;> ring
  | inr k =>
    simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      Matrix.single_mulVec,Function.update_apply,siegel,polarD_e,
      e,Pi.single_apply,smul_eq_mul]
    <;> linear_combination (v (.inr k)) * sign_square K k.val

theorem naturalOrthogonalHom_Y_sum (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (t : K) :
    naturalOrthogonalHom n hn K
        (selectedWeightCompanionY (.D (n+2) hn) K (Fin.last (n+1)) t) =
      siegelElement (formD (n+2) K) (f (Fin.last n).castSucc)
        (((-1 : K)^n*t) • f (Fin.last n).succ)
        (formD_f _) (polar_ff K _ _ _) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [naturalOrthogonalHom_apply,matrix_Y_sum]
  change frameVector n K (_ *ᵥ frameVector n K v) =
    siegel (formD (n+2) K) (f (Fin.last n).castSucc)
      (((-1 : K)^n*t) • f (Fin.last n).succ) v
  simp only [siegel,map_smul,polarD_e,polarD_f,QuadraticMap.map_smul,
    formD_e,formD_f,mul_zero,smul_zero,zero_smul,sub_zero]
  have hlast : (Fin.last n).castSucc ≠ Fin.last (n+1) :=
    Fin.castSucc_ne_last (Fin.last n)
  ext a
  cases a with
  | inl k =>
    simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      Matrix.single_mulVec,Function.update_apply,siegel,polarD_f,
      f,Pi.single_apply,smul_eq_mul]
  | inr k =>
    by_cases hi : k=(Fin.last n).castSucc <;> by_cases hj : k=(Fin.last n).succ
    all_goals simp only [Fin.succ_last] at hi hj
    all_goals simp [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      Matrix.single_mulVec,Function.update_apply,siegel,polarD_f,
      f,Pi.single_apply,smul_eq_mul,hi,hj,hlast,Ne.symm hlast,pow_succ,mul_add]
    all_goals first
      | ring1
      | linear_combination (v (.inr k)) * sign_square K k.val
      | linear_combination (v (.inr (Fin.last n).castSucc)) * sign_square K n
      | linear_combination (norm := (ring_nf <;> simp only [pow_mul', neg_one_sq, one_pow, Fin.succ_last] <;> ring1)) (v (.inr (Fin.last n).succ)) * sign_square K n

theorem naturalOrthogonalHom_X_mem_elementary (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] (i : Fin (n+2)) (t : K) :
    naturalOrthogonalHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i t) ∈
      elementarySubgroup (formD (n+2) K) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [naturalOrthogonalHom_X_sum]
    exact siegelElement_mem _ _ _ _ _
  · rw [naturalOrthogonalHom_X_pair]
    exact siegelElement_mem _ _ _ _ _

theorem naturalOrthogonalHom_Y_mem_elementary (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] (i : Fin (n+2)) (t : K) :
    naturalOrthogonalHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i t) ∈
      elementarySubgroup (formD (n+2) K) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [naturalOrthogonalHom_Y_sum]
    exact siegelElement_mem _ _ _ _ _
  · rw [naturalOrthogonalHom_Y_pair]
    exact siegelElement_mem _ _ _ _ _

theorem naturalOrthogonalHom_mem_elementary (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] (g : SelectedWeightCompanion (.D (n+2) hn) K) :
    naturalOrthogonalHom n hn K g ∈ elementarySubgroup (formD (n+2) K) := by
  apply weightCompanion_induction_left (rootDatum (.D (n+2) hn)).pairing
    (rootDatum (.D (n+2) hn)).base (selectedWeightOrbits (.D (n+2) hn))
    (selectedWeightOrbits_closed (.D (n+2) hn))
    (selectedWeightOrbits_minuscule (.D (n+2) hn)) K ?_ ?_ ?_ g
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.D (n+2) hn)).indexEquiv.surjective j
    rw [map_mul]
    exact Subgroup.mul_mem _ (naturalOrthogonalHom_X_mem_elementary n hn K i t) hh
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.D (n+2) hn)).indexEquiv.surjective j
    rw [map_mul]
    exact Subgroup.mul_mem _ (naturalOrthogonalHom_Y_mem_elementary n hn K i t) hh

/-- The codomain is the existing literal elementary subgroup, not the full O group. -/
def naturalElementaryHom (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] :
    SelectedWeightCompanion (.D (n+2) hn) K →* elementarySubgroup (formD (n+2) K) :=
  (naturalOrthogonalHom n hn K).codRestrict _ (naturalOrthogonalHom_mem_elementary n hn K)

@[simp] theorem naturalElementaryHom_val (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (g : SelectedWeightCompanion (.D (n+2) hn) K) :
    (naturalElementaryHom n hn K g).val = naturalOrthogonalHom n hn K g := rfl

end Atlas.Chevalley.Comparison.TypeD
