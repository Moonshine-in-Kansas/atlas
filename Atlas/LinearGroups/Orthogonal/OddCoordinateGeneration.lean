import Atlas.LinearGroups.Orthogonal.OddSiegelCoordinates
import Atlas.LinearGroups.Orthogonal.CoordinateRootGeneration

/-! A structural image criterion for the existing elementary odd orthogonal group.
Mixed long coordinate roots and short roots at one axis suffice. This is a
generation theorem inside the existing quadratic group, not a spin comparison. -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable (r : ℕ) (F : Type*) [Field F]

def oddShortWeyl (i : Fin r) : O_B r F :=
  oddShortUpper r F i 1 * oddShortLower r F i (-1) * oddShortUpper r F i 1

theorem oddShortWeyl_e (i j : Fin r) :
    (oddShortWeyl r F i).val (e j,0) =
      if i=j then -(f j,0) else (e j,0) := by
  change (oddShortUpper r F i 1).val
    ((oddShortLower r F i (-1)).val ((oddShortUpper r F i 1).val (e j,0))) = _
  apply Prod.ext
  · funext k
    cases k with
    | inl k =>
      simp only [oddShortUpper_apply_x, oddShortUpper_apply_y, oddShortUpper_apply_z,
        oddShortLower_apply_x, oddShortLower_apply_y, oddShortLower_apply_z]
      by_cases h : i = j
      · subst j
        by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            hk, Ne.symm hk, ite_true, ite_false] <;> ring
      · by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, hk, Ne.symm hk, ite_true, ite_false] <;> ring
    | inr k =>
      simp only [oddShortUpper_apply_x, oddShortUpper_apply_y, oddShortUpper_apply_z,
        oddShortLower_apply_x, oddShortLower_apply_y, oddShortLower_apply_z]
      by_cases h : i = j
      · subst j
        by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            hk, Ne.symm hk, ite_true, ite_false] <;> ring
      · by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, hk, Ne.symm hk, ite_true, ite_false] <;> ring
  · by_cases h : i=j <;> simp [h, e, f, Pi.single_apply] <;> ring

theorem oddShortWeyl_f (i j : Fin r) :
    (oddShortWeyl r F i).val (f j,0) =
      if i=j then -(e j,0) else (f j,0) := by
  change (oddShortUpper r F i 1).val
    ((oddShortLower r F i (-1)).val ((oddShortUpper r F i 1).val (f j,0))) = _
  apply Prod.ext
  · funext k
    cases k with
    | inl k =>
      simp only [oddShortUpper_apply_x, oddShortUpper_apply_y, oddShortUpper_apply_z,
        oddShortLower_apply_x, oddShortLower_apply_y, oddShortLower_apply_z]
      by_cases h : i = j
      · subst j
        by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            hk, Ne.symm hk, ite_true, ite_false] <;> ring
      · by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, hk, Ne.symm hk, ite_true, ite_false] <;> ring
    | inr k =>
      simp only [oddShortUpper_apply_x, oddShortUpper_apply_y, oddShortUpper_apply_z,
        oddShortLower_apply_x, oddShortLower_apply_y, oddShortLower_apply_z]
      by_cases h : i = j
      · subst j
        by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            hk, Ne.symm hk, ite_true, ite_false] <;> ring
      · by_cases hk : i = k
        · subst k
          simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, ite_true, ite_false] <;> ring
        · simp only [e, f, Pi.single_apply, Prod.fst_neg, Pi.neg_apply,
            Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, eq_self,
            h, Ne.symm h, hk, Ne.symm hk, ite_true, ite_false] <;> ring
  · by_cases h : i=j <;> simp [h, e, f, Pi.single_apply] <;> ring

theorem oddShortWeyl_z (i : Fin r) :
    (oddShortWeyl r F i).val (0,1) = -(0,1) := by
  change (oddShortUpper r F i 1).val
    ((oddShortLower r F i (-1)).val ((oddShortUpper r F i 1).val (0,1))) = _
  apply Prod.ext
  · funext k
    cases k <;> simp <;> split_ifs <;> ring
  · simp <;> ring

private theorem siegel_neg_neg {V : Type*} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (u v x : V) :
    siegel Q (-u) (-v) x = siegel Q u v x := by
  simpa only [neg_one_smul, neg_neg] using siegel_scale Q u (-v) x (-1)

private theorem siegel_swap {V : Type*} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (u v x : V) (hu : Q u=0) (hv : Q v=0) :
    siegel Q u v x = siegel Q v (-u) x := by
  simp only [siegel, map_neg, QuadraticMap.map_neg, hu, hv, mul_zero, zero_mul, zero_smul]
  module

private theorem parallel_siegel (u : VectorB r F) (hu : formB r F u=0)
    (t : F) (h : (formB r F).polarBilin u (t • u)=0) :
    siegelElement (formB r F) u (t • u) hu h = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel (formB r F) u (t • u) x = x
  simpa only [zero_add, siegel_zero] using
    siegel_parameter_mod_line (formB r F) u 0 x t hu (by simp)

private theorem zero_siegel (u : VectorB r F) (hu : formB r F u=0)
    (h : (formB r F).polarBilin u 0=0) :
    siegelElement (formB r F) u 0 hu h = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  exact siegel_zero (formB r F) u

private theorem basis_e (i : Fin r) :
    coordinateBasisB (F := F) r (.inl (.inl i)) = (e i,0) := by
  simp [coordinateBasisB, coordinateBasisD, e]

private theorem basis_f (i : Fin r) :
    coordinateBasisB (F := F) r (.inl (.inr i)) = (f i,0) := by
  simp [coordinateBasisB, coordinateBasisD, f]

private theorem basis_z (i : Unit) :
    coordinateBasisB (F := F) r (.inr i) = (0,1) := by
  simp [coordinateBasisB]

/-- All mixed long roots and both short roots at each coordinate supply every
coordinate Siegel root, hence the full elementary subgroup. -/
theorem elementary_le_of_odd_coordinate_roots (hr : 2 ≤ r) (H : Subgroup (O_B r F))
    (hl : ∀ i j (hij : i ≠ j) t, oddLong r F i j hij t ∈ H)
    (hu : ∀ i t, oddShortUpper r F i t ∈ H)
    (hd : ∀ i t, oddShortLower r F i t ∈ H) :
    elementarySubgroup (formB r F) ≤ H := by
  classical
  have hw (i : Fin r) : oddShortWeyl r F i ∈ H :=
    H.mul_mem (H.mul_mem (hu i 1) (hd i (-1))) (hu i 1)
  have hee (i j : Fin r) (hij : i ≠ j) (t : F)
      (hs : formB r F (e i,0)=0)
      (hp : (formB r F).polarBilin (e i,0) (t • (e j,0))=0) :
      siegelElement (formB r F) (e i,0) (t • (e j,0)) hs hp ∈ H := by
    have he : oddShortWeyl r F j * oddLong r F i j hij (-t) *
        (oddShortWeyl r F j)⁻¹ =
        siegelElement (formB r F) (e i,0) (t • (e j,0)) hs hp := by
      rw [oddLong, siegelElement_conj]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formB r F) ((oddShortWeyl r F j).val (e i,0))
        ((oddShortWeyl r F j).val ((-t) • (f j,0))) x =
        siegel (formB r F) (e i,0) (t • (e j,0)) x
      rw [map_smul, oddShortWeyl_e, oddShortWeyl_f,
        if_neg (Ne.symm hij), if_pos rfl]
      simp only [smul_neg, neg_smul, neg_neg]
    rw [← he]
    exact H.mul_mem (H.mul_mem (hw j) (hl i j hij (-t))) (H.inv_mem (hw j))
  have hff (i j : Fin r) (hij : i ≠ j) (t : F)
      (hs : formB r F (f i,0)=0)
      (hp : (formB r F).polarBilin (f i,0) (t • (f j,0))=0) :
      siegelElement (formB r F) (f i,0) (t • (f j,0)) hs hp ∈ H := by
    have he : oddShortWeyl r F i * oddLong r F i j hij (-t) *
        (oddShortWeyl r F i)⁻¹ =
        siegelElement (formB r F) (f i,0) (t • (f j,0)) hs hp := by
      rw [oddLong, siegelElement_conj]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formB r F) ((oddShortWeyl r F i).val (e i,0))
        ((oddShortWeyl r F i).val ((-t) • (f j,0))) x =
        siegel (formB r F) (f i,0) (t • (f j,0)) x
      rw [map_smul, oddShortWeyl_e, oddShortWeyl_f, if_pos rfl, if_neg hij]
      simpa only [neg_smul] using
        siegel_neg_neg F (formB r F) (f i,0) (t • (f j,0)) x
    rw [← he]
    exact H.mul_mem (H.mul_mem (hw i) (hl i j hij (-t))) (H.inv_mem (hw i))
  have hfe (i j : Fin r) (hij : i ≠ j) (t : F)
      (hs : formB r F (f i,0)=0)
      (hp : (formB r F).polarBilin (f i,0) (t • (e j,0))=0) :
      siegelElement (formB r F) (f i,0) (t • (e j,0)) hs hp ∈ H := by
    have he : siegelElement (formB r F) (f i,0) (t • (e j,0)) hs hp =
        oddLong r F j i (Ne.symm hij) (-t) := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formB r F) (f i,0) (t • (e j,0)) x =
        siegel (formB r F) (e j,0) ((-t) • (f i,0)) x
      rw [siegel_swap F _ _ _ _ hs (by simp [e]), siegel_scale]
      simp only [smul_neg, neg_smul]
    rw [he]
    exact hl j i (Ne.symm hij) (-t)
  rw [← coordinateRootSubgroupB_eq_elementary r hr]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i,j,t,hs,hp,rfl⟩
  cases i with
  | inr i =>
    have hbad : (1 : F)=0 := by simpa [coordinateBasisB] using hs
    exact False.elim (one_ne_zero hbad)
  | inl i =>
    cases i with
    | inl i =>
      simp only [basis_e] at hs hp ⊢
      cases j with
      | inr j =>
        simp only [basis_z, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
        change oddShortUpper r F i t ∈ H
        exact hu i t
      | inl j =>
        cases j with
        | inl j =>
          simp only [basis_e] at hp ⊢
          by_cases hij : i=j
          · subst j
            change siegelElement (formB r F) (e i,0) (t • (e i,0)) _ _ ∈ H
            rw [parallel_siegel]
            exact H.one_mem
          · exact hee i j hij t _ _
        | inr j =>
          simp only [basis_f] at hp ⊢
          by_cases hij : i=j
          · subst j
            have ht : t=0 := by
              simpa [-QuadraticMap.polarBilin_apply_apply,
                polarB_apply, polarD_apply, e, f, Pi.single_apply] using hp
            subst t
            simp only [zero_smul]
            rw [zero_siegel]
            exact H.one_mem
          · exact hl i j hij t
    | inr i =>
      simp only [basis_f] at hs hp ⊢
      cases j with
      | inr j =>
        simp only [basis_z, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
        change siegelElement (formB r F) (f i,0) (0,t) _ _ ∈ H
        simpa only [oddShortLower, neg_neg] using hd i (-t)
      | inl j =>
        cases j with
        | inl j =>
          simp only [basis_e] at hp ⊢
          by_cases hij : i=j
          · subst j
            have ht : t=0 := by
              simpa [-QuadraticMap.polarBilin_apply_apply,
                polarB_apply, polarD_apply, e, f, Pi.single_apply] using hp
            subst t
            simp only [zero_smul]
            rw [zero_siegel]
            exact H.one_mem
          · exact hfe i j hij t _ _
        | inr j =>
          simp only [basis_f] at hp ⊢
          by_cases hij : i=j
          · subst j
            change siegelElement (formB r F) (f i,0) (t • (f i,0)) _ _ ∈ H
            rw [parallel_siegel]
            exact H.one_mem
          · exact hff i j hij t _ _

end Atlas.Orthogonal
