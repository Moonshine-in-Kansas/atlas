import Atlas.LinearGroups.Orthogonal.B2ExteriorSymplectic
import Atlas.LinearGroups.Symplectic.Center

/-! # The structural scalar kernel of the B₂ exterior-square representation

Fixing the contraction kernel forces the entire exterior square to be fixed:
Pfaffian polarization determines its other coordinates, and odd characteristic
separates the two contraction coordinates. The elementary three-row minor
identity then forces the original four-dimensional matrix to be scalar.
No group order or simplicity theorem enters these arguments.
-/
noncomputable section
namespace Atlas.Orthogonal.B2Exterior
open Matrix
variable {F : Type*} [Field F]

theorem kernelMap_eq_of_toOrthogonal_eq_one (g : Atlas.Symplectic.Sp 2 F)
    (hg : toOrthogonal g = 1) (w : LinearMap.ker (contraction (F := F))) :
    kernelMap g w = w := by
  have h := congrArg (fun z : O_B 2 F => z.val (kernelEquiv.symm w)) hg
  change kernelEquiv.symm (kernelMap g (kernelEquiv (kernelEquiv.symm w))) =
    kernelEquiv.symm w at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact kernelEquiv.symm.injective h

theorem exteriorMap_eq_of_toOrthogonal_eq_one (h2 : (2 : F) ≠ 0)
    (g : Atlas.Symplectic.Sp 2 F) (hg : toOrthogonal g = 1) (w : Six F) :
    exteriorMap (symplecticMatrix g) w = w := by
  let T := exteriorMap (symplecticMatrix g)
  have hk (b : Six F) (hb : contraction b = 0) : T b = b :=
    congrArg Subtype.val (kernelMap_eq_of_toOrthogonal_eq_one g hg ⟨b,hb⟩)
  have hp (b : Six F) (hb : contraction b = 0) :
      pfaffian (T w + b) - pfaffian (T w) = pfaffian (w + b) - pfaffian w := by
    conv_lhs => rw [← hk b hb, ← map_add]
    exact congrArg₂ (· - ·) (symplectic_pfaffian g (w+b)) (symplectic_pfaffian g w)
  have h0 := hp ![0,0,0,0,0,1] (by simp)
  have h5 := hp ![1,0,0,0,0,0] (by simp)
  have h2' := hp ![0,0,0,1,0,0] (by simp)
  have h3 := hp ![0,0,1,0,0,0] (by simp)
  have h14 := hp ![0,1,0,0,-1,0] (by simp)
  have hc := symplectic_contraction g w
  change T w 1 + T w 4 = w 1 + w 4 at hc
  simp [pfaffian_apply, Pi.add_apply, Matrix.vecHead, Matrix.vecTail] at h0 h5 h2' h3 h14
  have he1 : T w 1 = w 1 := by
    apply (mul_left_cancel₀ h2)
    linear_combination h14 + hc
  have he4 : T w 4 = w 4 := by linear_combination hc - he1
  have he0 : T w 0 = w 0 := by linear_combination h0
  have he2 : T w 2 = w 2 := by linear_combination h2'
  have he3 : T w 3 = w 3 := by linear_combination h3
  have he5 : T w 5 = w 5 := by linear_combination h5
  change T w = w
  ext i
  fin_cases i <;> assumption

/-- Every ordered minor can be recovered from the six exterior coordinates. -/
theorem wedge_eq_minor {u v x y : Four F} (h : wedge u v = wedge x y) (i j : Fin 4) :
    u i * v j - u j * v i = x i * y j - x j * y i := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp [wedge, Matrix.vecHead, Matrix.vecTail] at h0 h1 h2 h3 h4 h5
  have hn0 : u 1 * v 0 - u 0 * v 1 = x 1 * y 0 - x 0 * y 1 := by
    linear_combination -h0
  have hn1 : u 2 * v 0 - u 0 * v 2 = x 2 * y 0 - x 0 * y 2 := by
    linear_combination -h1
  have hn2 : u 3 * v 0 - u 0 * v 3 = x 3 * y 0 - x 0 * y 3 := by
    linear_combination -h2
  have hn3 : u 2 * v 1 - u 1 * v 2 = x 2 * y 1 - x 1 * y 2 := by
    linear_combination -h3
  have hn4 : u 3 * v 1 - u 1 * v 3 = x 3 * y 1 - x 1 * y 3 := by
    linear_combination -h4
  have hn5 : u 3 * v 2 - u 2 * v 3 = x 3 * y 2 - x 2 * y 3 := by
    linear_combination -h5
  fin_cases i <;> fin_cases j <;> first | assumption | simp

/-- An identity exterior square forces the original four-dimensional matrix to be scalar. -/
theorem scalar_of_exteriorMap_eq_id (A : Matrix (Fin 4) (Fin 4) F)
    (hA : ∀ w, exteriorMap A w = w) : ∃ c : F, c ^ 2 = 1 ∧ A = c • 1 := by
  have hm (i j a b : Fin 4) : A i a * A j b - A j a * A i b =
      ((Pi.single a (1 : F)) : Four F) i * ((Pi.single b (1 : F)) : Four F) j -
      ((Pi.single a (1 : F)) : Four F) j * ((Pi.single b (1 : F)) : Four F) i := by
    have h := hA (wedge (Pi.single a (1 : F)) (Pi.single b (1 : F)))
    rw [exteriorMap_wedge] at h
    simpa using wedge_eq_minor h i j
  have ho (k i : Fin 4) (hki : k ≠ i) : A k i = 0 := by
    obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by
      fin_cases k <;> fin_cases i <;> first | contradiction | decide
    have h1 := hm i j i j
    have h2 := hm i k i j
    have h3 := hm j k i j
    simp [hji, hjk, hki, Ne.symm hji, Ne.symm hjk, Ne.symm hki] at h1 h2 h3
    linear_combination -A k i * h1 + A j i * h2 - A i i * h3
  have hd (i j : Fin 4) (hij : i ≠ j) : A i i * A j j = 1 := by
    have h := hm i j i j
    simpa [hij, Ne.symm hij, ho i j hij, ho j i (Ne.symm hij)] using h
  have ha : A 0 0 ≠ 0 := by
    intro h
    have hh := hd 0 1 (by decide)
    simp [h] at hh
  have h01 := hd 0 1 (by decide)
  have h02 := hd 0 2 (by decide)
  have h12 := hd 1 2 (by decide)
  have hs : A 0 0 ^ 2 = 1 := by
    linear_combination -A 0 0 * A 0 0 * h12 + A 0 0 * A 2 2 * h01 + h02
  refine ⟨A 0 0, hs, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    by_cases hi : i = 0
    · subst i; rfl
    apply mul_left_cancel₀ ha
    have hh := hd 0 i (Ne.symm hi)
    linear_combination hh - hs
  · simp [hij, ho i j hij]

/-- The actual kernel consists of square-one scalar matrices, uniformly over odd fields. -/
theorem scalar_of_toOrthogonal_eq_one (h2 : (2 : F) ≠ 0)
    (g : Atlas.Symplectic.Sp 2 F) (hg : toOrthogonal g = 1) :
    ∃ c : F, c ^ 2 = 1 ∧ symplecticMatrix g = c • 1 :=
  scalar_of_exteriorMap_eq_id (symplecticMatrix g)
    (exteriorMap_eq_of_toOrthogonal_eq_one h2 g hg)

end Atlas.Orthogonal.B2Exterior
