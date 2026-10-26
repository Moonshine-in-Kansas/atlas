import Atlas.Comparisons.Exceptional.E6.Roots

/-! Binary reduction identifies precisely opposite pairs of integral roots. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice

def reduceBinary (x : Fin 6 → ℤ) : Fin 6 → ZMod 2 := fun i => x i

theorem norm_reduceBinary (x : Fin 6 → ℤ) :
    norm (reduceBinary x) = ((norm x : ℤ) : ZMod 2) := by
  simp [norm,reduceBinary]

theorem norm_neg (x : Fin 6 → ℤ) : norm (-x) = norm x := by
  simp [norm]

theorem root_reduction_pair (x y : Fin 6 → ℤ)
    (hx : norm x = 1) (hy : norm y = 1)
    (hxy : reduceBinary x = reduceBinary y) : y = x ∨ y = -x := by
  have hd (i : Fin 6) : (2 : ℤ) ∣ y i - x i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (y i) 2).mp
      (congrFun hxy i)
  choose u hu using hd
  have he : y = fun i => x i + 2 * u i := by
    funext i
    have := hu i
    omega
  have hp : norm u + norm (x+u) = 1 := by
    have hid : norm (fun i => x i + 2 * u i) + norm x =
        2 * norm u + 2 * norm (x+u) := by
      simp [norm]
      ring
    rw [← he,hy,hx] at hid
    omega
  have hu0 := norm_nonneg u
  have hv0 := norm_nonneg (x+u)
  have hz : norm u = 0 ∨ norm (x+u) = 0 := by omega
  rcases hz with hz | hz
  · left
    have hu := (norm_eq_zero_iff u).mp hz
    simp [he,hu]
  · right
    have hv := (norm_eq_zero_iff (x+u)).mp hz
    funext i
    have hv' := congrFun hv i
    have he' := congrFun he i
    simp only [Pi.add_apply,Pi.zero_apply,Pi.neg_apply] at hv' he' ⊢
    omega

end Atlas.Comparisons.E6Lattice
