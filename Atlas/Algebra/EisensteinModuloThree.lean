import Atlas.Algebra.Eisenstein

namespace Atlas.Algebra

/-- The residue-one theta class has exactly three lifts modulo three. -/
theorem eisenstein_residue_one_mod_three (z : Eisenstein) (hz : eisensteinResidue z=1) :
    (3 : Eisenstein) ∣ z-1 ∨ (3 : Eisenstein) ∣ z-eisensteinOmega ∨
      (3 : Eisenstein) ∣ z-(-1-eisensteinOmega) := by
  obtain ⟨d,hd⟩ := (eisensteinResidue_eq_zero (z-1)).mp (by simp [hz])
  let c : Fin 3 := ⟨(eisensteinResidue d).val,ZMod.val_lt _⟩
  have hc : eisensteinResidue (d-(c.val : Eisenstein))=0 := by
    simp [c,ZMod.natCast_zmod_val]
  obtain ⟨e,he⟩ := (eisensteinResidue_eq_zero _).mp hc
  have hm : z=1+eisensteinTheta*(c.val : Eisenstein)-3*e := by
    linear_combination hd+eisensteinTheta*he+e*eisensteinTheta_sq
  have hcases : ∀ c : Fin 3,
      (3 : Eisenstein) ∣ (1+eisensteinTheta*(c.val : Eisenstein))-1 ∨
      (3 : Eisenstein) ∣ (1+eisensteinTheta*(c.val : Eisenstein))-eisensteinOmega ∨
      (3 : Eisenstein) ∣ (1+eisensteinTheta*(c.val : Eisenstein))-(-1-eisensteinOmega) := by
    intro k
    fin_cases k
    · exact Or.inl ⟨0,by simp⟩
    · right; right
      refine ⟨1+eisensteinOmega,?_⟩
      simp [eisensteinTheta]
      ring
    · right; left
      refine ⟨1+eisensteinOmega,?_⟩
      simp [eisensteinTheta]
      ring
  rcases hcases c with h|h|h
  · left
    rw [hm]
    convert dvd_sub h (dvd_mul_right (3 : Eisenstein) e) using 1 <;> ring
  · right; left
    rw [hm]
    convert dvd_sub h (dvd_mul_right (3 : Eisenstein) e) using 1 <;> ring
  · right; right
    rw [hm]
    convert dvd_sub h (dvd_mul_right (3 : Eisenstein) e) using 1 <;> ring

end Atlas.Algebra
