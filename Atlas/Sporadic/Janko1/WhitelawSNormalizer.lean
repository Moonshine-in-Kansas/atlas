import Atlas.Sporadic.Janko1.WhitelawExactCount

/-!
Uncompiled source-only successor. The actual S normalizes the actual complement
<P,Q>. This moves the 21 complementary factors outside an S-membership test.
The two matrix identities are split into scalar entries; no group is enumerated.
-/
noncomputable section
namespace Atlas.Janko1
open scoped Pointwise

def sCoordinateAction (v : Fin 7 → Field) : Fin 7 → Field :=
  Matrix.mulVec (imaginaryGeneratorMatrix 3) v

def signedWhitelawSeed (r : Fin 10) (a : SignParameters) (k : Fin 7) : Field :=
  signCharacter a k * whitelawSeed r k

theorem imaginaryCoordinateAction_S (v : Fin 7 → Field) :
    imaginaryCoordinateAction S v = sCoordinateAction v := by
  funext k
  exact imaginaryCoordinateAction_generator 3 v k

theorem sCoordinateAction_ne_zero (v : Fin 7 → Field) (hv : v ≠ 0) :
    sCoordinateAction v ≠ 0 := by
  rw [← imaginaryCoordinateAction_S]
  simpa using (imaginaryCoordinateAction S).injective.ne hv

theorem S_smul_S (p : ProjV) : S • (S • p) = p := by
  rw [← mul_smul, ← pow_two, S_pow, one_smul]

set_option maxRecDepth 8192 in
theorem P_S_P_matrix_entry (i j : Fin 8) :
    (generatorMatrix 0 * generatorMatrix 3 * generatorMatrix 0) i j =
      generatorMatrix 3 i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem P_mul_S_mul_P : P * S * P = S := by
  apply coordinateRepresentation_injective
  simp only [map_mul, coordinateRepresentation_P, coordinateRepresentation_S]
  ext i j
  exact P_S_P_matrix_entry i j

theorem S_mul_P : S * P = P⁻¹ * S := by
  calc
    S * P = P⁻¹ * (P * S * P) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = P⁻¹ * S := by rw [P_mul_S_mul_P]

set_option maxRecDepth 8192 in
theorem S_Q_matrix_entry (i j : Fin 8) :
    (generatorMatrix 3 * generatorMatrix 1) i j =
      (generatorMatrix 1 * generatorMatrix 3) i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem S_mul_Q : S * Q = Q * S := by
  apply coordinateRepresentation_injective
  simp only [map_mul, coordinateRepresentation_S, coordinateRepresentation_Q]
  ext i j
  exact S_Q_matrix_entry i j

theorem S_conjugates_P : S * P * S⁻¹ = P⁻¹ := by
  rw [S_mul_P, mul_assoc, mul_inv_cancel, mul_one]

theorem S_conjugates_Q : S * Q * S⁻¹ = Q := by
  rw [S_mul_Q, mul_assoc, mul_inv_cancel, mul_one]

theorem S_mem_pqSubgroup_normalizer :
    S ∈ Subgroup.normalizer (pqSubgroup : Set (G2.Model Field)) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨⟨i, j⟩, he⟩ := pqNormalFormEquiv.surjective ⟨g, hg⟩
  have he' : P ^ i.val * Q ^ j.val = g := by
    simpa only [pqNormalFormEquiv_apply] using
      congrArg (fun x : pqSubgroup => (x : G2.Model Field)) he
  rw [← he', ← conj_mul, ← conj_pow, ← conj_pow, S_conjugates_P, S_conjugates_Q]
  exact pqSubgroup.mul_mem
    (pqSubgroup.pow_mem (pqSubgroup.inv_mem P_mem_pqSubgroup) i.val)
    (pqSubgroup.pow_mem Q_mem_pqSubgroup j.val)

/-- Right signs in the existing H, obtained from its already proved internal product. -/
theorem H_right_sign_factorization (h : H) :
    ∃ (c : pqSubgroup) (a : SignParameters),
      (h : G2.Model Field) = (c : G2.Model Field) * signElement a := by
  have hh : (h : G2.Model Field) ∈
      (pqSubgroup : Set (G2.Model Field)) * (signSubgroup : Set (G2.Model Field)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right pqSubgroup signSubgroup
      pqSubgroup_le_sign_normalizer, sup_comm, ← H_eq_signSubgroup_sup_pqSubgroup]
    exact h.property
  obtain ⟨c, hc, e, he, hce⟩ := hh
  change ∃ a : Multiplicative SignParameters, signHom a = e at he
  obtain ⟨a, rfl⟩ := he
  exact ⟨⟨c, hc⟩, a.toAdd, hce.symm⟩

end Atlas.Janko1
