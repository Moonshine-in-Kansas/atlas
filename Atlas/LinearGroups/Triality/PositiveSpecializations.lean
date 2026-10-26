import Atlas.LinearGroups.Triality.Unipotent

/-! Single-root specializations of the unique positive coordinates. -/
noncomputable section
namespace Atlas.Triality
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

@[simp] theorem nextShortRoot_zero : nextShortRoot F K 0 = 1 := by
  have h := congrArg (fun g => g * (longWeyl F K)⁻¹) (nextShortRoot_intertwine F K 0)
  simpa [mul_assoc] using h.symm
@[simp] theorem middleRoot_zero : middleRoot F K 0 = 1 := by
  have h := congrArg (fun g => g * (shortWeyl F K * longWeyl F K)⁻¹)
    (middleRoot_intertwine F K 0)
  simpa [mul_assoc] using h.symm
@[simp] theorem highLongRoot_zero : highLongRoot F K 0 = 1 := by
  have h := congrArg (fun g => g * (shortWeyl F K)⁻¹) (highLongRoot_intertwine F K 0)
  simpa [mul_assoc] using h.symm
@[simp] theorem highestRoot_zero : highestRoot F K 0 = 1 := by
  have h := congrArg (fun g => g * (longWeyl F K)⁻¹) (highestRoot_intertwine F K 0)
  simpa [mul_assoc] using h.symm

theorem positiveMatrix_short (a : K) : positiveMatrix F K ⟨a,0,0,0,0,0⟩ = shortRoot F K a := by
  simp [positiveMatrix, positiveWord]
theorem positiveMatrix_long (b : F) : positiveMatrix F K ⟨0,b,0,0,0,0⟩ = longRoot F K b := by
  simp [positiveMatrix, positiveWord]
theorem positiveMatrix_next (c : K) : positiveMatrix F K ⟨0,0,c,0,0,0⟩ = nextShortRoot F K c := by
  simp [positiveMatrix, positiveWord]
theorem positiveMatrix_middle (d : K) : positiveMatrix F K ⟨0,0,0,d,0,0⟩ = middleRoot F K d := by
  simp [positiveMatrix, positiveWord]
theorem positiveMatrix_high (u : F) : positiveMatrix F K ⟨0,0,0,0,u,0⟩ = highLongRoot F K u := by
  simp [positiveMatrix, positiveWord]
theorem positiveMatrix_highest (v : F) : positiveMatrix F K ⟨0,0,0,0,0,v⟩ = highestRoot F K v := by
  simp [positiveMatrix, positiveWord]

end Atlas.Triality
