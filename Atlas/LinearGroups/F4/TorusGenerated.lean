import Atlas.LinearGroups.F4.TorusRootWords

/-! The determinant-one F₄ Cartan matrix gives the full four-parameter torus,
without imposing any square condition on the field units. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def torusCorootPreimage (t : TorusParameters F) : Fin 4 → Fˣ :=
  ![t 0^2*t 1^3*t 2^4*t 3^2,
    t 0^3*t 1^6*t 2^8*t 3^4,
    t 0^2*t 1^4*t 2^6*t 3^3,
    t 0*t 1^2*t 2^3*t 3^2]

set_option maxHeartbeats 2000000 in
theorem torusCorootPreimage_identity (t : TorusParameters F) :
    simpleCorootParameters 0 (torusCorootPreimage t 0) *
      simpleCorootParameters 1 (torusCorootPreimage t 1) *
      simpleCorootParameters 2 (torusCorootPreimage t 2) *
      simpleCorootParameters 3 (torusCorootPreimage t 3) = t := by
  funext i
  apply Units.ext
  fin_cases i <;>
    simp [simpleCorootParameters,torusCorootPreimage] <;> field_simp <;> ring

/-- Every element of the actual four-parameter diagonal torus is a product
of actual Albert root automorphisms. -/
theorem diagonalTorus_mem_rootGenerated (t : TorusParameters F) :
    diagonalTorus t∈rootGenerated := by
  rw [←torusCorootPreimage_identity t]
  simp only [map_mul]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (simpleCoroot_mem_rootGenerated _ _)
        (simpleCoroot_mem_rootGenerated _ _)) (simpleCoroot_mem_rootGenerated _ _))
    (simpleCoroot_mem_rootGenerated _ _)

end Atlas.F4
