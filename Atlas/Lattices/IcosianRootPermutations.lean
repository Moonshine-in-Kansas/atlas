import Atlas.Lattices.IcosianRoots

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

def icosianPermute (p : Equiv.Perm (Fin 3)) (x : IcosianCoordinates) : IcosianCoordinates :=
  fun i => x (p.symm i)

theorem icosianPermute_mem (p : Equiv.Perm (Fin 3)) (x : IcosianCoordinates)
    (hx : x∈icosianLeechModule) : icosianPermute p x∈icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue] at hx ⊢
  intro j
  exact icosianGluePermute_mem p (icosianGlueColumn (fun i => icosianModuloTwo (x i)) j) (hx j)

theorem icosianPermute_hermitian (p : Equiv.Perm (Fin 3)) (x y : IcosianCoordinates) :
    icosianHermitian (icosianCoordinateEmbedding (icosianPermute p x))
      (icosianCoordinateEmbedding (icosianPermute p y))=
    icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding y) := by
  change (1/2 : ℚ) • (∑ i,star (x (p.symm i)).val*(y (p.symm i)).val)=
    (1/2 : ℚ) • (∑ i,star (x i).val*(y i).val)
  exact congrArg (fun z => (1/2 : ℚ) • z)
    (Equiv.sum_comp p.symm (fun i => star (x i).val*(y i).val))

def icosianRootPermute (p : Equiv.Perm (Fin 3)) : IcosianRoot ≃ IcosianRoot where
  toFun r := ⟨icosianPermute p r.val,icosianPermute_mem p r.val r.property.1,
    by rw [icosianPermute_hermitian]; exact r.property.2⟩
  invFun r := ⟨icosianPermute p.symm r.val,icosianPermute_mem p.symm r.val r.property.1,
    by rw [icosianPermute_hermitian]; exact r.property.2⟩
  left_inv r := by apply Subtype.ext; funext i; simp [icosianPermute]
  right_inv r := by apply Subtype.ext; funext i; simp [icosianPermute]

@[simp] theorem icosianRootPermute_apply (p : Equiv.Perm (Fin 3)) (r : IcosianRoot) (i : Fin 3) :
    (icosianRootPermute p r).val i=r.val (p.symm i) := rfl

end Atlas.Lattices
