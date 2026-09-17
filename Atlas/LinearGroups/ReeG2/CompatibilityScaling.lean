import Atlas.LinearGroups.ReeG2.PointCompatibility

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem pointCompatibility_scale (m : ℕ) {v w : Vector F}
    (h : pointCompatibility m v w) (l : F) (hl : l ≠ 0) :
    pointCompatibility m (fun i => l * v i) (fun i => (sigma F m l / l) * w i) := by
  have he (i j : Fin 7) :
      wedgeCoordinate (fun i => l * v i) (fun i => (sigma F m l / l) * w i) i j =
      sigma F m l * wedgeCoordinate v w i j := by
    unfold wedgeCoordinate
    field_simp
    <;> ring
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  simp only [pointCompatibility, exteriorKernel, he, map_mul, ← mul_neg, ← mul_add]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact congrArg (fun x => sigma F m l * x) k0
    | exact congrArg (fun x => sigma F m l * x) k1
    | exact congrArg (fun x => sigma F m l * x) k2
    | exact congrArg (fun x => sigma F m l * x) k3
    | exact congrArg (fun x => sigma F m l * x) k4
    | exact congrArg (fun x => sigma F m l * x) k5
    | exact congrArg (fun x => sigma F m l * x) k6
    | exact congrArg (fun x => sigma F m l * x) s0
    | exact congrArg (fun x => sigma F m l * x) s1
    | exact congrArg (fun x => sigma F m l * x) s2
    | exact congrArg (fun x => sigma F m l * x) s3
    | exact congrArg (fun x => sigma F m l * x) s4
    | exact congrArg (fun x => sigma F m l * x) s5
    | exact congrArg (fun x => sigma F m l * x) s6

end Atlas.ReeG2
