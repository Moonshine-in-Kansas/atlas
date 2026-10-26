import Atlas.Rudvalis.MatrixRankCounts

/-! Recovering affine geometry from the affine-function code on an eight-point block. -/
namespace Atlas.Rudvalis

def IsAffineFunction (f : E → Bit) : Prop :=
  ∃ a : Bit, ∃ b : E, ∀ x, f x = a + dot b x

theorem quadratic_isAffineFunction_iff (a : Bit) (b c : E) :
    IsAffineFunction (fun x => a + dot b x + quadratic c x) ↔ c = 0 := by
  constructor
  · rintro ⟨d,e,h⟩
    apply (affine_quadratic_zero (a+d) (b+e) c ?_).2.2
    intro x
    have hx := h x
    change a + dot b x + quadratic c x = d + dot e x at hx
    rw [dot_add_left]
    calc
      a + d + (dot b x + dot e x) + quadratic c x =
          (a + dot b x + quadratic c x) + (d + dot e x) := by ring
      _ = 0 := by rw [hx]; exact Atlas.Codes.bit_self_add _
  · rintro rfl
    refine ⟨a,b,?_⟩
    intro x
    simp [quadratic]

theorem normal_block_isAffineFunction_iff (a : BinaryParameters) (p : Point) :
    IsAffineFunction (fun x => binaryNormalMap a (p,x)) ↔ a.2.2 = 0 := by
  have he : (fun x => binaryNormalMap a (p,x)) =
      (fun x => a.1 p + dot (matrixAt a.2.1 p.val + eta p a.2.2) x + quadratic a.2.2 x) := by
    funext x
    change a.1 p + dot (matrixAt a.2.1 p.val) x + theta p a.2.2 x = _
    rw [dot_add_left]
    simp only [theta]
    ring
  rw [he,quadratic_isAffineFunction_iff]

theorem affine_code_permutation (g : Equiv.Perm E)
    (hg : ∀ f : E → Bit, IsAffineFunction f → IsAffineFunction (f ∘ g)) :
    ∃ A : BinaryMatrix, ∃ t : E, IsUnit A ∧ ∀ x, g x = matrixAt A x + t := by
  classical
  have hcoord (i : Fin 3) : ∃ a : Bit, ∃ b : E, ∀ x, (g x) i = a + dot b x := by
    have hb (x : E) : dot (basisPoint i).val x = x i := by
      fin_cases i <;> simp [basisPoint,binaryLabel,dot,Fin.sum_univ_succ]
    have hf : IsAffineFunction (fun x : E => x i) := ⟨0,(basisPoint i).val,by simp [hb]⟩
    exact hg _ hf
  choose a b hab using hcoord
  let A : BinaryMatrix := fun i => b i
  have he (x : E) : g x = matrixAt A x + a := by
    ext i
    change (g x) i = dot (b i) x + a i
    rw [hab i x,add_comm]
  have hinj : Function.Injective (matrixAt A) := by
    intro x y h
    apply g.injective
    rw [he x,he y,h]
  refine ⟨A,a,?_,he⟩
  exact Matrix.mulVec_injective_iff_isUnit.mp hinj

end Atlas.Rudvalis
