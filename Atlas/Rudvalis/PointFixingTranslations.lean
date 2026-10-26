import Atlas.Rudvalis.MatrixFibres
import Atlas.Rudvalis.BinaryTranslations
import Atlas.Rudvalis.CoordinateCrossRows

namespace Atlas.Rudvalis

/-- The translations preserving a Gaussian coordinate pair in row p. -/
def FixesCoordinatePair (p : Point) (A : BinaryMatrix) : Prop :=
  matrixAt A p.val=0 ∨ matrixAt A p.val=p.val

noncomputable def contractionFibreTranspose (p : E) (b : E) :
    {A : BinaryMatrix // matrixAt A p=b} ≃ {A : BinaryMatrix // matrixAt A.transpose p=b} where
  toFun A := ⟨A.val.transpose,by simpa using A.prop⟩
  invFun A := ⟨A.val.transpose,A.prop⟩
  left_inv A := Subtype.ext (Matrix.transpose_transpose _)
  right_inv A := Subtype.ext (Matrix.transpose_transpose _)

theorem contraction_fibre_card (p : Point) (b : E) :
    Nat.card {A : BinaryMatrix // matrixAt A p.val=b}=64 := by
  rw [Nat.card_congr (contractionFibreTranspose p.val b)]
  exact transposeContraction_fibre_card p.val p.prop b

noncomputable def pointFixingTranslationEquiv (p : Point) :
    {A : BinaryMatrix // FixesCoordinatePair p A} ≃
      {A : BinaryMatrix // matrixAt A p.val=0} ⊕ {A : BinaryMatrix // matrixAt A p.val=p.val} := by
  classical
  apply Equiv.Set.union
  exact Set.disjoint_left.mpr (by
    intro A ha hb
    exact p.prop (hb.symm.trans ha))

theorem pointFixingTranslations_card (p : Point) :
    Nat.card {A : BinaryMatrix // FixesCoordinatePair p A}=128 := by
  rw [Nat.card_congr (pointFixingTranslationEquiv p),Nat.card_sum,
    contraction_fibre_card,contraction_fibre_card]

theorem translation_fixes_coordinateCross_iff (A : BinaryMatrix) (p : Point) (x : E) :
    coordinateCross (coordinateTranslation A (p,x))=coordinateCross (p,x) ↔
      FixesCoordinatePair p A := by
  rw [coordinateCross_eq_iff,codeI_coordinate]
  change ((p,x+matrixAt A p.val)=(p,x) ∨ (p,x+matrixAt A p.val+p.val)=(p,x)) ↔ _
  simp only [Prod.mk.injEq,true_and,add_assoc,add_eq_left]
  have h : ∀u v : E,u+v=0 ↔ u=v := by decide +kernel
  rw [h]
  rfl

end Atlas.Rudvalis

