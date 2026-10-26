import Atlas.Algebra.Albert.ZeroDiagonalCount
import Atlas.Algebra.Albert.Adjoint

noncomputable section
namespace Atlas.Albert.ZeroDiagonal
variable {F : Type*} [Field F]

private theorem conjugate_eq_zero (v : SplitOctonion.Carrier F) :
    SplitOctonion.conjugate v=0 ↔ v=0 := by
  have hz : SplitOctonion.conjugate (0 : SplitOctonion.Carrier F)=0 := by
    ext i
    fin_cases i <;> simp [SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit]
  constructor
  · intro h
    have := congrArg SplitOctonion.conjugate h
    simpa [SplitOctonion.conjugate_conjugate,hz] using this
  · rintro rfl; exact hz

private theorem vec3_zero {X : Type*} [Zero X] (a b c : X) :
    (![a,b,c] : Fin 3→X)=0 ↔ a=0 ∧ b=0 ∧ c=0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩
  · rintro ⟨rfl,rfl,rfl⟩
    ext i; fin_cases i <;> rfl

theorem adjoint_zero_diagonal_iff (A B C : SplitOctonion.Carrier F) :
    adjoint (0,![A,B,C])=0 ↔
      SplitOctonion.norm B=0 ∧ SplitOctonion.norm A=0 ∧ SplitOctonion.mul A B=0 ∧
      SplitOctonion.norm C=0 ∧ SplitOctonion.mul B C=0 ∧ SplitOctonion.mul C A=0 := by
  change ((![0*0-SplitOctonion.norm A,0*0-SplitOctonion.norm B,0*0-SplitOctonion.norm C],
    ![SplitOctonion.conjugate (SplitOctonion.mul B C)-0 • A,
      SplitOctonion.conjugate (SplitOctonion.mul C A)-0 • B,
      SplitOctonion.conjugate (SplitOctonion.mul A B)-0 • C])=(0,0)) ↔ _
  simp only [Prod.mk.injEq,zero_mul,zero_sub,zero_smul,sub_zero,vec3_zero,neg_eq_zero,
    conjugate_eq_zero]
  tauto

abbrev Locus (F : Type*) [Field F] :=
  {x : Atlas.Albert.Carrier F // x.1=0 ∧ adjoint x=0}

def dataEquivLocus : Data F ≃ Locus F where
  toFun d := ⟨(0,![d.2.1.val,d.1.val,d.2.2.val]),rfl,
    (adjoint_zero_diagonal_iff _ _ _).mpr
      ⟨d.1.prop,d.2.1.prop.1,d.2.1.prop.2,d.2.2.prop⟩⟩
  invFun x := by
    have hx : x.val=(0,![x.val.2 0,x.val.2 1,x.val.2 2]) := by
      apply Prod.ext
      · exact x.prop.1
      · ext i; fin_cases i <;> rfl
    have h := (adjoint_zero_diagonal_iff _ _ _).mp (hx ▸ x.prop.2)
    exact ⟨⟨x.val.2 1,h.1⟩,⟨x.val.2 0,h.2.1,h.2.2.1⟩,
      ⟨x.val.2 2,h.2.2.2⟩⟩
  left_inv d := by rcases d with ⟨B,A,C⟩; rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact x.prop.1.symm
    · ext i; fin_cases i <;> rfl

theorem card_locus [Finite F] : Nat.card (Locus F)=
    1+((Nat.card F^4-1)*(Nat.card F^3+1))*
      (2*Nat.card F^4+1+(Nat.card F^4-1)*Nat.card F^3) := by
  rw [←Nat.card_congr dataEquivLocus,card_data]

end Atlas.Albert.ZeroDiagonal
