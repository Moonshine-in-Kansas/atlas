import Atlas.Algebra.SplitOctonion.AnnihilatorCommon
import Atlas.Algebra.SplitOctonion.IsotropicCount

/-! The zero-diagonal rank-one locus, counted by actual annihilator fibres. -/
noncomputable section
namespace Atlas.Albert.ZeroDiagonal
open Atlas.SplitOctonion Atlas.SplitOctonion.Annihilator
variable {F : Type*} [Field F]

@[simp] private theorem oct_mul_zero (v : Atlas.SplitOctonion.Carrier F) : mul v 0=0 :=
  (multiplication v).map_zero

@[simp] private theorem oct_zero_mul (v : Atlas.SplitOctonion.Carrier F) : mul 0 v=0 :=
  (multiplication.flip v).map_zero

abbrev NormZero (F : Type*) [Field F] := {v : Atlas.SplitOctonion.Carrier F // SplitOctonion.norm v=0}
def Incident (B : Atlas.SplitOctonion.Carrier F) := {A : Atlas.SplitOctonion.Carrier F // SplitOctonion.norm A=0 ∧ mul A B=0}
def Completion (A B : Atlas.SplitOctonion.Carrier F) :=
  {C : Atlas.SplitOctonion.Carrier F // SplitOctonion.norm C=0 ∧ mul B C=0 ∧ mul C A=0}
abbrev Data (F : Type*) [Field F] :=
  Σ B : NormZero F, Σ A : Incident B.val, Completion A.val B.val

def incidentZeroEquiv : Incident (0 : Atlas.SplitOctonion.Carrier F) ≃ NormZero F where
  toFun A := ⟨A.val,A.prop.1⟩
  invFun A := ⟨A.val,A.prop,by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

def incidentEquiv (B : Atlas.SplitOctonion.Carrier F) (hB : B≠0) : Incident B ≃ leftAnnihilator B where
  toFun A := ⟨A.val,A.prop.2⟩
  invFun A := ⟨A.val,norm_of_leftAnnihilator B hB A,A.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

def completionZeroZeroEquiv : Completion (0 : Atlas.SplitOctonion.Carrier F) 0 ≃ NormZero F where
  toFun C := ⟨C.val,C.prop.1⟩
  invFun C := ⟨C.val,C.prop,by simp,by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

def completionZeroLeftEquiv (B : Atlas.SplitOctonion.Carrier F) (hB : B≠0) :
    Completion 0 B ≃ rightAnnihilator B where
  toFun C := ⟨C.val,C.prop.2.1⟩
  invFun C := ⟨C.val,norm_of_rightAnnihilator B hB C,C.prop,by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

def completionZeroRightEquiv (A : Atlas.SplitOctonion.Carrier F) (hA : A≠0) :
    Completion A 0 ≃ leftAnnihilator A where
  toFun C := ⟨C.val,C.prop.2.2⟩
  invFun C := ⟨C.val,norm_of_leftAnnihilator A hA C,by simp,C.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

def completionCommonEquiv (A B : Atlas.SplitOctonion.Carrier F) (hB : B≠0) :
    Completion A B ≃ commonAnnihilator A B where
  toFun C := ⟨C.val,C.prop.2⟩
  invFun C := ⟨C.val,norm_of_rightAnnihilator B hB ⟨C.val,C.prop.1⟩,C.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_one_exception {X : Type*} [Fintype X] (x : X) (f : X→ℕ)
    (a b : ℕ) (hx : f x=a) (hrest : ∀y,y≠x→f y=b) :
    ∑y,f y=a+(Fintype.card X-1)*b := by
  classical
  calc
    ∑y,f y = f x+∑y∈Finset.univ.erase x,f y :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
    _ = a+(Fintype.card X-1)*b := by
      rw [hx]
      congr 1
      rw [Finset.sum_congr rfl (fun y hy=>hrest y (Finset.mem_erase.mp hy).1)]
      simp

variable [Finite F]

instance (B : Atlas.SplitOctonion.Carrier F) : Finite (Incident B) := by
  unfold Incident
  infer_instance

instance (A B : Atlas.SplitOctonion.Carrier F) : Finite (Completion A B) := by
  unfold Completion
  infer_instance

theorem card_incident (B : Atlas.SplitOctonion.Carrier F) (hB : SplitOctonion.norm B=0) (hB0 : B≠0) :
    Nat.card (Incident B)=Nat.card F^4 :=
  (Nat.card_congr (incidentEquiv B hB0)).trans (leftAnnihilator_card B hB hB0)

theorem card_completion_nonzero (A B : Atlas.SplitOctonion.Carrier F) (hB : SplitOctonion.norm B=0)
    (hA0 : A≠0) (hB0 : B≠0) (hAB : mul A B=0) :
    Nat.card (Completion A B)=Nat.card F^3 :=
  (Nat.card_congr (completionCommonEquiv A B hB0)).trans
    (commonAnnihilator_card A B hB hA0 hB0 hAB)

theorem card_nonzero_fibre (B : Atlas.SplitOctonion.Carrier F) (hB : SplitOctonion.norm B=0) (hB0 : B≠0) :
    Nat.card (Σ A : Incident B, Completion A.val B)=
      Nat.card F^4+(Nat.card F^4-1)*Nat.card F^3 := by
  classical
  letI := Fintype.ofFinite (Incident B)
  let z : Incident B := ⟨0,by simp [SplitOctonion.norm]⟩
  rw [Nat.card_sigma]
  have hz : Nat.card (Completion z.val B)=Nat.card F^4 :=
    (Nat.card_congr (completionZeroLeftEquiv B hB0)).trans (rightAnnihilator_card B hB hB0)
  have hn (A : Incident B) (hA : A≠z) :
      Nat.card (Completion A.val B)=Nat.card F^3 := by
    exact card_completion_nonzero A.val B hB
      (fun h=>hA (Subtype.ext h)) hB0 A.prop.2
  rw [sum_one_exception z _ _ _ hz hn,←Nat.card_eq_fintype_card,card_incident B hB hB0]

theorem card_zero_fibre :
    Nat.card (Σ A : Incident (0 : Atlas.SplitOctonion.Carrier F), Completion A.val 0)=
      (Nat.card F^4+(Nat.card F^4-1)*Nat.card F^3)+
      ((Nat.card F^4-1)*(Nat.card F^3+1))*Nat.card F^4 := by
  classical
  letI := Fintype.ofFinite (Incident (0 : Atlas.SplitOctonion.Carrier F))
  let z : Incident (0 : Atlas.SplitOctonion.Carrier F) := ⟨0,by simp [SplitOctonion.norm]⟩
  rw [Nat.card_sigma]
  have hz : Nat.card (Completion z.val 0)=Nat.card (NormZero F) :=
    Nat.card_congr completionZeroZeroEquiv
  have hn (A : Incident (0 : Atlas.SplitOctonion.Carrier F)) (hA : A≠z) :
      Nat.card (Completion A.val 0)=Nat.card F^4 := by
    have ha : A.val≠0 := fun h=>hA (Subtype.ext h)
    exact (Nat.card_congr (completionZeroRightEquiv A.val ha)).trans
      (leftAnnihilator_card A.val A.prop.1 ha)
  rw [sum_one_exception z _ _ _ hz hn,←Nat.card_eq_fintype_card,
    Nat.card_congr incidentZeroEquiv,card_norm_zero]
  have hq : 1≤Nat.card F^4 := one_le_pow₀ (by
    have := Finite.one_lt_card (α:=F)
    omega)
  congr 1
  congr 1
  rw [_root_.mul_add,mul_one]
  omega

theorem card_data : Nat.card (Data F)=
    1+((Nat.card F^4-1)*(Nat.card F^3+1))*
      (2*Nat.card F^4+1+(Nat.card F^4-1)*Nat.card F^3) := by
  classical
  letI := Fintype.ofFinite (NormZero F)
  let z : NormZero F := ⟨0,by simp [SplitOctonion.norm]⟩
  change Nat.card (Σ B : NormZero F, Σ A : Incident B.val, Completion A.val B.val)=_
  rw [Nat.card_sigma]
  have hn (B : NormZero F) (hB : B≠z) :=
    card_nonzero_fibre B.val B.prop (fun h=>hB (Subtype.ext h))
  rw [sum_one_exception z _ _ _ card_zero_fibre hn,←Nat.card_eq_fintype_card,card_norm_zero]
  have hq : 1≤Nat.card F^4 := one_le_pow₀ (by
    have := Finite.one_lt_card (α:=F)
    omega)
  have he : Nat.card F^4+(Nat.card F^4-1)*Nat.card F^3 =
      1+(Nat.card F^4-1)*(Nat.card F^3+1) := by
    rw [_root_.mul_add,mul_one]
    omega
  rw [he]
  simp only [Nat.add_sub_cancel_left]
  have he' : Nat.card F^4 = 1+(Nat.card F^4-1) := by omega
  rw [he']
  simp only [Nat.add_sub_cancel_left]
  ring

end Atlas.Albert.ZeroDiagonal
