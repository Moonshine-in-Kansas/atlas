import Atlas.LinearGroups.Triality.Basic
import Atlas.LinearGroups.Orthogonal.FieldTransport

/-! Coordinatewise transport of the literal triality generators. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {K L : Type*} [Field K] [Field L]

theorem fieldEquiv_differenceRoot (e : K ≃+* L) (i j : Fin 4) (h : i ≠ j) (t : K) :
    fieldEquivFullD e (differenceRoot i j h t)=differenceRoot i j h (e t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  change e ((differenceRoot i j h t).val (fun k => e.symm (x k)) k) =
    (differenceRoot i j h (e t)).val x k
  rcases k with k|k <;>
    simp [differenceRoot_apply,Atlas.Orthogonal.e,Atlas.Orthogonal.f,Pi.single_apply,Algebra.smul_def]
  all_goals split_ifs <;> simp_all

theorem fieldEquiv_sumRoot (e : K ≃+* L) (i j : Fin 4) (t : K) :
    fieldEquivFullD e (sumRoot i j t)=sumRoot i j (e t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  change e ((sumRoot i j t).val (fun k => e.symm (x k)) k) =
    (sumRoot i j (e t)).val x k
  rcases k with k|k <;>
    simp [sumRoot_apply,Atlas.Orthogonal.e,Atlas.Orthogonal.f,Pi.single_apply,Algebra.smul_def]
  all_goals split_ifs <;> simp_all

theorem fieldEquiv_negativeSumRoot (e : K ≃+* L) (i j : Fin 4) (t : K) :
    fieldEquivFullD e (negativeSumRoot i j t)=negativeSumRoot i j (e t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext k
  change e ((negativeSumRoot i j t).val (fun k => e.symm (x k)) k) =
    (negativeSumRoot i j (e t)).val x k
  rcases k with k|k <;>
    simp [negativeSumRoot_apply,Atlas.Orthogonal.e,Atlas.Orthogonal.f,Pi.single_apply,Algebra.smul_def]
  all_goals split_ifs <;> simp_all

theorem fieldEquiv_pinnedRoot (e : K ≃+* L) (i : Fin 4) (t : K) :
    fieldEquivFullD e (pinnedRoot i t)=pinnedRoot i (e t) := by
  fin_cases i <;> simp [pinnedRoot,fieldEquiv_differenceRoot,fieldEquiv_sumRoot]

theorem fieldEquiv_pinnedNegativeRoot (e : K ≃+* L) (i : Fin 4) (t : K) :
    fieldEquivFullD e (pinnedNegativeRoot i t)=pinnedNegativeRoot i (e t) := by
  fin_cases i <;> simp [pinnedNegativeRoot,fieldEquiv_differenceRoot,fieldEquiv_negativeSumRoot]

variable {F E : Type*} [Field F] [Field E] [Finite F] [Finite E]
  [Finite K] [Finite L] [Algebra F K] [Algebra E L]

theorem fieldEquiv_sigma (e : K ≃+* L) (hcard : Nat.card F=Nat.card E) (t : K) :
    e (FiniteCubic.sigma F K t)=FiniteCubic.sigma E L (e t) := by
  simp only [FiniteCubic.sigma_apply,map_pow,hcard]

theorem fieldEquiv_shortRoot (e : K ≃+* L) (hcard : Nat.card F=Nat.card E) (t : K) :
    fieldEquivFullD e (shortRoot F K t)=shortRoot E L (e t) := by
  simp only [shortRoot,map_mul,fieldEquiv_pinnedRoot,fieldEquiv_sigma e hcard]

theorem fieldEquiv_shortNegativeRoot (e : K ≃+* L) (hcard : Nat.card F=Nat.card E) (t : K) :
    fieldEquivFullD e (shortNegativeRoot F K t)=shortNegativeRoot E L (e t) := by
  simp only [shortNegativeRoot,map_mul,fieldEquiv_pinnedNegativeRoot,fieldEquiv_sigma e hcard]

theorem fieldEquiv_longRoot (eF : F ≃+* E) (eK : K ≃+* L)
    (hcompat : ∀ t, eK (algebraMap F K t)=algebraMap E L (eF t)) (t : F) :
    fieldEquivFullD eK (longRoot F K t)=longRoot E L (eF t) := by
  simp only [longRoot,fieldEquiv_pinnedRoot,hcompat]

theorem fieldEquiv_longNegativeRoot (eF : F ≃+* E) (eK : K ≃+* L)
    (hcompat : ∀ t, eK (algebraMap F K t)=algebraMap E L (eF t)) (t : F) :
    fieldEquivFullD eK (longNegativeRoot F K t)=longNegativeRoot E L (eF t) := by
  simp only [longNegativeRoot,fieldEquiv_pinnedNegativeRoot,hcompat]

theorem fieldEquiv_generated (eF : F ≃+* E) (eK : K ≃+* L)
    (hcompat : ∀ t, eK (algebraMap F K t)=algebraMap E L (eF t)) :
    (generated F K).map (fieldEquivFullD eK).toMonoidHom=generated E L := by
  have hcard : Nat.card F=Nat.card E := Nat.card_congr eF.toEquiv
  rw [generated,MonoidHom.map_closure,generated]
  congr 1
  ext g
  constructor
  · rintro ⟨x,(((⟨a,rfl⟩|⟨a,rfl⟩)|⟨b,rfl⟩)|⟨b,rfl⟩),rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨eK a,fieldEquiv_shortRoot eK hcard a |>.symm⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨eK a,fieldEquiv_shortNegativeRoot eK hcard a |>.symm⟩))
    · exact Or.inl (Or.inr ⟨eF b,fieldEquiv_longRoot eF eK hcompat b |>.symm⟩)
    · exact Or.inr ⟨eF b,fieldEquiv_longNegativeRoot eF eK hcompat b |>.symm⟩
  · rintro (((⟨a,rfl⟩|⟨a,rfl⟩)|⟨b,rfl⟩)|⟨b,rfl⟩)
    · refine ⟨shortRoot F K (eK.symm a),Or.inl (Or.inl (Or.inl ⟨_,rfl⟩)),?_⟩
      simpa using fieldEquiv_shortRoot eK hcard (eK.symm a)
    · refine ⟨shortNegativeRoot F K (eK.symm a),Or.inl (Or.inl (Or.inr ⟨_,rfl⟩)),?_⟩
      simpa using fieldEquiv_shortNegativeRoot eK hcard (eK.symm a)
    · refine ⟨longRoot F K (eF.symm b),Or.inl (Or.inr ⟨_,rfl⟩),?_⟩
      simpa using fieldEquiv_longRoot eF eK hcompat (eF.symm b)
    · refine ⟨longNegativeRoot F K (eF.symm b),Or.inr ⟨_,rfl⟩,?_⟩
      simpa using fieldEquiv_longNegativeRoot eF eK hcompat (eF.symm b)

def fieldEquiv (eF : F ≃+* E) (eK : K ≃+* L)
    (hcompat : ∀ t, eK (algebraMap F K t)=algebraMap E L (eF t)) : Group F K ≃* Group E L :=
  (fieldEquivFullD eK).subgroupMap (generated F K) |>.trans
    (MulEquiv.subgroupCongr (fieldEquiv_generated eF eK hcompat))

end Atlas.Triality
