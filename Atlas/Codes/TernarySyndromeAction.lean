import Atlas.Codes.TernarySmallSyndromes

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def ternaryWordPermutation (g : Equiv.Perm (Fin 12)) : TernaryWord ≃ₗ[ZMod 3] TernaryWord :=
  LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) g.symm

theorem ternaryWordPermutation_code (g : TernaryPureAutomorphism) :
    ternaryGolay.map (ternaryWordPermutation g.val).toLinearMap = ternaryGolay := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact g.property v hv
  · intro hw
    refine ⟨ternaryWordPermutation g.val.symm w, (g⁻¹).property w hw, ?_⟩
    funext i
    change w (g.val (g.val.symm i)) = w i
    rw [Equiv.apply_symm_apply]

def ternarySyndromePermutation (g : TernaryPureAutomorphism) :
    TernarySyndrome ≃ₗ[ZMod 3] TernarySyndrome :=
  Submodule.Quotient.equiv _ _ (ternaryWordPermutation g.val) (ternaryWordPermutation_code g)

@[simp] theorem ternarySyndromePermutation_class (g : TernaryPureAutomorphism) (w : TernaryWord) :
    ternarySyndromePermutation g (ternarySyndromeClass w) =
      ternarySyndromeClass (fun i => w (g.val.symm i)) := rfl

theorem ternarySyndromePermutation_sum (g : TernaryPureAutomorphism) (s : TernarySyndrome) :
    ternarySyndromeSum (ternarySyndromePermutation g s) = ternarySyndromeSum s := by
  obtain ⟨w, rfl⟩ := ternaryGolay.mkQ_surjective s
  change ternarySyndromeSum (ternarySyndromePermutation g (ternarySyndromeClass w)) =
    ternarySyndromeSum (ternarySyndromeClass w)
  simp only [ternarySyndromePermutation_class, ternarySyndromeSum_class]
  exact Equiv.sum_comp g.val.symm w

def ternaryAffineSyndromePermutation (g : TernaryPureAutomorphism) :
    Equiv.Perm TernaryAffineSyndrome :=
  (ternarySyndromePermutation g).toEquiv.subtypeEquiv (fun s => by
    change ternarySyndromeSum s=1 ↔ ternarySyndromeSum (ternarySyndromePermutation g s)=1
    rw [ternarySyndromePermutation_sum])

theorem ternarySyndromePermutation_one (s : TernarySyndrome) :
    ternarySyndromePermutation 1 s = s := by
  obtain ⟨w, rfl⟩ := ternaryGolay.mkQ_surjective s
  rfl

theorem ternarySyndromePermutation_mul (g h : TernaryPureAutomorphism) (s : TernarySyndrome) :
    ternarySyndromePermutation (g*h) s = ternarySyndromePermutation g (ternarySyndromePermutation h s) := by
  obtain ⟨w, rfl⟩ := ternaryGolay.mkQ_surjective s
  rfl

instance ternaryAffineSyndromeAction : MulAction TernaryPureAutomorphism TernaryAffineSyndrome where
  smul g s := ternaryAffineSyndromePermutation g s
  one_smul s := Subtype.ext (ternarySyndromePermutation_one s.val)
  mul_smul g h s := Subtype.ext (ternarySyndromePermutation_mul g h s.val)

theorem ternarySingletonSyndrome_action (g : TernaryPureAutomorphism) (i : Fin 12) :
    g • ternarySingletonSyndrome i = ternarySingletonSyndrome (g.val i) := by
  apply Subtype.ext
  change ternarySyndromePermutation g (ternarySyndromeClass (Pi.single i 1)) = _
  rw [ternarySyndromePermutation_class]
  congr 1
  funext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

end Atlas.Codes
