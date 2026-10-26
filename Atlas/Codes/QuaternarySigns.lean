import Atlas.Codes.QuaternaryLayers

/-! Signs of quaternary words and their exact torsion criterion. -/
namespace Atlas.Codes.Quaternary

def signedScalar (b : Binary) (a : Quat) : Quat := if b=0 then a else -a

theorem signedScalar_difference (b : Binary) (a : Quat) :
    signedScalar b a=a-doubleScalar (b*reduceScalar a) := by
  decide +kernel +revert

theorem signedScalar_add_sign (b c : Binary) (a : Quat) :
    signedScalar (b+c) a=signedScalar b (signedScalar c a) := by
  decide +kernel +revert

variable {ι : Type*}

def signChange (s : ι → Binary) : (ι → Quat) ≃ₗ[Quat] (ι → Quat) where
  toFun w i := signedScalar (s i) (w i)
  invFun w i := signedScalar (s i) (w i)
  left_inv w := by ext i; simp [signedScalar]; split <;> simp_all
  right_inv w := by ext i; simp [signedScalar]; split <;> simp_all
  map_add' v w := by ext i; by_cases h : s i=0 <;> simp [signedScalar,h,add_comm]
  map_smul' a w := by ext i; simp [signedScalar]

theorem signChange_difference (s : ι → Binary) (w : ι → Quat) :
    signChange s w=w-double (fun i => s i*reduce w i) := by
  ext i
  exact signedScalar_difference _ _

def signChangeHom : Multiplicative (ι → Binary) →* ((ι → Quat) ≃ₗ[Quat] (ι → Quat)) where
  toFun s := signChange s.toAdd
  map_one' := by ext w i; simp [signChange,signedScalar]
  map_mul' s t := by ext w i; exact signedScalar_add_sign _ _ _

theorem signChangeHom_injective : Function.Injective (signChangeHom (ι := ι)) := by
  intro s t h
  change s.toAdd=t.toAdd
  funext i
  have he := congrArg (fun g : (ι → Quat) ≃ₗ[Quat] (ι → Quat) => g (fun _ => 1) i) h
  have hk : ∀ b c : Binary, signedScalar b 1=signedScalar c 1 → b=c := by decide +kernel
  exact hk _ _ he

theorem signs_preserve_iff (Q : Submodule Quat (ι → Quat))
    (D : Submodule Binary (ι → Binary))
    (hres : ∀ d, d∈D ↔ ∃ q, q∈Q ∧ reduce q=d) (s : ι → Binary) :
    (∀ q, q∈Q → signChange s q∈Q) ↔
      ∀ d, d∈D → double (fun i => s i*d i)∈Q := by
  constructor
  · intro h d hd
    obtain ⟨q,hq,hr⟩ := (hres d).mp hd
    have hm := Q.sub_mem hq (h q hq)
    rw [signChange_difference,sub_sub_cancel,hr] at hm
    exact hm
  · intro h q hq
    rw [signChange_difference]
    exact Q.sub_mem hq (h (reduce q) ((hres _).mpr ⟨q,hq,rfl⟩))

end Atlas.Codes.Quaternary
