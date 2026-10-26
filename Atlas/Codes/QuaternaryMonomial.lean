import Atlas.Codes.QuaternarySigns
import Mathlib.GroupTheory.SemidirectProduct

/-! All signed coordinate permutations, acting faithfully on quaternary words. -/
namespace Atlas.Codes.Quaternary
variable {ι : Type*}

def signPermutationAction : Equiv.Perm ι →* MulAut (Multiplicative (ι → Binary)) where
  toFun p :=
    { toFun := fun s => Multiplicative.ofAdd (s.toAdd ∘ p.symm)
      invFun := fun s => Multiplicative.ofAdd (s.toAdd ∘ p)
      left_inv := by intro s; change (s.toAdd ∘ p.symm ∘ p)=s.toAdd; funext i; simp
      right_inv := by intro s; change (s.toAdd ∘ p ∘ p.symm)=s.toAdd; funext i; simp
      map_mul' := by intro s t; rfl }
  map_one' := by ext s i; rfl
  map_mul' := by intro p q; ext s i; rfl

abbrev SignedCoordinates (ι : Type*) :=
  SemidirectProduct (Multiplicative (ι → Binary)) (Equiv.Perm ι) signPermutationAction

def monomialAction (g : SignedCoordinates ι) : (ι → Quat) ≃ₗ[Quat] (ι → Quat) where
  toFun w i := signedScalar (g.left.toAdd i) (w (g.right.symm i))
  invFun w i := signedScalar (g.left.toAdd (g.right i)) (w (g.right i))
  left_inv w := by ext i; simp [signedScalar]; split <;> simp_all
  right_inv w := by ext i; simp [signedScalar]; split <;> simp_all
  map_add' v w := by ext i; by_cases h : g.left.toAdd i=0 <;> simp [signedScalar,h,add_comm]
  map_smul' a w := by ext i; simp [signedScalar]

def monomialHom : SignedCoordinates ι →* ((ι → Quat) ≃ₗ[Quat] (ι → Quat)) where
  toFun := monomialAction
  map_one' := by ext w i; change signedScalar 0 (w i)=w i; simp [signedScalar]
  map_mul' g h := by
    ext w i
    change signedScalar (g.left.toAdd i+h.left.toAdd (g.right.symm i))
      (w (h.right.symm (g.right.symm i))) =
      signedScalar (g.left.toAdd i) (signedScalar (h.left.toAdd (g.right.symm i))
        (w (h.right.symm (g.right.symm i))))
    exact signedScalar_add_sign _ _ _

theorem monomialAction_reduce (g : SignedCoordinates ι) (w : ι → Quat) :
    reduce (monomialAction g w)=reduce w ∘ g.right.symm := by
  funext i
  have h : ∀ b : Binary, ∀ a : Quat, reduceScalar (signedScalar b a)=reduceScalar a := by
    decide +kernel
  exact h _ _

theorem monomialHom_injective : Function.Injective (monomialHom (ι := ι)) := by
  classical
  intro g h he
  have hp : g.right=h.right := by
    suffices hi : g.right.symm=h.right.symm from by
      simpa using congrArg Equiv.symm hi
    ext i
    by_contra hn
    let w : ι → Quat := fun j => if j=g.right.symm i then 2 else 0
    have hh := congrArg (fun f : (ι → Quat) ≃ₗ[Quat] (ι → Quat) => f w i) he
    have hz : h.right.symm i≠g.right.symm i := Ne.symm hn
    have hs : ∀ b : Binary, signedScalar b 2=2 ∧ signedScalar b 0=0 := by decide +kernel
    change signedScalar _ (w _) = signedScalar _ (w _) at hh
    simp only [w,if_pos rfl,if_neg hz] at hh
    rw [(hs _).1,(hs _).2] at hh
    exact (by decide : (2 : Quat)≠0) hh
  have hs : g.left=h.left := by
    change g.left.toAdd=h.left.toAdd
    funext i
    have hh := congrArg (fun f : (ι → Quat) ≃ₗ[Quat] (ι → Quat) => f (fun _ => 1) i) he
    have hk : ∀ b c : Binary, signedScalar b 1=signedScalar c 1 → b=c := by decide +kernel
    exact hk _ _ hh
  exact SemidirectProduct.ext hs hp

instance [Finite ι] : Finite (SignedCoordinates ι) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem monomialAction_double (g : SignedCoordinates ι) (w : ι → Binary) :
    monomialAction g (double w)=double (w ∘ g.right.symm) := by
  funext i
  have h : ∀ b c : Binary, signedScalar b (doubleScalar c)=doubleScalar c := by
    decide +kernel
  exact h _ _

end Atlas.Codes.Quaternary
