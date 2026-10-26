import Atlas.LinearGroups.SuzukiFamily.Model

/-! The actual two-parameter root subgroup inside the existing symplectic group. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem rootElement_zero (m : ℕ) : rootElement m (0:F) 0 = 1 := by
  apply Subtype.ext
  change toStandard (u m 0 0) = 1
  rw [u_zero,map_one]

theorem rootElement_mul (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b c d : F) :
    rootElement m a b * rootElement m c d =
      rootElement m (a+c) (b+d+a*theta F m c) := by
  apply Subtype.ext
  change toStandard (u m a b) * toStandard (u m c d) = _
  rw [← map_mul,u_mul m hcard]
  rfl

theorem rootElement_injective (m : ℕ) :
    Function.Injective (fun p : F × F => rootElement m p.1 p.2) := by
  intro p q he
  apply u_injective m
  apply toStandard.injective
  exact congrArg Subtype.val he

theorem rootElement_inv (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    (rootElement m a b)⁻¹ = rootElement m a (b+a*theta F m a) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change toStandard (u m a b) * toStandard (u m a (b+a*theta F m a)) = 1
  rw [← map_mul,u_mul_inverse m hcard,map_one]

def rootSubgroup (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Subgroup (Atlas.Symplectic.Sp 2 F) where
  carrier := Set.range (fun p : F × F => rootElement m p.1 p.2)
  one_mem' := ⟨(0,0),rootElement_zero m⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a,b⟩,rfl⟩ ⟨⟨c,d⟩,rfl⟩
    exact ⟨(a+c,b+d+a*theta F m c),(rootElement_mul m hcard a b c d).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨a,b⟩,rfl⟩
    exact ⟨(a,b+a*theta F m a),(rootElement_inv m hcard a b).symm⟩

def rootParameters (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    (F × F) ≃ rootSubgroup m hcard :=
  Equiv.ofBijective (fun p => ⟨rootElement m p.1 p.2,⟨p,rfl⟩⟩) ⟨
    fun _ _ he => rootElement_injective m (congrArg Subtype.val he),
    by rintro ⟨g,p,hp⟩; exact ⟨p,Subtype.ext hp⟩⟩

theorem card_rootSubgroup (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (rootSubgroup m hcard) = (Nat.card F)^2 := by
  rw [← Nat.card_congr (rootParameters m hcard),Nat.card_prod,pow_two]

theorem rootSubgroup_le_generated (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    rootSubgroup m hcard ≤ generated m := by
  rintro g ⟨⟨a,b⟩,rfl⟩
  exact rootElement_mem m a b
end Atlas.SuzukiFamily
