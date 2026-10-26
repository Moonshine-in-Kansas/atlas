import Atlas.LinearGroups.ReeF4.RootGroupParameters

/-! The actual q² subgroup of linear automorphisms, with its unique two-field
parameter normal form. Membership in the full Ree candidate is proved separately. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def shortRootSubgroup (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Subgroup (TraceZero F ≃ₗ[F] TraceZero F) where
  carrier := Set.range (fun p : F × F => shortRootPairEquiv m hcard p.1 p.2)
  one_mem' := ⟨(0,0),shortRootPairEquiv_zero m hcard⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a,b⟩,rfl⟩ ⟨⟨c,d⟩,rfl⟩
    exact ⟨(a+c,b+d+theta F m a*c),(shortRootPairEquiv_mul m hcard a b c d).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨a,b⟩,rfl⟩
    exact ⟨(a,b+a*theta F m a),(shortRootPairEquiv_inv m hcard a b).symm⟩

def shortRootParameters (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    (F × F) ≃ shortRootSubgroup m hcard :=
  Equiv.ofBijective (fun p => ⟨shortRootPairEquiv m hcard p.1 p.2,⟨p,rfl⟩⟩) ⟨
    fun _ _ h => shortRootPairEquiv_injective m hcard (congrArg Subtype.val h),
    by rintro ⟨g,p,hp⟩; exact ⟨p,Subtype.ext hp⟩⟩

theorem card_shortRootSubgroup (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (shortRootSubgroup m hcard) = (Nat.card F)^2 := by
  rw [← Nat.card_congr (shortRootParameters m hcard), Nat.card_prod, pow_two]

end Atlas.ReeF4
