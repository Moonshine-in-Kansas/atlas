import Atlas.LinearGroups.SuzukiFamily.BorelSolvable

/-! The split root-by-torus exact sequence for the full ovoid point stabilizer. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def torusSubgroup (m : ℕ) : Subgroup (Atlas.Symplectic.Sp 2 F) := (torusHom m).range

def torusParameters (m : ℕ) : Fˣ ≃* torusSubgroup (F := F) m :=
  MulEquiv.ofBijective (torusHom m).rangeRestrict
    ⟨fun _ _ he => torusElement_injective m (congrArg Subtype.val he),
      (torusHom m).rangeRestrict_surjective⟩

theorem card_torusSubgroup (m : ℕ) : Nat.card (torusSubgroup (F := F) m)=Nat.card F-1 := by
  rw [← Nat.card_congr (torusParameters (F := F) m).toEquiv,Nat.card_units]

def borelTorusHom (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) : Fˣ →* borel m hcard where
  toFun t := shortInBorel m hcard 0 0 t
  map_one' := shortInBorel_zero_one m hcard
  map_mul' s t := by simp [shortInBorel_mul m hcard]

theorem borelProjection_section (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.RightInverse (borelTorusHom m hcard) (borelProjection m hcard) :=
  fun t => borelProjection_short m hcard 0 0 t

theorem rootIntoBorel_injective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (rootIntoBorel m hcard) := by
  intro g h he
  exact Subtype.ext (congrArg (fun x : borel m hcard => x.val.val) he)

theorem borelTorusHom_injective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (borelTorusHom m hcard) := (borelProjection_section m hcard).injective
end Atlas.SuzukiFamily
