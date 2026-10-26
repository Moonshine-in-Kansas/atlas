import Atlas.LinearGroups.ReeF4.RootGroupMembership
import Atlas.LinearGroups.ReeF4.RootSuzukiStructure

/-! The concrete local subgroup inside the intrinsic full stabilizer. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def shortRootModelEmbedding {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    shortRootSubgroup m hcard →* Model F m :=
  Subgroup.inclusion (shortRootSubgroup_le_modelSubgroup hcard)

theorem shortRootModelEmbedding_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (shortRootModelEmbedding hcard) := by
  intro g h he
  apply Subtype.ext
  exact congrArg (fun z : Model F m => z.val) he

/-- Noncommuting local root elements remain noncommuting in the actual model. -/
theorem model_noncommutative_of_large {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) :
    ∃ g h : Model F m, g*h ≠ h*g := by
  obtain ⟨g,h,hne⟩ := shortRootSubgroup_noncommutative m hcard hm
  refine ⟨shortRootModelEmbedding hcard g, shortRootModelEmbedding hcard h, ?_⟩
  intro he
  apply hne
  apply shortRootModelEmbedding_injective hcard
  simpa only [map_mul] using he

end Atlas.ReeF4
