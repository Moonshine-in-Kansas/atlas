import Atlas.LinearGroups.ReeF4.RootSuzukiScalarProduct
import Atlas.LinearGroups.ReeF4.ElementaryDerived

/-! The actual local Suzuki × scalar product lies in the displayed elementary
subgroup. No equality of that subgroup with the full model is assumed. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem modelSuzukiEmbedding_mem_elementary {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (g : Atlas.SuzukiFamily.Group F m) :
    modelSuzukiEmbedding m hcard g ∈ elementarySubgroup hcard := by
  let H := (elementarySubgroup hcard).map (modelSubgroup F m).subtype
  have hle : suzukiLeviSubgroup m hcard ≤ H := by
    apply (Subgroup.closure_le H).mpr
    intro x hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨⟨a,b⟩,rfl⟩ := hx
      exact ⟨shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b)),
        shortRoot_mem_elementary hcard a b,rfl⟩
    · obtain ⟨b,rfl⟩ := hx
      exact ⟨torusModelHom hcard (1,b),torus_mem_elementary hcard 1 b,rfl⟩
    · rcases hx with rfl
      exact ⟨weylRhoModel m,weylRho_mem_elementary hcard,rfl⟩
  obtain ⟨x,hx,he⟩ := hle (suzukiLeviEmbedding m hcard g).property
  have hxe : x=modelSuzukiEmbedding m hcard g := Subtype.ext he
  change x ∈ elementarySubgroup hcard at hx
  rw [← hxe]
  exact hx

theorem modelSuzukiScalarHom_mem_elementary {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) (s : Fˣ) :
    modelSuzukiScalarHom hcard s ∈ elementarySubgroup hcard :=
  torus_mem_elementary hcard (thetaUnits m s) s

theorem modelSuzukiProductSubgroup_le_elementary {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    modelSuzukiProductSubgroup hcard ≤ elementarySubgroup hcard := by
  rintro x ⟨⟨g,s⟩,rfl⟩
  exact (elementarySubgroup hcard).mul_mem
    (modelSuzukiEmbedding_mem_elementary hcard g)
    (modelSuzukiScalarHom_mem_elementary hcard s)

end Atlas.ReeF4
