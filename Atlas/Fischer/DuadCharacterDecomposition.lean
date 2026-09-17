import Atlas.Fischer.DuadOctadDecomposition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual sum map from the two retained shortened octad codes. -/
def duadOctadSum (p : Finset Omega) (F G : Octad) (hFG : F.val ∩ G.val=p) :
    (octadShortenedCode F × octadShortenedCode G) →ₗ[Bit] duadShortenedCode p :=
  ((octadShortenedCode F).subtype.coprod (octadShortenedCode G).subtype).codRestrict
    (duadShortenedCode p) (fun x => (duadShortenedCode p).add_mem
      (octadShortenedCode_le_duad p F (hFG ▸ Finset.inter_subset_left) x.1.property)
      (octadShortenedCode_le_duad p G (hFG ▸ Finset.inter_subset_right) x.2.property))

/-- A chosen intersecting pair gives the actual direct-sum equivalence. -/
def duadOctadSumEquiv (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p) :
    (octadShortenedCode F × octadShortenedCode G) ≃ₗ[Bit] duadShortenedCode p := by
  apply LinearEquiv.ofBijective (duadOctadSum p F G hFG)
  constructor
  · have hi : Function.Injective
        ((octadShortenedCode F).subtype.coprod (octadShortenedCode G).subtype) := by
      rw [← LinearMap.ker_eq_bot,LinearMap.ker_coprod_of_disjoint_range,
        Submodule.ker_subtype,Submodule.ker_subtype,Submodule.prod_bot]
      rw [Submodule.range_subtype,Submodule.range_subtype]
      exact duadOctadSubcodes_disjoint F G (hFG ▸ hp)
    intro x y h
    apply hi
    exact congrArg Subtype.val h
  · intro c
    have hc := c.property
    simp only [duadShortenedCode_eq_sup p hp F G hFG,Submodule.mem_sup] at hc
    obtain ⟨x,hx,y,hy,hxy⟩ := hc
    exact ⟨(⟨x,hx⟩,⟨y,hy⟩),Subtype.ext hxy⟩

@[simp] theorem duadOctadSumEquiv_apply (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (x : octadShortenedCode F × octadShortenedCode G) :
    (duadOctadSumEquiv p hp F G hFG x).val=x.1.val+x.2.val := rfl

/-- Characters of the direct sum are exactly pairs of actual octadic characters. -/
def duadCharacterEquiv (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p) :
    (Module.Dual Bit (octadShortenedCode F) × Module.Dual Bit (octadShortenedCode G)) ≃ₗ[Bit]
      Module.Dual Bit (duadShortenedCode p) :=
  (Module.dualProdDualEquivDual Bit _ _).trans
    (duadOctadSumEquiv p hp F G hFG).symm.dualMap

@[simp] theorem duadCharacterEquiv_on_sum (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (χ : Module.Dual Bit (octadShortenedCode F)) (ψ : Module.Dual Bit (octadShortenedCode G))
    (x : octadShortenedCode F) (y : octadShortenedCode G) :
    duadCharacterEquiv p hp F G hFG (χ,ψ) (duadOctadSumEquiv p hp F G hFG (x,y))=
      χ x+ψ y := by
  simp [duadCharacterEquiv]

end Atlas.Fischer
