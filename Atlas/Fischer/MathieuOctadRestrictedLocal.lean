import Atlas.Fischer.MathieuOctadInsideFull
import Atlas.Families.Alternating.Stabilizers

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The full local subgroup fixing a specified subset of the eight actual points. -/
def mathieuOctadRestrictedLocal (O : Octad) (A : Finset (OctadInterior O)) :
    Subgroup (MathieuOctadStabilizer O) :=
  (fixingSubgroup (alternatingGroup (OctadInterior O)) (A : Set (OctadInterior O))).comap
    (mathieuOctadAlternatingHom O)

def mathieuOctadRestrictedHom (O : Octad) (A : Finset (OctadInterior O)) :
    mathieuOctadRestrictedLocal O A →*
      fixingSubgroup (alternatingGroup (OctadInterior O)) (A : Set (OctadInterior O)) where
  toFun g := ⟨mathieuOctadAlternatingHom O g.val,g.prop⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

theorem mathieuOctadRestrictedHom_surjective (O : Octad) (A : Finset (OctadInterior O)) :
    Function.Surjective (mathieuOctadRestrictedHom O A) := by
  intro a
  obtain ⟨g,hg⟩ := mathieuOctadAlternating_surjective O a.val
  exact ⟨⟨g,by change mathieuOctadAlternatingHom O g ∈ fixingSubgroup (alternatingGroup (OctadInterior O)) (A : Set (OctadInterior O)); rw [hg]; exact a.prop⟩,
    Subtype.ext hg⟩

/-- The full induced group on the unmarked octad points, with the actual
pointwise octad kernel retained. -/
def mathieuOctadComplementHom (O : Octad) (A : Finset (OctadInterior O)) :
    mathieuOctadRestrictedLocal O A →* alternatingGroup (Aᶜ : Finset (OctadInterior O)) :=
  (Atlas.Families.Alternating.stabilizerComplementEquiv A).toMonoidHom.comp
    (mathieuOctadRestrictedHom O A)

theorem mathieuOctadComplementHom_surjective (O : Octad) (A : Finset (OctadInterior O)) :
    Function.Surjective (mathieuOctadComplementHom O A) :=
  (Atlas.Families.Alternating.stabilizerComplementEquiv A).surjective.comp
    (mathieuOctadRestrictedHom_surjective O A)

theorem mathieuOctadComplementHom_ker (O : Octad) (A : Finset (OctadInterior O)) :
    (mathieuOctadComplementHom O A).ker =
      (mathieuOctadPointwise O).comap (mathieuOctadRestrictedLocal O A).subtype := by
  ext g
  change (Atlas.Families.Alternating.stabilizerComplementEquiv A)
    (mathieuOctadRestrictedHom O A g)=1 ↔ mathieuOctadAlternatingHom O g.val=1
  rw [map_eq_one_iff _ (Atlas.Families.Alternating.stabilizerComplementEquiv A).injective]
  exact Subtype.ext_iff

end Atlas.Fischer
