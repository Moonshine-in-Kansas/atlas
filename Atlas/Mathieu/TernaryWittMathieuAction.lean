import Atlas.Mathieu.TernaryWittComparison
import Atlas.Mathieu.Mathieu12SharpAction

noncomputable section
namespace Atlas.Codes

/-- Transport the existing dodecad Mathieu group to the ternary Witt coordinates.
This is an action on the hexad design, not a claim of pure ternary-code preservation. -/
def ternaryWittMathieuHom : Mathieu12DodecadModel ternaryComparisonDodecad →*
    Equiv.Perm (Fin 12) :=
  ternaryWittCoordinates.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom _ (Mathieu12Points ternaryComparisonDodecad))

theorem ternaryWittMathieu_equivariant (g : Mathieu12DodecadModel ternaryComparisonDodecad)
    (i : Fin 12) :
    ternaryWittCoordinates (ternaryWittMathieuHom g i) = g • ternaryWittCoordinates i := by
  simp [ternaryWittMathieuHom, Equiv.permCongrHom]

theorem ternaryWittMathieuHom_injective : Function.Injective ternaryWittMathieuHom := by
  letI := mathieu12_faithful ternaryComparisonDodecad
  exact ternaryWittCoordinates.symm.permCongrHom.injective.comp MulAction.toPerm_injective

theorem ternaryWittMathieu_blocks (g : Mathieu12DodecadModel ternaryComparisonDodecad)
    (B : Finset (Fin 12)) :
    (B.image (ternaryWittMathieuHom g)).map ternaryWittCoordinates.toEmbedding =
      mathieu12PermuteBlock ternaryComparisonDodecad g
        (B.map ternaryWittCoordinates.toEmbedding) := by
  classical
  simp only [Finset.map_eq_image, mathieu12PermuteBlock, Finset.image_image]
  congr 1
  funext i
  exact ternaryWittMathieu_equivariant g i

theorem ternaryWittMathieu_preserves (g : Mathieu12DodecadModel ternaryComparisonDodecad)
    (B : Finset (Fin 12)) (hB : B ∈ ternaryHexads) :
    B.image (ternaryWittMathieuHom g) ∈ ternaryHexads := by
  rw [ternaryWitt_hexads_iff, ternaryWittMathieu_blocks]
  exact mathieu12Blocks_preserved _ g _ ((ternaryWitt_hexads_iff B).mp hB)

theorem ternaryWittMathieu_sharp_five (a b : Fin 5 ↪ Fin 12) :
    ∃! g : Mathieu12DodecadModel ternaryComparisonDodecad,
      ∀ k, ternaryWittMathieuHom g (a k) = b k := by
  obtain ⟨g,hg,huniq⟩ := mathieu12_sharp_five_transitive ternaryComparisonDodecad
    (a.trans ternaryWittCoordinates.toEmbedding) (b.trans ternaryWittCoordinates.toEmbedding)
  refine ⟨g, ?_, ?_⟩
  · intro k
    apply ternaryWittCoordinates.injective
    rw [ternaryWittMathieu_equivariant]
    exact congrArg (fun f : Fin 5 ↪ Mathieu12Points ternaryComparisonDodecad => f k) hg
  · intro h hh
    apply huniq h
    apply Function.Embedding.ext
    intro k
    change h • ternaryWittCoordinates (a k) = ternaryWittCoordinates (b k)
    rw [← ternaryWittMathieu_equivariant, hh k]

end Atlas.Codes
