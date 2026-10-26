import Atlas.Rudvalis.MinimumLiftFibres

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

theorem monomial_euclideanWeight (g : SignedCoordinates Coordinate) (w : QuaternaryWord) :
    euclideanWeight (monomialHom g w)=euclideanWeight w := by
  have hs : ∀ a : Quat,∀ b : Binary,euclideanSymbolWeight (signedScalar b a)=euclideanSymbolWeight a := by
    decide +kernel
  change (∑ z,euclideanSymbolWeight (signedScalar (g.left.toAdd z) (w (g.right.symm z))))=_
  simp_rw [hs]
  exact Equiv.sum_comp g.right.symm (fun z => euclideanSymbolWeight (w z))

abbrev MinimumWords := {w : quaternaryCode // euclideanWeight w.val=16}

instance : MulAction codeGroup MinimumWords where
  smul g w := ⟨⟨monomialHom g.val w.val.val,(g.prop _).mp w.val.prop⟩,
    (monomial_euclideanWeight g.val w.val.val).trans w.prop⟩
  one_smul w := by apply Subtype.ext; apply Subtype.ext; change monomialHom 1 w.val.val=w.val.val; simp
  mul_smul g h w := by
    apply Subtype.ext
    apply Subtype.ext
    change monomialHom (g.val*h.val) w.val.val=monomialHom g.val (monomialHom h.val w.val.val)
    rw [map_mul]; rfl

theorem minimumWord_action (g : codeGroup) (w : MinimumWords) :
    (g • w).val.val=monomialHom g.val w.val.val := rfl

end Atlas.Rudvalis
