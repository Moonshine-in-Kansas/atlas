import Atlas.Mathieu.TetradLocalNormal

namespace Atlas.Codes

theorem tetradAffineTranslations_card (i : HexIndex) :
    Nat.card (tetradAffineTranslations i) = 16 := by
  have he := Nat.card_congr (MonoidHom.ofInjective
    (SemidirectProduct.inl_injective (φ := hexZeroAffineAction i))).toEquiv
  exact he.symm.trans (hexZeroCoordinate_card i)

theorem tetradPointTranslations_card (i : HexIndex) :
    Nat.card (tetradPointTranslations i) = 16 := by
  unfold tetradPointTranslations
  rw [← Nat.card_congr ((tetradAffineTranslations i).equivMapOfInjective
    (tetradPointStabilizerEquiv i).toMonoidHom
    (tetradPointStabilizerEquiv i).injective).toEquiv]
  exact tetradAffineTranslations_card i

end Atlas.Codes
