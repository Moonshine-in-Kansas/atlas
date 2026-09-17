import Atlas.Algebra.GoldenModuloTwo

namespace Atlas.Algebra

instance goldenFour_fintype : Fintype GoldenFour :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm

theorem goldenFour_card : Fintype.card GoldenFour=4 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd 1 1),Fintype.card_prod]
  norm_num

end Atlas.Algebra
