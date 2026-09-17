import Atlas.Fischer.CubicPointNetworkValue
import Atlas.Fischer.QuinticPointDecomposition

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

theorem coordinateQuinticTerm_all_points (i j k a b c p q r : Omega) :
    coordinateQuinticTerm (.inl i) (.inl j) (.inl k) (.inl a) (.inl b) (.inl c)
      (.inl p) (.inl q) (.inl r)=
      (cubicPointPattern i j k*cubicPointPattern a b c*cubicPointPattern p a i*
        cubicPointPattern q b j*cubicPointPattern r c k)/4294967296 := by
  have hc (a i p : Omega) : cubicPointPattern a i p=cubicPointPattern p a i :=
    (cubicPointPattern_swap_last a i p).trans (cubicPointPattern_swap_first a p i)
  simp only [coordinateQuinticTerm,coordinateQuinticCubicProduct,coordinateCubic_points,
    star_div₀,cubicPointPattern_star,star_ofNat]
  norm_num [inverseCoordinateMetric,coordinateWeight]
  rw [hc a i p,hc b j q,hc c k r]
  ring

theorem quinticPointUUU_eq_network (p q r : Omega) :
    quinticPointUUU p q r=
      cubicPointNetwork (cubicPointPattern p) (cubicPointPattern q) (cubicPointPattern r)/4294967296 := by
  unfold quinticPointUUU cubicPointNetwork
  simp_rw [coordinateQuinticTerm_all_points,← Finset.sum_div]

/-- The pure-point partial sum of the actual weighted quintic contraction.
This is the source UUU row, in the retained unnormalized point basis. -/
theorem quinticPointUUU_value (p q r : Omega) :
    quinticPointUUU p q r=(122*cubicPointPattern p q r+1815/16)/1024 := by
  rw [quinticPointUUU_eq_network,cubicPointNetwork_value]
  ring

theorem quinticPointUUU_normalized (p q r : Omega) :
    1024*quinticPointUUU p q r=122*cubicPointPattern p q r+1815/16 := by
  rw [quinticPointUUU_value]
  ring

end Atlas.Fischer
