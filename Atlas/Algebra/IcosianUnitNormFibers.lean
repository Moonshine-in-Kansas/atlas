import Atlas.Algebra.IcosianGoldenUnits
import Atlas.Algebra.IcosianNormTwoReductionFibers

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra

/-- Transport a target matrix to determinant one by the actual integral unit. -/
def icosianUnitNormReductionTarget (a : icosianOrderˣ) (m : IcosianMatrix)
    (hm : Matrix.det m=goldenModuloTwo (icosianIntegralNorm (a : icosianOrder))) :
    IcosianSpecialLinear :=
  ⟨icosianModuloTwo ((a⁻¹ : icosianOrderˣ) : icosianOrder)*m,by
    rw [Matrix.det_mul,hm,← icosianModuloTwo_det,← Matrix.det_mul,← map_mul,
      Units.inv_mul,map_one,Matrix.det_one]⟩

theorem icosianUnitNorm_reduction_iff (a : icosianOrderˣ) (m : IcosianMatrix)
    (hm : Matrix.det m=goldenModuloTwo (icosianIntegralNorm (a : icosianOrder)))
    (u : icosianNormOneGroup) :
    icosianNormOneReduction u=icosianUnitNormReductionTarget a m hm ↔
      icosianModuloTwo (icosianUnitNormParameter a u).val=m := by
  change icosianNormOneReduction u=icosianUnitNormReductionTarget a m hm ↔
    icosianModuloTwo ((a : icosianOrder)*icosianNormOneToOrder u)=m
  rw [map_mul]
  constructor
  · intro h
    have he := congrArg Subtype.val h
    change icosianModuloTwo (icosianNormOneToOrder u)=
      icosianModuloTwo ((a⁻¹ : icosianOrderˣ) : icosianOrder)*m at he
    rw [he,← mul_assoc,← map_mul,Units.mul_inv,map_one,one_mul]
  · intro h
    apply Subtype.ext
    change icosianModuloTwo (icosianNormOneToOrder u)=
      icosianModuloTwo ((a⁻¹ : icosianOrderˣ) : icosianOrder)*m
    rw [← h,← mul_assoc,← map_mul,Units.inv_mul,map_one,one_mul]

def icosianUnitNormFiberEquiv (a : icosianOrderˣ) (m : IcosianMatrix)
    (hm : Matrix.det m=goldenModuloTwo (icosianIntegralNorm (a : icosianOrder))) :
    {u : icosianNormOneGroup // icosianNormOneReduction u=icosianUnitNormReductionTarget a m hm} ≃
      {x : IcosianNormShell (icosianNorm (a : icosianOrder).val) // icosianModuloTwo x.val=m} :=
  (icosianUnitNormEquiv a).subtypeEquiv (icosianUnitNorm_reduction_iff a m hm)

theorem icosianUnitNormFiber_card (a : icosianOrderˣ) (m : IcosianMatrix)
    (hm : Matrix.det m=goldenModuloTwo (icosianIntegralNorm (a : icosianOrder))) :
    Nat.card {x : IcosianNormShell (icosianNorm (a : icosianOrder).val) //
      icosianModuloTwo x.val=m}=2 := by
  rw [← Nat.card_congr (icosianUnitNormFiberEquiv a m hm)]
  exact icosianNormOneReduction_fiber_card _

theorem icosianGoldenUnitNormFiber_card (a : GoldenIntegerˣ) (m : IcosianMatrix)
    (hm : Matrix.det m=(goldenModuloTwo (a : GoldenInteger))^2) :
    Nat.card {x : IcosianNormShell ((goldenIntegerToRational (a : GoldenInteger))^2) //
      icosianModuloTwo x.val=m}=2 := by
  let u := Units.map icosianGoldenToOrder.toMonoidHom a
  have hu : Matrix.det m=goldenModuloTwo (icosianIntegralNorm (u : icosianOrder)) := by
    change Matrix.det m=goldenModuloTwo (icosianIntegralNorm (icosianGoldenToOrder (a : GoldenInteger)))
    rw [icosianGoldenToOrder_integralNorm,map_pow,hm]
  have h := icosianUnitNormFiber_card u m hu
  change Nat.card {x : IcosianNormShell (icosianNorm (icosianGoldenToOrder (a : GoldenInteger)).val) //
    icosianModuloTwo x.val=m}=2 at h
  rwa [icosianGoldenToOrder_norm] at h

end Atlas.Algebra

