import Atlas.Algebra.IcosianNormTwoRepresentatives
import Atlas.Algebra.IcosianNormOneCard
import Atlas.Algebra.IcosianNormOneKernelCard

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix Quaternion QuadraticAlgebra

abbrev IcosianNormTwo := {x : icosianOrder // icosianNorm x.val=2}

def icosianNormTwoParameter (p : Fin 5 × icosianNormOneGroup) : IcosianNormTwo :=
  ⟨icosianNormTwoRepresentative p.1*icosianNormOneToOrder p.2,by
    change icosianNorm ((icosianNormTwoRepresentative p.1).val*p.2.val.val)=2
    rw [icosianNorm_mul,icosianNormTwoRepresentative_norm,icosianNormOneGroup_norm,mul_one]⟩

theorem icosianNormTwoParameter_surjective : Function.Surjective icosianNormTwoParameter := by
  intro x
  obtain ⟨i,hi⟩ := icosianNormTwoRepresentative_cover (icosianModuloTwo x.val)
    (icosianReduction_norm_two_det x.property)
  rw [← icosianNormTwoRepresentative_reduction] at hi
  obtain ⟨u,hu⟩ := icosianNormTwo_associate_of_adjugate
    (icosianNormTwoRepresentative_norm i) x.property hi
  refine ⟨(i,u),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hu.symm

theorem icosianNormTwoParameter_injective : Function.Injective icosianNormTwoParameter := by
  rintro ⟨i,u⟩ ⟨j,v⟩ h
  have he : icosianNormTwoRepresentative i*icosianNormOneToOrder u=
      icosianNormTwoRepresentative j*icosianNormOneToOrder v := congrArg Subtype.val h
  have hm := congrArg icosianModuloTwo he
  rw [map_mul,map_mul,icosianNormTwoRepresentative_reduction,
    icosianNormTwoRepresentative_reduction] at hm
  have hij : i=j := by
    by_contra hij
    apply icosianNormTwoRepresentative_separate i j hij
    have hh := congrArg (fun m => Matrix.adjugate (icosianNormTwoRepresentativeMatrix i)*m) hm
    rw [← mul_assoc,Matrix.adjugate_mul] at hh
    have hd : Matrix.det (icosianNormTwoRepresentativeMatrix i)=0 := by
      rw [← icosianNormTwoRepresentative_reduction]
      exact icosianReduction_norm_two_det (icosianNormTwoRepresentative_norm i)
    rw [hd] at hh
    simp only [zero_smul,zero_mul] at hh
    have hc := congrArg (fun m => m*icosianModuloTwo (icosianNormOneToOrder v⁻¹)) hh
    have hinv : icosianModuloTwo (icosianNormOneToOrder v)*
        icosianModuloTwo (icosianNormOneToOrder v⁻¹)=1 := by
      rw [← map_mul,← map_mul,mul_inv_cancel,map_one,map_one]
    simpa only [zero_mul,mul_assoc,hinv,mul_one] using hc.symm
  subst j
  have hr : (icosianNormTwoRepresentative i).val≠0 := by
    intro hz
    have hn := icosianNormTwoRepresentative_norm i
    rw [hz] at hn
    norm_num [icosianNorm] at hn
  have huv : u=v := by
    apply icosianNormOne_value_injective
    apply mul_left_cancel₀ hr
    exact congrArg Subtype.val he
  exact Prod.ext rfl huv

def icosianNormTwoEquiv : IcosianNormTwo ≃ (Fin 5 × icosianNormOneGroup) :=
  (Equiv.ofBijective icosianNormTwoParameter
    ⟨icosianNormTwoParameter_injective,icosianNormTwoParameter_surjective⟩).symm

instance icosianNormTwo_finite : Finite IcosianNormTwo :=
  Finite.of_equiv _ icosianNormTwoEquiv.symm

theorem icosianNormTwo_card : Nat.card IcosianNormTwo=600 := by
  rw [Nat.card_congr icosianNormTwoEquiv,Nat.card_prod,icosianNormOneGroup_card]
  simp

end Atlas.Algebra
