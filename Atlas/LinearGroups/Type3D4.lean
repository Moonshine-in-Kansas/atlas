import Atlas.LinearGroups.Triality.Simplicity
import Atlas.LinearGroups.Triality.ProjectiveEmbedding
import Atlas.LinearGroups.Triality.BruhatNormalForm
import Atlas.LinearGroups.Triality.WeylDihedral
import Atlas.LinearGroups.Triality.SplitBorel
import Atlas.LinearGroups.Triality.ParabolicIndices
import Atlas.LinearGroups.Triality.ActionTransport

/-! Public construction package for the actual cubic-folded triality matrix group.
This does not assert a full graph–field fixed-point comparison. -/
noncomputable section
namespace Atlas

structure Type3D4Construction (F K : Type*) [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K=3) : Prop where
  finite : Finite (Triality.Group F K)
  order : Nat.card (Triality.Group F K)=
    Nat.card F^12*(Nat.card F^8+Nat.card F^4+1)*(Nat.card F^6-1)*(Nat.card F^2-1)
  simple : IsSimpleGroup (Triality.Group F K)
  nonabelian : ¬ IsMulCommutative (Triality.Group F K)
  perfect : Group.IsPerfect (Triality.Group F K)
  elementary_embedding : Function.Injective (Triality.intoElementary F K)
  projective_embedding : Function.Injective (Triality.intoProjective F K)
  unipotent_order : Nat.card (Triality.unipotent F K hdeg)=Nat.card F^12
  torus_order : Nat.card (Triality.torus F K)=(Nat.card F^3-1)*(Nat.card F-1)
  borel_order : Nat.card (Triality.borel F K hdeg)=Nat.card F^12*(Nat.card F^3-1)*(Nat.card F-1)
  borel_kernel : (Triality.borelProjection F K hdeg).ker=
    (Triality.unipotent F K hdeg).subgroupOf (Triality.borel F K hdeg)
  borel_split : Function.LeftInverse (Triality.borelProjection F K hdeg) (Triality.borelSection F K hdeg)
  normal_forms : Nonempty (Triality.CellParameters F K hdeg ≃ Triality.Group F K)
  weyl_dihedral : Nonempty (DihedralGroup 6 ≃* Triality.WeylQuotient F K hdeg)
  parabolic_maximal : IsCoatom (Triality.parabolic F K hdeg)
  faithful : FaithfulSMul (Triality.Group F K) (Triality.ParabolicPoints F K hdeg)
  primitive : MulAction.IsPreprimitive (Triality.Group F K) (Triality.ParabolicPoints F K hdeg)
  points : Nat.card (Triality.ParabolicPoints F K hdeg)=
    (Nat.card F^3+1)*(Nat.card F^8+Nat.card F^4+1)
  short_parabolic_order : Nat.card (Triality.shortParabolic F K hdeg)=
    Nat.card F^12*(Nat.card F^6-1)*(Nat.card F-1)
  long_parabolic_order : Nat.card (Triality.longParabolic F K hdeg)=
    Nat.card F^12*(Nat.card F^3-1)*(Nat.card F^2-1)

theorem type3D4_construction {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K=3) : Type3D4Construction F K hdeg where
  finite := inferInstance
  order := Triality.card_group F K hdeg
  simple := Triality.simple F K hdeg
  nonabelian := Triality.noncommutative F K hdeg
  perfect := Triality.perfect F K hdeg
  elementary_embedding := Triality.intoElementary_injective F K
  projective_embedding := Triality.intoProjective_injective F K hdeg
  unipotent_order := Triality.card_unipotent F K hdeg
  torus_order := Triality.card_torus F K hdeg
  borel_order := Triality.card_borel F K hdeg
  borel_kernel := Triality.borelProjection_kernel F K hdeg
  borel_split := Triality.borelProjection_section F K hdeg
  normal_forms := ⟨Triality.cellEquiv F K hdeg⟩
  weyl_dihedral := ⟨Triality.dihedralWeylEquiv F K hdeg⟩
  parabolic_maximal := Triality.parabolic_isCoatom F K hdeg
  faithful := inferInstance
  primitive := inferInstance
  points := Triality.card_parabolicPoints F K hdeg
  short_parabolic_order := Triality.card_shortParabolic F K hdeg
  long_parabolic_order := Triality.card_longParabolic F K hdeg

theorem exists_type3D4 {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K=3) :
    ∃ (G : Type v) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G=Nat.card F^12*(Nat.card F^8+Nat.card F^4+1)*(Nat.card F^6-1)*(Nat.card F^2-1) ∧
      Nonempty (G ≃* Triality.Group F K) ∧ Type3D4Construction F K hdeg :=
  ⟨Triality.Group F K,inferInstance,inferInstance,Triality.simple F K hdeg,
    Triality.noncommutative F K hdeg,Triality.card_group F K hdeg,
    ⟨MulEquiv.refl _⟩,type3D4_construction hdeg⟩

namespace Triality
abbrev PrimePowerModel (p f : ℕ) [Fact p.Prime] :=
  Group (GaloisField p f) (FiniteField.Extension (GaloisField p f) p 3)

theorem primePower_order (p f : ℕ) [Fact p.Prime] (hf : 1≤f) :
    Nat.card (PrimePowerModel p f)=(p^f)^12*((p^f)^8+(p^f)^4+1)*((p^f)^6-1)*((p^f)^2-1) := by
  rw [card_group _ _ (FiniteField.finrank_extension (GaloisField p f) p 3),
    GaloisField.card p f (by omega)]

theorem primePower_simple (p f : ℕ) [Fact p.Prime] : IsSimpleGroup (PrimePowerModel p f) :=
  simple _ _ (FiniteField.finrank_extension (GaloisField p f) p 3)

theorem primePower_noncommutative (p f : ℕ) [Fact p.Prime] : ¬ IsMulCommutative (PrimePowerModel p f) :=
  noncommutative _ _ (FiniteField.finrank_extension (GaloisField p f) p 3)
end Triality

theorem type3D4_prime_power (p f : ℕ) (hp : p.Prime) (hf : 1≤f) :
    ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K)
      (_ : Algebra F K) (hdeg : Module.finrank F K=3),
      Nat.card F=p^f ∧ Type3D4Construction F K hdeg := by
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p f
  let K := FiniteField.Extension F p 3
  have hd : Module.finrank F K=3 := FiniteField.finrank_extension F p 3
  exact ⟨F,K,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,hd,
    GaloisField.card p f (by omega),type3D4_construction hd⟩

theorem exists_type3D4_parameter (p f : ℕ) (hp : p.Prime) (hf : 1≤f) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G=(p^f)^12*((p^f)^8+(p^f)^4+1)*((p^f)^6-1)*((p^f)^2-1) ∧
      Nonempty (G ≃* Triality.PrimePowerModel p f) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨Triality.PrimePowerModel p f,inferInstance,inferInstance,
    Triality.primePower_simple p f,Triality.primePower_noncommutative p f,
    Triality.primePower_order p f hf,⟨MulEquiv.refl _⟩⟩

theorem type3D4_field_transport {F E K L : Type*} [Field F] [Field E] [Field K] [Field L]
    [Finite F] [Finite E] [Finite K] [Finite L] [Algebra F K] [Algebra E L]
    (e : F ≃+* E) (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) :
    Nonempty (Triality.Group F K ≃* Triality.Group E L) := ⟨Triality.baseFieldEquiv e hK hL⟩

end Atlas
