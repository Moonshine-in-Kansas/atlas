import Atlas.LinearGroups.Chevalley.RootData.ParabolicLengthSplit
import Atlas.LinearGroups.Chevalley.RootData.ParabolicLengthAdditivity

/-! Unique length-additive right-parabolic coordinates in the actual Weyl
permutation image. The equivalence is a set equivalence, not a group product. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem rootWeyl_parabolic_minimal_unique
    (J : Finset b.support) (x y : P.weylGroupToPerm.range)
    (hx : ∀ i ∈ J, b.IsPos (x.val i.val))
    (hy : ∀ i ∈ J, b.IsPos (y.val i.val))
    (hxy : x⁻¹ * y ∈ rootParabolicSubgroup P b J) : x = y := by
  let v := x⁻¹ * y
  have hv : v ∈ rootParabolicSubgroup P b J := hxy
  have h1 : rootWeylLength P b y = rootWeylLength P b x + rootWeylLength P b v := by
    simpa only [v, mul_inv_cancel_left] using
      rootWeylLength_mul_parabolic_of_simple_positive P b J x hx v hv
  have h2 : rootWeylLength P b x = rootWeylLength P b y + rootWeylLength P b v := by
    have h := rootWeylLength_mul_parabolic_of_simple_positive P b J y hy v⁻¹
      ((rootParabolicSubgroup P b J).inv_mem hv)
    have he : y * v⁻¹ = x := by dsimp only [v]; group
    simpa only [he, rootWeylLength_inv] using h
  have hv0 : rootWeylLength P b v = 0 := by omega
  have hv1 : v = 1 := (rootWeylLength_eq_zero_iff P b v).mp hv0
  calc
    x = x * v := by rw [hv1, mul_one]
    _ = y := by dsimp only [v]; group

/-- Actual minimal representatives for right cosets, identified by simple-root signs. -/
def rootParabolicRepresentatives (J : Finset b.support) :=
  {x : P.weylGroupToPerm.range // ∀ i ∈ J, b.IsPos (x.val i.val)}

def rootParabolicProductMap (J : Finset b.support) :
    rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J →
      P.weylGroupToPerm.range := fun p => p.1.val * p.2.val

theorem rootParabolicProductMap_bijective (J : Finset b.support) :
    Function.Bijective (rootParabolicProductMap P b J) := by
  constructor
  · intro p q hpq
    change p.1.val * p.2.val = q.1.val * q.2.val at hpq
    have hcos : p.1.val⁻¹ * q.1.val ∈ rootParabolicSubgroup P b J := by
      have he : p.1.val⁻¹ * q.1.val = p.2.val * q.2.val⁻¹ := by
        calc
          p.1.val⁻¹ * q.1.val = p.1.val⁻¹ * (q.1.val * q.2.val) * q.2.val⁻¹ := by group
          _ = p.1.val⁻¹ * (p.1.val * p.2.val) * q.2.val⁻¹ := by rw [← hpq]
          _ = p.2.val * q.2.val⁻¹ := by group
      rw [he]
      exact (rootParabolicSubgroup P b J).mul_mem p.2.property
        ((rootParabolicSubgroup P b J).inv_mem q.2.property)
    have hfirst := rootWeyl_parabolic_minimal_unique P b J _ _
      p.1.property q.1.property hcos
    have hsecond : p.2.val = q.2.val := by
      apply mul_left_cancel (a := q.1.val)
      simpa only [hfirst] using hpq
    exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)
  · intro w
    obtain ⟨x, l, hl, hx, hfactor, _hlen, _hred⟩ :=
      exists_rootWeyl_parabolic_length_split P b (J : Set b.support) w
    exact ⟨(⟨x, hx⟩, ⟨rootWeylWord P b l, rootWeylWord_mem_parabolic P b J l hl⟩),
      hfactor.symm⟩

/-- Actual right-coset coordinates with the original Weyl image as the codomain. -/
def rootParabolicProductEquiv (J : Finset b.support) :
    rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J ≃
      P.weylGroupToPerm.range :=
  Equiv.ofBijective (rootParabolicProductMap P b J) (rootParabolicProductMap_bijective P b J)

theorem rootParabolicProductEquiv_length (J : Finset b.support)
    (p : rootParabolicRepresentatives P b J × rootParabolicSubgroup P b J) :
    rootWeylLength P b (rootParabolicProductEquiv P b J p) =
      rootWeylLength P b p.1.val + rootWeylLength P b p.2.val :=
  rootWeylLength_mul_parabolic_of_simple_positive P b J p.1.val p.1.property
    p.2.val p.2.property

end Atlas.Chevalley.RootData
