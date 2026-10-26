import Atlas.LinearGroups.ReeF4.ExteriorSpanning
import Mathlib.Algebra.Module.Submodule.EqLocus

/-! Structural span of decomposable vectors in the actual polar/cross kernel.
The span below uses precisely the assigned domain, without quadratic-isotropy
hypotheses on either factor. No group or partial-product values enter it. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def admissibleWedgeSpan : Submodule F (⋀[F]^2 (TraceZero F)) :=
  Submodule.span F {w | ∃ u v : TraceZero F, StarDomain u v ∧ wedge u v = w}

theorem admissibleWedgeSpan_le : admissibleWedgeSpan (F := F) ≤ StarCarrier := by
  apply Submodule.span_le.mpr
  rintro w ⟨u, v, huv, rfl⟩
  exact (wedge_mem_starCarrier_iff u v).mpr huv

theorem wedge_mem_admissibleWedgeSpan {u v : TraceZero F} (h : StarDomain u v) :
    wedge u v ∈ admissibleWedgeSpan (F := F) :=
  Submodule.subset_span ⟨u, v, h, rfl⟩

private theorem wedge_add_left' (u v w : TraceZero F) :
    wedge (u + v) w = wedge u w + wedge v w :=
  (exteriorPower.ιMulti F 2).map_vecCons_add ![w] u v

private theorem wedge_add_right' (u v w : TraceZero F) :
    wedge u (v + w) = wedge u v + wedge u w := by
  have h := (exteriorPower.ιMulti F 2).map_update_add ![u,v] 1 v w
  have hu (z : TraceZero F) : Function.update ![u,v] 1 z = ![u,z] := by
    funext i
    fin_cases i <;> simp
  simpa only [hu, wedge] using h

/-- A rectangle of decomposable vectors replaces a sum of two nonadmissible
wedges by three admissible wedges. This is the basic root-table relation. -/
theorem rectangle_wedges_mem_admissibleWedgeSpan
    (u x v y : TraceZero F)
    (h : StarDomain (u + x) (v + y))
    (huy : StarDomain u y) (hxv : StarDomain x v) :
    wedge u v + wedge x y ∈ admissibleWedgeSpan (F := F) := by
  have h0 := wedge_mem_admissibleWedgeSpan h
  have h1 := wedge_mem_admissibleWedgeSpan huy
  have h2 := wedge_mem_admissibleWedgeSpan hxv
  have he : wedge u v + wedge x y =
      wedge (u + x) (v + y) - wedge u y - wedge x v := by
    rw [wedge_add_left', wedge_add_right', wedge_add_right']
    abel
  rw [he]
  exact (admissibleWedgeSpan (F := F)).sub_mem
    ((admissibleWedgeSpan (F := F)).sub_mem h0 h1) h2

private theorem polar_add_right' (u v w : TraceZero F) :
    traceZeroPolar u (v + w) = traceZeroPolar u v + traceZeroPolar u w := by
  simpa only [traceZeroPolar_comm] using traceZeroPolar_add_left v w u

private theorem cross_add_right' (u v w : TraceZero F) :
    traceZeroCross u (v + w) = traceZeroCross u v + traceZeroCross u w := by
  simpa only [traceZeroCross_comm] using traceZeroCross_add_left v w u

/-- Two polar/cross collisions and two admissible mixed entries give an
admissible rectangle, uniformly over every characteristic-two ring. -/
theorem starDomain_rectangle (u x v y : TraceZero F)
    (hp : traceZeroPolar u v = traceZeroPolar x y)
    (hc : traceZeroCross u v = traceZeroCross x y)
    (huy : StarDomain u y) (hxv : StarDomain x v) :
    StarDomain (u + x) (v + y) := by
  constructor
  · simp only [traceZeroPolar_add_left, polar_add_right', huy.1, hxv.1,
      add_zero, zero_add, hp]
    exact CharTwo.add_self_eq_zero _
  · simp only [traceZeroCross_add_left, cross_add_right', huy.2, hxv.2,
      add_zero, zero_add, hc]
    rw [← two_smul F, (CharTwo.two_eq_zero (R := F)), zero_smul]

theorem collision_wedges_mem_admissibleWedgeSpan (u x v y : TraceZero F)
    (hp : traceZeroPolar u v = traceZeroPolar x y)
    (hc : traceZeroCross u v = traceZeroCross x y)
    (huy : StarDomain u y) (hxv : StarDomain x v) :
    wedge u v + wedge x y ∈ admissibleWedgeSpan (F := F) :=
  rectangle_wedges_mem_admissibleWedgeSpan u x v y
    (starDomain_rectangle u x v y hp hc huy hxv) huy hxv

/-- Once decomposable admissible wedges span the kernel, agreement of linear
maps on the assigned partial domain is agreement on the complete kernel. -/
theorem domainWedge_linear_ext_of_span
    (hspan : admissibleWedgeSpan (F := F) = StarCarrier)
    {M : Type*} [AddCommMonoid M] [Module F M]
    (f g : (⋀[F]^2 (TraceZero F)) →ₗ[F] M)
    (hfg : ∀ u v, StarDomain u v → f (wedge u v) = g (wedge u v))
    (x : StarCarrier (F := F)) : f x.val = g x.val := by
  have hx : x.val ∈ admissibleWedgeSpan (F := F) := by rw [hspan]; exact x.property
  change x.val ∈ LinearMap.eqLocus f g
  apply (Submodule.span_le.mpr ?_) hx
  rintro w ⟨u, v, huv, rfl⟩
  exact hfg u v huv

set_option maxHeartbeats 800000 in
/-- Reduce containment of the whole kernel to the 26-by-26 marked pair
calculation. This uses the existing exterior basis and projection, not a
matrix-rank computation. -/
theorem starCarrier_le_of_marked_projection (N : Submodule F (⋀[F]^2 (TraceZero F)))
    (h : ∀ i j : TraceZeroCoordinate,
      starProjectionLinear (wedge (markedBasis (F := F) i) (markedBasis j)) ∈ N) :
    StarCarrier (F := F) ≤ N := by
  intro w hw
  have hw' : starProjectionLinear (F := F) w = w :=
    congrArg Subtype.val (starProjection_of_mem (⟨w, hw⟩ : StarCarrier (F := F)))
  rw [← hw', ← (markedExteriorBasis (F := F)).sum_repr w]
  simp only [_root_.map_sum, _root_.map_smul]
  apply Submodule.sum_mem
  intro s hs
  apply N.smul_mem
  let e := Set.powersetCard.ofFinEmbEquiv.symm s
  have he : markedExteriorBasis (F := F) s =
      wedge (orderedMarkedBasis (F := F) (e 0)) (orderedMarkedBasis (e 1)) := by
    simp only [markedExteriorBasis, exteriorPower.coe_basis, exteriorPower.ιMulti_family]
    unfold wedge
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [he]
  simpa only [orderedMarkedBasis, Module.Basis.reindex_apply] using
    h ((Fintype.equivFin TraceZeroCoordinate).symm (e 0))
      ((Fintype.equivFin TraceZeroCoordinate).symm (e 1))

end Atlas.ReeF4
