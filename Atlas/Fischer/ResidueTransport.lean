import Atlas.Fischer.ResidueModels
import Atlas.Fischer.ResidueCentralizerOrder
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private theorem centralizer_transport {A B : Set rootGeneratedRayGroup}
    (e : MulAut rootGeneratedRayGroup) (h : e '' A = B)
    {x : rootGeneratedRayGroup} (hx : x ∈ Subgroup.centralizer A) :
    e x ∈ Subgroup.centralizer B := by
  rintro y hy
  rw [← h] at hy
  obtain ⟨z,hz,rfl⟩ := hy
  simpa only [map_mul] using congrArg e (hx z hz)

private theorem image_symm_eq {A B : Set rootGeneratedRayGroup}
    (e : MulAut rootGeneratedRayGroup) (h : e '' A = B) : e.symm '' B = A := by
  rw [← h,Set.image_image]
  simp

/-- Conjugation transports the actual centralizers of the marked elements. -/
def residueCentralizerTransport (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T) :
    residueCentralizer S ≃* residueCentralizer T where
  toFun x := ⟨MulAut.conj g x.val, centralizer_transport (MulAut.conj g) h x.property⟩
  invFun x := ⟨(MulAut.conj g).symm x.val,
    centralizer_transport (MulAut.conj g).symm (image_symm_eq _ h) x.property⟩
  left_inv x := Subtype.ext ((MulAut.conj g).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((MulAut.conj g).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((MulAut.conj g).map_mul x.val y.val)

@[simp] theorem residueCentralizerTransport_val (S T : Finset Omega)
    (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T)
    (x : residueCentralizer S) :
    (residueCentralizerTransport S T g h x).val = g*x.val*g⁻¹ := rfl

theorem residueElementary_transport (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T) :
    (residueElementary S).map (MulAut.conj g).toMonoidHom = residueElementary T := by
  unfold residueElementary
  rw [MonoidHom.map_closure]
  exact congrArg Subgroup.closure h

/-- The specified central subgroup is carried onto the specified central subgroup. -/
theorem residueCentralElementary_transport (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T) :
    (residueCentralElementary S).map (residueCentralizerTransport S T g h).toMonoidHom =
      residueCentralElementary T := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change MulAut.conj g x.val ∈ residueElementary T
    rw [← residueElementary_transport S T g h]
    exact ⟨x.val,hx,rfl⟩
  · intro hy
    have hm : y.val ∈ (residueElementary S).map (MulAut.conj g).toMonoidHom := by
      rw [residueElementary_transport S T g h]
      exact hy
    obtain ⟨x,hx,hxy⟩ := hm
    refine ⟨⟨x,residueElementary_le_centralizer S hx⟩,hx,?_⟩
    exact Subtype.ext hxy

/-- The residue quotient isomorphism is induced by the same actual conjugator. -/
def residueQuotientTransport (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T) :
    residueCentralizer S ⧸ residueCentralElementary S ≃*
      residueCentralizer T ⧸ residueCentralElementary T :=
  QuotientGroup.congr _ _ (residueCentralizerTransport S T g h)
    (residueCentralElementary_transport S T g h)

/-- Actual small-clique homogeneity makes the marking independent of its coordinates. -/
theorem residueBasicSets_conjugate (S T : Finset Omega) (hS : S.card ≤ 5)
    (hST : S.card = T.card) :
    ∃ g : rootGeneratedRayGroup, (MulAut.conj g) '' residueBasicSet S = residueBasicSet T := by
  let a := residueCoordinateEmbedding S
  let b : Fin S.card ↪ Omega :=
    (finCongr hST).toEmbedding.trans (residueCoordinateEmbedding T)
  have hb : Finset.univ.image b = T := by
    classical
    ext i
    constructor
    · intro hi
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
      exact ((T.equivFin).symm (finCongr hST k)).property
    · intro hi
      refine Finset.mem_image.mpr ⟨(finCongr hST).symm (T.equivFin ⟨i,hi⟩),
        Finset.mem_univ _,?_⟩
      change ((T.equivFin).symm (finCongr hST ((finCongr hST).symm _))).val = i
      rw [Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  obtain ⟨g,hg⟩ := commutingTuples_homogeneous hS (basicCommutingTuple a) (basicCommutingTuple b)
    (basicOrderedCommutingTuple a).property.1 (basicOrderedCommutingTuple b).property.1
    (basicOrderedCommutingTuple a).property.2 (basicOrderedCommutingTuple b).property.2
  refine ⟨g,?_⟩
  classical
  ext x
  constructor
  · rintro ⟨_,⟨i,hi,rfl⟩,rfl⟩
    rw [← residueCoordinateEmbedding_image S] at hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    refine ⟨b k,?_,(hg k).symm⟩
    rw [← hb]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    rw [← hb] at hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    refine ⟨distinguishedRootElement (.inl (a k)),⟨a k,?_,rfl⟩,hg k⟩
    exact ((S.equivFin).symm k).property

end Atlas.Fischer
