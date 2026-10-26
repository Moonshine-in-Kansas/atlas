import Atlas.Rudvalis.FourPlaneGeometry
import Atlas.Rudvalis.MinimumSupportObstructions
import Atlas.Codes.QuaternaryLiftFibres

/-! Common moments of torsion words on four active affine planes. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Atlas.Rudvalis
open scoped BigOperators

/-- The four selected planes in the `a=1` normal form. -/
def fourPlaneSupport (r : Fin 4 → Bit) : BinaryWord := fun z =>
  if z.1.val 0=1 ∧ z.2 0=r (squareIndex (z.1.val 1) (z.1.val 2)) then 1 else 0


abbrev FourPlaneParameters := (Fin 4 → Bit) × Bit × Bit

/-- Six affine parameters: four row constants and the common two-dimensional moment. -/
def fourPlaneParamMap (r : Fin 4 → Bit) : FourPlaneParameters →ₗ[Bit] BinaryWord where
  toFun v z := if z.1.val 0=1 ∧ z.2 0=r (squareIndex (z.1.val 1) (z.1.val 2)) then
    v.1 (squareIndex (z.1.val 1) (z.1.val 2))+v.2.1*z.2 1+v.2.2*z.2 2 else 0
  map_add' u v := by
    funext z
    dsimp
    split <;> ring
  map_smul' a v := by
    funext z
    dsimp
    split <;> ring

theorem point_active_sum (f : Point → Bit) :
    (∑ p : Point,if p.val 0=1 then f p else 0)=∑ i : Fin 4,f (fourActivePoint i) := by
  classical
  have hi (p : Point) : (if p.val 0=1 then (1 : Bit) else 0)=
      ∑ i : Fin 4,if p=fourActivePoint i then 1 else 0 := by decide +kernel +revert
  calc
    _ = ∑ p : Point,(if p.val 0=1 then (1 : Bit) else 0)*f p := by simp
    _ = ∑ p : Point,∑ i : Fin 4,(if p=fourActivePoint i then (1 : Bit) else 0)*f p := by
      simp_rw [hi,Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm]; simp

noncomputable def torsionRowMoment
 (w : BinaryWord) (p : Point) : E :=
  ∑ x : E,w (p,x) • x

theorem torsion_matrix_moment (w : BinaryWord) (hw : w∈binaryTorsion) (i j : Fin 3) :
    (∑ p : Point,p.val i * torsionRowMoment w p j)=0 := by
  let M := outerMatrix (Pi.single j 1) (Pi.single i 1)
  have h := hw (binaryNormalMap (0,M,0)) ⟨_,rfl⟩
  rw [Atlas.Codes.binaryDot_apply,Fintype.sum_prod_type] at h
  have hv (p : Point) (x : E) : binaryNormalMap (0,M,0) (p,x)=p.val i*x j := by
    change 0+dot (matrixAt M p.val) x+theta p 0 x=_
    rw [theta_zero_parameter]
    simp [M,matrixAt_outer,dot,Pi.single_apply,ite_mul]
  simp_rw [hv] at h
  simpa [torsionRowMoment,Finset.sum_apply,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm] using h

theorem torsion_four_active_common_moment (w : BinaryWord) (hw : w∈binaryTorsion)
    (hs : ∀ p : Point,p.val 0≠1 → ∀ x,w (p,x)=0) :
    ∀ i : Fin 4,torsionRowMoment w (fourActivePoint i)=torsionRowMoment w (fourActivePoint 0) := by
  intro i
  ext j
  apply (fourActivePoint_relation (fun k => torsionRowMoment w (fourActivePoint k) j)).mp ?_ i
  intro k
  have h := torsion_matrix_moment w hw k j
  have he : (∑ p : Point,p.val k*torsionRowMoment w p j)=
      ∑ p : Point,if p.val 0=1 then p.val k*torsionRowMoment w p j else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.val 0=1
    · simp [hp]
    · simp [torsionRowMoment,hs p hp,hp]
  rw [he,point_active_sum] at h
  exact h


theorem cube_plane_sum (r : Bit) (f : E → Bit) (hs : ∀ x,x 0≠r → f x=0) :
    (∑ x : E,f x)=∑ i : Fin 4,f (fourPlanePoint r i) := by
  classical
  have hi (x : E) : (if x 0=r then (1 : Bit) else 0)=
      ∑ i : Fin 4,if x=fourPlanePoint r i then 1 else 0 := by decide +kernel +revert
  calc
    _ = ∑ x : E,(if x 0=r then (1 : Bit) else 0)*f x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x 0=r
      · simp [hx]
      · simp [hx,hs x hx]
    _ = ∑ x : E,∑ i : Fin 4,(if x=fourPlanePoint r i then (1 : Bit) else 0)*f x := by
      simp_rw [hi,Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem cube_plane_moment
 (r : Bit) (f : E → Bit) (hs : ∀ x,x 0≠r → f x=0) :
    (∑ x : E,f x • x)=∑ i : Fin 4,f (fourPlanePoint r i) • fourPlanePoint r i := by
  ext j
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact cube_plane_sum r (fun x => f x*x j) (fun x hx => by rw [hs x hx,zero_mul])

/-- Every supported even word is determined by its constant and first moment. -/
theorem cube_plane_affine (r : Bit) (f : E → Bit) (hs : ∀ x,x 0≠r → f x=0)
    (he : (∑ x : E,f x)=0) (x : E) (hx : x 0=r) :
    f x=f (fourPlanePoint r 0)+(∑ y : E,f y • y) 2*x 1+(∑ y : E,f y • y) 1*x 2 := by
  obtain ⟨δ,hδ,_⟩ := four_plane_even_moment_classification r (fun i => f (fourPlanePoint r i))
    ((cube_plane_sum r f hs).symm.trans he)
  have hδ0 := hδ 0
  simp [fourPlanePattern,fourPlanePoint] at hδ0
  have h := hδ (squareIndex (x 1) (x 2))
  have hpoint : fourPlanePoint r (squareIndex (x 1) (x 2))=x := by
    rw [← hx]; exact fourPlanePoint_inverse x
  rw [hpoint,← cube_plane_moment r f hs] at h
  rw [fourPlanePattern,← hδ0] at h
  have h1 := congrFun hpoint 1
  have h2 := congrFun hpoint 2
  have he1 : fourPlanePoint 0 (squareIndex (x 1) (x 2)) 1=x 1 := h1
  have he2 : fourPlanePoint 0 (squareIndex (x 1) (x 2)) 2=x 2 := h2
  rwa [he1,he2] at h


theorem squareIndex_fourPlanePoint (r : Bit) (i : Fin 4) :
    squareIndex (fourPlanePoint r i 1) (fourPlanePoint r i 2)=i := by decide +kernel +revert

theorem fourPlaneParamMap_apply (r : Fin 4 → Bit) (v : FourPlaneParameters) (i : Fin 4)
    (x : E) (hx : x 0=r i) :
    fourPlaneParamMap r v (fourActivePoint i,x)=v.1 i+v.2.1*x 1+v.2.2*x 2 := by
  change (if (fourPlanePoint 1 i) 0=1 ∧ x 0=r (squareIndex (fourPlanePoint 1 i 1)
    (fourPlanePoint 1 i 2)) then v.1 (squareIndex (fourPlanePoint 1 i 1)
    (fourPlanePoint 1 i 2))+v.2.1*x 1+v.2.2*x 2 else 0)=_
  rw [squareIndex_fourPlanePoint]
  simp [fourPlanePoint,hx]

theorem fourPlaneParamMap_injective (r : Fin 4 → Bit) : Function.Injective (fourPlaneParamMap r) := by
  intro u v h
  have he (i : Fin 4) (j : Fin 4) :
      u.1 i+u.2.1*fourPlanePoint (r i) j 1+u.2.2*fourPlanePoint (r i) j 2=
      v.1 i+v.2.1*fourPlanePoint (r i) j 1+v.2.2*fourPlanePoint (r i) j 2 := by
    have hh := congrFun h (fourActivePoint i,fourPlanePoint (r i) j)
    rwa [fourPlaneParamMap_apply r u i _ rfl,fourPlaneParamMap_apply r v i _ rfl] at hh

  have hd : u.1=v.1 := by
    funext i
    simpa [fourPlanePoint] using he i 0
  have hb : u.2.1=v.2.1 := by
    have h := he 0 1
    simpa [fourPlanePoint,hd] using h
  have hc : u.2.2=v.2.2 := by
    have h := he 0 2
    simpa [fourPlanePoint,hd] using h
  exact Prod.ext hd (Prod.ext hb hc)

theorem fourPlaneParamMap_supported (r : Fin 4 → Bit) (v : FourPlaneParameters) :
    ∀ z,fourPlaneSupport r z=0 → fourPlaneParamMap r v z=0 := by
  intro z hz
  unfold fourPlaneSupport at hz
  change (if z.1.val 0=1 ∧ z.2 0=r (squareIndex (z.1.val 1) (z.1.val 2)) then _ else 0)=0
  split <;> simp_all

/-- Every shortened torsion word has the six-parameter common-moment form. -/
theorem fourPlaneParamMap_complete (r : Fin 4 → Bit) (w : BinaryWord) (hw : w∈binaryTorsion)
    (hs : ∀ z,fourPlaneSupport r z=0 → w z=0) :
    ∃ v : FourPlaneParameters,fourPlaneParamMap r v=w := by
  have hinactive (p : Point) (hp : p.val 0≠1) (x : E) : w (p,x)=0 :=
    hs _ (by simp [fourPlaneSupport,hp])
  have hmoment := torsion_four_active_common_moment w hw hinactive
  let v : FourPlaneParameters :=
    (fun i => w (fourActivePoint i,fourPlanePoint (r i) 0),
      torsionRowMoment w (fourActivePoint 0) 2,torsionRowMoment w (fourActivePoint 0) 1)
  refine ⟨v,?_⟩
  funext z
  rcases z with ⟨p,x⟩
  by_cases hp : p.val 0=1
  · have hpa : ∃ i : Fin 4,fourActivePoint i=p := by
      refine ⟨squareIndex (p.val 1) (p.val 2),?_⟩
      apply Subtype.ext
      change fourPlanePoint 1 _=p.val
      rw [← hp]
      exact fourPlanePoint_inverse p.val
    obtain ⟨i,rfl⟩ := hpa
    by_cases hx : x 0=r i
    · rw [fourPlaneParamMap_apply r v i x hx]
      have hplane (y : E) (hy : y 0≠r i) : w (fourActivePoint i,y)=0 := hs _ (by
        simp only [fourPlaneSupport,fourActivePoint,squareIndex_fourPlanePoint]
        simp [hy])
      have he := (Atlas.Codes.even_weight_iff _).mp (binaryTorsion_row_even w hw (fourActivePoint i))
      have hc := cube_plane_affine (r i) (fun y => w (fourActivePoint i,y)) hplane he x hx
      change w (fourActivePoint i,x)=w (fourActivePoint i,fourPlanePoint (r i) 0)+
        torsionRowMoment w (fourActivePoint i) 2*x 1+
        torsionRowMoment w (fourActivePoint i) 1*x 2 at hc
      rw [hmoment i] at hc
      exact hc.symm
    · have hz : fourPlaneSupport r (fourActivePoint i,x)=0 := by
        simp only [fourPlaneSupport,fourActivePoint,squareIndex_fourPlanePoint]
        simp [hx]
      rw [fourPlaneParamMap_supported r v _ hz,hs _ hz]
  · have hz : fourPlaneSupport r (p,x)=0 := by simp [fourPlaneSupport,hp]
    rw [fourPlaneParamMap_supported r v _ hz,hs _ hz]


/-- The two global parameters are precisely the two free coordinates of the common moment. -/
theorem fourPlaneParamMap_row_moment (r : Fin 4 → Bit) (v : FourPlaneParameters) (i : Fin 4) :
    torsionRowMoment (fourPlaneParamMap r v) (fourActivePoint i)=![0,v.2.2,v.2.1] := by
  have hs (x : E) (hx : x 0≠r i) : fourPlaneParamMap r v (fourActivePoint i,x)=0 :=
    fourPlaneParamMap_supported r v _ (by
      simp only [fourPlaneSupport,fourActivePoint,squareIndex_fourPlanePoint]
      simp [hx])
  change (∑ x : E,fourPlaneParamMap r v (fourActivePoint i,x) • x)=_
  rw [cube_plane_moment (r i) _ hs]
  have hv (j : Fin 4) : fourPlaneParamMap r v (fourActivePoint i,fourPlanePoint (r i) j)=
      fourPlanePattern (v.1 i) v.2.1 v.2.2 j := by
    rw [fourPlaneParamMap_apply r v i _ rfl]
    rfl
  simp_rw [hv]
  exact (fourPlanePattern_moments (r i) (v.1 i) v.2.1 v.2.2).2

theorem fourPlaneParamMap_row_even (r : Fin 4 → Bit) (v : FourPlaneParameters) (i : Fin 4) :
    (∑ x : E,fourPlaneParamMap r v (fourActivePoint i,x))=0 := by
  have hs (x : E) (hx : x 0≠r i) : fourPlaneParamMap r v (fourActivePoint i,x)=0 :=
    fourPlaneParamMap_supported r v _ (by
      simp only [fourPlaneSupport,fourActivePoint,squareIndex_fourPlanePoint]
      simp [hx])
  rw [cube_plane_sum (r i) _ hs]
  have hv (j : Fin 4) : fourPlaneParamMap r v (fourActivePoint i,fourPlanePoint (r i) j)=
      fourPlanePattern (v.1 i) v.2.1 v.2.2 j := by
    rw [fourPlaneParamMap_apply r v i _ rfl]
    rfl
  simp_rw [hv]
  exact (fourPlanePattern_moments (r i) (v.1 i) v.2.1 v.2.2).1

end Atlas.Rudvalis
