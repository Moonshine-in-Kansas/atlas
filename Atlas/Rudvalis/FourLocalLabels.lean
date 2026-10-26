import Atlas.Rudvalis.FourLocalWordOrbit
import Atlas.Rudvalis.SeedFrobenius
import Atlas.Rudvalis.FourOrthogonalCount

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
set_option maxRecDepth 16384

theorem codeT_coordinate_pow_inverse (n : ℕ) (z : SeedCoordinate) :
    (codeT^n).val.right.symm (originalCoordinateEquiv z)=originalCoordinateEquiv ((seedTCoord^n) z) := by
  have ht : codeT.val.right=originalCoordinateEquiv.permCongrHom seedTCoord.symm :=
    seedConjugateMonomial_right _
  have hp : (codeT^n).val.right=originalCoordinateEquiv.permCongrHom (seedTCoord.symm^n) := by
    change SemidirectProduct.rightHom (codeT.val^n)=_
    rw [map_pow]
    change codeT.val.right^n=_
    rw [ht,map_pow]
  rw [hp]
  change (originalCoordinateEquiv.permCongrHom (seedTCoord.symm^n))⁻¹ (originalCoordinateEquiv z)=_
  rw [←map_inv,←inv_pow]
  change originalCoordinateEquiv.permCongrHom ((seedTCoord⁻¹)⁻¹^n) (originalCoordinateEquiv z)=_
  rw [inv_inv,original_congr_apply]

theorem codeT_local_fix :
    codeT • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) := by
  apply original_coordinate_cross_fix codeT seedTMonomial rfl
  left
  decide +kernel

theorem codeT_pow_local_fix (n : ℕ) :
    codeT^n • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) := by
  induction n with
  | zero => rw [pow_zero,one_smul]
  | succ n ih => rw [pow_succ,mul_smul,codeT_local_fix,ih]

theorem fourNormal_pair (ε : Point→Bit) (a : E) (p : Point) (x : E) :
    binaryNormalMap (ε,outerMatrix a a,0) (p,x)+
      binaryNormalMap (ε,outerMatrix a a,0) (p,x+p.val)=dot a p.val := by
  change (ε p+dot (matrixAt (outerMatrix a a) p.val) x+theta p 0 x)+
    (ε p+dot (matrixAt (outerMatrix a a) p.val) (x+p.val)+theta p 0 (x+p.val))=_
  simp only [matrixAt_outer,dot_smul_left,theta_zero_parameter,add_zero,dot_add_right]
  have h : ∀e s t : Bit,(e+s*t)+(e+(s*t+s*s))=s := by decide +kernel
  exact h _ _ _

theorem originalCoordinate_pair (r : Fin 7) :
    originalCoordinateEquiv (r,1)=(rowLabel r,0) ∧
    originalCoordinateEquiv (r,0)=(rowLabel r,(rowLabel r).val) := by
  decide +kernel +revert

theorem codeT_label_cycle (a : Point) (ha : dot a.val (rowLabel 0).val=0) :
    ∃n : Fin 3,∀r : Fin 7,dot a.val (rowLabel ((seedTRowEquiv^n.val) r)).val=dot (binaryLabel 1) (rowLabel r).val := by
  obtain ⟨j,rfl⟩ := rowLabel_bijective.2 a
  decide +kernel +revert

theorem codeT_original_pair (n : ℕ) (r : Fin 7) (k : Fin 8) (hk : k=0 ∨ k=1) :
    (seedTCoord^n) (r,k)=((seedTRowEquiv^n) r,k) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,Equiv.Perm.mul_apply]
    have he : seedTCoord (r,k)=(seedTRowEquiv r,k) := by
      rcases hk with rfl|rfl <;> rfl
    rw [he,ih]
    rfl

theorem codeT_transported_pair (n : ℕ) (w : QuaternaryWord) (ε : Point→Bit) (a : E)
    (hw : reduce w=binaryNormalMap (ε,outerMatrix a a,0)) (r : Fin 7) :
    reduce (monomialHom (codeT^n).val w) (rowLabel r,0)+
      reduce (monomialHom (codeT^n).val w) (rowLabel r,(rowLabel r).val)=
      dot a (rowLabel ((seedTRowEquiv^n) r)).val := by
  change reduce (monomialAction (codeT^n).val w) _+reduce (monomialAction (codeT^n).val w) _=_
  rw [monomialAction_reduce,←(originalCoordinate_pair r).1,←(originalCoordinate_pair r).2]
  change reduce w ((codeT^n).val.right.symm (originalCoordinateEquiv (r,1)))+
    reduce w ((codeT^n).val.right.symm (originalCoordinateEquiv (r,0)))=_
  rw [codeT_coordinate_pow_inverse,codeT_coordinate_pow_inverse,
    codeT_original_pair n r 1 (Or.inr rfl),codeT_original_pair n r 0 (Or.inl rfl),
    (originalCoordinate_pair _).1,(originalCoordinate_pair _).2,hw]
  simpa only [zero_add] using fourNormal_pair ε a (rowLabel ((seedTRowEquiv^n) r)) 0

end Atlas.Rudvalis
