import Atlas.LinearGroups.Orthogonal.Minus.RankThreeHodge
import Atlas.LinearGroups.Orthogonal.D3ExteriorAction
import Atlas.LinearGroups.Unitary.Hermitian

/-! The actual exterior action of SU4 preserves the semilinear Hodge fixed space. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open B2Exterior Matrix Atlas.FiniteQuadratic
section Compound
variable {L : Type*} [CommRing L]

theorem compound_mul (A B : Matrix (Fin 4) (Fin 4) L) :
    compound (A*B)=compound A*compound B := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  exact exteriorMap_mul A B

theorem compound_one : compound (1 : Matrix (Fin 4) (Fin 4) L)=1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_one]
  exact exteriorMap_one

theorem compound_dagger (σ : L →+* L) (A : Matrix (Fin 4) (Fin 4) L) :
    compound (A.transpose.map σ)=(compound A).transpose.map σ := by
  ext i j
  simp [compound,map_sub,map_mul,mul_comm]
end Compound

variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def suExteriorUnitary (hdeg : Module.finrank F K=2) (g : Atlas.Unitary.SU F K 4 hdeg) :
    Atlas.Unitary.U F K 6 hdeg := by
  letI := Atlas.Unitary.conjugationStarRing F K hdeg
  refine ⟨compound g.val, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (compound g.val).transpose.map (conjugation F K) * compound g.val=1
  have hc : compound (g.val.transpose.map (conjugation F K)) =
      (compound g.val).transpose.map (conjugation F K) := by
    ext i j
    simp [compound,map_sub,map_mul,mul_comm]
  rw [← hc,← compound_mul]
  have hg : g.val.transpose.map (conjugation F K)*g.val=1 := g.prop.1.1
  rw [hg,compound_one]

def suExteriorEquiv (hdeg : Module.finrank F K=2) (g : Atlas.Unitary.SU F K 4 hdeg) :
    Six K ≃ₗ[K] Six K :=
  D3Exterior.exteriorAction ⟨g.val,g.prop.2⟩

theorem exterior_preserves_hermitian (hdeg : Module.finrank F K=2)
    (g : Atlas.Unitary.SU F K 4 hdeg) (x y : Six K) :
    Atlas.Unitary.hermitian F K (exteriorMap g.val x) (exteriorMap g.val y)=
      Atlas.Unitary.hermitian F K x y :=
  by simpa only [suExteriorUnitary,exteriorMap,Matrix.toLin'_apply] using
    Atlas.Unitary.u_preserves_hermitian hdeg (suExteriorUnitary hdeg g) x y

theorem hermitian_hodge_polar (hdeg : Module.finrank F K=2) (x y : Six K) :
    Atlas.Unitary.hermitian F K x (hodge (F := F) y) = pfaffian.polarBilin x y := by
  simp [Atlas.Unitary.hermitian,hodge,Fin.sum_univ_succ,
    conjugation_conjugation hdeg,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  ring

theorem exterior_preserves_pfaffian_polar (hdeg : Module.finrank F K=2)
    (g : Atlas.Unitary.SU F K 4 hdeg) (x y : Six K) :
    pfaffian.polarBilin (exteriorMap g.val x) (exteriorMap g.val y)=
      pfaffian.polarBilin x y := by
  have hd : g.val.det=1 := g.prop.2
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    ← map_add,pfaffian_exteriorMap,hd,one_mul]

theorem exterior_commutes_hodge (hdeg : Module.finrank F K=2)
    (g : Atlas.Unitary.SU F K 4 hdeg) (y : Six K) :
    exteriorMap g.val (hodge (F := F) y)=hodge (F := F) (exteriorMap g.val y) := by
  have hp (w : Six K) :
      Atlas.Unitary.hermitian F K w (exteriorMap g.val (hodge (F := F) y)) =
        Atlas.Unitary.hermitian F K w (hodge (F := F) (exteriorMap g.val y)) := by
    obtain ⟨x,hx⟩ := (suExteriorEquiv hdeg g).surjective w
    change exteriorMap g.val x=w at hx
    rw [← hx,exterior_preserves_hermitian,hermitian_hodge_polar hdeg,
      hermitian_hodge_polar hdeg,exterior_preserves_pfaffian_polar]
  ext i
  apply (conjugation F K).injective
  simpa [Atlas.Unitary.hermitian,Pi.single_apply] using hp (Pi.single i 1)

/-- Restriction is made only after proving the actual exterior action preserves Fix(J). -/
def hodgeFixedAction (hdeg : Module.finrank F K=2)
    (g : Atlas.Unitary.SU F K 4 hdeg) : hodgeFixed hdeg ≃ₗ[F] hodgeFixed hdeg where
  toFun x := ⟨exteriorMap g.val x.val,by
    change hodge (F := F) (exteriorMap g.val x.val)=exteriorMap g.val x.val
    rw [← exterior_commutes_hodge hdeg g,x.prop]⟩
  invFun x := ⟨exteriorMap g⁻¹.val x.val,by
    change hodge (F := F) (exteriorMap g⁻¹.val x.val)=exteriorMap g⁻¹.val x.val
    rw [← exterior_commutes_hodge hdeg g⁻¹,x.prop]⟩
  left_inv x := by
    apply Subtype.ext
    change exteriorMap g⁻¹.val (exteriorMap g.val x.val)=x.val
    change ((exteriorMap g⁻¹.val).comp (exteriorMap g.val)) x.val=x.val
    rw [← exteriorMap_mul]
    have he : g⁻¹.val*g.val=1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [he,exteriorMap_one,LinearMap.id_apply]
  right_inv x := by
    apply Subtype.ext
    change exteriorMap g.val (exteriorMap g⁻¹.val x.val)=x.val
    change ((exteriorMap g.val).comp (exteriorMap g⁻¹.val)) x.val=x.val
    rw [← exteriorMap_mul]
    have he : g.val*g⁻¹.val=1 := congrArg Subtype.val (mul_inv_cancel g)
    rw [he,exteriorMap_one,LinearMap.id_apply]
  map_add' x y := by apply Subtype.ext; exact map_add (exteriorMap g.val) x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact (exteriorMap g.val).restrictScalars F |>.map_smul c x.val
theorem hodgeFixedAction_preserves (hdeg : Module.finrank F K=2)
    (g : Atlas.Unitary.SU F K 4 hdeg) (x : hodgeFixed hdeg) :
    hodgeFixedForm hdeg (hodgeFixedAction hdeg g x)=hodgeFixedForm hdeg x := by
  apply (algebraMap F K).injective
  rw [hodgeFixedForm_pfaffian,hodgeFixedForm_pfaffian]
  change pfaffian (exteriorMap g.val x.val)=pfaffian x.val
  have hd : g.val.det=1 := g.prop.2
  rw [pfaffian_exteriorMap,hd,one_mul]

def hodgeFixedHom (hdeg : Module.finrank F K=2) :
    Atlas.Unitary.SU F K 4 hdeg →* (hodgeFixed hdeg ≃ₗ[F] hodgeFixed hdeg) where
  toFun := hodgeFixedAction hdeg
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change exteriorMap (1 : Matrix (Fin 4) (Fin 4) K) x.val=x.val
    rw [exteriorMap_one,LinearMap.id_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change exteriorMap (g.val*h.val) x.val=exteriorMap g.val (exteriorMap h.val x.val)
    rw [exteriorMap_mul,LinearMap.comp_apply]
end Atlas.Orthogonal.Minus

