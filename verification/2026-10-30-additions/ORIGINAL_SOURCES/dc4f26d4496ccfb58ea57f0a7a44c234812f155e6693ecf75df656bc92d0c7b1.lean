import Atlas.LinearGroups.ReeF4.RootSuzukiLeviGroup
import Atlas.LinearGroups.ReeF4.RootGroupTorusNormalizer
import Atlas.LinearGroups.ReeF4.WeylTorus
import Atlas.LinearGroups.ReeF4.TorusDerived
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Actual commuting scalar torus and Suzuki subgroup. 
No identification with the full ordered-pair stabilizer is asserted. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def modelSuzukiScalarHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Fˣ →* Model F m where
  toFun s := torusModelHom hcard (thetaUnits m s,s)
  map_one' := by
    change torusModelHom hcard (thetaUnits m 1,1) = 1
    rw [map_one]
    exact (torusModelHom hcard).map_one
  map_mul' s t := by
    change torusModelHom hcard (thetaUnits m (s*t),s*t) = _
    rw [map_mul]
    exact (torusModelHom hcard).map_mul (thetaUnits m s,s) (thetaUnits m t,t)

theorem modelSuzukiScalarHom_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (modelSuzukiScalarHom hcard) := by
  intro s t h
  have hh := congrArg (fun g : Model F m => g.val) h
  have hp := torusHom_injective (F := F) m hh
  exact congrArg Prod.snd hp

theorem suzukiScalar_commutes_root {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (s : Fˣ) (a b : F) :
    Commute (torusEquiv m (thetaUnits m s) s) (shortRootPairEquiv m hcard a b) := by
  have hf : shortRootPairEquiv m hcard a b =
      shortRootPairEquiv m hcard a 0 * shortRootPairEquiv m hcard 0 b := by
    rw [shortRootPairEquiv_mul]
    simp only [add_zero, zero_add, mul_zero]
  rw [hf,torusEquiv_residual hcard s]
  exact (rootParameter_residual_comm hcard s (thetaUnits m s) a).mul_right
    (rootCenter_residual_comm hcard s (thetaUnits m s) b)

theorem suzukiScalar_commutes_torus {m : ℕ} (s b : Fˣ) :
    Commute (torusEquiv m (thetaUnits m s) s) (torusEquiv m 1 b) := by
  change torusHom m (thetaUnits m s,s) * torusHom m (1,b) =
    torusHom m (1,b) * torusHom m (thetaUnits m s,s)
  rw [← map_mul,← map_mul,mul_comm]

theorem suzukiScalar_commutes_rho {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (s : Fˣ) :
    Commute (torusEquiv m (thetaUnits m s) s) weylRho := by
  have ht : thetaUnits m (thetaUnits m s) * s⁻¹ = s := by
    rw [thetaUnits_square hcard s,pow_two]
    group
  have hh := weylRho_torus hcard (thetaUnits m s) s
  rw [ht] at hh
  have hr : (weylRho (F := F)) * weylRho = 1 := by
    simpa only [pow_two] using (weylRho_square (F := F))
  have he := congrArg (fun g : TraceZero F ≃ₗ[F] TraceZero F => g * weylRho) hh
  change torusEquiv m (thetaUnits m s) s * weylRho =
    weylRho * torusEquiv m (thetaUnits m s) s
  simpa only [mul_assoc,hr,mul_one] using he.symm

theorem suzukiLeviSubgroup_le_scalarCentralizer {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (s : Fˣ) :
    suzukiLeviSubgroup m hcard ≤
      Subgroup.centralizer {torusEquiv m (thetaUnits m s) s} := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rcases hg with (hg | hg) | hg
  · rcases hg with ⟨⟨a,b⟩,rfl⟩
    exact (suzukiScalar_commutes_root hcard s a b).eq.symm
  · rcases hg with ⟨b,rfl⟩
    exact (suzukiScalar_commutes_torus (m := m) s b).eq.symm
  · rcases hg with rfl
    exact (suzukiScalar_commutes_rho hcard s).eq.symm

theorem modelSuzuki_commutes_scalar {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.SuzukiFamily.Group F m) (s : Fˣ) :
    Commute (modelSuzukiEmbedding m hcard g) (modelSuzukiScalarHom hcard s) := by
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (suzukiLeviSubgroup_le_scalarCentralizer hcard s
      (suzukiLeviEmbedding m hcard g).property)

/-- The actual representation fixes the negative extremal coordinate functional. -/
theorem suzukiLeviHom_negative_coordinate
    (g : Atlas.Symplectic.Sp 2 F) (w : TraceZero F) :
    (suzukiLeviHom g w).val.2 0 0 = w.val.2 0 0 := by
  have h := suzukiLeviLinear_coordinates (Atlas.SuzukiFamily.matrix g) w
  exact congrArg (fun x : SuzukiLeviCoordinates F => x.2.2 0) h

theorem suzukiScalar_intersection {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.SuzukiFamily.Group F m) (s : Fˣ)
    (h : modelSuzukiEmbedding m hcard g = modelSuzukiScalarHom hcard s) : s = 1 := by
  have he := congrArg
    (fun z : Model F m => (z.val (rootVector (0,0))).val.2 0 0) h
  change (suzukiLeviHom g.val (rootVector (0,0))).val.2 0 0 =
    (torusEquiv m (thetaUnits m s) s (rootVector (0,0))).val.2 0 0 at he
  rw [suzukiLeviHom_negative_coordinate,torusEquiv_root] at he
  have hs : ((thetaUnits m s : Fˣ) : F) = 1 := by
    simpa [torusWeight,torusWeightExponents,rootVector,Pi.single_apply] using he.symm
  apply Units.ext
  apply (theta F m).injective
  change theta F m (s : F) = 1 at hs
  simpa only [Units.val_one,map_one] using hs

theorem modelSuzuki_disjoint_scalar {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Disjoint (modelSuzukiEmbedding m hcard).range (modelSuzukiScalarHom hcard).range := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨g,hg⟩,⟨s,hs⟩⟩
  have h1 := suzukiScalar_intersection hcard g s (hg.trans hs.symm)
  have hx : x = 1 := by rw [← hs,h1,map_one]
  exact hx

def modelSuzukiProductHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Atlas.SuzukiFamily.Group F m × Fˣ →* Model F m :=
  (modelSuzukiEmbedding m hcard).noncommCoprod (modelSuzukiScalarHom hcard)
    (modelSuzuki_commutes_scalar hcard)

theorem modelSuzukiProductHom_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) : Function.Injective (modelSuzukiProductHom hcard) :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨modelSuzukiEmbedding_injective m hcard,modelSuzukiScalarHom_injective hcard,
      modelSuzuki_disjoint_scalar hcard⟩

def modelSuzukiProductSubgroup {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Subgroup (Model F m) := (modelSuzukiProductHom hcard).range

def modelSuzukiProductEquiv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Atlas.SuzukiFamily.Group F m × Fˣ ≃* modelSuzukiProductSubgroup hcard :=
  MonoidHom.ofInjective (modelSuzukiProductHom_injective hcard)

end Atlas.ReeF4
