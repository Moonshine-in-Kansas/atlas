import Atlas.LinearGroups.ReeF4.WeylSL2Torus
import Atlas.LinearGroups.ReeF4.RootGroupMembership

/-! Every long-root parameter belongs to the full intrinsic Ree stabilizer.
Nonzero parameters are torus conjugates of the previously audited long-root
involution, using the existing inverse Frobenius on the finite field. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem longRootEquiv_mem_modelSubgroup (m : ℕ) :
    (longRootEquiv : TraceZero F ≃ₗ[F] TraceZero F) ∈ modelSubgroup F m := by
  rw [mem_modelSubgroup_iff]
  exact ⟨longRootEquiv_mem_polynomialStabilizer,
    longRoot_mem_candidatePartialStabilizer (thetaInv F m).toRingHom⟩

theorem longSL2Parameter_mem_modelSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : F) :
    longSL2Equiv u (theta F m u) ∈ modelSubgroup F m := by
  by_cases hu : u = 0
  · subst u
    rw [map_zero, longSL2Equiv_zero]
    exact (modelSubgroup F m).one_mem
  · obtain ⟨s, hs⟩ := (frobeniusEquiv F 2).surjective u
    change s^2 = u at hs
    have hs0 : s ≠ 0 := by
      intro h
      apply hu
      simpa [h] using hs.symm
    let a : Fˣ := Units.mk0 s hs0
    have ha : (a : F)^2 = u := hs
    have ht := torusEquiv_mem_modelSubgroup hcard a a⁻¹
    have hh := (modelSubgroup F m).mul_mem
      ((modelSubgroup F m).mul_mem ht (longRootEquiv_mem_modelSubgroup m))
      ((modelSubgroup F m).inv_mem ht)
    rw [longSL2Parameter_torus_one, ha] at hh
    exact hh

theorem longSL2RootSubgroup_le_modelSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    longSL2RootSubgroup (theta F m).toRingHom ≤ modelSubgroup F m := by
  rintro g ⟨u,rfl⟩
  exact longSL2Parameter_mem_modelSubgroup hcard u.toAdd

def modelLongSL2RootHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Multiplicative F →* Model F m where
  toFun u := ⟨longSL2ParameterHom (theta F m).toRingHom u,
    longSL2Parameter_mem_modelSubgroup hcard u.toAdd⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (longSL2ParameterHom (theta F m).toRingHom)
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (longSL2ParameterHom (theta F m).toRingHom) u v

theorem modelLongSL2RootHom_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) : Function.Injective (modelLongSL2RootHom hcard) := by
  intro u v h
  exact longSL2ParameterHom_injective (theta F m).toRingHom
    (congrArg (fun g : Model F m => g.val) h)

def modelLongSL2RootSubgroup {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Subgroup (Model F m) := (modelLongSL2RootHom hcard).range

def modelLongSL2RootEquiv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Multiplicative F ≃* modelLongSL2RootSubgroup hcard :=
  MonoidHom.ofInjective (modelLongSL2RootHom_injective hcard)

theorem card_modelLongSL2RootSubgroup {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (modelLongSL2RootSubgroup hcard) = 2^(2*m+1) := by
  rw [← Nat.card_congr (modelLongSL2RootEquiv hcard).toEquiv]
  exact hcard

end Atlas.ReeF4
