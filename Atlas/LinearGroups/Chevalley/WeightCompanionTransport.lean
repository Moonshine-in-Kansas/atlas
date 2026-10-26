import Atlas.LinearGroups.Chevalley.WeightCompanion

/-! Coefficient transport for the concrete adjoint/minuscule companion. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open scoped DirectSum
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)
  (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

variable {R} {S : Type*} [CommRing S]

omit [Fintype ι] [DecidableEq ι] [P.IsReduced] in
/-- Entrywise coefficient transport on the actual finite minuscule module. -/
theorem weightOrbitRootElement_map (a : κ) (φ : R →+* S) (i : ι)
    (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    Units.map φ.mapMatrix.toMonoidHom
      (weightOrbitRootElement P (O a) (hclosed a) (hmin a) R i ε hε t) =
    weightOrbitRootElement P (O a) (hclosed a) (hmin a) S i ε hε (φ t) := by
  apply Units.ext
  ext μ ν
  change φ ((weightOrbitRootElement P (O a) (hclosed a) (hmin a) R i ε hε t).val μ ν) = _
  rw [weightOrbitRootElement_entry, weightOrbitRootElement_entry]
  split_ifs <;> simp

def weightCompanionAmbientMap (φ : R →+* S) :
    WeightCompanionAmbient P b O R →* WeightCompanionAmbient P b O S where
  toFun g := (adjointMap P b φ g.1, fun a => Units.map φ.mapMatrix.toMonoidHom (g.2 a))
  map_one' := by
    apply Prod.ext
    · exact map_one _
    · funext a
      exact map_one _
  map_mul' g h := by
    apply Prod.ext
    · exact map_mul _ _ _
    · funext a
      exact map_mul _ _ _

theorem weightCompanionAmbientMap_X (φ : R →+* S) (i : b.support) (t : R) :
    weightCompanionAmbientMap P b O φ (weightCompanionRootX P b O hclosed hmin R i t) =
      weightCompanionRootX P b O hclosed hmin S i (φ t) := by
  apply Prod.ext
  · exact adjointMap_x P b φ i t
  · funext a
    exact weightOrbitRootElement_map P O hclosed hmin a φ i.val (-1) (by decide) t

theorem weightCompanionAmbientMap_Y (φ : R →+* S) (i : b.support) (t : R) :
    weightCompanionAmbientMap P b O φ (weightCompanionRootY P b O hclosed hmin R i t) =
      weightCompanionRootY P b O hclosed hmin S i (φ t) := by
  apply Prod.ext
  · exact adjointMap_y P b φ i t
  · funext a
    exact weightOrbitRootElement_map P O hclosed hmin a φ i.val 1 (by decide) t

theorem weightCompanionAmbientMap_mem (φ : R →+* S) {g : WeightCompanionAmbient P b O R}
    (hg : g ∈ weightCompanionSubgroup P b O hclosed hmin R) :
    weightCompanionAmbientMap P b O φ g ∈ weightCompanionSubgroup P b O hclosed hmin S := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨i,t,rfl⟩ | ⟨i,t,rfl⟩
    · rw [weightCompanionAmbientMap_X]
      exact Subgroup.subset_closure (Or.inl ⟨i,φ t,rfl⟩)
    · rw [weightCompanionAmbientMap_Y]
      exact Subgroup.subset_closure (Or.inr ⟨i,φ t,rfl⟩)
  | one => simpa only [map_one] using (weightCompanionSubgroup P b O hclosed hmin S).one_mem
  | mul g h hg hh ihg ihh => simpa only [map_mul] using Subgroup.mul_mem _ ihg ihh
  | inv g hg ih => simpa only [map_inv] using Subgroup.inv_mem _ ih

/-- Coefficient transport preserves the generated companion and the specified adjoint map. -/
def weightCompanionMap (φ : R →+* S) :
    WeightCompanion P b O hclosed hmin R →* WeightCompanion P b O hclosed hmin S where
  toFun g := ⟨weightCompanionAmbientMap P b O φ g.val,
    weightCompanionAmbientMap_mem P b O hclosed hmin φ g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

@[simp] theorem weightCompanionMap_X (φ : R →+* S) (i : b.support) (t : R) :
    weightCompanionMap P b O hclosed hmin φ (weightCompanionX P b O hclosed hmin R i t) =
      weightCompanionX P b O hclosed hmin S i (φ t) :=
  Subtype.ext (weightCompanionAmbientMap_X P b O hclosed hmin φ i t)

@[simp] theorem weightCompanionMap_Y (φ : R →+* S) (i : b.support) (t : R) :
    weightCompanionMap P b O hclosed hmin φ (weightCompanionY P b O hclosed hmin R i t) =
      weightCompanionY P b O hclosed hmin S i (φ t) :=
  Subtype.ext (weightCompanionAmbientMap_Y P b O hclosed hmin φ i t)

theorem weightCompanionMap_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (weightCompanionMap P b O hclosed hmin φ) := by
  intro g h he
  apply Subtype.ext
  apply Prod.ext
  · apply adjointMap_injective P b φ hφ
    exact congrArg (fun z : WeightCompanion P b O hclosed hmin S => z.val.1) he
  · funext a
    apply Units.ext
    ext μ ν
    apply hφ
    exact congrArg (fun z : WeightCompanion P b O hclosed hmin S => (z.val.2 a).val μ ν) he

/-- Naturality of restriction to the actual adjoint summand. -/
theorem weightCompanionMap_rho (φ : R →+* S) :
    (weightCompanionRho P b O hclosed hmin S).comp (weightCompanionMap P b O hclosed hmin φ) =
      (adjointMap P b φ).comp (weightCompanionRho P b O hclosed hmin R) := by
  ext g
  rfl

@[simp] theorem weightCompanionMap_id :
    weightCompanionMap P b O hclosed hmin (RingHom.id R) = MonoidHom.id _ := by
  ext g : 1
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun f => f g.val.1) (adjointMap_id P b (R := R))
  · funext a
    apply Units.ext
    rfl

theorem weightCompanionMap_comp {T : Type*} [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    weightCompanionMap P b O hclosed hmin (ψ.comp φ) =
      (weightCompanionMap P b O hclosed hmin ψ).comp (weightCompanionMap P b O hclosed hmin φ) := by
  ext g : 1
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun f => f g.val.1) (adjointMap_comp P b φ ψ)
  · funext a
    apply Units.ext
    rfl

end Atlas.Chevalley
