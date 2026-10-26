import Atlas.LinearGroups.ReeF4.ElementaryDerived

/-! Perfectness of the actual locally generated subgroup, by commutators inside
that subgroup. Equality with the full intrinsic model is not asserted. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private abbrev E {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) := elementarySubgroup hcard

private def eShort {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (a b : F) : E hcard :=
  ⟨shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b)),shortRoot_mem_elementary hcard a b⟩

private def eLong {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : Multiplicative F →* E hcard where
  toFun a := ⟨modelLongSL2RootHom hcard a,longRoot_mem_elementary hcard a.toAdd⟩
  map_one' := by apply Subtype.ext; exact map_one (modelLongSL2RootHom hcard)
  map_mul' a b := by apply Subtype.ext; exact map_mul (modelLongSL2RootHom hcard) a b

private def eTorus {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : Fˣ × Fˣ →* E hcard where
  toFun p := ⟨torusModelHom hcard p,torus_mem_elementary hcard p.1 p.2⟩
  map_one' := by apply Subtype.ext; exact map_one (torusModelHom hcard)
  map_mul' a b := by apply Subtype.ext; exact map_mul (torusModelHom hcard) a b

private def eRho {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : E hcard :=
  ⟨weylRhoModel m,weylRho_mem_elementary hcard⟩
private def eSigma {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : E hcard :=
  ⟨weylSigmaModel m,weylSigma_mem_elementary hcard⟩
private def eLongest {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : E hcard :=
  (eRho hcard * eSigma hcard)^4

private theorem eShort_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    (eShort hcard a b).val = shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b)) := rfl
private theorem eLong_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (a : Multiplicative F) :
    (eLong hcard a).val = modelLongSL2RootHom hcard a := rfl
private theorem eTorus_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (p : Fˣ × Fˣ) :
    (eTorus hcard p).val = torusModelHom hcard p := rfl
private theorem eRho_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (eRho hcard).val = weylRhoModel m := rfl
private theorem eSigma_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (eSigma hcard).val = weylSigmaModel m := rfl
private theorem eLongest_val {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (eLongest hcard).val = weylLongestModel m := by
  apply Subtype.ext
  rfl

private theorem exists_unit_ne_one {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) :
    ∃ u : Fˣ, u ≠ 1 := by
  by_contra hn
  push_neg at hn
  have hs : Subsingleton Fˣ := ⟨fun u v => (hn u).trans (hn v).symm⟩
  have hc : Nat.card Fˣ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs,⟨1⟩⟩
  rw [Nat.card_units] at hc
  have hq := SuzukiFamily.card_ge_eight hcard hm
  omega

private theorem eShort_mem_derived {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) (a b : F) :
    eShort hcard a b ∈ commutator (E hcard) := by
  obtain ⟨u,hu⟩ := exists_unit_ne_one hcard hm
  have huF : (u : F) ≠ 1 := by intro h; exact hu (Units.ext h)
  have hnF : (u : F)*theta F m (u : F) ≠ 1 := by
    intro h
    apply hu
    apply (thetaNormEquiv hcard).injective
    apply Units.ext
    change (u : F)*theta F m (u : F) = (1:F)*theta F m 1
    simpa only [map_one,one_mul] using h
  let U := eShort hcard
  let t := eTorus hcard (u*thetaUnits m u,1)
  have hmul (c d e f : F) : U c d * U e f = U (c+e) (d+f+theta F m c*e) := by
    apply Subtype.ext
    apply Subtype.ext
    exact shortRootPairEquiv_mul m hcard c d e f
  have hinv (c d : F) : (U c d)⁻¹ = U c (d+c*theta F m c) := by
    apply Subtype.ext
    apply Subtype.ext
    exact shortRootPairEquiv_inv m hcard c d
  have hscale (c d : F) : t⁻¹ * U c d * t = U ((u:F)*c) ((u:F)*theta F m (u:F)*d) := by
    apply Subtype.ext
    apply Subtype.ext
    change (torusEquiv m (u*thetaUnits m u) 1)⁻¹ * shortRootPairEquiv m hcard c d *
      torusEquiv m (u*thetaUnits m u) 1 = _
    rw [torusEquiv_normalizes_shortRootPair,shortRootTorusScale_norm_one]
    rfl
  exact Atlas.twistedRoot_mem_commutator_of_scaling (theta F m).toRingHom U
    hmul hinv t (u:F) huF hnF hscale a b

private theorem eLong_mem_derived {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) (u : F) :
    eLong hcard (Multiplicative.ofAdd u) ∈ commutator (E hcard) := by
  obtain ⟨a,ha⟩ := exists_unit_ne_one hcard hm
  have hsq : (a:F)^2 ≠ 1 := by
    intro h
    apply ha
    apply Units.ext
    apply (frobeniusEquiv F 2).injective
    change (a:F)^2 = (1:F)^2
    simpa using h
  let cscale : F := (a:F)^2
  have hn : cscale-1 ≠ 0 := sub_ne_zero.mpr hsq
  let U : F → E hcard := fun v => eLong hcard (Multiplicative.ofAdd v)
  let t := eTorus hcard (a,a⁻¹)
  have hmul (v w : F) : U v * U w = U (v+w) :=
    (map_mul (eLong hcard) (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)).symm
  have hinv (v : F) : (U v)⁻¹ = U (-v) :=
    (map_inv (eLong hcard) (Multiplicative.ofAdd v)).symm
  have hscale (v : F) : t * U v * t⁻¹ = U (cscale*v) := by
    apply Subtype.ext
    apply Subtype.ext
    exact longSL2Parameter_torus_conjugate m a v
  have hc (v : F) : ⁅t,U v⁆ = U ((cscale-1)*v) := by
    rw [commutatorElement_def,hscale,hinv,hmul]
    congr 1
    ring
  have hv : (cscale-1)*(u/(cscale-1)) = u := by field_simp [hn]
  have h : ⁅t,U (u/(cscale-1))⁆ ∈ commutator (E hcard) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rwa [hc,hv] at h

private theorem eRho_inv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (eRho hcard)⁻¹ = eRho hcard := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv,eRho_val]
  exact weylRhoModel_inv m
private theorem eSigma_inv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (eSigma hcard)⁻¹ = eSigma hcard := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv,eSigma_val]
  exact weylSigmaModel_inv m

private theorem eRho_mem_derived {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) : eRho hcard ∈ commutator (E hcard) := by
  have hw : (eShort hcard 1 0)⁻¹ * (eRho hcard * eShort hcard 0 1 * eRho hcard) *
      (eShort hcard 1 1)⁻¹ = eRho hcard := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,eShort_val,eRho_val]
    exact weylRhoModel_root_word hcard
  have hc := (inferInstance : (commutator (E hcard)).Normal).conj_mem _
    (eShort_mem_derived hcard hm 0 1) (eRho hcard)
  rw [eRho_inv] at hc
  rw [←hw]
  exact (commutator (E hcard)).mul_mem
    ((commutator (E hcard)).mul_mem ((commutator (E hcard)).inv_mem (eShort_mem_derived hcard hm 1 0)) hc)
    ((commutator (E hcard)).inv_mem (eShort_mem_derived hcard hm 1 1))

private theorem eSigma_mem_derived {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) : eSigma hcard ∈ commutator (E hcard) := by
  let U := eLong hcard (Multiplicative.ofAdd (1:F))
  have hw : U * (eSigma hcard * U * eSigma hcard) * U = eSigma hcard := by
    apply Subtype.ext
    simp only [U,Subgroup.coe_mul,eLong_val,eSigma_val]
    exact weylSigmaModel_root_word hcard
  have hu := eLong_mem_derived hcard hm (1:F)
  have hc := (inferInstance : (commutator (E hcard)).Normal).conj_mem _ hu (eSigma hcard)
  rw [eSigma_inv] at hc
  rw [←hw]
  exact (commutator (E hcard)).mul_mem ((commutator (E hcard)).mul_mem hu hc) hu

private theorem eTorus_mem_derived {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) : eTorus hcard (a,b) ∈ commutator (E hcard) := by
  have hex (a : Fˣ) : ∃ u : Fˣ, u^2=a := by
    obtain ⟨u,hu⟩ := (Units.mapEquiv (frobeniusEquiv F 2).toMulEquiv).surjective a
    refine ⟨u,?_⟩
    apply Units.ext
    have h := congrArg (fun z : Fˣ => (z:F)) hu
    change (u:F)^2 = (a:F) at h
    exact h
  obtain ⟨u,hu⟩ := hex a
  obtain ⟨v,hv⟩ := hex b
  have hc : ⁅eTorus hcard (u,v),eLongest hcard⁆ = (eTorus hcard (u,v))^2 := by
    rw [commutatorElement_def]
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,Subgroup.coe_pow,eTorus_val,eLongest_val]
    simpa only [commutatorElement_def] using torusModelHom_commutator_longest hcard u v
  have h : ⁅eTorus hcard (u,v),eLongest hcard⁆ ∈ commutator (E hcard) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [hc,←map_pow] at h
  have hp : (u,v)^2=(a,b) := Prod.ext hu hv
  rwa [hp] at h

/-- Actual perfectness of the locally generated subgroup; no equality with Model
is a premise or conclusion. -/
theorem elementarySubgroup_isPerfect {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) :
    Group.IsPerfect (elementarySubgroup hcard) := by
  let D : Subgroup (Model F m) := (commutator (E hcard)).map (E hcard).subtype
  have hE : E hcard ≤ D := by
    apply sup_le
    · rintro _ ⟨g,rfl⟩
      obtain ⟨⟨a,b⟩,rfl⟩ := (shortRootParameters m hcard).surjective g
      exact ⟨eShort hcard a b,eShort_mem_derived hcard hm a b,rfl⟩
    · apply sup_le
      · rintro _ ⟨u,rfl⟩
        exact ⟨eLong hcard u,eLong_mem_derived hcard hm u.toAdd,rfl⟩
      · apply sup_le
        · rintro _ ⟨⟨a,b⟩,rfl⟩
          exact ⟨eTorus hcard (a,b),eTorus_mem_derived hcard a b,rfl⟩
        · apply (Subgroup.closure_le _).mpr
          intro g hg
          simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl
          · exact ⟨eRho hcard,eRho_mem_derived hcard hm,rfl⟩
          · exact ⟨eSigma hcard,eSigma_mem_derived hcard hm,rfl⟩
  constructor
  apply top_unique
  intro e _
  obtain ⟨k,hk,he⟩ := hE e.property
  have hke : k=e := Subtype.ext he
  change k ∈ commutator (E hcard) at hk
  rw [hke] at hk
  exact hk

end Atlas.ReeF4
