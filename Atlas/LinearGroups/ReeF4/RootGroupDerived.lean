import Atlas.GroupTheory.TwistedRootCommutator
import Atlas.LinearGroups.ReeF4.RootGroupTorusNormalizer
import Atlas.LinearGroups.ReeF4.RootGroupModel

/-! The actual short-root subgroup lies in the derived subgroup of the full
intrinsic Ree model in every nonbinary admissible field. This is a local
containment theorem, not yet perfectness of the ambient group. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem shortRootModelParameter_mem_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) (a b : F) :
    shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b)) ∈
      commutator (Model F m) := by
  have hex : ∃ u : Fˣ, u ≠ 1 := by
    by_contra hn
    push_neg at hn
    have hs : Subsingleton Fˣ := ⟨fun u v => (hn u).trans (hn v).symm⟩
    have hc : Nat.card Fˣ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs,⟨1⟩⟩
    rw [Nat.card_units] at hc
    have hq := SuzukiFamily.card_ge_eight hcard hm
    omega
  obtain ⟨u,hu⟩ := hex
  have huF : (u : F) ≠ 1 := by
    intro h
    exact hu (Units.ext h)
  have hnF : (u : F)*theta F m (u : F) ≠ 1 := by
    intro h
    apply hu
    apply (thetaNormEquiv hcard).injective
    apply Units.ext
    change (u : F)*theta F m (u : F) = (1 : F)*theta F m 1
    simpa only [map_one,one_mul] using h
  let U : F → F → Model F m := fun c d =>
    shortRootModelEmbedding hcard (shortRootParameters m hcard (c,d))
  let t : Model F m := ⟨torusEquiv m (u*thetaUnits m u) 1,
    torusEquiv_mem_modelSubgroup hcard _ _⟩
  have hmul (c d e f : F) : U c d * U e f =
      U (c+e) (d+f+theta F m c*e) := by
    apply Subtype.ext
    exact shortRootPairEquiv_mul m hcard c d e f
  have hinv (c d : F) : (U c d)⁻¹ = U c (d+c*theta F m c) := by
    apply Subtype.ext
    exact shortRootPairEquiv_inv m hcard c d
  have hscale (c d : F) : t⁻¹ * U c d * t =
      U ((u : F)*c) ((u : F)*theta F m (u : F)*d) := by
    apply Subtype.ext
    change (torusEquiv m (u*thetaUnits m u) 1)⁻¹ *
        shortRootPairEquiv m hcard c d * torusEquiv m (u*thetaUnits m u) 1 = _
    rw [torusEquiv_normalizes_shortRootPair,shortRootTorusScale_norm_one]
    rfl
  exact Atlas.twistedRoot_mem_commutator_of_scaling (theta F m).toRingHom U
    hmul hinv t (u : F) huF hnF hscale a b

theorem shortRootModelEmbedding_range_le_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) :
    (shortRootModelEmbedding hcard).range ≤ commutator (Model F m) := by
  rintro _ ⟨g,rfl⟩
  obtain ⟨⟨a,b⟩,rfl⟩ := (shortRootParameters m hcard).surjective g
  exact shortRootModelParameter_mem_commutator hcard hm a b

end Atlas.ReeF4
