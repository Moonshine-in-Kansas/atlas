import Atlas.Fischer.OctadShortenedCode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Conway
open scoped BigOperators

abbrev OctadExterior (O : Octad) := {i : Omega // i ∉ O.val}

theorem octadExterior_card (O : Octad) : Nat.card (OctadExterior O) = 16 := by
  classical
  have e : OctadExterior O ≃ {i : Omega // i ∈ O.valᶜ} :=
    Equiv.subtypeEquivRight (fun i => (Finset.mem_compl).symm)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  rw [Fintype.card_coe, Finset.card_compl, octad_size O.val O.prop]
  norm_num [Omega, HexIndex, Tetrad]

noncomputable instance (O : Octad) : Nonempty (OctadExterior O) :=
  Finite.card_pos_iff.mp (by rw [octadExterior_card]; decide)

def octadEvaluation (O : Octad) (i : OctadExterior O) :
    Module.Dual Bit (octadShortenedCode O) where
  toFun c := c.val.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem octadEvaluation_one (O : Octad) (i : OctadExterior O) :
    octadEvaluation O i (octadShortenedOne O) = 1 := by
  change (octadComplementWord O).val i.val = 1
  simp [octadComplementWord_apply, i.prop]

theorem octadEvaluation_injective (O : Octad) : Function.Injective (octadEvaluation O) := by
  classical
  intro p q hpq
  by_contra hn
  have hpqv : p.val ≠ q.val := fun h => hn (Subtype.ext h)
  let J : Finset Omega := {p.val,q.val}
  have hJ : J.card ≤ 2 := by simp [J, hpqv]
  have hOJ : Disjoint O.val J := by
    apply Finset.disjoint_left.mpr
    intro i hi hij
    rcases Finset.mem_insert.mp hij with rfl | hij
    · exact p.prop hi
    · have h := Finset.mem_singleton.mp hij
      exact q.prop (h ▸ hi)
  let w : BinaryWord := fun i => if i = q.val then 1 else 0
  have hw (i : Omega) (hi : i ∈ O.val) : w i = 0 := by
    simp [w, show i ≠ q.val from fun h => q.prop (h ▸ hi)]
  obtain ⟨c,hc⟩ := golay_octad_exterior_restriction O.val J O.prop hJ hOJ w
    (Finset.sum_eq_zero hw)
  have hcm : c ∈ octadShortenedCode O := by
    rw [mem_octadShortenedCode]
    intro i hi
    exact (hc i (Finset.mem_union_left _ hi)).trans (hw i hi)
  have he := LinearMap.congr_fun hpq ⟨c,hcm⟩
  change c.val p.val = c.val q.val at he
  rw [hc p.val (by simp [J]), hc q.val (by simp [J])] at he
  simp [w, hpqv] at he

def octadDualConstant (O : Octad) :
    Module.Dual Bit (Module.Dual Bit (octadShortenedCode O)) :=
  LinearMap.applyₗ' Bit (octadShortenedOne O)

abbrev OctadAffineHyperplane (O : Octad) :=
  {l : Module.Dual Bit (octadShortenedCode O) // octadDualConstant O l = 1}

theorem octadDualConstant_surjective (O : Octad) : Function.Surjective (octadDualConstant O) := by
  intro b
  let i : OctadExterior O := Classical.arbitrary _
  refine ⟨b • octadEvaluation O i, ?_⟩
  change b * octadEvaluation O i (octadShortenedOne O) = b
  rw [octadEvaluation_one, mul_one]

theorem octadDualConstant_kernel_finrank (O : Octad) :
    Module.finrank Bit (octadDualConstant O).ker = 4 := by
  have h := (octadDualConstant O).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (octadDualConstant_surjective O), finrank_top,
    Module.finrank_self, Subspace.dual_finrank_eq, octadShortenedCode_finrank] at h
  omega

theorem octadAffineHyperplane_card (O : Octad) : Nat.card (OctadAffineHyperplane O) = 16 := by
  have h := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective
    (f := (octadDualConstant O).toAddMonoidHom) (octadDualConstant_surjective O) 1)
  change Nat.card (OctadAffineHyperplane O) = Nat.card (octadDualConstant O).ker at h
  rw [h, Module.natCard_eq_pow_finrank (K := Bit), octadDualConstant_kernel_finrank]
  simp [Bit]

/-- Actual coordinate evaluations, onto the affine hyperplane in the dual. -/
def octadAffineEvaluation (O : Octad) (i : OctadExterior O) : OctadAffineHyperplane O :=
  ⟨octadEvaluation O i, octadEvaluation_one O i⟩

theorem octadAffineEvaluation_bijective (O : Octad) : Function.Bijective (octadAffineEvaluation O) := by
  letI : Finite (OctadAffineHyperplane O) := Nat.finite_of_card_ne_zero (by
    rw [octadAffineHyperplane_card]; decide)
  have hi : Function.Injective (octadAffineEvaluation O) := by
    intro i j h
    exact octadEvaluation_injective O (congrArg Subtype.val h)
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨hi, (octadExterior_card O).trans (octadAffineHyperplane_card O).symm⟩

noncomputable def octadAffineEvaluationEquiv (O : Octad) :
    OctadExterior O ≃ OctadAffineHyperplane O :=
  Equiv.ofBijective _ (octadAffineEvaluation_bijective O)

/-- The comparison identifies every actual shortened word with evaluation on
its actual affine dual hyperplane, rather than merely comparing weight lists. -/
theorem octadAffineEvaluation_word (O : Octad) (c : octadShortenedCode O)
    (i : OctadExterior O) : (octadAffineEvaluationEquiv O i).val c = c.val.val i.val := rfl

end Atlas.Fischer
