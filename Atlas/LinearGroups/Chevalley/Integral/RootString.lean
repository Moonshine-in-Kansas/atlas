import Atlas.LinearGroups.Chevalley.Integral.GeckDividedPowers
import Atlas.LinearGroups.Chevalley.Integral.DividedPowers

/-! Actual root-string embeddings and integral raising/lowering intertwining. -/

noncomputable section
open scoped Matrix
open RootPairing.GeckConstruction
namespace Atlas.Chevalley.Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringBottom_independent (i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    LinearIndependent ℤ ![P.root i, P.root (P.chainBotIdx i j)] := by
  rw [P.root_chainBotIdx]
  have he : P.root j - P.chainBotCoeff i j • P.root i =
      (-(P.chainBotCoeff i j : ℤ)) • P.root i + P.root j := by module
  rw [he, LinearIndependent.pair_add_smul_right_iff]
  exact h

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringBottom_coeff (i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    P.chainBotCoeff i (P.chainBotIdx i j) = 0 := by
  apply P.chainBotCoeff_eq_zero_iff.mpr
  right
  intro hex
  have hex' : P.root j - (P.chainBotCoeff i j + 1) • P.root i ∈ Set.range P.root := by
    convert hex using 1
    rw [P.root_chainBotIdx]
    module
  have := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mp hex'
  omega

/-- The actual length of the complete simple-root string through a root. -/
def geckStringLength (i j : ι) : ℕ := P.chainTopCoeff i (P.chainBotIdx i j)

omit [DecidableEq ι] in
 theorem geckStringLength_le_three (i j : ι) : geckStringLength P i j ≤ 3 := by
  have := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := P.chainBotIdx i j)
  dsimp only [geckStringLength]
  omega

/-- The root at position k from the actual bottom endpoint. -/
def geckStringIndex (i j : ι) (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j + 1)) : ι :=
  ((P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
    (geckStringBottom_independent P i j h)).mpr (Nat.lt_succ_iff.mp k.isLt)).choose

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringIndex_root (i j : ι) (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j + 1)) :
    P.root (geckStringIndex P i j h k) = P.root (P.chainBotIdx i j) + k.val • P.root i :=
  ((P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
    (geckStringBottom_independent P i j h)).mpr (Nat.lt_succ_iff.mp k.isLt)).choose_spec

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringIndex_independent (i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j + 1)) :
    LinearIndependent ℤ ![P.root i, P.root (geckStringIndex P i j h k)] :=
  shifted_root_independent P k.val (geckStringBottom_independent P i j h)
    (geckStringIndex_root P i j h k)

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringIndex_injective (i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    Function.Injective (geckStringIndex P i j h) := by
  intro k l hkl
  have he := congrArg P.root hkl
  rw [geckStringIndex_root, geckStringIndex_root] at he
  have hz : ((k.val : ℤ) - (l.val : ℤ)) • P.root i +
      (0 : ℤ) • P.root (P.chainBotIdx i j) = 0 := by
    have he' := add_left_cancel he
    simpa only [sub_smul, zero_smul, add_zero, sub_eq_zero, natCast_zsmul] using he'
  have hc := (LinearIndependent.pair_iff.mp (geckStringBottom_independent P i j h)) _ _ hz
  apply Fin.ext
  omega

omit [P.IsReduced] in
 theorem geckStringIndex_bot (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j + 1)) :
    P.chainBotCoeff i (geckStringIndex P i j h k) = k.val := by
  have hc := (raising_pow_root_and_bot P b i (P.chainBotIdx i j)
    (geckStringBottom_independent P i j h) k.val (geckStringIndex P i j h k)
    (geckStringIndex_root P i j h k)).1
  simpa only [geckStringBottom_coeff P i j h, zero_add] using hc

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringIndex_top (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j + 1)) :
    P.chainTopCoeff i (geckStringIndex P i j h k) = geckStringLength P i j - k.val := by
  have hi := geckStringIndex_independent P i j h k
  have hbot := geckStringBottom_independent P i j h
  have he (n : ℕ) : P.root (geckStringIndex P i j h k) + n • P.root i =
      P.root (P.chainBotIdx i j) + (k.val+n) • P.root i := by
    rw [geckStringIndex_root]
    module
  have hb : k.val + P.chainTopCoeff i (geckStringIndex P i j h k) ≤ geckStringLength P i j := by
    apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hbot).mp
    rw [← he]
    exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hi).mpr le_rfl
  have ht : geckStringLength P i j - k.val ≤ P.chainTopCoeff i (geckStringIndex P i j h k) := by
    apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hi).mp
    rw [he]
    apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hbot).mpr
    change k.val + (geckStringLength P i j - k.val) ≤ geckStringLength P i j
    omega
  omega

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckString_original_le (i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    P.chainBotCoeff i j ≤ geckStringLength P i j := by
  apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
    (geckStringBottom_independent P i j h)).mp
  refine ⟨j, ?_⟩
  rw [P.root_chainBotIdx]
  module

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringIndex_original (i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    geckStringIndex P i j h ⟨P.chainBotCoeff i j, Nat.lt_succ_of_le
      (geckString_original_le P i j h)⟩ = j := by
  apply P.root.injective
  rw [geckStringIndex_root, P.root_chainBotIdx]
  module

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringLength_eq (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    geckStringLength P i j = P.chainBotCoeff i j + P.chainTopCoeff i j := by
  have hl := geckString_original_le P i j h
  have ht := geckStringIndex_top P b i j h
    ⟨P.chainBotCoeff i j, Nat.lt_succ_of_le hl⟩
  rw [geckStringIndex_original] at ht
  dsimp only at ht
  omega

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringIndex_bottom (i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    geckStringIndex P i j h ⟨0, Nat.zero_lt_succ _⟩ = P.chainBotIdx i j := by
  apply P.root.injective
  simp only [geckStringIndex_root, zero_smul, add_zero]

omit [DecidableEq ι] [P.IsReduced] in
 theorem geckStringIndex_top_endpoint (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    geckStringIndex P i j h ⟨geckStringLength P i j, Nat.lt_succ_self _⟩ = P.chainTopIdx i j := by
  apply P.root.injective
  rw [geckStringIndex_root, P.root_chainTopIdx, P.root_chainBotIdx,
    geckStringLength_eq P b i j h]
  module

/-- The actual bottom-to-top root-basis map into the integral adjoint module. -/
def geckStringMap (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    StringLattice (geckStringLength P i j) →ₗ[ℤ] (b.support ⊕ ι → ℤ) :=
  Finsupp.linearCombination ℤ fun k => v b (geckStringIndex P i j h k)

omit [P.IsReduced] in
 theorem geckStringMap_single (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (k : Fin (geckStringLength P i j + 1)) (z : ℤ) :
    geckStringMap P b i j h (Finsupp.single k z) = z • v b (geckStringIndex P i j h k) := by
  simp [geckStringMap]

omit [P.IsReduced] in
 theorem geckStringMap_injective (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    Function.Injective (geckStringMap P b i j h) := by
  apply LinearIndependent.finsuppLinearCombination_injective
  have hi : Function.Injective (fun k : Fin (geckStringLength P i j+1) =>
      (Sum.inr (geckStringIndex P i j h k) : b.support ⊕ ι)) :=
    Sum.inr_injective.comp (geckStringIndex_injective P i j h)
  simpa only [Function.comp_def, Pi.basisFun_apply, v] using
    (Pi.basisFun ℤ (b.support ⊕ ι)).linearIndependent.comp _ hi

/-- The opposite integral string operator, with its bottom endpoint fixed to zero. -/
def stringLowering (n : ℕ) : Module.End ℤ (StringLattice n) :=
  Finsupp.linearCombination ℤ fun k : Fin (n+1) =>
    if k.val = 0 then 0 else ((n-k.val+1 : ℕ) : ℤ) • stringBasis n (k.val-1)

omit [P.IsReduced] in
 theorem stringLowering_single (n : ℕ) (k : Fin (n+1)) (z : ℤ) :
    stringLowering n (Finsupp.single k z) =
      z • (if k.val = 0 then 0 else ((n-k.val+1 : ℕ) : ℤ) • stringBasis n (k.val-1)) := by
  simp [stringLowering]

omit [P.IsReduced] in
 theorem lowering_root_zero_of_not_sub (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j])
    (hn : P.root j - P.root i ∉ Set.range P.root) :
    lowering P b i *ᵥ v b j = 0 := by
  have hj : j ≠ i.val := by
    intro he
    subst j
    have he := h.injective (show (![P.root i, P.root i] : Fin 2 → M) 0 =
      (![P.root i, P.root i] : Fin 2 → M) 1 from rfl)
    norm_num at he
  have hn' (k : ι) : P.root k ≠ P.root j - P.root i := fun hk => hn ⟨k,hk⟩
  ext (k | k)
  · simp [lowering, f, v, hj]
  · simp [lowering, f, v, hn']

omit [P.IsReduced] in
 theorem geckString_raising (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    (raising P b i).mulVecLin.comp (geckStringMap P b i j h) =
      (geckStringMap P b i j h).comp (stringRaising (geckStringLength P i j)) := by
  apply Finsupp.lhom_ext
  intro k z
  change raising P b i *ᵥ geckStringMap P b i j h (Finsupp.single k z) = _
  rw [geckStringMap_single, Matrix.mulVec_smul]
  change _ = geckStringMap P b i j h (stringRaising _ (Finsupp.single k z))
  have hs : Finsupp.single k z = z • Finsupp.single k (1 : ℤ) := by simp
  rw [hs, map_smul, map_smul]
  congr 1
  rw [← stringBasis_fin, stringRaising_basis, map_smul]
  by_cases hk : k.val+1 < geckStringLength P i j+1
  · let l : Fin (geckStringLength P i j+1) := ⟨k.val+1,hk⟩
    have hr : P.root (geckStringIndex P i j h l) = P.root i + P.root (geckStringIndex P i j h k) := by
      rw [geckStringIndex_root, geckStringIndex_root]
      dsimp only [l]
      module
    change _ = ((k.val : ℤ)+1) • geckStringMap P b i j h (stringBasis _ l.val)
    rw [stringBasis_fin, geckStringMap_single, one_smul]
    have he : raising P b i *ᵥ v b (geckStringIndex P i j h k) =
        (P.chainBotCoeff i (geckStringIndex P i j h k)+1 : ℤ) • v b (geckStringIndex P i j h l) :=
      e_lie_v_ne hr
    rw [he, geckStringIndex_bot]
  · rw [stringBasis, dite_eq_right hk, map_zero, smul_zero]
    apply raising_root_zero_of_not_add P b i _ (geckStringIndex_independent P i j h k)
    intro hex
    have ht := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
      (geckStringIndex_independent P i j h k)).mp (show
        P.root (geckStringIndex P i j h k) + 1 • P.root i ∈ Set.range P.root by
          simpa [add_comm] using hex)
    rw [geckStringIndex_top] at ht
    omega

omit [P.IsReduced] in
 theorem geckString_lowering (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    (lowering P b i).mulVecLin.comp (geckStringMap P b i j h) =
      (geckStringMap P b i j h).comp (stringLowering (geckStringLength P i j)) := by
  apply Finsupp.lhom_ext
  intro k z
  change lowering P b i *ᵥ geckStringMap P b i j h (Finsupp.single k z) = _
  rw [geckStringMap_single, Matrix.mulVec_smul]
  change _ = geckStringMap P b i j h (stringLowering _ (Finsupp.single k z))
  rw [stringLowering_single, map_smul]
  congr 1
  by_cases hk : k.val = 0
  · rw [ite_eq_left hk, map_zero]
    apply lowering_root_zero_of_not_sub P b i _ (geckStringIndex_independent P i j h k)
    intro hex
    have hb := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff
      (geckStringIndex_independent P i j h k)).mp (show
        P.root (geckStringIndex P i j h k) - 1 • P.root i ∈ Set.range P.root by
          simpa using hex)
    rw [geckStringIndex_bot, hk] at hb
    omega
  · rw [ite_eq_right hk, map_smul]
    have hl : k.val-1 < geckStringLength P i j+1 := by omega
    let l : Fin (geckStringLength P i j+1) := ⟨k.val-1,hl⟩
    change _ = (((geckStringLength P i j-k.val+1 : ℕ) : ℤ)) •
      geckStringMap P b i j h (stringBasis _ l.val)
    rw [stringBasis_fin, geckStringMap_single, one_smul]
    have hr : P.root (geckStringIndex P i j h k) = P.root (geckStringIndex P i j h l) + P.root i := by
      rw [geckStringIndex_root, geckStringIndex_root]
      dsimp only [l]
      have ha : k.val-1+1 = k.val := by omega
      nth_rw 1 [← ha]
      module
    have he : lowering P b i *ᵥ v b (geckStringIndex P i j h k) =
        (P.chainTopCoeff i (geckStringIndex P i j h k)+1 : ℤ) • v b (geckStringIndex P i j h l) :=
      f_lie_v_ne hr
    rw [he, geckStringIndex_top]
    norm_cast


omit [P.IsReduced] in
 theorem geckString_raising_pow (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (n : ℕ)
    (a : StringLattice (geckStringLength P i j)) :
    raising P b i ^ n *ᵥ geckStringMap P b i j h a =
      geckStringMap P b i j h ((stringRaising (geckStringLength P i j) ^ n) a) := by
  induction n with
  | zero => simp only [pow_zero, Matrix.one_mulVec, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', Module.End.mul_apply]
    exact LinearMap.congr_fun (geckString_raising P b i j h) _

/-- Integral factorial cancellation transfers the proved divided powers to the
actual Geck root string. No integrality or representation identity is assumed. -/
 theorem geckString_dividedPower (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (n : ℕ)
    (a : StringLattice (geckStringLength P i j)) :
    raisingDividedPower P b i n *ᵥ geckStringMap P b i j h a =
      geckStringMap P b i j h (stringDividedPower (geckStringLength P i j) n a) := by
  apply (smul_right_injective (M := (b.support ⊕ ι → ℤ))
    (by exact_mod_cast Nat.factorial_ne_zero n : (n.factorial : ℤ) ≠ 0))
  calc
    (n.factorial : ℤ) • (raisingDividedPower P b i n *ᵥ geckStringMap P b i j h a) =
        ((n.factorial : ℤ) • raisingDividedPower P b i n) *ᵥ geckStringMap P b i j h a :=
      (Matrix.smul_mulVec _ _ _).symm
    _ = raising P b i ^ n *ᵥ geckStringMap P b i j h a := by
      rw [factorial_smul_raisingDividedPower]
    _ = geckStringMap P b i j h ((stringRaising (geckStringLength P i j) ^ n) a) :=
      geckString_raising_pow P b i j h n a
    _ = _ := by
      rw [← factorial_smul_stringDividedPower]
      simp only [LinearMap.smul_apply, map_smul]

end Atlas.Chevalley.Integral
