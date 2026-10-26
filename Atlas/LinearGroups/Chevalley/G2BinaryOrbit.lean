import Atlas.LinearGroups.Chevalley.G2BinaryAdjointMatrices
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! A literal63-vector invariant set in the actual binary adjoint module.
Only this set and four local generator actions are checked finitely. -/
noncomputable section
namespace Atlas.Chevalley.G2Binary
open Classical Integral G2Data
open scoped Matrix
set_option maxRecDepth 32768

/-- Bits are ordered u0,u1,v0,...,v11. -/
def pointCode (i : Fin 63) : ℕ :=
  (#[4, 21, 1124, 16, 1149, 10645, 1636, 32, 10512, 1592, 10555, 12676, 1511, 1629, 516, 544, 14608, 256, 1560, 11258, 14635, 291, 12420, 7662, 2019, 565, 12127, 512, 14485, 4352, 4112, 12190, 13250, 960, 15087, 4403, 15725, 807, 13566, 7722, 6184, 8155, 12273, 48, 16246, 15607, 4373, 4096, 14271, 964, 12998, 7144, 16045, 4658, 11636, 4870, 6200, 7706, 14297, 260, 7165, 13980, 4610][i.val]!)
def point (i : Fin 63) (a : I) : K :=
  ((pointCode i / 2 ^ (finSumFinEquiv a).val % 2 : ℕ) : K)
def encode (v : I → K) : ℕ :=
  ∑ a : Fin 14, (v (finSumFinEquiv.symm a)).val * 2 ^ a.val

theorem encode_point (i : Fin 63) : encode (point i) = pointCode i := by
  fin_cases i <;> decide +kernel

theorem point_injective : Function.Injective point := by
  have hc : Function.Injective pointCode := by
    intro i
    fin_cases i <;> decide +kernel
  intro i j h
  apply hc
  rw [← encode_point, ← encode_point, h]

def actionTable : Array (Array ℕ) :=
  #[#[0, 3, 6, 1, 9, 8, 2, 15, 5, 4, 19, 22, 24, 18, 14, 7, 28, 17, 13, 10, 34, 37, 11, 39, 12, 43, 31, 27, 16, 47, 46, 26, 50, 33, 20, 53, 52, 21, 48, 23, 51, 57, 54, 25, 45, 44, 30, 29, 38, 49, 32, 40, 36, 35, 42, 62, 60, 41, 61, 59, 56, 58, 55],
    #[1, 0, 4, 3, 2, 11, 13, 7, 16, 18, 20, 5, 23, 6, 25, 27, 8, 29, 9, 32, 10, 35, 28, 12, 41, 14, 44, 15, 22, 17, 30, 48, 19, 51, 50, 21, 54, 55, 45, 57, 40, 24, 58, 43, 26, 38, 59, 47, 31, 60, 34, 33, 61, 62, 36, 37, 56, 39, 42, 46, 49, 52, 53],
    #[2, 4, 0, 3, 1, 12, 14, 7, 17, 18, 21, 23, 5, 25, 6, 15, 29, 8, 9, 33, 35, 10, 38, 11, 42, 13, 37, 27, 45, 16, 30, 49, 51, 19, 52, 20, 46, 26, 22, 57, 56, 58, 24, 43, 55, 28, 36, 47, 60, 31, 61, 32, 34, 53, 59, 44, 40, 39, 41, 54, 48, 50, 62],
    #[0, 5, 7, 8, 10, 1, 15, 2, 3, 19, 4, 22, 21, 26, 14, 6, 30, 17, 31, 9, 36, 12, 11, 40, 37, 42, 13, 27, 46, 29, 16, 18, 50, 49, 52, 45, 20, 24, 56, 51, 23, 58, 25, 54, 53, 35, 28, 47, 60, 33, 32, 39, 34, 44, 43, 55, 38, 61, 41, 59, 48, 57, 62]]
def generatorLabel (g : Fin 4) (i : Fin 63) : Fin 63 :=
  Fin.ofNat 63 ((actionTable[g.val]!)[i.val]!)
def binaryRows : Array (Array ℕ) :=
  #[#[17, 2, 22, 8, 16, 32, 72, 2176, 4352, 544, 1024, 2048, 4096, 8192],
    #[5, 2, 4, 72, 22, 544, 64, 128, 256, 512, 1024, 2176, 4352, 8192],
    #[1, 130, 4, 137, 10512, 1124, 68, 128, 256, 512, 1028, 2304, 4096, 8448],
    #[1, 10, 1124, 8, 16, 32, 96, 137, 10512, 512, 1056, 2064, 4096, 8208]]
def generatorMatrix (g : Fin 4) (a c : I) : K :=
  ((((binaryRows[g.val]!)[(finSumFinEquiv a).val]!) /
    2 ^ (finSumFinEquiv c).val % 2 : ℕ) : K)

/- The opposition is a coordinate permutation. Use that fact symbolically before
checking the small literal matrix entries, instead of expanding a dense product. -/
private def oppositionIndex : I → I
  | Sum.inl a => Sum.inl a
  | Sum.inr a => Sum.inr (opposite a)

private theorem oppositionIndex_involutive (a : I) :
    oppositionIndex (oppositionIndex a) = a := by
  rcases a with a | a
  · rfl
  · fin_cases a <;> decide +kernel

private theorem W_entry (a c : I) :
    W K a c = if a = oppositionIndex c then 1 else 0 := by
  rcases a with a | a <;> rcases c with c | c <;>
    simp [W, Matrix.fromBlocks, Matrix.one_apply, oppositionIndex]

private theorem W_mul_entry (A : Matrix I I K) (a c : I) :
    (W K * A) a c = A (oppositionIndex a) c := by
  have he (j : I) : a = oppositionIndex j ↔ j = oppositionIndex a := by
    constructor
    · intro h
      have h' := congrArg oppositionIndex h
      simpa only [oppositionIndex_involutive] using h'.symm
    · intro h
      rw [h, oppositionIndex_involutive]
  simp only [Matrix.mul_apply, W_entry, he, ite_mul, one_mul, zero_mul]
  simp

private theorem mul_W_entry (A : Matrix I I K) (a c : I) :
    (A * W K) a c = A a (oppositionIndex c) := by
  simp only [Matrix.mul_apply, W_entry, mul_ite, mul_one, mul_zero]
  simp

private theorem W_mul_W_entry (A : Matrix I I K) (a c : I) :
    (W K * A * W K) a c = A (oppositionIndex a) (oppositionIndex c) := by
  rw [mul_W_entry, W_mul_entry]

set_option maxHeartbeats 1000000 in
theorem generatorMatrix_X (k : Fin 2) : X k 1 = generatorMatrix (![0,2] k) := by
  funext a c
  fin_cases k <;> rcases a with a | a <;> rcases c with c | c <;>
    fin_cases a <;> fin_cases c <;> decide +kernel

theorem generatorMatrix_Y (k : Fin 2) : Y k 1 = generatorMatrix (![1,3] k) := by
  rw [Y, generatorMatrix_X]
  funext a c
  refine (W_mul_W_entry (generatorMatrix (![0,2] k)) a c).trans ?_
  fin_cases k <;> rcases a with a | a <;> rcases c with c | c <;>
    fin_cases a <;> fin_cases c <;> decide +kernel

theorem generatorLabel_involutive (g : Fin 4) : Function.Involutive (generatorLabel g) := by
  intro i
  fin_cases g <;> fin_cases i <;> decide +kernel

theorem generator_action (g : Fin 4) (i : Fin 63) :
    generatorMatrix g *ᵥ point i = point (generatorLabel g i) := by
  fin_cases g <;> fin_cases i <;> decide +kernel

private theorem X_zero (k : Fin 2) : X k 0 = 1 := by
  rw [← reindex_exponential, raisingExponential_zero, map_one]
private theorem Y_zero (k : Fin 2) : Y k 0 = 1 := by
  rw [Y, X_zero, mul_one]
  have h := congrArg (reindex K) (oppositionOver_mul_self pairing base K)
  simpa only [map_mul, reindex_opposition, map_one] using h

def Preserves (A : Matrix I I K) : Prop := ∀ i : Fin 63, ∃ j : Fin 63, A *ᵥ point i = point j

private theorem preserves_X (k : Fin 2) (t : K) : Preserves (X k t) := by
  have ht : t = 0 ∨ t = 1 := (by decide : ∀ t : K, t = 0 ∨ t = 1) t
  rcases ht with rfl | rfl
  · intro i; exact ⟨i, by rw [X_zero, Matrix.one_mulVec]⟩
  · intro i
    fin_cases k
    · exact ⟨generatorLabel 0 i, by rw [generatorMatrix_X]; exact generator_action 0 i⟩
    · exact ⟨generatorLabel 2 i, by rw [generatorMatrix_X]; exact generator_action 2 i⟩

private theorem preserves_Y (k : Fin 2) (t : K) : Preserves (Y k t) := by
  have ht : t = 0 ∨ t = 1 := (by decide : ∀ t : K, t = 0 ∨ t = 1) t
  rcases ht with rfl | rfl
  · intro i; exact ⟨i, by rw [Y_zero, Matrix.one_mulVec]⟩
  · intro i
    fin_cases k
    · exact ⟨generatorLabel 1 i, by rw [generatorMatrix_Y]; exact generator_action 1 i⟩
    · exact ⟨generatorLabel 3 i, by rw [generatorMatrix_Y]; exact generator_action 3 i⟩

private theorem preserves_mul {A B : Matrix I I K} (hA : Preserves A) (hB : Preserves B) :
    Preserves (A * B) := by
  intro i
  obtain ⟨j,hj⟩ := hB i
  obtain ⟨k,hk⟩ := hA j
  exact ⟨k, by rw [← Matrix.mulVec_mulVec, hj, hk]⟩

private theorem preserves_inv (g : G) (hg : Preserves (matrixHom g)) :
    Preserves (matrixHom g⁻¹) := by
  choose f hf using hg
  have hi : Function.Injective f := by
    intro i j hij
    apply point_injective
    have h : matrixHom g *ᵥ point i = matrixHom g *ᵥ point j := by rw [hf, hf, hij]
    have h' := congrArg (fun v => matrixHom g⁻¹ *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
      Matrix.one_mulVec] using h'
  intro i
  obtain ⟨j,hj⟩ := (Finite.surjective_of_injective hi) i
  refine ⟨j, ?_⟩
  have he : matrixHom g *ᵥ point j = point i := (hf j).trans (congrArg point hj)
  rw [← he, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem preserves_actual (g : G) : Preserves (matrixHom g) := by
  apply adjoint_induction pairing base K (C := fun h => Preserves (matrixHom h))
  · intro i t
    obtain ⟨k,rfl⟩ := baseIndexEquiv.surjective i
    rw [matrix_X]
    exact preserves_X k t
  · intro i t
    obtain ⟨k,rfl⟩ := baseIndexEquiv.surjective i
    rw [matrix_Y]
    exact preserves_Y k t
  · intro i
    exact ⟨i, by rw [map_one, Matrix.one_mulVec]⟩
  · intro a b ha hb
    rw [map_mul]
    exact preserves_mul ha hb
  · exact preserves_inv

def label (g : G) (i : Fin 63) : Fin 63 := (preserves_actual g i).choose

theorem label_spec (g : G) (i : Fin 63) :
    matrixHom g *ᵥ point i = point (label g i) := (preserves_actual g i).choose_spec

theorem label_one (i : Fin 63) : label 1 i = i := by
  apply point_injective
  rw [← label_spec, map_one, Matrix.one_mulVec]

theorem label_mul (g h : G) (i : Fin 63) : label (g*h) i = label g (label h i) := by
  apply point_injective
  rw [← label_spec, map_mul, ← Matrix.mulVec_mulVec, label_spec, label_spec]

def permutation (g : G) : Equiv.Perm (Fin 63) where
  toFun := label g
  invFun := label g⁻¹
  left_inv i := by rw [← label_mul, inv_mul_cancel, label_one]
  right_inv i := by rw [← label_mul, mul_inv_cancel, label_one]

def permutationHom : G →* Equiv.Perm (Fin 63) where
  toFun := permutation
  map_one' := by
    apply Equiv.ext
    intro i
    exact label_one i
  map_mul' g h := by
    apply Equiv.ext
    intro i
    exact label_mul g h i

def generatorPermutation (g : Fin 4) : Equiv.Perm (Fin 63) where
  toFun := generatorLabel g
  invFun := generatorLabel g
  left_inv := generatorLabel_involutive g
  right_inv := generatorLabel_involutive g

theorem short_permutation :
    permutationHom (adjointX pairing base K (baseIndexEquiv 1) 1) = generatorPermutation 2 := by
  apply Equiv.ext
  intro i
  change label (adjointX pairing base K (baseIndexEquiv 1) 1) i = generatorLabel 2 i
  apply point_injective
  rw [← label_spec, matrix_X, generatorMatrix_X]
  exact generator_action 2 i

theorem short_fixed_count :
    Fintype.card (Function.fixedPoints (generatorPermutation 2)) = 9 := by decide +kernel

theorem short_sign : Equiv.Perm.sign (generatorPermutation 2) = -1 := by
  have hsq : generatorPermutation 2 ^ 2 = 1 := by
    apply Equiv.ext
    intro i
    simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    change generatorLabel 2 (generatorLabel 2 i) = i
    exact generatorLabel_involutive 2 i
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, short_fixed_count]
  norm_num

def oddSign : G →* ℤˣ := Equiv.Perm.sign.comp permutationHom

theorem oddSign_short : oddSign (adjointX pairing base K (baseIndexEquiv 1) 1) = -1 := by
  change Equiv.Perm.sign (permutationHom (adjointX pairing base K (baseIndexEquiv 1) 1)) = -1
  rw [short_permutation, short_sign]

end Atlas.Chevalley.G2Binary
