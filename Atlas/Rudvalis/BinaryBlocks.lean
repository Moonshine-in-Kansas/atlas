import Atlas.Rudvalis.BinaryTranslations

/-! The seven coordinate blocks are intrinsic to the binary residue code. -/
namespace Atlas.Rudvalis

theorem binaryWord_weight_permute (w : BinaryWord) (g : Equiv.Perm Coordinate) :
    hammingNorm (w ∘ g) = hammingNorm w := by
  classical
  simp only [Atlas.Codes.hammingNorm_eq_sum, Function.comp_def]
  exact Equiv.sum_comp g (fun z => if w z = 0 then 0 else 1)

theorem binaryPermutation_row_image (g : binaryPermutationGroup) (p : Point) :
    ∃! q : Point, rowWord p ∘ (g.val⁻¹ : Equiv.Perm Coordinate) = rowWord q := by
  have hm : rowWord p ∘ (g.val⁻¹ : Equiv.Perm Coordinate) ∈ binaryResidue :=
    ((g⁻¹).prop (rowWord p)).mp (binaryResidue_row_word p 1)
  obtain ⟨q,hq⟩ := (binaryResidue_weight_eight_iff _ hm).mp
    (by rw [binaryWord_weight_permute,rowWord_weight])
  exact ⟨q,hq,fun r hr => rowWord_injective (hr.symm.trans hq)⟩

noncomputable def binaryRowImage (g : binaryPermutationGroup) (p : Point) : Point :=
  (binaryPermutation_row_image g p).exists.choose

theorem binaryRowImage_spec (g : binaryPermutationGroup) (p : Point) :
    rowWord p ∘ (g.val⁻¹ : Equiv.Perm Coordinate) = rowWord (binaryRowImage g p) :=
  (binaryPermutation_row_image g p).exists.choose_spec

theorem binaryRowImage_injective (g : binaryPermutationGroup) :
    Function.Injective (binaryRowImage g) := by
  intro p q h
  apply rowWord_injective
  funext z
  have he := (binaryRowImage_spec g p).trans
    ((congrArg rowWord h).trans (binaryRowImage_spec g q).symm)
  simpa using congrFun he (g.val z)

noncomputable def binaryBlockPermutation (g : binaryPermutationGroup) : Equiv.Perm Point :=
  Equiv.ofBijective (binaryRowImage g)
    ⟨binaryRowImage_injective g, Finite.surjective_of_injective (binaryRowImage_injective g)⟩

theorem binaryBlockPermutation_coordinates (g : binaryPermutationGroup) (z : Coordinate) :
    (g.val z).1 = binaryBlockPermutation g z.1 := by
  have he := congrFun (binaryRowImage_spec g z.1) (g.val z)
  have hv : rowWord (binaryRowImage g z.1) (g.val z) = 1 := by
    simpa [Function.comp_def,rowWord] using he.symm
  by_contra hn
  change (g.val z).1 ≠ binaryRowImage g z.1 at hn
  simp [rowWord,hn] at hv

noncomputable def binaryBlockHom : binaryPermutationGroup →* Equiv.Perm Point where
  toFun := binaryBlockPermutation
  map_one' := by
    apply Equiv.ext
    intro p
    exact (binaryBlockPermutation_coordinates 1 (p,0)).symm
  map_mul' g h := by
    apply Equiv.ext
    intro p
    have he := binaryBlockPermutation_coordinates (g*h) (p,0)
    have hg := binaryBlockPermutation_coordinates g (h.val (p,0))
    have hh := binaryBlockPermutation_coordinates h (p,0)
    exact he.symm.trans (hg.trans (congrArg (binaryBlockPermutation g) hh))

theorem coordinateTranslation_block_trivial (A : BinaryMatrix) :
    binaryBlockHom (coordinateTranslationHom (Multiplicative.ofAdd A)) = 1 := by
  apply Equiv.ext
  intro p
  exact (binaryBlockPermutation_coordinates
    (coordinateTranslationHom (Multiplicative.ofAdd A)) (p,0)).symm

end Atlas.Rudvalis
