import Atlas.Lattices.LeechPermutations
import Atlas.Lattices.LeechSextetVectors
import Atlas.Mathieu.SextetAction

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def permutedTetradEquiv (σ : Equiv.Perm Omega) (T : Finset Omega) : permuteBlock σ T ≃ T where
  toFun i := ⟨σ.symm i.val,by
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp i.prop
    simpa [← he] using hj⟩
  invFun i := ⟨σ i.val,Finset.mem_image.mpr ⟨i.val,i.prop,rfl⟩⟩
  left_inv i := Subtype.ext (σ.apply_symm_apply i.val)
  right_inv i := Subtype.ext (σ.symm_apply_apply i.val)

theorem permutation_tetradFour (σ : Equiv.Perm Omega) (T : Finset Omega) (s : T → Bit) :
    integerPermutation σ (tetradFourVector T s) =
      tetradFourVector (permuteBlock σ T) (fun i => s (permutedTetradEquiv σ T i)) := by
  ext i
  change tetradFourVector T s (σ.symm i) = _
  simp only [tetradFourVector_apply,signedSupport]
  by_cases hi : i ∈ permuteBlock σ T
  · have ht : σ.symm i ∈ T := (permutedTetradEquiv σ T ⟨i,hi⟩).prop
    simp only [dif_pos hi,dif_pos ht,permutedTetradEquiv,Equiv.coe_fn_mk]
    rfl
  · have ht : σ.symm i ∉ T := by
      intro h
      exact hi (Finset.mem_image.mpr ⟨σ.symm i,h,σ.apply_symm_apply i⟩)
    simp [hi,ht]

theorem sextetCross_permutation_action (S : UnorderedSextet) (b : Bit) (g : Mathieu24CodeModel) :
    crossAction (permutationIsometry g) (sextetCross S b) = sextetCross (sextetAction g S) b := by
  let p := sextetBaseParameter S b
  let T : {T // T ∈ (sextetAction g S).val} :=
    ⟨permuteBlock g.val p.1.val,Finset.mem_image.mpr ⟨p.1.val,p.1.prop,rfl⟩⟩
  let t : ParitySigns T.val b := ⟨fun i => p.2.val (permutedTetradEquiv g.val p.1.val i),by
    rw [Equiv.sum_comp]; exact p.2.prop⟩
  let r : SextetVectorParameters (sextetAction g S) b := ⟨T,t⟩
  have hv : (permutationIsometry g).val (sextetLatticeVector S b p) =
      sextetLatticeVector (sextetAction g S) b r := by
    apply Subtype.ext
    exact permutation_tetradFour g.val p.1.val p.2.val
  apply Subtype.ext
  change leechModTwoRepresentation (permutationIsometry g) (leechReduction (sextetLatticeVector S b p)) = _
  rw [leechModTwoRepresentation_reduce,hv]
  exact sextetVector_class (sextetAction g S) b r (sextetBaseParameter (sextetAction g S) b)

end Atlas.Lattices
