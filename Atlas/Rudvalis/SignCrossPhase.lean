import Atlas.Rudvalis.CoordinateFramePointwiseKernel

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem code_sign_patterns (g : codeGroup) (hg : g.val.right=1) :
    g.val.left.toAdd∈signPatterns := by
  have hk : g∈codePermutationHom.ker := (codePermutationHom_kernel g).mpr hg
  exact (codeSignKernelEquiv ⟨g,hk⟩).toAdd.prop

theorem code_sign_square (g : codeGroup) (hg : g.val.right=1) : g*g=1 := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (g.val*g.val).left.toAdd=0
    funext i
    change g.val.left.toAdd i+g.val.left.toAdd (g.val.right.symm i)=0
    rw [hg]
    exact Atlas.Codes.bit_self_add _
  · change g.val.right*g.val.right=1
    rw [hg,one_mul]

theorem gaussianUnit_square_one_cases (u : GaussianUnits) (hu : u*u=1) :
    u.val=1 ∨ u.val=codeI^2 := by
  classical
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp u.prop)
  have hn4 : n<4 := by simpa only [Finset.mem_range,codeI_order] using hn
  have h := congrArg Subtype.val hu
  change u.val*u.val=1 at h
  rw [←he,←pow_add] at h
  interval_cases n
  · left;rw [←he,pow_zero]
  · exact False.elim (codeI_pow_two_ne_one h)
  · right;exact he.symm
  · have he6 : codeI^(3+3)=codeI^2 := by
      rw [show 3+3=4+2 from rfl,pow_add,codeI_pow_four,one_mul]
    rw [he6] at h
    exact False.elim (codeI_pow_two_ne_one h)

/-- A pure sign change fixing a Gaussian cross acts on its representative by a real sign. -/
theorem code_sign_cross_phase (g : codeGroup) (hg : g.val.right=1) (v : MinimalShell)
    (hv : g • minimalCross v=minimalCross v) :
    g • v=v ∨ g • v=(codeI^2) • v := by
  obtain ⟨u,hu⟩ := (minimalCross_eq_iff (g • v) v).mp hv
  have hphase : (u*u) • v=v := by
    change (u.val*u.val) • v=v
    rw [mul_smul]
    change u.val • (u • v)=v
    rw [hu]
    rw [←mul_smul,←codeGroup_commute_gaussianUnits g u,mul_smul]
    change g • (u • v)=v
    rw [hu,←mul_smul,code_sign_square g hg,one_smul]
  have hs := gaussianUnits_free (u*u) v hphase
  rcases gaussianUnit_square_one_cases u hs with he|he
  · left
    change u.val • v=g • v at hu
    simpa only [he,one_smul] using hu.symm
  · right
    change u.val • v=g • v at hu
    rw [he] at hu
    exact hu.symm

end Atlas.Rudvalis
