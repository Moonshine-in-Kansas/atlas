import Atlas.Mathieu.Mathieu24FiveTransitive

noncomputable section
namespace Atlas.Codes

def distinctCoordinateTriple (i j k : Omega) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Fin 3 ↪ Omega := ⟨![i,j,k],by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all⟩

theorem mathieu24_ordered_triple_transport (i j a k l b : Omega)
    (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j)
    (hkl : k ≠ l) (hbk : b ≠ k) (hbl : b ≠ l) :
    ∃ g : Mathieu24CodeModel, g.val i = k ∧ g.val j = l ∧ g.val a = b := by
  let e := distinctCoordinateTriple i j a hij hai haj
  let f := distinctCoordinateTriple k l b hkl hbk hbl
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 3 := by
    letI := mathieu24_five_transitive
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 3 ≤ 5)
      (by norm_num [Omega,HexIndex])
  obtain ⟨g,hg⟩ := MulAction.isMultiplyPretransitive_iff.mp ht e f
  exact ⟨g,congrArg (fun e => e 0) hg,congrArg (fun e => e 1) hg,congrArg (fun e => e 2) hg⟩

end Atlas.Codes
