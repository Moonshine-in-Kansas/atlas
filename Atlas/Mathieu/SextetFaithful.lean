import Atlas.Mathieu.Mathieu24Simplicity

noncomputable section
namespace Atlas.Codes

def mathieuSextetRepresentation : Mathieu24CodeModel →* Equiv.Perm UnorderedSextet :=
  MulAction.toPermHom _ _

theorem mathieuSextetRepresentation_injective :
    Function.Injective mathieuSextetRepresentation := by
  letI : IsSimpleGroup Mathieu24CodeModel := mathieu24_simple
  rcases (inferInstance : mathieuSextetRepresentation.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact (MonoidHom.ker_eq_bot_iff _).mp hb
  · have he (g : Mathieu24CodeModel) : mathieuSextetRepresentation g = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [ht]
      trivial
    have hs (S : UnorderedSextet) : S = distinguishedUnorderedSextet := by
      obtain ⟨g,hg⟩ := sextet_from_distinguished S
      have hh := congrArg (fun p : Equiv.Perm UnorderedSextet => p distinguishedUnorderedSextet) (he g)
      change g • distinguishedUnorderedSextet = distinguishedUnorderedSextet at hh
      exact hg.symm.trans hh
    letI : Subsingleton UnorderedSextet := ⟨fun S T => (hs S).trans (hs T).symm⟩
    have hc := Nat.card_of_subsingleton distinguishedUnorderedSextet
    rw [unordered_sextets_card] at hc
    omega

theorem mathieu_eq_one_of_fixes_sextets (g : Mathieu24CodeModel)
    (hg : ∀ S : UnorderedSextet, g • S = S) : g = 1 := by
  apply mathieuSextetRepresentation_injective
  apply Equiv.ext; intro S
  change g • S = (1 : Mathieu24CodeModel) • S
  simpa using hg S

end Atlas.Codes
