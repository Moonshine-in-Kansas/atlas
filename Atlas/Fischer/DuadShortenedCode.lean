import Atlas.Fischer.OctadShortenedCode
import Atlas.Fischer.WittDuads

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Conway

/-- Actual Golay words vanishing on the marked duad. -/
def duadShortenedCode (p : Finset Omega) : Submodule Bit golay :=
  (golayRestriction p).ker

@[simp] theorem mem_duadShortenedCode (p : Finset Omega) (c : golay) :
    c ∈ duadShortenedCode p ↔ ∀ i ∈ p, c.val i=0 := by
  change golayRestriction p c=0 ↔ _
  constructor
  · intro h i hi
    exact congrFun h ⟨i,hi⟩
  · intro h
    funext i
    exact h i.val i.property

theorem duadShortenedCode_finrank (p : Finset Omega) (hp : p.card=2) :
    Module.finrank Bit (duadShortenedCode p)=10 := by
  have hs := golay_small_restriction_surjective p (by omega)
  have he := (golayRestriction p).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top,Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe,hp,golay_finrank] at he
  change Module.finrank Bit (golayRestriction p).ker=10
  omega

theorem duadShortenedCode_card (p : Finset Omega) (hp : p.card=2) :
    Nat.card (duadShortenedCode p)=1024 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),duadShortenedCode_finrank p hp]
  norm_num [Bit]

theorem octadShortenedCode_le_duad (p : Finset Omega) (F : Octad) (hp : p ⊆ F.val) :
    octadShortenedCode F ≤ duadShortenedCode p := by
  intro c hc
  rw [mem_duadShortenedCode]
  intro i hi
  exact (mem_octadShortenedCode F c).mp hc i (hp hi)

/-- The intended nonzero coordinate-label subset, without adding any sign data. -/
def DuadCoordinateWord (p : Finset Omega) :=
  {c : duadShortenedCode p // hammingNorm c.val.val=8 ∨ hammingNorm c.val.val=16}

end Atlas.Fischer
