import Atlas.Mathieu.TernaryMathieu11Full
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Codes

def ternaryTriads : Finset (Finset (Fin 12)) := Finset.univ.powersetCard 3

theorem ternaryTriads_card : ternaryTriads.card = 220 := by
  rw [ternaryTriads,Finset.card_powersetCard]
  decide

def ternaryTriadWord (s : Finset (Fin 12)) : TernaryWord :=
  fun i => if i ∈ s then 1 else 0

def ternaryTriadRelated (s t : Finset (Fin 12)) : Prop :=
  ∃ b : Bool, let w := ternaryTriadWord s - (if b then (1 : ZMod 3) else -1) • ternaryTriadWord t
    ternaryEncoder (ternaryDecoder w) = w

instance (s t : Finset (Fin 12)) : Decidable (ternaryTriadRelated s t) :=
  inferInstanceAs (Decidable (∃ b : Bool, _))

theorem ternaryTriadRelated_iff (s t : Finset (Fin 12)) :
    ternaryTriadRelated s t ↔ ∃ b : Bool,
      ternaryTriadWord s - (if b then (1 : ZMod 3) else -1) • ternaryTriadWord t ∈
        ternaryGolay := by
  simp only [ternaryTriadRelated,ternaryGolay_mem_iff_decode]

def ternaryTriadPartners (s : Finset (Fin 12)) : Finset (Finset (Fin 12)) :=
  ternaryTriads.filter (ternaryTriadRelated s)

def ternaryBaseTriad : Finset (Fin 12) := {0,1,2}

theorem ternaryBaseTriad_partners : ternaryTriadPartners ternaryBaseTriad =
    {{0,1,2},{3,4,5},{6,8,11},{7,9,10}} := by
  decide +kernel

theorem ternaryTriadWord_permute (σ : Equiv.Perm (Fin 12)) (s : Finset (Fin 12)) :
    ternaryTriadWord (s.map σ.toEmbedding) = fun i => ternaryTriadWord s (σ.symm i) := by
  funext i
  simp [ternaryTriadWord]

theorem ternaryTriadRelated_permute (g : TernaryPureAutomorphism)
    (s t : Finset (Fin 12)) (h : ternaryTriadRelated s t) :
    ternaryTriadRelated (s.map g.val.toEmbedding) (t.map g.val.toEmbedding) := by
  obtain ⟨b,hb⟩ := (ternaryTriadRelated_iff s t).mp h
  apply (ternaryTriadRelated_iff _ _).mpr
  refine ⟨b,?_⟩
  convert g.prop _ hb using 1
  ext i
  simp only [ternaryTriadWord_permute,Pi.sub_apply,Pi.smul_apply]

theorem ternaryTriads_transitive (s t : Finset (Fin 12)) (hs : s.card=3) (ht : t.card=3) :
    ∃ g : TernaryPureAutomorphism, s.map g.val.toEmbedding = t := by
  letI := ternaryPureAutomorphism_three_transitive
  let es : Fin 3 ↪ Fin 12 := (s.orderEmbOfFin hs).toEmbedding
  let et : Fin 3 ↪ Fin 12 := (t.orderEmbOfFin ht).toEmbedding
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq TernaryPureAutomorphism es et
  refine ⟨g,?_⟩
  have he (i : Fin 3) : g.val (es i) = et i := congrArg (fun e : Fin 3 ↪ Fin 12 => e i) hg
  have hsi : Finset.univ.map es = s := by
    simpa [es] using s.range_orderEmbOfFin hs
  have hti : Finset.univ.map et = t := by
    simpa [et] using t.range_orderEmbOfFin ht
  rw [← hsi,Finset.map_map,← hti]
  congr 1

theorem ternaryTriadRelated_permute_iff (g : TernaryPureAutomorphism)
    (s t : Finset (Fin 12)) :
    ternaryTriadRelated (s.map g.val.toEmbedding) (t.map g.val.toEmbedding) ↔
      ternaryTriadRelated s t := by
  constructor
  · intro h
    have hi := ternaryTriadRelated_permute g⁻¹ _ _ h
    have he (u : Finset (Fin 12)) :
        (u.map g.val.toEmbedding).map (g⁻¹).val.toEmbedding = u := by
      ext i
      simp only [Finset.mem_map_equiv]
      change g.val.symm (g.val i) ∈ u ↔ i ∈ u
      rw [Equiv.symm_apply_apply]
    simpa only [he] using hi
  · exact ternaryTriadRelated_permute g s t

theorem ternaryTriadPartners_permute (g : TernaryPureAutomorphism)
    (s : Finset (Fin 12)) :
    ternaryTriadPartners (s.map g.val.toEmbedding) =
      (ternaryTriadPartners s).image (fun t => t.map g.val.toEmbedding) := by
  ext t
  constructor
  · intro ht
    refine Finset.mem_image.mpr ⟨t.map g.val.symm.toEmbedding,?_,by
      ext i; simp only [Finset.mem_map_equiv,Equiv.symm_symm,Equiv.apply_symm_apply]⟩
    have h := Finset.mem_filter.mp ht
    apply Finset.mem_filter.mpr
    constructor
    · simpa [ternaryTriads,Finset.mem_powersetCard] using h.1
    · have hh := ternaryTriadRelated_permute g⁻¹ _ _ h.2
      have he : (s.map g.val.toEmbedding).map (g⁻¹).val.toEmbedding = s := by
        ext i
        simp only [Finset.mem_map_equiv]
        change g.val.symm (g.val i) ∈ s ↔ i ∈ s
        rw [Equiv.symm_apply_apply]
      rw [he] at hh
      exact hh
  · intro ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    have h := Finset.mem_filter.mp hu
    apply Finset.mem_filter.mpr
    constructor
    · simpa [ternaryTriads,Finset.mem_powersetCard] using h.1
    · exact ternaryTriadRelated_permute g s u h.2

theorem ternaryTriadPartners_card (s : Finset (Fin 12)) (hs : s.card=3) :
    (ternaryTriadPartners s).card = 4 := by
  obtain ⟨g,hg⟩ := ternaryTriads_transitive ternaryBaseTriad s (by decide) hs
  rw [← hg,ternaryTriadPartners_permute,Finset.card_image_of_injective]
  · rw [ternaryBaseTriad_partners]
    decide
  · intro t u he
    exact Finset.map_injective g.val.toEmbedding he

/-- Each triad determines four disjoint triads covering the twelve coordinates. -/
theorem ternaryTriadPartners_partition (s : Finset (Fin 12)) (hs : s.card=3)
    (i : Fin 12) : ∃! t, t ∈ ternaryTriadPartners s ∧ i ∈ t := by
  obtain ⟨g,hg⟩ := ternaryTriads_transitive ternaryBaseTriad s (by decide) hs
  have hb : ∀ j : Fin 12, ∃! t, t ∈ ternaryTriadPartners ternaryBaseTriad ∧ j ∈ t := by
    rw [ternaryBaseTriad_partners]
    intro j
    fin_cases j <;> simp [ExistsUnique,Finset.mem_insert,Finset.mem_singleton]
  obtain ⟨t,ht,hunique⟩ := hb (g.val.symm i)
  refine ⟨t.map g.val.toEmbedding,?_,?_⟩
  · constructor
    · rw [← hg,ternaryTriadPartners_permute]
      exact Finset.mem_image.mpr ⟨t,ht.1,rfl⟩
    · exact Finset.mem_map_equiv.mpr ht.2
  · intro u hu
    rw [← hg,ternaryTriadPartners_permute] at hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu.1
    have he := hunique v ⟨hv,Finset.mem_map_equiv.mp hu.2⟩
    rw [he]

/-- Code phases realize every exponent sum on every triad. -/
theorem ternaryTriad_sum_surjective (s : Finset (Fin 12)) (hs : s.card=3)
    (a : ZMod 3) : ∃ w : ternaryGolay, ∑ i ∈ s,w.val i = a := by
  obtain ⟨g,hg⟩ := ternaryTriads_transitive ternaryBaseTriad s (by decide) hs
  let w := ternaryEncoder (Pi.single 0 a)
  refine ⟨⟨fun i => w (g.val.symm i),g.prop w ⟨_,rfl⟩⟩,?_⟩
  rw [← hg,Finset.sum_map]
  simp only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
  simp [ternaryBaseTriad,w,ternaryEncoder,Pi.single_apply]

theorem ternaryTriadWord_not_mem (s : Finset (Fin 12)) (hs : s.card=3) :
    ternaryTriadWord s ∉ ternaryGolay := by
  have hw : ternaryWeight (ternaryTriadWord s) = 3 := by
    simp [ternaryWeight,ternaryTriadWord,hs]
  intro h
  have hn : ternaryTriadWord s ≠ 0 := by
    intro he
    rw [he] at hw
    norm_num [ternaryWeight] at hw
  have hm := ternaryGolay_minimum _ h hn
  omega

theorem ternaryTriad_sign_unique (s t : Finset (Fin 12)) (hs : s.card=3)
    (hminus : ternaryTriadWord s-ternaryTriadWord t ∈ ternaryGolay) :
    ternaryTriadWord s+ternaryTriadWord t ∉ ternaryGolay := by
  intro hplus
  have htwo : (2 : ZMod 3) • ternaryTriadWord s ∈ ternaryGolay := by
    convert ternaryGolay.add_mem hminus hplus using 1
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.sub_apply]
    ring
  have hfour := ternaryGolay.smul_mem (2 : ZMod 3) htwo
  have he : (2 : ZMod 3)*2=1 := by decide
  exact ternaryTriadWord_not_mem s hs (by simpa only [smul_smul,he,one_smul] using hfour)

end Atlas.Codes
