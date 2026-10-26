import Atlas.Rudvalis.CrossOrthogonality
import Mathlib.Data.Set.Card

/-! Intrinsic configurations in the actual Gaussian minimal-cross geometry.
The dozen and canonical-base definitions impose no cardinality conclusions. -/
namespace Atlas.Rudvalis

/-- An unordered orthogonal pair. -/
def IsCouple (c : Set MinimalCross) : Prop :=
  c.ncard=2 ∧ c.Pairwise CrossOrthogonal

/-- A Gaussian frame. -/
def IsFrame (F : Set MinimalCross) : Prop :=
  F.ncard=28 ∧ F.Pairwise CrossOrthogonal

/-- External crosses orthogonal to all but one member are orthogonal to the last.
The external-point exclusion is part of the definition. -/
def QuartetClosure (Q : Set MinimalCross) : Prop :=
  ∀x : MinimalCross,x∉Q → ∀q∈Q,
    (∀y∈Q,y≠q → CrossOrthogonal x y) → CrossOrthogonal x q

/-- The intrinsic v33 quartet predicate, before any coordinate classification. -/
def IsQuartet (Q : Set MinimalCross) : Prop :=
  Q.ncard=4 ∧ Q.Pairwise CrossOrthogonal ∧ QuartetClosure Q

/-- Hermitian support of a cross on a set of crosses. -/
def crossSupportOn (Q : Set MinimalCross) (x : MinimalCross) : Set MinimalCross :=
  {q | q∈Q ∧ ¬CrossOrthogonal x q}

/-- The union of all quartets containing a specified set. No size is assumed. -/
def intrinsicDozen (c : Set MinimalCross) : Set MinimalCross :=
  {x | ∃Q : Set MinimalCross,IsQuartet Q ∧ c⊆Q ∧ x∈Q}

/-- The union of the dozens of the couples in Q. No frame condition is assumed. -/
def canonicalBase (Q : Set MinimalCross) : Set MinimalCross :=
  {x | ∃c : Set MinimalCross,IsCouple c ∧ c⊆Q ∧ x∈intrinsicDozen c}

def canonicalBases : Set (Set MinimalCross) :=
  {F | ∃Q : Set MinimalCross,IsQuartet Q ∧ canonicalBase Q=F}

theorem isCouple_finite {c : Set MinimalCross} (h : IsCouple c) : c.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [h.1]; decide)
theorem isQuartet_finite {Q : Set MinimalCross} (h : IsQuartet Q) : Q.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [h.1]; decide)
theorem isFrame_finite {F : Set MinimalCross} (h : IsFrame F) : F.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [h.1]; decide)

theorem quartetClosure_iff_no_unique_support (Q : Set MinimalCross) :
    QuartetClosure Q ↔ ∀x : MinimalCross,x∉Q → ¬∃!q,q∈Q ∧ ¬CrossOrthogonal x q := by
  classical
  constructor
  · intro h x hx hu
    obtain ⟨q,⟨hq,hnq⟩,hu⟩ := hu
    apply hnq (h x hx q hq ?_)
    intro y hy hne
    by_contra hn
    exact hne (hu y ⟨hy,hn⟩)
  · intro h x hx q hq hall
    by_contra hn
    apply h x hx
    refine ⟨q,⟨hq,hn⟩,?_⟩
    intro y hy
    by_contra hne
    exact hy.2 (hall y hy.1 hne)

theorem quartetClosure_iff_no_single_support (Q : Set MinimalCross) :
    QuartetClosure Q ↔ ∀x : MinimalCross,x∉Q → (crossSupportOn Q x).ncard≠1 := by
  rw [quartetClosure_iff_no_unique_support]
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro _
  change (¬∃!q,q∈Q ∧ ¬CrossOrthogonal x q) ↔ ¬((crossSupportOn Q x).ncard=1)
  rw [Set.ncard_eq_one]
  constructor
  · intro h ⟨q,hq⟩
    apply h
    refine ⟨q,?_,?_⟩
    · have : q∈crossSupportOn Q x := by rw [hq]; exact Set.mem_singleton q
      exact this
    · intro y hy
      have : y∈({q}:Set MinimalCross) := hq ▸ hy
      exact this
  · intro h ⟨q,hq,hu⟩
    apply h
    refine ⟨q,?_⟩
    ext y
    exact ⟨fun hy => hu y hy,fun hy => hy ▸ hq⟩

noncomputable def gaussianImage (g : gaussianLatticeGroup) (s : Set MinimalCross) : Set MinimalCross :=
  (fun x=>g • x) '' s

theorem gaussianImage_mem (g : gaussianLatticeGroup) (s : Set MinimalCross) (x : MinimalCross) :
    g • x∈gaussianImage g s ↔ x∈s :=
  by
    constructor
    · rintro ⟨y,hy,h⟩
      exact (MulAction.injective g h) ▸ hy
    · exact Set.mem_image_of_mem _


theorem gaussianImage_inv (g : gaussianLatticeGroup) (s : Set MinimalCross) :
    gaussianImage g⁻¹ (gaussianImage g s)=s := by
  ext x
  simp [gaussianImage,Set.mem_image]

theorem gaussianImage_subset_iff (g : gaussianLatticeGroup) (s t : Set MinimalCross) :
    gaussianImage g s⊆gaussianImage g t ↔ s⊆t :=
  Set.image_subset_image_iff (MulAction.injective g)

theorem gaussianImage_pairwise (g : gaussianLatticeGroup) (s : Set MinimalCross) :
    (gaussianImage g s).Pairwise CrossOrthogonal ↔ s.Pairwise CrossOrthogonal := by
  constructor
  · intro h x hx y hy hne
    exact (crossOrthogonal_gaussian g x y).mp
      (h (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy)
        (fun he => hne (MulAction.injective g he)))
  · intro h _ hx _ hy hne
    obtain ⟨x,hx,rfl⟩ := hx
    obtain ⟨y,hy,rfl⟩ := hy
    exact (crossOrthogonal_gaussian g x y).mpr (h hx hy (fun he=>hne (congrArg (fun z=>g • z) he)))

theorem gaussianImage_ncard (g : gaussianLatticeGroup) (s : Set MinimalCross) :
    (gaussianImage g s).ncard=s.ncard := Set.ncard_image_of_injective _ (MulAction.injective g)

theorem isCouple_gaussianImage (g : gaussianLatticeGroup) (c : Set MinimalCross) :
    IsCouple (gaussianImage g c) ↔ IsCouple c := by
  unfold IsCouple
  rw [gaussianImage_ncard,gaussianImage_pairwise]

theorem isFrame_gaussianImage (g : gaussianLatticeGroup) (F : Set MinimalCross) :
    IsFrame (gaussianImage g F) ↔ IsFrame F := by
  unfold IsFrame
  rw [gaussianImage_ncard,gaussianImage_pairwise]

theorem quartetClosure_gaussianImage_forward (g : gaussianLatticeGroup) (Q : Set MinimalCross)
    (h : QuartetClosure Q) : QuartetClosure (gaussianImage g Q) := by
  intro x hx q hq hall
  obtain ⟨x,rfl⟩ := MulAction.surjective g x
  obtain ⟨q,hq,rfl⟩ := hq
  apply (crossOrthogonal_gaussian g x q).mpr
  apply h x (fun hm=>hx (Set.mem_image_of_mem _ hm)) q hq
  intro y hy hne
  apply (crossOrthogonal_gaussian g x y).mp
  exact hall (g • y) (Set.mem_image_of_mem _ hy) (fun he=>hne (MulAction.injective g he))

theorem quartetClosure_gaussianImage (g : gaussianLatticeGroup) (Q : Set MinimalCross) :
    QuartetClosure (gaussianImage g Q) ↔ QuartetClosure Q := by
  constructor
  · intro h
    simpa only [gaussianImage_inv] using quartetClosure_gaussianImage_forward g⁻¹ _ h
  · exact quartetClosure_gaussianImage_forward g Q

theorem isQuartet_gaussianImage (g : gaussianLatticeGroup) (Q : Set MinimalCross) :
    IsQuartet (gaussianImage g Q) ↔ IsQuartet Q := by
  unfold IsQuartet
  rw [gaussianImage_ncard,gaussianImage_pairwise,quartetClosure_gaussianImage]

theorem gaussianImage_inv_right (g : gaussianLatticeGroup) (s : Set MinimalCross) :
    gaussianImage g (gaussianImage g⁻¹ s)=s := by
  simpa only [inv_inv] using gaussianImage_inv g⁻¹ s

theorem intrinsicDozen_gaussianImage_forward (g : gaussianLatticeGroup) (c : Set MinimalCross) :
    gaussianImage g (intrinsicDozen c)⊆intrinsicDozen (gaussianImage g c) := by
  rintro _ ⟨x,⟨Q,hQ,hc,hx⟩,rfl⟩
  exact ⟨gaussianImage g Q,(isQuartet_gaussianImage g Q).mpr hQ,
    Set.image_mono hc,Set.mem_image_of_mem _ hx⟩

theorem intrinsicDozen_gaussianImage (g : gaussianLatticeGroup) (c : Set MinimalCross) :
    gaussianImage g (intrinsicDozen c)=intrinsicDozen (gaussianImage g c) := by
  apply Set.Subset.antisymm (intrinsicDozen_gaussianImage_forward g c)
  have h := intrinsicDozen_gaussianImage_forward g⁻¹ (gaussianImage g c)
  rw [gaussianImage_inv] at h
  have hi := Set.image_mono (f:=fun x:MinimalCross=>g • x) h
  change gaussianImage g (gaussianImage g⁻¹ (intrinsicDozen (gaussianImage g c)))⊆
    gaussianImage g (intrinsicDozen c) at hi
  rw [gaussianImage_inv_right] at hi
  exact hi

theorem canonicalBase_gaussianImage_forward (g : gaussianLatticeGroup) (Q : Set MinimalCross) :
    gaussianImage g (canonicalBase Q)⊆canonicalBase (gaussianImage g Q) := by
  rintro _ ⟨x,⟨c,hc,hQ,hx⟩,rfl⟩
  refine ⟨gaussianImage g c,(isCouple_gaussianImage g c).mpr hc,Set.image_mono hQ,?_⟩
  rw [←intrinsicDozen_gaussianImage]
  exact Set.mem_image_of_mem _ hx

theorem canonicalBase_gaussianImage (g : gaussianLatticeGroup) (Q : Set MinimalCross) :
    gaussianImage g (canonicalBase Q)=canonicalBase (gaussianImage g Q) := by
  apply Set.Subset.antisymm (canonicalBase_gaussianImage_forward g Q)
  have h := canonicalBase_gaussianImage_forward g⁻¹ (gaussianImage g Q)
  rw [gaussianImage_inv] at h
  have hi := Set.image_mono (f:=fun x:MinimalCross=>g • x) h
  change gaussianImage g (gaussianImage g⁻¹ (canonicalBase (gaussianImage g Q)))⊆
    gaussianImage g (canonicalBase Q) at hi
  rw [gaussianImage_inv_right] at hi
  exact hi

theorem canonicalBases_gaussianImage (g : gaussianLatticeGroup) (F : Set MinimalCross) :
    gaussianImage g F∈canonicalBases ↔ F∈canonicalBases := by
  constructor
  · rintro ⟨Q,hQ,hF⟩
    refine ⟨gaussianImage g⁻¹ Q,(isQuartet_gaussianImage g⁻¹ Q).mpr hQ,?_⟩
    rw [←canonicalBase_gaussianImage,hF,gaussianImage_inv]
  · rintro ⟨Q,hQ,rfl⟩
    exact ⟨gaussianImage g Q,(isQuartet_gaussianImage g Q).mpr hQ,
      (canonicalBase_gaussianImage g Q).symm⟩

end Atlas.Rudvalis

