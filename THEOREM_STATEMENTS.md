# Principal compiled theorem statements

These signatures are copied verbatim from the source-bound 26 October compiled
audit, with implicit parameters and instances visible. See [verification status](AUDIT.md)
for the distinction between this cached-artifact audit and a fresh proof rebuild.

<a id="family-cyclic"></a>

## Cₚ

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Families.Cyclic.card : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    @Eq.{1} Nat (Nat.card.{0} (Atlas.Families.Cyclic.Model m)) (Atlas.Families.Cyclic.order m)
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Families.Cyclic.isSimpleGroup : ∀ (p : Nat),
  Atlas.Families.Cyclic.IsAdmissible p →
    @IsSimpleGroup.{0} (Atlas.Families.Cyclic.Model p)
      (@Multiplicative.group.{0} (ZMod p)
        (@AddGroupWithOne.toAddGroup.{0} (ZMod p)
          (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))
```

<a id="family-alternating"></a>

## Aₙ

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Families.Alternating.card_factorial : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    @Eq.{1} Nat (Nat.card.{0} (Atlas.Families.Alternating.Model n))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n.factorial
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Families.Alternating.isSimpleGroup : ∀ (n : Nat),
  Atlas.Families.Alternating.IsAdmissible n →
    @IsSimpleGroup.{0} (Atlas.Families.Alternating.Model n)
      (@Subgroup.toGroup.{0} (Equiv.Perm.{1} (Fin n)) (@Equiv.Perm.permGroup.{0} (Fin n))
        (@alternatingGroup.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)))
```

<a id="family-psl"></a>

## Aₙ(q)

Primary construction: Projective special-linear matrix model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.card_psl_factor.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] (n : Nat)
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] [Finite.{u_1 + 1} F],
  @Eq.{1} Nat
    (Nat.card.{u_1}
      (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
        (@Field.toCommRing.{u_1} F inst)))
    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (∏
          i ∈
            @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n,
          @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) i)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (n.gcd
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} F)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.psl_simple_iff.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    Iff
      (@IsSimpleGroup.{u_1}
        (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
          (@Field.toCommRing.{u_1} F inst))
        (@QuotientGroup.Quotient.group.{u_1}
          (@Matrix.SpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
            (@Field.toCommRing.{u_1} F inst))
          (@Matrix.SpecialLinearGroup.instGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
            (@Field.toCommRing.{u_1} F inst))
          (@Subgroup.center.{u_1}
            (@Matrix.SpecialLinearGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
              (@Field.toCommRing.{u_1} F inst))
            (@Matrix.SpecialLinearGroup.instGroup.{0, u_1} (Fin n) (instDecidableEqFin n) (Fin.fintype n) F
              (@Field.toCommRing.{u_1} F inst)))
          ⋯))
      (And
        (@Ne.{1} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat n (Nat.card.{u_1} F))
          (@Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@Ne.{1} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat n (Nat.card.{u_1} F))
          (@Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
```

### Chevalley root-operator model

Order: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.A_order.{u_1} : ∀ (r : Nat)
  (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) (K : Type u_1)
  [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.AFieldDomain.{u_1} r hr K inst →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (∏ d ∈ Finset.range r,
            @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        ((@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).gcd
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

Simple: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.A_simple.{u_1} : ∀ (r : Nat)
  (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) (K : Type u_1)
  [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.AGoodDomain.{u_1} r hr K inst →
    @IsSimpleGroup.{u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst)
      (@Atlas.Chevalley.Catalogue.AGroup.{u_1} r hr K inst)
```

[Lean isomorphism certificate](catalogue/ISOMORPHISMS.md#chevalley-a-to-legacy-v1) · [`Atlas.Chevalley.Catalogue.A_identification`](Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L24).

<a id="family-psu"></a>

## ²Aₙ(q)

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Unitary.card_psu_factor.{u_1,
    u_2} : ∀ {F : Type u_1} {K : Type u_2} [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))]
  (hdeg :
    @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (n : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @Eq.{1} Nat (Nat.card.{u_2} (@Atlas.Unitary.PSU.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 n hdeg))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (∏
            i ∈
              @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n,
            Atlas.Unitary.orderFactor (Nat.card.{u_1} F) i))
        (n.gcd
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Unitary.simple_of_good.{u_1,
    u_2} : ∀ {F : Type u_1} {K : Type u_2} [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))]
  (hdeg :
    @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  {n : Nat},
  Atlas.Unitary.Good n (Nat.card.{u_1} F) →
    @IsSimpleGroup.{u_2} (@Atlas.Unitary.PSU.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 n hdeg)
      (@QuotientGroup.Quotient.group.{u_2} (@Atlas.Unitary.SU.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 n hdeg)
        (@Atlas.Unitary.group_su.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 n hdeg)
        (@Subgroup.center.{u_2} (@Atlas.Unitary.SU.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 n hdeg)
          (@Atlas.Unitary.group_su.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 n hdeg))
        ⋯)
```

<a id="family-b"></a>

## Bₙ(q)

Primary construction: Quadratic-form model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Orthogonal.B_card_all_rank.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Orthogonal.B.{u_1} n F inst)) (Atlas.Orthogonal.B_order n (Nat.card.{u_1} F))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Orthogonal.B_simple_all_rank.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  Atlas.Orthogonal.B_good n (Nat.card.{u_1} F) →
    @IsSimpleGroup.{u_1} (@Atlas.Orthogonal.B.{u_1} n F inst)
      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, u_1} F (Atlas.Orthogonal.VectorB.{u_1} n F) inst
        (@Prod.instAddCommGroup.{u_1, u_1} (Atlas.Orthogonal.VectorD.{u_1} n F) F
          (@Pi.addCommGroup.{0, u_1} (Atlas.Orthogonal.Index n) (fun a ↦ F) fun i ↦
            @Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst)))
          (@Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
        (@Prod.instModule.{u_1, u_1, u_1} F (Atlas.Orthogonal.VectorD.{u_1} n F) F
          (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
          (@Pi.addCommMonoid.{0, u_1} (Atlas.Orthogonal.Index n) (fun a ↦ F) fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Semiring.toAddCommMonoid.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Atlas.Orthogonal.Index n) F F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Semiring.toModule.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
          (@Semiring.toModule.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@Atlas.Orthogonal.formB.{u_1} n F (@Field.toCommRing.{u_1} F inst)))
```

### Chevalley root-operator model

Order: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.B_order.{u_1} : ∀ (n : Nat)
  (hn :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.BFieldDomain.{u_1} n hn K inst →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (∏
            d ∈
              Finset.range
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
            @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

Simple: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.B_simple.{u_1} : ∀ (n : Nat)
  (hn :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.BGoodDomain.{u_1} n hn K inst →
    @IsSimpleGroup.{u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst)
      (@Atlas.Chevalley.Catalogue.BGroup.{u_1} n hn K inst)
```

[Lean isomorphism certificate](catalogue/ISOMORPHISMS.md#chevalley-b-to-legacy-v1) · [`Atlas.Chevalley.Catalogue.B_identification`](Atlas/LinearGroups/Chevalley/Catalogue/BIdentification.lean#L16).

<a id="family-suzuki"></a>

## ²B₂(q)

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.SuzukiFamily.card_group.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [inst_1 : Finite.{u_1 + 1} F]
  [inst_2 :
    @CharP.{u_1} F
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} F
        (@Ring.toAddGroupWithOne.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  (m : Nat),
  @Eq.{1} Nat (Nat.card.{u_1} F)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.SuzukiFamily.Group.{u_1} F inst inst_1 inst_2 m))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} F)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.SuzukiFamily.simple_of_large.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [inst_1 : Finite.{u_1 + 1} F]
  [inst_2 :
    @CharP.{u_1} F
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} F
        (@Ring.toAddGroupWithOne.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  (m : Nat),
  @Eq.{1} Nat (Nat.card.{u_1} F)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
      @IsSimpleGroup.{u_1} (@Atlas.SuzukiFamily.Group.{u_1} F inst inst_1 inst_2 m)
        (@Subgroup.toGroup.{u_1}
          (@Atlas.Symplectic.Sp.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) F
            (@Field.toCommRing.{u_1} F inst))
          (@SymplecticGroup.instGroupSubtypeMatrixSumMemSubmonoidSymplecticGroup.{0, u_1}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) F
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Field.toCommRing.{u_1} F inst))
          (@Atlas.SuzukiFamily.generated.{u_1} F inst inst_1 inst_2 m))
```

<a id="family-c"></a>

## Cₙ(q)

Primary construction: Symplectic matrix model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Symplectic.card_psp.{u_1} : ∀ {n : Nat} {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F],
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Symplectic.PSp.{u_1} n F (@Field.toCommRing.{u_1} F inst)))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (Atlas.Symplectic.orderNumerator n (Nat.card.{u_1} F))
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Symplectic.simple_of_good.{u_1} : ∀ {n : Nat} {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F],
  Atlas.Symplectic.Good n (Nat.card.{u_1} F) →
    @IsSimpleGroup.{u_1} (@Atlas.Symplectic.PSp.{u_1} n F (@Field.toCommRing.{u_1} F inst))
      (@QuotientGroup.Quotient.group.{u_1} (@Atlas.Symplectic.Sp.{u_1} n F (@Field.toCommRing.{u_1} F inst))
        (@SymplecticGroup.instGroupSubtypeMatrixSumMemSubmonoidSymplecticGroup.{0, u_1} (Fin n) F (instDecidableEqFin n)
          (Fin.fintype n) (@Field.toCommRing.{u_1} F inst))
        (@Subgroup.center.{u_1} (@Atlas.Symplectic.Sp.{u_1} n F (@Field.toCommRing.{u_1} F inst))
          (@SymplecticGroup.instGroupSubtypeMatrixSumMemSubmonoidSymplecticGroup.{0, u_1} (Fin n) F
            (instDecidableEqFin n) (Fin.fintype n) (@Field.toCommRing.{u_1} F inst)))
        ⋯)
```

### Chevalley root-operator model

Order: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.C_order.{u_1} : ∀ (n : Nat)
  (hn :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.CFieldDomain.{u_1} n hn K inst →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (∏
            d ∈
              Finset.range
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
            @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

Simple: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.C_simple.{u_1} : ∀ (n : Nat)
  (hn :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.CGoodDomain.{u_1} n hn K inst →
    @IsSimpleGroup.{u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst)
      (@Atlas.Chevalley.Catalogue.CGroup.{u_1} n hn K inst)
```

[Lean isomorphism certificate](catalogue/ISOMORPHISMS.md#chevalley-c-to-legacy-v1) · [`Atlas.Chevalley.Catalogue.C_identification`](Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L31).

<a id="family-d"></a>

## Dₙ(q)

Primary construction: Quadratic-form model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Orthogonal.DPlus_card.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Orthogonal.DPlus.{u_1} n F inst))
      (Atlas.Orthogonal.DPlus_order n (Nat.card.{u_1} F))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Orthogonal.DPlus_simple.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    @IsSimpleGroup.{u_1} (@Atlas.Orthogonal.DPlus.{u_1} n F inst)
      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, u_1} F (Atlas.Orthogonal.VectorD.{u_1} n F) inst
        (@Pi.addCommGroup.{0, u_1} (Atlas.Orthogonal.Index n) (fun a ↦ F) fun i ↦
          @Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst)))
        (@Pi.Function.module.{0, u_1, u_1} (Atlas.Orthogonal.Index n) F F
          (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
          (@Semiring.toAddCommMonoid.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Semiring.toModule.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@Atlas.Orthogonal.formD.{u_1} n F (@Field.toCommRing.{u_1} F inst)))
```

### Chevalley root-operator model

Order: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.D_order.{u_1} : ∀ (r : Nat)
  (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) r) (K : Type u_1)
  [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.DFieldDomain.{u_1} r hr K inst →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} K)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K) r)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (∏
            d ∈
              Finset.range
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
            @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} K) r)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

Simple: [compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.D_simple.{u_1} : ∀ (r : Nat)
  (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) r) (K : Type u_1)
  [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.DGoodDomain.{u_1} r hr K inst →
    @IsSimpleGroup.{u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst)
      (@Atlas.Chevalley.Catalogue.DGroup.{u_1} r hr K inst)
```

[Lean isomorphism certificate](catalogue/ISOMORPHISMS.md#chevalley-d-to-legacy-v1) · [`Atlas.Chevalley.Catalogue.D_identification`](Atlas/LinearGroups/Chevalley/Catalogue/DIdentification.lean#L16).

<a id="family-2d"></a>

## ²Dₙ(q)

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Orthogonal.Minus.family_order.{u_1,
    u_2} : ∀ {F : Type u_1} {K : Type u_2} [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))]
  (hdeg :
    @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n →
    @Eq.{1} Nat
      (Nat.card.{max u_2 u_1} (@Atlas.Orthogonal.Minus.DMinus.{u_1, u_2} n F K inst inst_1 inst_2 inst_3 inst_4 hdeg))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (Atlas.Orthogonal.Minus.orderNumerator (Nat.card.{u_1} F) n)
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) n)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.Orthogonal.Minus.family_simple.{u_1,
    u_2} : ∀ {F : Type u_1} {K : Type u_2} [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))]
  (hdeg :
    @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    @IsSimpleGroup.{max u_2 u_1} (@Atlas.Orthogonal.Minus.DMinus.{u_1, u_2} n F K inst inst_1 inst_2 inst_3 inst_4 hdeg)
      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, max u_1 u_2} F
        (Atlas.Orthogonal.Minus.Vector.{u_1, u_2}
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          F K)
        inst
        (@Prod.instAddCommGroup.{u_1, u_2}
          (Atlas.Orthogonal.VectorD.{u_1}
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            F)
          K
          (@Pi.addCommGroup.{0, u_1}
            (Atlas.Orthogonal.Index
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (fun a ↦ F) fun i ↦
            @Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst)))
          (@Ring.toAddCommGroup.{u_2} K (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst_1))))
        (@Prod.instModule.{u_1, u_1, u_2} F
          (Atlas.Orthogonal.VectorD.{u_1}
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            F)
          K (@CommSemiring.toSemiring.{u_1} F (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
          (@Pi.addCommMonoid.{0, u_1}
            (Atlas.Orthogonal.Index
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (fun a ↦ F) fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@DivisionSemiring.toSemiring.{u_1} F
                (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))))
          (@Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
          (@Pi.Function.module.{0, u_1, u_1}
            (Atlas.Orthogonal.Index
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            F F (@CommSemiring.toSemiring.{u_1} F (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
            (@Semiring.toAddCommMonoid.{u_1} F
              (@DivisionSemiring.toSemiring.{u_1} F
                (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))))
            (@Semiring.toModule.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))))
          (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
            inst_4))
        (@Atlas.Orthogonal.Minus.form.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 hdeg
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Uniform order, n ≥ 2

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz) · [Passed audit (27 Sep)](verification/runs/minus-orthogonal-rank-three-all-ranks-order/20260927T013845-635/CERTIFICATE.md).

```lean
@Atlas.Orthogonal.Minus.family_order_all.{u_1,
    u_2} : ∀ {F : Type u_1} {K : Type u_2} [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))]
  (hdeg :
    @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    @Eq.{1} Nat
      (Nat.card.{max u_2 u_1} (@Atlas.Orthogonal.Minus.DMinus.{u_1, u_2} n F K inst inst_1 inst_2 inst_3 inst_4 hdeg))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (Atlas.Orthogonal.Minus.orderNumerator (Nat.card.{u_1} F) n)
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) n)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Uniform simplicity, n ≥ 2

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz) · [Passed audit (27 Sep)](verification/runs/minus-orthogonal-rank-three-all-ranks-simplicity/20260927T013328-843/CERTIFICATE.md).

```lean
@Atlas.Orthogonal.Minus.family_simple_all.{u_1,
    u_2} : ∀ {F : Type u_1} {K : Type u_2} [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))]
  (hdeg :
    @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    @IsSimpleGroup.{max u_2 u_1} (@Atlas.Orthogonal.Minus.DMinus.{u_1, u_2} n F K inst inst_1 inst_2 inst_3 inst_4 hdeg)
      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, max u_1 u_2} F
        (Atlas.Orthogonal.Minus.Vector.{u_1, u_2}
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          F K)
        inst
        (@Prod.instAddCommGroup.{u_1, u_2}
          (Atlas.Orthogonal.VectorD.{u_1}
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            F)
          K
          (@Pi.addCommGroup.{0, u_1}
            (Atlas.Orthogonal.Index
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (fun a ↦ F) fun i ↦
            @Ring.toAddCommGroup.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst)))
          (@Ring.toAddCommGroup.{u_2} K (@DivisionRing.toRing.{u_2} K (@Field.toDivisionRing.{u_2} K inst_1))))
        (@Prod.instModule.{u_1, u_1, u_2} F
          (Atlas.Orthogonal.VectorD.{u_1}
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            F)
          K (@CommSemiring.toSemiring.{u_1} F (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
          (@Pi.addCommMonoid.{0, u_1}
            (Atlas.Orthogonal.Index
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (fun a ↦ F) fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@DivisionSemiring.toSemiring.{u_1} F
                (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))))
          (@Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
          (@Pi.Function.module.{0, u_1, u_1}
            (Atlas.Orthogonal.Index
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            F F (@CommSemiring.toSemiring.{u_1} F (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
            (@Semiring.toAddCommMonoid.{u_1} F
              (@DivisionSemiring.toSemiring.{u_1} F
                (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))))
            (@Semiring.toModule.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))))
          (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
            inst_4))
        (@Atlas.Orthogonal.Minus.form.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4 hdeg
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

<a id="family-3d4"></a>

## ³D₄(q)

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Triality.card_group.{u_1,
  u_2} : ∀ (F : Type u_1) (K : Type u_2) [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))],
  @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (Nat.card.{u_2} (@Atlas.Triality.Group.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Triality.simple.{u_1,
  u_2} : ∀ (F : Type u_1) (K : Type u_2) [inst : Field.{u_1} F] [inst_1 : Field.{u_2} K] [inst_2 : Finite.{u_1 + 1} F]
  [inst_3 : Finite.{u_2 + 1} K]
  [inst_4 :
    @Algebra.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
      (@DivisionSemiring.toSemiring.{u_2} K
        (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))],
  @Eq.{1} Nat
      (@Module.finrank.{u_1, u_2} F K
        (@DivisionSemiring.toSemiring.{u_1} F (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1))))
        (@Algebra.toModule.{u_1, u_2} F K (@Semifield.toCommSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_1)))
          inst_4))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @IsSimpleGroup.{u_2} (@Atlas.Triality.Group.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4)
      (@Subgroup.toGroup.{u_2}
        (@Atlas.Orthogonal.O_DPlus.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K
          (@Field.toCommRing.{u_2} K inst_1))
        (@Subgroup.toGroup.{u_2}
          (@LinearEquiv.{u_2, u_2, u_2, u_2} K K
            (@CommSemiring.toSemiring.{u_2} K (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
            (@CommSemiring.toSemiring.{u_2} K (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
            (@RingHom.id.{u_2} K
              (@Semiring.toNonAssocSemiring.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))))
            (@RingHom.id.{u_2} K
              (@Semiring.toNonAssocSemiring.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))))
            ⋯ ⋯ (Atlas.Orthogonal.VectorD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
            (Atlas.Orthogonal.VectorD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
            (@AddCommGroup.toAddCommMonoid.{u_2}
              (Atlas.Orthogonal.VectorD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
              (@Pi.addCommGroup.{0, u_2}
                (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (fun a ↦ K)
                fun i ↦ @Ring.toAddCommGroup.{u_2} K (@CommRing.toRing.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))
            (@AddCommGroup.toAddCommMonoid.{u_2}
              (Atlas.Orthogonal.VectorD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
              (@Pi.addCommGroup.{0, u_2}
                (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (fun a ↦ K)
                fun i ↦ @Ring.toAddCommGroup.{u_2} K (@CommRing.toRing.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))
            (@Pi.Function.module.{0, u_2, u_2}
              (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) K K
              (@CommSemiring.toSemiring.{u_2} K (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
              (@Semiring.toAddCommMonoid.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))
              (@Semiring.toModule.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))))
            (@Pi.Function.module.{0, u_2, u_2}
              (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) K K
              (@CommSemiring.toSemiring.{u_2} K (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
              (@Semiring.toAddCommMonoid.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))
              (@Semiring.toModule.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))))
          (@LinearEquiv.automorphismGroup.{u_2, u_2} K
            (Atlas.Orthogonal.VectorD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
            (@CommSemiring.toSemiring.{u_2} K (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
            (@AddCommGroup.toAddCommMonoid.{u_2}
              (Atlas.Orthogonal.VectorD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
              (@Pi.addCommGroup.{0, u_2}
                (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (fun a ↦ K)
                fun i ↦ @Ring.toAddCommGroup.{u_2} K (@CommRing.toRing.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))
            (@Pi.Function.module.{0, u_2, u_2}
              (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) K K
              (@CommSemiring.toSemiring.{u_2} K (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
              (@Semiring.toAddCommMonoid.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))
              (@Semiring.toModule.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))))
          (@Atlas.Orthogonal.isometrySubgroup.{u_2, u_2} K (@Field.toCommRing.{u_2} K inst_1)
            (Atlas.Orthogonal.VectorD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
            (@Pi.addCommGroup.{0, u_2}
              (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (fun a ↦ K) fun i ↦
              @Ring.toAddCommGroup.{u_2} K (@CommRing.toRing.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
            (@Pi.Function.module.{0, u_2, u_2}
              (Atlas.Orthogonal.Index (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) K K
              (@CommSemiring.toSemiring.{u_2} K (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))
              (@Semiring.toAddCommMonoid.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1))))
              (@Semiring.toModule.{u_2} K
                (@CommSemiring.toSemiring.{u_2} K
                  (@CommRing.toCommSemiring.{u_2} K (@Field.toCommRing.{u_2} K inst_1)))))
            (@Atlas.Orthogonal.formD.{u_2} (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K
              (@Field.toCommRing.{u_2} K inst_1))))
        (@Atlas.Triality.generated.{u_1, u_2} F K inst inst_1 inst_2 inst_3 inst_4))
```

<a id="family-e6"></a>

## E₆(q)

Primary construction: Chevalley root-operator model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.E6_order.{u_1} : ∀ (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.FiniteFieldDomain.{u_1} K inst →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Chevalley.Catalogue.E6.{u_1} K inst))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.E6_simple.{u_1} : ∀ (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.FiniteFieldDomain.{u_1} K inst →
    @IsSimpleGroup.{u_1} (@Atlas.Chevalley.Catalogue.E6.{u_1} K inst) (@Atlas.Chevalley.Catalogue.E6Group.{u_1} K inst)
```

<a id="family-e7"></a>

## E₇(q)

Primary construction: Chevalley root-operator model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.E7_order.{u_1} : ∀ (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.FiniteFieldDomain.{u_1} K inst →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Chevalley.Catalogue.E7.{u_1} K inst))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63))))
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Nat.gcd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.E7_simple.{u_1} : ∀ (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.FiniteFieldDomain.{u_1} K inst →
    @IsSimpleGroup.{u_1} (@Atlas.Chevalley.Catalogue.E7.{u_1} K inst) (@Atlas.Chevalley.Catalogue.E7Group.{u_1} K inst)
```

<a id="family-e8"></a>

## E₈(q)

Primary construction: Chevalley root-operator model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.E8_order.{u_1} : ∀ (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.FiniteFieldDomain.{u_1} K inst →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.Chevalley.Catalogue.E8.{u_1} K inst))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} K) (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Chevalley.Catalogue.E8_simple.{u_1} : ∀ (K : Type u_1) [inst : Field.{u_1} K],
  @Atlas.Chevalley.Catalogue.FiniteFieldDomain.{u_1} K inst →
    @IsSimpleGroup.{u_1} (@Atlas.Chevalley.Catalogue.E8.{u_1} K inst) (@Atlas.Chevalley.Catalogue.E8Group.{u_1} K inst)
```

<a id="family-f4"></a>

## F₄(q)

Primary construction: Split-Albert model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.F4.card_Model.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F],
  @Eq.{1} Nat (Nat.card.{u_1} ↥(@Atlas.F4.Model.{u_1} F inst))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.F4.isSimple.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [Finite.{u_1 + 1} F],
  @IsSimpleGroup.{u_1} (↥(@Atlas.F4.Model.{u_1} F inst))
    (@Subgroup.toGroup.{u_1}
      (@LinearEquiv.{u_1, u_1, u_1, u_1} F F
        (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
        (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
        (@RingHom.id.{u_1} F
          (@Semiring.toNonAssocSemiring.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@RingHom.id.{u_1} F
          (@Semiring.toNonAssocSemiring.{u_1} F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        ⋯ ⋯ (Atlas.Albert.Carrier.{u_1} F) (Atlas.Albert.Carrier.{u_1} F)
        (@Prod.instAddCommMonoid.{u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → F)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Atlas.SplitOctonion.Carrier.{u_1} F)
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (fun a ↦ F)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (fun a ↦ Atlas.SplitOctonion.Carrier.{u_1} F) fun i ↦
            @Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@Prod.instAddCommMonoid.{u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → F)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Atlas.SplitOctonion.Carrier.{u_1} F)
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (fun a ↦ F)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (fun a ↦ Atlas.SplitOctonion.Carrier.{u_1} F) fun i ↦
            @Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@Prod.instModule.{u_1, u_1, u_1} F (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → F)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Atlas.SplitOctonion.Carrier.{u_1} F)
          (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (fun a ↦ F)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (fun a ↦ Atlas.SplitOctonion.Carrier.{u_1} F) fun i ↦
            @Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) F F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Semiring.toModule.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) F
            (Atlas.SplitOctonion.Carrier.{u_1} F)
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) F F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
              (@Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
              (@Semiring.toModule.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F
                  (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))))
        (@Prod.instModule.{u_1, u_1, u_1} F (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → F)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Atlas.SplitOctonion.Carrier.{u_1} F)
          (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (fun a ↦ F)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (fun a ↦ Atlas.SplitOctonion.Carrier.{u_1} F) fun i ↦
            @Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) F F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Semiring.toModule.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) F
            (Atlas.SplitOctonion.Carrier.{u_1} F)
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) F F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
              (@Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
              (@Semiring.toModule.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F
                  (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))))))
      (@LinearEquiv.automorphismGroup.{u_1, u_1} F (Atlas.Albert.Carrier.{u_1} F)
        (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
        (@Prod.instAddCommMonoid.{u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → F)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Atlas.SplitOctonion.Carrier.{u_1} F)
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (fun a ↦ F)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (fun a ↦ Atlas.SplitOctonion.Carrier.{u_1} F) fun i ↦
            @Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
        (@Prod.instModule.{u_1, u_1, u_1} F (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → F)
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Atlas.SplitOctonion.Carrier.{u_1} F)
          (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (fun a ↦ F)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (fun a ↦ Atlas.SplitOctonion.Carrier.{u_1} F) fun i ↦
            @Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) F F
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Semiring.toAddCommMonoid.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Semiring.toModule.{u_1} F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) F
            (Atlas.SplitOctonion.Carrier.{u_1} F)
            (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
            (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ F)
              fun i ↦
              @Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
            (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) F F
              (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst)))
              (@Semiring.toAddCommMonoid.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))
              (@Semiring.toModule.{u_1} F
                (@CommSemiring.toSemiring.{u_1} F
                  (@CommRing.toCommSemiring.{u_1} F (@Field.toCommRing.{u_1} F inst))))))))
      (@Atlas.F4.Model.{u_1} F inst))
```

### Chevalley root-operator model

[Concrete-model Lean certificate](verification/existence/2026-10-25-draft/Chevalley-F4/Solution.lean) · [exact mathematical specification](verification/existence/2026-10-25-draft/Chevalley-F4/Challenge.lean).

<a id="exceptional-tits"></a>

## ²F₄(2)′ (Tits)

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Tits.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Tits.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 17971200) (instOfNatNat (nat_lit 17971200)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Tits.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Tits.Model
  (@Subgroup.toGroup.{0} Atlas.Tits.Ambient
    (@Subgroup.toGroup.{0} Atlas.Rudvalis.RudvalisGroup
      (@QuotientGroup.Quotient.group.{0} (↥Atlas.Rudvalis.gaussianLatticeGroup)
        (@Subgroup.toGroup.{0}
          (@LinearEquiv.{0, 0, 0, 0} Rat Rat Rat.semiring Rat.semiring
            (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring))
            (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring)) ⋯ ⋯ Atlas.Rudvalis.RationalSpace
            Atlas.Rudvalis.RationalSpace
            (@Pi.addCommMonoid.{0, 0} Atlas.Rudvalis.Coordinate (fun a ↦ Rat) fun i ↦ Rat.addCommMonoid)
            (@Pi.addCommMonoid.{0, 0} Atlas.Rudvalis.Coordinate (fun a ↦ Rat) fun i ↦ Rat.addCommMonoid)
            (@Pi.Function.module.{0, 0, 0} Atlas.Rudvalis.Coordinate Rat Rat Rat.semiring Rat.addCommMonoid
              (@Semiring.toModule.{0} Rat Rat.semiring))
            (@Pi.Function.module.{0, 0, 0} Atlas.Rudvalis.Coordinate Rat Rat Rat.semiring Rat.addCommMonoid
              (@Semiring.toModule.{0} Rat Rat.semiring)))
          (@LinearEquiv.automorphismGroup.{0, 0} Rat Atlas.Rudvalis.RationalSpace Rat.semiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Rudvalis.Coordinate (fun a ↦ Rat) fun i ↦ Rat.addCommMonoid)
            (@Pi.Function.module.{0, 0, 0} Atlas.Rudvalis.Coordinate Rat Rat Rat.semiring Rat.addCommMonoid
              (@Semiring.toModule.{0} Rat Rat.semiring)))
          Atlas.Rudvalis.gaussianLatticeGroup)
        Atlas.Rudvalis.gaussianScalarSubgroup Atlas.Rudvalis.gaussianScalarSubgroup_normal)
      Atlas.Tits.ambientStabilizer)
    Atlas.Tits.derivedSubgroup)
```

<a id="family-g2"></a>

## G₂(q)

Primary construction: Split-octonion model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.G2.card_Model.{u_1} : ∀ {K : Type u_1} [inst : Field.{u_1} K] [Finite.{u_1 + 1} K],
  @Eq.{1} Nat (Nat.card.{u_1} ↥(@Atlas.G2.Model.{u_1} K inst))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} K)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.G2.isSimple.{u_1} : ∀ {K : Type u_1} [inst : Field.{u_1} K] [Finite.{u_1 + 1} K],
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat.card.{u_1} K) →
    @IsSimpleGroup.{u_1} (↥(@Atlas.G2.Model.{u_1} K inst))
      (@Subgroup.toGroup.{u_1}
        (@LinearEquiv.{u_1, u_1, u_1, u_1} K K
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@RingHom.id.{u_1} K
            (@Semiring.toNonAssocSemiring.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
          (@RingHom.id.{u_1} K
            (@Semiring.toNonAssocSemiring.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
          ⋯ ⋯ (Atlas.SplitOctonion.Carrier.{u_1} K) (Atlas.SplitOctonion.Carrier.{u_1} K)
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ K)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ K)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) K K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
            (@Semiring.toModule.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) K K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
            (@Semiring.toModule.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
        (@LinearEquiv.automorphismGroup.{u_1, u_1} K (Atlas.SplitOctonion.Carrier.{u_1} K)
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@Pi.addCommMonoid.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun a ↦ K)
            fun i ↦
            @Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
          (@Pi.Function.module.{0, u_1, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) K K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@Semiring.toAddCommMonoid.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
            (@Semiring.toModule.{u_1} K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
        (@Atlas.G2.Model.{u_1} K inst))
```

### Chevalley root-operator model

[Concrete-model Lean certificate](verification/existence/2026-10-25-draft/Chevalley-G2/Solution.lean) · [exact mathematical specification](verification/existence/2026-10-25-draft/Chevalley-G2/Challenge.lean).

<a id="family-reeg2"></a>

## ²G₂(q)

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.ReeG2.order.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [inst_1 : Finite.{u_1 + 1} F]
  [inst_2 :
    @CharP.{u_1} F
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} F
        (@Ring.toAddGroupWithOne.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  (m : Nat),
  @Eq.{1} Nat (Nat.card.{u_1} F)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    @Eq.{1} Nat (Nat.card.{u_1} (@Atlas.ReeG2.Model.{u_1} F inst inst_1 inst_2 m))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Nat.card.{u_1} F)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (Nat.card.{u_1} F) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.card.{u_1} F)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
@Atlas.ReeG2.simple.{u_1} : ∀ {F : Type u_1} [inst : Field.{u_1} F] [inst_1 : Finite.{u_1 + 1} F]
  [inst_2 :
    @CharP.{u_1} F
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} F
        (@Ring.toAddGroupWithOne.{u_1} F (@DivisionRing.toRing.{u_1} F (@Field.toDivisionRing.{u_1} F inst))))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  (m : Nat),
  @Atlas.ReeG2.Parameters.{u_1} F inst inst_1 m →
    @IsSimpleGroup.{u_1} (@Atlas.ReeG2.Model.{u_1} F inst inst_1 inst_2 m)
      (@Subgroup.toGroup.{u_1} (@Atlas.ReeG2.Ambient.{u_1} F inst)
        (@Units.instGroup.{u_1}
          (Matrix.{0, 0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F)
          (@Semiring.toMonoid.{u_1}
            (Matrix.{0, 0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F)
            (@Matrix.semiring.{u_1, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F
              (@DivisionSemiring.toSemiring.{u_1} F
                (@Semifield.toDivisionSemiring.{u_1} F (@Field.toSemifield.{u_1} F inst)))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
        (@Atlas.ReeG2.generated.{u_1} F inst inst_1 inst_2 m))
```

<a id="sporadic-m11"></a>

## M₁₁

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu11.card : ∀ (D : Atlas.Codes.Dodecad) (a : Atlas.Codes.Mathieu12Points D),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu11.Model D a)) Atlas.Sporadic.Mathieu11.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu11.isSimpleGroup : ∀ (D : Atlas.Codes.Dodecad) (a : Atlas.Codes.Mathieu12Points D),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu11.Model D a)
    (@Subgroup.toGroup.{0} (↥(Atlas.Codes.Mathieu12DodecadModel D))
      (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
        (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
          Atlas.Codes.Mathieu24CodeModel)
        (Atlas.Codes.Mathieu12DodecadModel D))
      (Atlas.Codes.Mathieu11PointModel D a))
```

<a id="sporadic-m12"></a>

## M₁₂

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu12.card : ∀ (D : Atlas.Codes.Dodecad),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu12.Model D)) Atlas.Sporadic.Mathieu12.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu12.isSimpleGroup : ∀ (D : Atlas.Codes.Dodecad),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu12.Model D)
    (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
      (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
        Atlas.Codes.Mathieu24CodeModel)
      (Atlas.Codes.Mathieu12DodecadModel D))
```

<a id="sporadic-m22"></a>

## M₂₂

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu22.card : ∀ (a : Atlas.Codes.Omega) (b : ↥(Atlas.Codes.Mathieu23Points a)),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu22.Model a b)) Atlas.Sporadic.Mathieu22.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu22.isSimpleGroup : ∀ (a : Atlas.Codes.Omega) (b : ↥(Atlas.Codes.Mathieu23Points a)),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu22.Model a b)
    (@Subgroup.toGroup.{0} (↥(Atlas.Codes.Mathieu23PointModel a))
      (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
        (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
          Atlas.Codes.Mathieu24CodeModel)
        (Atlas.Codes.Mathieu23PointModel a))
      (Atlas.Codes.Mathieu22PointModel a b))
```

<a id="sporadic-m23"></a>

## M₂₃

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu23.card : ∀ (a : Atlas.Codes.Omega),
  @Eq.{1} Nat (Nat.card.{0} (Atlas.Sporadic.Mathieu23.Model a)) Atlas.Sporadic.Mathieu23.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu23.isSimpleGroup : ∀ (a : Atlas.Codes.Omega),
  @IsSimpleGroup.{0} (Atlas.Sporadic.Mathieu23.Model a)
    (@Subgroup.toGroup.{0} (↥Atlas.Codes.Mathieu24CodeModel)
      (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
        Atlas.Codes.Mathieu24CodeModel)
      (Atlas.Codes.Mathieu23PointModel a))
```

<a id="sporadic-m24"></a>

## M₂₄

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu24.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Mathieu24.Model)
  Atlas.Sporadic.Mathieu24.expectedOrder
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Mathieu24.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Mathieu24.Model
  (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Atlas.Codes.Omega) (@Equiv.Perm.permGroup.{0} Atlas.Codes.Omega)
    Atlas.Codes.Mathieu24CodeModel)
```

<a id="sporadic-co1"></a>

## Co₁

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Conway1.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Conway1.Model) Atlas.Sporadic.Conway1.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Conway1.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Conway1.Model
  (@QuotientGroup.Quotient.group.{0} Atlas.Lattices.LeechIsometryGroup
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
        (↥Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech))
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      Atlas.Lattices.leechIsometries)
    Atlas.Conway.leechCentralSigns Atlas.Conway.instNormalLeechIsometryGroupLeechCentralSigns)
```

<a id="sporadic-co2"></a>

## Co₂

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Conway2.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.Conway2.Model) Atlas.Sporadic.Conway2.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Conway2.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.Conway2.Model)
  (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
        (↥Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech))
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      Atlas.Lattices.leechIsometries)
    Atlas.Sporadic.Conway2.Model)
```

<a id="sporadic-co3"></a>

## Co₃

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Conway3.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.Conway3.Model) Atlas.Sporadic.Conway3.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Conway3.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.Conway3.Model)
  (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
        (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
        (↥Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech))
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
        (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
          (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
          (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
          Atlas.Lattices.leech)
        (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
          (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
            (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)))
      Atlas.Lattices.leechIsometries)
    Atlas.Sporadic.Conway3.Model)
```

<a id="sporadic-mcl"></a>

## McL

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.McLaughlin.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.McLaughlin.Model)
  Atlas.Sporadic.McLaughlin.order
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.McLaughlin.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.McLaughlin.Model)
  (@Subgroup.toGroup.{0} (↥Atlas.Sporadic.Conway3.Model)
    (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
      (@Subgroup.toGroup.{0}
        (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
          (↥Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech))
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        Atlas.Lattices.leechIsometries)
      Atlas.Sporadic.Conway3.Model)
    Atlas.Sporadic.McLaughlin.Model)
```

<a id="sporadic-hs"></a>

## HS

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.HigmanSims.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.HigmanSims.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 44352000) (instOfNatNat (nat_lit 44352000)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.HigmanSims.isSimpleGroup : @IsSimpleGroup.{0} (↥Atlas.Sporadic.HigmanSims.Model)
  (@Subgroup.toGroup.{0}
    (↥(Atlas.Conway.fullVectorStabilizer (Atlas.Conway.normSixVector Atlas.Conway.co3MarkedCoordinate)))
    (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
      (@Subgroup.toGroup.{0}
        (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
          (↥Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech))
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        Atlas.Lattices.leechIsometries)
      (Atlas.Conway.fullVectorStabilizer (Atlas.Conway.normSixVector Atlas.Conway.co3MarkedCoordinate)))
    Atlas.Sporadic.HigmanSims.Model)
```

<a id="sporadic-suz"></a>

## Suz

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Suzuki.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Suzuki.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 448345497600) (instOfNatNat (nat_lit 448345497600)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Suzuki.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Suzuki.Model
  (@QuotientGroup.Quotient.group.{0} (↥Atlas.Conway.eisensteinCentralizer)
    (@Subgroup.toGroup.{0} Atlas.Lattices.LeechIsometryGroup
      (@Subgroup.toGroup.{0}
        (@LinearEquiv.{0, 0, 0, 0} Int Int Int.instSemiring Int.instSemiring
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring))
          (@RingHom.id.{0} Int (@Semiring.toNonAssocSemiring.{0} Int Int.instSemiring)) ⋯ ⋯ (↥Atlas.Lattices.leech)
          (↥Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech))
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        (@LinearEquiv.automorphismGroup.{0, 0} Int (↥Atlas.Lattices.leech) Int.instSemiring
          (@Submodule.addCommMonoid.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instSemiring
            (@Pi.addCommMonoid.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommMonoid)
            (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
            Atlas.Lattices.leech)
          (@AddCommGroup.toIntModule.{0} (↥Atlas.Lattices.leech)
            (@Submodule.addCommGroup.{0, 0} Int Atlas.Lattices.IntegerCoordinates Int.instRing
              (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup)
              (@AddCommGroup.toIntModule.{0} Atlas.Lattices.IntegerCoordinates
                (@Pi.addCommGroup.{0, 0} Atlas.Codes.Omega (fun a ↦ Int) fun i ↦ Int.instAddCommGroup))
              Atlas.Lattices.leech)))
        Atlas.Lattices.leechIsometries)
      Atlas.Conway.eisensteinCentralizer)
    Atlas.Conway.eisensteinCentralizerScalars Atlas.Conway.eisensteinCentralizerScalars_normal)
```

<a id="sporadic-j2"></a>

## J₂

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Janko2.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Janko2.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 604800) (instOfNatNat (nat_lit 604800)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Janko2.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Janko2.Model
  (@QuotientGroup.Quotient.group.{0} (↥Atlas.Conway.icosianHermitianGroup)
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Rat Rat Rat.semiring Rat.semiring
        (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring))
        (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring)) ⋯ ⋯
        Atlas.Lattices.IcosianRationalCoordinates Atlas.Lattices.IcosianRationalCoordinates
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun a ↦ Atlas.Algebra.IcosianQuaternion) fun i ↦
          @Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun a ↦ Atlas.Algebra.IcosianQuaternion) fun i ↦
          @Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat
          Atlas.Algebra.IcosianQuaternion Rat.semiring
          (@Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
          (@Quaternion.instModule.{0, 0} Rat Atlas.Algebra.GoldenRational
            (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing)
            Rat.semiring
            (@QuadraticAlgebra.instModule.{0, 0} Rat Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.semiring
              (@Semiring.toAddCommMonoid.{0} Rat
                (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
              (@Semiring.toModule.{0} Rat Rat.semiring))))
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat
          Atlas.Algebra.IcosianQuaternion Rat.semiring
          (@Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
          (@Quaternion.instModule.{0, 0} Rat Atlas.Algebra.GoldenRational
            (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing)
            Rat.semiring
            (@QuadraticAlgebra.instModule.{0, 0} Rat Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.semiring
              (@Semiring.toAddCommMonoid.{0} Rat
                (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
              (@Semiring.toModule.{0} Rat Rat.semiring)))))
      (@LinearEquiv.automorphismGroup.{0, 0} Rat Atlas.Lattices.IcosianRationalCoordinates Rat.semiring
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun a ↦ Atlas.Algebra.IcosianQuaternion) fun i ↦
          @Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat
          Atlas.Algebra.IcosianQuaternion Rat.semiring
          (@Semiring.toAddCommMonoid.{0} Atlas.Algebra.IcosianQuaternion
            (@Ring.toSemiring.{0} Atlas.Algebra.IcosianQuaternion
              (@Quaternion.instRing.{0} Atlas.Algebra.GoldenRational
                (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing))))
          (@Quaternion.instModule.{0, 0} Rat Atlas.Algebra.GoldenRational
            (@QuadraticAlgebra.instCommRing.{0} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.commRing)
            Rat.semiring
            (@QuadraticAlgebra.instModule.{0, 0} Rat Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) Rat.semiring
              (@Semiring.toAddCommMonoid.{0} Rat
                (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
              (@Semiring.toModule.{0} Rat Rat.semiring)))))
      Atlas.Conway.icosianHermitianGroup)
    Atlas.Conway.icosianCentralSigns Atlas.Conway.icosianCentralSigns_normal)
```

<a id="sporadic-fi22"></a>

## Fi₂₂

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Fischer22.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Fischer22.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 64561751654400) (instOfNatNat (nat_lit 64561751654400)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Fischer22.simple : @IsSimpleGroup.{0} Atlas.Sporadic.Fischer22.Model
  (@QuotientGroup.Quotient.group.{0} (↥(Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer22Marking))
    (@Subgroup.toGroup.{0} (↥Atlas.Fischer.rootGeneratedRayGroup)
      (@Subgroup.toGroup.{0}
        (Equiv.Perm.{1} (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        (@Equiv.Perm.permGroup.{0}
          (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        Atlas.Fischer.rootGeneratedRayGroup)
      (Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer22Marking))
    (Atlas.Fischer.residueCentralElementary Atlas.Fischer.fischer22Marking) ⋯)
```

<a id="sporadic-fi23"></a>

## Fi₂₃

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Fischer23.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Fischer23.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 4089470473293004800) (instOfNatNat (nat_lit 4089470473293004800)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Fischer23.simple : @IsSimpleGroup.{0} Atlas.Sporadic.Fischer23.Model
  (@QuotientGroup.Quotient.group.{0} (↥(Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer23Marking))
    (@Subgroup.toGroup.{0} (↥Atlas.Fischer.rootGeneratedRayGroup)
      (@Subgroup.toGroup.{0}
        (Equiv.Perm.{1} (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        (@Equiv.Perm.permGroup.{0}
          (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
        Atlas.Fischer.rootGeneratedRayGroup)
      (Atlas.Fischer.residueCentralizer Atlas.Fischer.fischer23Marking))
    (Atlas.Fischer.residueCentralElementary Atlas.Fischer.fischer23Marking) ⋯)
```

<a id="sporadic-fi24prime"></a>

## Fi₂₄′

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Fischer24Prime.card : @Eq.{1} Nat (Nat.card.{0} ↥Atlas.Sporadic.Fischer24Prime.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 1255205709190661721292800) (instOfNatNat (nat_lit 1255205709190661721292800)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Fischer24Prime.simple : @IsSimpleGroup.{0} (↥Atlas.Sporadic.Fischer24Prime.Model)
  (@Subgroup.toGroup.{0} (↥Atlas.Fischer.rootGeneratedRayGroup)
    (@Subgroup.toGroup.{0}
      (Equiv.Perm.{1} (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
      (@Equiv.Perm.permGroup.{0}
        (@Set.Elem.{0} (Finset.{0} Atlas.Fischer.Coordinates) Atlas.Fischer.DisplayedReflectingRay))
      Atlas.Fischer.rootGeneratedRayGroup)
    Atlas.Sporadic.Fischer24Prime.Model)
```

<a id="sporadic-ru"></a>

## Ru

Primary construction: Original concrete model.

### Order

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Rudvalis.card : @Eq.{1} Nat (Nat.card.{0} Atlas.Sporadic.Rudvalis.Model)
  (@OfNat.ofNat.{0} Nat (nat_lit 145926144000) (instOfNatNat (nat_lit 145926144000)))
```

### Simple

[Compiled evidence](verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz).

```lean
Atlas.Sporadic.Rudvalis.isSimpleGroup : @IsSimpleGroup.{0} Atlas.Sporadic.Rudvalis.Model
  (@QuotientGroup.Quotient.group.{0} (↥Atlas.Rudvalis.gaussianLatticeGroup)
    (@Subgroup.toGroup.{0}
      (@LinearEquiv.{0, 0, 0, 0} Rat Rat Rat.semiring Rat.semiring
        (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring))
        (@RingHom.id.{0} Rat (@Semiring.toNonAssocSemiring.{0} Rat Rat.semiring)) ⋯ ⋯ Atlas.Rudvalis.RationalSpace
        Atlas.Rudvalis.RationalSpace
        (@Pi.addCommMonoid.{0, 0} Atlas.Rudvalis.Coordinate (fun a ↦ Rat) fun i ↦ Rat.addCommMonoid)
        (@Pi.addCommMonoid.{0, 0} Atlas.Rudvalis.Coordinate (fun a ↦ Rat) fun i ↦ Rat.addCommMonoid)
        (@Pi.Function.module.{0, 0, 0} Atlas.Rudvalis.Coordinate Rat Rat Rat.semiring Rat.addCommMonoid
          (@Semiring.toModule.{0} Rat Rat.semiring))
        (@Pi.Function.module.{0, 0, 0} Atlas.Rudvalis.Coordinate Rat Rat Rat.semiring Rat.addCommMonoid
          (@Semiring.toModule.{0} Rat Rat.semiring)))
      (@LinearEquiv.automorphismGroup.{0, 0} Rat Atlas.Rudvalis.RationalSpace Rat.semiring
        (@Pi.addCommMonoid.{0, 0} Atlas.Rudvalis.Coordinate (fun a ↦ Rat) fun i ↦ Rat.addCommMonoid)
        (@Pi.Function.module.{0, 0, 0} Atlas.Rudvalis.Coordinate Rat Rat Rat.semiring Rat.addCommMonoid
          (@Semiring.toModule.{0} Rat Rat.semiring)))
      Atlas.Rudvalis.gaussianLatticeGroup)
    Atlas.Rudvalis.gaussianScalarSubgroup Atlas.Rudvalis.gaussianScalarSubgroup_normal)
```

