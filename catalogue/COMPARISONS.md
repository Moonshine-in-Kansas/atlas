# Comparison certificates: complete interface index

The [construction and identification guide](REALIZATIONS.md) explains the
mathematical conclusions. This index retains every registered interface
and its exact parameter assumptions, grouped by the question it answers.
[One aggregate certificate](REALIZATIONS.md#remaining-pairs) covers all
nonisomorphic pairs in its [stated scope](REALIZATIONS.md#comparison-scope).

## Different construction models

| Family | Models | Proved domain | Certificate |
|---|---|---|---|
| Aₙ(q) | Matrix · Chevalley | K an arbitrary finite field; q = Nat.card K; r >= 1; every finite characteristic | [Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-a-to-legacy-v1) |
| Cₙ(q) | Symplectic · Chevalley | K an arbitrary finite field; q = Nat.card K; r >= 2; every finite characteristic | [Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-c-to-legacy-v1) |
| Dₙ(q) | Quadratic · Chevalley | K an arbitrary finite field; q = Nat.card K; r >= 4; every finite characteristic | [Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-d-to-legacy-v1) |
| Bₙ(q) | Quadratic · Chevalley | K an arbitrary finite field; q = Nat.card K; n : Nat, rank r = n+1 >= 2; every finite characteristic, including B2(F2) | [Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-b-to-legacy-v1) |

G₂/F₄ comparisons retain their [separate scopes](REALIZATIONS.md#comparison-scope).

<a id="field-transport"></a>

## Field and extension transport

| Groups | Conclusion | Parameters | Lean certificate |
|---|---|---|---|
| B(n,F) / B(n,K) | Isomorphic | F,K any fields; n any natural rank; explicit field isomorphism F ~= K | [`Atlas.Comparisons.Classical.bFieldEquiv`](../Atlas/Comparisons/Classical/Orthogonal.lean#L48) |
| D+(n,F) / D+(n,K) | Isomorphic | F,K any fields; n any natural rank; explicit field isomorphism F ~= K | [`Atlas.Comparisons.Classical.dFieldEquiv`](../Atlas/Comparisons/Classical/Orthogonal.lean#L53) |
| PSU(d,K/F) / PSU(d,Kprime/Fprime) | Isomorphic | Finite quadratic extensions; explicit base and extension field equivalences; actual Frobenius involutions | [`Atlas.Comparisons.Classical.unitaryFieldEquiv`](../Atlas/Comparisons/LowRank/FieldTransport.lean#L13) |
| DMinus(n,F,K) / DMinus(n,Fprime,Kprime) | Isomorphic | Finite quadratic extensions; explicit base/extension field equivalences with commuting algebraMap square | [`Atlas.Comparisons.Classical.dMinusFieldEquiv`](../Atlas/Comparisons/LowRank/FieldTransport.lean#L18) |

<a id="between-families"></a>

## Uniform and low-rank isomorphisms

| Groups | Conclusion | Parameters | Lean certificate |
|---|---|---|---|
| B(1,F) / PSL(2,F) | Isomorphic | F any field; natural quadratic dimension 3; PSL dimension 2; includes q=2,3 | [`Atlas.Comparisons.Classical.b1EquivA1`](../Atlas/Comparisons/Classical/Orthogonal.lean#L20) |
| C(1,F) / PSL(2,F) | Isomorphic | F any field; Lie rank one, PSL dimension two | [`Atlas.Comparisons.Classical.c1EquivA1`](../Atlas/Comparisons/LowRank/Symplectic.lean#L9) |
| PSU(2,K/F) / PSL(2,F) | Isomorphic | F,K finite fields; Algebra F K; finrank F K = 2; PSL over base F | [`Atlas.Comparisons.Classical.psuTwoEquivA1`](../Atlas/Comparisons/LowRank/Unitary.lean#L10) |
| PSU(2,K/F) / C(1,F) | Isomorphic | F,K finite quadratic extension; all characteristics | [`Atlas.Comparisons.Classical.psuTwoEquivC1`](../Atlas/Comparisons/LowRank/Unitary.lean#L14) |
| PSU(2,K/F) / B(1,F) | Isomorphic | F,K finite quadratic extension; all characteristics | [`Atlas.Comparisons.Classical.psuTwoEquivB1`](../Atlas/Comparisons/LowRank/Unitary.lean#L18) |
| B(n,F) / C(n,F) | Isomorphic | F finite, characteristic 2; n >= 1; natural dimensions 2n+1 and 2n | [`Atlas.Comparisons.Classical.evenBEquivC`](../Atlas/Comparisons/Classical/Orthogonal.lean#L24) |
| B(2,F) / C(2,F) | Isomorphic | F finite, every characteristic; natural dimensions 5 and 4 | [`Atlas.Comparisons.Classical.b2EquivC2`](../Atlas/Comparisons/Classical/Orthogonal.lean#L29) |
| D+(2,F) / PSL(2,F) x PSL(2,F) | Isomorphic | F any field; split quadratic dimension 4; PSL dimensions 2 and 2 | [`Atlas.Comparisons.Classical.d2EquivProduct`](../Atlas/Comparisons/Classical/Orthogonal.lean#L37) |
| D+(3,F) / PSL(4,F) | Isomorphic | F finite, every characteristic; split quadratic dimension 6; PSL dimension 4 | [`Atlas.Comparisons.Classical.d3EquivA3`](../Atlas/Comparisons/Classical/Orthogonal.lean#L43) |
| DMinus(2,F,K) / PSL(2,K) | Isomorphic | F,K finite quadratic extension; Lie rank two; PSL over extension K | [`Atlas.Comparisons.Classical.dMinusTwoEquivA1`](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean#L8) |
| DMinus(3,F,K) / PSU(4,K/F) | Isomorphic | F,K finite quadratic extension; Lie rank three, unitary dimension four | [`Atlas.Comparisons.Classical.dMinusThreeEquivUnitary`](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean#L13) |

<a id="small-parameters"></a>

## Exceptional and small-parameter isomorphisms

| Groups | Conclusion | Parameters | Lean certificate |
|---|---|---|---|
| PSL(2,F) / A5 | Isomorphic | F any finite field of cardinality 4; natural projective-line action | [`Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5`](../Atlas/Comparisons/Exceptional/Order60Four.lean#L21) |
| PSL(2,F) / A5 | Isomorphic | F any finite field of cardinality 5; proved elementary order-60 recognition | [`Atlas.Comparisons.Exceptional.psl2Card5EquivAlt5`](../Atlas/Comparisons/Exceptional/Order60Five.lean#L15) |
| PSL(2,F) / PSL(2,ZMod 5) | Isomorphic | F any finite field of cardinality 4; composition of the verified maps | [`Atlas.Comparisons.Exceptional.psl2Card4EquivPsl2Five`](../Atlas/Comparisons/Exceptional/Order60Five.lean#L29) |
| PSL(2,ZMod 7) / PSL(3,ZMod 2) | Isomorphic | Actual matrix models; common faithful action on eight points | [`Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two`](../Atlas/Comparisons/Exceptional/Order168.lean#L38) |
| PSL(2,F) / A6 | Isomorphic | F any finite field of cardinality 9; common faithful ten-point actions | [`Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6`](../Atlas/Comparisons/Exceptional/Order360.lean#L47) |
| PSL(2,GaloisField 3 2) / A6 | Isomorphic | Canonical pinned finite-field wrapper | [`Atlas.Comparisons.Exceptional.psl2NineEquivAlt6`](../Atlas/Comparisons/Exceptional/Order360.lean#L52) |
| B(2,ZMod 2)' / C(2,ZMod 2)' | Isomorphic | Actual commutator subgroups; restriction of the full B2/C2 comparison | [`Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived`](../Atlas/Comparisons/Exceptional/BinaryDerived.lean#L15) |
| C(2,ZMod 2)' / A6 | Isomorphic | Derived group of order 360; full C2(2) is not the endpoint | [`Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6`](../Atlas/Comparisons/Exceptional/BinaryDerived.lean#L21) |
| PSL(2,F) / B(2,ZMod 2)' | Isomorphic | F finite of cardinality 9; composition through actual A6 | [`Atlas.Comparisons.Exceptional.psl2Card9EquivB2BinaryDerived`](../Atlas/Comparisons/Exceptional/Order360.lean#L55) |
| PSL(2,F) / C(2,ZMod 2)' | Isomorphic | F finite of cardinality 9; composition through actual A6 | [`Atlas.Comparisons.Exceptional.psl2Card9EquivC2BinaryDerived`](../Atlas/Comparisons/Exceptional/Order360.lean#L61) |
| A8 / D+(3,ZMod 2) | Isomorphic | Actual binary deleted permutation quotient with explicit split isometry | [`Atlas.Comparisons.Exceptional.alt8EquivD3Two`](../Atlas/Comparisons/Exceptional/Order20160A8.lean#L81) |
| PSL(4,ZMod 2) / A8 | Isomorphic | Actual D3/A3 comparison composed with the faithful deleted-module action | [`Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8`](../Atlas/Comparisons/Exceptional/Order20160A8.lean#L88) |
| PSU(4,K/ZMod 2) / C(2,ZMod 3) | Isomorphic | K finite; Algebra (ZMod 2) K; finrank (ZMod 2) K = 2; actual positive E6 Weyl reductions | [`Atlas.Comparisons.Exceptional.psu4BinaryEquivPSp4Ternary`](../Atlas/Comparisons/Exceptional/Order25920.lean#L15) |
| PSU(4,L/F) / C(2,T) | Isomorphic | F,L,T finite fields; Algebra F L; finrank F L = 2; \|F\|=2 and \|T\|=3; full-center projective models | [`Atlas.Comparisons.Exceptional.psu4Card2EquivPSp4Card3`](../Atlas/Comparisons/Exceptional/Order25920.lean#L29) |
| DMinus(3,F,L) / C(2,T) | Isomorphic | F,L,T finite fields; Algebra F L; finrank F L = 2; \|F\|=2 and \|T\|=3; retained minus/unitary map | [`Atlas.Comparisons.Exceptional.dMinus3Card2EquivPSp4Card3`](../Atlas/Comparisons/Exceptional/Order25920.lean#L38) |
| PSU(4,L/F) / B(2,T) | Isomorphic | F,L,T finite fields; Algebra F L; finrank F L = 2; \|F\|=2 and \|T\|=3; retained B2/C2 map | [`Atlas.Comparisons.Exceptional.psu4Card2EquivB2Card3`](../Atlas/Comparisons/Exceptional/Order25920.lean#L45) |
| C(2,ZMod 2) / S6 | Isomorphic | Full group of order720; compatible with existing derived A6 map | [`Atlas.Comparisons.Exceptional.c2BinaryEquivSymmetric`](../Atlas/Comparisons/Small/BinarySymplectic.lean#L9) |
| C(2,F) / S6 | Isomorphic | F any finite field of cardinality2; field transport of actual six-refinement action | [`Atlas.Comparisons.Exceptional.c2Card2EquivSymmetric`](../Atlas/Comparisons/Small/BinarySymplectic.lean#L33) |
| B(2,F) / S6 | Isomorphic | F any finite field of cardinality2; full B2/C2 comparison composed with transported six-point action | [`Atlas.Comparisons.Exceptional.b2Card2EquivSymmetric`](../Atlas/Comparisons/Small/BinarySymplectic.lean#L37) |

<a id="equal-order-separation"></a>

## Equal-order and nonisomorphism certificates

| Groups | Conclusion | Parameters | Lean certificate |
|---|---|---|---|
| B(n,F) / C(n,F) | Equal order | F finite, odd characteristic; n >= 2; no isomorphism asserted | [`Atlas.Comparisons.Classical.oddB_card_eq_C`](../Atlas/Comparisons/Classical/OrthogonalOrder.lean#L10) |
| B(n,F) / C(n,F) | Nonisomorphic | F finite, odd characteristic; n >= 3; distinguished by proved involution-class counts | [`Atlas.Comparisons.Classical.oddB_not_equiv_C`](../Atlas/Comparisons/Classical/OrthogonalInvolutions.lean#L21) |
| PSL(4,ZMod 2) / PSL(3,F) | Equal order | F finite of cardinality 4; both orders 20160 | [`Atlas.Comparisons.Exceptional.psl4Two_card_eq_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L27) |
| A8 / PSL(3,F) | Equal order | F finite of cardinality 4; both orders 20160 | [`Atlas.Comparisons.Exceptional.alt8_card_eq_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L31) |
| PSL(4,ZMod 2) / PSL(3,F) | Nonisomorphic | F finite of cardinality 4; Sylow-2 centers of cardinalities 2 and 4 | [`Atlas.Comparisons.Exceptional.psl4Two_not_equiv_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L13) |
| A8 / PSL(3,F) | Nonisomorphic | F finite of cardinality 4; transport of the proved Sylow-center obstruction | [`Atlas.Comparisons.Exceptional.alt8_not_equiv_psl3Card4`](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L22) |

These 40 registered interfaces supplement the [aggregate comparison and order certificates](REALIZATIONS.md#remaining-pairs). All current coverage limits and unfinished bridges are listed in [one scope section](REALIZATIONS.md#comparison-scope).
