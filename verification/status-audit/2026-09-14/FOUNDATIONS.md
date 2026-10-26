# What the checked assertions mean

This report uses the pinned Lean v4.34.0-rc2 and mathlib revision in SNAPSHOT.json. The complete printed declarations are in THEOREM_STATEMENTS.txt and definitions.log. The concrete example is printed separately in EXAMPLE.txt; it is compiler output, not a reconstructed theorem.

## Group

`Group G` is a structure on a carrier type G. In this version it extends `DivInvMonoid G` and adds the law a⁻¹a=1. Its inherited structures provide multiplication, associativity, identity and both identity laws, inverse, division, natural powers and integer powers with their compatibility/recursion laws. `DivInvMonoid` extends `Monoid`, `Inv`, `Div`, and `ZPow`; `Monoid` supplies the semigroup and identity structure and natural powers. Division is required to agree with multiplication by inverse. The right inverse law follows from these laws. The compiler's expanded Group/parent printouts expose the exact fields, including the additional power operations used by the library.

The carrier's equality is Lean equality; for subtypes it identifies equal underlying elements, while quotient constructions use the relevant equivalence relation through quotient equality. Quotient soundness is addressed below. The group laws are proof fields supplied by the constructed instance. They are not additional project axioms.

A theorem with a variable G and an instance parameter `[Group G]` assumes such structure. For example, the cyclic classification interface quantifies over commutative groups. A theorem about `Atlas.Sporadic.Fischer22.Model` instead uses the particular constructed centralizer quotient and its subgroup/quotient group instance. Evidence.lean synthesizes that instance from the existing environment and prints it; it does not introduce a new assumed group.

The Mathieu interfaces sometimes quantify over a Golay dodecad or marked distinct coordinates. These parameters select objects of already constructed types. The source also supplies standard choices and existence packages. The exact statements retain those parameters rather than incorrectly presenting every interface as a constant with no arguments.

## Order

In the pinned library, `Nat.card α` is `Cardinal.toNat (Cardinal.mk α)`. Cardinal.mk gives the cardinal of the type; toNat returns the corresponding natural number for finite cardinals and zero for infinite cardinals. `Nat.card` therefore returns zero on infinite types. It is not itself a finiteness predicate. On a type with `Fintype` structure it equals `Fintype.card`; `Finite` is the proposition that such a finite enumeration exists, without choosing a computationally convenient enumeration.

The public finite assertions and order proofs are extracted separately. The positive numeral equalities for sporadics also rule out infinitude through Nat.card's infinite behavior, but the catalogue does not rely on silently interpreting Nat.card as a finiteness hypothesis. For cyclic groups the order theorem assumes positive modulus; modulus zero would give the infinite additive integer model. For PSL the field and finite-field hypotheses and the rank assumptions are visible in the signature. The exported natural-number divisions are ordinary truncated natural division, justified here by exact group-index/cardinality relations; the TypeAConstruction package includes the corresponding division-free order identity. The alternating factorial formula assumes n≥2; the all-n order definition handles n=0,1 separately.

A declaration named `order` is sometimes just an integer definition, while `card` proves equality with Nat.card. For other interfaces `order` itself is a theorem. This audit selects the actual equality declarations. `orderOf g`, used for distinguished involutions and generators, is the order of an element and is a different concept.

## Simplicity and nonabelianity

The actual mathlib class `IsSimpleGroup G` extends `Nontrivial G` and requires every normal subgroup H to equal either the bottom or top subgroup. Nontrivial means that two unequal elements exist. A subgroup is a subset closed under multiplication, containing identity and closed under inverse. Its normality structure requires gng⁻¹ to lie in H whenever n lies in H, for every g in G. The bottom subgroup consists of the identity and the top subgroup is all of G.

Thus the mathematical statement is: G is nontrivial and has no proper nontrivial normal subgroup. Commutativity is **not** excluded. Cyclic groups of prime order qualify. For the nonabelian entries the additional extracted assertion is either the negation of `IsMulCommutative` or the existence of two elements with unequal products in opposite orders. The alternating noncommutativity theorem already holds for n≥4; its nonabelian simplicity package uses n≥5. The PSL simplicity equivalence includes precisely the two stated exceptions for n≥2 over finite fields.

## Logical foundations and scope of assurance

Lean checks proof terms in dependent type theory. Types may depend on terms; propositions inhabit Prop and proofs inhabit their propositions. Universes keep type levels distinct. Inductive declarations include their introduction and elimination rules. Equality, definitional reduction, proof irrelevance, and quotient mechanisms are parts of the logical framework, not fully enumerated by an axiom report.

The extracted dependency graph contains exactly three axiom constants:

- `propext`: logically equivalent propositions are equal as propositions.
- `Classical.choice`: from nonemptiness of a type, select an element of that type, at arbitrary universe level. This supports noncomputable choices and classical reasoning.
- `Quot.sound`: related representatives have equal images under the primitive quotient constructor.

The exact axiom declarations, including universes and implicit arguments, are printed in definitions.log. AXIOMS.txt records the actual list per selected declaration; lists are not inferred from a whitelist. The name-search hits `Classical.axiomOfChoice` and `Classical.axiom_of_choice` are proved theorems derived from these foundations, not new axiom declarations.

An axiom report does not list every assumption in a theorem's type. It does not prove consistency, verify the kernel's implementation, certify the compiler/operating system/filesystem/silicon, or establish that the formal definitions express the author's intended mathematics. In particular this audit loads compiled dependencies and performs a current incremental build plus fresh extraction; it is not an independently implemented kernel/comparator check. Historical comparator reports are separate evidence and are not presented as rerun here.

Classical/noncomputable constructions can establish existence without an efficient algorithm for enumerating the group. Finite tables, explicit matrices, normalization and ordinary `decide` may occur inside kernel-checkable proofs; their existence does not make the mathematics computer-free. The current closures contain no sorryAx, project axiom or native reduction trust constant, and the Atlas token scan found no native_decide. This supports absence of externally trusted computational certificates in these proof closures; it does not describe all software used historically to discover proofs or generate candidate data.

The conditional assurance is: under these logical foundations and a correct Lean kernel implementation, the proof terms establish the extracted formal statements. Independent mathematical review of the constructions and their interpretation remains meaningful and necessary.

## Actual printed example

EXAMPLE.txt is the complete output of the example portion of Evidence.lean, with proof bodies omitted by the printer. It prints the Fi22 carrier, residue quotient and its defining centralizer/kernel, the fixed marking, synthesized Group and Finite instances, and the finiteness, order, simplicity and noncommutativity signatures and axiom reports. It then prints the actual cyclic carrier and its order, simplicity and commutativity signatures and dependencies. Those outputs are included in THEOREM_STATEMENTS.txt through the model/foundations extraction as well; the smaller file makes this example easier to inspect.

In ordinary mathematics the first example is the actual quotient of the common centralizer of two marked commuting involutions in the constructed full Fischer ray group by the central subgroup they generate. It has order 64,561,751,654,400 and is nonabelian simple. The second is the multiplicative type tag on the additive group of Z/pZ; for prime p it has order p and is simple and commutative. Neither example assumes the desired order or simplicity as input.
