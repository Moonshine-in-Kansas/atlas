# Additional realizations and explicit identifications

Different constructions remain distinct until an actual multiplicative
equivalence is proved. Order and simplicity alone do not identify them.
These records do not add families to the 33-entry catalogue.

<a id="family-psl-chevalley"></a>

## A Chevalley root operators

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action. The selected simply connected companion is a distinct cover; no replacement occurs at nonsimple parameters.

Parameters: K an arbitrary finite field; q = Nat.card K; r >= 1; every finite characteristic

Carrier: `Atlas.Chevalley.Catalogue.A` ([source](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean)).

| Property | Declaration | Full audit |
|---|---|---|
| finite | `Atlas.Chevalley.Catalogue.A_finite` | [evidence](../verification/runs/chevalley-catalogue-a-finite/20261018T160128-105) |
| order | `Atlas.Chevalley.Catalogue.A_order` | [evidence](../verification/runs/chevalley-catalogue-a-order/20261018T160235-105) |
| center | `Atlas.Chevalley.Catalogue.A_center` | [evidence](../verification/runs/chevalley-catalogue-a-center/20261018T160348-105) |
| simple | `Atlas.Chevalley.Catalogue.A_simple` | [evidence](../verification/runs/chevalley-catalogue-a-simple/20261018T160458-105) |
| exceptions | `Atlas.Chevalley.Catalogue.A_exceptions` | [evidence](../verification/runs/chevalley-catalogue-a-exceptions/20261018T160714-105) |

Identification with `family.PSL/matrix`: `Atlas.Chevalley.Catalogue.A_identification`
([source](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean), [full audit](../verification/runs/chevalley-a-to-legacy-v1/20261018T160827-105)).

Domain: K an arbitrary finite field; q = Nat.card K; r >= 1; every finite characteristic.

<a id="family-b-chevalley"></a>

## B Chevalley root operators

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action; the carrier is unchanged at B2(F2). The selected simply connected companion is a distinct cover.

Parameters: K an arbitrary finite field; q = Nat.card K; n : Nat, rank r = n+1 >= 2; every finite characteristic, including B2(F2)

Carrier: `Atlas.Chevalley.Catalogue.B` ([source](../Atlas/LinearGroups/Chevalley/Catalogue/BConstruction.lean)).

| Property | Declaration | Full audit |
|---|---|---|
| finite | `Atlas.Chevalley.Catalogue.B_finite` | [evidence](../verification/runs/chevalley-catalogue-b-finite/20261018T164023-105) |
| order | `Atlas.Chevalley.Catalogue.B_order` | [evidence](../verification/runs/chevalley-catalogue-b-order/20261018T164216-105) |
| center | `Atlas.Chevalley.Catalogue.B_center` | [evidence](../verification/runs/chevalley-catalogue-b-center/20261018T164427-105) |
| simple | `Atlas.Chevalley.Catalogue.B_simple` | [evidence](../verification/runs/chevalley-catalogue-b-simple/20261018T164645-105) |
| exceptions | `Atlas.Chevalley.Catalogue.B_exceptions` | [evidence](../verification/runs/chevalley-catalogue-b-exceptions/20261018T165018-105) |

Identification with `family.B/quadratic`: `Atlas.Chevalley.Catalogue.B_identification`
([source](../Atlas/LinearGroups/Chevalley/Catalogue/BIdentification.lean), [full audit](../verification/runs/chevalley-b-to-legacy-v1/20261018T165216-105)).

Domain: K an arbitrary finite field; q = Nat.card K; n : Nat, rank r = n+1 >= 2; every finite characteristic, including B2(F2).

<a id="family-c-chevalley"></a>

## C Chevalley root operators

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action. The selected simply connected companion is a distinct cover; no replacement occurs at nonsimple parameters.

Parameters: K an arbitrary finite field; q = Nat.card K; r >= 2; every finite characteristic

Carrier: `Atlas.Chevalley.Catalogue.C` ([source](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean)).

| Property | Declaration | Full audit |
|---|---|---|
| finite | `Atlas.Chevalley.Catalogue.C_finite` | [evidence](../verification/runs/chevalley-catalogue-c-finite/20261018T161215-105) |
| order | `Atlas.Chevalley.Catalogue.C_order` | [evidence](../verification/runs/chevalley-catalogue-c-order/20261018T161342-105) |
| center | `Atlas.Chevalley.Catalogue.C_center` | [evidence](../verification/runs/chevalley-catalogue-c-center/20261018T161519-105) |
| simple | `Atlas.Chevalley.Catalogue.C_simple` | [evidence](../verification/runs/chevalley-catalogue-c-simple/20261018T161656-105) |
| exceptions | `Atlas.Chevalley.Catalogue.C_exceptions` | [evidence](../verification/runs/chevalley-catalogue-c-exceptions/20261018T162002-105) |

Identification with `family.C/symplectic`: `Atlas.Chevalley.Catalogue.C_identification`
([source](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean), [full audit](../verification/runs/chevalley-c-to-legacy-v1/20261018T162154-105)).

Domain: K an arbitrary finite field; q = Nat.card K; r >= 2; every finite characteristic.

<a id="family-d-chevalley"></a>

## D Chevalley root operators

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action. The selected simply connected companion is a distinct cover, not this registered realization.

Parameters: K an arbitrary finite field; q = Nat.card K; r >= 4; every finite characteristic

Carrier: `Atlas.Chevalley.Catalogue.D` ([source](../Atlas/LinearGroups/Chevalley/Catalogue/DConstruction.lean)).

| Property | Declaration | Full audit |
|---|---|---|
| finite | `Atlas.Chevalley.Catalogue.D_finite` | [evidence](../verification/runs/chevalley-catalogue-d-finite/20261018T162701-105) |
| order | `Atlas.Chevalley.Catalogue.D_order` | [evidence](../verification/runs/chevalley-catalogue-d-order/20261018T162810-105) |
| center | `Atlas.Chevalley.Catalogue.D_center` | [evidence](../verification/runs/chevalley-catalogue-d-center/20261018T162944-105) |
| simple | `Atlas.Chevalley.Catalogue.D_simple` | [evidence](../verification/runs/chevalley-catalogue-d-simple/20261018T163112-105) |
| exceptions | `Atlas.Chevalley.Catalogue.D_exceptions` | [evidence](../verification/runs/chevalley-catalogue-d-exceptions/20261018T163340-105) |

Identification with `family.D/quadratic`: `Atlas.Chevalley.Catalogue.D_identification`
([source](../Atlas/LinearGroups/Chevalley/Catalogue/DIdentification.lean), [full audit](../verification/runs/chevalley-d-to-legacy-v1/20261018T163507-105)).

Domain: K an arbitrary finite field; q = Nat.card K; r >= 4; every finite characteristic.

<a id="family-e6-chevalley"></a>

## E6 Chevalley root operators

The root-generated elementary adjoint subgroup of matrix units from the integral Geck root operators, with its inherited group operations and faithful adjoint action. The simply connected group is a separate cover, not this carrier.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 6; every finite characteristic

Carrier: `Atlas.Chevalley.Catalogue.E6` ([source](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean)).

| Property | Declaration | Full audit |
|---|---|---|
| finite | `Atlas.Chevalley.Catalogue.E6_finite` | [evidence](../verification/runs/chevalley-catalogue-e6-finite/20261018T121513-9) |
| order | `Atlas.Chevalley.Catalogue.E6_order` | [evidence](../verification/runs/chevalley-catalogue-e6-order/20261018T121655-9) |
| center | `Atlas.Chevalley.Catalogue.E6_center` | [evidence](../verification/runs/chevalley-catalogue-e6-center/20261018T121057-9) |
| simple | `Atlas.Chevalley.Catalogue.E6_simple` | [evidence](../verification/runs/chevalley-catalogue-e6-simple/20261018T121753-9) |
| exceptions | `Atlas.Chevalley.Catalogue.E6_exceptions` | [evidence](../verification/runs/chevalley-catalogue-e6-exceptions/20261018T121411-9) |

This is the first completed anchor for its family. No identification with a different model is asserted.

<a id="family-e7-chevalley"></a>

## E7 Chevalley root operators

The root-generated elementary adjoint subgroup of matrix units from the integral Geck root operators, with its inherited group operations and faithful adjoint action. The simply connected group is a separate cover, not this carrier.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 7; every finite characteristic

Carrier: `Atlas.Chevalley.Catalogue.E7` ([source](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean)).

| Property | Declaration | Full audit |
|---|---|---|
| finite | `Atlas.Chevalley.Catalogue.E7_finite` | [evidence](../verification/runs/chevalley-catalogue-e7-finite/20261018T122155-9) |
| order | `Atlas.Chevalley.Catalogue.E7_order` | [evidence](../verification/runs/chevalley-catalogue-e7-order/20261018T122351-9) |
| center | `Atlas.Chevalley.Catalogue.E7_center` | [evidence](../verification/runs/chevalley-catalogue-e7-center/20261018T121855-9) |
| simple | `Atlas.Chevalley.Catalogue.E7_simple` | [evidence](../verification/runs/chevalley-catalogue-e7-simple/20261018T122507-9) |
| exceptions | `Atlas.Chevalley.Catalogue.E7_exceptions` | [evidence](../verification/runs/chevalley-catalogue-e7-exceptions/20261018T122052-9) |

This is the first completed anchor for its family. No identification with a different model is asserted.

<a id="family-e8-chevalley"></a>

## E8 Chevalley root operators

The root-generated elementary adjoint subgroup of matrix units from the integral Geck root operators, with its inherited group operations and faithful adjoint action. The simply connected group is a separate cover, not this carrier.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 8; every finite characteristic

Carrier: `Atlas.Chevalley.Catalogue.E8` ([source](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean)).

| Property | Declaration | Full audit |
|---|---|---|
| finite | `Atlas.Chevalley.Catalogue.E8_finite` | [evidence](../verification/runs/chevalley-catalogue-e8-finite/20261018T122949-9) |
| order | `Atlas.Chevalley.Catalogue.E8_order` | [evidence](../verification/runs/chevalley-catalogue-e8-order/20261018T123141-9) |
| center | `Atlas.Chevalley.Catalogue.E8_center` | [evidence](../verification/runs/chevalley-catalogue-e8-center/20261018T122620-9) |
| simple | `Atlas.Chevalley.Catalogue.E8_simple` | [evidence](../verification/runs/chevalley-catalogue-e8-simple/20261018T123304-9) |
| exceptions | `Atlas.Chevalley.Catalogue.E8_exceptions` | [evidence](../verification/runs/chevalley-catalogue-e8-exceptions/20261018T122839-9) |

This is the first completed anchor for its family. No identification with a different model is asserted.

## Chevalley G₂ and F₄

Their separate model-specific [Comparator contracts](../verification/existence/RESULTS.md) passed.
The G₂ and F₄ comparisons with the octonion and Albert models are not claimed here.
The preserved registry marks their dedicated catalogue registration separately.
