# Catalogue data

`catalogue.json` contains the 33 completed entries, exact parameter conventions,
public declarations, auxiliary groups and evidence bindings. `realizations.json`
retains separate model records and explicit identification maps. `comparisons.json`
retains the 40 exposed comparison interfaces with their mathematical hypotheses.

Run `ruby catalogue/manage.rb refresh` after a reviewed data edit, then
`ruby catalogue/manage.rb check`. This deterministically produces the catalogue,
realization and comparison pages, CSV inventory and principal compiled signatures.
It checks diagram sources and registered interfaces; it does not run Lean or grant
new verification status. Use the [audit procedure](../AUDIT.md) for that.

The independent existence specifications retain exact source-bound mathematical
contracts. No separate nonabelian theorem rows are displayed in the catalogue;
those declarations remain in Lean and in the full verification target data.

`current-verification.json` binds these three registries to the 1,207-root
26 October compiled audit. The prior 1,167-reference catalogue check is preserved
as [dated evidence](../verification/catalogue/2026-10-19/original-current-verification.json);
its historical development paths and scope are not current release paths.
