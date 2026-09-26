import Lake
open Lake DSL

package myerson_satterthwaite

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0-rc2"

@[default_target]
lean_lib MS where
  roots := #[
    `MS,
    `MS.Defs,
    `MS.Envelope,
    `MS.Efficiency,
    `MS.Main,
    `MS.Palomar
  ]

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
