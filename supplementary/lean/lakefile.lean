-- Lake build file for the Formal-AVS replication package.
--
-- Frozen snapshot of the HowardBridge scaffold that backs Formal-AVS
-- (the public benchmark for the dataset paper). All HowardBridge
-- modules are vendored in HowardBridge/.
--
-- Mathlib pinned at SHA c1e30e172c8fda21e6776bf1f10351e882ee31b9 — the
-- exact commit the 2026-04-25 paper sweep type-checked against. The
-- lake-manifest.json in this directory locks every transitive dep to
-- the matching SHA so `lake update` produces the same build tree the
-- sweep saw. Lean toolchain pinned in `lean-toolchain` (v4.30.0-rc2).
--
-- To replicate from scratch: `cd lean && lake exe cache get && lake build`.

import Lake
open Lake DSL

package «HowardBridge» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c1e30e172c8fda21e6776bf1f10351e882ee31b9"

@[default_target]
lean_lib «HowardBridge» where
