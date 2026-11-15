/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvGood

/-!
# The final package and the source-buffer bound (the interface with NEARIMG2's `kSel`)

Packet PROVE-GW2-BUF (round 19). The package nearImg is proved for is `pkgB` with:
* the goodness re-indexing `psiGoodFam` (the version loss);
* SDE's counterflow word `cwSrc`;
* the exit rules `exitB`;
* any base `K₀`;
* a candidate selector `kSel` (NEARIMG2's, D50).

* **`pkgF h13 h12 K₀ kSel k`**: that package; `pkgVerF`, `pkgKbF`.
* `slotGood n m a`: the version loss's good event of the near stop of slot `(l, n, m, a)`: the death family's slot
  behind version `m − 1` of `pkgVerF` (the near stop's lower cap) has its cell exit plus start below its cap.
* **`srcBad n m a`**: on that good event, the J32 sample's gain is below the near stop. That is clause (iii)'s
  source-buffer loss.
* **`SrcBoundStatement h13 h12 K₀ kSel`** (NEARIMG2's `kSel` bound, D50): almost surely on the alive event, for
  every level `n` and every `ε > 0`, eventually in `m`, the conditional probability of `srcBad` at the selected
  candidate is at most `ε`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (K₀ : PkgFamily.{u})

/-- The final package's version family. -/
abbrev pkgVerF : SchedVerXFamily.{u} := pkgVer h13 (psiGoodFam h13 h12)

/-- The final package's base package. -/
abbrev pkgKbF : PkgFamily.{u} := pkgKb h13 h12 (psiGoodFam h13 h12) cwSrc exitB K₀

/-- **The final package at buffer index `k`.** -/
abbrev pkgF (kSel : NearSelB.{u}) (k : ℕ) : VPkgXFamily.{u} :=
  pkgB h13 h12 (psiGoodFam h13 h12) cwSrc exitB K₀ kSel k

section Events

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

open Classical in
/-- **The good event of slot `(l, n, m, a)`**: the death family's slot behind version `m − 1` of the final version
family has its cell exit plus stage start below its cap (empty off the good roots). -/
def slotGood (n m a : ℕ) : Set Ω :=
  if hg : GoodRoot c r then
    goodVer h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l) n a
      (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (m - 1) + (m - 1))
  else ∅

/-- **Clause (iii)'s source-buffer loss at slot `(l, n, m, a)`**: on the slot's good event, the J32 sample's gain is
below the near stop. -/
def srcBad (n m a : ℕ) : Set Ω :=
  slotGood h13 h12 c r l n m a ∩
    {ξ | (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) <
      ((pkgX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) (pkgKbF h13 h12 K₀) Ω c r).nearVar l n m a).stop ξ}

end Events

/-- **NEARIMG2's `kSel` bound** (D50), in the final package's terms: almost surely on the alive event of
`J32S GW2Sdq.gapFam`, for every level `n` and every `ε > 0`, eventually in `m`, the conditional probability given
the retained history of the source-buffer loss at the selected candidate is at most `ε`. -/
def SrcBoundStatement (kSel : NearSelB.{u}) : Prop :=
  ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ (n : ℕ) {ε : ℝ≥0∞}, 0 < ε → ∀ᶠ m in atTop,
        condExpKernel c.P (c.sigma r l) ω₀
          (srcBad h13 h12 K₀ c r l n m ((pkgF h13 h12 K₀ kSel k Ω c r).nearCandidate l ω₀ n m)) ≤ ε

end InteractingSLE.Theorem14.GW2Bh
