/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxDrvAssemble
import InteractingSLE.Spec.Supplement.SBS3DxDrvEntrK2
import InteractingSLE.Spec.Supplement.SBS3DxDrvEntrance
import InteractingSLE.Spec.Supplement.SBS3DxDrvHint
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DxKAmb
import InteractingSLE.Spec.Supplement.SBS3DxKSplit
import InteractingSLE.Spec.Supplement.SBS3DxSBLuAmb
import InteractingSLE.Spec.Supplement.SBS3DxSBLuWire
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SB2DrvLineIfaceR` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB2DrvLineIfaceR` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `sb2EntranceLinesStatement_of_halvesRLe`;
* `sb2DriverLinkAmbStatement_of_halvesRLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal

/-! ### The completed physical line filtration -/

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

end EntranceUnion

/-! ### The repaired version data -/

/-! ### The two named inputs, repaired -/

/-- **The two repaired halves give K2's line data in the entrance σ-algebra.** -/
theorem sb2EntranceLinesStatement_of_halvesRLe (hV : SB2LineVersionRLeStatement.{u})
    (hK : SB2LineKernelRStatement.{u}) : SB2EntranceLinesLeStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h E k u ψ η ζ HP _ I u₀ hu₀ D
  obtain ⟨Vd⟩ := hV κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D
  exact ⟨Vd.𝓗, Vd.W, Vd.Γ, Vd.marks_le, Vd.W_zero, Vd.W_cont, Vd.W_adapted,
    hK κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd, Vd.Vg, Vd.link, Vd.life⟩

/-- **SB2(1)'s ambient driver link from the two repaired line halves** (Theorems 1.2–1.3 as hypotheses, R48). -/
theorem sb2DriverLinkAmbStatement_of_halvesRLe (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : SB2LineVersionRLeStatement.{u}) (hK : SB2LineKernelRStatement.{u}) :
    SB2DriverLinkAmbLeStatement.{u} :=
  sb2DriverLinkAmbStatement_of_lineDataLe h12p h13 (sb2EntranceLinesStatement_of_halvesRLe hV hK)

end InteractingSLE.Theorem14.SB.Lv
