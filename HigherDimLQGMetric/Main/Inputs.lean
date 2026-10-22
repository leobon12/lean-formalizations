import HigherDimLQGMetric.Locality.Main
import HigherDimLQGMetric.Locality.Copies
import HigherDimLQGMetric.Thm13.Main
import HigherDimLQGMetric.LfppTight.TightMain
import HigherDimLQGMetric.LfppTight.CrossMain
import HigherDimLQGMetric.Limits.TightScales
import HigherDimLQGMetric.Law.Main
import HigherDimLQGMetric.Trunc.Main
import HigherDimLQGMetric.Determ.L7f
import HigherDimLQGMetric.Bilip.MetricShell
import HigherDimLQGMetric.Bilip.Main
import HigherDimLQGMetric.Thm16.Theorem16
import HigherDimLQGMetric.Sec4.Prop42
import HigherDimLQGMetric.DGZ.ExportRealEps
import HigherDimLQGMetric.Sec10.Lemma103

/-!
# The unconditional inputs of the final assembly (orchestrator-owned)

The interface hypotheses of L10a's `theorem12_of_inputs` (`Main/Theorem12.lean`) and `sharpWeak_nonempty_of_inputs`
(`Main/Existence.lean`), discharged by the landed producers (interface pattern; rulings M30, M31, M35):

* `l6f_tightScales'`: [1] Lemma 3.7 (L6c's `l6f_tightScales` from L6a's `l6a_tight'`, L6b's `l6b_cross` with L1e's
  `l1e_law`, and L2c's `l2c_trunc`);
* `l7f_determined'`: [1] Lemma 3.16 (L7c's `l7f_determined_of` from L7a's `l7a_locality_of` and `l7b_copies`, L7b's
  `l7c_metricShell` and `l7d_bilip`);
* `b3Goal'`: [1] Theorem 1.3 (L8's `b3Goal_of`);
* `theorem16Shape'`: [1] Theorem 1.6 = (E2) (L9c's `theorem16Shape_of` with L9b's `prop42Shape_of` and L5b's
  `realEpsAdapterShape`);
* `lemma103Shape'`: [S] Lemma 10.3 (S8b's `lemma103`) in the shape `Lemma103Shape`.

This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- [1] Lemma 3.7, unconditional -/
theorem l6f_tightScales' : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6f_tightScales d ξ κ :=
  l6f_tightScales l6a_tight' (l6b_cross l1e_law) l2c_trunc

/-- [1] Lemma 3.16, unconditional -/
theorem l7f_determined' : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L7f_determined d ξ κ :=
  l7f_determined_of l7a_locality_of l7b_copies l7c_metricShell l7d_bilip l6f_tightScales'

/-- [1] Theorem 1.3 (the B3 goal), unconditional -/
theorem b3Goal' : B3Goal :=
  b3Goal_of l6a_tight' l6f_tightScales' l7f_determined'

/-- [1] Theorem 1.6 = (E2), unconditional -/
theorem theorem16Shape' : Theorem16Shape :=
  theorem16Shape_of (prop42Shape_of l6a_tight' DGZ.realEpsAdapterShape) DGZ.realEpsAdapterShape l6a_tight'

/-- [S] Lemma 10.3 in the shape `Lemma103Shape` -/
theorem lemma103Shape' : Lemma103Shape := by
  intro d hd ξ Q hξ hQ D hD Ω _ P _ h hh u v hu huv
  exact lemma103 hd hξ hQ hD P h hh hu huv

end HigherDimLQGMetric
