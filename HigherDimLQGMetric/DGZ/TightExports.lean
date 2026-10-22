import HigherDimLQGMetric.DGZ.TightShapes
import HigherDimLQGMetric.DGZ.TightCompact
import HigherDimLQGMetric.DGZ.CompareCor52

/-!
# DGZ §6 (packet L5a): unconditional exports

Packet L4c has proved `cor52Shape : ∀ d κ ξ Q, Cor52Shape d κ ξ Q` (`DGZ/CompareCor52.lean`), so
the `Cor52Shape`-conditional results of packet L5a hold outright:

* **`distInfShape : ∀ d κ ξ Q, DistInfShape d κ ξ Q`** — the orchestrator's interface shape of
  `DGZ/Interfaces.lean` (verbatim MA7 §F), proved for all parameters;
* `holderTightShape_of_lambdaComparable : LambdaComparableShape d κ ξ Q → HolderTightShape d κ ξ Q`
  — the export `HolderTightShape` once packet L5b proves DGZ (6.5) (`LambdaComparableShape`);
* `isTightMeasureSet_normMetricC_median`: under (6.5), the laws of `λ_n⁻¹ D_n` (MA7's
  `normMetricC ξ h_n (aQ … 2⁻¹)`, the normalization of `DGZThm12Shape`) are tight (over all
  realizations and all `n`); the compact sets are `holderMetricSet (B̄(0, j)) (M/c) β₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP

variable {d : ℕ}

/-- **The distance-to-infinity export** (DGZ Lemma 6.7 + (6.3); MA7 Details (c) §F,
`DistInfShape`): proved for all `d κ ξ Q` from `cor52Shape` (L4c) and `distInfShape_of_cor52`. -/
theorem distInfShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : DistInfShape d κ ξ Q :=
  distInfShape_of_cor52 (cor52Shape d κ ξ Q)

/-- **The Hölder-tightness export from (6.5)**: `HolderTightShape` holds as soon as the quantiles
are comparable to the median (`LambdaComparableShape`, DGZ (6.5), a target of packet L5b). -/
theorem holderTightShape_of_lambdaComparable {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hcomp : LambdaComparableShape d κ ξ Q) : HolderTightShape d κ ξ Q :=
  holderTightShape_of_comparable (cor52Shape d κ ξ Q) hcomp

/-- **Tightness of `λ_n⁻¹ D_n` under (6.5)** (the tightness clause of `DGZThm12Shape`; blueprint
Theorem `r2:thm:12`(d): "Proposition 6.3 with `U = ℝ^d` and (6.5)"): if `c a^{(q)}_n ≤ λ_n`, then
`λ_n⁻¹ D_n = (a^{(q)}_n/λ_n) a^{(q)}_n⁻¹ D_n` with `a^{(q)}_n/λ_n ≤ 1/c`, so the compact sets of
`exists_normMetricC_holderMetricSet` with constants `M j / c` work for the median normalization. -/
theorem isTightMeasureSet_normMetricC_median {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q)
    (hcomp : LambdaComparableShape d κ ξ Q) :
    IsTightMeasureSet {μ : MeasureTheory.Measure C(Rd d × Rd d, ℝ) | ∃ (Ω : Type)
      (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H ∧ ∃ n : ℕ,
        μ = P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n 2⁻¹))} := by
  have hd0 : 0 < d := by have := h.dim; omega
  have hξ := h.xi_pos
  have hg : 0 < ξ * (Q - Real.sqrt (2 * d)) := mul_pos hξ (by linarith [h.subcritical])
  set β₀ : ℝ := ξ * (Q - Real.sqrt (2 * d)) / 2 with hβ₀
  have hβ₀0 : 0 < β₀ := by positivity
  obtain ⟨q₂, hq₂0, hq₂1, hstr⟩ := exists_normMetricC_holderMetricSet (cor52Shape d κ ξ Q) h
    (β := β₀) hβ₀0 (by linarith)
  obtain ⟨c, hc, hcb⟩ := hcomp h q₂ hq₂1
  have hhalf0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hhalf1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨M, hM0, hMb⟩ := hstr q₂ le_rfl hq₂1 hε
  set M' : ℕ → ℝ := fun j => M j / c with hM'
  have hM'0 : ∀ j, 0 ≤ M' j := fun j => div_nonneg (hM0 j) hc.le
  have hK := isCompact_holderMetricSet (β := β₀) (tc_closedBall_mono (d := d))
    tc_closedBall_mem_nhds hβ₀0 hM'0
  refine ⟨_, hK, ?_⟩
  rintro μ ⟨Ω, _, P, W, H, hH, n, rfl⟩
  have hφ := (hH.band n).continuous
  set a := aQ P H ξ n q₂ with ha
  set lam := aQ P H ξ n 2⁻¹ with hlam
  have ha0 : 0 < a := tight_aQ_pos hd0 hH ξ n hq₂0 hq₂1
  have hlam0 : 0 < lam := tight_aQ_pos hd0 hH ξ n hhalf0 hhalf1
  have hca : c * a ≤ lam := hcb Ω P W H hH n
  have hF₁ := measurable_normMetricC (H := H n) (hH.band n).continuous (hH.band n).measurable ξ a
  have hF₂ := measurable_normMetricC (H := H n) (hH.band n).continuous (hH.band n).measurable ξ
    lam
  have hK₀ := isCompact_holderMetricSet (β := β₀) (tc_closedBall_mono (d := d))
    tc_closedBall_mem_nhds hβ₀0 hM0
  rw [MeasureTheory.Measure.map_apply hF₂ hK.isClosed.isOpen_compl.measurableSet]
  refine le_trans (measure_mono fun ω hω => ?_) ((Measure.map_apply hF₁
    hK₀.isClosed.isOpen_compl.measurableSet).symm.le.trans (hMb Ω P W H hH n))
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at hω ⊢
  intro hmem
  apply hω
  obtain ⟨h1, h2, h3⟩ := hmem
  -- the median normalization is `(a / λ)` times the `a`-normalization
  have hrel : ∀ p : Rd d × Rd d, normMetricC ξ (fun z => H n z ω) lam p =
      a / lam * normMetricC ξ (fun z => H n z ω) a p := fun p => by
    rw [normMetricC_apply (hφ ω), normMetricC_apply (hφ ω)]
    field_simp
  have hfac0 : 0 ≤ a / lam := div_nonneg ha0.le hlam0.le
  have hfac : a / lam ≤ 1 / c := by
    rw [div_le_div_iff₀ hlam0 hc]; linarith
  refine ⟨fun x => ?_, fun x y z => ?_, fun j x hx y hy => ?_⟩
  · rw [hrel, h1 x, mul_zero]
  · rw [hrel, hrel, hrel, ← mul_add]
    exact mul_le_mul_of_nonneg_left (h2 x y z) hfac0
  · rw [hrel]
    have hb := h3 j x hx y hy
    have hnn : 0 ≤ normMetricC ξ (fun z => H n z ω) a (x, y) := by
      rw [normMetricC_apply (hφ ω)]
      exact mul_nonneg (inv_pos.2 ha0).le (lfppMetric_nonneg _ _ _ _)
    have hdist : 0 ≤ dist x y ^ β₀ := Real.rpow_nonneg dist_nonneg _
    calc a / lam * normMetricC ξ (fun z => H n z ω) a (x, y)
        ≤ 1 / c * normMetricC ξ (fun z => H n z ω) a (x, y) :=
          mul_le_mul_of_nonneg_right hfac hnn
      _ ≤ 1 / c * (M j * dist x y ^ β₀) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = M' j * dist x y ^ β₀ := by rw [hM']; ring

end DGZ

end HigherDimLQGMetric
