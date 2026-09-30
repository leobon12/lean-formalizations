import QuantumZipper.Proofs.Complex.JSShadowACL4
import QuantumZipper.Proofs.Complex.JSLayerShadowSum

/-!
# EXT-JS node B1, step 5: the line shadow functions tend to zero almost everywhere

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 "(C0: SH ⇒ removable.)", steps 3 and 5.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, proof of Proposition 1, p. 272: after
integrating over the lines, the charged sum is `Σ_{l(Q) ≤ Λ} |∇f|(Q) l(Q) s(Q)^{n-1}`, which is
small by Hölder's inequality since `Σ (|∇f|(Q) l(Q))^2 ≲ ∫ |∇f|^2 < ∞` and the tail of the shadow
sum `Σ s(Q)^2` tends to `0`.

Here: `Σ_{k,j} o_{k,j}² < ∞` for `o_{k,j} = diam (g '' Q_{k,j})` (Cauchy–area estimate A1 for the top
boxes, the overlap bound `≤ 6` of the enlarged boxes A3 and the area formula A2), then Young's
inequality `2od ≤ t o² + t⁻¹ d²` in place of Cauchy–Schwarz, and the tail of the shadow sum.
Since `n ↦ Φ_n(y)` decreases, `∫ ⨅ Φ_n = 0` gives `Φ_n(y) → 0` for a.e. `y`.

Main results: `isChart_comp`, `tsum_ediam_topBox_sq_lt_top`, `measurable_lineShadow`,
`ae_tendsto_lineShadow`.
-/

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

variable {R : ℝ}

/-- A homeomorphism holomorphic off `K`, composed with a chart for `K`, is a chart (for `∅`). -/
theorem isChart_comp {K : Set ℂ} {F : ℂ → ℂ} (hF : IsChart K R F) (e : ℂ ≃ₜ ℂ)
    (he : DifferentiableOn ℂ e Kᶜ) : IsChart ∅ R (e ∘ F) where
  pos := hF.pos
  cont := e.continuous.comp_continuousOn hF.cont
  holo := he.comp hF.holo hF.mapsTo
  inj := e.injective.comp_injOn hF.inj
  mapsTo := fun _ _ => by simp

/-- **`Σ o² < ∞`.** For a chart `G`, the squared image diameters of all top boxes have finite
sum: `Σ_{k,j} diam (G '' Q_{k,j})² ≤ (20/π) · 6 · area (G '' layer)`. -/
theorem tsum_ediam_topBox_sq_lt_top {K : Set ℂ} {G : ℂ → ℂ} (hG : IsChart K R G) :
    ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), ediam (G '' topBox R k j) ^ 2 < ⊤ := by
  have hR := hG.pos
  set S := layerOpen R (5 * dyLen R 0 / 4) with hSdef
  have hSH : S ⊆ H := layerOpen_subset_H hR.le _
  have hsub : ∀ k, ∀ j ∈ Finset.range (2 ^ k), bigBox R k j ⊆ S := by
    intro k j hj z hz
    have h1 := bigBox_subset_layerOpen hR.le (Finset.mem_range.1 hj) hz
    have h2 := dyLen_le_of_le hR.le (Nat.zero_le k)
    exact ⟨h1.1, h1.2.1, by linarith [h1.2.2]⟩
  have hSB : S ⊆ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
    intro z hz
    rw [hSdef, layerOpen, mem_reProdIm, dyLen_zero] at hz
    exact mem_reProdIm.2 ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      hz.2.1.le, by linarith [hz.2.2]⟩
  have hfin : volume (G '' S) < ⊤ :=
    (measure_mono (image_mono hSB)).trans_lt
      (((isCompact_Icc.reProdIm isCompact_Icc).image_of_continuousOn hG.cont).measure_lt_top)
  set f : ℂ → ℝ≥0∞ := fun z => ‖deriv G z‖ₑ ^ 2 with hfdef
  have hfmeas : Measurable f := by
    have h2 : Measurable fun z : ℂ => ‖deriv G z‖ₑ ^ 2 := by
      simpa only [Function.comp_apply, ofReal_norm] using
        (ENNReal.measurable_ofReal.comp (measurable_norm.comp (measurable_deriv G))).pow_const
          (2 : ℕ)
    rwa [hfdef]
  have h1 : ∀ k, ∀ j ∈ Finset.range (2 ^ k),
      volume (G '' bigBox R k j) = ∫⁻ z in S, (bigBox R k j).indicator f z := by
    intro k j hj
    rw [volume_image_eq_lintegral_normSq_deriv (isOpen_bigBox R k j) (hG.holo.mono (fun z hz =>
        bigBox_subset_upper hR.le k j hz)) (hG.inj.mono (fun z hz => bigBox_subset_upper hR.le k j hz)),
      ← hfdef, ← Measure.restrict_restrict_of_subset (hsub k j hj),
      lintegral_indicator (isOpen_bigBox R k j).measurableSet]
  have hmeasI : ∀ k j, Measurable ((bigBox R k j).indicator f) := fun k j =>
    hfmeas.indicator (isOpen_bigBox R k j).measurableSet
  have hvol : ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), volume (G '' bigBox R k j) ≤
      6 * volume (G '' S) := by
    calc ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), volume (G '' bigBox R k j)
        = ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), ∫⁻ z in S, (bigBox R k j).indicator f z :=
          tsum_congr fun k => Finset.sum_congr rfl (h1 k)
      _ = ∫⁻ z in S, ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), (bigBox R k j).indicator f z := by
          rw [lintegral_tsum fun k => (Finset.measurable_sum _ fun j _ => hmeasI k j).aemeasurable]
          refine tsum_congr fun k => ?_
          rw [lintegral_finsetSum' _ fun j _ => (hmeasI k j).aemeasurable]
      _ ≤ ∫⁻ z in S, 6 * f z := by
          refine lintegral_mono fun z => ?_
          have hpt : ∀ k j, (bigBox R k j).indicator f z =
              (bigBox R k j).indicator (1 : ℂ → ℝ≥0∞) z * f z := by
            intro k j
            by_cases hj : z ∈ bigBox R k j <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, hj]
          calc ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), (bigBox R k j).indicator f z
              = (∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k),
                  (bigBox R k j).indicator (1 : ℂ → ℝ≥0∞) z) * f z := by
                rw [← ENNReal.tsum_mul_right]
                refine tsum_congr fun k => ?_
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun j _ => hpt k j
            _ ≤ 6 * f z := mul_le_mul_left (sum_indicator_bigBox_le_six hR z) _
      _ = 6 * volume (G '' S) := by
          rw [lintegral_const_mul' 6 f (by norm_num),
            volume_image_eq_lintegral_normSq_deriv (isOpen_layerOpen R _)
              (hG.holo.mono hSH) (hG.inj.mono hSH)]
  calc ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), ediam (G '' topBox R k j) ^ 2
      ≤ ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k),
          ENNReal.ofReal (20 / Real.pi) * volume (G '' bigBox R k j) :=
        ENNReal.tsum_le_tsum fun k => Finset.sum_le_sum fun j _ => ediam_image_topBox_sq_le hG k j
    _ = ENNReal.ofReal (20 / Real.pi) *
          ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), volume (G '' bigBox R k j) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun k => (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (20 / Real.pi) * (6 * volume (G '' S)) := by gcongr
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top (by norm_num) hfin)

/-- The line shadow functions are measurable. -/
theorem measurable_lineShadow (hR : 0 < R) {g F : ℂ → ℂ}
    (hF : ContinuousOn F (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R))) (n : ℕ) :
    Measurable (lineShadow R g F n) := by
  have hmW : ∀ m, ∀ j ∈ Finset.range (2 ^ (n + m)), Measurable (lineW R g F (n + m) j) :=
    fun m j hj => (measurable_one.indicator (measurableSet_im_image_tent
      (ShadowNull.isCompact_image_tent hR hF (Finset.mem_range.1 hj)))).const_mul _
  exact Measurable.ennreal_tsum fun m => Finset.measurable_sum _ (hmW m)

/-- **Step 5.** For a chart `F` with finite shadow sum and `g` a chart (e.g. `e ∘ F`), the line
shadow functions `Φ_n(y)` tend to `0` for almost every height `y`. -/
theorem ae_tendsto_lineShadow {K K' : Set ℂ} {F g : ℂ → ℂ} (hF : IsChart K R F)
    (hSH : shadowSum R F < ⊤) (hg : IsChart K' R g) :
    ∀ᵐ y : ℝ, Tendsto (fun n => lineShadow R g F n y) atTop (𝓝 0) := by
  have hR := hF.pos
  set A := ∑' k : ℕ, ∑ j ∈ Finset.range (2 ^ k), ediam (g '' topBox R k j) ^ 2 with hA
  have hAt : A < ⊤ := tsum_ediam_topBox_sq_lt_top hg
  set T : ℕ → ℝ≥0∞ := fun n => ∑' m : ℕ, ShadowNull.shadowLevel R F (n + m) with hT
  have hTt : Tendsto T atTop (𝓝 0) :=
    (ENNReal.tendsto_sum_nat_add (ShadowNull.shadowLevel R F) hSH.ne).congr fun n =>
      tsum_congr fun m => by rw [Nat.add_comm]
  -- Young's inequality, level by level
  have hbound : ∀ n (t : ℝ≥0∞), ∫⁻ y, lineShadow R g F n y ≤ t * A + t⁻¹ * T n := by
    intro n t
    refine (lintegral_lineShadow_le hR hF.cont n).trans ?_
    have hAn : ∑' m : ℕ, ∑ j ∈ Finset.range (2 ^ (n + m)),
        ediam (g '' topBox R (n + m) j) ^ 2 ≤ A :=
      ENNReal.tsum_comp_le_tsum_of_injective (f := fun m => n + m) (add_right_injective n)
        (fun k => ∑ j ∈ Finset.range (2 ^ k), ediam (g '' topBox R k j) ^ 2)
    calc ∑' m : ℕ, ∑ j ∈ Finset.range (2 ^ (n + m)),
          2 * (ediam (g '' topBox R (n + m) j) * ediam (F '' tent R (n + m) j))
        ≤ ∑' m : ℕ, ∑ j ∈ Finset.range (2 ^ (n + m)),
          (t * ediam (g '' topBox R (n + m) j) ^ 2 + t⁻¹ * ediam (F '' tent R (n + m) j) ^ 2) :=
          ENNReal.tsum_le_tsum fun m => Finset.sum_le_sum fun j _ =>
            two_mul_mul_le_mul_sq_add_inv_mul_sq _ _ _
      _ = t * ∑' m : ℕ, ∑ j ∈ Finset.range (2 ^ (n + m)), ediam (g '' topBox R (n + m) j) ^ 2 +
          t⁻¹ * T n := by
          rw [hT, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          refine tsum_congr fun m => ?_
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          rfl
      _ ≤ t * A + t⁻¹ * T n := by gcongr
  -- the infimum has zero integral
  set Φ : ℝ → ℝ≥0∞ := fun y => ⨅ n, lineShadow R g F n y with hΦ
  have hΦm : Measurable Φ := Measurable.iInf fun n => measurable_lineShadow hR hF.cont n
  have hΦle : ∀ n (t : ℝ≥0∞), ∫⁻ y, Φ y ≤ t * A + t⁻¹ * T n := fun n t =>
    (lintegral_mono fun y => iInf_le _ n).trans (hbound n t)
  have hΦt : ∀ t : ℝ≥0∞, t⁻¹ ≠ ⊤ → ∫⁻ y, Φ y ≤ t * A := by
    intro t ht
    have hlim : Tendsto (fun n => t * A + t⁻¹ * T n) atTop (𝓝 (t * A + t⁻¹ * 0)) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hTt (Or.inr ht))
    rw [mul_zero, add_zero] at hlim
    exact ge_of_tendsto' hlim fun n => hΦle n t
  have hΦ0 : ∫⁻ y, Φ y = 0 := by
    have hlim : Tendsto (fun k : ℕ => (k : ℝ≥0∞)⁻¹ * A) atTop (𝓝 (0 * A)) :=
      ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hAt.ne)
    rw [zero_mul] at hlim
    exact le_antisymm (ge_of_tendsto' hlim fun k => hΦt _ (by simp)) zero_le
  have hae := (lintegral_eq_zero_iff hΦm).1 hΦ0
  filter_upwards [hae] with y hy
  have h := tendsto_atTop_iInf (antitone_lineShadow R g F y)
  rwa [show (⨅ n, lineShadow R g F n y) = 0 from hy] at h

end QuantumZipper.JS
