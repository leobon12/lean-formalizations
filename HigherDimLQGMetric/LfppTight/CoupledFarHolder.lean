import HigherDimLQGMetric.LfppTight.FarMedian
import HigherDimLQGMetric.LfppTight.CoupledProb
import HigherDimLQGMetric.LfppTight.HighFieldTail
import HigherDimLQGMetric.DGZ.AdapterFixed
import HigherDimLQGMetric.DGZ.Crossing

/-! Hölder tails for the coupled field with cutoffs bounded away from zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

private theorem l6a_norm_le_power {d : ℕ} {r β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) r)
    (hy : y ∈ closedBall (0 : Rd d) r) :
    ‖x - y‖ ≤ max 1 (2 * r) * ‖x - y‖ ^ β := by
  have hxn : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hyn : ‖y‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hdist : ‖x - y‖ ≤ 2 * r := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * r := by linarith
  by_cases ht : ‖x - y‖ ≤ 1
  · have hh := Real.self_le_rpow_of_le_one (norm_nonneg (x - y)) ht hβ1
    exact hh.trans (le_mul_of_one_le_left (Real.rpow_nonneg (norm_nonneg _) _) (le_max_left _ _))
  · have ht1 : 1 ≤ ‖x - y‖ := le_of_not_ge ht
    have hpow : 1 ≤ ‖x - y‖ ^ β := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le ht1 hβ0.le
    calc
      ‖x - y‖ ≤ max 1 (2 * r) := hdist.trans (le_max_right _ _)
      _ ≤ max 1 (2 * r) * ‖x - y‖ ^ β :=
        le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) hpow

theorem l6a_coupled_holder_far {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z))
    {a₀ r θ : ℝ} (ha₀ : 0 < a₀) (ha₀1 : a₀ < 1)
    (hr : 0 < r) (hθ : 0 < θ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε ∈ Ico a₀ 1,
      P {ω | ∃ x ∈ closedBall (0 : Rd d) r, ∃ y ∈ closedBall (0 : Rd d) r,
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
          DGZ.lfppMetric ξ (fun z => G ε z ω -
            W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ≤
        ENNReal.ofReal θ := by
  have hd : 0 < d := by have := hDGZ.dim; omega
  have hq : 0 < θ / 3 := by positivity
  obtain ⟨t, ht, hmed⟩ := l6a_aHat_lower_far hDGZ W hW G hG ha₀ ha₀1
  obtain ⟨L, hL0, hGtail⟩ := DGZ.adapter_fixed_band_sup hd hDGZ.kernel
    ha₀ ha₀1.le (R := r + 2) (θ := θ / 3) (by linarith) hq
  obtain ⟨C, hC0, hCtail⟩ := l6a_uniform_sphereBand_tail_at hDGZ.dim
    hDGZ.kernel P W hW hq
  obtain ⟨T, hT0, hTtail⟩ := l6a_exists_highField_sup_tail
    P Ψ hΨc hΨm (R := r + 1) hq
  let A : ℝ := Real.exp (ξ * (L + C + T)) * max 1 (2 * r)
  let M : ℝ := A / t
  have hM : 0 ≤ M := by dsimp [M, A]; positivity
  refine ⟨M, hM, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := ha₀.trans_le hε.1
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, hε.2⟩
  let E₁ : Set Ω := {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) (r + 2),
    L < |G ε z ω|}
  let E₂ : Set Ω := {ω | C < |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω|}
  let E₃ : Set Ω := {ω | T < l6a_highNorm Ψ hΨc (r + 1) ω}
  have hsub : {ω | ∃ x ∈ closedBall (0 : Rd d) r,
      ∃ y ∈ closedBall (0 : Rd d) r,
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
          DGZ.lfppMetric ξ (fun z => G ε z ω -
            W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ⊆
      E₁ ∪ E₂ ∪ E₃ := by
    intro ω hω
    by_contra hn
    obtain ⟨x, hx, y, hy, hxy⟩ := hω
    have hno₁ : ω ∉ E₁ := fun he => hn (Or.inl (Or.inl he))
    have hno₂ : ω ∉ E₂ := fun he => hn (Or.inl (Or.inr he))
    have hno₃ : ω ∉ E₃ := fun he => hn (Or.inr he)
    have hΦc : Continuous (fun z : Rd d => G ε z ω -
        W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) :=
      ((hG ε hε1).continuous ω).sub continuous_const |>.add (hΨc ω)
    have hxU : x ∈ ball (0 : Rd d) (r + 1) :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))
    have hyU : y ∈ ball (0 : Rd d) (r + 1) :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith))
    have hfield : ∀ z ∈ ball (0 : Rd d) (r + 1),
        ξ * (G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) ≤
          ξ * (L + C + T) := by
      intro z hz
      have hzU : z ∈ HigherDimLFPP.DGZ.obox (0 : Rd d) (r + 2) :=
        DGZ.adapter_closedBall_subset_obox (by linarith : r + 1 < r + 2)
          (ball_subset_closedBall hz)
      have hzG : z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) (r + 2) :=
        HigherDimLFPP.DGZ.obox_subset_cbox _ _ hzU
      have hG' : |G ε z ω| ≤ L := le_of_not_gt (fun he => hno₁ ⟨z, hzG, he⟩)
      have hc : |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω| ≤ C :=
        le_of_not_gt hno₂
      have hΨ : |Ψ z ω| ≤ T :=
        (l6a_abs_highField_le_norm Ψ hΨc (r + 1) ω
          (ball_subset_closedBall hz)).trans (le_of_not_gt hno₃)
      nlinarith [hDGZ.xi_pos, (abs_le.mp hG').2, (abs_le.mp hc).1,
        (abs_le.mp hΨ).2]
    have hbound := DGZ.lfppDistOn_le_exp_mul_norm_of_convex hΦc
      (convex_ball (0 : Rd d) (r + 1)) hxU hyU hfield
    have hjoin : HigherDimLFPP.PcwJoined (ball (0 : Rd d) (r + 1)) x y :=
      HigherDimLFPP.PcwJoined.of_convex (convex_ball (0 : Rd d) (r + 1)) hxU hyU
    have hdist : DGZ.lfppMetric ξ (fun z => G ε z ω -
        W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y ≤
        A * ‖x - y‖ ^ β := by
      calc
        _ ≤ HigherDimLFPP.lfppDistOn ξ (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
            (ball 0 (r + 1)) x y := DGZ.lfppMetric_le_lfppDistOn hjoin
        _ ≤ Real.exp (ξ * (L + C + T)) * ‖y - x‖ := hbound
        _ ≤ A * ‖x - y‖ ^ β := by
          rw [norm_sub_rev]
          change Real.exp (ξ * (L + C + T)) * ‖x - y‖ ≤
            Real.exp (ξ * (L + C + T)) * max 1 (2 * r) * ‖x - y‖ ^ β
          calc
            _ ≤ Real.exp (ξ * (L + C + T)) *
                (max 1 (2 * r) * ‖x - y‖ ^ β) :=
                  mul_le_mul_of_nonneg_left (l6a_norm_le_power hβ0 hβ1 hx hy)
                    (Real.exp_pos _).le
            _ = _ := by ring
    have hcoef : A ≤ M * DGZ.aHat P G ξ ε := by
      dsimp [M]
      calc
        A = (A / t) * t := by field_simp
        _ ≤ (A / t) * DGZ.aHat P G ξ ε :=
          mul_le_mul_of_nonneg_left (hmed ε hε) (div_nonneg (by dsimp [A]; positivity) ht.le)
    have hpow : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    have hle : A * ‖x - y‖ ^ β ≤
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β :=
      mul_le_mul_of_nonneg_right hcoef hpow
    exact (not_le_of_gt hxy) (hdist.trans hle)
  have h1 : P E₁ ≤ ENNReal.ofReal (θ / 3) := hGtail hW hε.1 hε.2.le (hG ε hε1)
  have h2 : P E₂ ≤ ENNReal.ofReal (θ / 3) := hCtail ε hε1
  have h3 : P E₃ ≤ ENNReal.ofReal (θ / 3) := hTtail
  calc
    P {ω | ∃ x ∈ closedBall (0 : Rd d) r, ∃ y ∈ closedBall (0 : Rd d) r,
      M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
        DGZ.lfppMetric ξ (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ≤
        P (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub
    _ ≤ P E₁ + P E₂ + P E₃ := by
      calc
        P (E₁ ∪ E₂ ∪ E₃) ≤ P (E₁ ∪ E₂) + P E₃ := measure_union_le _ _
        _ ≤ P E₁ + P E₂ + P E₃ := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 3) + ENNReal.ofReal (θ / 3) +
          ENNReal.ofReal (θ / 3) := by gcongr
    _ = ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add hq.le hq.le,
        ← ENNReal.ofReal_add (add_nonneg hq.le hq.le) hq.le]
      congr 1
      ring

end HigherDimLQGMetric
