import HigherDimLQGMetric.LfppTight.CrossHolderShell
import HigherDimLQGMetric.LfppTight.CoupledHolderAll
import HigherDimLQGMetric.LfppTight.CoupledShellTail
import HigherDimLQGMetric.LfppTight.CoupledLaw

/-! Unit-scale crossing for the coupled centred convolution field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

theorem l6a_coupled_unitCross {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z))
    {p C : ℝ} (hp : p < 1) (hC : 0 < C) :
    ∃ b ε₀ : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        ENNReal.ofReal p ≤ P {ω |
          supPairs (fun q : Rd d × Rd d =>
            DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω) q.1 q.2)
            (ball (0 : Rd d) b) ≤
              ENNReal.ofReal C⁻¹ * infPairs
                (fun q : Rd d × Rd d =>
                  DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω) q.1 q.2)
                (sphere 0 b) (sphere 0 1)} := by
  by_cases hp0 : p ≤ 0
  · refine ⟨1 / 4, 1 / 2, by norm_num, le_rfl, by norm_num, le_rfl,
      fun ε hε => ?_⟩
    simp only [ENNReal.ofReal_eq_zero.mpr hp0]
    exact bot_le
  have hp0' : 0 < p := lt_of_not_ge hp0
  let q : ℝ := (1 - p) / 4
  have hq : 0 < q := by dsimp [q]; linarith
  have hd0 : 0 < d := by have := hDGZ.dim; omega
  have hgap : 0 < ξ * (Q - Real.sqrt (2 * d)) :=
    mul_pos hDGZ.xi_pos (by linarith [hDGZ.subcritical])
  let β : ℝ := min (1 / 2) (ξ * (Q - Real.sqrt (2 * d)) / 2)
  have hβ0 : 0 < β := lt_min (by norm_num) (by positivity)
  have hβ1 : β ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hβ : β < ξ * (Q - Real.sqrt (2 * d)) :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨M, hM, hHolder⟩ := l6a_coupled_holder_all hDGZ hAdapter
    hβ0 hβ1 hβ P W hW G hG Ψ hΨc hΨm
    (r := 1) (θ := q) (by norm_num) hq
  obtain ⟨m, εs, hm, hεs, hShell⟩ := l6a_coupled_shell_tail
    hDGZ hAdapter hβ0 hβ P W hW G hG Ψ hΨc hΨm hq
  let M' : ℝ := max M 1
  have hM' : 0 ≤ M' := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  obtain ⟨b, hb, hb4, hbsmall⟩ := l6a_exists_small_ball
    (M := M') hm hC hβ0
  let ε₀ : ℝ := min εs (1 / 2)
  have hε₀ : 0 < ε₀ := lt_min hεs (by norm_num)
  refine ⟨b, ε₀, hb, hb4, hε₀, min_le_right _ _, ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  have hεs' : ε ∈ Ioo (0 : ℝ) εs :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have ha : 0 < DGZ.aHat P G ξ ε :=
    DGZ.aHat_pos hd0 hW (hG ε hε1) ξ
  let H : Rd d → Ω → ℝ := l6a_coupledPhi κ W G Ψ ε
  let E₁ : Set Ω := {ω | ∃ x ∈ closedBall (0 : Rd d) 1,
    ∃ y ∈ closedBall (0 : Rd d) 1,
      M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β < DGZ.lfppMetric ξ (H · ω) x y}
  let E₂ : Set Ω := {ω | DGZ.lfppSetDist ξ (H · ω) univ
    (sphere (0 : Rd d) (1 / 2)) (sphere 0 1) ≤
      m * DGZ.aHat P G ξ ε}
  let E : Set Ω := {ω | supPairs
    (fun q : Rd d × Rd d => DGZ.lfppMetric ξ (H · ω) q.1 q.2)
    (ball (0 : Rd d) b) ≤ ENNReal.ofReal C⁻¹ * infPairs
      (fun q : Rd d × Rd d => DGZ.lfppMetric ξ (H · ω) q.1 q.2)
      (sphere 0 b) (sphere 0 1)}
  have hsub : (E₁ ∪ E₂)ᶜ ⊆ E := by
    intro ω hω
    have hno₁ : ω ∉ E₁ := fun he => hω (Or.inl he)
    have hno₂ : ω ∉ E₂ := fun he => hω (Or.inr he)
    have hH : Continuous fun z => H z ω :=
      ((hG ε hε1).continuous ω).sub continuous_const |>.add (hΨc ω)
    have hhold : ∀ x ∈ closedBall (0 : Rd d) 1,
        ∀ y ∈ closedBall (0 : Rd d) 1,
          DGZ.lfppMetric ξ (H · ω) x y ≤
            M' * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β := by
      intro x hx y hy
      have hMxy : DGZ.lfppMetric ξ (H · ω) x y ≤
          M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β :=
        le_of_not_gt fun hn => hno₁ ⟨x, hx, y, hy, hn⟩
      exact hMxy.trans (by
        have hpown : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le) hpown)
    have hs : m * DGZ.aHat P G ξ ε < DGZ.lfppSetDist ξ (H · ω) univ
        (sphere (0 : Rd d) (1 / 2)) (sphere 0 1) :=
      lt_of_not_ge hno₂
    exact l6a_cross_of_holder_shell ξ (H · ω) hH ha hM'
      hβ0 hb hb4 hC hbsmall hhold hs
  have hbad : P (E₁ ∪ E₂) ≤ ENNReal.ofReal q + ENNReal.ofReal q :=
    (measure_union_le _ _).trans (add_le_add (hHolder ε hε1) (hShell ε hεs'))
  have hsum : (1 : ℝ≥0∞) ≤ P E + ENNReal.ofReal q + ENNReal.ofReal q := by
    calc
      (1 : ℝ≥0∞) = P ((E₁ ∪ E₂)ᶜ ∪ (E₁ ∪ E₂)) := by
        rw [compl_union_self, measure_univ]
      _ ≤ P (E₁ ∪ E₂)ᶜ + P (E₁ ∪ E₂) := measure_union_le _ _
      _ ≤ P E + (ENNReal.ofReal q + ENNReal.ofReal q) := by gcongr
      _ = _ := by ac_rfl
  have hqsum : ENNReal.ofReal p + ENNReal.ofReal q + ENNReal.ofReal q ≤ 1 := by
    rw [← ENNReal.ofReal_add hp0'.le hq.le,
      ← ENNReal.ofReal_add (add_nonneg hp0'.le hq.le) hq.le,
      ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    dsimp [q]
    linarith
  exact (ENNReal.add_le_add_iff_right (show
    ENNReal.ofReal q + ENNReal.ofReal q ≠ ⊤ by simp)).mp
      (show ENNReal.ofReal p + (ENNReal.ofReal q + ENNReal.ofReal q) ≤
        P E + (ENNReal.ofReal q + ENNReal.ofReal q) by
        calc
          _ = ENNReal.ofReal p + ENNReal.ofReal q + ENNReal.ofReal q := by ac_rfl
          _ ≤ 1 := hqsum
          _ ≤ P E + ENNReal.ofReal q + ENNReal.ofReal q := hsum
          _ = _ := by ac_rfl)

end HigherDimLQGMetric
