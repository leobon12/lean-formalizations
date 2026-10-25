import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1ActualMoment
import LQGMetric.Papers.DDDF.T20CHol

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

private theorem nearIdx_nonempty (K : ℕ) : (T20B.nearIdx K).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp only [T20B.nearIdx, Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor <;> norm_num

def laneCJ1MaxPositiveLog (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) (ω : Ω) : ℝ :=
  (T20B.nearIdx K).sup' (nearIdx_nonempty K)
    (fun b => laneCJ1PositiveLog Qψ ξ P W hW n K m b ω)

theorem laneC_aemeasurable_J1MaxPositiveLog
    (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) :
    AEMeasurable (laneCJ1MaxPositiveLog Qψ ξ P W hW n K m) P := by
  exact T20C.aemeasurable_sup'_fun (nearIdx_nonempty K)
    (fun b _ => laneC_aemeasurable_J1PositiveLog P W hW Qψ ξ n K m b)

universe u

 

theorem laneC_J1_max_positive_log_moment_of_J1_input
    (Qψ : PsiParams) (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ l : ℝ, 0 < l →
          ∫⁻ ω, ENNReal.ofReal (Real.exp
            (l * laneCJ1MaxPositiveLog Qψ (ξ : ℝ) P W hW n K m ω)) ∂P ≤
          ENNReal.ofReal (Real.exp
            (l * max (laneCLogMin Qψ K)
              (T20B.tailX0 l c₀ ((5 : ℝ) ^ K)
                (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, htail⟩ :=
    laneC_positive_log_tail_of_J1_input Qψ hJ1 ξ C p hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ l hl
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let X : Ω → ℝ := laneCJ1MaxPositiveLog Qψ (ξ : ℝ) P W hW n K m
  have hX0 : ∀ ω, 0 ≤ X ω := by
    intro ω
    obtain ⟨b, hb⟩ := nearIdx_nonempty K
    exact (Real.log_nonneg (le_max_left _ _)).trans
      (Finset.le_sup' (s := T20B.nearIdx K) (f := fun b =>
        laneCJ1PositiveLog Qψ (ξ : ℝ) P W hW n K m b ω) hb)
  have hXm : AEMeasurable X P :=
    laneC_aemeasurable_J1MaxPositiveLog Qψ (ξ : ℝ) P W hW n K m
  have ha : 0 < (K : ℝ) ^ (3 * Qψ.ε₀) := by positivity
  have hMin2 : 2 ≤ laneCLogMin Qψ K := by
    unfold laneCLogMin
    exact (by norm_num : (2 : ℝ) ≤ 3).trans (le_max_left _ _)
  have hT : ∀ t, laneCLogMin Qψ K < t →
      (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < Real.exp (t / 2) := by
    intro t ht
    have hbase : 0 < (2 : ℝ) ^
        ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) := by positivity
    have hlt : 2 * Real.log ((2 : ℝ) ^
        ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀))) + 1 < t :=
      (le_max_right _ _).trans_lt ht
    have hlog : Real.log ((2 : ℝ) ^
        ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀))) < t / 2 := by
      linarith
    rw [← Real.exp_log hbase]
    exact Real.exp_lt_exp.mpr hlog
  have htailX : ∀ t, laneCLogMin Qψ K < t →
      P {ω | t ≤ X ω} ≤ ENNReal.ofReal
        (c₀ * (5 : ℝ) ^ K * Real.exp
          (-(c₁ * (t / 2) ^ 2 /
            ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (t / 2))))) := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt (by linarith [hMin2] :
      0 ≤ laneCLogMin Qψ K) ht
    have hsub : {ω | t ≤ X ω} ⊆ {ω | ∃ b ∈ T20B.nearIdx K,
        t ≤ laneCJ1PositiveLog Qψ (ξ : ℝ) P W hW n K m b ω} := by
      intro ω hω
      exact (Finset.le_sup'_iff (nearIdx_nonempty K)).mp hω
    exact (measure_mono hsub).trans (by
      simpa only [X, laneCJ1PositiveLog] using
        htail P W hW n K m hK hKn hmK hmlo hmhi hΛ t ht0 (hT t ht))
  exact laneC_exp_moment_of_half_log_tail hX0 hXm
    hl hc₀.le (by positivity : 0 < (5 : ℝ) ^ K) hc₁ ha hMin2 htailX

end SupercriticalLQGUniqueness.B2.DG20Conc
