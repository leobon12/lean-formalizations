import HigherDimLQGContinuity.MomentsW1.CubeChain

/-! Uniform comparison of chain costs with the median normalizer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set HigherDimLFPP HigherDimLQGMetric HigherDimLQGMetric.DGZ
open scoped ENNReal

variable {d : ℕ}

/-- Random factor contributed by the coarse envelope. -/
def wnCoarseFactor {Ω : Type*} [MeasurableSpace Ω]
    (b R Q CZ : ℝ) (H : ℕ → Rd d → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (b*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω))

theorem wnCoarseFactor_pos {Ω : Type*} [MeasurableSpace Ω]
    (b R Q CZ : ℝ) (H : ℕ → Rd d → Ω → ℝ) (ω : Ω) :
    0 < wnCoarseFactor (d := d) b R Q CZ H ω := Real.exp_pos _

private theorem wnCoarseFactor_mono {Ω : Type*} [MeasurableSpace Ω]
    {b ξ R Q CZ : ℝ} (hξb : ξ ≤ b) (hCZ : 0 ≤ CZ) (hR : 1 ≤ R)
    (H : ℕ → Rd d → Ω → ℝ) (ω : Ω) :
    Real.exp (ξ*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω)) ≤
      wnCoarseFactor (d := d) b R Q CZ H ω := by
  have hlog : 0 ≤ Real.log (2+R) := Real.log_nonneg (by linarith)
  have hZ : 0 ≤ wnZR (d := d) R Q CZ H ω := ENNReal.toReal_nonneg
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hξb)
    (add_nonneg (mul_nonneg hCZ hlog) hZ)]

private theorem wnEdgeCost_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R Q CZ : ℝ) (q : ℝ≥0∞) (n k : ℕ) (ω : Ω) :
    wnEdgeCost P H ξ R Q CZ q n ω k =
      Real.exp (ξ*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω)) *
        ((2 : ℝ)⁻¹ ^ k * Real.exp (ξ*(Q*k*Real.log 2)) *
          aQ P H ξ (n-k) q) := by
  unfold wnEdgeCost
  have hexp : Real.exp (ξ*(Q*k*Real.log 2+CZ*Real.log (2+R)+
      wnZR (d := d) R Q CZ H ω)) =
      Real.exp (ξ*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω)) *
      Real.exp (ξ*(Q*k*Real.log 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

private theorem wnSegmentCost_split {Ω : Type*} [MeasurableSpace Ω]
    (H : ℕ → Rd d → Ω → ℝ) (ξ R Q CZ : ℝ) (n : ℕ) (ω : Ω) :
    wnSegmentCost H ξ R Q CZ n ω =
      Real.exp (ξ*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω)) *
        Real.exp (ξ*(Q*n*Real.log 2)) := by
  unfold wnSegmentCost
  rw [← Real.exp_add]
  congr 1
  ring

/-- Uniform normalized costs, with all dependence on the realization in one coarse factor. -/
theorem wnNormalized_costs {κ : Rd d → ℝ}
    (hE : UExpRate d κ) (h52 : UCor52Shape d κ) (hQ : UQuantCompShape d κ)
    {b μ σ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hσμ : σ < μ)
    {q q' : ℝ≥0∞} (hq0 : 0 < q) (hqq' : q < q') (hq'1 : q' < 1) :
    ∃ CN : ℝ, 0 < CN ∧ ∀ (ξ : ℝ), UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ (n : ℕ) (R CZ : ℝ),
        1 ≤ R → 0 ≤ CZ → ∀ ω : Ω,
        let Q : ℝ := Real.sqrt (2 * d)+(μ-σ)/(2*b)
        let s₀ : ℝ := (3*μ+5*σ)/8
        let G : ℝ := CN*wnCoarseFactor b R Q CZ H ω*aQ P H ξ n 2⁻¹
        (∀ k : ℕ, k ≤ n → wnEdgeCost P H ξ R Q CZ q n ω k ≤
          G*(2 : ℝ)^(-(s₀*k))) ∧
        (2 : ℝ)⁻¹ ^ n*wnSegmentCost H ξ R Q CZ n ω ≤
          G*(2 : ℝ)^(-(s₀*n)) := by
  let ε : ℝ := (μ-σ)/8
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hhalf0 : (0:ℝ≥0∞) < 2⁻¹ := by norm_num
  have hhalf1 : (2⁻¹:ℝ≥0∞) < 1 := by norm_num
  have hq'0 : 0 < q' := hq0.trans hqq'
  obtain ⟨C₁, hC₁, h52'⟩ := h52 b μ hb hμ ε hε q q' hq0 hqq' hq'1
  obtain ⟨C₂, hC₂, hQ'⟩ := hQ b μ hb hμ q' 2⁻¹ hq'0 hq'1 hhalf0 hhalf1
  obtain ⟨N, C₃, hC₃, hE'⟩ := hE b ε hb hε 2⁻¹ hhalf0 hhalf1
  let CN : ℝ := C₁*C₂+C₃+1
  have hCN : 0 < CN := by dsimp [CN]; positivity
  have hC₁₂ : 0 ≤ C₁*C₂ := mul_nonneg hC₁.le hC₂.le
  have hC₁₂CN : C₁*C₂ ≤ CN := by dsimp [CN]; linarith
  have hC₃CN : C₃ ≤ CN := by dsimp [CN]; linarith
  refine ⟨CN, hCN, ?_⟩
  intro ξ hξ Ω _ P W H hH n R CZ hR hCZ ω
  let Q : ℝ := Real.sqrt (2 * d)+(μ-σ)/(2*b)
  let s₀ : ℝ := (3*μ+5*σ)/8
  let w : ℝ := aQ P H ξ n 2⁻¹
  let F : ℝ := wnCoarseFactor b R Q CZ H ω
  let X : ℝ := Real.exp (ξ*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω))
  have hw : 0 < w := tight_aQ_pos (by have := hξ.base.dim; omega : 0 < d)
    hH ξ n hhalf0 hhalf1
  have hF : 0 < F := wnCoarseFactor_pos b R Q CZ H ω
  have hX : 0 < X := Real.exp_pos _
  have hXF : X ≤ F := wnCoarseFactor_mono hξ.le_b hCZ hR H ω
  have hslope : s₀ ≤ ξ*(distExp d ξ-Q)-ε := by
    simpa only [s₀, Q, ε] using wnSlope_lower hb hσμ hξ.le_b hξ.gap
  have hEξ := hE' ξ hξ.base.xi_pos hξ.le_b Ω P W H hH
  have hlow : C₃⁻¹*(2 : ℝ)^(-((1-ξ*distExp d ξ+ε)*n)) ≤ w :=
    (hEξ.2 n).1
  have hterminal := wnNorm_terminal_bound n hC₃ hlow hslope
  have hterminal' : (2 : ℝ)⁻¹ ^ n*wnSegmentCost H ξ R Q CZ n ω ≤
      CN*F*w*(2 : ℝ)^(-(s₀*n)) := by
    have hsplit : wnSegmentCost H ξ R Q CZ n ω = X*Real.exp (ξ*(Q*n*Real.log 2)) :=
      wnSegmentCost_split H ξ R Q CZ n ω
    have ht0 : 0 ≤ (2 : ℝ)⁻¹ ^ n*Real.exp (ξ*(Q*n*Real.log 2)) := by positivity
    have hp0 : 0 ≤ (2 : ℝ)^(-(s₀*n))*w := by positivity
    calc
      (2 : ℝ)⁻¹ ^ n*wnSegmentCost H ξ R Q CZ n ω =
          X*((2 : ℝ)⁻¹ ^ n*Real.exp (ξ*(Q*n*Real.log 2))) := by rw [hsplit]; ring
      _ ≤ X*(C₃*(2 : ℝ)^(-(s₀*n))*w) :=
        mul_le_mul_of_nonneg_left hterminal hX.le
      _ ≤ F*(C₃*(2 : ℝ)^(-(s₀*n))*w) :=
        mul_le_mul_of_nonneg_right hXF (by positivity)
      _ = C₃*(F*w*(2 : ℝ)^(-(s₀*n))) := by ring
      _ ≤ CN*(F*w*(2 : ℝ)^(-(s₀*n))) :=
        mul_le_mul_of_nonneg_right hC₃CN (by positivity)
      _ = CN*F*w*(2 : ℝ)^(-(s₀*n)) := by ring
  refine ⟨?_, ?_⟩
  · intro k hkn
    have hcor := h52' ξ hξ Ω P W H hH n k hkn
    have hcomp := hQ' ξ hξ Ω P W H hH n
    have hscale : (2 : ℝ)⁻¹ ^ k*Real.exp (ξ*(Q*k*Real.log 2))*aQ P H ξ (n-k) q ≤
        (C₁*C₂)*(2 : ℝ)^(-(s₀*k))*w :=
      wnNorm_edge_bound k hC₁.le hC₂.le hcor hcomp hw.le hslope
    have hsplit : wnEdgeCost P H ξ R Q CZ q n ω k =
        X*((2 : ℝ)⁻¹ ^ k*Real.exp (ξ*(Q*k*Real.log 2))*aQ P H ξ (n-k) q) :=
      wnEdgeCost_split P H ξ R Q CZ q n k ω
    have hpos : 0 ≤ (C₁*C₂)*(2 : ℝ)^(-(s₀*k))*w := by positivity
    change wnEdgeCost P H ξ R Q CZ q n ω k ≤
      CN*F*w*(2 : ℝ)^(-(s₀*k))
    calc
      wnEdgeCost P H ξ R Q CZ q n ω k =
          X*((2 : ℝ)⁻¹ ^ k*Real.exp (ξ*(Q*k*Real.log 2))*aQ P H ξ (n-k) q) := hsplit
      _ ≤ X*((C₁*C₂)*(2 : ℝ)^(-(s₀*k))*w) :=
        mul_le_mul_of_nonneg_left hscale hX.le
      _ ≤ F*((C₁*C₂)*(2 : ℝ)^(-(s₀*k))*w) :=
        mul_le_mul_of_nonneg_right hXF hpos
      _ = (C₁*C₂)*(F*w*(2 : ℝ)^(-(s₀*k))) := by ring
      _ ≤ CN*(F*w*(2 : ℝ)^(-(s₀*k))) :=
        mul_le_mul_of_nonneg_right hC₁₂CN (by positivity)
      _ = CN*F*w*(2 : ℝ)^(-(s₀*k)) := by ring
  · exact hterminal'

end HigherDimLQGContinuity
