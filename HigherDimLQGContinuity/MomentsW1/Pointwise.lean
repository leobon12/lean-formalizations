import HigherDimLQGContinuity.MomentsW1.BallCover

/-! The almost-sure confined modulus before taking its moment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Metric HigherDimLFPP HigherDimLQGMetric.DGZ
open scoped ENNReal
open HigherDimLFPP.DGZ (cbox)

variable {d : ℕ}

theorem wnPointwise_constant (hd : 2 ≤ d) {b μ σ : ℝ}
    (hμ1 : μ ≤ 1) (hσ : 0 < σ) (hσμ : σ < μ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {κ : Rd d → ℝ}
      {Ω : Type*} [MeasurableSpace Ω]
      {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
      (_hH : IsDyadicRealization κ P W H) {ξ R Q CZ CN : ℝ}
      (_hξ : 0 ≤ ξ) (_hR : 1 ≤ R) (_hCN : 0 ≤ CN)
      {q : ℝ≥0∞} (_hq0 : 0 < q) (_hq1 : q < 1)
      {n : ℕ} {ω : Ω} (_hfinite : wnZRext (d := d) R Q CZ H ω ≠ ⊤),
      let s₀ : ℝ := (3*μ+5*σ)/8
      let F : ℝ := wnCoarseFactor (d := d) b R Q CZ H ω
      let a : ℝ := aQ P H ξ n 2⁻¹
      let G : ℝ := CN*F*a
      (∀ k, k ≤ n → wnEdgeCost P H ξ R Q CZ q n ω k ≤
        G*(2 : ℝ)^(-(s₀*k))) →
      (2 : ℝ)⁻¹ ^ n*wnSegmentCost H ξ R Q CZ n ω ≤
        G*(2 : ℝ)^(-(s₀*n)) →
      ∀ z ∈ closedBall (0 : Rd d) R, ∀ s ∈ Ioc (0 : ℝ) 1,
        ∀ x ∈ ball z s, ∀ y ∈ ball z s,
          lfppDistOn ξ (fun u => H n u ω) (ball z (3/2*s)) x y ≤
            K*G*((2 : ℝ)^(wnBadScale P H ξ R q n ω))^4*s^σ := by
  let s₀ : ℝ := (3*μ+5*σ)/8
  let s₁ : ℝ := (s₀+σ)/2
  let D : ℝ := 2*(2011:ℝ)^d+4004*Real.sqrt d
  have hσs₀ : σ < s₀ := (wnSlope_between hμ1 hσμ).1
  have hs₀1 : s₀ ≤ 1 := (wnSlope_between hμ1 hσμ).2.le
  have hσ1 : σ ≤ 1 := by linarith
  have hσs₁ : σ < s₁ := by dsimp [s₁]; linarith
  have hs₁s₀ : s₁ < s₀ := by dsimp [s₁]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨K₀, hK₀, hscale⟩ := wnScale_diameter_bound d hσ hσ1 hσs₁ hs₁s₀ hs₀1 hD
  let K : ℝ := (wnBallLinks d:ℝ)*K₀
  have hK : 0 < K := mul_pos (by exact_mod_cast wnBallLinks_pos d) hK₀
  refine ⟨K, hK, ?_⟩
  intro κ Ω _ P W H hH ξ R Q CZ CN hξ hR hCN q hq0 hq1 n ω hfinite
  dsimp only
  intro hcost hterminal z hz s hs x hx y hy
  let M : ℕ := wnBadScale P H ξ R q n ω
  let F : ℝ := wnCoarseFactor (d := d) b R Q CZ H ω
  let a : ℝ := aQ P H ξ n 2⁻¹
  let G : ℝ := CN*F*a
  have ha : 0 < a := tight_aQ_pos (by omega : 0 < d) hH ξ n
    (by norm_num) (by norm_num)
  have hF : 0 < F := wnCoarseFactor_pos b R Q CZ H ω
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hterm : (n : ℝ)^2*(2 : ℝ)⁻¹ ^ n*wnSegmentCost H ξ R Q CZ n ω ≤
      G*((n : ℝ)^2*(2 : ℝ)^(-(s₀*n))) := by
    have hm := mul_le_mul_of_nonneg_left hterminal (by positivity : 0 ≤ (n:ℝ)^2)
    nlinarith
  have hseg : wnSegmentCost H ξ R Q CZ n ω ≤
      G*(2 : ℝ)^((1-s₀)*(n:ℝ)) :=
    wnNorm_terminal_cancel n hterminal
  have hφ : Continuous (fun u => H n u ω) := (hH.band n).continuous ω
  have hcube : ∀ w ∈ cbox (0 : Rd d) (R+1), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      selfDiam ξ (fun u => H n u ω) w ρ ≤
        K₀*G*((2 : ℝ)^M)^4*ρ^σ := by
    intro w hw ρ hρ hρ1
    obtain ⟨hchain,hsegment⟩ := wnCube_chain hd hH hξ hq0 hq1 hfinite hw hρ hρ1
    have hchain' : ∀ j, M ≤ j → wnStartScale ρ hρ ≤ j → j ≤ n →
        selfDiam ξ (fun u => H n u ω) w ρ ≤
          (2*ρ*(2 : ℝ)^j+2)*D*
            wnLocalChain_sum d j n (wnEdgeCost P H ξ R Q CZ q n ω)
              (wnSegmentCost H ξ R Q CZ n ω) := by
      intro j hMj hjδ hjn
      exact hchain j hMj (wnStartScale_delta_le ρ hρ hjδ) hjn
    have hc : ∀ k, M ≤ k → k < n →
        wnEdgeCost P H ξ R Q CZ q n ω k ≤ G*(2 : ℝ)^(-(s₀*k)) :=
      fun k _ hkn => hcost k hkn.le
    exact hscale hρ hρ1 hG hchain' hsegment hc hterm hseg
  have hB : 0 ≤ K₀*G*((2 : ℝ)^M)^4 := by positivity
  have hball := wnBall_of_cubes hd hφ hσ hR hB hcube hz hs.1 hs.2 hx hy
  change lfppDistOn ξ (fun u => H n u ω) (ball z (3/2*s)) x y ≤
    K*G*((2 : ℝ)^M)^4*s^σ
  calc
    lfppDistOn ξ (fun u => H n u ω) (ball z (3/2*s)) x y ≤
      (wnBallLinks d:ℝ)*(K₀*G*((2 : ℝ)^M)^4)*s^σ := hball
    _ = K*G*((2 : ℝ)^M)^4*s^σ := by dsimp [K]; ring

end HigherDimLQGContinuity
