import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSourceL2Rate
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNormalizeConditional

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
universe u

private theorem laneC_nearIdx_nonempty (K : ℕ) : (T20B.nearIdx K).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp only [T20B.nearIdx, Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor <;> norm_num

 

def laneCNormalizedAroundProduct
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (ξ p : ℝ) (n K m : ℕ) (b : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    ((lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) x)⁻¹) ^ p *
    ((lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z x)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
      (LaneCInputs.sourceAround K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b)) ^ p
    ∂(condExpKernel P (MeasurableSpace.comap
      (fun y z => psiMN Qψ W P K n z y)
      (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)

 


theorem laneC_normalized_around_max_L2_of_B3_J1_inputs
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    (hB3 : LaneCInputs.B3SubaddTails.{u} Qψ)
    (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (C p₀ δ p ζ ν : ℝ) (hC : 0 < C)
    (hp₀ : 0 < p₀) (hp₀2 : p₀ < 2⁻¹)
    (hδ : 0 < δ) (hp : 0 < p) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hν : 0 < ν) :
    ∃ K₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p₀) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
      let q : ℝ := 2 * ((1 + ζ) / ζ)
      let t : ℝ := ζ / (2 * (1 + ζ))
      let a : ℝ := laneCB3Scale (ξ : ℝ) Q δ P W n K
      let G : ℝ≥0∞ := (ENNReal.ofReal
        (Real.exp (((K : ℝ) * Real.log 2) *
          (((1 + ζ) * p * (ξ : ℝ)) ^ 2) / 2))) ^ (1 / (1 + ζ))
      (∫⁻ ω, ((T20B.nearIdx K).sup' (laneC_nearIdx_nonempty K)
        (fun b => laneCNormalizedAroundProduct P W hW Qψ (ξ : ℝ)
          p n K m b ω)) ^ (2 : ℝ) ∂P) ≤
        (ENNReal.ofReal a ^ p)⁻¹ ^ (2 : ℝ) *
        ((ENNReal.ofReal (Real.exp (ν * K) + 1)) ^ (2 * t) *
          (ENNReal.ofReal
            (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ (p * q)) *
            ENNReal.ofReal (Real.exp (ν * K) + 1)) ^ (2 * t) *
          G ^ (2 : ℝ)) := by
  obtain ⟨K₀, hrate⟩ := laneC_source_product_L2_rate_of_B3_J1_inputs
    Qψ hε hB3 hJ1 ξ Q hQ C p₀ δ p ζ ν hC hp₀ hp₀2 hδ hp hζ hζ1 hν
  refine ⟨K₀, ?_⟩
  intro Ω mΩ _ P _ W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  let a : ℝ := laneCB3Scale (ξ : ℝ) Q δ P W n K
  have ha : 0 < a := by
    dsimp [a, laneCB3Scale]
    exact mul_pos (by positivity) (lambdaN_pos hW (n - K))
  have hc0 : ENNReal.ofReal a ^ p ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr ha) hp.le)
  have hcTop : ENNReal.ofReal a ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have hL (x : Ω) : 0 < lenObs (ξ : ℝ) (psiMN Qψ W P 0 n)
      (rectAB 1 1) x :=
    lenObs_pos ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont)
      _ (by norm_num [rectAB]) (by norm_num [rectAB])
        (by norm_num [MarkedRect.crossWidth, rectAB]) x
  let κ := condExpKernel P (MeasurableSpace.comap
    (fun y z => psiMN Qψ W P K n z y)
    (inferInstance : MeasurableSpace (ℂ → ℝ)))
  let R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (a / lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) x)
  let D (b : ℤ × ℤ) (x : Ω) :=
    (lfppContMetric (ξ : ℝ) (fun z => psiMN Qψ W P 0 n z x)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
      (LaneCInputs.sourceAround K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b)
  have hnorm (b : ℤ × ℤ) (ω : Ω) :
      (ENNReal.ofReal a ^ p)⁻¹ * (∫⁻ x, R x ^ p * D b x ^ p ∂(κ ω)) =
        laneCNormalizedAroundProduct P W hW Qψ (ξ : ℝ) p n K m b ω := by
    exact laneC_normalize_conditional_product (κ ω) ha hp.le
      (fun x => lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) x)
      hL (D b)
  have hraw := hrate P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  have hscaled := laneC_max_scale_L2 P (T20B.nearIdx K)
    (laneC_nearIdx_nonempty K)
    (fun b ω => ∫⁻ x, R x ^ p * D b x ^ p ∂(κ ω))
    hc0 hcTop hraw
  simpa only [hnorm, a, R, D, κ] using hscaled

end SupercriticalLQGUniqueness.B2.DG20Conc
