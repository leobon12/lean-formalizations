import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSourceL2Envelope
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRateMoments
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1MaxRate

 
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

 


theorem laneC_source_product_L2_rate_of_B3_J1_inputs
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
      let κ := condExpKernel P (MeasurableSpace.comap
        (fun y z => psiMN Qψ W P K n z y)
        (inferInstance : MeasurableSpace (ℂ → ℝ)))
      let R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
        (laneCB3Scale (ξ : ℝ) Q δ P W n K /
          lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) x)
      let D (b : ℤ × ℤ) (x : Ω) :=
        (lfppContMetric (ξ : ℝ) (fun z => psiMN Qψ W P 0 n z x)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
          (LaneCInputs.sourceAround K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b)
      let G : ℝ≥0∞ := (ENNReal.ofReal
        (Real.exp (((K : ℝ) * Real.log 2) *
          (((1 + ζ) * p * (ξ : ℝ)) ^ 2) / 2))) ^ (1 / (1 + ζ))
      (∫⁻ ω, ((T20B.nearIdx K).sup' (laneC_nearIdx_nonempty K)
        (fun b => ∫⁻ x, R x ^ p * D b x ^ p ∂(κ ω))) ^ (2 : ℝ) ∂P) ≤
        (ENNReal.ofReal (Real.exp (ν * K) + 1)) ^ (2 * t) *
          (ENNReal.ofReal
            (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ (p * q)) *
            ENNReal.ofReal (Real.exp (ν * K) + 1)) ^ (2 * t) *
          G ^ (2 : ℝ) := by
  let q : ℝ := 2 * ((1 + ζ) / ζ)
  let t : ℝ := ζ / (2 * (1 + ζ))
  have hq : 0 < q := by dsimp [q]; positivity
  have hpq : 0 < p * q := mul_pos hp hq
  obtain ⟨Kb, hb⟩ := laneC_B3_ratio_moment_rate_of_B3_input
    Qψ hε hB3 ξ Q hQ δ C p₀ (p * q) ν hδ hC hp₀ hp₀2 hpq hν
  obtain ⟨Kj, hj⟩ := laneC_J1_max_log_envelope_moment_rate_of_J1_input
    Qψ hε hJ1 ξ C p₀ (p * q) ν hC hp₀ hp₀2 hpq hν
  obtain ⟨Ke, he⟩ := laneC_source_product_L2_of_J1_input
    Qψ hJ1 ξ C p₀ Q δ p ζ hC hp₀ hp₀2 hp hζ hζ1
  refine ⟨max Kb (max Kj Ke), ?_⟩
  intro Ω mΩ _ P _ W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  let R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (laneCB3Scale (ξ : ℝ) Q δ P W n K /
      lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) x)
  let Z₀ := laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m (p * q)
  let hZm := laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m (p * q)
  let Z := hZm.mk Z₀
  have hB : (∫⁻ x, (R x ^ p) ^ q ∂P) ≤
      ENNReal.ofReal (Real.exp (ν * K) + 1) := by
    have h := hb P W hW n K ((le_max_left _ _).trans hK) hK0 hKn hΛ
    convert h using 1
    congr 1
    funext x
    rw [← ENNReal.rpow_mul]
    exact (laneC_B3_ratio_ofReal_rpow hW Qψ (ξ : ℝ) Q δ n K x hpq.le).symm
  have hJ : (∫⁻ x, Z x ∂P) ≤
      ENNReal.ofReal
        (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ (p * q)) *
        ENNReal.ofReal (Real.exp (ν * K) + 1) := by
    have h := hj P W hW n K m ((le_max_left _ _).trans ((le_max_right _ _).trans hK))
      hK0 hKn hmK hmlo hmhi hΛ
    have heq : (∫⁻ x, Z x ∂P) = ∫⁻ x, Z₀ x ∂P :=
      lintegral_congr_ae hZm.ae_eq_mk.symm
    rw [heq]
    exact h
  have hE := he P W hW n K m
    ((le_max_right _ _).trans ((le_max_right _ _).trans hK))
    hK0 hKn hmK hmlo hmhi hΛ
  refine hE.trans ?_
  gcongr

end SupercriticalLQGUniqueness.B2.DG20Conc
