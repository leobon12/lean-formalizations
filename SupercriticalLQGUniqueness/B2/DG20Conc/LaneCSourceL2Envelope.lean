import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTripleAllBlocks
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCMaxConditionalL2

 
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

 

theorem laneC_source_product_L2_of_J1_input
    (Qψ : PsiParams)
    (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p₀ Q δ p ζ : ℝ) (hC : 0 < C)
    (hp₀ : 0 < p₀) (hp₀2 : p₀ < 2⁻¹)
    (hp : 0 < p) (hζ : 0 < ζ) (hζ1 : ζ < 1) :
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
      let Z := (laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ) P W hW
        n K m (p * q)).mk
          (laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m (p * q))
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
        ((∫⁻ x, (R x ^ p) ^ q ∂P) ^ (2 * t) *
          (∫⁻ x, Z x ∂P) ^ (2 * t)) * G ^ (2 : ℝ) := by
  obtain ⟨K₀, hpoint⟩ :=
    laneC_J1_all_conditional_source_products_of_J1_input
      Qψ hJ1 ξ C p₀ Q δ p ζ hC hp₀ hp₀2 hp hζ
  refine ⟨K₀, ?_⟩
  intro Ω mΩ _ P _ W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  have hmFine : MeasurableSpace.comap
      (fun y z => psiMN Qψ W P K n z y)
      (inferInstance : MeasurableSpace (ℂ → ℝ)) ≤ mΩ :=
    (measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Qψ) hW hKn).meas).comap_le
  let q : ℝ := 2 * ((1 + ζ) / ζ)
  let t : ℝ := ζ / (2 * (1 + ζ))
  let R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (laneCB3Scale (ξ : ℝ) Q δ P W n K /
      lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) x)
  let Z₀ := laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m (p * q)
  let hZm := laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m (p * q)
  let Z := hZm.mk Z₀
  have hLm : Measurable
      (lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1)) :=
    measurable_lenObs ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).meas) _
  have hRm : Measurable R := by
    dsimp [R]
    fun_prop
  have hUm : Measurable (fun x => (R x ^ p) ^ q) :=
    (hRm.pow_const p).pow_const q
  have hVm : Measurable Z := hZm.measurable_mk
  let G : ℝ≥0∞ := (ENNReal.ofReal
    (Real.exp (((K : ℝ) * Real.log 2) *
      (((1 + ζ) * p * (ξ : ℝ)) ^ 2) / 2))) ^ (1 / (1 + ζ))
  have hGtop : G ≠ ⊤ := by
    dsimp [G]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : 4 * t < 1 := by
    dsimp [t]
    have hz : 0 < 1 + ζ := by linarith
    calc
      4 * (ζ / (2 * (1 + ζ))) = (4 * ζ) / (2 * (1 + ζ)) := by ring
      _ < 1 := (div_lt_iff₀ (by positivity : 0 < 2 * (1 + ζ))).2 (by linarith)
  have hpnt := hpoint P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  have hpoint' : ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K,
      (∫⁻ x, R x ^ p *
        ((lfppContMetric (ξ : ℝ) (fun z => psiMN Qψ W P 0 n z x)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
          (LaneCInputs.sourceAround K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b)) ^ p ∂(condExpKernel P
            (MeasurableSpace.comap (fun y z => psiMN Qψ W P K n z y)
              (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ≤
        (∫⁻ x, (R x ^ p) ^ q ∂(condExpKernel P
          (MeasurableSpace.comap (fun y z => psiMN Qψ W P K n z y)
            (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ^ t *
        (∫⁻ x, Z x ∂(condExpKernel P
          (MeasurableSpace.comap (fun y z => psiMN Qψ W P K n z y)
            (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ^ t * G := by
    simpa only [q, t, R, Z, Z₀, G, mul_assoc] using hpnt
  exact laneC_max_conditional_two_envelope_L2 P hmFine
    (T20B.nearIdx K) (laneC_nearIdx_nonempty K)
    (fun b ω => ∫⁻ x, R x ^ p *
      ((lfppContMetric (ξ : ℝ) (fun z => psiMN Qψ W P 0 n z x)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)) ^ p ∂(condExpKernel P
          (MeasurableSpace.comap (fun y z => psiMN Qψ W P K n z y)
            (inferInstance : MeasurableSpace (ℂ → ℝ))) ω))
    hUm hVm ht ht4 G hGtop hpoint'

end SupercriticalLQGUniqueness.B2.DG20Conc
