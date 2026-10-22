import HigherDimLQGContinuity.ConvTransfer.MedianDet
import HigherDimLQGMetric.DGZ.AdapterHolder
import HigherDimLQGMetric.LfppTight.MedianBridge

/-!
# Uniform dyadic events for the convolution median comparison
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP
open HigherDimLFPP.DGZ (obox)
open HigherDimLQGMetric.DGZ

/-- Specialize the uniform dyadic Hölder interface to the two fixed cubes
used in the real-cutoff median comparison. -/
theorem convUniform_holder_box {d : ℕ} {κ : Rd d → ℝ}
    (hT : UHolderTightShape d κ)
    {b μ β θ : ℝ} (hb : 0 < b) (hμ : 0 < μ)
    (hβ : 0 < β) (hβμ : β < μ) (hθ : 0 < θ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ n : ℕ,
      P {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
        M * aQ P H ξ n 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H n z ω) (obox 0 4) x y} ≤ ENNReal.ofReal θ := by
  obtain ⟨M₀, hbound⟩ := hT b μ hb hμ β hβ hβμ (obox 0 4) (obox 0 3)
    (HigherDimLFPP.DGZ.isOpen_obox 0 4)
    (HigherDimLFPP.DGZ.isOpen_obox 0 3)
    ((HigherDimLFPP.DGZ.convex_obox 0 3).isConnected
      ⟨0, fun i => by simp only [PiLp.zero_apply, sub_self, abs_zero]; norm_num⟩)
    (isBounded_obox 0 3)
    (adapter_closure_obox_subset (by norm_num : (3 : ℝ) < 4)) θ hθ
  let M : ℝ := max 1 M₀
  have hM : 1 ≤ M := le_max_left _ _
  refine ⟨M, hM, ?_⟩
  intro ξ hU Ω _ P W H hH n
  have hd0 : 0 < d := by have := hU.base.dim; omega
  have hq : 0 ≤ aQ P H ξ n 2⁻¹ := by
    unfold aQ
    exact ((hH.band n).lowerQuantile_lfppDistance_pos hd0
      hH.whiteNoise ξ (by norm_num) (by norm_num)).le
  have hsub : {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
        M * aQ P H ξ n 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H n z ω) (obox 0 4) x y} ⊆
      {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
        M₀ * aQ P H ξ n 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H n z ω) (obox 0 4) x y} := by
    rintro ω ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hxy⟩
    dsimp [M]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)
      (Real.rpow_nonneg (norm_nonneg _) _)
  exact (measure_mono hsub).trans (hbound ξ hU Ω P W H hH n)

/-- A uniform exponential-moment bound supplies a fixed small bad-event
probability. The threshold is explicit, so no measurability of a quantile is
needed. -/
theorem convEnv_tail_of_exp_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hXm : AEMeasurable X P)
    {B : ℝ} (hB : 0 ≤ B)
    (hExp : ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P ≤ ENNReal.ofReal B) :
    P {ω | 64 * (B + 1) ≤ X ω} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  let L : ℝ := 64 * (B + 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hEL : 64 * B ≤ Real.exp L := by
    have h := Real.add_one_le_exp L
    dsimp [L] at *
    linarith
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (X ω))) P :=
    (Real.measurable_exp.comp_aemeasurable hXm).ennreal_ofReal
  have hsub : {ω | L ≤ X ω} ⊆
      {ω | ENNReal.ofReal (Real.exp L) ≤ ENNReal.ofReal (Real.exp (X ω))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
  have hth0 : ENNReal.ofReal (Real.exp L) ≠ 0 := by positivity
  have hthtop : ENNReal.ofReal (Real.exp L) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmark := meas_ge_le_lintegral_div (ε := ENNReal.ofReal (Real.exp L))
    hm hth0 hthtop
  have hdiv : B / Real.exp L ≤ (1 / 64 : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos L)).2
    nlinarith
  calc
    P {ω | 64 * (B + 1) ≤ X ω} = P {ω | L ≤ X ω} := rfl
    _ ≤ P {ω | ENNReal.ofReal (Real.exp L) ≤
        ENNReal.ofReal (Real.exp (X ω))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P) /
        ENNReal.ofReal (Real.exp L) := hmark
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (Real.exp L) := by gcongr
    _ = ENNReal.ofReal (B / Real.exp L) :=
      (ENNReal.ofReal_div_of_pos (Real.exp_pos L)).symm
    _ ≤ ENNReal.ofReal (1 / 64 : ℝ) := ENNReal.ofReal_le_ofReal hdiv

/-- A cutoff-independent high-probability bound for the model correction on
one fixed box. -/
theorem convModelGamma_uniform_tail {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {ε r : ℝ}, ε ∈ Ioo (0 : ℝ) 1 → 1 / 2 < r → r ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        {W₀ W' : WN d → Ω → ℝ},
        HigherDimLFPP.IsWhiteNoise P W₀ → HigherDimLFPP.IsWhiteNoise P W' →
      ∀ {T I : Rd d → Ω → ℝ},
        HigherDimLFPP.IsBandVersion P W' κ 1 (1 / r) T →
        (∀ ω, Continuous fun x => I x ω) →
        (∀ x, I x =ᵐ[P] W₀ (HigherDimLFPP.bandVecM κ (Ioi 1)
          (Measure.dirac x) (HigherDimLQGMetric.unitSphereProb d))) →
      ∀ (m : Ω → ℝ), Measurable m →
        (∀ ω, m ω = W₀ (HigherDimLFPP.bandVecM κ (Ioo ε 1)
          (HigherDimLQGMetric.unitSphereProb d) 0) ω) →
      P {ω | L ≤ convModelGamma R T I m ω} ≤ ENNReal.ofReal (1 / 64 : ℝ) := by
  obtain ⟨C, A, hC, hA, hMom⟩ :=
    convModelGamma_poly_moment hd hκ (show 0 < (1 : ℝ) by norm_num)
  let B : ℝ := C * (1 + R) ^ A
  have hB : 0 ≤ B := mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  let L : ℝ := 64 * (B + 1)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro ε r hε hr hr1 Ω _ P W₀ W' hW₀ hW' T I hT hIc hIeq m hmm hm
  have hmeas : AEMeasurable (convModelGamma R T I m) P :=
    convModelGamma_aemeasurable hd hκ hr hr1 hW₀ hW' hT hIc hIeq m hmm hR
  have hmom : ∫⁻ ω, ENNReal.ofReal (Real.exp (convModelGamma R T I m ω)) ∂P ≤
      ENNReal.ofReal B := by
    simpa only [one_mul, B] using
      hMom hε hr hr1 hW₀ hW' hT hIc hIeq m hmm hm hR
  exact convEnv_tail_of_exp_moment hmeas hB hmom

/-- The dyadic nondegeneracy, confined Hölder event, and the model correction
give a uniform two-sided point-distance tail. -/
theorem convModel_point_uniform_tail {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hT : UHolderTightShape d κ) (hN : UNondegShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ (ξ : ℝ), UHyp d κ b μ ξ →
      ∀ {ε r : ℝ}, ε ∈ Ioo (0 : ℝ) 1 → 1 / 2 < r → r ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        {W₀ W' : WN d → Ω → ℝ} (H : ℕ → Rd d → Ω → ℝ),
        HigherDimLFPP.IsWhiteNoise P W₀ →
        IsDyadicRealization κ P W' H →
      ∀ {T I : Rd d → Ω → ℝ},
        HigherDimLFPP.IsBandVersion P W' κ 1 (1 / r) T →
        (∀ ω, Continuous fun x => I x ω) →
        (∀ x, I x =ᵐ[P] W₀ (HigherDimLFPP.bandVecM κ (Ioi 1)
          (Measure.dirac x) (HigherDimLQGMetric.unitSphereProb d))) →
      ∀ (m₀ : Ω → ℝ), Measurable m₀ →
        (∀ ω, m₀ ω = W₀ (HigherDimLFPP.bandVecM κ (Ioo ε 1)
          (HigherDimLQGMetric.unitSphereProb d) 0) ω) →
      ∀ (n : ℕ) (Φ : Rd d → Ω → ℝ), (∀ ω, Continuous fun x => Φ x ω) →
        (∀ z ω, Φ (r • z) ω = H n z ω + T z ω - m₀ ω + I (r • z) ω) →
      P {ω | lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d) <
          m * r * aQ P H ξ n 2⁻¹ ∨
        M * r * aQ P H ξ n 2⁻¹ <
          lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d)} ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
  let β : ℝ := μ / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβμ : β < μ := by dsimp [β]; linarith
  obtain ⟨Mₕ, hMₕ, hHolder⟩ := convUniform_holder_box hT hb hμ hβ hβμ
    (by norm_num : (0 : ℝ) < 1 / 64)
  obtain ⟨δ, hδ, hCross⟩ := hN b μ hb hμ (0 : Rd d) 1 (1 / 2)
    (by norm_num) (by norm_num) (1 / 64) (by norm_num)
  let R : ℝ := 4 * Real.sqrt (d : ℝ) + 1
  have hR : 1 ≤ R := by dsimp [R]; nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hS : 4 * Real.sqrt (d : ℝ) ≤ 2 * R + 12 := by
    dsimp [R]
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  obtain ⟨L, hL, hΓ⟩ := convModelGamma_uniform_tail hd hκ hR
  let m : ℝ := Real.exp (-(b * L)) * δ
  let M : ℝ := Real.exp (b * L) * Mₕ * (2 : ℝ) ^ β
  have hm : 0 < m := mul_pos (Real.exp_pos _) hδ
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨m, M, hm, hM, ?_⟩
  intro ξ hU ε r hε hr hr1 Ω _ P W₀ W' H hW₀ hH T I hBand hIc hIeq m₀ hmm hm₀ n Φ hΦc hΦeq
  let a : ℝ := aQ P H ξ n 2⁻¹
  have ha : 0 < a := tight_aQ_pos (by omega : 0 < d) hH ξ n
    (by norm_num) (by norm_num)
  have hTc : ∀ ω, Continuous fun x => T x ω := hBand.continuous
  let EG : Set Ω := {ω | L ≤ convModelGamma R T I m₀ ω}
  let EN : Set Ω := {ω | acrossDist ξ (fun z => H n z ω) 0 1 (1 / 2) ≤ δ * a}
  let EH : Set Ω := {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
      Mₕ * a * ‖x - y‖ ^ β < lfppDistOn ξ (fun z => H n z ω) (obox 0 4) x y}
  have hEG : P EG ≤ ENNReal.ofReal (1 / 64 : ℝ) :=
    hΓ hε hr hr1 hW₀ hH.whiteNoise hBand hIc hIeq m₀ hmm hm₀
  have hEN : P EN ≤ ENNReal.ofReal (1 / 64 : ℝ) :=
    hCross ξ hU Ω P W' H hH n
  have hEH : P EH ≤ ENNReal.ofReal (1 / 64 : ℝ) :=
    hHolder ξ hU Ω P W' H hH n
  have hsub : {ω | lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d) <
          m * r * a ∨ M * r * a < lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d)} ⊆
      EG ∪ EN ∪ EH := by
    intro ω hw
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    have hGam : convModelGamma R T I m₀ ω ≤ L :=
      le_of_lt (lt_of_not_ge hn.1.1)
    have hCrossGood : δ * a < acrossDist ξ (fun z => H n z ω) 0 1 (1 / 2) :=
      lt_of_not_ge hn.1.2
    have hHoldGood : ∀ x ∈ obox (0 : Rd d) 3, ∀ y ∈ obox (0 : Rd d) 3,
        lfppDistOn ξ (fun z => H n z ω) (obox 0 4) x y ≤
          Mₕ * a * ‖x - y‖ ^ β := by
      intro x hx y hy
      exact le_of_not_gt (fun hbad => hn.2 ⟨x, hx, y, hy, hbad⟩)
    have hCorr : ∀ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 4,
        |Φ (r • z) ω - H n z ω| ≤ L := by
      intro z hz
      rw [hΦeq z ω]
      have hbnd := convModelGamma_cbox4_bound (R := R) (by linarith : 0 ≤ R) hS
        (by linarith : 0 ≤ r) hr1 hTc hIc m₀ ω hz
      have heq : H n z ω + T z ω - m₀ ω + I (r • z) ω - H n z ω =
          T z ω + I (r • z) ω - m₀ ω := by ring
      simpa only [heq] using hbnd.trans hGam
    have hgood := convModel_point_good_bounds (by omega : 0 < d)
      hU.base.xi_pos hU.le_b hr hr1 hL.le hδ ha (by linarith : 0 ≤ Mₕ) hβ
      (hΦc ω) ((hH.band n).continuous ω) hCorr hCrossGood hHoldGood
    rcases hw with hw | hw
    · have hlo : m * r * a ≤ lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d) := by
        calc
          m * r * a = r * Real.exp (-(b * L)) * δ * a := by dsimp [m]; ring
          _ ≤ lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d) := hgood.1.le
      exact (not_lt_of_ge hlo) hw
    · have hhi : lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d) ≤ M * r * a := by
        calc
          lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d) ≤
              r * Real.exp (b * L) * Mₕ * a * (2 : ℝ) ^ β := hgood.2
          _ = M * r * a := by dsimp [M]; ring
      exact (not_lt_of_ge hhi) hw
  calc
    P {ω | lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d) < m * r * aQ P H ξ n 2⁻¹ ∨
        M * r * aQ P H ξ n 2⁻¹ < lfppMetric ξ (fun x => Φ x ω) 0 (e₁ d)} ≤
      P (EG ∪ EN ∪ EH) := measure_mono hsub
    _ ≤ P EG + P EN + P EH := by
      calc
        P (EG ∪ EN ∪ EH) ≤ P (EG ∪ EN) + P EH := measure_union_le _ _
        _ ≤ (P EG + P EN) + P EH := by
          exact add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (1 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) +
        ENNReal.ofReal (1 / 64 : ℝ) := add_le_add (add_le_add hEG hEN) hEH
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 64 + 1 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

end HigherDimLQGContinuity
