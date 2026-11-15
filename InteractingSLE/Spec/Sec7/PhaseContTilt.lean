/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.SubdomainMGF
import InteractingSLE.Spec.Sec6.Prop65Gauss

/-!
# Theorem 1.2's R.7: Gaussian tails for the increments of two conditional means

Packet PROVE-PHASECONT. Astra's follow-up 5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483) uses
"the adopted mean continuity" of the pocket's conditional mean. The source's continuity proof (Proposition 6.5,
`source/spec/p145-192.md`, pp. 158–159) compares conditional Gaussian laws at two times. Here is the two-time comparison
in the form needed for a lattice-valued phase, with no filtration and no stopping times:

if an observable `X` is conditionally Gaussian given `𝒢` on `L ∈ 𝒢` (mean `μ`, variance `V`) and given `𝒢' ⊇ 𝒢` on
`L' ⊆ L`, `L' ∈ 𝒢'` (mean `μ'`, variance `V'`), then `E[1_{L'} exp(λ(μ' − μ) − λ²(V − V')/2)] ≤ 1` for every real
`λ` (exponential tilt; only positivity is used off `L'`, so nothing is assumed about `X` after the later lifetime), and
Markov's inequality gives `P(L', |μ' − μ| ≥ b, V − V' ≤ d) ≤ 2 exp(−b²/(2d))`.

## Main results

* `condCharFun_indicator_centered`: a conditional characteristic function that is Gaussian on `L ∈ 𝒢`, centred and cut
  off at `L`;
* `setLIntegral_mul_tilt_eq`: the one-level exponential tilt;
* **`setLIntegral_tilt_le_one`**: the two-level exponential tilt;
* **`measure_increment_le`**: Gaussian tails for the increment of the conditional means.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseCont

section Local

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A conditional characteristic function that is Gaussian on an event `L ∈ 𝒢` gives a global centred one for the
observable centred and cut off at `L`. -/
theorem condCharFun_indicator_centered [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {X μ V : Ω → ℝ} (hX : Measurable X)
    (hμ : Measurable[𝒢] μ) {L : Set Ω} (hL : MeasurableSet[𝒢] L)
    (hc : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) (t : ℝ) :
    P[fun ω => cexp (I * ((t * L.indicator (fun ω => X ω - μ ω) ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * L.indicator V ω)) : ℝ) : ℂ) := by
  set f : Ω → ℂ := fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) with hf
  set g : Ω → ℂ := fun ω => cexp (I * ((-(t * μ ω) : ℝ) : ℂ)) with hg
  have hgm : StronglyMeasurable[𝒢] g :=
    ((by fun_prop : Measurable fun x : ℝ => cexp (I * ((-(t * x) : ℝ) : ℂ))).comp hμ).stronglyMeasurable
  have hfi : Integrable f P :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => (norm_exp_I_mul_ofReal _).le)
  have hgfi : Integrable (fun ω => g ω * f ω) P := by
    refine Integrable.of_bound ((hgm.mono h𝒢).aestronglyMeasurable.mul hfi.1) 1
      (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, norm_exp_I_mul_ofReal, norm_exp_I_mul_ofReal, one_mul]
  have hLm : MeasurableSet L := h𝒢 _ hL
  have e : (fun ω => cexp (I * ((t * L.indicator (fun ω => X ω - μ ω) ω : ℝ) : ℂ))) =
      fun ω => L.indicator (fun ω => g ω * f ω) ω + Lᶜ.indicator (fun _ => (1 : ℂ)) ω := by
    funext ω
    by_cases hω : ω ∈ L
    · simp only [indicator_of_mem hω, indicator_of_notMem (show ω ∉ Lᶜ from fun h => h hω), add_zero, hf, hg,
        ← Complex.exp_add]
      congr 1; push_cast; ring
    · simp only [indicator_of_notMem hω, indicator_of_mem (show ω ∈ Lᶜ from hω), zero_add, mul_zero,
        Complex.ofReal_zero, Complex.exp_zero]
  rw [e]
  have h1 : P[fun ω => L.indicator (fun ω => g ω * f ω) ω | 𝒢] =ᵐ[P]
      L.indicator (P[fun ω => g ω * f ω | 𝒢]) := condExp_indicator hgfi hL
  have h2 : P[fun ω => g ω * f ω | 𝒢] =ᵐ[P] fun ω => g ω * P[f | 𝒢] ω := by
    have := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hgm
      (by simpa [ContinuousLinearMap.mul_apply'] using hgfi) hfi
    simpa [ContinuousLinearMap.mul_apply'] using this
  have h3 : P[fun ω => Lᶜ.indicator (fun _ => (1 : ℂ)) ω | 𝒢] = Lᶜ.indicator (fun _ => (1 : ℂ)) := by
    refine condExp_of_stronglyMeasurable h𝒢 ?_ ((integrable_const (1 : ℂ)).indicator hLm.compl)
    exact (stronglyMeasurable_const.indicator hL.compl)
  have h4 := condExp_add (m := 𝒢) (μ := P) (hgfi.indicator hLm)
    ((integrable_const (1 : ℂ)).indicator hLm.compl)
  have h5 := hc t
  filter_upwards [h1, h2, h4, h5] with ω e1 e2 e4 e5
  rw [show (fun ω => L.indicator (fun ω => g ω * f ω) ω + Lᶜ.indicator (fun _ => (1 : ℂ)) ω) =
      (L.indicator fun ω => g ω * f ω) + Lᶜ.indicator (fun _ => (1 : ℂ)) from rfl, e4, Pi.add_apply, e1, h3]
  by_cases hω : ω ∈ L
  · rw [indicator_of_mem hω, indicator_of_notMem (show ω ∉ Lᶜ from fun h => h hω), add_zero, e2, e5 hω,
      indicator_of_mem hω, hg, ← mul_assoc, ← Complex.exp_add]
    have : I * ((-(t * μ ω) : ℝ) : ℂ) + I * ((t * μ ω : ℝ) : ℂ) = 0 := by push_cast; ring
    rw [this, Complex.exp_zero, one_mul]
  · rw [indicator_of_notMem hω, indicator_of_mem (show ω ∈ Lᶜ from hω), zero_add, indicator_of_notMem hω,
      mul_zero, mul_zero, Real.exp_zero, Complex.ofReal_one]

/-- **The exponential tilt at one level**: if `X` is conditionally Gaussian given `𝒢` with mean `μ` and variance `V` on
`L ∈ 𝒢`, then `E[W 1_L e^{λ(X − μ) − λ²V/2}] = E[W 1_L]` for every `𝒢`-measurable `W ≥ 0`. -/
theorem setLIntegral_mul_tilt_eq [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {X μ V : Ω → ℝ} (hX : Measurable X)
    (hμ : Measurable[𝒢] μ) (hV : Measurable[𝒢] V) {L : Set Ω} (hL : MeasurableSet[𝒢] L)
    (hV0 : ∀ ω ∈ L, 0 ≤ V ω)
    (hc : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    {W : Ω → ℝ≥0∞} (hW : Measurable[𝒢] W) (lam : ℝ) :
    ∫⁻ ω in L, W ω * ENNReal.ofReal (Real.exp (lam * (X ω - μ ω) - lam ^ 2 * V ω / 2)) ∂P =
      ∫⁻ ω in L, W ω ∂P := by
  have hLm : MeasurableSet L := h𝒢 _ hL
  have hμm : Measurable μ := hμ.mono h𝒢 le_rfl
  have hVm : Measurable V := hV.mono h𝒢 le_rfl
  set Y : Ω → ℝ := L.indicator fun ω => X ω - μ ω with hY
  set Vh : Ω → ℝ := L.indicator V with hVh
  have hYm : Measurable Y := (hX.sub hμm).indicator hLm
  have hVhm : Measurable Vh := hVm.indicator hLm
  have hVh0 : ∀ᵐ ω ∂P, 0 ≤ Vh ω := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ L
    · rw [hVh, indicator_of_mem hω]; exact hV0 ω hω
    · rw [hVh, indicator_of_notMem hω]
  set W' : Ω → ℝ≥0∞ := L.indicator fun ω => W ω * ENNReal.ofReal (Real.exp (-(lam ^ 2 * V ω / 2))) with hW'
  have hW'm : Measurable[𝒢] W' := by
    refine Measurable.indicator (hW.mul ?_) hL
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hV.const_mul (lam ^ 2)).div_const 2).neg)
  have hmgf := LocalSets.lintegral_mul_exp_of_condCharFun (P := P) h𝒢 hYm hVhm hVh0
    (condCharFun_indicator_centered h𝒢 hX hμ hL hc) hW'm lam
  have e1 : (fun ω => W' ω * ENNReal.ofReal (Real.exp (lam * Y ω))) =
      L.indicator fun ω => W ω * ENNReal.ofReal (Real.exp (lam * (X ω - μ ω) - lam ^ 2 * V ω / 2)) := by
    funext ω
    by_cases hω : ω ∈ L
    · rw [hW', hY, indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hω, mul_assoc,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3; ring
    · rw [hW', indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
  have e2 : (fun ω => W' ω * ENNReal.ofReal (Real.exp (lam ^ 2 * Vh ω / 2))) = L.indicator W := by
    funext ω
    by_cases hω : ω ∈ L
    · rw [hW', hVh, indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hω, mul_assoc,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        ENNReal.ofReal_one, mul_one]
    · rw [hW', indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
  rw [e1, e2, lintegral_indicator hLm, lintegral_indicator hLm] at hmgf
  exact hmgf

end Local

section Tilt

variable {Ω : Type*} {𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The two-level exponential tilt**: if `X` is conditionally Gaussian given `𝒢` on `L` (mean `μ`, variance `V`)
and given `𝒢' ⊇ 𝒢` on `L' ⊆ L` (mean `μ'`, variance `V'`), then
`E[1_{L'} e^{λ(μ' − μ) − λ²(V − V')/2}] ≤ 1` for every real `λ`. Only positivity is used on `L ∖ L'`. -/
theorem setLIntegral_tilt_le_one [IsProbabilityMeasure P] (h𝒢𝒢' : 𝒢 ≤ 𝒢')
    (h𝒢' : 𝒢' ≤ mΩ) {X : Ω → ℝ} (hX : Measurable X) {μ V μ' V' : Ω → ℝ} (hμ : Measurable[𝒢] μ)
    (hV : Measurable[𝒢] V) (hμ' : Measurable[𝒢'] μ') (hV' : Measurable[𝒢'] V') {L L' : Set Ω}
    (hL : MeasurableSet[𝒢] L) (hL' : MeasurableSet[𝒢'] L') (hLL : L' ⊆ L) (hV0 : ∀ ω ∈ L, 0 ≤ V ω)
    (hV0' : ∀ ω ∈ L', 0 ≤ V' ω)
    (hc : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    (hc' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L' → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢'] ω =
      cexp (I * ((t * μ' ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V' ω)) : ℝ) : ℂ)) (lam : ℝ) :
    ∫⁻ ω in L', ENNReal.ofReal (Real.exp (lam * (μ' ω - μ ω) - lam ^ 2 * (V ω - V' ω) / 2)) ∂P ≤ 1 := by
  have h𝒢 : 𝒢 ≤ mΩ := h𝒢𝒢'.trans h𝒢'
  have hWm : Measurable[𝒢'] fun ω => ENNReal.ofReal (Real.exp (lam * (μ' ω - μ ω) - lam ^ 2 * (V ω - V' ω) / 2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((hμ'.sub (hμ.mono h𝒢𝒢' le_rfl)).const_mul lam).sub
        ((((hV.mono h𝒢𝒢' le_rfl).sub hV').const_mul (lam ^ 2)).div_const 2)))
  have h2 := setLIntegral_mul_tilt_eq (P := P) h𝒢' hX hμ' hV' hL' hV0' hc' hWm lam
  have e : (fun ω => ENNReal.ofReal (Real.exp (lam * (μ' ω - μ ω) - lam ^ 2 * (V ω - V' ω) / 2)) *
      ENNReal.ofReal (Real.exp (lam * (X ω - μ' ω) - lam ^ 2 * V' ω / 2))) =
      fun ω => 1 * ENNReal.ofReal (Real.exp (lam * (X ω - μ ω) - lam ^ 2 * V ω / 2)) := by
    funext ω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, one_mul]
    congr 2; ring
  rw [e] at h2
  have h1 := setLIntegral_mul_tilt_eq (P := P) h𝒢 hX hμ hV hL hV0 hc
    (@measurable_const _ _ _ 𝒢 (1 : ℝ≥0∞)) lam
  rw [← h2]
  calc ∫⁻ ω in L', 1 * ENNReal.ofReal (Real.exp (lam * (X ω - μ ω) - lam ^ 2 * V ω / 2)) ∂P
      ≤ ∫⁻ ω in L, 1 * ENNReal.ofReal (Real.exp (lam * (X ω - μ ω) - lam ^ 2 * V ω / 2)) ∂P :=
        lintegral_mono_set hLL
    _ = ∫⁻ ω in L, 1 ∂P := h1
    _ ≤ 1 := by
        rw [setLIntegral_const, one_mul]
        exact prob_le_one

/-- Markov's inequality on a subset of the tilt event. -/
theorem measure_le_of_tilt {L' S : Set Ω} (hS : MeasurableSet S) (hSL : S ⊆ L') {f : Ω → ℝ} {c : ℝ}
    (hf : ∀ ω ∈ S, c ≤ f ω) (h : ∫⁻ ω in L', ENNReal.ofReal (Real.exp (f ω)) ∂P ≤ 1) :
    P S ≤ ENNReal.ofReal (Real.exp (-c)) := by
  have h1 : ENNReal.ofReal (Real.exp c) * P S ≤ 1 := by
    calc ENNReal.ofReal (Real.exp c) * P S = ∫⁻ _ in S, ENNReal.ofReal (Real.exp c) ∂P := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ ω in S, ENNReal.ofReal (Real.exp (f ω)) ∂P :=
          setLIntegral_mono' hS fun ω hω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hf ω hω))
      _ ≤ ∫⁻ ω in L', ENNReal.ofReal (Real.exp (f ω)) ∂P := lintegral_mono_set hSL
      _ ≤ 1 := h
  have hpos : ENNReal.ofReal (Real.exp c) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos c
  have hinv : ENNReal.ofReal (Real.exp (-c)) * ENNReal.ofReal (Real.exp c) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  calc P S = ENNReal.ofReal (Real.exp (-c)) * (ENNReal.ofReal (Real.exp c) * P S) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-c)) * 1 := by gcongr
    _ = ENNReal.ofReal (Real.exp (-c)) := mul_one _

/-- **Gaussian tails for the increment of conditional means** (two-level tilt and Markov's inequality): on the later
live event `L'`, where the variance decreased by at most `d`, the mean moved by at least `b` with probability at most
`2 e^{−b²/(2d)}`. -/
theorem measure_increment_le [IsProbabilityMeasure P] (h𝒢𝒢' : 𝒢 ≤ 𝒢')
    (h𝒢' : 𝒢' ≤ mΩ) {X : Ω → ℝ} (hX : Measurable X) {μ V μ' V' : Ω → ℝ} (hμ : Measurable[𝒢] μ)
    (hV : Measurable[𝒢] V) (hμ' : Measurable[𝒢'] μ') (hV' : Measurable[𝒢'] V') {L L' : Set Ω}
    (hL : MeasurableSet[𝒢] L) (hL' : MeasurableSet[𝒢'] L') (hLL : L' ⊆ L) (hV0 : ∀ ω ∈ L, 0 ≤ V ω)
    (hV0' : ∀ ω ∈ L', 0 ≤ V' ω)
    (hc : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    (hc' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L' → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢'] ω =
      cexp (I * ((t * μ' ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V' ω)) : ℝ) : ℂ))
    {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    P (L' ∩ {ω | b ≤ |μ' ω - μ ω| ∧ V ω - V' ω ≤ d}) ≤ 2 * ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * d)))) := by
  have h𝒢 : 𝒢 ≤ mΩ := h𝒢𝒢'.trans h𝒢'
  have hμm : Measurable μ := hμ.mono h𝒢 le_rfl
  have hVm : Measurable V := hV.mono h𝒢 le_rfl
  have hμ'm : Measurable μ' := hμ'.mono h𝒢' le_rfl
  have hV'm : Measurable V' := hV'.mono h𝒢' le_rfl
  have hL'm : MeasurableSet L' := h𝒢' _ hL'
  have htilt := fun lam => setLIntegral_tilt_le_one (P := P) h𝒢𝒢' h𝒢' hX hμ hV hμ' hV' hL hL' hLL hV0 hV0' hc hc' lam
  set Sp : Set Ω := L' ∩ {ω | b ≤ μ' ω - μ ω ∧ V ω - V' ω ≤ d} with hSp
  set Sm : Set Ω := L' ∩ {ω | b ≤ -(μ' ω - μ ω) ∧ V ω - V' ω ≤ d} with hSm
  have hSpm : MeasurableSet Sp :=
    hL'm.inter ((measurableSet_le measurable_const (hμ'm.sub hμm)).inter
      (measurableSet_le (hVm.sub hV'm) measurable_const))
  have hSmm : MeasurableSet Sm :=
    hL'm.inter ((measurableSet_le measurable_const (hμ'm.sub hμm).neg).inter
      (measurableSet_le (hVm.sub hV'm) measurable_const))
  have key : ∀ (lam : ℝ) (y v : ℝ), 0 ≤ lam → lam * b ≤ lam * y → v ≤ d →
      lam * b - lam ^ 2 * d / 2 ≤ lam * y - lam ^ 2 * v / 2 := by
    intro lam y v hl hy hv
    have : lam ^ 2 * v ≤ lam ^ 2 * d := mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    linarith
  have hval : (b / d) * b - (b / d) ^ 2 * d / 2 = b ^ 2 / (2 * d) := by
    field_simp; ring
  have hp : P Sp ≤ ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * d)))) := by
    refine measure_le_of_tilt hSpm inter_subset_left (fun ω hω => ?_) (htilt (b / d))
    rw [← hval]
    exact key (b / d) _ _ (div_pos hb hd).le (mul_le_mul_of_nonneg_left hω.2.1 (div_pos hb hd).le) hω.2.2
  have hm : P Sm ≤ ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * d)))) := by
    refine measure_le_of_tilt hSmm inter_subset_left (fun ω hω => ?_) (htilt (-(b / d)))
    rw [← hval]
    have h1 := key (b / d) (-(μ' ω - μ ω)) (V ω - V' ω) (div_pos hb hd).le
      (mul_le_mul_of_nonneg_left hω.2.1 (div_pos hb hd).le) hω.2.2
    have e : -(b / d) * (μ' ω - μ ω) - (-(b / d)) ^ 2 * (V ω - V' ω) / 2 =
        b / d * -(μ' ω - μ ω) - (b / d) ^ 2 * (V ω - V' ω) / 2 := by ring
    rw [e]; exact h1
  have hsub : L' ∩ {ω | b ≤ |μ' ω - μ ω| ∧ V ω - V' ω ≤ d} ⊆ Sp ∪ Sm := by
    rintro ω ⟨hωL, hb', hd'⟩
    rcases le_abs'.1 hb' with h | h
    · exact Or.inr ⟨hωL, by linarith, hd'⟩
    · exact Or.inl ⟨hωL, h, hd'⟩
  calc P (L' ∩ {ω | b ≤ |μ' ω - μ ω| ∧ V ω - V' ω ≤ d}) ≤ P (Sp ∪ Sm) := measure_mono hsub
    _ ≤ P Sp + P Sm := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * d)))) + ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * d)))) :=
        add_le_add hp hm
    _ = 2 * ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * d)))) := (two_mul _).symm

end Tilt

end InteractingSLE.Sec7.PhaseCont
