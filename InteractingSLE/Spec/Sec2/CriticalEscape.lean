/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.CriticalPath
import InteractingSLE.Spec.Sec2.TerminalEvolution
import InteractingSLE.Stochastic.LocalTime.ItoExpectation
import InteractingSLE.Stochastic.LocalTime.Occupation
import InteractingSLE.Stochastic.LocalTime.Bridge

/-!
# The critical case of Aux. lemma 3: no escape with side total `−2`

Packet PROVE-SEC2-TERM2. Specification pp. 27–28 (`source/spec/p001-048.md` L612–L648): if the
left side total is `∑ ρ^{i,L} = −2`, then almost surely the left force points do not escape to
`−∞` at a finite lifetime while the right ones stay bounded.

The proof follows the source. For a rational starting time `q`, a horizon `t = q + H`, and the
localization `CritAlive` (`ε < Q < M`, `V^out > −n`, right coordinates `< n` and at distance
`> 1` from the driver, at rational times), Itô's formula in expectation
(`LocalTime.integral_sub_eq_of_isTanakaPath`, PROVE-TANAKA) for the regularized `x log x` applied
to the clamped extended gap gives, with the bounds (N7)–(N8) of `CriticalPath.lean`,

  `(κ/4) E ∫_q^ρ dt/Q ≤ 2 (M log M + 1) + K₁ + C' H`  (`integral_critY_le`),

uniformly in `ε` and `n` (this is (N8)). Markov's inequality and the choice `ε = 1/(k+1)`,
`n = k` with `k → ∞` show that the event "`∫_q^u dt/Q` is unbounded for `u < ζ`, with `Q < M`
and the driver at distance `> 1` from the right force points on `[q, ζ)`, and `ζ ≤ q + H`" is
null (`measure_critEscapeSet`). A critical escape lies in one of countably many such events
(`(N4)` makes `Q` bounded, the driver tends to `−∞`, and `∫ dt/Q = ∞` because
`V^out_t = V^out_q − ∫_q^t 2/Q`), which proves `ae_bddBelow_of_sum_eq`. The mirror image gives the
right side, and together with the pathwise trichotomy of PROVE-SEC2-TERM this completes Aux.
lemma 3: `IsIntegratedSLEEvolution.ae_tendsto_threshold`.

The process `B` enters through a coefficient `σ` with `σ² = 1` (the reflected evolution is driven
by `−B`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology InteractingSLE.LocalTime
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- `IsTanakaPath` with the Brownian path written as `σ β`. -/
theorem isTanakaPath_mul_of {k c N : ℝ} {s ρ : ℝ≥0} {x β j b : ℝ≥0 → ℝ} {σ : ℝ}
    (hP : IsTanakaPath k c N s ρ x (fun u => σ * β u) j b) (hβ : ContinuousOn β (Icc s ρ)) :
    IsTanakaPath (k * σ) c N s ρ x β j b := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hP
  refine ⟨h1, hβ, h3, h4, fun u hu => ?_, h6, h7, h8, h9, h10⟩
  rw [h5 u hu]
  ring

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {a σ : ℝ} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {o : Fin nL}

/-- The extended gap process `Q̄_u = √κ σ B_u + gapAffine(V̄_u)`. -/
def critGap (a σ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (o : Fin nL) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (u : ℝ≥0) (ω : Ω) : ℝ :=
  gapExt a xL xR ρL ρR o (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => σ * B t ω) (ζ ω) u

/-- The localization events of the critical case. -/
def critAliveSet (a σ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (o : Fin nL) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0) (ε M : ℝ) (n : ℕ) (u : ℝ≥0) : Set Ω :=
  {ω | critAlivePath a xL xR ρL ρR o (fun i t => VL i t ω) (fun j t => VR j t ω)
    (fun t => σ * B t ω) (ζ ω) q ε M n u}

theorem critAliveSet_antitone {q : ℝ≥0} {ε M : ℝ} {n : ℕ} :
    Antitone (critAliveSet a σ xL xR ρL ρR o VL VR B ζ q ε M n) :=
  fun _ _ huv _ hω => CritAlive.anti _ _ huv hω

variable (hB : ∀ u, Measurable[𝓕 u] (B u)) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
  (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))

include hB hVL hVR in
/-- The extended gap is adapted. -/
theorem measurable_critGap (u : ℝ≥0) :
    Measurable[𝓕 u] (critGap a σ xL xR ρL ρR o VL VR B ζ u) := by
  have hL : ∀ i, Measurable[𝓕 u] (lowerExt ζ (VL i) (xL i) u) := fun i =>
    measurable_lowerExt (hVL i) (xL i) u
  have hR : ∀ j, Measurable[𝓕 u] (upperExt ζ (VR j) (xR j) u) := fun j =>
    measurable_upperExt (hVR j) (xR j) u
  change Measurable[𝓕 u] fun ω => Real.sqrt a * (σ * B u ω) +
    (-(1 / 2) * (∑ i, ρL i * (lowerExt ζ (VL i) (xL i) u ω - lowerExt ζ (VL o) (xL o) u ω)) +
      (1 / 2) * (∑ i, ρL i * xL i) -
      (1 / 2) * (∑ j, ρR j * (upperExt ζ (VR j) (xR j) u ω - xR j)))
  refine (((hB u).const_mul σ).const_mul _).add ?_
  refine (((Finset.measurable_sum _ fun i _ => ((hL i).sub (hL o)).const_mul (ρL i)).const_mul
    _).add measurable_const).sub ?_
  exact (Finset.measurable_sum _ fun j _ => ((hR j).sub measurable_const).const_mul (ρR j)).const_mul _

include hB hVL hVR in
/-- The localization events are adapted. -/
theorem measurableSet_critAliveSet (hζ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | (u : ℝ≥0∞) < ζ ω})
    (q : ℝ≥0) (ε M : ℝ) (n : ℕ) (u : ℝ≥0) :
    MeasurableSet[𝓕 u] (critAliveSet a σ xL xR ρL ρR o VL VR B ζ q ε M n u) := by
  by_cases huq : u < q
  · convert MeasurableSet.univ (m := 𝓕 u) using 1
    ext ω
    simp only [critAliveSet, critAlivePath, CritAlive, huq, true_or, mem_ofPred_eq, mem_univ]
  have hcond : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω |
      ε < critGap a σ xL xR ρL ρR o VL VR B ζ s ω ∧ critGap a σ xL xR ρL ρR o VL VR B ζ s ω < M ∧
        -(n : ℝ) < lowerExt ζ (VL o) (xL o) s ω ∧ ∀ j, upperExt ζ (VR j) (xR j) s ω < n ∧
          critGap a σ xL xR ρL ρR o VL VR B ζ s ω + lowerExt ζ (VL o) (xL o) s ω <
            upperExt ζ (VR j) (xR j) s ω - 1} := fun s => by
    have hQ := measurable_critGap (a := a) (σ := σ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (o := o)
      hB hVL hVR s
    have hL := measurable_lowerExt (hVL o) (xL o) s
    have hR : ∀ j, Measurable[𝓕 s] (upperExt ζ (VR j) (xR j) s) := fun j =>
      measurable_upperExt (hVR j) (xR j) s
    simp only [ofPred_and, ofPred_forall]
    exact (measurableSet_lt measurable_const hQ).inter ((measurableSet_lt hQ measurable_const).inter
      ((measurableSet_lt measurable_const hL).inter (MeasurableSet.iInter fun j =>
        (measurableSet_lt (hR j) measurable_const).inter
          (measurableSet_lt (hQ.add hL) ((hR j).sub measurable_const)))))
  have e : critAliveSet a σ xL xR ρL ρR o VL VR B ζ q ε M n u = {ω | (u : ℝ≥0∞) < ζ ω} ∩
      ⋂ r : ℚ, {ω | q ≤ ratTime r → ratTime r ≤ u →
        ε < critGap a σ xL xR ρL ρR o VL VR B ζ (ratTime r) ω ∧
        critGap a σ xL xR ρL ρR o VL VR B ζ (ratTime r) ω < M ∧
        -(n : ℝ) < lowerExt ζ (VL o) (xL o) (ratTime r) ω ∧
        ∀ j, upperExt ζ (VR j) (xR j) (ratTime r) ω < n ∧
          critGap a σ xL xR ρL ρR o VL VR B ζ (ratTime r) ω +
            lowerExt ζ (VL o) (xL o) (ratTime r) ω < upperExt ζ (VR j) (xR j) (ratTime r) ω - 1} := by
    ext ω
    simp only [critAliveSet, critAlivePath, CritAlive, huq, false_or, mem_ofPred_eq, mem_inter_iff,
      mem_iInter]
    rfl
  rw [e]
  refine (hζ u).inter (MeasurableSet.iInter fun r => ?_)
  by_cases hr : q ≤ ratTime r ∧ ratTime r ≤ u
  · have := 𝓕.mono hr.2 _ (hcond (ratTime r))
    convert this using 1
    ext ω
    simp only [mem_ofPred_eq, hr.1, hr.2, forall_const]
  · convert MeasurableSet.univ (m := 𝓕 u) using 1
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    intro h1 h2
    exact absurd ⟨h1, h2⟩ hr

/-- The uniform constant of (N8): `(4/κ) (2 (M log M + 1) + K₁ + C' H)`. -/
def critKY (a : ℝ) (xL : Fin nL → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (o : Fin nL)
    (M H : ℝ) : ℝ :=
  4 / a * (2 * (M * Real.log M + 1) + critK₁ xL ρL o M + critC' a ρR M * H)

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **(N8)**: the localized `∫_q^ρ F''(X) = ∫_q^ρ dt/Q` is integrable and its expectation is
bounded by `critKY`, uniformly in `ε` and `n` (Specification p. 27, "the bound is uniform in both
localizations"). -/
theorem integrable_and_integral_critY_le (ha : 0 < a) (hBf : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))
    (hζ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | (u : ℝ≥0∞) < ζ ω}) (hσ : σ ^ 2 = 1)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => σ * B t ω) (ζ ω))
    (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o) (q₀ : ℚ) {t : ℝ≥0} (hqt : ratTime q₀ ≤ t)
    {ε M : ℝ} (n : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 1 ≤ M) :
    Integrable (fun ω => ∫ r in (ratTime q₀ : ℝ)..(lifetime
        (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
        xlogxReg'' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω))) P ∧
    ∫ ω, (∫ r in (ratTime q₀ : ℝ)..(lifetime
        (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
        xlogxReg'' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω))) ∂P ≤
      critKY a xL ρL ρR o M ((t : ℝ) - ratTime q₀) := by
  have hεM : ε ≤ M := hε1.trans hM
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => (hBf.stronglyAdapted u).measurable
  have hX : ∀ u, Measurable[𝓕 u] (fun ω => clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ u ω)) :=
    fun u => (continuous_clampIcc ε M).measurable.comp (measurable_critGap hBm hVL hVR u)
  have h𝒢 := measurableSet_critAliveSet (a := a) (σ := σ) (xL := xL) (xR := xR) (ρL := ρL)
    (ρR := ρR) (o := o) hBm hVL hVR hζ (ratTime q₀) ε M n
  have h𝒢a : Antitone (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) :=
    critAliveSet_antitone
  set N := max M (critBound xL ρL ρR o M ((t : ℝ) - ratTime q₀))
  have hpathT : ∀ᵐ ω ∂P, IsTanakaPath (Real.sqrt a * σ) 0 N (ratTime q₀)
      (lifetime (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω)
      (fun u => clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ u ω)) (fun u => B u ω)
      (fun _ => 0) (fun u => gapOutDrift ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) o u) := by
    filter_upwards [hpath, hBc] with ω hp hc
    exact isTanakaPath_mul_of (hp.isForcePath.isTanakaPath_crit hp.driverEq hS ho
      (continuous_const.mul hc) hε hεM hqt (le_max_left _ _) (le_max_right _ _)) hc.continuousOn
  have hIto := integral_sub_eq_of_isTanakaPath (J := fun _ _ => (0 : ℝ)) hBf hqt hX h𝒢 h𝒢a
    (hasDerivAt_xlogxReg hε) (hasDerivAt_xlogxReg' hε) (continuous_xlogxReg'' hε) hpathT
  have hSi := integrable_limitS hqt hX h𝒢 h𝒢a (continuous_xlogxReg hε) hpathT
  have hAi := integrable_limitA (J := fun _ _ => (0 : ℝ)) hBf hqt hX h𝒢 h𝒢a
    (continuous_xlogxReg' hε) hpathT
  have hYi := integrable_limitT hqt hX h𝒢 h𝒢a (continuous_xlogxReg'' hε) hpathT
  simp only [mul_zero, zero_mul, sub_self, add_zero, gapOutDrift_coe_toNNReal] at hIto hAi
  have hcoef : (Real.sqrt a * σ) ^ 2 / 2 = a / 2 := by
    rw [mul_pow, Real.sq_sqrt ha.le, hσ, mul_one]
  rw [hcoef] at hIto
  -- the bounds
  set KS := 2 * (M * Real.log M + 1)
  have hSle : ∫ ω, (xlogxReg ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ
      (lifetime (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω) ω)) -
      xlogxReg ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ω))) ∂P ≤ KS := by
    have := integral_mono_ae hSi (integrable_const KS) (Eventually.of_forall fun ω => by
      have h1 := abs_le.1 (abs_xlogxReg_clampIcc_le hε hεM hM (critGap a σ xL xR ρL ρR o VL VR B ζ
        (lifetime (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω) ω))
      have h2 := abs_le.1 (abs_xlogxReg_clampIcc_le hε hεM hM
        (critGap a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ω))
      show _ ≤ KS
      linarith)
    simpa using this
  set Y : Ω → ℝ := fun ω => ∫ r in (ratTime q₀ : ℝ)..(lifetime
      (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
      xlogxReg'' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω)) with hY
  set K₁ := critK₁ xL ρL o M
  set CH := critC' a ρR M * ((t : ℝ) - ratTime q₀)
  set A : Ω → ℝ := fun ω => ∫ r in (ratTime q₀ : ℝ)..(lifetime
      (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
      xlogxReg' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω)) *
        gapOutDrift ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) o r with hA
  have hAi' : Integrable (fun ω => -A ω) P := hAi.neg
  have hRi : Integrable (fun ω => K₁ + CH + a / 4 * Y ω) P :=
    (integrable_const (K₁ + CH)).add (hYi.const_mul (a / 4))
  have hAge : ∫ ω, -A ω ∂P ≤ ∫ ω, (K₁ + CH + a / 4 * Y ω) ∂P := by
    refine integral_mono_ae hAi' hRi ?_
    filter_upwards [hpath, hBc] with ω hp hc
    have h' : -(K₁ + a / 4 * Y ω + CH) ≤ A ω :=
      hp.isForcePath.integral_xlogxReg'_mul_ge hp.driverEq hS ho (continuous_const.mul hc)
        (n := n) ha hε hε1 hM hqt
    show -A ω ≤ K₁ + CH + a / 4 * Y ω
    linarith
  rw [integral_neg, integral_add (integrable_const _) (hYi.const_mul _), integral_const_mul]
    at hAge
  simp only [integral_const, probReal_univ, one_smul] at hAge
  have hfinal : a / 4 * ∫ ω, Y ω ∂P ≤ KS + K₁ + CH := by linarith
  refine ⟨hYi, ?_⟩
  unfold critKY
  rw [show 4 / a * (KS + K₁ + CH) = (4 * (KS + K₁ + CH)) / a by ring, le_div_iff₀ ha]
  linarith

theorem critKY_nonneg (ha : 0 < a) {M H : ℝ} (hM : 1 ≤ M) (hH : 0 ≤ H) :
    0 ≤ critKY a xL ρL ρR o M H := by
  have hlogM := Real.log_nonneg hM
  have hK1 : 0 ≤ critK₁ xL ρL o M := Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (by
      have : 0 ≤ (1 + Real.log M) * |xL i - xL o| := mul_nonneg (by linarith) (abs_nonneg _)
      linarith)
  have hC' : 0 ≤ critC' a ρR M := by unfold critC'; positivity
  have hMl : 0 ≤ M * Real.log M := mul_nonneg (by linarith) hlogM
  unfold critKY
  have : 0 ≤ critC' a ρR M * H := mul_nonneg hC' hH
  positivity

/-- **Markov's inequality for the localized `∫ dt/Q`**: `P(∫_q^ρ F''(X) ≥ L) ≤ critKY / L`. -/
theorem measure_le_critY_le (ha : 0 < a) (hBf : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))
    (hζ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | (u : ℝ≥0∞) < ζ ω}) (hσ : σ ^ 2 = 1)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => σ * B t ω) (ζ ω))
    (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o) (q₀ : ℚ) {t : ℝ≥0} (hqt : ratTime q₀ ≤ t)
    {ε M : ℝ} (n : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 1 ≤ M) {L : ℝ} (hL : 0 < L) :
    P {ω | L ≤ ∫ r in (ratTime q₀ : ℝ)..(lifetime
        (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
        xlogxReg'' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω))} ≤
      ENNReal.ofReal (critKY a xL ρL ρR o M ((t : ℝ) - ratTime q₀) / L) := by
  obtain ⟨hYi, hY⟩ := integrable_and_integral_critY_le (W := W) ha hBf hBc hVL hVR hζ hσ hpath hS
    ho q₀ hqt n hε hε1 hM
  have hY0 : 0 ≤ᵐ[P] fun ω => ∫ r in (ratTime q₀ : ℝ)..(lifetime
      (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
      xlogxReg'' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω)) :=
    Eventually.of_forall fun ω => intervalIntegral.integral_nonneg
      (by exact_mod_cast le_lifetimeOf _ _ _) fun r _ => (xlogxReg''_pos hε _).le
  have hmk := mul_meas_ge_le_integral_of_nonneg hY0 hYi L
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hL]
  have : P.real {ω | L ≤ ∫ r in (ratTime q₀ : ℝ)..(lifetime
      (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
      xlogxReg'' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω))} =
    (P {ω | L ≤ ∫ r in (ratTime q₀ : ℝ)..(lifetime
      (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) ε M n) (ratTime q₀) t ω),
      xlogxReg'' ε (clampIcc ε M (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω))}).toReal := rfl
  rw [← this]
  linarith

/-- The event of a localized critical escape: the path is a solution, `B` is continuous, the
lifetime `T` lies in `(q, q + H]`, on `[q, T)` the gap is `< M` and the driver is at distance
`> 1` from every right force point, and `∫_q^u dt/Q` is unbounded for `u < T`. -/
def critEscapeSet (a σ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (o : Fin nL) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q₀ : ℚ) (M H : ℕ) :
    Set Ω :=
  {ω | IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => σ * B t ω) (ζ ω) ∧ Continuous (fun t => B t ω) ∧
    ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω ∧ ratTime q₀ < T ∧ T ≤ ratTime q₀ + H ∧
      (∀ s : ℝ≥0, ratTime q₀ ≤ s → s < T → W s ω - VL o s ω < M ∧ ∀ j, W s ω < VR j s ω - 1) ∧
      ∀ K : ℝ, ∃ u : ℝ≥0, ratTime q₀ ≤ u ∧ u < T ∧
        K < ∫ r in (ratTime q₀ : ℝ)..u, (W r.toNNReal ω - VL o r.toNNReal ω)⁻¹}

/-- **On a localized critical escape the localized `∫ dt/Q` is eventually large**: for every
`L` there is `N` such that for all `k ≥ N` (with `ε = 1/(k+1)`, `n = k`, horizon `q + H`) the
localized integral exceeds `L`. -/
theorem exists_forall_le_critY (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o) {q₀ : ℚ} {M H : ℕ}
    {ω : Ω} (hω : ω ∈ critEscapeSet a σ xL xR ρL ρR o W VL VR B ζ q₀ M H) (L : ℝ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → L ≤ ∫ r in (ratTime q₀ : ℝ)..(lifetime
        (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) (1 / ((k : ℝ) + 1)) M k)
        (ratTime q₀) (ratTime q₀ + H) ω),
      xlogxReg'' (1 / ((k : ℝ) + 1)) (clampIcc (1 / ((k : ℝ) + 1)) M
        (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω)) := by
  obtain ⟨hp, hc, T, hTζ, hqT, hTH, hbd, hint⟩ := hω
  have hF := hp.isForcePath
  have hw := hp.driverEq
  have hb : Continuous fun t => σ * B t ω := continuous_const.mul hc
  obtain ⟨u, hqu, huT, hLu⟩ := hint L
  have hlt : ∀ s : ℝ≥0, s ≤ u → (s : ℝ≥0∞) < ζ ω := fun s hs => by
    rw [← hTζ]; exact_mod_cast hs.trans_lt huT
  have huζ := hlt u le_rfl
  have hQc : ContinuousOn (fun s => W s ω - VL o s ω) (Icc (ratTime q₀) u) :=
    (hF.continuousOn_w.sub (hF.continuousOn_vL o)).mono fun s hs => hlt s hs.2
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hqu) hQc
  have hm₀ : 0 < W s₀ ω - VL o s₀ ω := hF.gap_out_pos hS ho (hlt s₀ hs₀.2)
  obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt hm₀
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (-VL o u ω)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (∑ j, |VR j u ω|)
  refine ⟨max N₁ (max N₂ N₃), fun k hk => ?_⟩
  have hk1 : (N₁ : ℝ) ≤ k := by exact_mod_cast (le_max_left _ _).trans hk
  have hk2 : (N₂ : ℝ) ≤ k := by exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hk3 : (N₃ : ℝ) ≤ k := by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hεm : ε < W s₀ ω - VL o s₀ ω :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hN₁
  -- the closed bounds on `[q, u]`
  have hB1 : ∀ s : ℝ≥0, ratTime q₀ ≤ s → s ≤ u →
      ε < W s ω - VL o s ω ∧ W s ω - VL o s ω < M ∧ -(k : ℝ) < VL o s ω ∧
        ∀ j, VR j s ω < k ∧ W s ω < VR j s ω - 1 := fun s hs1 hs2 => by
    have hsζ := hlt s hs2
    refine ⟨hεm.trans_le (hmin ⟨hs1, hs2⟩), (hbd s hs1 (hs2.trans_lt huT)).1, ?_, fun j => ⟨?_,
      (hbd s hs1 (hs2.trans_lt huT)).2 j⟩⟩
    · have := hF.vL_le_of_le hs2 huζ o
      linarith
    · have h1 := hF.le_vR_of_le hs2 huζ j
      have h2 : VR j u ω ≤ ∑ j, |VR j u ω| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |VR j u ω|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ j))
      linarith
  -- alive at `u`
  have hA : critAlivePath a xL xR ρL ρR o (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => σ * B t ω) (ζ ω) (ratTime q₀) ε M k u := by
    refine Or.inr ⟨huζ, fun r hr1 hr2 => ?_⟩
    have hrζ := hlt _ hr2
    rw [hF.gapExt_eq hw hS hrζ, hF.lowerExtPath_vL_eq hrζ]
    obtain ⟨h1, h2, h3, h4⟩ := hB1 _ hr1 hr2
    refine ⟨h1, h2, h3, fun j => ?_⟩
    simp only [hF.upperExtPath_vR_eq hrζ]
    exact ⟨(h4 j).1, by linarith [(h4 j).2]⟩
  have hA0 := CritAlive.anti _ _ hqu hA
  have hut : u ≤ ratTime q₀ + H := huT.le.trans hTH
  have hρ : u ≤ lifetimeOf (critAlivePath a xL xR ρL ρR o (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => σ * B t ω) (ζ ω) (ratTime q₀) ε M k)
      (ratTime q₀) (ratTime q₀ + H) := le_lifetimeOf_of hut hA
  have hX := hF.continuousOn_clamp_Icc_real hw hS ho hb hA0 (t := ratTime q₀ + H)
  have hint' := ((continuous_xlogxReg'' hε).comp_continuousOn hX).intervalIntegrable (μ := volume)
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) le_rfl
    (show (ratTime q₀ : ℝ) ≤ u from hqu) (show (u : ℝ) ≤ _ from hρ)
    (Eventually.of_forall fun r => (xlogxReg''_pos hε _).le) hint'
  have hcongr : ∫ r in (ratTime q₀ : ℝ)..u, xlogxReg'' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => σ * B t ω)
        (ζ ω) r.toNNReal)) =
      ∫ r in (ratTime q₀ : ℝ)..u, (W r.toNNReal ω - VL o r.toNNReal ω)⁻¹ := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (show (ratTime q₀ : ℝ) ≤ u from hqu)] at hr
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg _).trans hr.1
    have hs1 : ratTime q₀ ≤ r.toNNReal := (Real.le_toNNReal_iff_coe_le hr0).2 hr.1
    have hs2 : r.toNNReal ≤ u := Real.toNNReal_le_iff_le_coe.2 hr.2
    obtain ⟨h1, h2, -⟩ := hB1 _ hs1 hs2
    rw [hF.gapExt_eq hw hS (hlt _ hs2), clampIcc_eq h1.le h2.le, xlogxReg''_eq h1.le]
  exact hLu.le.trans (hcongr ▸ hmono)

/-- **A localized critical escape is null** (Specification p. 28, "(N6) rules out escape on each
such event"). -/
theorem measure_critEscapeSet (ha : 0 < a) (hBf : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))
    (hζ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | (u : ℝ≥0∞) < ζ ω}) (hσ : σ ^ 2 = 1)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => σ * B t ω) (ζ ω))
    (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o) (q₀ : ℚ) {M H : ℕ} (hM : 1 ≤ M) :
    P (critEscapeSet a σ xL xR ρL ρR o W VL VR B ζ q₀ M H) = 0 := by
  set E := critEscapeSet a σ xL xR ρL ρR o W VL VR B ζ q₀ M H
  set t : ℝ≥0 := ratTime q₀ + H with ht
  have hqt : ratTime q₀ ≤ t := le_self_add
  have htq : (t : ℝ) - ratTime q₀ = H := by simp [ht]
  set KY := critKY a xL ρL ρR o (M : ℝ) (H : ℝ)
  have hKY : 0 ≤ KY := critKY_nonneg ha (by exact_mod_cast hM) (Nat.cast_nonneg _)
  have hbound : ∀ L : ℝ, 0 < L → P E ≤ ENNReal.ofReal (KY / L) := by
    intro L hL
    set A : ℕ → Set Ω := fun N => {ω | ∀ k : ℕ, N ≤ k → L ≤ ∫ r in (ratTime q₀ : ℝ)..(lifetime
        (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) (1 / ((k : ℝ) + 1)) M k)
        (ratTime q₀) t ω),
      xlogxReg'' (1 / ((k : ℝ) + 1)) (clampIcc (1 / ((k : ℝ) + 1)) M
        (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω))} with hAdef
    have hAmono : Monotone A := fun N N' hNN' ω hω k hk => hω k (hNN'.trans hk)
    have hsub : E ⊆ ⋃ N, A N := fun ω hω => by
      obtain ⟨N, hN⟩ := exists_forall_le_critY hS ho hω L
      exact mem_iUnion.2 ⟨N, hN⟩
    have hAN : ∀ N, P (A N) ≤ ENNReal.ofReal (KY / L) := fun N => by
      have hsub' : A N ⊆ {ω | L ≤ ∫ r in (ratTime q₀ : ℝ)..(lifetime
          (critAliveSet a σ xL xR ρL ρR o VL VR B ζ (ratTime q₀) (1 / ((N : ℝ) + 1)) M N)
          (ratTime q₀) t ω), xlogxReg'' (1 / ((N : ℝ) + 1)) (clampIcc (1 / ((N : ℝ) + 1)) M
            (critGap a σ xL xR ρL ρR o VL VR B ζ r.toNNReal ω))} := fun ω hω => hω N le_rfl
      refine (measure_mono hsub').trans ?_
      have hN1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have := measure_le_critY_le (W := W) ha hBf hBc hVL hVR hζ hσ hpath hS ho q₀ hqt N
        (ε := 1 / ((N : ℝ) + 1)) (M := M) (by positivity) hN1 (by exact_mod_cast hM) hL
      rwa [htq] at this
    calc P E ≤ P (⋃ N, A N) := measure_mono hsub
      _ = ⨆ N, P (A N) := hAmono.measure_iUnion
      _ ≤ _ := iSup_le hAN
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) (zero_le : (0 : ℝ≥0∞) ≤ _)
  rw [zero_add]
  have hη' : (0 : ℝ) < η := hη
  have hL : 0 < (KY + 1) / η := by positivity
  refine (hbound _ hL).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **No critical escape on the left** (Aux. lemma 3, the critical side total `s = −2`;
Specification pp. 27–28): if `∑ ρ^{i,L} = −2`, then almost surely, at every finite positive
lifetime `ζ = T` at which the right force points stay bounded above, the left force points stay
bounded below. -/
theorem ae_bddBelow_of_sum_eq (ha : 0 < a) (hBf : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))
    (hζ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | (u : ℝ≥0∞) < ζ ω}) (hσ : σ ^ 2 = 1)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => σ * B t ω) (ζ ω))
    (hS : ∑ i, ρL i = -2) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → VR j s ω ≤ M) →
      ∀ i, ∃ m : ℝ, ∀ s : ℝ≥0, s < T → m ≤ VL i s ω := by
  rcases Nat.eq_zero_or_pos nL with hn | hn
  · subst hn
    exact Eventually.of_forall fun ω T _ _ _ i => i.elim0
  obtain ⟨o, ho⟩ := exists_forall_le_fin (⟨0, hn⟩ : Fin nL)
  have hnull : ∀ᵐ ω ∂P, ∀ q₀ : ℚ, ∀ M H : ℕ,
      ω ∉ critEscapeSet a σ xL xR ρL ρR o W VL VR B ζ q₀ (M + 1) H := by
    refine ae_all_iff.2 fun q₀ => ae_all_iff.2 fun M => ae_all_iff.2 fun H => ?_
    exact measure_eq_zero_iff_ae_notMem.1 (measure_critEscapeSet ha hBf hBc hVL hVR hζ hσ hpath hS
      ho q₀ (Nat.le_add_left 1 M))
  filter_upwards [hpath, hBc, hnull] with ω hp hc hnot T _ hTζ hR
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := hcon
  have hF := hp.isForcePath
  have hw := hp.driverEq
  have hb : Continuous fun t => σ * B t ω := continuous_const.mul hc
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < ζ ω := fun s hs => by
    rw [← hTζ]; exact_mod_cast hs
  have hesc : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ VL o s ω < m := fun m => by
    obtain ⟨s, hs, hms⟩ := hi m
    exact ⟨s, hs, (hF.antitone_vL (hlt s hs) (ho i)).trans_lt hms⟩
  obtain ⟨K₀, hK₀⟩ := hF.exists_bound_gap_out hw hTζ hb.continuousOn ho hS hR
  obtain ⟨s₁, hs₁T, hs₁⟩ := hesc (-(∑ j, |xR j|) - 1 - K₀)
  have hWlt : ∀ s : ℝ≥0, s₁ ≤ s → s < T → ∀ j, W s ω < VR j s ω - 1 := fun s hs1 hs2 j => by
    have h1 := hF.vL_le_of_le hs1 (hlt s hs2) o
    have h2 := hK₀ s hs2
    have h3 := hF.xR_le_vR (hlt s hs2) j
    have h4 : xR j ≥ -(∑ j, |xR j|) := by
      have := Finset.single_le_sum (f := fun j => |xR j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)
      linarith [neg_abs_le (xR j)]
    linarith
  obtain ⟨q₀, hq1, hq2⟩ := exists_ratTime_btwn hs₁T
  refine hnot q₀ ⌈K₀⌉₊ ⌈(T : ℝ)⌉₊ ⟨hp, hc, T, hTζ, hq2, ?_, fun s hs1 hs2 => ⟨?_,
    hWlt s (hq1.le.trans hs1) hs2⟩, fun K => ?_⟩
  · rw [← NNReal.coe_le_coe]
    push_cast
    linarith [Nat.le_ceil (T : ℝ), NNReal.coe_nonneg (ratTime q₀)]
  · push_cast
    linarith [Nat.le_ceil K₀, hK₀ s hs2]
  · have hqζ := hlt _ hq2
    obtain ⟨t₁, ht₁T, ht₁⟩ := hF.integral_inv_gap_out_unbounded hTζ hesc
      (K + ∫ r in (0 : ℝ)..(ratTime q₀ : ℝ), (W r.toNNReal ω - VL o r.toNNReal ω)⁻¹)
    refine ⟨max t₁ (ratTime q₀), le_max_right _ _, max_lt ht₁T hq2, ?_⟩
    have huζ := hlt _ (max_lt ht₁T hq2)
    have hiu := hF.integrable_gapL huζ o
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) le_rfl
      (show (0 : ℝ) ≤ t₁ from NNReal.coe_nonneg _)
      (show (t₁ : ℝ) ≤ (max t₁ (ratTime q₀) : ℝ≥0) from by exact_mod_cast le_max_left _ _)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => by
        have hr' : r.toNNReal ≤ max t₁ (ratTime q₀) := Real.toNNReal_le_iff_le_coe.2 hr.2
        have hrζ : (r.toNNReal : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr') huζ
        exact inv_nonneg.2 (sub_nonneg.2 (hF.vL_le_w hrζ o)))) hiu
    have hsplit := intervalIntegral.integral_interval_sub_left hiu (hF.integrable_gapL hqζ o)
    linarith

end Process

end Sec2

end InteractingSLE
