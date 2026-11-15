/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualGirsanov
import MathFin.Probability.Martingales.UnifIntegrableL2

/-!
# Girsanov with the other curve frozen, II: removing the localization

Packet PROVE-ZHAN-GT4-A9. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L341–L351, R38).

For a driver log-field `ℓ` up to `S ≤ R` and `a ∈ ℝ`, the tilted exponential
`N^a_t = exp ℓ^a(t, σB_t) = (M_t/M_0) exp(a(B_t − B_0) − aI_t − a²t/2)` stopped at `S` is a martingale:
`E[ξ N^a_{t∧S}] = E[ξ N^a_{s∧S}]` for bounded `𝓕_s`-measurable `ξ` (`integral_mul_tilt_stopped_eq`).
`IsDriverLogField.tilt` gives this up to the localizations `S_N`; as `N → ∞`, `t ∧ S_N = t ∧ S` eventually for every
path, and the second moments are bounded uniformly in `N`: `(N^a)² ≤ C e^{a²t} Z^{2a}` where `Z^{2a}` is the tilted
exponential of the **zero** log-field with parameter `2a` (the Brownian exponential `exp(2a(B − B_0) − 2a²t)`), whose
stopped mean is `1` by the same theorem. Vitali (MathFin's `L²`-bounded set-integral limit) passes to the limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Sec6.Prop65 (hitLe)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### A limit of equal integrals -/

/-- **Equal integrals pass to pointwise limits under a uniform `L²` bound.** -/
theorem integral_eq_of_tendsto_of_sq_bound {P : Measure Ω} [IsProbabilityMeasure P] {f h : ℕ → Ω → ℝ}
    {g k : Ω → ℝ} (hfm : ∀ n, Measurable (f n)) (hhm : ∀ n, Measurable (h n)) (hf2 : ∀ n, MemLp (f n) 2 P)
    (hh2 : ∀ n, MemLp (h n) 2 P) {M : ℝ} (hfM : ∀ n, ∫ ω, (f n ω) ^ 2 ∂P ≤ M) (hhM : ∀ n, ∫ ω, (h n ω) ^ 2 ∂P ≤ M)
    (hfg : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) (hhk : ∀ ω, Tendsto (fun n => h n ω) atTop (𝓝 (k ω)))
    (heq : ∀ n, ∫ ω, f n ω ∂P = ∫ ω, h n ω ∂P) : ∫ ω, g ω ∂P = ∫ ω, k ω ∂P := by
  have hg2 : MemLp g 2 P := MathFin.memLp_two_of_subseq_ae_of_sq_bound hf2 hfm hfM ⟨id, ae_of_all _ hfg⟩
  have hk2 : MemLp k 2 P := MathFin.memLp_two_of_subseq_ae_of_sq_bound hh2 hhm hhM ⟨id, ae_of_all _ hhk⟩
  have hg1 : MemLp g 1 P := hg2.mono_exponent (by norm_num)
  have hk1 : MemLp k 1 P := hk2.mono_exponent (by norm_num)
  have hT1 := MathFin.tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound hf2 hfM hg1
    (tendstoInMeasure_of_tendsto_ae (fun n => (hfm n).aestronglyMeasurable) (ae_of_all _ hfg)) univ
  have hT2 := MathFin.tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound hh2 hhM hk1
    (tendstoInMeasure_of_tendsto_ae (fun n => (hhm n).aestronglyMeasurable) (ae_of_all _ hhk)) univ
  simp only [Measure.restrict_univ] at hT1 hT2
  exact tendsto_nhds_unique (hT1.congr fun n => heq n) hT2

/-! ### The zero log-field -/

/-- The zero field. -/
def zeroL : Ω → ℝ → ℝ → ℝ := fun _ _ _ => 0

variable {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}

/-- **The zero field is a driver log-field** (with the bound `0`). -/
theorem isDriverLogField_zeroL (hρ : 0 < ρ) :
    IsDriverLogField 𝓕 σ ρ 0 B S (zeroL (Ω := Ω)) zeroL zeroL zeroL zeroL where
  loc ω b c y _ _ _ _ :=
    { pos := hρ
      Knonneg := le_rfl
      dx := fun _ _ x _ => hasDerivAt_const x (0 : ℝ)
      dxx := fun _ _ x _ => hasDerivAt_const x (0 : ℝ)
      dxxx := fun _ _ x _ => hasDerivAt_const x (0 : ℝ)
      dt := fun t _ _ _ => hasDerivWithinAt_const t _ (0 : ℝ)
      cont := continuousOn_const
      contX := continuousOn_const
      contXX := continuousOn_const
      contT := continuousOn_const
      bound := fun _ _ _ _ => by simp [zeroL] }
  gen ω r _ _ := by simp [zeroL]
  meas0 r := by
    simp only [zeroL]
    rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, indicator_zero']
    exact measurable_const
  meas1 r := by
    simp only [zeroL]
    rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, indicator_zero']
    exact measurable_const
  meas2 r := by
    simp only [zeroL]
    rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, indicator_zero']
    exact measurable_const

omit mΩ in
theorem drvInt_zeroL (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ω : Ω) (t : ℝ) :
    drvInt σ B S zeroL ω t = 0 := by
  simp [drvInt, drvTheta, drvRate, zeroL]

omit mΩ in
/-- The tilted zero field along the driver: `exp(a(B_r − B_0) − a²r/2)`. -/
theorem logFieldExp_tilt_zeroL (hσ : σ ≠ 0) (a : ℝ) (r : ℝ≥0) (ω : Ω) :
    logFieldExp σ B (tiltL σ a B S zeroL zeroL) r ω = Real.exp (a * (B r ω - B 0 ω) - a ^ 2 / 2 * r) := by
  simp only [logFieldExp, tiltL, tiltB, drvInt_zeroL, zeroL]
  congr 1
  field_simp
  ring

omit mΩ in
/-- The tilted exponential along the driver. -/
theorem logFieldExp_tilt (hσ : σ ≠ 0) (a : ℝ) (r : ℝ≥0) (ω : Ω) :
    logFieldExp σ B (tiltL σ a B S ℓ ℓx) r ω = Real.exp (ℓ ω r (σ * B r ω) - ℓ ω 0 (σ * B 0 ω) +
      a * (B r ω - B 0 ω) - a * drvInt σ B S ℓx ω r - a ^ 2 / 2 * r) := by
  simp only [logFieldExp, tiltL, tiltB]
  congr 1
  field_simp
  ring

/-! ### Removing the localization -/

omit mΩ in
/-- For every path, `t ∧ S_N = t ∧ S` for all large `N`. -/
theorem eventually_min_stopN_eq (hBc : ∀ ω, Continuous (B · ω)) {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (t : ℝ≥0)
    (ω : Ω) : ∀ᶠ N : ℕ in atTop, min t (stopN B S R ((N : ℝ) + 1) ω) = min t (S ω) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (f := fun u => B u ω - B 0 ω) ((hBc ω).sub continuous_const).continuousOn
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt M
  refine eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
  have hNM : M < (N : ℝ) + 1 := hN₀.trans (by exact_mod_cast Nat.lt_succ_of_le hN)
  have hle : min t (S ω) ≤ hitLe (stopY B ((N : ℝ) + 1)) 0 R ω := by
    refine Sec6.Prop65.le_hitLe_of_forall (fun ω => continuous_stopY hBc _ ω) ((min_le_right _ _).trans (hSR ω))
      fun u hu => ?_
    have h1 := hM u ⟨zero_le, hu.trans (min_le_left _ _)⟩
    rw [Real.norm_eq_abs] at h1
    simp only [stopY]; linarith
  simp only [stopN]
  rw [← min_assoc, min_eq_left hle]

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- **The second moment of the tilted exponential** is dominated by the tilted zero exponential with parameter
`2a`: `(N^a_τ)² ≤ e^{4K + 2|a|σKR} e^{a²τ} Z^{2a}_τ` for `τ ≤ S ≤ R`. -/
theorem sq_logFieldExp_tilt_le (hσ : 0 < σ) (hρ : 0 < ρ) {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (a : ℝ) {τ : ℝ≥0}
    {ω : Ω} (hτ : τ ≤ S ω) :
    (logFieldExp σ B (tiltL σ a B S ℓ ℓx) τ ω) ^ 2 ≤ Real.exp (4 * K + 2 * (|a| * (σ * K * R))) *
      Real.exp (a ^ 2 * τ) * logFieldExp σ B (tiltL σ (2 * a) B S zeroL zeroL) τ ω := by
  rw [logFieldExp_tilt hσ.ne', logFieldExp_tilt_zeroL hσ.ne', sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := hL.abs_le hρ ω ⟨τ.coe_nonneg, NNReal.coe_le_coe.2 hτ⟩
  have h0 := hL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩
  have hI := hL.abs_drvInt_le hρ ω τ.coe_nonneg
  simp only [Real.toNNReal_coe] at h1
  simp only [Real.toNNReal_zero] at h0
  rw [abs_of_pos hσ] at hI
  have hK : 0 ≤ K := (abs_nonneg _).trans h0
  have hτR : (τ : ℝ) ≤ R := NNReal.coe_le_coe.2 (hτ.trans (hSR ω))
  have hIa : |a * drvInt σ B S ℓx ω τ| ≤ |a| * (σ * K * R) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_left hτR (by positivity))) (abs_nonneg a)
  have e1 := _root_.abs_le.1 h1
  have e0 := _root_.abs_le.1 h0
  have eI := _root_.abs_le.1 hIa
  have e2 : (2 * a) ^ 2 / 2 * (τ : ℝ) = 2 * (a ^ 2 * τ) := by ring
  have e3 : a ^ 2 / 2 * (τ : ℝ) = (a ^ 2 * τ) / 2 := by ring
  rw [e2, e3]
  linarith

/-- **The tilted exponential stopped at `S` is a martingale** (§A.1.3, Girsanov's exponential identity without
stochastic integrals): `E[ξ N^a_{t∧S}] = E[ξ N^a_{s∧S}]` for every bounded `𝓕_s`-measurable `ξ`, where
`N^a_r = exp ℓ^a(r, σB_r) = (M_r/M_0) exp(a(B_r − B_0) − aI_r − a²r/2)`. -/
theorem integral_mul_tilt_stopped_eq {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ)
    (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * logFieldExp σ B (tiltL σ a B S ℓ ℓx) (min t (S ω)) ω ∂P =
      ∫ ω, ξ ω * logFieldExp σ B (tiltL σ a B S ℓ ℓx) (min s (S ω)) ω ∂P := by
  have hP := hB.isProbabilityMeasure'
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hξm : Measurable ξ := hξ.mono (𝓕.le s) le_rfl
  have hNn : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  have hLN := fun N : ℕ => hL.tilt hBc hBm hσ hρ hS hSR a (hNn N)
  have hZ := isDriverLogField_zeroL (𝓕 := 𝓕) (σ := σ) (B := B) (S := S) hρ
  have hZN := fun N : ℕ => hZ.tilt hBc hBm hσ hρ hS hSR (2 * a) (hNn N)
  have hTN := fun N : ℕ => isStoppingTime_stopN hBc hBm hS R ((N : ℝ) + 1)
  set X := logFieldExp σ B (tiltL σ a B S ℓ ℓx) with hXdef
  set Z := logFieldExp σ B (tiltL σ (2 * a) B S zeroL zeroL) with hZdef
  have hXm : ∀ (N : ℕ) (u : ℝ≥0), Measurable fun ω => X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω := fun N u =>
    ((hLN N).measurable_logFieldExp_stopped hBc hρ (hTN N) (fun ω => le_rfl) u).mono (𝓕.le u) le_rfl
  have hXb : ∀ (N : ℕ) (u : ℝ≥0) ω, |X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω| ≤
      Real.exp (K + tiltBound σ ρ K R a ((N : ℝ) + 1)) := fun N u ω =>
    (hLN N).abs_logFieldExp_le hρ (min_le_right _ _)
  have hZm : ∀ (N : ℕ) (u : ℝ≥0), Measurable fun ω => Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω := fun N u =>
    ((hZN N).measurable_logFieldExp_stopped hBc hρ (hTN N) (fun ω => le_rfl) u).mono (𝓕.le u) le_rfl
  have hZb : ∀ (N : ℕ) (u : ℝ≥0) ω, |Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω| ≤
      Real.exp (0 + tiltBound σ ρ 0 R (2 * a) ((N : ℝ) + 1)) := fun N u ω =>
    (hZN N).abs_logFieldExp_le hρ (min_le_right _ _)
  have hZi : ∀ (N : ℕ) (u : ℝ≥0), Integrable (fun ω => Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) P :=
    fun N u => (integrable_const _).mono' (hZm N u).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb N u ω)
  have hXi : ∀ (N : ℕ) (u : ℝ≥0), Integrable (fun ω => ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) P :=
    fun N u => (integrable_const (Real.exp (K + tiltBound σ ρ K R a ((N : ℝ) + 1)))).mono'
      (hξm.mul (hXm N u)).aestronglyMeasurable (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |ξ ω| * |X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω|
            ≤ 1 * Real.exp (K + tiltBound σ ρ K R a ((N : ℝ) + 1)) :=
              mul_le_mul (hξb ω) (hXb N u ω) (abs_nonneg _) zero_le_one
          _ = _ := one_mul _)
  -- the stopped mean of the zero tilt is `1`
  have hZ1 : ∀ (N : ℕ) (u : ℝ≥0), ∫ ω, Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω ∂P = 1 := fun N u => by
    have h := (hZN N).integral_mul_logField_stopped_sub_eq_zero hB hBc hσ.le hρ (hTN N) (zero_le (a := u))
      (ξ := fun _ => 1) measurable_const (fun _ => by simp)
    simp only [one_mul] at h
    rw [integral_sub (hZi N u) (hZi N 0)] at h
    have h0 : ∀ ω, Z (min 0 (stopN B S R ((N : ℝ) + 1) ω)) ω = 1 := fun ω => by
      rw [min_eq_left zero_le, hZdef, logFieldExp_tilt_zeroL hσ.ne']; simp
    simp only [h0, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    linarith
  -- the second moments
  set C := Real.exp (4 * K + 2 * (|a| * (σ * K * R))) * Real.exp (a ^ 2 * t) with hCdef
  have hsq : ∀ (N : ℕ) (u : ℝ≥0), u ≤ t →
      ∫ ω, (ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) ^ 2 ∂P ≤ C := by
    intro N u hut
    have hpt : ∀ ω, (ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) ^ 2 ≤
        C * Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω := fun ω => by
      have hτS : min u (stopN B S R ((N : ℝ) + 1) ω) ≤ S ω := (min_le_right _ _).trans (stopN_le R _ ω)
      have h1 := hL.sq_logFieldExp_tilt_le hσ hρ hSR a hτS
      have hτt : ((min u (stopN B S R ((N : ℝ) + 1) ω) : ℝ≥0) : ℝ) ≤ t :=
        NNReal.coe_le_coe.2 ((min_le_left _ _).trans hut)
      have hZ0 : 0 ≤ Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω := (Real.exp_pos _).le
      have hξ1 : ξ ω ^ 2 ≤ 1 := by
        have := hξb ω; rw [← sq_abs]; nlinarith [abs_nonneg (ξ ω)]
      calc (ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) ^ 2
          = ξ ω ^ 2 * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω ^ 2 := by ring
        _ ≤ 1 * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω ^ 2 :=
            mul_le_mul_of_nonneg_right hξ1 (sq_nonneg _)
        _ ≤ Real.exp (4 * K + 2 * (|a| * (σ * K * R))) * Real.exp (a ^ 2 * ↑(min u (stopN B S R ((N : ℝ) + 1) ω))) *
              Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω := by rw [one_mul]; exact h1
        _ ≤ C * Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω := by
            refine mul_le_mul_of_nonneg_right ?_ hZ0
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτt (sq_nonneg a)))
              (Real.exp_pos _).le
    calc ∫ ω, (ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) ^ 2 ∂P
        ≤ ∫ ω, C * Z (min u (stopN B S R ((N : ℝ) + 1) ω)) ω ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) ((hZi N u).const_mul C)
            (Eventually.of_forall hpt)
      _ = C := by rw [integral_const_mul, hZ1, mul_one]
  -- the limit
  have hMemLp : ∀ (N : ℕ) (u : ℝ≥0), MemLp (fun ω => ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) 2 P :=
    fun N u => MemLp.of_bound (hξm.mul (hXm N u)).aestronglyMeasurable
      (Real.exp (K + tiltBound σ ρ K R a ((N : ℝ) + 1))) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |ξ ω| * |X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω|
            ≤ 1 * Real.exp (K + tiltBound σ ρ K R a ((N : ℝ) + 1)) :=
              mul_le_mul (hξb ω) (hXb N u ω) (abs_nonneg _) zero_le_one
          _ = _ := one_mul _)
  have hconv : ∀ (u : ℝ≥0) ω, Tendsto (fun N : ℕ => ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω) atTop
      (𝓝 (ξ ω * X (min u (S ω)) ω)) := fun u ω =>
    tendsto_const_nhds.congr' ((eventually_min_stopN_eq hBc hSR u ω).mono fun N hN => by
      show _ = ξ ω * X (min u (stopN B S R ((N : ℝ) + 1) ω)) ω
      rw [hN])
  refine integral_eq_of_tendsto_of_sq_bound (f := fun N ω => ξ ω * X (min t (stopN B S R ((N : ℝ) + 1) ω)) ω)
    (h := fun N ω => ξ ω * X (min s (stopN B S R ((N : ℝ) + 1) ω)) ω) (fun N => hξm.mul (hXm N t))
    (fun N => hξm.mul (hXm N s))
    (fun N => hMemLp N t) (fun N => hMemLp N s) (fun N => hsq N t le_rfl) (fun N => hsq N s hst)
    (hconv t) (hconv s) fun N => ?_
  have h := (hLN N).integral_mul_logField_stopped_sub_eq_zero hB hBc hσ.le hρ (hTN N) hst hξ hξb
  simp only [mul_sub] at h
  rw [integral_sub (hXi N t) (hXi N s)] at h
  linarith

end IsDriverLogField

end InteractingSLE.ZhanGT4
