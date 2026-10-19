import HigherDimLFPP.Field.LogCov

/-!
# Lemma 3.1: the transport covariance bound (packet P-F2, target T4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.1, (3.4) and Lemma 3.1 ((3.5)–(3.7));
planning audit HA2 (`planning/audits/HA2-section-3.md`), findings HA2-07, HA2-08, Details D5 and the
Lean block (c) (`GrowthBound`, `CoupledWithin`, `Lemma31`); interface (I4) of HA3 §7.

**Statement** (`transport_cov_bound`).  For every `B` there is `C = C(d, κ, B)` such that for every
measurable scale set `S ⊆ (0, ∞)` (in particular every band `(a, b]`, `0 ≤ a < b ≤ ∞`, including
the all-scale set `(0, ∞)`), all `R, r > 0`, `u, v ≥ 0`, and probability measures `μ_R, ν_R`
(resp. `μ_r, ν_r`) satisfying the growth bound (3.4) at scale `R` (resp. `r`) with constant `B` and
coupled within `u` (resp. `v`):
`IsPairable κ S μ_R ν_R`, `IsPairable κ S μ_r ν_r` and
`|Cov(⟨H_S, μ_R - ν_R⟩, ⟨H_S, μ_r - ν_r⟩)| ≤ C √(uv) / R`.
The paper's hypothesis `r ≤ R` is not needed (HA2-08).  The variance form is
`transport_var_bound`, and the all-scale log-covariance form (constant depending only on `d`, `B`)
is `transport_logCov_bound`.

**Proof** (HA2 D5), at each scale `t > 0`, with `η = μ - ν`, `π` a displacement coupling and
`K_t(v) = t^{-(d+1)/2} κ(v/t)`:

* (i) `(η * K_t)(y) = ∫ (K_t(z - y) - K_t(z' - y)) dπ(z, z')`;
* (ii) sup bound (3.6): `|(η_R * K_t)(y)| ≤ C₁ t^{-(d+1)/2} t min(1, u/t) / R`, from the growth
  bounds of both measures if `u > t` and from the Lipschitz bound and the growth of `μ_R` alone if
  `u ≤ t` (`abs_scaleConv_sub_le_sup`);
* (iii) `L¹` bound (3.7): `∫ |(η_r * K_t)(y)| dy ≤ C₂ t^{-(d+1)/2} t^d min(1, v/t)`, with no growth
  bound (`integral_abs_scaleConv_sub_le`);
* (iv)–(v): `|scalePair κ t η_R η_r| ≤ (C₁ C₂ / R) min(1, u/t) min(1, v/t)
  ≤ (C₁ C₂ / R) min(1, √(uv)/t)²` (`abs_scalePair_le_transport`);
* (vi): `∫₀^∞ min(1, w/t)² dt = 2w` (`integral_min_sq`).

There is no 2D source file for this proof: `LQGDimension.twoScaleCovBound`
(`LQGDimension/LFPP/TwoScale*.lean`) uses the Gaussian heat kernel and a four-point method; this
file follows the paper's `L^∞`–`L¹` argument, as recommended by HA2 §5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

variable {d : ℕ}

/-! ### Growth bounds and displacement couplings -/

/-- Linear growth bound (3.4) at scale `R` with constant `B` (HA2's `GrowthBound`; same body as
`HigherDimLFPP.Upper.GrowthBound`). -/
def GrowthBound (μ : Measure (Rd d)) (B R : ℝ) : Prop :=
  ∀ z : Rd d, ∀ t > 0, μ.real (Metric.closedBall z t) ≤ B * min 1 (t / R)

/-- Displacement coupling of size `u` (HA2's `CoupledWithin`; same body as
`HigherDimLFPP.Upper.CoupledWithin`). -/
def CoupledWithin (μ ν : Measure (Rd d)) (u : ℝ) : Prop :=
  ∃ cpl : Measure (Rd d × Rd d), cpl.map Prod.fst = μ ∧ cpl.map Prod.snd = ν ∧
    ∀ᵐ q ∂cpl, ‖q.1 - q.2‖ ≤ u

/-- A growth bound with constant `B` is one with constant `max B 0`. -/
theorem GrowthBound.max_zero {μ : Measure (Rd d)} {B R : ℝ} (h : GrowthBound μ B R)
    (hR : 0 < R) : GrowthBound μ (max B 0) R := by
  intro z t ht
  have hm : 0 ≤ min 1 (t / R) := le_min zero_le_one (div_nonneg ht.le hR.le)
  exact (h z t ht).trans (mul_le_mul_of_nonneg_right (le_max_left B 0) hm)

/-- A growth bound at scale `R` gives `μ(B̄(z, s)) ≤ B s / R` for `B ≥ 0`. -/
theorem GrowthBound.le_div {μ : Measure (Rd d)} {B R : ℝ} (h : GrowthBound μ B R)
    (hB : 0 ≤ B) (z : Rd d) {s : ℝ} (hs : 0 < s) : μ.real (closedBall z s) ≤ B * (s / R) :=
  (h z s hs).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hB)

theorem FieldAux.isProbabilityMeasure_of_map_fst {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    {cpl : Measure (Rd d × Rd d)} (h : cpl.map Prod.fst = μ) : IsProbabilityMeasure cpl := by
  constructor
  have := Measure.map_apply (μ := cpl) measurable_fst MeasurableSet.univ
  rw [h, preimage_univ, measure_univ] at this
  exact this.symm

/-- Marginal integrals as coupling integrals. -/
theorem FieldAux.integral_eq_integral_fst {μ : Measure (Rd d)} {cpl : Measure (Rd d × Rd d)}
    (h : cpl.map Prod.fst = μ) {f : Rd d → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂μ = ∫ q, f q.1 ∂cpl := by
  rw [← h, integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]

theorem FieldAux.integral_eq_integral_snd {ν : Measure (Rd d)} {cpl : Measure (Rd d × Rd d)}
    (h : cpl.map Prod.snd = ν) {f : Rd d → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂ν = ∫ q, f q.2 ∂cpl := by
  rw [← h, integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]

theorem FieldAux.measureReal_fst_preimage {μ : Measure (Rd d)} {cpl : Measure (Rd d × Rd d)}
    (h : cpl.map Prod.fst = μ) {A : Set (Rd d)} (hA : MeasurableSet A) :
    cpl.real (Prod.fst ⁻¹' A) = μ.real A := by
  rw [← h, measureReal_def, measureReal_def, Measure.map_apply measurable_fst hA]

/-! ### The kernel `K_t` at a fixed scale -/

/-- The prefactor `t^{-(d+1)/2}` of `K_t`. -/
def kpre (d : ℕ) (t : ℝ) : ℝ := t ^ (-((d : ℝ) + 1) / 2)

theorem kpre_pos {t : ℝ} (ht : 0 < t) : 0 < kpre d t := Real.rpow_pos_of_pos ht _

/-- `t^{-(d+1)/2} · t^{-(d+1)/2} · t^d · t = 1`. -/
theorem kpre_mul_kpre_mul {t : ℝ} (ht : 0 < t) : kpre d t * kpre d t * t ^ d * t = 1 := by
  unfold kpre
  rw [← Real.rpow_add ht, ← Real.rpow_natCast, ← Real.rpow_add ht, ← Real.rpow_add_one ht.ne']
  have : -((d : ℝ) + 1) / 2 + -((d : ℝ) + 1) / 2 + (d : ℝ) + 1 = 0 := by ring
  rw [this, Real.rpow_zero]

section Kernel

variable {κ : Rd d → ℝ}

theorem scaleKernel_eq_kpre (t : ℝ) (v : Rd d) : scaleKernel κ t v = kpre d t * κ (t⁻¹ • v) :=
  rfl

/-- `|K_t(v)| ≤ t^{-(d+1)/2} A` for `|κ| ≤ A`. -/
theorem abs_scaleKernel_le {A : ℝ} (hA : ∀ x, |κ x| ≤ A) {t : ℝ} (ht : 0 < t) (v : Rd d) :
    |scaleKernel κ t v| ≤ kpre d t * A := by
  rw [scaleKernel_eq_kpre, abs_mul, abs_of_pos (kpre_pos ht)]
  exact mul_le_mul_of_nonneg_left (hA _) (kpre_pos ht).le

/-- `K_t(v) = 0` for `‖v‖ ≥ ρ t`, if `κ` vanishes outside `B(0, ρ)`. -/
theorem scaleKernel_eq_zero_of_le {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {t : ℝ} (ht : 0 < t)
    {v : Rd d} (hv : ρ * t ≤ ‖v‖) : scaleKernel κ t v = 0 := by
  rw [scaleKernel_eq_kpre, hρ, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_eq_div, le_div_iff₀ ht]
  exact hv

/-- `|K_t(v) - K_t(v')| ≤ t^{-(d+1)/2} K t⁻¹ ‖v - v'‖` for a `K`-Lipschitz `κ`. -/
theorem abs_scaleKernel_sub_le {K : NNReal} (hK : LipschitzWith K κ) {t : ℝ} (ht : 0 < t)
    (v v' : Rd d) :
    |scaleKernel κ t v - scaleKernel κ t v'| ≤ kpre d t * K * (t⁻¹ * ‖v - v'‖) := by
  rw [scaleKernel_eq_kpre, scaleKernel_eq_kpre, ← mul_sub, abs_mul, abs_of_pos (kpre_pos ht),
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (kpre_pos ht).le
  have h := hK.dist_le_mul (t⁻¹ • v) (t⁻¹ • v')
  rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 ht.le)] at h
  exact h

theorem integrable_scaleKernel_comp_sub (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (z : Rd d) :
    Integrable fun y => scaleKernel κ t (z - y) := by
  simp_rw [scaleKernel_eq_kpre]
  exact ((hκ.integrable.comp_smul (inv_ne_zero ht.ne')).comp_sub_left z).const_mul _

/-- `∫ κ(t⁻¹(z - y)) dy = t^d ∫ κ`. -/
theorem integral_kappa_comp (κ : Rd d → ℝ) {t : ℝ} (ht : 0 < t) (z : Rd d) :
    ∫ y, κ (t⁻¹ • (z - y)) = t ^ d * ∫ y, κ y := by
  rw [integral_sub_left_eq_self (fun y => κ (t⁻¹ • y)) volume z,
    Measure.integral_comp_inv_smul_of_nonneg volume κ ht.le, finrank_euclideanSpace_fin,
    smul_eq_mul]

/-- `‖K_t(z - ·)‖₁ = t^{-(d+1)/2} t^d ∫ κ`. -/
theorem integral_abs_scaleKernel (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (z : Rd d) :
    ∫ y, |scaleKernel κ t (z - y)| = kpre d t * t ^ d * ∫ y, κ y := by
  have e : ∀ y, |scaleKernel κ t (z - y)| = kpre d t * κ (t⁻¹ • (z - y)) := fun y => by
    rw [scaleKernel_eq_kpre, abs_of_nonneg (mul_nonneg (kpre_pos ht).le (hκ.nonneg _))]
  simp_rw [e]
  rw [integral_const_mul, integral_kappa_comp κ ht, mul_assoc]

/-- `L¹` modulus of continuity of `κ`: `∫ |κ(u + h) - κ(u)| du ≤ 2 K |B(0, ρ)| ‖h‖`. -/
theorem integral_abs_kappa_add_sub_le (hκ : IsLFPPKernel κ) {K : NNReal} (hK : LipschitzWith K κ)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (h : Rd d) :
    ∫ u, |κ (u + h) - κ u| ≤ 2 * K * volume.real (ball (0 : Rd d) ρ) * ‖h‖ := by
  set B : Set (Rd d) := ball 0 ρ with hB
  have hBm : MeasurableSet B := measurableSet_ball
  have hI : Integrable (B.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const measure_ball_lt_top.ne)
  have hIh : Integrable fun u => B.indicator (fun _ => (1 : ℝ)) (u + h) := hI.comp_add_right h
  have hint : ∫ u, (B.indicator (fun _ => (1 : ℝ)) u + B.indicator (fun _ => 1) (u + h)) =
      2 * volume.real B := by
    rw [integral_add hI hIh, integral_add_right_eq_self (B.indicator fun _ => (1 : ℝ)) h,
      integral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one]
    ring
  have hpt : ∀ u, |κ (u + h) - κ u| ≤
      ((K : ℝ) * ‖h‖) * (B.indicator (fun _ => (1 : ℝ)) u + B.indicator (fun _ => 1) (u + h)) := by
    intro u
    have hlip : |κ (u + h) - κ u| ≤ (K : ℝ) * ‖h‖ := by
      have := hK.dist_le_mul (u + h) u
      rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
    have hn1 : 0 ≤ B.indicator (fun _ => (1 : ℝ)) u := indicator_nonneg (fun _ _ => zero_le_one) _
    have hn2 : 0 ≤ B.indicator (fun _ => (1 : ℝ)) (u + h) :=
      indicator_nonneg (fun _ _ => zero_le_one) _
    by_cases h1 : u ∈ B
    · have : 1 ≤ B.indicator (fun _ => (1 : ℝ)) u + B.indicator (fun _ => 1) (u + h) := by
        rw [indicator_of_mem h1]; linarith
      calc |κ (u + h) - κ u| ≤ (K : ℝ) * ‖h‖ := hlip
        _ ≤ _ := le_mul_of_one_le_right (by positivity) this
    · by_cases h2 : u + h ∈ B
      · have : 1 ≤ B.indicator (fun _ => (1 : ℝ)) u + B.indicator (fun _ => 1) (u + h) := by
          rw [indicator_of_mem h2]; linarith
        calc |κ (u + h) - κ u| ≤ (K : ℝ) * ‖h‖ := hlip
          _ ≤ _ := le_mul_of_one_le_right (by positivity) this
      · rw [hB, mem_ball, dist_zero_right, not_lt] at h1 h2
        rw [hρ u h1, hρ (u + h) h2, sub_self, abs_zero]
        positivity
  have hm : Integrable fun u => |κ (u + h) - κ u| :=
    ((hκ.integrable.comp_add_right h).sub hκ.integrable).abs
  calc ∫ u, |κ (u + h) - κ u| ≤ ∫ u, ((K : ℝ) * ‖h‖) *
        (B.indicator (fun _ => (1 : ℝ)) u + B.indicator (fun _ => 1) (u + h)) :=
        integral_mono hm ((hI.add hIh).const_mul _) hpt
    _ = 2 * K * volume.real B * ‖h‖ := by
        rw [integral_const_mul, hint]
        ring

/-- `‖K_t(z - ·) - K_t(z' - ·)‖₁ ≤ t^{-(d+1)/2} t^d · 2K|B(0,ρ)| · t⁻¹ ‖z - z'‖`. -/
theorem integral_abs_scaleKernel_sub_le_lip (hκ : IsLFPPKernel κ) {K : NNReal}
    (hK : LipschitzWith K κ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {t : ℝ} (ht : 0 < t)
    (z z' : Rd d) :
    ∫ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)| ≤
      kpre d t * t ^ d * (2 * K * volume.real (ball (0 : Rd d) ρ)) * (t⁻¹ * ‖z - z'‖) := by
  set h : Rd d := t⁻¹ • (z - z') with hh
  have e : ∀ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)| =
      kpre d t * |κ (t⁻¹ • (z - y)) - κ (t⁻¹ • (z' - y))| := fun y => by
    rw [scaleKernel_eq_kpre, scaleKernel_eq_kpre, ← mul_sub, abs_mul, abs_of_pos (kpre_pos ht)]
  simp_rw [e]
  rw [integral_const_mul]
  have hsub : ∫ y, |κ (t⁻¹ • (z - y)) - κ (t⁻¹ • (z' - y))| =
      ∫ y, |κ (t⁻¹ • y + h) - κ (t⁻¹ • y)| := by
    rw [← integral_sub_left_eq_self (fun y => |κ (t⁻¹ • y + h) - κ (t⁻¹ • y)|) volume z']
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hh]
    congr 3
    rw [← smul_add]
    congr 1
    abel
  rw [hsub, Measure.integral_comp_inv_smul_of_nonneg volume (fun u => |κ (u + h) - κ u|) ht.le,
    finrank_euclideanSpace_fin, smul_eq_mul]
  have hb := integral_abs_kappa_add_sub_le hκ hK hρ h
  rw [hh, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)] at hb
  have hk := (kpre_pos (d := d) ht).le
  have htd : 0 ≤ t ^ d := pow_nonneg ht.le d
  calc kpre d t * (t ^ d * ∫ u, |κ (u + h) - κ u|)
      ≤ kpre d t * (t ^ d * (2 * K * volume.real (ball (0 : Rd d) ρ) * (t⁻¹ * ‖z - z'‖))) := by
        gcongr
    _ = _ := by ring

theorem FieldAux.min_mul_le_max_mul_min {α β x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : min (α * x) (β * y) ≤ max α β * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right (le_max_left α β) hx)
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right α β) hy)

/-- **`L¹` bound for kernel differences** (HA2 D5 (iii)): there is `C₂` with
`‖K_t(z - ·) - K_t(z' - ·)‖₁ ≤ C₂ t^{-(d+1)/2} t^d min(1, ‖z - z'‖/t)` for all `t > 0`. -/
theorem exists_integral_abs_scaleKernel_sub_le (hκ : IsLFPPKernel κ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ t : ℝ, 0 < t → ∀ z z' : Rd d,
      ∫ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)| ≤
        C₂ * kpre d t * t ^ d * min 1 (‖z - z'‖ / t) := by
  obtain ⟨K, hK⟩ := hκ.exists_lipschitzWith
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  set N₀ := ∫ y, κ y with hN₀
  set N₁ := 2 * K * volume.real (ball (0 : Rd d) ρ) with hN₁
  have hN₀0 : 0 ≤ N₀ := integral_nonneg hκ.nonneg
  have hN₁0 : 0 ≤ N₁ := by positivity
  refine ⟨max (2 * N₀) N₁, le_max_of_le_right hN₁0, fun t ht z z' => ?_⟩
  have hk := kpre_pos (d := d) ht
  have htd : 0 < t ^ d := pow_pos ht d
  have h1 : ∫ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)| ≤
      kpre d t * t ^ d * (2 * N₀ * 1) := by
    have hi := integrable_scaleKernel_comp_sub hκ ht z
    have hi' := integrable_scaleKernel_comp_sub hκ ht z'
    calc ∫ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)|
        ≤ ∫ y, (|scaleKernel κ t (z - y)| + |scaleKernel κ t (z' - y)|) :=
          integral_mono (hi.sub hi').abs (hi.abs.add hi'.abs) fun y => abs_sub _ _
      _ = kpre d t * t ^ d * (2 * N₀ * 1) := by
          rw [integral_add hi.abs hi'.abs, integral_abs_scaleKernel hκ ht,
            integral_abs_scaleKernel hκ ht]
          ring
  have h2 : ∫ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)| ≤
      kpre d t * t ^ d * (N₁ * (‖z - z'‖ / t)) := by
    have := integral_abs_scaleKernel_sub_le_lip hκ hK hρ ht z z'
    rw [div_eq_inv_mul ‖z - z'‖ t]
    calc _ ≤ _ := this
      _ = kpre d t * t ^ d * (N₁ * (t⁻¹ * ‖z - z'‖)) := by rw [hN₁]; ring
  have h3 := le_min h1 h2
  have h4 := FieldAux.min_mul_le_max_mul_min (α := 2 * N₀) (β := N₁) zero_le_one
    (div_nonneg (norm_nonneg (z - z')) ht.le)
  calc ∫ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)|
      ≤ min (kpre d t * t ^ d * (2 * N₀ * 1)) (kpre d t * t ^ d * (N₁ * (‖z - z'‖ / t))) := h3
    _ = kpre d t * t ^ d * min (2 * N₀ * 1) (N₁ * (‖z - z'‖ / t)) :=
        (mul_min_of_nonneg _ _ (by positivity)).symm
    _ ≤ kpre d t * t ^ d * (max (2 * N₀) N₁ * min 1 (‖z - z'‖ / t)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = max (2 * N₀) N₁ * kpre d t * t ^ d * min 1 (‖z - z'‖ / t) := by ring

end Kernel

/-! ### Coupling bounds at a fixed scale (HA2 D5 (i)–(iii)) -/

section Coupling

variable {κ : Rd d → ℝ}

theorem measurable_scaleConv (hκ : IsLFPPKernel κ) (t : ℝ) (μ : Measure (Rd d)) [SFinite μ] :
    Measurable (scaleConv κ t μ) :=
  (measurable_scaleConv_uncurry hκ μ).comp (measurable_const.prodMk measurable_id)

theorem measurable_scaleKernel_sub (hκ : IsLFPPKernel κ) (t : ℝ) (y : Rd d) :
    Measurable fun z => scaleKernel κ t (z - y) :=
  ((continuous_scaleKernel hκ t).comp (continuous_id.sub continuous_const)).measurable

/-- **HA2 D5 (i), coupling representation**:
`(μ * K_t)(y) - (ν * K_t)(y) = ∫ (K_t(z - y) - K_t(z' - y)) dπ(z, z')`. -/
theorem scaleConv_sub_eq_integral (hκ : IsLFPPKernel κ) (t : ℝ) {μ ν : Measure (Rd d)}
    {cpl : Measure (Rd d × Rd d)} [IsFiniteMeasure cpl] (h1 : cpl.map Prod.fst = μ)
    (h2 : cpl.map Prod.snd = ν) (y : Rd d) :
    scaleConv κ t μ y - scaleConv κ t ν y =
      ∫ q, (scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)) ∂cpl := by
  have hm := measurable_scaleKernel_sub hκ t y
  rw [scaleConv, scaleConv, FieldAux.integral_eq_integral_fst h1 hm, FieldAux.integral_eq_integral_snd h2 hm,
    integral_sub]
  · have h := integrable_scaleKernel_sub hκ t y (cpl.map Prod.fst)
    exact (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).1 h
  · have h := integrable_scaleKernel_sub hκ t y (cpl.map Prod.snd)
    exact (integrable_map_measure hm.aestronglyMeasurable measurable_snd.aemeasurable).1 h

/-- **HA2 D5 (ii), Bound A**: `|(μ * K_t)(y)| ≤ t^{-(d+1)/2} A₀ B ρ t / R` under (3.4). -/
theorem abs_scaleConv_le_growth {A₀ : ℝ} (hA : ∀ x, |κ x| ≤ A₀) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    {μ : Measure (Rd d)} [IsFiniteMeasure μ] {B R : ℝ} (hB : 0 ≤ B) (hμ : GrowthBound μ B R)
    (y : Rd d) : |scaleConv κ t μ y| ≤ kpre d t * A₀ * (B * (ρ * t / R)) := by
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA 0)
  have hk := (kpre_pos (d := d) ht).le
  have hpt : ∀ z, |scaleKernel κ t (z - y)| ≤
      (closedBall y (ρ * t)).indicator (fun _ => kpre d t * A₀) z := by
    intro z
    by_cases hz : z ∈ closedBall y (ρ * t)
    · rw [indicator_of_mem hz]
      exact abs_scaleKernel_le hA ht _
    · rw [indicator_of_notMem hz, scaleKernel_eq_zero_of_le hρ ht, abs_zero]
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      exact hz.le
  have hi : Integrable ((closedBall y (ρ * t)).indicator fun _ => kpre d t * A₀) μ :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrable_const _).integrableOn
  calc |scaleConv κ t μ y| ≤ ∫ z, |scaleKernel κ t (z - y)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z, (closedBall y (ρ * t)).indicator (fun _ => kpre d t * A₀) z ∂μ :=
        integral_mono (integrable_scaleKernel_sub hκ t y μ).abs hi hpt
    _ = kpre d t * A₀ * μ.real (closedBall y (ρ * t)) := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
    _ ≤ kpre d t * A₀ * (B * (ρ * t / R)) :=
        mul_le_mul_of_nonneg_left (hμ.le_div hB y (mul_pos hρ0 ht)) (mul_nonneg hk hA0)

/-- **HA2 D5 (ii), Bound B** (displacement `u ≤ t`, growth of `μ` only):
`|(μ - ν) * K_t(y)| ≤ t^{-(d+1)/2} K t⁻¹ u B (ρ + 1) t / R`. -/
theorem abs_scaleConv_sub_le_lip (hκ : IsLFPPKernel κ) {K : NNReal} (hK : LipschitzWith K κ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {t : ℝ} (ht : 0 < t)
    {μ ν : Measure (Rd d)} [IsProbabilityMeasure μ] {cpl : Measure (Rd d × Rd d)}
    (h1 : cpl.map Prod.fst = μ) (h2 : cpl.map Prod.snd = ν) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : ∀ᵐ q ∂cpl, ‖q.1 - q.2‖ ≤ u) (hut : u ≤ t) {B R : ℝ} (hB : 0 ≤ B)
    (hμ : GrowthBound μ B R) (y : Rd d) :
    |scaleConv κ t μ y - scaleConv κ t ν y| ≤
      kpre d t * K * (t⁻¹ * u) * (B * ((ρ + 1) * t / R)) := by
  have : IsProbabilityMeasure cpl := FieldAux.isProbabilityMeasure_of_map_fst h1
  have hk := (kpre_pos (d := d) ht).le
  have hc0 : 0 ≤ kpre d t * K * (t⁻¹ * u) :=
    mul_nonneg (mul_nonneg hk K.2) (mul_nonneg (inv_nonneg.2 ht.le) hu0)
  set A : Set (Rd d × Rd d) := Prod.fst ⁻¹' closedBall y ((ρ + 1) * t) with hAdef
  have hAm : MeasurableSet A := measurable_fst measurableSet_closedBall
  have hpt : ∀ᵐ q ∂cpl, |scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)| ≤
      A.indicator (fun _ => kpre d t * K * (t⁻¹ * u)) q := by
    filter_upwards [hu] with q hq
    by_cases hq1 : q ∈ A
    · rw [indicator_of_mem hq1]
      calc |scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)|
          ≤ kpre d t * K * (t⁻¹ * ‖(q.1 - y) - (q.2 - y)‖) := abs_scaleKernel_sub_le hK ht _ _
        _ ≤ kpre d t * K * (t⁻¹ * u) := by
            rw [sub_sub_sub_cancel_right]
            gcongr
    · rw [indicator_of_notMem hq1]
      have hq1' : (ρ + 1) * t < ‖q.1 - y‖ := by
        simp only [hAdef, mem_preimage, mem_closedBall, dist_eq_norm, not_le] at hq1
        exact hq1
      have e1 : scaleKernel κ t (q.1 - y) = 0 := scaleKernel_eq_zero_of_le hρ ht (by nlinarith)
      have e2 : scaleKernel κ t (q.2 - y) = 0 := by
        refine scaleKernel_eq_zero_of_le hρ ht ?_
        have htri : ‖q.1 - y‖ ≤ ‖q.1 - q.2‖ + ‖q.2 - y‖ := by
          have := norm_add_le (q.1 - q.2) (q.2 - y)
          rwa [sub_add_sub_cancel] at this
        nlinarith
      rw [e1, e2, sub_self, abs_zero]
  have hi : Integrable (A.indicator fun _ => kpre d t * K * (t⁻¹ * u)) cpl :=
    (integrable_indicator_iff hAm).2 (integrable_const _).integrableOn
  have hint : Integrable (fun q : Rd d × Rd d =>
      scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)) cpl := by
    have hm := measurable_scaleKernel_sub hκ t y
    refine Integrable.sub ?_ ?_
    · exact (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).1
        (integrable_scaleKernel_sub hκ t y (cpl.map Prod.fst))
    · exact (integrable_map_measure hm.aestronglyMeasurable measurable_snd.aemeasurable).1
        (integrable_scaleKernel_sub hκ t y (cpl.map Prod.snd))
  rw [scaleConv_sub_eq_integral hκ t h1 h2 y]
  calc |∫ q, (scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)) ∂cpl|
      ≤ ∫ q, |scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)| ∂cpl :=
        abs_integral_le_integral_abs
    _ ≤ ∫ q, A.indicator (fun _ => kpre d t * K * (t⁻¹ * u)) q ∂cpl :=
        integral_mono_ae hint.abs hi hpt
    _ = kpre d t * K * (t⁻¹ * u) * μ.real (closedBall y ((ρ + 1) * t)) := by
        rw [integral_indicator_const _ hAm, smul_eq_mul, mul_comm, hAdef,
          FieldAux.measureReal_fst_preimage h1 measurableSet_closedBall]
    _ ≤ kpre d t * K * (t⁻¹ * u) * (B * ((ρ + 1) * t / R)) :=
        mul_le_mul_of_nonneg_left (hμ.le_div hB y (by positivity)) hc0

/-- **HA2 D5 (ii), the sup bound (3.6)**:
`|(μ - ν) * K_t(y)| ≤ C₁ t^{-(d+1)/2} t min(1, u/t) / R` with `C₁ = max(2A₀Bρ, KB(ρ+1))`. -/
theorem abs_scaleConv_sub_le_sup (hκ : IsLFPPKernel κ) {A₀ : ℝ} (hA : ∀ x, |κ x| ≤ A₀)
    {K : NNReal} (hK : LipschitzWith K κ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0)
    {t : ℝ} (ht : 0 < t) {μ ν : Measure (Rd d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : ℝ} (hu0 : 0 ≤ u) (hcpl : CoupledWithin μ ν u) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hμ : GrowthBound μ B R) (hν : GrowthBound ν B R) (y : Rd d) :
    |scaleConv κ t μ y - scaleConv κ t ν y| ≤
      max (2 * A₀ * B * ρ) (K * B * (ρ + 1)) * kpre d t * t * min 1 (u / t) / R := by
  obtain ⟨cpl, h1, h2, hu⟩ := hcpl
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA 0)
  have hk := kpre_pos (d := d) ht
  rcases le_or_gt u t with hut | hut
  · have hmin : min 1 (u / t) = u / t := min_eq_right ((div_le_one ht).2 hut)
    rw [hmin]
    calc |scaleConv κ t μ y - scaleConv κ t ν y|
        ≤ kpre d t * K * (t⁻¹ * u) * (B * ((ρ + 1) * t / R)) :=
          abs_scaleConv_sub_le_lip hκ hK hρ0 hρ ht h1 h2 hu0 hu hut hB hμ y
      _ = K * B * (ρ + 1) * kpre d t * t * (u / t) / R := by field_simp
      _ ≤ max (2 * A₀ * B * ρ) (K * B * (ρ + 1)) * kpre d t * t * (u / t) / R := by
          gcongr
          exact le_max_right _ _
  · have hmin : min 1 (u / t) = 1 := min_eq_left ((one_le_div ht).2 hut.le)
    rw [hmin]
    have hμ' := abs_scaleConv_le_growth hA hρ0 hρ hκ ht hB hμ y
    have hν' := abs_scaleConv_le_growth hA hρ0 hρ hκ ht hB hν y
    calc |scaleConv κ t μ y - scaleConv κ t ν y|
        ≤ |scaleConv κ t μ y| + |scaleConv κ t ν y| := abs_sub _ _
      _ ≤ kpre d t * A₀ * (B * (ρ * t / R)) + kpre d t * A₀ * (B * (ρ * t / R)) :=
          add_le_add hμ' hν'
      _ = 2 * A₀ * B * ρ * kpre d t * t * 1 / R := by field_simp; ring
      _ ≤ max (2 * A₀ * B * ρ) (K * B * (ρ + 1)) * kpre d t * t * 1 / R := by
          gcongr
          exact le_max_left _ _

/-- **HA2 D5 (iii), the `L¹` bound (3.7)**: if `μ, ν` are coupled within `v`, then
`y ↦ (μ - ν) * K_t(y)` is integrable and `∫ |(μ - ν) * K_t| ≤ C₂ t^{-(d+1)/2} t^d min(1, v/t)`.
No growth bound is used. -/
theorem integral_abs_scaleConv_sub_le (hκ : IsLFPPKernel κ) {C₂ : ℝ} (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ t : ℝ, 0 < t → ∀ z z' : Rd d,
      ∫ y, |scaleKernel κ t (z - y) - scaleKernel κ t (z' - y)| ≤
        C₂ * kpre d t * t ^ d * min 1 (‖z - z'‖ / t))
    {t : ℝ} (ht : 0 < t) {μ ν : Measure (Rd d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {v : ℝ} (hcpl : CoupledWithin μ ν v) :
    Integrable (fun y => scaleConv κ t μ y - scaleConv κ t ν y) ∧
      ∫ y, |scaleConv κ t μ y - scaleConv κ t ν y| ≤ C₂ * kpre d t * t ^ d * min 1 (v / t) := by
  obtain ⟨cpl, h1, h2, hv⟩ := hcpl
  have : IsProbabilityMeasure cpl := FieldAux.isProbabilityMeasure_of_map_fst h1
  have hk := (kpre_pos (d := d) ht).le
  have htd : 0 ≤ t ^ d := pow_nonneg ht.le d
  set D : Rd d → Rd d × Rd d → ℝ := fun y q =>
    |scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)| with hD
  have hDm : Measurable (Function.uncurry D) := by
    have h := (continuous_scaleKernel hκ t).measurable
    exact continuous_abs.measurable.comp ((h.comp (measurable_snd.fst.sub measurable_fst)).sub
      (h.comp (measurable_snd.snd.sub measurable_fst)))
  have hDi : Integrable (Function.uncurry D) (volume.prod cpl) := by
    rw [integrable_prod_iff' hDm.aestronglyMeasurable]
    constructor
    · exact Eventually.of_forall fun q => ((integrable_scaleKernel_comp_sub hκ ht q.1).sub
        (integrable_scaleKernel_comp_sub hκ ht q.2)).abs
    · refine Integrable.of_bound (StronglyMeasurable.integral_prod_left (μ := volume)
        (f := fun y q => ‖D y q‖) hDm.norm.stronglyMeasurable).aestronglyMeasurable
        (C₂ * kpre d t * t ^ d) (Eventually.of_forall fun q => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      simp only [hD, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_abs]
      calc ∫ y, |scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)|
          ≤ C₂ * kpre d t * t ^ d * min 1 (‖q.1 - q.2‖ / t) := hC₂ t ht q.1 q.2
        _ ≤ C₂ * kpre d t * t ^ d * 1 := by gcongr; exact min_le_left _ _
        _ = C₂ * kpre d t * t ^ d := mul_one _
  have hΦ : Integrable (fun y => ∫ q, D y q ∂cpl) := hDi.integral_prod_left
  have hle : ∀ y, |scaleConv κ t μ y - scaleConv κ t ν y| ≤ ∫ q, D y q ∂cpl := fun y => by
    rw [scaleConv_sub_eq_integral hκ t h1 h2 y]
    exact abs_integral_le_integral_abs
  have hFm : Measurable fun y => scaleConv κ t μ y - scaleConv κ t ν y :=
    (measurable_scaleConv hκ t μ).sub (measurable_scaleConv hκ t ν)
  have hFi : Integrable (fun y => scaleConv κ t μ y - scaleConv κ t ν y) :=
    hΦ.mono' hFm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hle y)
  refine ⟨hFi, ?_⟩
  calc ∫ y, |scaleConv κ t μ y - scaleConv κ t ν y|
      ≤ ∫ y, ∫ q, D y q ∂cpl := integral_mono hFi.abs hΦ hle
    _ = ∫ q, (∫ y, D y q) ∂cpl := integral_integral_swap hDi
    _ ≤ ∫ q, C₂ * kpre d t * t ^ d * min 1 (v / t) ∂cpl := by
        refine integral_mono_ae hDi.integral_prod_right (integrable_const _) ?_
        filter_upwards [hv] with q hq
        calc ∫ y, D y q = ∫ y, |scaleKernel κ t (q.1 - y) - scaleKernel κ t (q.2 - y)| := rfl
          _ ≤ C₂ * kpre d t * t ^ d * min 1 (‖q.1 - q.2‖ / t) := hC₂ t ht q.1 q.2
          _ ≤ C₂ * kpre d t * t ^ d * min 1 (v / t) := by gcongr
    _ = C₂ * kpre d t * t ^ d * min 1 (v / t) := by
        rw [integral_const, probReal_univ, one_smul]

/-- **HA2 D5 (iv)–(v) at one scale**: `|scalePair κ t (μ - ν) (μ' - ν')| ≤ M L₁` whenever
`|(μ - ν) * K_t| ≤ M` and `‖(μ' - ν') * K_t‖₁ ≤ L₁`. -/
theorem abs_scalePair_le_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] {M L₁ : ℝ} (hM : ∀ y, |scaleConv κ t μ y - scaleConv κ t ν y| ≤ M)
    (hG : Integrable fun y => scaleConv κ t μ' y - scaleConv κ t ν' y)
    (hL : ∫ y, |scaleConv κ t μ' y - scaleConv κ t ν' y| ≤ L₁) (hM0 : 0 ≤ M) :
    |scalePair κ t μ ν μ' ν'| ≤ M * L₁ := by
  rw [← integral_scaleConv_sub_mul hκ ht]
  calc |∫ y, (scaleConv κ t μ y - scaleConv κ t ν y) * (scaleConv κ t μ' y - scaleConv κ t ν' y)|
      ≤ ∫ y, |(scaleConv κ t μ y - scaleConv κ t ν y) *
          (scaleConv κ t μ' y - scaleConv κ t ν' y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, M * |scaleConv κ t μ' y - scaleConv κ t ν' y| := by
        refine integral_mono (integrable_scaleConv_sub_mul hκ ht μ ν μ' ν').abs
          (hG.abs.const_mul M) fun y => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)
    _ = M * ∫ y, |scaleConv κ t μ' y - scaleConv κ t ν' y| := integral_const_mul _ _
    _ ≤ M * L₁ := mul_le_mul_of_nonneg_left hL hM0

end Coupling

/-! ### The scale integral (HA2 D5 (vi)) -/

/-- `min(1, a) min(1, b) ≤ min(1, √(ab))²` for `a, b ≥ 0`. -/
theorem FieldAux.min_one_mul_min_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 a * min 1 b ≤ min 1 (Real.sqrt (a * b)) ^ 2 := by
  have h1 : min 1 a * min 1 b ≤ min 1 (a * b) := by
    refine le_min ?_ ?_
    · calc min 1 a * min 1 b ≤ 1 * 1 :=
            mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min zero_le_one hb) zero_le_one
        _ = 1 := one_mul 1
    · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min zero_le_one hb) ha
  have h2 : min 1 (Real.sqrt (a * b)) ^ 2 = min 1 (a * b) := by
    rcases le_total (Real.sqrt (a * b)) 1 with h | h
    · rw [min_eq_right h, Real.sq_sqrt (mul_nonneg ha hb)]
      have : a * b ≤ 1 := by
        have := mul_self_le_mul_self (Real.sqrt_nonneg _) h
        rwa [Real.mul_self_sqrt (mul_nonneg ha hb), one_mul] at this
      rw [min_eq_right this]
    · rw [min_eq_left h, one_pow]
      have : 1 ≤ a * b := by
        have := mul_self_le_mul_self zero_le_one h
        rwa [Real.mul_self_sqrt (mul_nonneg ha hb), one_mul] at this
      rw [min_eq_left this]
  rw [h2]
  exact h1

theorem FieldAux.measurable_min_sq (w : ℝ) : Measurable fun t : ℝ => min 1 (w / t) ^ 2 :=
  (measurable_const.min (measurable_const.div measurable_id)).pow_const 2

/-- `t ↦ min(1, w/t)²` is integrable on `(0, ∞)` with integral `2w`. -/
theorem FieldAux.integrableOn_min_sq {w : ℝ} (hw : 0 ≤ w) :
    IntegrableOn (fun t : ℝ => min 1 (w / t) ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, min 1 (w / t) ^ 2 = 2 * w := by
  rcases hw.eq_or_lt with rfl | hw
  · have e : EqOn (fun t : ℝ => min 1 (0 / t) ^ 2) (fun _ => (0 : ℝ)) (Ioi 0) := fun t _ => by
      simp only [zero_div, zero_le_one, min_eq_right, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
    refine ⟨integrableOn_zero.congr_fun e.symm measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_zero, mul_zero]
  · have e1 : EqOn (fun t : ℝ => min 1 (w / t) ^ 2) (fun _ => (1 : ℝ)) (Ioc 0 w) := by
      intro t ht
      have : 1 ≤ w / t := (one_le_div ht.1).2 ht.2
      simp only [min_eq_left this, one_pow]
    have e2 : EqOn (fun t : ℝ => min 1 (w / t) ^ 2) (fun t => w ^ 2 * t ^ (-2 : ℝ)) (Ioi w) := by
      intro t ht
      have ht0 : 0 < t := lt_trans hw ht
      have : w / t ≤ 1 := (div_le_one ht0).2 (le_of_lt ht)
      simp only [min_eq_right this]
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast,
        div_pow, div_eq_mul_inv]
    have i1 : IntegrableOn (fun t : ℝ => min 1 (w / t) ^ 2) (Ioc 0 w) :=
      (integrableOn_const measure_Ioc_lt_top.ne).congr_fun e1.symm measurableSet_Ioc
    have i2' : IntegrableOn (fun t : ℝ => w ^ 2 * t ^ (-2 : ℝ)) (Ioi w) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hw).const_mul (w ^ 2)
    have i2 : IntegrableOn (fun t : ℝ => min 1 (w / t) ^ 2) (Ioi w) :=
      i2'.congr_fun e2.symm measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi hw.le]
    refine ⟨i1.union i2, ?_⟩
    rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
      setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
      setIntegral_const, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hw,
      measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
      mul_one, show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
    ring

/-! ### Lemma 3.1 -/

section Lemma31

variable {κ : Rd d → ℝ}

/-- **HA2 D5 (iv)–(v), one scale**: there is `C₀ = C₀(d, κ, B)` with
`|scalePair κ t (μ_R - ν_R) (μ' - ν')| ≤ (C₀ / R) min(1, u/t) min(1, v/t)` for all `t > 0`, if
`μ_R, ν_R` satisfy (3.4) at scale `R` and are coupled within `u`, and `μ', ν'` are coupled within
`v` (no growth bound on `μ', ν'`). -/
theorem exists_abs_scalePair_le (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ t : ℝ, 0 < t →
      ∀ (μ ν μ' ν' : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
        [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] (R u v : ℝ), 0 < R → 0 ≤ u →
        GrowthBound μ B R → GrowthBound ν B R → CoupledWithin μ ν u → CoupledWithin μ' ν' v →
        |scalePair κ t μ ν μ' ν'| ≤ C₀ / R * (min 1 (u / t) * min 1 (v / t)) := by
  obtain ⟨A₀, hA⟩ := hκ.exists_bound
  obtain ⟨K, hK⟩ := hκ.exists_lipschitzWith
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_integral_abs_scaleKernel_sub_le hκ
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA 0)
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set C₁ := max (2 * A₀ * B' * ρ) (K * B' * (ρ + 1)) with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_of_le_left (by positivity)
  refine ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, fun t ht μ ν μ' ν' _ _ _ _ R u v hR hu gμ gν cR cr => ?_⟩
  have hk := kpre_pos (d := d) ht
  have hsup := abs_scaleConv_sub_le_sup hκ hA hK hρ0 hρ ht hu cR hB'0 hR (gμ.max_zero hR)
    (gν.max_zero hR)
  obtain ⟨hGi, hGl⟩ := integral_abs_scaleConv_sub_le hκ hC₂0 hC₂ ht cr
  have hM0 : 0 ≤ C₁ * kpre d t * t * min 1 (u / t) / R := by
    have : 0 ≤ min 1 (u / t) := le_min zero_le_one (div_nonneg hu ht.le)
    positivity
  calc |scalePair κ t μ ν μ' ν'|
      ≤ (C₁ * kpre d t * t * min 1 (u / t) / R) * (C₂ * kpre d t * t ^ d * min 1 (v / t)) :=
        abs_scalePair_le_mul hκ ht hsup hGi hGl hM0
    _ = C₁ * C₂ / R * (min 1 (u / t) * min 1 (v / t)) * (kpre d t * kpre d t * t ^ d * t) := by
        ring
    _ = C₁ * C₂ / R * (min 1 (u / t) * min 1 (v / t)) := by rw [kpre_mul_kpre_mul ht, mul_one]

/-- **Lemma 3.1 (3.5)** (target T4; HA2 D5, HA2's `Lemma31` without the unused `r ≤ R`):
for every `B` there is `C = C(d, κ, B)` such that for every measurable scale set `S ⊆ (0, ∞)`,
all `R, r > 0`, `u, v ≥ 0`, and probability measures `μ_R, ν_R` (growth bound (3.4) at scale `R`,
coupled within `u`) and `μ_r, ν_r` (growth bound at scale `r`, coupled within `v`), both pairs are
pairable for `S` and `|Cov(⟨H_S, μ_R - ν_R⟩, ⟨H_S, μ_r - ν_r⟩)| ≤ C √(uv) / R`. -/
theorem transport_cov_bound (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Ioi 0 →
      ∀ (μR νR μr νr : Measure (Rd d)) [IsProbabilityMeasure μR] [IsProbabilityMeasure νR]
        [IsProbabilityMeasure μr] [IsProbabilityMeasure νr] (R r u v : ℝ),
        0 < R → 0 < r → 0 ≤ u → 0 ≤ v →
        GrowthBound μR B R → GrowthBound νR B R → GrowthBound μr B r → GrowthBound νr B r →
        CoupledWithin μR νR u → CoupledWithin μr νr v →
        IsPairable κ S μR νR ∧ IsPairable κ S μr νr ∧
          |scaleCov κ S μR νR μr νr| ≤ C * Real.sqrt (u * v) / R := by
  obtain ⟨C₀, hC₀0, hpt⟩ := exists_abs_scalePair_le hκ B
  refine ⟨2 * C₀, by positivity, fun S hS hS0 μR νR μr νr _ _ _ _ R r u v hR hr hu hv gR gR'
    gr gr' cR cr => ?_⟩
  -- pairability of a coupled pair with growth bounds, from the one-scale bound
  have hpair : ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (ρ w : ℝ), 0 < ρ → 0 ≤ w → GrowthBound μ B ρ → GrowthBound ν B ρ → CoupledWithin μ ν w →
      IsPairable κ S μ ν := by
    intro μ ν _ _ ρ w hρ hw g g' c
    have hgi : IntegrableOn (fun t => C₀ / ρ * min 1 (w / t) ^ 2) (Ioi 0) :=
      (FieldAux.integrableOn_min_sq hw).1.const_mul (C₀ / ρ)
    refine isPairable_of_le hκ hS hS0 μ ν (g := fun t => C₀ / ρ * min 1 (w / t) ^ 2)
      (hgi.mono_set hS0) fun t ht => ?_
    calc scalePair κ t μ ν μ ν ≤ |scalePair κ t μ ν μ ν| := le_abs_self _
      _ ≤ C₀ / ρ * (min 1 (w / t) * min 1 (w / t)) :=
          hpt t (hS0 ht) μ ν μ ν ρ w w hρ hw g g' c c
      _ = C₀ / ρ * min 1 (w / t) ^ 2 := by rw [sq]
  have hpR := hpair μR νR R u hR hu gR gR' cR
  have hpr := hpair μr νr r v hr hv gr gr' cr
  refine ⟨hpR, hpr, ?_⟩
  set w := Real.sqrt (u * v) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hgi : IntegrableOn (fun t => C₀ / R * min 1 (w / t) ^ 2) (Ioi 0) :=
    (FieldAux.integrableOn_min_sq hw0).1.const_mul (C₀ / R)
  have hle : ∀ t ∈ S, |scalePair κ t μR νR μr νr| ≤ C₀ / R * min 1 (w / t) ^ 2 := by
    intro t ht
    have ht0 : 0 < t := hS0 ht
    have hmin := FieldAux.min_one_mul_min_one_le (div_nonneg hu ht0.le) (div_nonneg hv ht0.le)
    have hsq : Real.sqrt (u / t * (v / t)) = w / t := by
      rw [div_mul_div_comm, Real.sqrt_div' _ (mul_nonneg ht0.le ht0.le),
        Real.sqrt_mul_self ht0.le]
    rw [hsq] at hmin
    calc |scalePair κ t μR νR μr νr| ≤ C₀ / R * (min 1 (u / t) * min 1 (v / t)) :=
          hpt t ht0 μR νR μr νr R u v hR hu gR gR' cR cr
      _ ≤ C₀ / R * min 1 (w / t) ^ 2 :=
          mul_le_mul_of_nonneg_left hmin (div_nonneg hC₀0 hR.le)
  rw [scaleCov_eq_integral hκ hS hS0 hpR hpr]
  calc |∫ t in S, scalePair κ t μR νR μr νr|
      ≤ ∫ t in S, |scalePair κ t μR νR μr νr| := abs_integral_le_integral_abs
    _ ≤ ∫ t in S, C₀ / R * min 1 (w / t) ^ 2 :=
        setIntegral_mono_on (integrableOn_scalePair hκ hS hS0 hpR hpr).abs (hgi.mono_set hS0) hS hle
    _ ≤ ∫ t in Ioi 0, C₀ / R * min 1 (w / t) ^ 2 := by
        refine setIntegral_mono_set hgi ?_ (Eventually.of_forall hS0)
        exact Eventually.of_forall fun t => mul_nonneg (div_nonneg hC₀0 hR.le) (sq_nonneg _)
    _ = 2 * C₀ * w / R := by
        rw [integral_const_mul, (FieldAux.integrableOn_min_sq hw0).2]
        ring

/-- **Lemma 3.1, variance form**: `Var⟨H_S, μ - ν⟩ ≤ C u / R` for probability measures with the
growth bound (3.4) at scale `R`, coupled within `u`. -/
theorem transport_var_bound (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Ioi 0 →
      ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (R u : ℝ),
        0 < R → 0 ≤ u → GrowthBound μ B R → GrowthBound ν B R → CoupledWithin μ ν u →
        IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ C * u / R := by
  obtain ⟨C, hC0, hC⟩ := transport_cov_bound hκ B
  refine ⟨C, hC0, fun S hS hS0 μ ν _ _ R u hR hu g g' c => ?_⟩
  obtain ⟨hp, -, hb⟩ := hC S hS hS0 μ ν μ ν R R u u hR hR hu hu g g' g g' c c
  refine ⟨hp, (le_abs_self _).trans ?_⟩
  rwa [Real.sqrt_mul_self hu] at hb

/-- **Lemma 3.1 for the all-scale log covariance** (interface (I4) of HA3 §7): the constant
depends only on `d` and `B` (`logCov` involves no kernel).  For log-pairable probability measures
with growth bounds and displacement couplings as in `transport_cov_bound`,
`|logCov μ_R ν_R μ_r ν_r| ≤ C √(uv) / R`. -/
theorem transport_logCov_bound (d : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (μR νR μr νr : Measure (Rd d)) [IsProbabilityMeasure μR] [IsProbabilityMeasure νR]
        [IsProbabilityMeasure μr] [IsProbabilityMeasure νr] (R r u v : ℝ),
        0 < R → 0 < r → 0 ≤ u → 0 ≤ v →
        GrowthBound μR B R → GrowthBound νR B R → GrowthBound μr B r → GrowthBound νr B r →
        CoupledWithin μR νR u → CoupledWithin μr νr v → LogPairable μR νR μr νr →
        |logCov μR νR μr νr| ≤ C * Real.sqrt (u * v) / R := by
  obtain ⟨κ, hκ⟩ := exists_isLFPPKernel d
  obtain ⟨C, hC0, hC⟩ := transport_cov_bound hκ B
  refine ⟨C, hC0, fun μR νR μr νr _ _ _ _ R r u v hR hr hu hv gR gR' gr gr' cR cr hlog => ?_⟩
  have hmass : μR.real univ = νR.real univ := by rw [probReal_univ, probReal_univ]
  have hmass' : μr.real univ = νr.real univ := by rw [probReal_univ, probReal_univ]
  rw [← (scaleCov_eq_logCov hκ hmass hmass' hlog).2.2]
  exact (hC (Ioi 0) measurableSet_Ioi subset_rfl μR νR μr νr R r u v hR hr hu hv gR gR' gr gr'
    cR cr).2.2

end Lemma31

end HigherDimLFPP
