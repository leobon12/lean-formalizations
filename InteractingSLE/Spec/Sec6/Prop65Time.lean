/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65Gauss
import InteractingSLE.WangWu.CouplingExp
import InteractingSLE.Spec.Sec2.JacobiExistsPath

/-!
# Proposition 6.5, part 2: time continuity of a conditionally Gaussian exploration mean

Packet PROVE-SEC6-B (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5-proof`, pp. 158–159).

**Abstract setting.** A filtration `𝓕` on `ℝ≥0`, a stopping time `ρ`, an observable `X`, and a variance
process `v`, continuous in time, nonincreasing up to `ρ` and adapted, such that at every stopping time
`T ≤ ρ` the observable is conditionally Gaussian: `ℒ(X | 𝓕_T) = N(E[X | 𝓕_T], v_T)` with `v_T ∈ [0, K]`
(`IsGaussianExploration`). In Proposition 6.5, `X` is the normalized pairing of the field with a small
radial bump around the point `z` and `v_t = const + log r_t(z)`.

**Theorem** (`IsGaussianExploration.exists_continuous_version`). The stopped conditional mean
`t ↦ E[X | 𝓕_{t∧ρ}]` has a modification `M` with continuous paths for **every** `ω`, stopped at `ρ`
for every `ω`; moreover `M_σ = E[X | 𝓕_σ]` almost surely at every stopping time `σ ≤ ρ`.

**Proof (a variant of the source's).** The source partitions time by the hitting times of the clock
levels `jδ`, bounds the fourth moment of the oscillation on each piece by Doob's inequality, and sums
over `δ = 2^{-n}` (Borel–Cantelli). We run the same estimate through a time change instead:
* the clock `A_t = v_0 − v_{t∧ρ}` is continuous, nondecreasing and adapted; `C_t = t + A_t` is a
  continuous strictly increasing bijection of `ℝ≥0` whose inverse `γ_u` consists of stopping times
  with `A_{γ_u} − A_{γ_s} ≤ u − s` (PROVE-WW-A's `WangWu.tcInv` machinery);
* `N_u = E[X | 𝓕_{γ_u ∧ ρ}]` satisfies the source's quartic identity
  `E[(N_u − N_s)⁴] = 6E[(N_u − N_s)² d] − 3E[d²] ≤ 6 (u − s)²`, `d = v_{γ_s∧ρ} − v_{γ_u∧ρ} ≤ u − s`
  (`Prop65.integral_pow_four_sub_le`), so the vendored Kolmogorov–Chentsov theorem gives a continuous
  modification `Ñ`;
* `M_t = Ñ(C_{t∧ρ})` is continuous. At a stopping time `σ ≤ ρ` it agrees with `E[X | 𝓕_σ]`: the dyadic
  upper approximations `u_n ↓ C_σ` give stopping times `γ_{u_n} ≥ σ` with
  `E[(N_{u_n} − E[X | 𝓕_σ])²] = E[v_σ − v_{γ_{u_n}∧ρ}] ≤ 2^{-n}`, so `N_{u_n} → E[X | 𝓕_σ]` almost surely,
  while `N_{u_n} = Ñ_{u_n} → Ñ(C_σ)` on the almost sure event where `Ñ` and `N` agree at all dyadics.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Finite stopping times -/

/-- The minimum of two finite stopping times. -/
theorem isStoppingTime_min_coe {S T : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => ((min (S ω) (T ω) : ℝ≥0) : WithTop ℝ≥0) := by
  have := hS.min hT
  simp only [← WithTop.coe_min] at this
  exact this

/-- A continuous adapted real process read at a finite stopping time `T` is `𝓕_T`-measurable. -/
theorem stronglyMeasurable_comp_stoppingTime {Y : ℝ≥0 → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun t => Y t ω) (hYm : ∀ t, Measurable[𝓕 t] (Y t)) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    StronglyMeasurable[hT.measurableSpace] fun ω => Y (T ω) ω := by
  have hprog := isStronglyProgressive_of_rightContinuous (fun t => (hYm t).stronglyMeasurable)
    (fun ω t => (hYc ω).continuousWithinAt)
  have := stronglyMeasurable_stoppedValue hprog (fun ω => (hYc ω).isRightContinuous) hT
  rwa [show stoppedValue Y (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => Y (T ω) ω from
    funext fun ω => WangWu.stoppedValue_coe Y T ω] at this

/-! ### The abstract setting -/

/-- **A conditionally Gaussian exploration observable** up to the stopping time `ρ`: the variance
process `v` is continuous, nonincreasing up to `ρ` and adapted, and at every stopping time `T ≤ ρ` the
observable `X` is conditionally Gaussian given `𝓕_T` with mean `E[X | 𝓕_T]` and variance `v_T ∈ [0, K]`. -/
structure IsGaussianExploration (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : Ω → ℝ)
    (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (K : ℝ) : Prop where
  stopping : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)
  cont : ∀ ω, Continuous fun t => v t ω
  anti : ∀ ω s t, s ≤ t → t ≤ ρ ω → v t ω ≤ v s ω
  adapted : ∀ t, Measurable[𝓕 t] (v t)
  integrable : MemLp X 2 P
  gauss : ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)),
    (∀ ω, T ω ≤ ρ ω) →
      IsCondGaussian hT.measurableSpace P X (P[X | hT.measurableSpace]) (fun ω => v (T ω) ω) K

/-- The clock `A_t = v_0 − v_{t∧ρ}`. -/
def clockA (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ := v 0 ω - v (min t (ρ ω)) ω

namespace IsGaussianExploration

variable {X : Ω → ℝ} {v : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} {K : ℝ}

theorem isStoppingTime_min_const (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => ((min t (ρ ω) : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_min_coe (S := fun _ => t) (isStoppingTime_const 𝓕 t) h.stopping

theorem v_nonneg (h : IsGaussianExploration P 𝓕 X v ρ K) {t : ℝ≥0} {ω : Ω} (ht : t ≤ ρ ω) :
    0 ≤ v t ω := by
  have := (h.gauss (fun ω => min t (ρ ω)) (h.isStoppingTime_min_const t)
    (fun _ => min_le_right _ _)).nonneg ω
  simpa [min_eq_left ht] using this

theorem v_le (h : IsGaussianExploration P 𝓕 X v ρ K) {t : ℝ≥0} {ω : Ω} (ht : t ≤ ρ ω) :
    v t ω ≤ K := by
  have := (h.gauss (fun ω => min t (ρ ω)) (h.isStoppingTime_min_const t)
    (fun _ => min_le_right _ _)).le_bound ω
  simpa [min_eq_left ht] using this

omit mΩ in
theorem clockA_zero (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (ω : Ω) : clockA v ρ 0 ω = 0 := by
  simp [clockA]

theorem monotone_clockA (h : IsGaussianExploration P 𝓕 X v ρ K) (ω : Ω) :
    Monotone fun t => clockA v ρ t ω := fun s t hst => by
  simp only [clockA]
  have := h.anti ω (min s (ρ ω)) (min t (ρ ω)) (min_le_min_right _ hst) (min_le_right _ _)
  linarith

theorem continuous_clockA (h : IsGaussianExploration P 𝓕 X v ρ K) (ω : Ω) :
    Continuous fun t => clockA v ρ t ω :=
  continuous_const.sub ((h.cont ω).comp (continuous_id.min continuous_const))

theorem clockA_nonneg (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) (ω : Ω) :
    0 ≤ clockA v ρ t ω := clockA_zero v ρ ω ▸ h.monotone_clockA ω (zero_le (a := t))

theorem clockA_le (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) (ω : Ω) :
    clockA v ρ t ω ≤ K := by
  have h1 := h.v_le (t := 0) (ω := ω) zero_le
  have h2 := h.v_nonneg (t := min t (ρ ω)) (ω := ω) (min_le_right _ _)
  simp only [clockA]; linarith

theorem stronglyAdapted_clockA (h : IsGaussianExploration P 𝓕 X v ρ K) :
    StronglyAdapted 𝓕 (clockA v ρ) := by
  intro t
  have h1 : StronglyMeasurable[𝓕 t] (v 0) :=
    ((h.adapted 0).mono (𝓕.mono (zero_le (a := t))) le_rfl).stronglyMeasurable
  have h2 := stronglyMeasurable_comp_stoppingTime h.cont h.adapted (h.isStoppingTime_min_const t)
  have hle : (h.isStoppingTime_min_const t).measurableSpace ≤ 𝓕 t := by
    have := IsStoppingTime.measurableSpace_mono (h.isStoppingTime_min_const t)
      (isStoppingTime_const 𝓕 t) fun ω => WithTop.coe_le_coe.2 (min_le_left t (ρ ω))
    rwa [IsStoppingTime.measurableSpace_const] at this
  exact h1.sub (h2.mono hle)

/-- The inverse clock `γ_u = C⁻¹(u)`, `C_t = t + A_t`. -/
def gam (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ≥0 := WangWu.tcInv (clockA v ρ) u ω

/-- The stopped inverse clock `γ_u ∧ ρ`. -/
def gamStop (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ≥0 := min (gam v ρ u ω) (ρ ω)

theorem isStoppingTime_gam (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => ((gam v ρ u ω : ℝ≥0) : WithTop ℝ≥0) :=
  WangWu.isStoppingTime_tcInv h.stronglyAdapted_clockA (clockA_zero v ρ) h.monotone_clockA
    h.continuous_clockA u

theorem isStoppingTime_gamStop (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => ((gamStop v ρ u ω : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_min_coe (h.isStoppingTime_gam u) h.stopping

theorem monotone_gam (h : IsGaussianExploration P 𝓕 X v ρ K) (ω : Ω) :
    Monotone fun u => gam v ρ u ω :=
  WangWu.monotone_tcInv (clockA_zero v ρ ω) (h.monotone_clockA ω) (h.continuous_clockA ω)

/-- The time-changed conditional mean `N_u = E[X | 𝓕_{γ_u ∧ ρ}]`. -/
def tcMean (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) : Ω → ℝ :=
  P[X | (h.isStoppingTime_gamStop u).measurableSpace]

theorem gauss_gamStop (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    IsCondGaussian (h.isStoppingTime_gamStop u).measurableSpace P X (h.tcMean u)
      (fun ω => v (gamStop v ρ u ω) ω) K :=
  h.gauss _ (h.isStoppingTime_gamStop u) fun _ => min_le_right _ _

/-- The variance drop along the inverse clock is at most the clock increment. -/
theorem v_gamStop_sub_le (h : IsGaussianExploration P 𝓕 X v ρ K) {s u : ℝ≥0} (hsu : s ≤ u)
    (ω : Ω) : v (gamStop v ρ s ω) ω - v (gamStop v ρ u ω) ω ≤ (u : ℝ) - s := by
  have := WangWu.A_tcInv_sub_le (clockA_zero v ρ ω) (h.monotone_clockA ω) (h.continuous_clockA ω)
    hsu
  simp only [clockA] at this
  simp only [gamStop, gam]
  linarith

/-- **The quartic increment bound**: `E[(N_u − N_s)⁴] ≤ 6 (u − s)²`. -/
theorem integral_tcMean_sub_pow_four_le [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K) {s u : ℝ≥0}
    (hsu : s ≤ u) : ∫ ω, (h.tcMean u ω - h.tcMean s ω) ^ 4 ∂P ≤ 6 * ((u : ℝ) - s) ^ 2 := by
  have h12 : (h.isStoppingTime_gamStop s).measurableSpace ≤
      (h.isStoppingTime_gamStop u).measurableSpace :=
    IsStoppingTime.measurableSpace_mono _ _ fun ω => WithTop.coe_le_coe.2
      (min_le_min_right _ (h.monotone_gam ω hsu))
  have hq := integral_pow_four_sub_le (h.gauss_gamStop s) (h.gauss_gamStop u) h12
    (δ := (u : ℝ) - s) (h.v_gamStop_sub_le hsu)
  have hD : ∫ ω, (v (gamStop v ρ s ω) ω - v (gamStop v ρ u ω) ω) ∂P ≤ (u : ℝ) - s := by
    calc ∫ ω, (v (gamStop v ρ s ω) ω - v (gamStop v ρ u ω) ω) ∂P ≤ ∫ _ω, ((u : ℝ) - s) ∂P := by
          refine integral_mono_of_nonneg ?_ (integrable_const _) (Eventually.of_forall
            (h.v_gamStop_sub_le hsu))
          exact Eventually.of_forall fun ω => sub_nonneg.2
            (h.anti ω _ _ (min_le_min_right _ (h.monotone_gam ω hsu)) (min_le_right _ _))
      _ = (u : ℝ) - s := by simp
  have hus : (0 : ℝ) ≤ (u : ℝ) - s := sub_nonneg.2 (by exact_mod_cast hsu)
  calc ∫ ω, (h.tcMean u ω - h.tcMean s ω) ^ 4 ∂P
      ≤ 6 * ((u : ℝ) - s) * ∫ ω, (v (gamStop v ρ s ω) ω - v (gamStop v ρ u ω) ω) ∂P := hq
    _ ≤ 6 * ((u : ℝ) - s) * ((u : ℝ) - s) := by gcongr
    _ = 6 * ((u : ℝ) - s) ^ 2 := by ring

theorem stronglyMeasurable_tcMean (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    StronglyMeasurable[(h.isStoppingTime_gamStop u).measurableSpace] (h.tcMean u) :=
  stronglyMeasurable_condExp

theorem measurable_tcMean (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    Measurable (h.tcMean u) :=
  (h.stronglyMeasurable_tcMean u).measurable.mono (h.isStoppingTime_gamStop u).measurableSpace_le
    le_rfl

theorem integrable_tcMean_sub_pow_four [IsProbabilityMeasure P]
    (h : IsGaussianExploration P 𝓕 X v ρ K) {s u : ℝ≥0} (_hsu : s ≤ u) :
    Integrable (fun ω => (h.tcMean u ω - h.tcMean s ω) ^ 4) P := by
  have := integrable_two_level (W := fun _ => (1 : ℝ)) (a := 4) (b := 0) (h.gauss_gamStop s)
    (h.gauss_gamStop u) measurable_const zero_le_one (fun _ => by simp) (by norm_num)
  exact this.congr (Eventually.of_forall fun ω => by simp)

lemma toNNReal_sub_le {x y : ℝ} (hxy : x ≤ y) :
    ((y.toNNReal : ℝ) - (x.toNNReal : ℝ)) ≤ y - x ∧ 0 ≤ (y.toNNReal : ℝ) - (x.toNNReal : ℝ) := by
  rw [Real.coe_toNNReal', Real.coe_toNNReal']
  constructor
  · rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_left (hx.trans hxy)]
    · rw [max_eq_right hx]
      rcases le_total 0 y with hy | hy
      · rw [max_eq_left hy]; linarith
      · rw [max_eq_right hy]; linarith
  · exact sub_nonneg.2 (max_le_max hxy le_rfl)

/-- The Kolmogorov condition for the time-changed mean, extended to `ℝ` by `x ↦ x⁺`. -/
theorem lintegral_edist_tcMean_le [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    (x y : ℝ) :
    ∫⁻ ω, edist (h.tcMean x.toNNReal ω) (h.tcMean y.toNNReal ω) ^ (4 : ℝ) ∂P ≤
      (6 : ℝ≥0) * edist x y ^ (2 : ℝ) := by
  wlog hxy : x ≤ y generalizing x y
  · have := this y x (le_of_not_ge hxy)
    simpa only [edist_comm] using this
  set a := x.toNNReal
  set b := y.toNNReal
  have hab : a ≤ b := Real.toNNReal_le_toNNReal hxy
  have e : ∀ ω : Ω, edist (h.tcMean a ω) (h.tcMean b ω) ^ (4 : ℝ) =
      ENNReal.ofReal ((h.tcMean b ω - h.tcMean a ω) ^ 4) := by
    intro ω
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
      abs_of_nonneg (by positivity)]
    congr 1
    ring
  simp only [e]
  rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable_tcMean_sub_pow_four hab)
    (Eventually.of_forall fun ω => by positivity)]
  have hq := h.integral_tcMean_sub_pow_four_le hab
  obtain ⟨h1, h2⟩ := toNNReal_sub_le hxy
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hMe : ((6 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal 6 := by simp
  rw [hMe, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal (hq.trans ?_)
  have : ((b : ℝ) - a) ^ 2 ≤ (x - y) ^ 2 := by
    rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]
    exact pow_le_pow_left₀ h2 h1 2
  linarith

/-- The time-changed mean is a Kolmogorov process with exponents `(4, 2)`. -/
theorem isKolmogorovProcess_tcMean [IsProbabilityMeasure P]
    (h : IsGaussianExploration P 𝓕 X v ρ K) :
    IsKolmogorovProcess (fun x : ℝ => h.tcMean x.toNNReal) P 4 2 6 := by
  refine ⟨fun s t => ?_, fun s t => h.lintegral_edist_tcMean_le s t, by norm_num, by norm_num⟩
  rw [← BorelSpace.measurable_eq (α := ℝ × ℝ)]
  exact (h.measurable_tcMean _).prodMk (h.measurable_tcMean _)

/-- **A continuous modification of the time-changed mean** (Kolmogorov–Chentsov). -/
theorem exists_continuous_tcMean [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K) :
    ∃ Nt : ℝ → Ω → ℝ, (∀ x, Measurable (Nt x)) ∧ (∀ x, Nt x =ᵐ[P] h.tcMean x.toNNReal) ∧
      ∀ ω, Continuous fun x => Nt x ω := by
  obtain ⟨Y, hYm, hYeq, hYH⟩ := exists_modification_holder_iSup
    (C := fun n : ℕ ↦ Set.Ioo (-((n : ℝ) + 1)) (n + 1)) (p := fun _ => 4) (q := fun _ => 2)
    (M := fun _ => 6) (d := 1) Sec2.JacobiExists.isCoverWithBoundedCoveringNumber_Ioo_real
    (fun _ => h.isKolmogorovProcess_tcMean.IsAEKolmogorovProcess) (fun n => by finiteness) one_pos
    (fun _ => by norm_num)
  refine ⟨Y, hYm, hYeq, fun ω => continuous_iff_continuousAt.2 fun t => ?_⟩
  have hβ : ((1 / 8 : ℝ≥0) : ℝ) < ⨆ _n : ℕ, ((2 : ℝ) - 1) / 4 := by
    rw [ciSup_const]; norm_num
  obtain ⟨U, hU, C, hC⟩ := hYH ω t (1 / 8) (by norm_num) hβ
  exact (hC.continuousOn (by norm_num)).continuousAt hU

/-! ### Identification at stopping times -/

omit [MeasurableSpace Ω] in
/-- The real clock `C_t = t + A_t`. -/
def clk (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ := (t : ℝ) + clockA v ρ t ω

theorem coe_tcClock (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) (ω : Ω) :
    ((WangWu.tcClock (clockA v ρ) ω t : ℝ≥0) : ℝ) = clk v ρ t ω := by
  simp only [WangWu.tcClock, clk, NNReal.coe_add, Real.coe_toNNReal _ (h.clockA_nonneg t ω)]

theorem continuous_clk (h : IsGaussianExploration P 𝓕 X v ρ K) (ω : Ω) :
    Continuous fun t => clk v ρ t ω :=
  NNReal.continuous_coe.add (h.continuous_clockA ω)

theorem measurable_clk (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) :
    Measurable[𝓕 t] (clk v ρ t) :=
  measurable_const.add (h.stronglyAdapted_clockA t).measurable

theorem clk_nonneg (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) (ω : Ω) :
    0 ≤ clk v ρ t ω := add_nonneg t.2 (h.clockA_nonneg t ω)

/-- `γ_{C_t} = t`. -/
theorem gam_clk (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) (ω : Ω) :
    gam v ρ (clk v ρ t ω).toNNReal ω = t := by
  rw [← h.coe_tcClock, Real.toNNReal_coe]
  exact WangWu.tcInv_tcClock (clockA_zero v ρ ω) (h.monotone_clockA ω) (h.continuous_clockA ω) t

/-- `γ_u ≥ t` once `u ≥ C_t`. -/
theorem le_gam_of_clk_le (h : IsGaussianExploration P 𝓕 X v ρ K) {t : ℝ≥0} {u : ℝ≥0} {ω : Ω}
    (hu : clk v ρ t ω ≤ u) : t ≤ gam v ρ u ω := by
  have h1 := h.gam_clk t ω
  have h2 : (clk v ρ t ω).toNNReal ≤ u := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hu
  calc t = gam v ρ (clk v ρ t ω).toNNReal ω := h1.symm
    _ ≤ gam v ρ u ω := h.monotone_gam ω h2

/-- The variance drop from `t ≤ ρ` to `γ_u ∧ ρ`, `u ≥ C_t`, is at most `u − C_t`. -/
theorem v_sub_v_gamStop_le (h : IsGaussianExploration P 𝓕 X v ρ K) {t : ℝ≥0} {u : ℝ≥0} {ω : Ω}
    (htρ : t ≤ ρ ω) (hu : clk v ρ t ω ≤ u) :
    v t ω - v (gamStop v ρ u ω) ω ≤ (u : ℝ) - clk v ρ t ω := by
  have hc0 := h.clk_nonneg t ω
  have hle : (clk v ρ t ω).toNNReal ≤ u := by rw [Real.toNNReal_le_iff_le_coe]; exact hu
  have := WangWu.A_tcInv_sub_le (clockA_zero v ρ ω) (h.monotone_clockA ω) (h.continuous_clockA ω)
    hle
  have e : WangWu.tcInv (clockA v ρ) (clk v ρ t ω).toNNReal ω = t := h.gam_clk t ω
  rw [e] at this
  simp only [clockA, min_eq_left htρ, Real.coe_toNNReal _ hc0] at this
  simp only [gamStop, gam]
  linarith

theorem measurableSpace_congr {τ τ' : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ)
    (hτ' : IsStoppingTime 𝓕 τ') (e : τ = τ') : hτ.measurableSpace = hτ'.measurableSpace := by
  subst e; rfl

/-- **The square-increment bound on a piece**: for a stopping time `σ ≤ ρ`, `u : ℝ≥0` and an `𝓕_σ`-event
`E` on which `C_σ ≤ u ≤ C_σ + δ`, `∫_E (N_u − E[X | 𝓕_σ])² ≤ δ P(E)`. -/
theorem setIntegral_tcMean_sub_sq_le [IsProbabilityMeasure P]
    (h : IsGaussianExploration P 𝓕 X v ρ K) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσρ : ∀ ω, σ ω ≤ ρ ω) (u : ℝ≥0)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E) {δ : ℝ}
    (hEu : ∀ ω ∈ E, clk v ρ (σ ω) ω ≤ u ∧ (u : ℝ) - clk v ρ (σ ω) ω ≤ δ) :
    ∫ ω in E, (h.tcMean u ω - P[X | hσ.measurableSpace] ω) ^ 2 ∂P ≤ δ * P.real E := by
  set T : Ω → ℝ≥0 := gamStop v ρ u
  have hT := h.isStoppingTime_gamStop u
  set S' : Ω → ℝ≥0 := fun ω => min (σ ω) (T ω)
  have hS' : IsStoppingTime 𝓕 fun ω => (S' ω : WithTop ℝ≥0) := isStoppingTime_min_coe hσ hT
  have hS'T : hS'.measurableSpace ≤ hT.measurableSpace :=
    IsStoppingTime.measurableSpace_mono _ _ fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)
  have hσT : ∀ ω ∈ E, σ ω ≤ T ω := fun ω hω =>
    le_min (h.le_gam_of_clk_le (hEu ω hω).1) (hσρ ω)
  have hEm : MeasurableSet E := hσ.measurableSpace_le _ hE
  -- `E ∈ 𝓕_{S'}`
  have hES' : MeasurableSet[hS'.measurableSpace] E := by
    have h1 := IsStoppingTime.measurableSet_inter_le hσ hT E hE
    have e1 : E ∩ {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (T ω : WithTop ℝ≥0)} = E := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe, and_iff_left_iff_imp]
      exact hσT ω
    rw [e1] at h1
    have e2 : (hσ.min hT).measurableSpace = hS'.measurableSpace :=
      measurableSpace_congr _ _ (funext fun ω => by simp [S', T])
    rwa [e2] at h1
  have g₁ := h.gauss S' hS' fun ω => (min_le_left _ _).trans (hσρ ω)
  have g₂ := h.gauss_gamStop u
  have hW : Measurable[hS'.measurableSpace] (E.indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator hES'
  have hid := integral_mul_sq_sub g₁ g₂ hS'T hW zero_le_one fun ω => by
    by_cases hω : ω ∈ E <;> simp [hω]
  -- on `E`, the mean at `S'` is the mean at `σ`
  have hmin : P[X | (hσ.min hT).measurableSpace] =ᵐ[P.restrict {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) ≤
      (T ω : WithTop ℝ≥0)}] P[X | hσ.measurableSpace] :=
    condExp_min_stopping_time_ae_eq_restrict_le hσ hT
  have e2 : (hσ.min hT).measurableSpace = hS'.measurableSpace :=
    measurableSpace_congr _ _ (funext fun ω => by simp [S', T])
  rw [e2] at hmin
  have hmeas_le : MeasurableSet {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (T ω : WithTop ℝ≥0)} :=
    hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hT)
  have hmin' : ∀ᵐ ω ∂P, ω ∈ E → P[X | hS'.measurableSpace] ω = P[X | hσ.measurableSpace] ω := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hmeas_le] at hmin
    filter_upwards [hmin] with ω hω hωE
    exact hω (WithTop.coe_le_coe.2 (hσT ω hωE))
  calc ∫ ω in E, (h.tcMean u ω - P[X | hσ.measurableSpace] ω) ^ 2 ∂P
      = ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω * (h.tcMean u ω - P[X | hS'.measurableSpace] ω) ^ 2 ∂P := by
        rw [← integral_indicator hEm]
        refine integral_congr_ae ?_
        filter_upwards [hmin'] with ω hω
        by_cases hωE : ω ∈ E
        · rw [indicator_of_mem hωE, indicator_of_mem hωE, one_mul, hω hωE]
        · simp [hωE]
    _ = ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω * (v (S' ω) ω - v (T ω) ω) ∂P := hid
    _ ≤ ∫ ω, E.indicator (fun _ => δ) ω ∂P := by
        refine integral_mono_of_nonneg ?_ ((integrable_const δ).indicator hEm) ?_
        · refine Eventually.of_forall fun ω => ?_
          by_cases hωE : ω ∈ E
          · have : S' ω = σ ω := min_eq_left (hσT ω hωE)
            simp only [indicator_of_mem hωE, one_mul, this]
            exact sub_nonneg.2 (h.anti ω _ _ (hσT ω hωE) (min_le_right _ _))
          · simp [hωE]
        · refine Eventually.of_forall fun ω => ?_
          by_cases hωE : ω ∈ E
          · have : S' ω = σ ω := min_eq_left (hσT ω hωE)
            simp only [indicator_of_mem hωE, one_mul, this]
            exact (h.v_sub_v_gamStop_le (hσρ ω) (hEu ω hωE).1).trans (hEu ω hωE).2
          · simp [hωE]
    _ = δ * P.real E := by
        rw [integral_indicator hEm, setIntegral_const, smul_eq_mul, mul_comm]

/-- The dyadic index `⌈2ⁿ x⌉`. -/
def dyIdx (n : ℕ) (x : ℝ) : ℕ := ⌈(2 : ℝ) ^ n * x⌉₊

/-- The dyadic point `k / 2ⁿ`. -/
def dyPt (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

omit [MeasurableSpace Ω] in
lemma coe_dyPt (n k : ℕ) : ((dyPt n k : ℝ≥0) : ℝ) = (k : ℝ) / 2 ^ n := by simp [dyPt]

omit [MeasurableSpace Ω] in
lemma le_dyPt_dyIdx (n : ℕ) (x : ℝ) : x ≤ (dyPt n (dyIdx n x) : ℝ) := by
  rw [coe_dyPt, dyIdx, le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

omit [MeasurableSpace Ω] in
lemma dyPt_dyIdx_sub_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (dyPt n (dyIdx n x) : ℝ) - x ≤ 1 / 2 ^ n := by
  have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 ^ n * x)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [coe_dyPt, dyIdx, sub_le_iff_le_add, div_le_iff₀ h2, add_mul, div_mul_cancel₀ _ h2.ne']
  linarith

omit [MeasurableSpace Ω] in
lemma measurable_dyIdx (n : ℕ) : Measurable (dyIdx n) :=
  Nat.measurable_ceil.comp (measurable_const.mul measurable_id)

/-- The clock at a stopping time `σ ≤ ρ` is `𝓕_σ`-measurable. -/
theorem measurable_clk_stop (h : IsGaussianExploration P 𝓕 X v ρ K) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) :
    Measurable[hσ.measurableSpace] fun ω => clk v ρ (σ ω) ω :=
  (stronglyMeasurable_comp_stoppingTime h.continuous_clk h.measurable_clk hσ).measurable

/-- The time-changed mean read at the random dyadic point above the clock at `σ`. -/
def dyMean (h : IsGaussianExploration P 𝓕 X v ρ K) (σ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  h.tcMean (dyPt n (dyIdx n (clk v ρ (σ ω) ω))) ω

theorem measurable_dyMean (h : IsGaussianExploration P 𝓕 X v ρ K) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (n : ℕ) :
    Measurable (h.dyMean σ n) := by
  let F : ℕ × Ω → ℝ := fun p => h.tcMean (dyPt n p.1) p.2
  have hF : Measurable F :=
    measurable_from_prod_countable_right fun k => h.measurable_tcMean (dyPt n k)
  let g : Ω → ℕ × Ω := fun ω => (dyIdx n (clk v ρ (σ ω) ω), ω)
  have hg : Measurable g :=
    ((measurable_dyIdx n).comp ((h.measurable_clk_stop hσ).mono hσ.measurableSpace_le
      le_rfl)).prodMk measurable_id
  have e : h.dyMean σ n = F ∘ g := rfl
  rw [e]
  exact hF.comp hg

/-- **The square bound at level `n`**: `E[(N_{u_n} − E[X | 𝓕_σ])²] ≤ 2^{-n}`, `u_n = ⌈2ⁿ C_σ⌉ / 2ⁿ`. -/
theorem lintegral_dyMean_sub_sq_le [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσρ : ∀ ω, σ ω ≤ ρ ω)
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2) ∂P ≤
      ENNReal.ofReal (1 / 2 ^ n) := by
  have hkm : Measurable[hσ.measurableSpace] fun ω => dyIdx n (clk v ρ (σ ω) ω) :=
    (measurable_dyIdx n).comp (h.measurable_clk_stop hσ)
  let E : ℕ → Set Ω := fun k => (fun ω => dyIdx n (clk v ρ (σ ω) ω)) ⁻¹' {k}
  have hEm : ∀ k, MeasurableSet[hσ.measurableSpace] (E k) := fun k =>
    hkm (measurableSet_singleton k)
  have hEm' : ∀ k, MeasurableSet (E k) := fun k => hσ.measurableSpace_le _ (hEm k)
  have hU : (⋃ k, E k) = univ := by
    ext ω; simp only [E, mem_iUnion, mem_preimage, mem_singleton_iff, mem_univ, iff_true]
    exact ⟨_, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    Set.disjoint_left.2 fun ω hi hj => hij (hi.symm.trans hj)
  have hXY : ∀ u : ℝ≥0, MemLp (fun ω => h.tcMean u ω - P[X | hσ.measurableSpace] ω) 2 P :=
    fun u => (h.integrable.condExp (m := (h.isStoppingTime_gamStop u).measurableSpace)
      one_le_two).sub (h.integrable.condExp (m := hσ.measurableSpace) one_le_two)
  have hk : ∀ k, ∫⁻ ω in E k, ENNReal.ofReal ((h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2)
      ∂P ≤ ENNReal.ofReal (1 / 2 ^ n) * P (E k) := by
    intro k
    have hEk : ∀ ω ∈ E k, h.dyMean σ n ω = h.tcMean (dyPt n k) ω := fun ω hω => by
      simp only [dyMean]
      rw [show dyIdx n (clk v ρ (σ ω) ω) = k from hω]
    rw [setLIntegral_congr_fun (hEm' k) fun ω hω => by rw [hEk ω hω]]
    rw [← ofReal_integral_eq_lintegral_ofReal ((hXY (dyPt n k)).integrable_sq.integrableOn)
      (Eventually.of_forall fun ω => sq_nonneg _)]
    have hb := h.setIntegral_tcMean_sub_sq_le hσ hσρ (dyPt n k) (hEm k) (δ := 1 / 2 ^ n)
      fun ω hω => by
        have hk : dyIdx n (clk v ρ (σ ω) ω) = k := hω
        have h1 := le_dyPt_dyIdx n (clk v ρ (σ ω) ω)
        have h2 := dyPt_dyIdx_sub_le n (h.clk_nonneg (σ ω) ω)
        rw [hk] at h1 h2
        exact ⟨h1, h2⟩
    refine (ENNReal.ofReal_le_ofReal hb).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top P _)]
  calc ∫⁻ ω, ENNReal.ofReal ((h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2) ∂P
      = ∫⁻ ω in ⋃ k, E k, ENNReal.ofReal ((h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2)
          ∂P := by rw [hU, Measure.restrict_univ]
    _ = ∑' k, ∫⁻ ω in E k, ENNReal.ofReal ((h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2)
          ∂P := lintegral_iUnion hEm' hdisj _
    _ ≤ ∑' k, ENNReal.ofReal (1 / 2 ^ n) * P (E k) := ENNReal.tsum_le_tsum hk
    _ = ENNReal.ofReal (1 / 2 ^ n) * P (⋃ k, E k) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hEm']
    _ = ENNReal.ofReal (1 / 2 ^ n) := by rw [hU, measure_univ, mul_one]

/-- **Identification at stopping times**: for a continuous modification `Ñ` of the time-changed mean,
`Ñ(C_σ) = E[X | 𝓕_σ]` almost surely, at every stopping time `σ ≤ ρ`. -/
theorem ae_eq_condExp_clk [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Nt : ℝ → Ω → ℝ} (hNeq : ∀ x, Nt x =ᵐ[P] h.tcMean x.toNNReal)
    (hNc : ∀ ω, Continuous fun x => Nt x ω) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσρ : ∀ ω, σ ω ≤ ρ ω) :
    (fun ω => Nt (clk v ρ (σ ω) ω) ω) =ᵐ[P] P[X | hσ.measurableSpace] := by
  have hYm : Measurable (P[X | hσ.measurableSpace]) :=
    stronglyMeasurable_condExp.measurable.mono hσ.measurableSpace_le le_rfl
  -- almost sure convergence of the dyadic means
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => h.dyMean σ n ω) atTop
      (𝓝 (P[X | hσ.measurableSpace] ω)) := by
    have hmeas : ∀ n, Measurable fun ω =>
        ENNReal.ofReal ((h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2) := fun n =>
      ENNReal.measurable_ofReal.comp (((h.measurable_dyMean hσ n).sub hYm).pow_const 2)
    have hsum : ∫⁻ ω, ∑' n, ENNReal.ofReal ((h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2)
        ∂P ≠ ⊤ := by
      rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (h.lintegral_dyMean_sub_sq_le hσ hσρ))
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)]
      · exact ENNReal.ofReal_ne_top
      · simpa only [one_div, inv_pow] using summable_geometric_two
    filter_upwards [ae_lt_top' (Measurable.tsum hmeas).aemeasurable hsum] with ω hω
    have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
    have h1 : Tendsto (fun n => (h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) ^ 2) atTop
        (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
      simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_zero]
        using this
    have h2 : Tendsto (fun n => h.dyMean σ n ω - P[X | hσ.measurableSpace] ω) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h1.sqrt
    simpa using h2.add_const (P[X | hσ.measurableSpace] ω)
  -- agreement at the dyadics
  have hagree : ∀ᵐ ω ∂P, ∀ n k, Nt (dyPt n k : ℝ) ω = h.tcMean (dyPt n k) ω := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k
    filter_upwards [hNeq (dyPt n k : ℝ)] with ω hω
    rw [hω, Real.toNNReal_coe]
  filter_upwards [hconv, hagree] with ω h1 h2
  set c := clk v ρ (σ ω) ω
  have hqc : Tendsto (fun n => (dyPt n (dyIdx n c) : ℝ)) atTop (𝓝 c) := by
    have hlim : Tendsto (fun n : ℕ => c + 1 / 2 ^ n) atTop (𝓝 c) := by
      have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa [one_div_pow] using tendsto_const_nhds.add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => le_dyPt_dyIdx n c)
      fun n => by linarith [dyPt_dyIdx_sub_le n (h.clk_nonneg (σ ω) ω)]
  have h3 : Tendsto (fun n => Nt (dyPt n (dyIdx n c) : ℝ) ω) atTop (𝓝 (Nt c ω)) :=
    ((hNc ω).tendsto c).comp hqc
  simp only [h2] at h3
  exact tendsto_nhds_unique h3 h1

/-- **Time continuity** (abstract form of the first assertion of Proposition 6.5): the stopped
conditional mean has a version `M` that is continuous and stopped at `ρ` for every `ω`, measurable at
each time, and equal to `E[X | 𝓕_σ]` at every stopping time `σ ≤ ρ`. -/
theorem exists_continuous_version [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => M t ω) ∧ (∀ t, Measurable (M t)) ∧
      (∀ ω t, ρ ω ≤ t → M t ω = M (ρ ω) ω) ∧
      ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)), (∀ ω, σ ω ≤ ρ ω) →
        (fun ω => M (σ ω) ω) =ᵐ[P] P[X | hσ.measurableSpace] := by
  obtain ⟨Nt, hNm, hNeq, hNc⟩ := h.exists_continuous_tcMean
  have hNjm : Measurable (Function.uncurry Nt) :=
    measurable_uncurry_of_continuous_of_measurable hNc hNm
  refine ⟨fun t ω => Nt (clk v ρ (min t (ρ ω)) ω) ω, fun ω => ?_, fun t => ?_, fun ω t ht => ?_,
    fun σ hσ hσρ => ?_⟩
  · exact (hNc ω).comp ((h.continuous_clk ω).comp (continuous_id.min continuous_const))
  · have hc : Measurable fun ω => clk v ρ (min t (ρ ω)) ω :=
      (h.measurable_clk_stop (h.isStoppingTime_min_const t)).mono
        (h.isStoppingTime_min_const t).measurableSpace_le le_rfl
    exact hNjm.comp (hc.prodMk measurable_id)
  · simp only [min_eq_right ht, min_self]
  · have := h.ae_eq_condExp_clk hNeq hNc hσ hσρ
    filter_upwards [this] with ω hω
    simp only [min_eq_left (hσρ ω)]
    exact hω

omit [MeasurableSpace Ω] in
/-- A measurable function almost everywhere equal to an `m`-measurable one is `m`-measurable when `m`
contains the null sets. -/
theorem measurable_of_ae_eq_of_null {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (hnull : ∀ s, MeasurableSet[mΩ] s → P s = 0 → MeasurableSet[m] s) {f g : Ω → ℝ}
    (hf : Measurable[mΩ] f) (hg : Measurable[m] g) (hm : m ≤ mΩ) (hfg : f =ᵐ[P] g) :
    Measurable[m] f := by
  have hN : MeasurableSet[mΩ] {ω | f ω ≠ g ω} :=
    (measurableSet_eq_fun hf (hg.mono hm le_rfl)).compl
  have hN0 : P {ω | f ω ≠ g ω} = 0 := hfg
  intro B hB
  have e : f ⁻¹' B = (g ⁻¹' B ∩ {ω | f ω ≠ g ω}ᶜ) ∪ (f ⁻¹' B ∩ {ω | f ω ≠ g ω}) := by
    ext ω
    by_cases hω : f ω = g ω
    · simp [hω]
    · simp [hω]
  rw [e]
  refine (hg hB |>.inter (hnull _ hN hN0).compl).union (hnull _ ((hf hB).inter hN) ?_)
  exact measure_mono_null inter_subset_right hN0

/-- **The martingale conclusions**: if `𝓕₀` contains the null sets, the continuous version `M` is a
martingale, and so is `M² + v_{·∧ρ}`; that is, `M − M₀` is a continuous martingale with quadratic
variation `v₀ − v_{·∧ρ}`. -/
theorem martingale_of_version [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {M : ℝ≥0 → Ω → ℝ}
    (hMm : ∀ t, Measurable (M t)) (hMstop : ∀ ω t, ρ ω ≤ t → M t ω = M (ρ ω) ω)
    (hMσ : ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)),
      (∀ ω, σ ω ≤ ρ ω) → (fun ω => M (σ ω) ω) =ᵐ[P] P[X | hσ.measurableSpace]) :
    Martingale M 𝓕 P ∧ Martingale (fun t ω => M t ω ^ 2 + v (min t (ρ ω)) ω) 𝓕 P := by
  have hτ := h.isStoppingTime_min_const
  have hτle : ∀ t, (hτ t).measurableSpace ≤ 𝓕 t := fun t => by
    have := IsStoppingTime.measurableSpace_mono (hτ t) (isStoppingTime_const 𝓕 t)
      fun ω => WithTop.coe_le_coe.2 (min_le_left t (ρ ω))
    rwa [IsStoppingTime.measurableSpace_const] at this
  have hnull' : ∀ t, ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 t] s := fun t s hs h0 =>
    𝓕.mono (zero_le (a := t)) _ (hnull s hs h0)
  have hMt : ∀ t, M t =ᵐ[P] P[X | (hτ t).measurableSpace] := fun t => by
    have := hMσ (fun ω => min t (ρ ω)) (hτ t) fun ω => min_le_right _ _
    filter_upwards [this] with ω hω
    rw [← hω]
    rcases le_total t (ρ ω) with htρ | hρt
    · rw [min_eq_left htρ]
    · rw [min_eq_right hρt, hMstop ω t hρt]
  -- the conditional-expectation identity along the stopped times
  have hcomm : ∀ (W : Ω → ℝ) (s t : ℝ≥0), s ≤ t →
      P[P[W | (hτ t).measurableSpace] | 𝓕 s] =ᵐ[P] P[W | (hτ s).measurableSpace] := by
    intro W s t hst
    have h1 := condExp_condExp_stoppingTime (P := P) (isStoppingTime_const 𝓕 s) (hτ t) W
    rw [IsStoppingTime.measurableSpace_const] at h1
    refine h1.trans (Eq.eventuallyEq ?_)
    congr 1
    exact measurableSpace_congr _ _ (funext fun ω => by
      simp only [← WithTop.coe_min]
      congr 1
      rw [← min_assoc, min_eq_left hst])
  have hAd : StronglyAdapted 𝓕 M := fun t =>
    (measurable_of_ae_eq_of_null (hnull' t) (hMm t)
      (stronglyMeasurable_condExp.measurable.mono (hτle t) le_rfl) (𝓕.le t) (hMt t)).stronglyMeasurable
  have hvτ : ∀ t, StronglyMeasurable[(hτ t).measurableSpace] fun ω => v (min t (ρ ω)) ω :=
    fun t => stronglyMeasurable_comp_stoppingTime h.cont h.adapted (hτ t)
  refine ⟨⟨hAd, fun s t hst => ?_⟩, ⟨fun t => ?_, fun s t hst => ?_⟩⟩
  · calc P[M t | 𝓕 s] =ᵐ[P] P[P[X | (hτ t).measurableSpace] | 𝓕 s] := condExp_congr_ae (hMt t)
      _ =ᵐ[P] P[X | (hτ s).measurableSpace] := hcomm X s t hst
      _ =ᵐ[P] M s := (hMt s).symm
  · exact ((hAd t).pow 2).add ((hvτ t).mono (hτle t))
  · -- `M_t² + v_{t∧ρ} = E[X² | 𝓕_{t∧ρ}]`
    have hsq : ∀ t, (fun ω => M t ω ^ 2 + v (min t (ρ ω)) ω) =ᵐ[P]
        P[fun ω => X ω ^ 2 | (hτ t).measurableSpace] := fun t => by
      have g := h.gauss (fun ω => min t (ρ ω)) (hτ t) fun ω => min_le_right _ _
      filter_upwards [hMt t, g.condExp_sq h.integrable] with ω h1 h2
      rw [h2, h1]
    calc P[fun ω => M t ω ^ 2 + v (min t (ρ ω)) ω | 𝓕 s]
        =ᵐ[P] P[P[fun ω => X ω ^ 2 | (hτ t).measurableSpace] | 𝓕 s] := condExp_congr_ae (hsq t)
      _ =ᵐ[P] P[fun ω => X ω ^ 2 | (hτ s).measurableSpace] := hcomm _ s t hst
      _ =ᵐ[P] fun ω => M s ω ^ 2 + v (min s (ρ ω)) ω := (hsq s).symm

end IsGaussianExploration

end InteractingSLE.Sec6.Prop65
