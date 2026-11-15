import InteractingSLE.Spec.Sec2.MartingaleQV
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import MathFin.Probability.Brownian.LevyCharacterization
import MathFin.Probability.Brownian.ExitTime
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal

/-!
# From the Laurent-coefficient martingales to a Brownian motion (Theorem 2.4, converse direction)

Packet PROVE-SEC2-MART. Specification, proof of Theorem 2.4 (`source/spec/p001-048.md`, anchor
`thm-2.4-proof`, L834–L874 and L894–L898). Let `W` be a continuous adapted driver and `Vʲ`
continuous adapted force-point coordinates with the deterministic properties of geometric
force-point images (`IsForcePath`: monotone, `dVʲ = 2/(Vʲ − W) dt` away from collisions, null
collision set). If the first two Laurent coefficients of `𝔥_t(z)` at `∞`,

  `N = 2W + ∑ⱼ ρⱼ Vʲ`,  `Q = W² + ½ ∑ⱼ ρⱼ (Vʲ)² − (2 ∑ⱼ ρⱼ + κ) t`,

are martingales up to localizing times, then the martingale part
`M = W − W₀ + ½ ∑ⱼ ρⱼ (Vʲ − Vʲ₀)` and `M² − κ t` are local martingales, so `M / √κ` is a Brownian
motion in the filtration by Lévy's characterization (`MathFin.LevyCharacterization`). This replaces
the source's Itô computation (2.6)–(2.7) for a general semimartingale driver (not available in the
vendored calculus) by the discrete expansion of `M²` along partitions: the cell identity of
`MartingaleQV` and the Riemann–Stieltjes limit `∑ (Vʲ − W) ΔVʲ → 2 Δt` of `MartingaleStieltjes`.

## Main results

* `martingale_stoppedProcess_martProc_sq_sub`: for a bounded stopping time `τ` up to which the
  coordinates are bounded, if `N^τ` and `Q^τ` are martingales then so is `(M² − κ t)^τ`;
* `martingale_stoppedProcess_martProc`: `M^τ` is a martingale;
* `isFilteredBrownianReal_martProc_div_sqrt`: if `N` and `Q` stopped at the localizing times
  `min T (exitTime Z K)` (`Z = |W| + ∑ⱼ |Vʲ|`) are martingales, then `M / √κ` is an
  `𝓕`-Brownian motion (`IsFilteredBrownianReal`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

/-! ### Path conditions and the coefficient processes -/

/-- The deterministic properties of a force-point coordinate `v` relative to a driver `w` used in
the proof of Theorem 2.4 ("deterministic properties of the real boundary maps", p. 35, and Lemma
2.5): `v` is continuous and monotone, solves `v' = 2/(v − w)` at every positive time where
`v ≠ w`, and its collision set with `w` is Lebesgue-null. Time is `ℝ≥0`; derivatives are taken
for the extension `s ↦ v s.toNNReal` to `ℝ`. -/
def IsForcePath (w v : ℝ≥0 → ℝ) : Prop :=
  Continuous v ∧ (Monotone v ∨ Antitone v) ∧
    (∀ u : ℝ, 0 < u → v u.toNNReal ≠ w u.toNNReal →
      HasDerivAt (fun s : ℝ => v s.toNNReal) (2 / (v u.toNNReal - w u.toNNReal)) u) ∧
    volume {u : ℝ | 0 ≤ u ∧ v u.toNNReal = w u.toNNReal} = 0

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι]

/-- The first Laurent coefficient process `N = 2W + ∑ⱼ ρⱼ Vʲ`. -/
def driftProc (ρ : ι → ℝ) (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => driftValue ρ (W t ω) (fun j => V j t ω)

/-- The second Laurent coefficient process `Q = W² + ½ ∑ⱼ ρⱼ (Vʲ)² − (2 ∑ⱼ ρⱼ + κ) t`. -/
def quadProc (κ : ℝ) (ρ : ι → ℝ) (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => quadValue κ ρ (W t ω) (fun j => V j t ω) t

/-- The martingale part `M = W − W₀ + ½ ∑ⱼ ρⱼ (Vʲ − Vʲ₀)` of the driver. -/
def martProc (ρ : ι → ℝ) (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => martValue ρ (W 0 ω) (fun j => V j 0 ω) (W t ω) (fun j => V j t ω)

lemma martValue_sub_martValue (ρ : ι → ℝ) (w₀ : ℝ) (v₀ : ι → ℝ) (a₀ a₁ : ℝ) (b₀ b₁ : ι → ℝ) :
    martValue ρ w₀ v₀ a₁ b₁ - martValue ρ w₀ v₀ a₀ b₀
      = (1 / 2) * (driftValue ρ a₁ b₁ - driftValue ρ a₀ b₀) := by
  have h : (∑ j, ρ j * (b₁ j - v₀ j)) - ∑ j, ρ j * (b₀ j - v₀ j)
      = (∑ j, ρ j * b₁ j) - ∑ j, ρ j * b₀ j := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [martValue, driftValue]
  linear_combination (1 / 2 : ℝ) * h

/-- The telescoped cell identity along a sequence of states. -/
lemma sum_cell_identity (κ : ℝ) (ρ : ι → ℝ) (w₀ : ℝ) (v₀ : ι → ℝ) (wk : ℕ → ℝ) (vk : ι → ℕ → ℝ)
    (tk : ℕ → ℝ) (n : ℕ) :
    martValue ρ w₀ v₀ (wk n) (fun j => vk j n) ^ 2 - martValue ρ w₀ v₀ (wk 0) (fun j => vk j 0) ^ 2
        - κ * (tk n - tk 0)
      = (quadValue κ ρ (wk n) (fun j => vk j n) (tk n)
          - quadValue κ ρ (wk 0) (fun j => vk j 0) (tk 0))
        + (∑ k ∈ Finset.range n, 2 * (martValue ρ w₀ v₀ (wk k) (fun j => vk j k) - wk k)
            * (martValue ρ w₀ v₀ (wk (k + 1)) (fun j => vk j (k + 1))
              - martValue ρ w₀ v₀ (wk k) (fun j => vk j k)))
        + ∑ k ∈ Finset.range n, cellDefect ρ (wk k) (wk (k + 1)) (fun j => vk j k)
            (fun j => vk j (k + 1)) (tk (k + 1) - tk k) := by
  calc _ = ∑ k ∈ Finset.range n,
        (martValue ρ w₀ v₀ (wk (k + 1)) (fun j => vk j (k + 1)) ^ 2
          - martValue ρ w₀ v₀ (wk k) (fun j => vk j k) ^ 2 - κ * (tk (k + 1) - tk k)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_range_sub
          (fun k => martValue ρ w₀ v₀ (wk k) (fun j => vk j k) ^ 2), ← Finset.mul_sum,
          Finset.sum_range_sub tk]
    _ = ∑ k ∈ Finset.range n,
        ((quadValue κ ρ (wk (k + 1)) (fun j => vk j (k + 1)) (tk (k + 1))
          - quadValue κ ρ (wk k) (fun j => vk j k) (tk k))
        + 2 * (martValue ρ w₀ v₀ (wk k) (fun j => vk j k) - wk k)
            * (martValue ρ w₀ v₀ (wk (k + 1)) (fun j => vk j (k + 1))
              - martValue ρ w₀ v₀ (wk k) (fun j => vk j k))
        + cellDefect ρ (wk k) (wk (k + 1)) (fun j => vk j k)
            (fun j => vk j (k + 1)) (tk (k + 1) - tk k)) :=
        Finset.sum_congr rfl fun k _ => cell_identity κ ρ w₀ v₀ (wk k) (wk (k + 1))
          (fun j => vk j k) (fun j => vk j (k + 1)) (tk k) (tk (k + 1))
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_range_sub (fun k => quadValue κ ρ (wk k) (fun j => vk j k) (tk k))]

/-! ### Martingale increments against bounded predictable weights -/

omit [Fintype ι] in
/-- A bounded `𝓕ᵢ`-measurable weight times a martingale increment has expectation zero. -/
lemma integral_mul_sub_eq_zero [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P)
    {i j : ℝ≥0} (hij : i ≤ j) {g : Ω → ℝ} (hg : StronglyMeasurable[𝓕 i] g) {C : ℝ}
    (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * (X j ω - X i ω) ∂P = 0 := by
  have hgm : AEStronglyMeasurable g P := (hg.mono (𝓕.le i)).aestronglyMeasurable
  have hbdd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω
  have hintj : Integrable (g * X j) P := (hX.integrable j).bdd_mul hgm hbdd
  have hinti : Integrable (g * X i) P := (hX.integrable i).bdd_mul hgm hbdd
  have hcond := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 i) hg hintj (hX.integrable j)
  have h1 : ∫ ω, (g * X j) ω ∂P = ∫ ω, (g * X i) ω ∂P := by
    rw [← integral_condExp (𝓕.le i)]
    refine integral_congr_ae ?_
    filter_upwards [hcond, hX.condExp_ae_eq hij] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, Pi.mul_apply]
  have hsub : (fun ω => g ω * (X j ω - X i ω)) = fun ω => (g * X j) ω - (g * X i) ω := by
    funext ω; simp only [Pi.mul_apply]; ring
  rw [hsub, integral_sub hintj hinti, h1, sub_self]

/-! ### Stopped times -/

omit [Fintype ι] in
lemma coe_untopA_of_ne_top {a : WithTop ℝ≥0} (ha : a ≠ ⊤) : ((a.untopA : ℝ≥0) : WithTop ℝ≥0) = a := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 ha
  rfl

omit [Fintype ι] in
/-- The stopped time `min u τ` of a finite random time, as an element of `ℝ≥0`. -/
lemma untopA_min_eq {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (u : ℝ≥0) (ω : Ω) :
    (min (u : WithTop ℝ≥0) (τ ω)).untopA = min u (τ ω).untopA := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr, ← WithTop.coe_min]
  rfl

omit [Fintype ι] in
lemma untopA_le_of_le {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    (τ ω).untopA ≤ T := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω)
  have h := hτT ω
  rw [← coe_untopA_of_ne_top hne] at h
  exact WithTop.coe_le_coe.1 h

omit [Fintype ι] in
lemma coe_min_untopA_le {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (u : ℝ≥0) (ω : Ω) :
    ((min u (τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω)
  calc ((min u (τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) :=
        WithTop.coe_le_coe.2 (min_le_right _ _)
    _ = τ ω := coe_untopA_of_ne_top hne

/-- The uniform grid `s + k (t − s)/(n + 1)` of `[s, t]`. -/
def gridPt (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 := s + (k : ℝ≥0) * ((t - s) / (n + 1))

lemma gridPt_zero (s t : ℝ≥0) (n : ℕ) : gridPt s t n 0 = s := by simp [gridPt]

lemma gridPt_last {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) : gridPt s t n (n + 1) = t := by
  simp only [gridPt]
  rw [Nat.cast_add, Nat.cast_one, mul_div_cancel₀ _ (by positivity : ((n : ℝ≥0) + 1) ≠ 0),
    add_tsub_cancel_of_le hst]

lemma gridPt_mono (s t : ℝ≥0) (n : ℕ) : Monotone (gridPt s t n) := fun k l hkl => by
  simp only [gridPt]
  gcongr

lemma le_gridPt (s t : ℝ≥0) (n k : ℕ) : s ≤ gridPt s t n k := le_self_add

lemma coe_gridPt_succ_sub (s t : ℝ≥0) (n k : ℕ) :
    (gridPt s t n (k + 1) : ℝ) - gridPt s t n k = (((t - s) / (n + 1) : ℝ≥0) : ℝ) := by
  simp only [gridPt, NNReal.coe_add, NNReal.coe_mul, Nat.cast_add, Nat.cast_one, NNReal.coe_add,
    NNReal.coe_natCast, NNReal.coe_one]
  ring

/-- A `1`-Lipschitz bound for `min · r`. -/
lemma min_sub_min_le {u u' r : ℝ≥0} (h : u ≤ u') :
    ((min u' r : ℝ≥0) : ℝ) - (min u r : ℝ≥0) ≤ (u' : ℝ) - u := by
  rcases le_total u' r with h1 | h1
  · rw [min_eq_left h1, min_eq_left (h.trans h1)]
  · rw [min_eq_right h1]
    rcases le_total u r with h2 | h2
    · rw [min_eq_left h2]
      have : (r : ℝ) ≤ u' := h1
      linarith
    · rw [min_eq_right h2]
      have : (u : ℝ) ≤ u' := h
      linarith

/-- A bound for the martingale part of bounded states. -/
lemma abs_martValue_le (ρ : ι → ℝ) {K w₀ a : ℝ} {v₀ b : ι → ℝ} (hw₀ : |w₀| ≤ K)
    (hv₀ : ∀ j, |v₀ j| ≤ K) (ha : |a| ≤ K) (hb : ∀ j, |b j| ≤ K) :
    |martValue ρ w₀ v₀ a b| ≤ 2 * K + (∑ j, |ρ j|) * K := by
  have hsum : |∑ j, ρ j * (b j - v₀ j)| ≤ (∑ j, |ρ j|) * (2 * K) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |b j - v₀ j| ≤ |b j| + |v₀ j| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hb j, hv₀ j]
  have h1 : |a - w₀| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
  calc |martValue ρ w₀ v₀ a b| ≤ |a - w₀| + |1 / 2 * ∑ j, ρ j * (b j - v₀ j)| := abs_add_le _ _
    _ = |a - w₀| + 1 / 2 * |∑ j, ρ j * (b j - v₀ j)| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ 2 * K + (∑ j, |ρ j|) * K := by nlinarith

omit [Fintype ι] in
lemma measurable_cellDefect [Fintype ι] (ρ : ι → ℝ) {w₀ w₁ d : Ω → ℝ} {v₀ v₁ : ι → Ω → ℝ}
    (hw₀ : Measurable w₀) (hw₁ : Measurable w₁) (hv₀ : ∀ j, Measurable (v₀ j))
    (hv₁ : ∀ j, Measurable (v₁ j)) (hd : Measurable d) :
    Measurable fun ω => cellDefect ρ (w₀ ω) (w₁ ω) (fun j => v₀ j ω) (fun j => v₁ j ω) (d ω) := by
  simp only [cellDefect]
  fun_prop

/-! ### The core: `(M² − κ t)^τ` is a martingale -/

section Core

variable [IsProbabilityMeasure P] {ρ : ι → ℝ} {κ : ℝ} {W : ℝ≥0 → Ω → ℝ}
  {V : ι → ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0} {K : ℝ}

omit [Fintype ι] [IsProbabilityMeasure P] in
/-- A continuous adapted process stopped at a stopping time is adapted. -/
lemma stronglyAdapted_stoppedProcess_of_continuous {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝓕 X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕 (stoppedProcess X τ) :=
  (isStronglyProgressive_of_rightContinuous hX
    fun ω _ => (hXc ω).continuousWithinAt).stronglyAdapted_stoppedProcess hτ

/-- **The core of the quadratic-variation identification.** Let `τ ≤ T` be a stopping time up to
which `W` and the `Vʲ` are bounded by `K`, with continuous adapted paths satisfying the force-path
conditions. If `N^τ` and `Q^τ` are martingales, then `(M² − κ t)^τ` is a martingale. -/
theorem martingale_stoppedProcess_martProc_sq_sub (hτ : IsStoppingTime 𝓕 τ)
    (hτT : ∀ ω, τ ω ≤ T)
    (hK : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → |W t ω| ≤ K ∧ ∀ j, |V j t ω| ≤ K)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVa : ∀ j, StronglyAdapted 𝓕 (V j))
    (hpath : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => V j t ω))
    (hN : Martingale (stoppedProcess (driftProc ρ W V) τ) 𝓕 P)
    (hQ : Martingale (stoppedProcess (quadProc κ ρ W V) τ) 𝓕 P) :
    Martingale (stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) τ) 𝓕 P := by
  -- notation for the stopped time
  set θ : ℝ≥0 → Ω → ℝ≥0 := fun u ω => min u (τ ω).untopA with hθ_def
  have hθ : ∀ (u : ℝ≥0) (ω : Ω), (min (u : WithTop ℝ≥0) (τ ω)).untopA = θ u ω :=
    untopA_min_eq hτT
  have hθτ : ∀ (u : ℝ≥0) (ω : Ω), ((θ u ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := coe_min_untopA_le hτT
  have hθT : ∀ (u : ℝ≥0) (ω : Ω), θ u ω ≤ T := fun u ω =>
    (min_le_right _ _).trans (untopA_le_of_le hτT ω)
  -- adaptedness of the stopped coordinates
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => (hpath ω j).1
  have hstop : ∀ (X : ℝ≥0 → Ω → ℝ) (u : ℝ≥0),
      (fun ω => X (θ u ω) ω) = stoppedProcess X τ u := fun X u =>
    funext fun ω => by rw [stoppedProcess, hθ]
  have hWs : ∀ u, StronglyMeasurable[𝓕 u] fun ω => W (θ u ω) ω := fun u => by
    rw [hstop W u]; exact stronglyAdapted_stoppedProcess_of_continuous hWa hWc hτ u
  have hVs : ∀ j u, StronglyMeasurable[𝓕 u] fun ω => V j (θ u ω) ω := fun j u => by
    rw [hstop (V j) u]; exact stronglyAdapted_stoppedProcess_of_continuous (hVa j) (hVc j) hτ u
  have hθs : ∀ u, StronglyMeasurable[𝓕 u] fun ω => ((θ u ω : ℝ≥0) : ℝ) := fun u => by
    rw [hstop (fun t _ => (t : ℝ)) u]
    exact stronglyAdapted_stoppedProcess_of_continuous (fun t => stronglyMeasurable_const)
      (fun ω => NNReal.continuous_coe) hτ u
  have hW0 : ∀ u, StronglyMeasurable[𝓕 u] fun ω => W 0 ω := fun u =>
    (hWa 0).mono (𝓕.mono (by simp : (0 : ℝ≥0) ≤ u))
  have hV0 : ∀ j u, StronglyMeasurable[𝓕 u] fun ω => V j 0 ω := fun j u =>
    ((hVa j) 0).mono (𝓕.mono (by simp : (0 : ℝ≥0) ≤ u))
  have hWm : ∀ u, Measurable[𝓕 u] fun ω => W (θ u ω) ω := fun u => (hWs u).measurable
  have hVm : ∀ j u, Measurable[𝓕 u] fun ω => V j (θ u ω) ω := fun j u => (hVs j u).measurable
  have hθm : ∀ u, Measurable[𝓕 u] fun ω => ((θ u ω : ℝ≥0) : ℝ) := fun u => (hθs u).measurable
  have hW0m : ∀ u, Measurable[𝓕 u] fun ω => W 0 ω := fun u => (hW0 u).measurable
  have hV0m : ∀ j u, Measurable[𝓕 u] fun ω => V j 0 ω := fun j u => (hV0 j u).measurable
  -- the martingale part along stopped times
  set mk : ℝ≥0 → Ω → ℝ := fun u ω => martValue ρ (W 0 ω) (fun j => V j 0 ω) (W (θ u ω) ω)
    (fun j => V j (θ u ω) ω) with hmk
  have hmk_meas : ∀ u, Measurable[𝓕 u] (mk u) := fun u => by
    simp only [hmk, martValue]
    exact ((hWm u).sub (hW0m u)).add (Measurable.const_mul (Finset.measurable_sum _
      fun j _ => ((hVm j u).sub (hV0m j u)).const_mul (ρ j)) _)
  set X := stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) τ with hX_def
  have hXeq : ∀ u ω, X u ω = mk u ω ^ 2 - κ * (θ u ω : ℝ) := fun u ω => by
    simp only [hX_def, stoppedProcess, hθ, martProc, hmk]
  have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u => by
    have : X u = fun ω => mk u ω ^ 2 - κ * (θ u ω : ℝ) := funext (hXeq u)
    rw [this]
    have := hmk_meas u
    have := hθm u
    fun_prop
  -- bounds
  have hb : ∀ u ω, |W (θ u ω) ω| ≤ K ∧ ∀ j, |V j (θ u ω) ω| ≤ K := fun u ω => hK ω _ (hθτ u ω)
  have hb0 : ∀ ω, |W 0 ω| ≤ K ∧ ∀ j, |V j 0 ω| ≤ K := fun ω => hK ω 0 (by simp)
  set CM : ℝ := 2 * K + (∑ j, |ρ j|) * K with hCM
  have hmk_bd : ∀ u ω, |mk u ω| ≤ CM := fun u ω =>
    abs_martValue_le ρ (hb0 ω).1 (hb0 ω).2 (hb u ω).1 (hb u ω).2
  have hX_bd : ∀ u ω, |X u ω| ≤ CM ^ 2 + |κ| * T := fun u ω => by
    rw [hXeq]
    have h1 : |mk u ω ^ 2| ≤ CM ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hmk_bd u ω) 2
    have h2 : |κ * (θ u ω : ℝ)| ≤ |κ| * T := by
      rw [abs_mul, NNReal.abs_eq]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hθT u ω) (abs_nonneg _)
    exact (abs_sub _ _).trans (by linarith)
  have hXint : ∀ u, Integrable (X u) P := fun u =>
    Integrable.of_bound ((hXm u).mono (𝓕.le u) le_rfl).aestronglyMeasurable (CM ^ 2 + |κ| * T)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hX_bd u ω)
  refine ⟨fun u => (hXm u).stronglyMeasurable, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hXint t)
    (fun A _ _ => (hXint s).integrableOn) (fun A hA _ => ?_)
    (hXm s).stronglyMeasurable.aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le s A hA
  -- the stopped coefficient processes
  set Qs := stoppedProcess (quadProc κ ρ W V) τ with hQs
  set Ns := stoppedProcess (driftProc ρ W V) τ with hNs
  have hQeq : ∀ u ω, Qs u ω
      = quadValue κ ρ (W (θ u ω) ω) (fun j => V j (θ u ω) ω) (θ u ω : ℝ) := fun u ω => by
    simp only [hQs, stoppedProcess, hθ, quadProc]
  have hNeq : ∀ u ω, Ns u ω = driftValue ρ (W (θ u ω) ω) (fun j => V j (θ u ω) ω) :=
    fun u ω => by simp only [hNs, stoppedProcess, hθ, driftProc]
  -- the summed defect along the `n`-th grid
  set g : ℕ → ℕ → ℝ≥0 := fun n k => gridPt s t n k with hg
  set D : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range (n + 1),
    cellDefect ρ (W (θ (g n k) ω) ω) (W (θ (g n (k + 1)) ω) ω) (fun j => V j (θ (g n k) ω) ω)
      (fun j => V j (θ (g n (k + 1)) ω) ω) ((θ (g n (k + 1)) ω : ℝ) - θ (g n k) ω) with hD
  -- the pathwise identity
  have hid : ∀ n ω, X t ω - X s ω = (Qs t ω - Qs s ω)
      + (∑ k ∈ Finset.range (n + 1), (mk (g n k) ω - W (θ (g n k) ω) ω)
          * (Ns (g n (k + 1)) ω - Ns (g n k) ω)) + D n ω := by
    intro n ω
    have h := sum_cell_identity κ ρ (W 0 ω) (fun j => V j 0 ω)
      (fun k => W (θ (g n k) ω) ω) (fun j k => V j (θ (g n k) ω) ω)
      (fun k => (θ (g n k) ω : ℝ)) (n + 1)
    simp only [hg, gridPt_zero, gridPt_last hst] at h
    rw [hXeq, hXeq, hQeq, hQeq]
    simp only [hmk, hD, hg]
    have hcross : ∑ k ∈ Finset.range (n + 1),
        (martValue ρ (W 0 ω) (fun j => V j 0 ω) (W (θ (gridPt s t n k) ω) ω)
            (fun j => V j (θ (gridPt s t n k) ω) ω) - W (θ (gridPt s t n k) ω) ω)
          * (Ns (gridPt s t n (k + 1)) ω - Ns (gridPt s t n k) ω)
        = ∑ k ∈ Finset.range (n + 1),
          2 * (martValue ρ (W 0 ω) (fun j => V j 0 ω) (W (θ (gridPt s t n k) ω) ω)
            (fun j => V j (θ (gridPt s t n k) ω) ω) - W (θ (gridPt s t n k) ω) ω)
          * (martValue ρ (W 0 ω) (fun j => V j 0 ω) (W (θ (gridPt s t n (k + 1)) ω) ω)
              (fun j => V j (θ (gridPt s t n (k + 1)) ω) ω)
            - martValue ρ (W 0 ω) (fun j => V j 0 ω) (W (θ (gridPt s t n k) ω) ω)
              (fun j => V j (θ (gridPt s t n k) ω) ω)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [martValue_sub_martValue, hNeq, hNeq]
      ring
    rw [hcross]
    linarith [h]
  -- measurability with respect to the ambient σ-algebra
  have hWM : ∀ u, Measurable fun ω => W (θ u ω) ω := fun u => (hWm u).mono (𝓕.le u) le_rfl
  have hVM : ∀ j u, Measurable fun ω => V j (θ u ω) ω := fun j u =>
    (hVm j u).mono (𝓕.le u) le_rfl
  have hθM : ∀ u, Measurable fun ω => ((θ u ω : ℝ≥0) : ℝ) := fun u => (hθm u).mono (𝓕.le u) le_rfl
  have hDm : ∀ n, Measurable (D n) := fun n => by
    simp only [hD]
    exact Finset.measurable_sum _ fun k _ => measurable_cellDefect ρ (hWM (g n k))
      (hWM (g n (k + 1))) (fun j => hVM j (g n k)) (fun j => hVM j (g n (k + 1)))
      ((hθM (g n (k + 1))).sub (hθM (g n k)))
  -- the bound on the summed defect
  have hdefT : ∀ L, L ≤ (T : ℝ) → defectBound ρ K L ≤ defectBound ρ K T := fun L hL => by
    simp only [defectBound]
    have : 0 ≤ ∑ j, |ρ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    nlinarith
  -- path conditions in real time
  have hwc : ∀ ω (a b : ℝ), ContinuousOn (fun x : ℝ => W x.toNNReal ω) (Icc a b) := fun ω a b =>
    ((hWc ω).comp continuous_real_toNNReal).continuousOn
  have hvc : ∀ ω j (a b : ℝ), ContinuousOn (fun x : ℝ => V j x.toNNReal ω) (Icc a b) :=
    fun ω j a b => ((hVc j ω).comp continuous_real_toNNReal).continuousOn
  have hvmono : ∀ ω j (a b : ℝ), MonotoneOn (fun x : ℝ => V j x.toNNReal ω) (Icc a b)
      ∨ AntitoneOn (fun x : ℝ => V j x.toNNReal ω) (Icc a b) := fun ω j a b => by
    rcases (hpath ω j).2.1 with h | h
    · exact Or.inl ((h.comp fun _ _ hxy => Real.toNNReal_le_toNNReal hxy).monotoneOn _)
    · exact Or.inr ((h.comp_monotone fun _ _ hxy => Real.toNNReal_le_toNNReal hxy).antitoneOn _)
  have hvderiv : ∀ ω j (a b : ℝ), 0 ≤ a → ∀ u ∈ Ioo a b,
      V j u.toNNReal ω ≠ W u.toNNReal ω →
      HasDerivAt (fun x : ℝ => V j x.toNNReal ω) (2 / (V j u.toNNReal ω - W u.toNNReal ω)) u :=
    fun ω j a b ha u hu hne => (hpath ω j).2.2.1 u (ha.trans_lt hu.1) hne
  have hvnull : ∀ ω j (a b : ℝ), 0 ≤ a →
      volume {u ∈ Icc a b | V j u.toNNReal ω = W u.toNNReal ω} = 0 := fun ω j a b ha =>
    measure_mono_null (t := {u : ℝ | 0 ≤ u ∧ V j u.toNNReal ω = W u.toNNReal ω})
      (fun u hu => ⟨ha.trans hu.1.1, hu.2⟩) (hpath ω j).2.2.2
  -- the partition in real time
  have hDconv : ∀ n ω, D n ω = ∑ k ∈ Finset.range (n + 1),
      cellDefect ρ ((fun x : ℝ => W x.toNNReal ω) (θ (g n k) ω))
        ((fun x : ℝ => W x.toNNReal ω) (θ (g n (k + 1)) ω))
        (fun j => (fun x : ℝ => V j x.toNNReal ω) (θ (g n k) ω))
        (fun j => (fun x : ℝ => V j x.toNNReal ω) (θ (g n (k + 1)) ω))
        ((θ (g n (k + 1)) ω : ℝ) - θ (g n k) ω) := fun n ω => by
    simp only [hD, Real.toNNReal_coe]
  have hpmono : ∀ n ω, Monotone fun k => ((θ (g n k) ω : ℝ≥0) : ℝ) := fun n ω k l hkl =>
    NNReal.coe_le_coe.2 (min_le_min_right _ (gridPt_mono s t n hkl))
  have hp0 : ∀ n ω, ((θ (g n 0) ω : ℝ≥0) : ℝ) = θ s ω := fun n ω => by
    simp only [hg, gridPt_zero]
  have hpn : ∀ n ω, ((θ (g n (n + 1)) ω : ℝ≥0) : ℝ) = θ t ω := fun n ω => by
    simp only [hg, gridPt_last hst]
  have hpmesh : ∀ n ω k, ((θ (g n (k + 1)) ω : ℝ≥0) : ℝ) - θ (g n k) ω
      ≤ (((t - s) / (n + 1) : ℝ≥0) : ℝ) := fun n ω k => by
    rw [← coe_gridPt_succ_sub s t n k]
    exact min_sub_min_le (gridPt_mono s t n (Nat.le_succ k))
  have hDbd : ∀ n ω, |D n ω| ≤ defectBound ρ K T := fun n ω => by
    rw [hDconv]
    have hK' : ∀ k ≤ n + 1, |(fun x : ℝ => W x.toNNReal ω) (θ (g n k) ω)| ≤ K ∧
        ∀ j, |(fun x : ℝ => V j x.toNNReal ω) (θ (g n k) ω)| ≤ K := fun k _ => by
      simp only [Real.toNNReal_coe]
      exact hb (g n k) ω
    have h := abs_sum_cellDefect_le (w := fun x : ℝ => W x.toNNReal ω)
      (v := fun j x => V j x.toNNReal ω) ρ (fun j => hvmono ω j (θ s ω) (θ t ω))
      (hpmono n ω) (hp0 n ω) (hpn n ω) hK'
    refine h.trans (hdefT _ ?_)
    have h1 : ((θ t ω : ℝ≥0) : ℝ) ≤ T := by exact_mod_cast hθT t ω
    have h2 : (0 : ℝ) ≤ θ s ω := NNReal.coe_nonneg _
    linarith
  -- the summed defect tends to `0` pathwise
  have hDlim : ∀ ω, Tendsto (fun n => D n ω) atTop (𝓝 0) := fun ω => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδD⟩ := exists_delta_abs_sum_cellDefect_le (w := fun x : ℝ => W x.toNNReal ω)
      (v := fun j x => V j x.toNNReal ω) (a := θ s ω) (b := θ t ω) ρ (hwc ω _ _)
      (fun j => hvc ω j _ _) (fun j => hvmono ω j _ _)
      (fun j => hvderiv ω j _ _ (NNReal.coe_nonneg _)) (fun j => hvnull ω j _ _ (NNReal.coe_nonneg _))
      (half_pos hε)
    have hmesh : Tendsto (fun n : ℕ => (((t - s) / (n + 1) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (((t - s : ℝ≥0) : ℝ))).comp
        (tendsto_add_atTop_nat 1)
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, NNReal.coe_div, Nat.cast_add, Nat.cast_one,
        NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hmesh).2 δ hδ)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, hDconv]
    exact (hδD (n + 1) _ (hpmono n ω) (hp0 n ω) (hpn n ω) fun k _ =>
      (hpmesh n ω k).trans_lt (hN n hn)).trans_lt (half_lt_self hε)
  have hDint : Tendsto (fun n => ∫ ω in A, D n ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := P.restrict A) (F := D)
      (f := fun _ => (0 : ℝ)) (fun _ => defectBound ρ K T)
      (fun n => (hDm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hDbd n ω)
      (Eventually.of_forall hDlim)
    simpa only [integral_zero] using h
  -- integrability of the pieces
  have hNint : ∀ u, Integrable (Ns u) P := hN.integrable
  have hQint : ∀ u, Integrable (Qs u) P := hQ.integrable
  have hDi : ∀ n, Integrable (D n) P := fun n =>
    Integrable.of_bound (hDm n).aestronglyMeasurable (defectBound ρ K T)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hDbd n ω)
  have hwt : ∀ u ω, |mk u ω - W (θ u ω) ω| ≤ CM + K := fun u ω =>
    (abs_sub _ _).trans (add_le_add (hmk_bd u ω) (hb u ω).1)
  have hcm : ∀ u, Measurable[𝓕 u] fun ω => mk u ω - W (θ u ω) ω := fun u =>
    (hmk_meas u).sub (hWm u)
  have hci : ∀ n k, Integrable (fun ω => (mk (g n k) ω - W (θ (g n k) ω) ω)
      * (Ns (g n (k + 1)) ω - Ns (g n k) ω)) P := fun n k =>
    ((hNint _).sub (hNint _)).bdd_mul ((hcm _).mono (𝓕.le _) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hwt _ ω)
  -- the martingale terms vanish on `A`
  have hc0 : ∀ n k, ∫ ω in A, (mk (g n k) ω - W (θ (g n k) ω) ω)
      * (Ns (g n (k + 1)) ω - Ns (g n k) ω) ∂P = 0 := fun n k => by
    rw [← integral_indicator hA']
    have hfun : A.indicator (fun ω => (mk (g n k) ω - W (θ (g n k) ω) ω)
        * (Ns (g n (k + 1)) ω - Ns (g n k) ω))
        = fun ω => A.indicator (fun ω => mk (g n k) ω - W (θ (g n k) ω) ω) ω
          * (Ns (g n (k + 1)) ω - Ns (g n k) ω) :=
      funext fun ω => Set.indicator_mul_left A _ _
    rw [hfun]
    refine integral_mul_sub_eq_zero hN (gridPt_mono s t n (Nat.le_succ k))
      ((hcm _).indicator (𝓕.mono (le_gridPt s t n k) A hA)).stronglyMeasurable
      (C := CM + K) fun ω => ?_
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]; exact hwt _ ω
    · rw [Set.indicator_of_notMem hω, abs_zero]
      exact (abs_nonneg _).trans (hwt (g n k) ω)
  have hQ0 : ∫ ω in A, (Qs t ω - Qs s ω) ∂P = 0 := by
    rw [integral_sub (hQint t).integrableOn (hQint s).integrableOn, hQ.setIntegral_eq hst hA,
      sub_self]
  -- conclusion
  have heq : ∀ n, ∫ ω in A, (X t ω - X s ω) ∂P = ∫ ω in A, D n ω ∂P := fun n => by
    rw [show (fun ω => X t ω - X s ω) = fun ω => (Qs t ω - Qs s ω)
        + (∑ k ∈ Finset.range (n + 1), (mk (g n k) ω - W (θ (g n k) ω) ω)
          * (Ns (g n (k + 1)) ω - Ns (g n k) ω)) + D n ω from funext (hid n)]
    have hI1 : IntegrableOn (fun ω => Qs t ω - Qs s ω) A P := ((hQint t).sub (hQint s)).integrableOn
    have hI2 : IntegrableOn (fun ω => ∑ k ∈ Finset.range (n + 1), (mk (g n k) ω - W (θ (g n k) ω) ω)
        * (Ns (g n (k + 1)) ω - Ns (g n k) ω)) A P :=
      (integrable_finsetSum _ fun k _ => hci n k).integrableOn
    have hI12 : IntegrableOn (fun ω => (Qs t ω - Qs s ω) + ∑ k ∈ Finset.range (n + 1),
        (mk (g n k) ω - W (θ (g n k) ω) ω) * (Ns (g n (k + 1)) ω - Ns (g n k) ω)) A P :=
      hI1.add hI2
    rw [integral_add hI12 (hDi n).integrableOn, integral_add hI1 hI2,
      integral_finsetSum _ fun k _ => (hci n k).integrableOn, hQ0]
    simp only [hc0, Finset.sum_const_zero, zero_add]
  have hzero : ∫ ω in A, (X t ω - X s ω) ∂P = 0 := by
    have hconst : Tendsto (fun _ : ℕ => ∫ ω in A, (X t ω - X s ω) ∂P) atTop
        (𝓝 (∫ ω in A, (X t ω - X s ω) ∂P)) := tendsto_const_nhds
    exact tendsto_nhds_unique hconst (hDint.congr fun n => (heq n).symm)
  rw [integral_sub (hXint t).integrableOn (hXint s).integrableOn, sub_eq_zero] at hzero
  exact hzero.symm

/-- `M^τ` is a martingale when `N^τ` is: `M^τ = ½ (N^τ − N₀)`. -/
theorem martingale_stoppedProcess_martProc (hτT : ∀ ω, τ ω ≤ T)
    (hN : Martingale (stoppedProcess (driftProc ρ W V) τ) 𝓕 P) :
    Martingale (stoppedProcess (martProc ρ W V) τ) 𝓕 P := by
  have hθ0 : ∀ ω, (min ((0 : ℝ≥0) : WithTop ℝ≥0) (τ ω)).untopA = 0 := fun ω => by
    rw [untopA_min_eq hτT]; exact min_eq_left (by simp)
  have h0 : ∀ ω, stoppedProcess (driftProc ρ W V) τ 0 ω = driftValue ρ (W 0 ω) (fun j => V j 0 ω) :=
    fun ω => by simp only [stoppedProcess, hθ0, driftProc]
  have heq : stoppedProcess (martProc ρ W V) τ
      = (1 / 2 : ℝ) • (stoppedProcess (driftProc ρ W V) τ
        - fun _ => stoppedProcess (driftProc ρ W V) τ 0) := by
    funext u ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h0]
    simp only [stoppedProcess, martProc, driftProc]
    have h := martValue_sub_martValue ρ (W 0 ω) (fun j => V j 0 ω) (W 0 ω)
      (W (min (u : WithTop ℝ≥0) (τ ω)).untopA ω) (fun j => V j 0 ω)
      (fun j => V j (min (u : WithTop ℝ≥0) (τ ω)).untopA ω)
    have h00 : martValue ρ (W 0 ω) (fun j => V j 0 ω) (W 0 ω) (fun j => V j 0 ω) = 0 := by
      simp [martValue]
    rw [h00, sub_zero] at h
    exact h
  rw [heq]
  refine (hN.sub (martingale_const_fun 𝓕 P ((hN.1 0).mono (𝓕.mono (le_refl 0)))
    (hN.integrable 0))).smul _

end Core

/-! ### Localization and Lévy's characterization -/

section Levy

variable [IsProbabilityMeasure P] {ρ : ι → ℝ} {κ : ℝ} {W : ℝ≥0 → Ω → ℝ}
  {V : ι → ℝ≥0 → Ω → ℝ}

/-- The localizing quantity `Z = |W| + ∑ⱼ |Vʲ|`. -/
def absSum (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => |W t ω| + ∑ j, |V j t ω|

/-- The localizing times `min T (exitTime Z N)`, `Z = |W| + ∑ⱼ |Vʲ|`. -/
def locTime (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) (T N : ℕ) : Ω → WithTop ℝ≥0 :=
  fun ω => min (((T : ℝ≥0)) : WithTop ℝ≥0) (MathFin.exitTime (absSum W V) N ω)

omit [IsProbabilityMeasure P] in
lemma continuous_absSum (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) (ω : Ω) : Continuous fun t => absSum W V t ω :=
  (continuous_abs.comp (hWc ω)).add (continuous_finsetSum _ fun j _ =>
    continuous_abs.comp (hVc j ω))

omit [IsProbabilityMeasure P] in
lemma measurable_absSum (hWa : StronglyAdapted 𝓕 W) (hVa : ∀ j, StronglyAdapted 𝓕 (V j))
    (t : ℝ≥0) : Measurable[𝓕 t] (absSum W V t) := by
  show Measurable[𝓕 t] (fun ω => |W t ω| + ∑ j, |V j t ω|)
  have h1 := (hWa t).measurable
  have h2 := fun j => ((hVa j) t).measurable
  fun_prop

omit [IsProbabilityMeasure P] in
lemma isStoppingTime_locTime (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVa : ∀ j, StronglyAdapted 𝓕 (V j)) (T N : ℕ) : IsStoppingTime 𝓕 (locTime W V T N) :=
  (isStoppingTime_const 𝓕 _).min (MathFin.isStoppingTime_exitTime_of_measurable
    (measurable_absSum hWa hVa) (continuous_absSum hWc hVc) N)

omit [IsProbabilityMeasure P] in
lemma locTime_le (T N : ℕ) (ω : Ω) : locTime W V T N ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) :=
  min_le_left _ _

omit [IsProbabilityMeasure P] in
/-- Up to the localizing time the coordinates are bounded by `N + |w₀| + ∑ⱼ |xⱼ|`. -/
lemma abs_le_of_le_locTime {w₀ : ℝ} {x : ι → ℝ} (hW0 : ∀ ω, W 0 ω = w₀)
    (hV0 : ∀ j ω, V j 0 ω = x j) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) {T N : ℕ} {ω : Ω} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ locTime W V T N ω) :
    |W t ω| ≤ N + |w₀| + ∑ j, |x j| ∧ ∀ j, |V j t ω| ≤ N + |w₀| + ∑ j, |x j| := by
  have hx : 0 ≤ ∑ j, |x j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hle : ∀ j, |V j t ω| ≤ absSum W V t ω := fun j => by
    have := Finset.single_le_sum (f := fun j => |V j t ω|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    simp only [absSum]
    linarith [abs_nonneg (W t ω)]
  have hleW : |W t ω| ≤ absSum W V t ω := by
    simp only [absSum]
    linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (V j t ω)]
  by_cases hpos : ⊥ < MathFin.exitTime (absSum W V) N ω
  · have hZ := MathFin.abs_le_of_le_exitTime (continuous_absSum hWc hVc) hpos
      (ht.trans (min_le_right _ _))
    have hZ' : absSum W V t ω ≤ N := (le_abs_self _).trans hZ
    exact ⟨by linarith [abs_nonneg w₀], fun j => by linarith [hle j, abs_nonneg w₀]⟩
  · have h0 : MathFin.exitTime (absSum W V) N ω = ⊥ := not_bot_lt_iff.1 hpos
    have ht0 : t = 0 := by
      have h1 : (t : WithTop ℝ≥0) ≤ ((⊥ : ℝ≥0) : WithTop ℝ≥0) := by
        rw [WithTop.coe_bot]; exact ht.trans ((min_le_right _ _).trans h0.le)
      exact le_bot_iff.1 (WithTop.coe_le_coe.1 h1)
    subst ht0
    refine ⟨by rw [hW0]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)], fun j => ?_⟩
    rw [hV0]
    have := Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), abs_nonneg w₀]

omit [IsProbabilityMeasure P] [Fintype ι] in
/-- Localizing a process that vanishes at time `0` needs no indicator. -/
lemma stoppedProcess_indicator_eq_of_zero {X : ℝ≥0 → Ω → ℝ} (hX0 : ∀ ω, X 0 ω = 0)
    (τ : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (X i)) τ = stoppedProcess X τ := by
  funext i ω
  simp only [stoppedProcess]
  by_cases h : ⊥ < τ ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from h)]
  · have h0 : τ ω = ⊥ := not_bot_lt_iff.1 h
    rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from h), h0, min_eq_right bot_le]
    exact (hX0 ω).symm

omit [IsProbabilityMeasure P] [Fintype ι] in
/-- A stopped continuous process with a finite stopping time has continuous paths. -/
lemma continuous_stoppedProcess {X : ℝ≥0 → Ω → ℝ} (hXc : ∀ ω, Continuous fun t => X t ω)
    {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    Continuous fun t => stoppedProcess X τ t ω := by
  have : (fun t => stoppedProcess X τ t ω) = fun t => X (min t (τ ω).untopA) ω := by
    funext t; simp only [stoppedProcess, untopA_min_eq hτT]
  rw [this]
  exact (hXc ω).comp (continuous_id.min continuous_const)

omit [IsProbabilityMeasure P] in
lemma continuous_martProc (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) (ω : Ω) :
    Continuous fun t => martProc ρ W V t ω := by
  simp only [martProc, martValue]
  have h1 := hWc ω
  have h2 := fun j => hVc j ω
  fun_prop

omit [IsProbabilityMeasure P] in
lemma stronglyAdapted_martProc (hWa : StronglyAdapted 𝓕 W) (hVa : ∀ j, StronglyAdapted 𝓕 (V j)) :
    StronglyAdapted 𝓕 (martProc ρ W V) := fun t => by
  have h1 : Measurable[𝓕 t] (W t) := (hWa t).measurable
  have h2 : Measurable[𝓕 t] (W 0) := ((hWa 0).mono (𝓕.mono (by simp))).measurable
  have h3 : ∀ j, Measurable[𝓕 t] (V j t) := fun j => ((hVa j) t).measurable
  have h4 : ∀ j, Measurable[𝓕 t] (V j 0) := fun j => (((hVa j) 0).mono (𝓕.mono (by simp))).measurable
  have : Measurable[𝓕 t] (martProc ρ W V t) := by
    show Measurable[𝓕 t] fun ω => W t ω - W 0 ω + 1 / 2 * ∑ j, ρ j * (V j t ω - V j 0 ω)
    fun_prop
  exact this.stronglyMeasurable

/-- **Lévy step of Theorem 2.4.** Let `W` and the force points `Vʲ` be continuous, adapted, with
deterministic initial values and the force-path conditions. If the Laurent-coefficient processes
`N = 2W + ∑ⱼ ρⱼ Vʲ` and `Q = W² + ½ ∑ⱼ ρⱼ (Vʲ)² − (2 ∑ⱼ ρⱼ + κ) t` stopped at every localizing
time `min T (exitTime Z N)` are martingales, then `B = M / √κ`,
`M = W − W₀ + ½ ∑ⱼ ρⱼ (Vʲ − Vʲ₀)`, is an `𝓕`-Brownian motion. -/
theorem isFilteredBrownianReal_martProc_div_sqrt (hκ : 0 < κ) {w₀ : ℝ} {x : ι → ℝ}
    (hW0 : ∀ ω, W 0 ω = w₀) (hV0 : ∀ j ω, V j 0 ω = x j)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVa : ∀ j, StronglyAdapted 𝓕 (V j))
    (hpath : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => V j t ω))
    (hN : ∀ T N : ℕ, Martingale (stoppedProcess (driftProc ρ W V) (locTime W V T N)) 𝓕 P)
    (hQ : ∀ T N : ℕ, Martingale (stoppedProcess (quadProc κ ρ W V) (locTime W V T N)) 𝓕 P) :
    IsFilteredBrownianReal 𝓕 (fun t ω => martProc ρ W V t ω / Real.sqrt κ) P := by
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => (hpath ω j).1
  set σ : ℕ → Ω → WithTop ℝ≥0 := fun n => locTime W V n n with hσ_def
  have hσst : ∀ n, IsStoppingTime 𝓕 (σ n) := fun n => isStoppingTime_locTime hWc hVc hWa hVa n n
  have hσT : ∀ n ω, σ n ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := fun n ω => locTime_le n n ω
  have hZc := continuous_absSum hWc hVc
  have hσ : IsLocalizingSequence 𝓕 σ P := {
    isStoppingTime := hσst
    mono := ae_of_all _ fun ω n m hnm => min_le_min (by exact_mod_cast hnm)
      (MathFin.exitTime_mono hZc hnm ω)
    tendsto_top := ae_of_all _ fun ω => by
      rw [WithTop.tendsto_nhds_top_iff _]
      intro c
      have h1 := (WithTop.tendsto_nhds_top_iff _).1 (MathFin.exitTime_tendsto_top hZc ω) c
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt c
      filter_upwards [h1, eventually_gt_atTop N₀] with n hn hn'
      refine lt_min ?_ hn
      exact WithTop.coe_lt_coe.2 (hN₀.trans (by exact_mod_cast hn')) }
  -- the two martingales at each localizing time
  have hMsq : ∀ n, Martingale (stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) (σ n))
      𝓕 P := fun n =>
    martingale_stoppedProcess_martProc_sq_sub (hσst n) (hσT n)
      (fun ω t ht => abs_le_of_le_locTime hW0 hV0 hWc hVc ht) hWc hWa hVa hpath (hN n n)
      (hQ n n)
  have hM : ∀ n, Martingale (stoppedProcess (martProc ρ W V) (σ n)) 𝓕 P := fun n =>
    martingale_stoppedProcess_martProc (hσT n) (hN n n)
  -- the normalized processes
  set B : ℝ≥0 → Ω → ℝ := fun t ω => martProc ρ W V t ω / Real.sqrt κ with hB_def
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hsqrt : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hB0 : ∀ ω, B 0 ω = 0 := fun ω => by simp [hB_def, martProc, martValue]
  have hBc : ∀ ω, Continuous fun t => B t ω := fun ω =>
    (continuous_martProc hWc hVc ω).div_const _
  have hBa : StronglyAdapted 𝓕 B := fun t =>
    ((stronglyAdapted_martProc (ρ := ρ) hWa hVa t).measurable.div_const _).stronglyMeasurable
  have hB2_0 : ∀ ω, B 0 ω ^ 2 - ((0 : ℝ≥0) : ℝ) = 0 := fun ω => by simp [hB0]
  have hBloc : IsLocalMartingale B 𝓕 P := by
    refine ⟨σ, hσ, fun n => ?_⟩
    rw [stoppedProcess_indicator_eq_of_zero hB0]
    refine ⟨?_, fun ω => (continuous_stoppedProcess hBc (hσT n) ω).isCadlag⟩
    have heq : stoppedProcess B (σ n) = (Real.sqrt κ)⁻¹ • stoppedProcess (martProc ρ W V) (σ n) := by
      funext t ω
      simp only [hB_def, stoppedProcess, Pi.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
    rw [heq]
    exact (hM n).smul _
  have hB2loc : IsLocalMartingale (fun t ω => B t ω ^ 2 - (t : ℝ)) 𝓕 P := by
    refine ⟨σ, hσ, fun n => ?_⟩
    rw [stoppedProcess_indicator_eq_of_zero hB2_0]
    refine ⟨?_, fun ω => (continuous_stoppedProcess (X := fun t ω => B t ω ^ 2 - (t : ℝ))
      (fun ω => ((hBc ω).pow 2).sub NNReal.continuous_coe) (hσT n) ω).isCadlag⟩
    have heq : stoppedProcess (fun t ω => B t ω ^ 2 - (t : ℝ)) (σ n)
        = κ⁻¹ • stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) (σ n) := by
      funext t ω
      simp only [hB_def, stoppedProcess, Pi.smul_apply, smul_eq_mul]
      rw [div_pow, hsq]
      field_simp
    rw [heq]
    exact (hMsq n).smul _
  have hpre := MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  have hbm := MathFin.LevyCharacterization.isBrownianReal_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  exact ⟨hbm, hBa.adapted, fun s t hst => hpre.indep s t hst⟩

end Levy

end MartChar

end InteractingSLE
