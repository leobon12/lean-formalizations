/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField3Brown
import MathFin.Probability.Brownian.LevyCharacterization

/-!
# Whole-field identification C.2: the stopped noise in the germ filtration, without localization

Source: `source/external/AstraIG1/ig1_followup_proofs.txt` (ruling R38), Part C.2 (L1497–1530): "The quadratic variation
is the pathwise quantity `t ∧ S`. Lévy's characterization, followed by localization over the announcing times and capacity
bounds, proves that `B` is Brownian in the enlarged germ filtration up to `T*`." The additional note
(`ig1_additional_proofs.txt`, ruling R39, §7.4, Aux. lemma 47, L3070–3100): "Localization removes the bounds. The quadratic
variation is `t`, and the usual Brownian characterization applies."

`WholeField.martingale_stoppedNoise_germ` (PROVE-WHOLEFIELD3) gives a version `Y` of `B_{·∧S}` that is a martingale of the
stopped germ filtration `𝒢`, together with *localized* brackets: `Y_{·∧ρₙ}² − (·∧ρₙ)` are `𝒢`-martingales along driving
stops `ρₙ ≤ S` with `ρₙ = S` eventually. Here the localization is removed:

* `martingale_exp_sq_of_localized` (abstract): a `𝒢`-martingale `Y` with continuous paths, `Y₀ = 0`, and a slow clock `A`
  such that the localized brackets `(Y^{ρₙ})² − A^{ρₙ}` are `𝒢`-martingales with `Y^{ρₙ} = Y`, `A^{ρₙ} = A` eventually,
  has `exp(aY − a²A/2)` and `Y² − A` as `𝒢`-martingales. Proof: stop further at the exit times of `|Y|` from
  `(−n−1, n+1)` (bounded martingale on a slow clock: MathFin's cell-by-cell exponential martingale), then pass to the limit
  with the `L²` bounds `E[exp(aY − a²A/2)²] ≤ e^{a²t}` and `E[(Y² − A)²] ≤ 96 e^{t/2} + 2t²` (from `x⁴ ≤ 24(eˣ + e⁻ˣ)`).
* **`martingale_stoppedNoise_germ_exp`**: for the frozen coupling, `B_{·∧S}` has a version `Y`, continuous everywhere and
  `𝒢`-adapted, such that `Y² − (·∧S)` and `exp(aY − a²(·∧S)/2)` (every real `a`) are `𝒢`-martingales: the stopped noise is
  a stopped Brownian motion of the germ filtration (Lévy's characterization in exponential form).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace WholeField

open QuantumZipper Ito Coupling MathFin.LevyQuadraticSums

section Clock

variable {Ω : Type*}

/-- A slow clock stopped at a random time is a slow clock. -/
theorem isSlowClock_stoppedProcess_of {A : ℝ≥0 → Ω → ℝ} (hA : IsSlowClock A) (ρ : Ω → WithTop ℝ≥0) :
    IsSlowClock (stoppedProcess A ρ) where
  zero ω := by
    change A (min ((0 : ℝ≥0) : WithTop ℝ≥0) (ρ ω)).untopA ω = 0
    rw [MathFin.untopA_min_zero, hA.zero]
  sub_nonneg p q hpq ω := by
    have h := (MathFin.LevyCharacterization.stoppedClock_sub (ρ ω) hpq).1
    exact hA.sub_nonneg (NNReal.coe_le_coe.1 (sub_nonneg.1 h)) ω
  sub_le p q hpq ω := by
    have h := MathFin.LevyCharacterization.stoppedClock_sub (ρ ω) hpq
    exact (hA.sub_le (NNReal.coe_le_coe.1 (sub_nonneg.1 h.1)) ω).trans h.2

/-- A slow clock has continuous paths (it is `1`-Lipschitz). -/
theorem continuous_of_isSlowClock {A : ℝ≥0 → Ω → ℝ} (hA : IsSlowClock A) (ω : Ω) :
    Continuous fun t => A t ω := by
  refine (LipschitzWith.of_dist_le_mul fun p q => ?_ : LipschitzWith 1 fun t => A t ω).continuous
  rw [Real.dist_eq, NNReal.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total p q with hpq | hpq
  · have h1 := hA.sub_nonneg hpq ω
    have h2 := hA.sub_le hpq ω
    have h3 : (p : ℝ) ≤ q := hpq
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 := hA.sub_nonneg hpq ω
    have h2 := hA.sub_le hpq ω
    have h3 : (q : ℝ) ≤ p := hpq
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

end Clock

/-- `x⁴ ≤ 24 (eˣ + e⁻ˣ)` (the fourth Taylor term of `e^{|x|}`). -/
theorem pow_four_le_exp_add_exp (x : ℝ) : x ^ 4 ≤ 24 * (Real.exp x + Real.exp (-x)) := by
  have h4 : ∀ y : ℝ, 0 ≤ y → y ^ 4 ≤ 24 * Real.exp y := fun y hy => by
    have h := Real.pow_div_factorial_le_exp y hy 4
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h
    linarith
  rcases le_total 0 x with hx | hx
  · have h1 := h4 x hx
    have h2 := Real.exp_pos (-x)
    linarith
  · have h1 := h4 (-x) (by linarith)
    have h2 := Real.exp_pos x
    have e : (-x) ^ 4 = x ^ 4 := by ring
    rw [e] at h1
    linarith

/-- The pointwise bound used for the bracket: for `0 ≤ c ≤ t`,
`(m² − c)² ≤ 48 e^{t/2} (e^{m − c/2} + e^{−m − c/2}) + 2t²`. -/
theorem sq_sq_sub_le_exp {m c t : ℝ} (hc0 : 0 ≤ c) (hct : c ≤ t) :
    (m ^ 2 - c) ^ 2 ≤ 48 * Real.exp (t / 2) *
      (Real.exp (1 * m - 1 ^ 2 * c / 2) + Real.exp ((-1) * m - (-1) ^ 2 * c / 2)) + 2 * t ^ 2 := by
  have h1 : (m ^ 2 - c) ^ 2 ≤ 2 * m ^ 4 + 2 * c ^ 2 := by nlinarith [sq_nonneg (m ^ 2 + c)]
  have h2 : c ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hc0 hct 2
  have h3 := pow_four_le_exp_add_exp m
  have hp : Real.exp m = Real.exp (1 * m - 1 ^ 2 * c / 2) * Real.exp (c / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hn : Real.exp (-m) = Real.exp ((-1) * m - (-1) ^ 2 * c / 2) * Real.exp (c / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hct2 : Real.exp (c / 2) ≤ Real.exp (t / 2) := Real.exp_le_exp.2 (by linarith)
  have hA := Real.exp_pos (1 * m - 1 ^ 2 * c / 2)
  have hB := Real.exp_pos ((-1) * m - (-1) ^ 2 * c / 2)
  have h4 : Real.exp m + Real.exp (-m) ≤ Real.exp (t / 2) *
      (Real.exp (1 * m - 1 ^ 2 * c / 2) + Real.exp ((-1) * m - (-1) ^ 2 * c / 2)) := by
    rw [hp, hn]
    nlinarith [mul_le_mul_of_nonneg_left hct2 hA.le, mul_le_mul_of_nonneg_left hct2 hB.le]
  nlinarith

section Abstract

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒢 : Filtration ℝ≥0 mΩ}

/-- **Removing the localization of a bracket (exponential and quadratic forms).** Let `Y` be a `𝒢`-martingale with
continuous paths and `Y₀ = 0`, `A` a `𝒢`-adapted slow clock, and `ρₙ` stopping times of `𝒢` such that
`(Y^{ρₙ})² − A^{ρₙ}` are `𝒢`-martingales and, almost surely, at every time `Y^{ρₙ} = Y` and `A^{ρₙ} = A` eventually.
Then `exp(aY − a²A/2)` (every real `a`) and `Y² − A` are `𝒢`-martingales. -/
theorem martingale_exp_sq_of_localized {Y A : ℝ≥0 → Ω → ℝ} (hY : Martingale Y 𝒢 P)
    (hYc : ∀ ω, Continuous fun t => Y t ω) (hY0 : ∀ ω, Y 0 ω = 0) (hA : IsSlowClock A)
    (hAa : StronglyAdapted 𝒢 A) {ρ : ℕ → Ω → WithTop ℝ≥0} (hρ : ∀ n, IsStoppingTime 𝒢 (ρ n))
    (hloc : ∀ n, Martingale (fun t ω => stoppedProcess Y (ρ n) t ω ^ 2 - stoppedProcess A (ρ n) t ω) 𝒢 P)
    (hlim : ∀ᵐ ω ∂P, ∀ t, ∀ᶠ n in atTop,
      stoppedProcess Y (ρ n) t ω = Y t ω ∧ stoppedProcess A (ρ n) t ω = A t ω) :
    (∀ a : ℝ, Martingale (fun t ω => Real.exp (a * Y t ω - a ^ 2 * A t ω / 2)) 𝒢 P) ∧
      Martingale (fun t ω => Y t ω ^ 2 - A t ω) 𝒢 P := by
  -- the exit times and the doubly stopped processes
  set e : ℕ → Ω → WithTop ℝ≥0 := fun n => MathFin.exitTime Y (n + 1) with he
  have he_st : ∀ n, IsStoppingTime 𝒢 (e n) := fun n =>
    MathFin.isStoppingTime_exitTime_of_measurable (fun t => (hY.stronglyAdapted t).measurable) hYc (n + 1)
  set σ : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (e n ω) (ρ n ω) with hσdef
  have hσ : ∀ n, IsStoppingTime 𝒢 (σ n) := fun n => (he_st n).min (hρ n)
  set M : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess Y (σ n) with hMdef
  set C : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess A (σ n) with hCdef
  have hrc : ∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t := fun ω t => (hYc ω).continuousWithinAt
  have hM : ∀ n, Martingale (M n) 𝒢 P := fun n => Martingale.stoppedProcess_of_rightContinuous hY hrc (hσ n)
  have hMc : ∀ n ω, Continuous fun t => M n t ω := fun n ω =>
    MathFin.continuous_stoppedProcess hYc (σ n) ω
  have hMb : ∀ n t ω, |M n t ω| ≤ ((n + 1 : ℕ) : ℝ) := by
    intro n t ω
    refine MathFin.abs_le_of_le_exitTime hYc (MathFin.LevyCharacterization.bot_lt_exitTime hYc hY0 n ω) ?_
    rw [MathFin.coe_untopA_min]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hC : ∀ n, IsSlowClock (C n) := fun n => isSlowClock_stoppedProcess_of hA (σ n)
  have hAc := continuous_of_isSlowClock hA
  have hMC : ∀ n, Martingale (fun t ω => M n t ω ^ 2 - C n t ω) 𝒢 P := by
    intro n
    have hZc : ∀ ω t, ContinuousWithinAt
        (fun s => stoppedProcess Y (ρ n) s ω ^ 2 - stoppedProcess A (ρ n) s ω) (Ici t) t := fun ω t =>
      (((MathFin.continuous_stoppedProcess hYc (ρ n) ω).pow 2).sub
        (MathFin.continuous_stoppedProcess hAc (ρ n) ω)).continuousWithinAt
    have h := Martingale.stoppedProcess_of_rightContinuous (hloc n) hZc (he_st n)
    have e1 : M n = stoppedProcess (stoppedProcess Y (ρ n)) (e n) := by
      rw [stoppedProcess_stoppedProcess']
    have e2 : C n = stoppedProcess (stoppedProcess A (ρ n)) (e n) := by
      rw [stoppedProcess_stoppedProcess']
    rw [e1, e2]
    exact h
  -- the exponential martingales of the doubly stopped processes
  set E : ℕ → ℝ → ℝ≥0 → Ω → ℝ := fun n a t ω => Real.exp (a * M n t ω - a ^ 2 * C n t ω / 2) with hEdef
  have hE : ∀ n a, Martingale (E n a) 𝒢 P := fun n a =>
    MathFin.LevyExpMartingale.martingale_exp (hC n) (hM n) (hMC n) (hMb n) (hMc n) a
  have hM0 : ∀ n ω, M n 0 ω = 0 := fun n ω => by
    change Y (min ((0 : ℝ≥0) : WithTop ℝ≥0) (σ n ω)).untopA ω = 0
    rw [MathFin.untopA_min_zero, hY0]
  have hE1 : ∀ n a t, ∫ ω, E n a t ω ∂P = 1 := by
    intro n a t
    have h := (hE n a).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    simp [hEdef, hM0, (hC n).zero]
  have hEm : ∀ n a t, Measurable (E n a t) := fun n a t =>
    ((hE n a).stronglyAdapted t).measurable.mono (𝒢.le t) le_rfl
  have hEb : ∀ n a t ω, |E n a t ω| ≤ Real.exp (|a| * ((n + 1 : ℕ) : ℝ)) := fun n a t ω => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact MathFin.LevyExpMartingale.exp_le_exp_abs_mul (hC n) (hMb n) a t ω
  have hEL2 : ∀ n a t, MemLp (E n a t) 2 P := fun n a t =>
    MemLp.of_bound (hEm n a t).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hEb n a t ω)
  have hEsq : ∀ n a t, ∫ ω, E n a t ω ^ 2 ∂P ≤ Real.exp (a ^ 2 * t) := by
    intro n a t
    calc ∫ ω, E n a t ω ^ 2 ∂P ≤ ∫ ω, Real.exp (a ^ 2 * t) * E n (2 * a) t ω ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
            (((hE n (2 * a)).integrable t).const_mul _) (Eventually.of_forall fun ω => ?_)
          simp only [hEdef]
          rw [sq, ← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have := (hC n).apply_le t ω
          nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg a)]
      _ = Real.exp (a ^ 2 * t) := by rw [integral_const_mul, hE1, mul_one]
  -- eventual agreement with the limit
  have hev : ∀ᵐ ω ∂P, ∀ t, ∀ᶠ n in atTop, M n t ω = Y t ω ∧ C n t ω = A t ω := by
    filter_upwards [hlim] with ω hω t
    have hexit : ∀ᶠ n : ℕ in atTop, (t : WithTop ℝ≥0) < e n ω :=
      (WithTop.tendsto_nhds_top_iff _).1
        ((MathFin.exitTime_tendsto_top hYc ω).comp (tendsto_add_atTop_nat 1)) t
    filter_upwards [hω t, hexit] with n hn hne
    have hmin : min (t : WithTop ℝ≥0) (σ n ω) = min (t : WithTop ℝ≥0) (ρ n ω) := by
      simp only [hσdef]
      rw [← min_assoc, min_eq_left hne.le]
    refine ⟨?_, ?_⟩
    · rw [← hn.1]
      change Y (min (t : WithTop ℝ≥0) (σ n ω)).untopA ω = Y (min (t : WithTop ℝ≥0) (ρ n ω)).untopA ω
      rw [hmin]
    · rw [← hn.2]
      change A (min (t : WithTop ℝ≥0) (σ n ω)).untopA ω = A (min (t : WithTop ℝ≥0) (ρ n ω)).untopA ω
      rw [hmin]
  refine ⟨fun a => ?_, ?_⟩
  · -- the exponential martingale
    have hl : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => E n a t ω) atTop
        (𝓝 (Real.exp (a * Y t ω - a ^ 2 * A t ω / 2))) := by
      intro t
      filter_upwards [hev] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω t] with n hn
      simp only [hEdef, hn.1, hn.2]
    refine Sec7.martingale_of_tendsto_of_sq_bound (fun n => hE n a) (fun n t => hEL2 n a t)
      (fun t => ⟨_, fun n => hEsq n a t⟩) hl (fun t => ?_) (fun t => ?_)
    · exact ((((hY.stronglyAdapted t).measurable.const_mul a).sub
        (((hAa t).measurable.const_mul (a ^ 2)).div_const 2)).exp).stronglyMeasurable
    · exact (MathFin.memLp_two_of_subseq_ae_of_sq_bound (fun n => hEL2 n a t) (fun n => hEm n a t)
        (fun n => hEsq n a t) ⟨id, hl t⟩).integrable one_le_two
  · -- the bracket
    set Q : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω => M n t ω ^ 2 - C n t ω with hQdef
    have hQm : ∀ n t, Measurable (Q n t) := fun n t =>
      ((hMC n).stronglyAdapted t).measurable.mono (𝒢.le t) le_rfl
    have hQb : ∀ n t ω, |Q n t ω| ≤ ((n + 1 : ℕ) : ℝ) ^ 2 + t := fun n t ω => by
      have h1 := hMb n t ω
      have h2 := (hC n).apply_nonneg t ω
      have h3 := (hC n).apply_le t ω
      have h4 : M n t ω ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
      simp only [hQdef]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (M n t ω)]
    have hQL2 : ∀ n t, MemLp (Q n t) 2 P := fun n t =>
      MemLp.of_bound (hQm n t).aestronglyMeasurable _
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hQb n t ω)
    have hQsq : ∀ n t, ∫ ω, Q n t ω ^ 2 ∂P ≤ 96 * Real.exp ((t : ℝ) / 2) + 2 * (t : ℝ) ^ 2 := by
      intro n t
      have hi1 := (hE n 1).integrable t
      have hi2 := (hE n (-1)).integrable t
      calc ∫ ω, Q n t ω ^ 2 ∂P ≤ ∫ ω, (48 * Real.exp ((t : ℝ) / 2) * (E n 1 t ω + E n (-1) t ω) +
            2 * (t : ℝ) ^ 2) ∂P := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
              (((hi1.add hi2).const_mul _).add (integrable_const _)) (Eventually.of_forall fun ω => ?_)
            exact sq_sq_sub_le_exp ((hC n).apply_nonneg t ω) ((hC n).apply_le t ω)
        _ = 96 * Real.exp ((t : ℝ) / 2) + 2 * (t : ℝ) ^ 2 := by
            have hi3 : Integrable (fun ω => 48 * Real.exp ((t : ℝ) / 2) * (E n 1 t ω + E n (-1) t ω)) P :=
              (hi1.add hi2).const_mul _
            rw [integral_add hi3 (integrable_const _), integral_const_mul, integral_add hi1 hi2, hE1, hE1]
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
            ring
    have hl : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Q n t ω) atTop (𝓝 (Y t ω ^ 2 - A t ω)) := by
      intro t
      filter_upwards [hev] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω t] with n hn
      simp only [hQdef, hn.1, hn.2]
    refine Sec7.martingale_of_tendsto_of_sq_bound hMC hQL2 (fun t => ⟨_, fun n => hQsq n t⟩) hl
      (fun t => ?_) (fun t => ?_)
    · exact ((((hY.stronglyAdapted t).measurable.pow_const 2).sub (hAa t).measurable)).stronglyMeasurable
    · exact (MathFin.memLp_two_of_subseq_ae_of_sq_bound (fun n => hQL2 n t) (fun n => hQm n t)
        (fun n => hQsq n t) ⟨id, hl t⟩).integrable one_le_two

end Abstract

/-! ### The stopped noise of the frozen coupling -/

section Main

universe u

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **C.2 / Aux. lemma 47, Brownian conclusion without localization.** For a coupling with the optional hull
specification (`κ > 0`) and a bounded stop `S ≤ N` of the driving filtration with `S < ζ`, let
`𝒢_t = Γ(𝓕_{S∧t}, K_{S∧t})` be the stopped germ filtration (history joined with the hull germ). The stopped driving
noise `t ↦ B_{t∧S}` has a version `Y`, with continuous paths and `Y₀ = 0` everywhere, such that `Y`, `Y² − (·∧S)` and
`exp(aY − a²(·∧S)/2)` (every real `a`) are `𝒢`-martingales: the noise is a Brownian motion of the germ filtration
stopped at `S` (Lévy's characterization in exponential form). -/
theorem martingale_stoppedNoise_germ_exp (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {S : Ω → ℝ≥0}
    (hS : IsStoppingTime (drivingFiltration P hX) fun ω => (S ω : WithTop ℝ≥0))
    (hSζ : ∀ᵐ ω ∂P, (S ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hSN : ∀ ω, S ω ≤ N) :
    ∃ (A : ℝ≥0 → Ω → Set ℂ) (𝒢 : Filtration ℝ≥0 mΩ),
      (∀ t, Measurable[mΩ, hittingSigma] (A t)) ∧
      (∀ t, ∀ᵐ ω ∂P, A t ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (S ω) t : ℝ≥0) : ℝ)) ∧
      (∀ t, 𝒢 t = histGerm (hS.min_const t).measurableSpace (A t) (centredField h u₀)) ∧
      (∀ t, (hS.min_const t).measurableSpace ≤ 𝒢 t) ∧
      ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝒢 P ∧ (∀ ω, Continuous fun t => Y t ω) ∧ (∀ ω, Y 0 ω = 0) ∧
        (∀ᵐ ω ∂P, ∀ t, Y t ω = B (min t (S ω)) ω) ∧
        Martingale (fun t ω => Y t ω ^ 2 - ((min t (S ω) : ℝ≥0) : ℝ)) 𝒢 P ∧
        ∀ a : ℝ, Martingale (fun t ω => Real.exp (a * Y t ω - a ^ 2 * ((min t (S ω) : ℝ≥0) : ℝ) / 2)) 𝒢 P := by
  obtain ⟨A, 𝒢, hAm, hA', h𝒢, h𝓓𝒢, Y, hY, hYB, ρ, hρst, hρle, hρev, hρmart⟩ :=
    martingale_stoppedNoise_germ hC hκ hu₀ hX hS hSζ hSN
  have hE := hC.1
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hnull𝓓 : ∀ t (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝓓 t] M :=
    fun t M hM h0 => measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hM h0 t
  have hnull𝒢 : ∀ t (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝒢 t] M :=
    fun t M hM h0 => h𝓓𝒢 t _ (measurableSet_stopping_of_null hnull𝓓 (hS.min_const t) hM h0)
  -- the good event
  set good : Ω → Prop := fun ω =>
    Continuous (fun t => B t ω) ∧ B 0 ω = 0 ∧ ∀ t, Y t ω = B (min t (S ω)) ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hE.1.1.cont, hE.1.1.toIsPreBrownianReal.eval_zero_ae_eq_zero, hYB] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨G, hGm, hG0, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  -- the version with continuous paths everywhere
  set Z : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then Y t ω else 0 with hZdef
  have hZB : ∀ ω ∈ G, ∀ t, Z t ω = B (min t (S ω)) ω := fun ω hω t => by
    simp only [hZdef, hω, ↓reduceIte]; exact (hGgood ω hω).2.2 t
  have hZc : ∀ ω, Continuous fun t => Z t ω := by
    intro ω
    by_cases hω : ω ∈ G
    · have e : (fun t => Z t ω) = fun t => B (min t (S ω)) ω := funext (hZB ω hω)
      rw [e]
      exact (hGgood ω hω).1.comp (continuous_id.min continuous_const)
    · simp only [hZdef, hω, ↓reduceIte]; exact continuous_const
  have hZ0 : ∀ ω, Z 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hZB ω hω, zero_min]; exact (hGgood ω hω).2.1
    · simp only [hZdef, hω, ↓reduceIte]
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.stronglyAdapted t).measurable.mono (𝒢.le t) le_rfl
  have hZm : ∀ t, Measurable (Z t) := fun t => Measurable.ite hGm (hYm t) measurable_const
  have hZae : ∀ t, Z t =ᵐ[P] Y t := fun t => hGae.mono fun ω hω => by simp only [hZdef, hω, ↓reduceIte]
  have hZmart : Martingale Z 𝒢 P := martingale_of_ae_eq_of_null hY hZm hZae hnull𝒢
  -- the clock `t ∧ S`
  set Ac : ℝ≥0 → Ω → ℝ := fun t ω => ((min t (S ω) : ℝ≥0) : ℝ) with hAcdef
  have hAca : StronglyAdapted 𝒢 Ac := fun t => by
    have hSt : IsStoppingTime 𝓓 fun ω => ((min (S ω) t : ℝ≥0) : WithTop ℝ≥0) := by
      simp only [WithTop.coe_min]; exact hS.min_const t
    have hle : hSt.measurableSpace ≤ 𝒢 t :=
      (hSt.measurableSpace_mono (hS.min_const t) fun ω => by
        simp only [WithTop.coe_min, le_refl]).trans (h𝓓𝒢 t)
    have hm := measurable_stoppedAt_of_agree (X := fun s (_ : Ω) => ((s : ℝ≥0) : ℝ))
      (K := fun s (_ : Ω) => ((s : ℝ≥0) : ℝ)) (fun s => measurable_const) (G := univ)
      MeasurableSet.univ (0 : ℝ) (fun _ _ _ _ => rfl) (fun _ _ => NNReal.continuous_coe.continuousOn) t hSt
    simp only [mem_univ, ↓reduceIte] at hm
    have e : (fun ω => ((min (S ω) t : ℝ≥0) : ℝ)) = fun ω => ((min t (S ω) : ℝ≥0) : ℝ) := by
      funext ω; rw [min_comm]
    rw [e] at hm
    exact (hm.mono hle le_rfl).stronglyMeasurable
  -- the localizing stops are stops of `𝒢`
  set ρ' : ℕ → Ω → WithTop ℝ≥0 := fun n ω => (ρ n ω : WithTop ℝ≥0) with hρ'def
  have hρ𝒢 : ∀ n, IsStoppingTime 𝒢 (ρ' n) := by
    intro n t
    have e : {ω | ρ' n ω ≤ t} = {ω | ρ' n ω ≤ min ((S ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0)} := by
      ext ω
      simp only [hρ'def, mem_ofPred_eq, le_min_iff]
      exact ⟨fun h' => ⟨WithTop.coe_le_coe.2 (hρle n ω), h'⟩, fun h' => h'.2⟩
    rw [e]
    exact h𝓓𝒢 t _ (IsStoppingTime.measurableSet_stopping_time_le (hρst n) (hS.min_const t))
  -- the localized brackets for the version `Z`
  have hZprog := isStronglyProgressive_of_rightContinuous hZmart.1 fun ω t => (hZc ω).continuousWithinAt
  have hloc : ∀ n, Martingale (fun t ω => stoppedProcess Z (ρ' n) t ω ^ 2 - stoppedProcess Ac (ρ' n) t ω)
      𝒢 P := by
    intro n
    have hSa := hZprog.stronglyAdapted_stoppedProcess (hρ𝒢 n)
    have hAce : ∀ t ω, stoppedProcess Ac (ρ' n) t ω = ((min t (ρ n ω) : ℝ≥0) : ℝ) := fun t ω => by
      simp only [hρ'def]
      rw [stoppedProcess_coe_apply]
      simp only [hAcdef]
      rw [min_eq_left ((min_le_right _ _).trans (hρle n ω))]
    have hAprog := isStronglyProgressive_of_rightContinuous hAca fun ω t =>
      (continuous_of_isSlowClock (isSlowClock_min S) ω).continuousWithinAt
    have hSA := hAprog.stronglyAdapted_stoppedProcess (hρ𝒢 n)
    refine martingale_of_ae_eq_of_null (hρmart n) (fun t => ?_) (fun t => ?_) hnull𝒢
    · exact (((hSa t).measurable.pow_const 2).sub (hSA t).measurable).mono (𝒢.le t) le_rfl
    · filter_upwards [hGae] with ω hω
      show stoppedProcess Z (ρ' n) t ω ^ 2 - stoppedProcess Ac (ρ' n) t ω =
        stoppedProcess Y (ρ' n) t ω ^ 2 - ((min t (ρ n ω) : ℝ≥0) : ℝ)
      rw [hAce]
      simp only [hρ'def]
      rw [stoppedProcess_coe_apply, stoppedProcess_coe_apply]
      simp only [hZdef, hω, ↓reduceIte]
  -- the localization is eventually inactive
  have hlim : ∀ᵐ ω ∂P, ∀ t, ∀ᶠ n in atTop,
      stoppedProcess Z (ρ' n) t ω = Z t ω ∧ stoppedProcess Ac (ρ' n) t ω = Ac t ω := by
    filter_upwards [hρev, hGae] with ω hev hω t
    filter_upwards [hev] with n hn
    simp only [hρ'def]
    rw [stoppedProcess_coe_apply, stoppedProcess_coe_apply, hn]
    refine ⟨?_, ?_⟩
    · rw [hZB ω hω, hZB ω hω, min_eq_left (min_le_right _ _)]
    · simp only [hAcdef]
      rw [min_eq_left (min_le_right _ _)]
  obtain ⟨hexp, hsq⟩ := martingale_exp_sq_of_localized hZmart hZc hZ0 (isSlowClock_min S) hAca hρ𝒢 hloc hlim
  refine ⟨A, 𝒢, hAm, hA', h𝒢, h𝓓𝒢, Z, hZmart, hZc, hZ0, ?_, hsq, hexp⟩
  filter_upwards [hGae] with ω hω t using hZB ω hω t

end Main

end WholeField

end InteractingSLE
