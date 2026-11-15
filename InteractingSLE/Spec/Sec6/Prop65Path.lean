/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import MathFin.Probability.Discrete.DoobLpMaximalInequality
import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Proposition 6.5, part 5: path-valued processes and Doob's `L⁴` inequality

Packet PROVE-SEC6-B (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5-proof`, p. 159: "Doob's
inequality gives `E[sup_{q≤t≤T} |H_{t∧σ}(w) − H_{t∧σ}(v)|^p] ≤ c'_p |w − v|^p` … The Kolmogorov continuity
criterion in the two spatial coordinates, with the supremum norm on `C([q, T])`").

* `measurable_continuousMap_of_eval`: a map into `C(K, ℝ)` (`K` compact metrizable) is Borel measurable as
  soon as its evaluations are measurable (`C(K, ℝ)` is Polish, restriction to a countable dense subset is a
  continuous injection into a Polish product, hence a measurable embedding);
* `lintegral_iSup_rpow_le`: Doob's `L⁴` maximal inequality for a martingale with continuous paths on a
  compact time interval, from MathFin's discrete inequality on dyadic grids.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

/-! ### Measurability of path-valued maps -/

/-- **Maps into `C(K, ℝ)` with measurable evaluations are Borel measurable** (`K` compact, metrizable,
separable). -/
theorem measurable_continuousMap_of_eval {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [TopologicalSpace.SeparableSpace K]
    [MeasurableSpace C(K, ℝ)] [BorelSpace C(K, ℝ)] {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → C(K, ℝ)} (hf : ∀ x, Measurable fun ω => f ω x) : Measurable f := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  have : Countable D := hDc.to_subtype
  let ι : C(K, ℝ) → (D → ℝ) := fun g d => g d
  have hιc : Continuous ι := continuous_pi fun d => (continuous_eval_const (d : K))
  have hιi : Function.Injective ι := by
    intro g₁ g₂ h
    have := Continuous.ext_on hDd g₁.continuous g₂.continuous fun x hx => congrFun h ⟨x, hx⟩
    exact ContinuousMap.ext (congrFun this)
  have hemb : MeasurableEmbedding ι := hιc.measurableEmbedding hιi
  rw [← hemb.measurable_comp_iff]
  exact measurable_pi_iff.2 fun d => hf d

/-! ### Doob's `L⁴` inequality for continuous martingales -/

section Doob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- The dyadic grid of level `n`, capped at `R`. -/
def gridT (n : ℕ) (R : ℝ≥0) (k : ℕ) : ℝ≥0 := min ((k : ℝ≥0) / 2 ^ n) R

lemma gridT_mono (n : ℕ) (R : ℝ≥0) : Monotone (gridT n R) := fun i j hij =>
  min_le_min_right _ (div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity))

/-- The filtration along the grid. -/
def gridFilt (𝓕 : Filtration ℝ≥0 mΩ) (n : ℕ) (R : ℝ≥0) : Filtration ℕ mΩ where
  seq k := 𝓕 (gridT n R k)
  mono' _ _ hij := 𝓕.mono (gridT_mono n R hij)
  le' _ := 𝓕.le _

omit [IsFiniteMeasure P] in
lemma martingale_grid {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓕 P) (n : ℕ) (R : ℝ≥0) :
    Martingale (fun k => N (gridT n R k)) (gridFilt 𝓕 n R) P :=
  ⟨fun _ => hN.stronglyAdapted _, fun _ _ hij => hN.condExp_ae_eq (gridT_mono n R hij)⟩

/-- **Doob's `L⁴` inequality on a grid.** -/
lemma lintegral_max_grid_le {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓕 P) (n : ℕ) (R : ℝ≥0)
    (K : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
        fun k => ‖N (gridT n R k) ω‖) ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (4 / 3) ^ (4 : ℝ) * ∫⁻ ω, ‖N (gridT n R K) ω‖ₑ ^ (4 : ℝ) ∂P := by
  have hsub := (martingale_grid hN n R).submartingale_norm
  have h := MeasureTheory.maximal_ineq_Lp hsub (fun _ _ => norm_nonneg _) (by norm_num : (1 : ℝ) < 4)
    K
  have h4 : (ENNReal.ofReal 4) ≠ 0 := by simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h4 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h4 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num)] at h
  have hnn : ∀ ω, 0 ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖N (gridT n R k) ω‖) := fun ω =>
    (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖N (gridT n R k) ω‖) (Finset.self_mem_range_succ K))
  have e1 : ∀ ω, ‖(Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖N (gridT n R k) ω‖)‖ₑ = ENNReal.ofReal ((Finset.range (K + 1)).sup'
        Finset.nonempty_range_add_one fun k => ‖N (gridT n R k) ω‖) := fun ω => by
    rw [Real.enorm_eq_ofReal (hnn ω)]
  have e2 : ∀ ω, ‖‖N (gridT n R K) ω‖‖ₑ = ‖N (gridT n R K) ω‖ₑ := fun ω => by simp
  simp only [e1, e2] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 4)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)] at h'
  have hinv : ∀ x : ℝ≥0∞, (x ^ (1 / (4 : ℝ))) ^ (4 : ℝ) = x := fun x => by
    rw [one_div, ENNReal.rpow_inv_rpow (by norm_num)]
  rw [hinv, hinv, show (4 : ℝ) / (4 - 1) = 4 / 3 by norm_num] at h'
  exact h'

lemma gridT_ceil (n : ℕ) (R : ℝ≥0) : gridT n R ⌈(2 : ℝ≥0) ^ n * R⌉₊ = R := by
  refine min_eq_right ?_
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

lemma gridT_floor (n : ℕ) {R t : ℝ≥0} (htR : t ≤ R) :
    gridT n R ⌊(2 : ℝ≥0) ^ n * t⌋₊ = (⌊(2 : ℝ≥0) ^ n * t⌋₊ : ℝ≥0) / 2 ^ n := by
  refine min_eq_left ((?_ : _ ≤ t).trans htR)
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact Nat.floor_le (by positivity)

lemma tendsto_gridT_floor {R t : ℝ≥0} (htR : t ≤ R) :
    Tendsto (fun n => gridT n R ⌊(2 : ℝ≥0) ^ n * t⌋₊) atTop (𝓝 t) := by
  simp only [gridT_floor _ htR]
  have hle : ∀ n : ℕ, (⌊(2 : ℝ≥0) ^ n * t⌋₊ : ℝ≥0) / 2 ^ n ≤ t := fun n => by
    rw [div_le_iff₀ (by positivity), mul_comm]; exact Nat.floor_le (by positivity)
  have hge : ∀ n : ℕ, t - 1 / 2 ^ n ≤ (⌊(2 : ℝ≥0) ^ n * t⌋₊ : ℝ≥0) / 2 ^ n := fun n => by
    rw [tsub_le_iff_right, ← add_div, le_div_iff₀ (by positivity), mul_comm]
    exact_mod_cast (Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * t)).le
  have hlim : Tendsto (fun n : ℕ => t - 1 / 2 ^ n) atTop (𝓝 t) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 0) :=
      NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    simpa [one_div_pow] using (tendsto_const_nhds (x := t)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hge hle

/-- **Doob's `L⁴` inequality** for a martingale with continuous paths on `[0, R]`:
`E[(sup_{t ≤ R} |N_t|)⁴] ≤ (4/3)⁴ E[|N_R|⁴]`. -/
theorem lintegral_iSup_rpow_le {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓕 P)
    (hNc : ∀ ω, Continuous fun t => N t ω) (R : ℝ≥0) :
    ∫⁻ ω, (⨆ t : Icc (0 : ℝ≥0) R, ‖N t ω‖ₑ) ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (4 / 3) ^ (4 : ℝ) * ∫⁻ ω, ‖N R ω‖ₑ ^ (4 : ℝ) ∂P := by
  set K : ℕ → ℕ := fun n => ⌈(2 : ℝ≥0) ^ n * R⌉₊
  set m : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal ((Finset.range (K n + 1)).sup'
    Finset.nonempty_range_add_one fun k => ‖N (gridT n R k) ω‖) with hm
  have hmm : ∀ n, Measurable (m n) := fun n => by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Finset.measurable_range_sup'' (f := fun k ω => ‖N (gridT n R k) ω‖) fun k _ => ?_
    exact ((hN.stronglyAdapted _).measurable.mono (𝓕.le _) le_rfl).norm
  have hcont4 : Continuous fun x : ℝ≥0∞ => x ^ (4 : ℝ) := ENNReal.continuous_rpow_const
  have hmono4 : Monotone fun x : ℝ≥0∞ => x ^ (4 : ℝ) := fun _ _ h =>
    ENNReal.rpow_le_rpow h (by norm_num)
  -- pointwise: the continuous supremum is dominated by the grid maxima
  have hpt : ∀ ω, (⨆ t : Icc (0 : ℝ≥0) R, ‖N t ω‖ₑ) ^ (4 : ℝ) ≤
      liminf (fun n => m n ω ^ (4 : ℝ)) atTop := by
    intro ω
    have hsup : (⨆ t : Icc (0 : ℝ≥0) R, ‖N t ω‖ₑ) ≤ liminf (fun n => m n ω) atTop := by
      refine iSup_le fun t => ?_
      have hlim : Tendsto (fun n => ‖N (gridT n R ⌊(2 : ℝ≥0) ^ n * (t : ℝ≥0)⌋₊) ω‖ₑ) atTop
          (𝓝 ‖N t ω‖ₑ) :=
        (continuous_enorm.tendsto _).comp (((hNc ω).tendsto t).comp (tendsto_gridT_floor t.2.2))
      have hle : ∀ n, ‖N (gridT n R ⌊(2 : ℝ≥0) ^ n * (t : ℝ≥0)⌋₊) ω‖ₑ ≤ m n ω := by
        intro n
        have hk : ⌊(2 : ℝ≥0) ^ n * (t : ℝ≥0)⌋₊ ∈ Finset.range (K n + 1) := by
          rw [Finset.mem_range, Nat.lt_succ_iff]
          exact (Nat.floor_le_floor (mul_le_mul_of_nonneg_left t.2.2 (by positivity))).trans
            (Nat.floor_le_ceil _)
        have h1 := Finset.le_sup' (fun k => ‖N (gridT n R k) ω‖) hk
        show ‖N (gridT n R ⌊(2 : ℝ≥0) ^ n * (t : ℝ≥0)⌋₊) ω‖ₑ ≤ ENNReal.ofReal
          ((Finset.range (K n + 1)).sup' Finset.nonempty_range_add_one
            fun k => ‖N (gridT n R k) ω‖)
        rw [← enorm_norm, Real.enorm_eq_ofReal (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal h1
      rw [← hlim.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall hle)
    calc (⨆ t : Icc (0 : ℝ≥0) R, ‖N t ω‖ₑ) ^ (4 : ℝ) ≤ (liminf (fun n => m n ω) atTop) ^ (4 : ℝ) :=
          hmono4 hsup
      _ = liminf (fun n => m n ω ^ (4 : ℝ)) atTop :=
          hmono4.map_liminf_of_continuousAt _ hcont4.continuousAt
  -- integrate (Fatou) and apply the grid inequality
  have hgrid : ∀ n, ∫⁻ ω, m n ω ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (4 / 3) ^ (4 : ℝ) * ∫⁻ ω, ‖N R ω‖ₑ ^ (4 : ℝ) ∂P := fun n => by
    have := lintegral_max_grid_le hN n R (K n)
    rwa [gridT_ceil] at this
  calc ∫⁻ ω, (⨆ t : Icc (0 : ℝ≥0) R, ‖N t ω‖ₑ) ^ (4 : ℝ) ∂P
      ≤ ∫⁻ ω, liminf (fun n => m n ω ^ (4 : ℝ)) atTop ∂P := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ ω, m n ω ^ (4 : ℝ) ∂P) atTop :=
        lintegral_liminf_le fun n => (hmm n).pow_const _
    _ ≤ ENNReal.ofReal (4 / 3) ^ (4 : ℝ) * ∫⁻ ω, ‖N R ω‖ₑ ^ (4 : ℝ) ∂P :=
        liminf_le_of_frequently_le (Frequently.of_forall hgrid)

end Doob

end InteractingSLE.Sec6.Prop65
