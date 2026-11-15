/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.Limit
import InteractingSLE.Stochastic.Bessel.Uniqueness

/-!
# Existence of Bessel processes of dimension `δ > 1`

Packet PROVE-BESSEL. Specification p. 19, (2.1)–(2.2), and the single-force-point case of the proof
of Theorem 2.2 (p. 21: "standard facts about Bessel processes", [RY99] Ch. XI): for `c > 0`
(dimension `δ = 1 + 2c > 1`), `x ≥ 0` and a pre-Brownian motion `B` with continuous paths, the
process `besselProc c x B` is adapted to every filtration to which `B` is adapted
(`besselProc_measurable`) and almost surely a Bessel path (`ae_isBesselPath`): nonnegative,
continuous, instantaneously reflecting (Lebesgue-null zero set), with integrable reciprocal, and
`X_t = x + B_t + ∫₀ᵗ c / X_s ds`. It is a deterministic functional of the path of `B`
(`besselPath`), and every Bessel path driven by the same path equals it (`IsBesselPath.eq`).

## Construction

`besselPath c x w = ⨆ n, regSol c εₙ x w` with `εₙ = η₀ / (n + 1)` (`besselEps`): the solutions of
the regularized equations with drift `c / max · εₙ` increase as `εₙ ↓ 0`. With probability one the
supremum is finite (the drift integrals have expectations bounded uniformly in `n`,
`integral_regA_le`, and monotone convergence). Pathwise, the limit `X` satisfies
`X_t = x + B_t + A_t` with `A` nondecreasing, `A_b - A_a ≥ ∫ₐᵇ c / X` and `{X ≤ 0}` Lebesgue-null
(`Limit.lean`). The defect `A_N - ∫₀ᴺ c / X` is at most `lim_n J_n(η)`, whose expectation is
`O(η^{1-p})` uniformly in `n` (`integral_regJ_le`); Fatou's lemma twice gives that the defect
vanishes almost surely at every integer `N`, hence (by the two one-sided inequalities) at every time.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Bessel

/-! ### The regularization sequence -/

/-- The regularization parameters `εₙ = η₀ / (n + 1)`, `η₀ = besselLevel c`. -/
def besselEps (c : ℝ) (n : ℕ) : ℝ := besselLevel c / ((n : ℝ) + 1)

theorem besselEps_pos (c : ℝ) (n : ℕ) : 0 < besselEps c n := by
  have := besselLevel_pos c
  unfold besselEps; positivity

theorem besselEps_le (c : ℝ) (n : ℕ) : besselEps c n ≤ besselLevel c := by
  have := besselLevel_pos c
  unfold besselEps
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

theorem besselEps_anti (c : ℝ) : Antitone (besselEps c) := fun n m hnm => by
  have := besselLevel_pos c
  unfold besselEps
  exact div_le_div_of_nonneg_left this.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem tendsto_besselEps (c : ℝ) : Tendsto (besselEps c) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (besselLevel c)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  unfold besselEps; ring

/-! ### The Bessel process -/

/-- The **Bessel path functional**: `besselPath c x w = ⨆ n, regSol c εₙ x w`. -/
def besselPath (c x : ℝ) (w : ℝ → ℝ) : ℝ≥0 → ℝ := limSol c x (besselEps c) w

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {c x : ℝ}

/-- The **Bessel process** `X_t = besselPath c x (B · ω) t` of dimension `1 + 2c` started at `x`. -/
def besselProc (c x : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  besselPath c x (realPath B ω) t

/-- **Adaptedness**: the Bessel process is adapted to every filtration to which `B` is adapted. -/
theorem besselProc_measurable (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 < c) (t : ℝ≥0) :
    Measurable[𝓕 t] (besselProc c x B t) :=
  Measurable.iSup fun n => regProc_measurable 𝓕 hBad hBc hc.le (besselEps_pos c n) t

omit mΩ in
theorem regA_eq_seqA (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    regA c (besselEps c n) x B t ω = seqA c x (besselEps c) (realPath B ω) n t := rfl

/-- Almost surely the regularized solutions are bounded at a fixed time. -/
theorem ae_bddAbove (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ r, Measurable (B r)) (hc : 0 < c) (hx : 0 ≤ x) (N : ℝ≥0) :
    ∀ᵐ ω ∂P, BddAbove (range fun n => seqSol c x (besselEps c) (realPath B ω) n N) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hw : ∀ ω, Continuous (realPath B ω) := continuous_realPath hBc
  set A : ℕ → Ω → ℝ := fun n ω => regA c (besselEps c n) x B N ω
  set K := 1 + ∫ ω, |x + B N ω| ∂P + 2 * (c / besselLevel c * N)
  have hAm : ∀ n, Measurable (A n) := fun n =>
    regA_measurable hBm hBc hc.le (besselEps_pos c n) N
  have hA0 : ∀ n ω, 0 ≤ A n ω := fun n ω => regA_nonneg hc.le (besselEps_pos c n) N ω
  have hAmono : ∀ ω, Monotone fun n => A n ω := fun ω =>
    seqA_mono (hw ω) hc.le (besselEps_pos c) (besselEps_anti c) N
  have hAK : ∀ n, ∫ ω, A n ω ∂P ≤ K := fun n =>
    integral_regA_le hB hBc hBm hc hx (besselEps_pos c n) (besselEps_le c n) N
  have hlin : ∫⁻ ω, ⨆ n, ENNReal.ofReal (A n ω) ∂P ≤ ENNReal.ofReal K := by
    rw [lintegral_iSup (fun n => (hAm n).ennreal_ofReal)
      (fun n m hnm ω => ENNReal.ofReal_le_ofReal (hAmono ω hnm))]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_regA hBm hBc hc.le (besselEps_pos c n) N) (ae_of_all _ (hA0 n))]
    exact ENNReal.ofReal_le_ofReal (hAK n)
  have hae := ae_lt_top (Measurable.iSup fun n => (hAm n).ennreal_ofReal)
    (hlin.trans_lt ENNReal.ofReal_lt_top).ne
  filter_upwards [hae] with ω hω
  refine ⟨x + realPath B ω N + (⨆ n, ENNReal.ofReal (A n ω)).toReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h1 : ENNReal.ofReal (A n ω) ≤ ⨆ n, ENNReal.ofReal (A n ω) := le_iSup (fun n =>
    ENNReal.ofReal (A n ω)) n
  have h2 : A n ω ≤ (⨆ n, ENNReal.ofReal (A n ω)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 h1
  simp only
  rw [seqSol_eq (hw ω) hc.le (besselEps_pos c) n N]
  have : seqA c x (besselEps c) (realPath B ω) n N = A n ω := rfl
  linarith

/-! ### Pathwise assembly -/

section Pathwise

variable {e : ℕ → ℝ} {w : ℝ → ℝ}

theorem limSol_zero (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n) :
    limSol c x e w 0 = x + w 0 := by
  have : ∀ n, seqSol c x e w n 0 = x + w 0 := fun n => by
    rw [seqSol_eq hw hc he n 0, seqA]; simp
  simp only [limSol, this, ciSup_const]

theorem bddAbove_of_nat (hw : Continuous w) (hc : 0 ≤ c) (he : ∀ n, 0 < e n)
    (hb : ∀ N : ℕ, BddAbove (range fun n => seqSol c x e w n N)) (t : ℝ≥0) :
    BddAbove (range fun n => seqSol c x e w n t) :=
  bddAbove_seqSol_of_le hw hc he (hb ⌈t⌉₊) (Nat.le_ceil t)

/-- **Pathwise assembly.** If the regularized solutions are bounded and the drift defect vanishes at
every integer time, the limit is a Bessel path. -/
theorem isBesselPath_limSol (hw : Continuous w) (hc : 0 < c) (he : ∀ n, 0 < e n)
    (hanti : Antitone e) (hlim : Tendsto e atTop (𝓝 0))
    (hb : ∀ N : ℕ, BddAbove (range fun n => seqSol c x e w n N))
    (hd : ∀ N : ℕ, limSol c x e w N - x - w ((N : ℝ≥0) : ℝ)
      = ∫ s in (0 : ℝ)..(N : ℝ≥0), regDrift c 0 (limSol c x e w s.toNNReal)) :
    IsBesselPath c x (fun t => w t) (limSol c x e w) := by
  set X := limSol c x e w with hXdef
  set F : ℝ → ℝ := fun s => regDrift c 0 (X s.toNNReal) with hFdef
  have hX0 : X 0 - x - w 0 = 0 := by rw [hXdef, limSol_zero hw hc.le he]; simp
  -- integrability and the integral equation
  have hint : ∀ t : ℝ≥0, IntervalIntegrable F volume 0 t := fun t => by
    have := (integral_regDrift_zero_limSol_le (x := x) hw hc.le he hanti hlim (hb ⌈t⌉₊)
      (by simp : (0 : ℝ≥0) ≤ t) (Nat.le_ceil t)).1
    simpa using this
  have heqA : ∀ t : ℝ≥0, X t - x - w t = ∫ s in (0 : ℝ)..t, F s := by
    intro t
    set N : ℝ≥0 := (⌈t⌉₊ : ℝ≥0)
    have h1 := (integral_regDrift_zero_limSol_le (x := x) hw hc.le he hanti hlim (hb ⌈t⌉₊)
      (by simp : (0 : ℝ≥0) ≤ t) (Nat.le_ceil t)).2
    have h2 := integral_regDrift_zero_limSol_le (x := x) hw hc.le he hanti hlim (hb ⌈t⌉₊)
      (Nat.le_ceil t) le_rfl
    simp only [NNReal.coe_zero] at h1
    simp only [← hXdef, ← hFdef] at h1 h2
    rw [hX0] at h1
    have hsum := intervalIntegral.integral_add_adjacent_intervals (hint t) h2.1
    have hN := hd ⌈t⌉₊
    linarith [h2.2]
  -- continuity
  have hGc : ContinuousOn (fun s : ℝ => ∫ u in (0 : ℝ)..s, F u) (Ici 0) := by
    intro s hs
    set T : ℝ≥0 := s.toNNReal + 1
    have hT : (T : ℝ) = s + 1 := by
      simp only [T, NNReal.coe_add, Real.coe_toNNReal s hs, NNReal.coe_one]
    have h := intervalIntegral.continuousOn_primitive_interval' (hint T) left_mem_uIcc
    rw [uIcc_of_le T.coe_nonneg, hT] at h
    have hmem : Icc (0 : ℝ) (s + 1) ∈ 𝓝[Ici 0] s := by
      rw [← Ici_inter_Iic]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
    exact (h s ⟨hs, by linarith⟩).mono_of_mem_nhdsWithin hmem
  have hXeq : X = fun t : ℝ≥0 => x + w t + ∫ u in (0 : ℝ)..t, F u := by
    funext t; linarith [heqA t]
  have hXc : Continuous X := by
    rw [hXeq]
    refine (continuous_const.add (hw.comp NNReal.continuous_coe)).add ?_
    exact hGc.comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg
  have hXcR : Continuous fun s : ℝ => X s.toNNReal := hXc.comp continuous_real_toNNReal
  -- the nonpositive set is null
  have hnull : ∀ N : ℕ, volume {s : ℝ | s ∈ Icc (0 : ℝ) (N : ℝ≥0) ∧ X s.toNNReal ≤ 0} = 0 :=
    fun N => volume_limSol_nonpos hw hc he hlim (hb N)
  -- nonnegativity
  have hnn : ∀ t : ℝ≥0, 0 ≤ X t := by
    intro t
    by_contra hneg
    push Not at hneg
    have hopen : IsOpen {s : ℝ | X s.toNNReal < 0} := isOpen_lt hXcR continuous_const
    have htmem : (t : ℝ) ∈ {s : ℝ | X s.toNNReal < 0} := by simpa using hneg
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen _ htmem
    set N : ℕ := ⌈(t : ℝ) + δ⌉₊
    have hsub : Ioo (t : ℝ) (t + δ) ⊆ {s : ℝ | s ∈ Icc (0 : ℝ) (N : ℝ≥0) ∧ X s.toNNReal ≤ 0} := by
      intro s hs
      have hsb : s ∈ Metric.ball (t : ℝ) δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
      refine ⟨⟨t.coe_nonneg.trans hs.1.le, ?_⟩, (hball hsb).le⟩
      rw [NNReal.coe_natCast]
      exact hs.2.le.trans (Nat.le_ceil _)
    have hvol := measure_mono_null hsub (hnull N)
    rw [Real.volume_Ioo] at hvol
    simp at hvol
    linarith
  have hF : ∀ s : ℝ, F s = c / X s.toNNReal := fun s => by
    rw [hFdef]; simp only [regDrift, max_eq_left (hnn _)]
  refine ⟨hXc, hnn, ?_, fun t => ?_, fun t => ?_⟩
  · refine measure_mono_null (t := ⋃ N : ℕ, {s : ℝ | s ∈ Icc (0 : ℝ) (N : ℝ≥0) ∧ X s.toNNReal ≤ 0})
      ?_ (measure_iUnion_null hnull)
    intro s hs
    refine mem_iUnion.2 ⟨⌈s⌉₊, ⟨hs.1, ?_⟩, hs.2.le⟩
    rw [NNReal.coe_natCast]; exact Nat.le_ceil s
  · have := (hint t).const_mul c⁻¹
    refine this.congr fun s _ => ?_
    simp only [hF]
    field_simp
  · have h := heqA t
    have hI : ∫ s in (0 : ℝ)..t, F s = ∫ s in (0 : ℝ)..t, c / X s.toNNReal :=
      intervalIntegral.integral_congr fun s _ => hF s
    show X t = x + w t + ∫ s in (0 : ℝ)..t, c / X s.toNNReal
    linarith

end Pathwise

/-! ### The drift defect vanishes almost surely -/

theorem tendsto_bound_levelSeq (hc : 0 < c) (R : ℝ) :
    Tendsto (fun k => ENNReal.ofReal
      (4 / besselExp c * (2 * levelSeq k) ^ (1 - besselExp c) * R)) atTop (𝓝 0) := by
  have hq : 0 < 1 - besselExp c := by linarith [besselExp_lt_one hc]
  have h2 : Tendsto (fun k => 2 * levelSeq k) atTop (𝓝 0) := by
    simpa using tendsto_levelSeq.const_mul 2
  have h3 : Tendsto (fun k => (2 * levelSeq k) ^ (1 - besselExp c)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (1 - besselExp c) (Or.inr hq.le)).tendsto).comp h2
    rwa [Real.zero_rpow hq.ne'] at this
  have h4 := ((h3.const_mul (4 / besselExp c)).mul_const R)
  simp only [mul_zero, zero_mul] at h4
  rw [← ENNReal.ofReal_zero]
  exact (ENNReal.continuous_ofReal.tendsto _).comp (h4.congr fun k => by ring)

/-- **The drift defect vanishes**: almost surely, at the time `N`,
`A_N = ∫₀ᴺ c / max X_s 0 ds`. -/
theorem ae_defect_eq_zero (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ r, Measurable (B r)) (hc : 0 < c) (hx : 0 ≤ x) (N : ℝ≥0) :
    ∀ᵐ ω ∂P, limSol c x (besselEps c) (realPath B ω) N - x - realPath B ω N
      = ∫ s in (0 : ℝ)..N, regDrift c 0 (limSol c x (besselEps c) (realPath B ω) s.toNNReal) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set e := besselEps c with he_def
  have he := besselEps_pos c
  have hw : ∀ ω, Continuous (realPath B ω) := continuous_realPath hBc
  set R := 2 + 2 * ∫ ω, |x + B N ω| ∂P + 2 * (c / besselLevel c * N)
  set J : ℕ → ℕ → Ω → ℝ := fun k n ω => regJ c (e n) x (levelSeq k) B N ω
  set g : ℕ → Ω → ℝ≥0∞ := fun k ω => liminf (fun n => ENNReal.ofReal (J k n ω)) atTop
  set D : Ω → ℝ := fun ω => (limSol c x e (realPath B ω) N - x - realPath B ω N)
    - ∫ s in (0 : ℝ)..N, regDrift c 0 (limSol c x e (realPath B ω) s.toNNReal)
  have hJm : ∀ k n, Measurable (J k n) := fun k n =>
    regJ_measurable hBm hBc hc.le (he n) (levelSeq k) N
  have hgm : ∀ k, Measurable (g k) := fun k => Measurable.liminf fun n => (hJm k n).ennreal_ofReal
  -- `E g_k ≤ bound_k`
  have hgint : ∀ k, ∫⁻ ω, g k ω ∂P
      ≤ ENNReal.ofReal (4 / besselExp c * (2 * levelSeq k) ^ (1 - besselExp c) * R) := by
    intro k
    refine (lintegral_liminf_le fun n => (hJm k n).ennreal_ofReal).trans ?_
    refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
    have hev : ∀ᶠ n in atTop, e n ≤ levelSeq k :=
      (tendsto_besselEps c).eventually (ge_mem_nhds (levelSeq_pos k))
    filter_upwards [hev] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_regJ hBm hBc hc.le (he n) (levelSeq k) N)
      (ae_of_all _ fun ω => regJ_nonneg hc.le (he n) _ N ω)]
    exact ENNReal.ofReal_le_ofReal
      (integral_regJ_le hB hBc hBm hc hx (he n) hn (besselEps_le c n) N)
  -- `liminf_k g_k = 0` almost surely
  have hlim0 : ∀ᵐ ω ∂P, liminf (fun k => g k ω) atTop = 0 := by
    have hm : Measurable fun ω => liminf (fun k => g k ω) atTop := Measurable.liminf hgm
    have hle : ∫⁻ ω, liminf (fun k => g k ω) atTop ∂P ≤ 0 := by
      refine (lintegral_liminf_le hgm).trans ?_
      have := (tendsto_bound_levelSeq hc R).liminf_eq
      rw [← this]
      exact liminf_le_liminf (Eventually.of_forall hgint)
    exact (lintegral_eq_zero_iff hm).1 (le_antisymm hle (by positivity))
  -- pathwise: `ofReal D ≤ g_k` on the bounded event
  have hpt : ∀ ω, BddAbove (range fun n => seqSol c x e (realPath B ω) n N) →
      ∀ k, ENNReal.ofReal (D ω) ≤ g k ω := by
    intro ω hbd k
    have hη := levelSeq_pos k
    have hT := tendsto_integral_cut_seqSol (x := x) (hw ω) hc.le he (besselEps_anti c)
      (tendsto_besselEps c) hη hbd
    have hg : g k ω = ENNReal.ofReal ((limSol c x e (realPath B ω) N - x - realPath B ω N)
        - ∫ s in (0 : ℝ)..N, qfun c (levelSeq k) (limSol c x e (realPath B ω) s.toNNReal)) :=
      ((ENNReal.continuous_ofReal.tendsto _).comp hT).liminf_eq
    rw [hg]
    refine ENNReal.ofReal_le_ofReal (sub_le_sub_left ?_ _)
    have hF := (integral_regDrift_zero_limSol_le (x := x) (hw ω) hc.le he (besselEps_anti c)
      (tendsto_besselEps c) hbd (by simp : (0 : ℝ≥0) ≤ N) le_rfl).1
    simp only [NNReal.coe_zero] at hF
    refine intervalIntegral.integral_mono_on N.coe_nonneg ?_ hF fun s _ =>
      qfun_le_regDrift_zero hc.le hη _
    refine hF.mono_fun ?_ (ae_of_all _ fun s => ?_)
    · exact ((continuous_qfun hc.le hη).measurable.comp
        (measurable_limSol_real (hw ω) hc.le he)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (qfun_nonneg hc.le hη _),
        abs_of_nonneg (show 0 ≤ regDrift c 0 _ from div_nonneg hc.le (le_max_right _ _))]
      exact qfun_le_regDrift_zero hc.le hη _
  -- pathwise: `D ≥ 0` on the bounded event
  have hD0 : ∀ ω, BddAbove (range fun n => seqSol c x e (realPath B ω) n N) → 0 ≤ D ω := by
    intro ω hbd
    have h := (integral_regDrift_zero_limSol_le (x := x) (hw ω) hc.le he (besselEps_anti c)
      (tendsto_besselEps c) hbd (by simp : (0 : ℝ≥0) ≤ N) le_rfl).2
    rw [limSol_zero (hw ω) hc.le he] at h
    simp only [NNReal.coe_zero] at h
    have : x + realPath B ω 0 - x - realPath B ω 0 = 0 := by ring
    simp only [D]
    linarith
  filter_upwards [ae_bddAbove hB hBc hBm hc hx N, hlim0] with ω hbd hω
  have hle : ENNReal.ofReal (D ω) ≤ 0 := by
    rw [← hω]
    exact le_liminf_of_le (h := Eventually.of_forall fun k => hpt ω hbd k)
  have hDle : D ω ≤ 0 := by simpa using hle
  have := hD0 ω hbd
  simp only [D] at hDle this
  linarith

/-! ### The main theorem -/

/-- **Existence of Bessel processes of dimension `1 + 2c > 1`** (Specification (2.2), p. 19;
[RY99] Ch. XI §1). For a pre-Brownian motion `B` with continuous paths, `c > 0` and `x ≥ 0`, almost
surely `t ↦ besselProc c x B t ω` is a Bessel path driven by `t ↦ B t ω`. -/
theorem ae_isBesselPath (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ r, Measurable (B r)) (hc : 0 < c) (hx : 0 ≤ x) :
    ∀ᵐ ω ∂P, IsBesselPath c x (fun t => B t ω) (fun t => besselProc c x B t ω) := by
  have hb : ∀ᵐ ω ∂P, ∀ N : ℕ,
      BddAbove (range fun n => seqSol c x (besselEps c) (realPath B ω) n (N : ℝ≥0)) :=
    ae_all_iff.2 fun N => ae_bddAbove hB hBc hBm hc hx N
  have hd : ∀ᵐ ω ∂P, ∀ N : ℕ,
      limSol c x (besselEps c) (realPath B ω) N - x - realPath B ω ((N : ℝ≥0) : ℝ)
        = ∫ s in (0 : ℝ)..(N : ℝ≥0),
            regDrift c 0 (limSol c x (besselEps c) (realPath B ω) s.toNNReal) :=
    ae_all_iff.2 fun N => ae_defect_eq_zero hB hBc hBm hc hx N
  filter_upwards [hb, hd] with ω hbω hdω
  have h := isBesselPath_limSol (continuous_realPath hBc ω) hc (besselEps_pos c)
    (besselEps_anti c) (tendsto_besselEps c) hbω hdω
  have hpath : (fun t : ℝ≥0 => realPath B ω t) = fun t => B t ω := by
    funext t; simp [realPath]
  rw [hpath] at h
  exact h

/-- **Uniqueness**: every Bessel path driven by the path of `B` is the Bessel process, almost surely. -/
theorem ae_eq_besselProc_of_isBesselPath (hB : IsPreBrownianReal B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ r, Measurable (B r)) (hc : 0 < c) (hx : 0 ≤ x)
    {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ᵐ ω ∂P, IsBesselPath c x (fun t => B t ω) (fun t => Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t, Y t ω = besselProc c x B t ω := by
  filter_upwards [hY, ae_isBesselPath hB hBc hBm hc hx] with ω h1 h2
  exact fun t => congrFun (h1.eq hc h2) t

/-- **Existence of an adapted Bessel process** in any filtration in which `B` is adapted. -/
theorem exists_isBesselPath (𝓕 : Filtration ℝ≥0 mΩ) (hB : IsPreBrownianReal B P)
    (hBad : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 < c)
    (hx : 0 ≤ x) :
    ∃ X : ℝ≥0 → Ω → ℝ, (∀ t, Measurable[𝓕 t] (X t)) ∧
      ∀ᵐ ω ∂P, IsBesselPath c x (fun t => B t ω) (fun t => X t ω) :=
  ⟨besselProc c x B, besselProc_measurable 𝓕 hBad hBc hc,
    ae_isBesselPath hB hBc (fun r => (hBad r).mono (𝓕.le r) le_rfl) hc hx⟩

end Bessel

end InteractingSLE
