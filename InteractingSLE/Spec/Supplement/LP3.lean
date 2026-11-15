/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP3Stage
import QuantumZipper.Proofs.Thm18.ASepGCFwd

/-!
# Lemma LP3 (ordinary-SLE steering input)

Packet PROVE-LP15. Supplement §6.3 (`source/spec/p481-528.md` L22–L35, pp. 481–482):

"**Lemma LP3** (ordinary-SLE steering input). Let `k > 4`, let `a < w < b`, and let `I = [p_-, p_+]` be a compact
interval with `a < p_- < w < p_+ < b`. Ordinary chordal `SLE_k`, started at `w`, has positive probability of
swallowing both endpoints of `I` at a finite time before swallowing either outer point `a, b`."

Ordinary chordal `SLE_κ` started at `w` is driven by `W_t = w + √κ B_t`; a real point `x` is swallowed by time `τ`
iff it is not alive on `[0, τ]` (QuantumZipper's `IsForwardSol`, the definition of `swallowTime`).

* `lp3_zero`: the case `w = 0`;
* **`lp3`**: Lemma LP3. There is an event `E` of the path of `B`, of positive probability, on which at some finite
  time `τ` both `p_-` and `p_+` are swallowed while `a` and `b` are alive on `[0, τ]`.

Proof (the source's): first `p_-` (the reflected stage, `stage_det` for `−B`), then, by the Markov property at the
deterministic end `τ₁` of the first stage (`measure_inter_eq_mul_of_past`), `p_+` from its image at `τ₁`. The
source's "positive conditional success probability in every successful first-stage configuration" is realized by a
second stage whose single event works for every configuration in a window: on the first-stage event the image of
`p_+` lies within `η₂ ≤ ε₂/8` of `p_+ − p_-` (the bounds `x − W_t ≤ u_t(x) ≤ x − W_t + 2t/m`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE.LP.LP3

section Helpers

variable {W : ℝ → ℝ}

/-- **Survival of a left point.** If the driver stays `m > 0` to the right of `x` on `[0, T]`, then `x` is alive
on `[0, T]`, with a solution satisfying `u_t(x) ≤ x − W_t`. -/
theorem exists_isForwardSol_of_forall_le_sub (hW : Continuous W) {x T m : ℝ} (hT : 0 ≤ T) (hm : 0 < m)
    (h : ∀ t ∈ Icc (0 : ℝ) T, x + m ≤ W t) :
    ∃ v, IsForwardSol W (x : ℂ) T v ∧ ∀ t ∈ Icc (0 : ℝ) T, (v t).re ≤ x - W t := by
  obtain ⟨v, hv, hvle⟩ := exists_isForwardSol_of_forall_add_le (W := fun t => -W t) hW.neg hT hm (x := -x)
    (fun t ht => by have := h t ht; show -W t + m ≤ -x; linarith)
  have hv' := isForwardSol_neg hv
  simp only [neg_neg, Complex.ofReal_neg] at hv'
  refine ⟨_, hv', fun t ht => ?_⟩
  have := hvle t ht
  simp only [Complex.neg_re]
  linarith

/-- The restarted driver of a path is the driver of the restarted path. -/
theorem pathDrive_restart (s : ℝ) (y : ℝ≥0 → ℝ) (τ : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) :
    pathDrive s y ((τ : ℝ) + r) - pathDrive s y τ = pathDrive s (fun t => y (τ + t) - y τ) r := by
  simp only [pathDrive]
  rw [Real.toNNReal_add τ.coe_nonneg hr, Real.toNNReal_coe]
  ring

theorem pathDrive_neg (s : ℝ) (y : ℝ≥0 → ℝ) : pathDrive s (fun t => -y t) = fun t => -pathDrive s y t := by
  funext t; simp [pathDrive]

end Helpers

/-! ### The parameters -/

/-- The scales of the two stages: `ε₂` small against the gaps `p_+ − p_-`, `b − p_+`, `p_- − a`; `ε₁` small
against `ε₂` (so that the first stage places the image of `p_+` in the second stage's window). -/
theorem lp3_params (K M : ℝ≥0) {a pm pp b : ℝ} (ha : a < pm) (hpm : pm < 0) (hpp : 0 < pp) (hb : pp < b) :
    ∃ ε₁ ε₂ : ℝ≥0, ε₁ ≠ 0 ∧ ε₂ ≠ 0 ∧ (ε₁ : ℝ) ≤ 1 ∧ 2 * (ε₁ : ℝ) ≤ -pm ∧
      ((M : ℝ) + 1) * ε₁ ≤ (pm - a) / 4 ∧ ((M : ℝ) + 1) * ε₁ ≤ (b - pp) / 4 ∧
      ((M : ℝ) + 1) * ε₁ ≤ pp / 2 ∧ (2 + ((M : ℝ) + 1) + 4 * (1 / 16 + K) / pp) * ε₁ ≤ ε₂ / 8 ∧
      2 * (ε₂ : ℝ) ≤ pp - pm ∧ ((M : ℝ) + 1) * ε₂ ≤ (pm - a) / 8 ∧ ((M : ℝ) + 1) * ε₂ ≤ (b - pp) / 8 := by
  set M' : ℝ := (M : ℝ) + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  set e₂ : ℝ := min ((pp - pm) / 2) (min ((pm - a) / (8 * M')) ((b - pp) / (8 * M'))) with he₂
  have he₂pos : 0 < e₂ := lt_min (by linarith) (lt_min (by apply div_pos <;> linarith)
    (by apply div_pos <;> linarith))
  set C₁ : ℝ := 2 + M' + 4 * (1 / 16 + K) / pp with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  set e₁ : ℝ := min 1 (min (-pm / 2) (min ((pm - a) / (4 * M')) (min ((b - pp) / (4 * M'))
    (min (pp / (2 * M')) (e₂ / (8 * C₁)))))) with he₁
  have he₁pos : 0 < e₁ := by
    refine lt_min one_pos (lt_min (by linarith) (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_)))) <;>
      apply div_pos <;> linarith
  refine ⟨e₁.toNNReal, e₂.toNNReal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using he₁pos
  · simpa using he₂pos
  all_goals simp only [Real.coe_toNNReal _ he₁pos.le, Real.coe_toNNReal _ he₂pos.le]
  · exact min_le_left _ _
  · have := (min_le_right _ _).trans (min_le_left (-pm / 2) _) |>.trans_eq' he₁.symm
    linarith
  · have h := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left ((pm - a) / (4 * M')) _))
      |>.trans_eq' he₁.symm
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · have h := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left ((b - pp) / (4 * M')) _))) |>.trans_eq' he₁.symm
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · have h := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left (pp / (2 * M')) _)))) |>.trans_eq' he₁.symm
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · have h := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right (pp / (2 * M')) _)))) |>.trans_eq' he₁.symm
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · have := min_le_left ((pp - pm) / 2) (min ((pm - a) / (8 * M')) ((b - pp) / (8 * M')))
    linarith
  · have h := (min_le_right _ _).trans (min_le_left ((pm - a) / (8 * M')) ((b - pp) / (8 * M')))
      |>.trans_eq' he₂.symm
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · have h := (min_le_right _ _).trans (min_le_right ((pm - a) / (8 * M')) ((b - pp) / (8 * M')))
      |>.trans_eq' he₂.symm
    rw [le_div_iff₀ (by positivity)] at h; linarith

/-! ### The assembly -/

universe u

/-- **Lemma LP3 with the driver started at `0`.** -/
theorem lp3_zero {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) {a pm pp b : ℝ} (ha : a < pm) (hpm : pm < 0)
    (hpp : 0 < pp) (hb : pp < b) :
    ∃ E : Set Ω, MeasurableSet[MeasurableSpace.comap (fun ω (t : ℝ≥0) => B t ω) MeasurableSpace.pi] E ∧
      0 < P E ∧ ∀ ω ∈ E, ∃ τ : ℝ, 0 ≤ τ ∧ ¬ Alive (drive κ B ω) pm τ ∧ ¬ Alive (drive κ B ω) pp τ ∧
        Alive (drive κ B ω) a τ ∧ Alive (drive κ B ω) b τ := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  obtain ⟨K, M, hK, hKM⟩ := exists_bessel_constants.{u, u} hB hBm hBc hB0 hκ
  obtain ⟨ε₁, ε₂, hε₁, hε₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := lp3_params K M ha hpm hpp hb
  set τ₁ : ℝ≥0 := ε₁ ^ 2 / 16 + ε₁ ^ 2 * K with hτ₁
  -- the first stage, for `−B`
  have hnB : IsBrownianReal (fun t ω => -B t ω) P := hB.neg
  obtain ⟨E₁, hE₁m, hE₁P, hE₁⟩ := exists_stageEvent (X := fun t ω => -B t ω) hnB (fun t => (hBm t).neg)
    (fun ω => (hBc ω).neg) hκ0 (fun hX hXm => hKM hX hXm) hε₁ (-pm) (ηs := (ε₁ : ℝ) / 8)
    (by have : (0 : ℝ) < ε₁ := by exact_mod_cast pos_iff_ne_zero.2 hε₁
        positivity)
  -- the second stage, for the increments after `τ₁`
  set Y : ℝ≥0 → Ω → ℝ := fun r ω => B (τ₁ + r) ω - B τ₁ ω with hY
  have hYB : IsBrownianReal Y P := hB.shift τ₁
  obtain ⟨E₂, hE₂m, hE₂P, hE₂⟩ := exists_stageEvent (X := Y) hYB (fun t => (hBm _).sub (hBm _))
    (fun ω => ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const) hκ0
    (fun hX hXm => hKM hX hXm) hε₂ (pp - pm) (ηs := (ε₂ : ℝ) / 8)
    (by have : (0 : ℝ) < ε₂ := by exact_mod_cast pos_iff_ne_zero.2 hε₂
        positivity)
  -- independence of the two stages
  have hE₁past : MeasurableSet[MeasurableSpace.comap (fun ω (r : Iic τ₁) => B r ω) MeasurableSpace.pi] E₁ :=
    measurableSet_comap_of_factor (Φ := fun x (r : Iic τ₁) => -x r)
      (measurable_pi_iff.2 fun r => (measurable_pi_apply _).neg) (fun _ => rfl) hE₁m
  have hE₂path : MeasurableSet[MeasurableSpace.comap (fun ω r => B (τ₁ + r) ω - B τ₁ ω)
      MeasurableSpace.pi] E₂ :=
    measurableSet_comap_of_factor (Φ := fun y (r : Iic (ε₂ ^ 2 / 16 + ε₂ ^ 2 * K)) => y r)
      (measurable_pi_iff.2 fun r => measurable_pi_apply _) (fun _ => rfl) hE₂m
  have hP12 := measure_inter_eq_mul_of_past hB.toIsPreBrownianReal τ₁ hE₁past hE₂path
  refine ⟨E₁ ∩ E₂, ?_, ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_comap_of_factor (Φ := fun y (r : Iic τ₁) => y r)
        (measurable_pi_iff.2 fun r => measurable_pi_apply _) (fun _ => rfl) hE₁past
    · exact measurableSet_comap_of_factor (Φ := fun y r => y (τ₁ + r) - y τ₁)
        (measurable_pi_iff.2 fun r => Measurable.sub (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) _)
          (measurable_pi_apply _)) (fun _ => rfl) hE₂path
  · rw [hP12]; exact ENNReal.mul_pos hE₁P.ne' hE₂P.ne'
  · rintro ω ⟨hω₁, hω₂⟩
    set W₀ : ℝ → ℝ := drive κ B ω with hW₀
    have hW₀c : Continuous W₀ := NonSwallow.continuous_drive_ns hBc κ ω
    have hW₀0 : W₀ 0 = 0 := by simp [hW₀, drive, hB0 ω]
    have he₁ : (0 : ℝ) < ε₁ := by exact_mod_cast pos_iff_ne_zero.2 hε₁
    have he₂ : (0 : ℝ) < ε₂ := by exact_mod_cast pos_iff_ne_zero.2 hε₂
    have hM0 : (0 : ℝ) ≤ M := M.2
    have hK0 : (0 : ℝ) ≤ K := K.2
    have hτ₁r : ((ε₁ : ℝ) ^ 2 / 16 + (ε₁ : ℝ) ^ 2 * K) = τ₁ := by rw [hτ₁]; push_cast; ring
    have hτ₁0 : (0 : ℝ) ≤ τ₁ := τ₁.2
    set ξ₁ : ℝ := (ε₁ : ℝ) / 8 + M * ε₁ with hξ₁
    set ξ₂ : ℝ := (ε₂ : ℝ) / 8 + M * ε₂ with hξ₂
    have hξ₁le : ξ₁ ≤ ((M : ℝ) + 1) * ε₁ := by rw [hξ₁]; linarith only [he₁]
    have hξ₂le : ξ₂ ≤ ((M : ℝ) + 1) * ε₂ := by rw [hξ₂]; linarith only [he₂]
    -- stage 1, for `−B`
    obtain ⟨t1, d1, m1⟩ := hE₁ ω hω₁
    have hV₁ : pathDrive (√κ) (fun s => -B s ω) = fun t => -W₀ t := pathDrive_neg (√κ) (fun s => B s ω)
    have hV₁c : Continuous (pathDrive (√κ) fun s => -B s ω) := continuous_pathDrive (hBc ω).neg
    have hV₁0 : pathDrive (√κ) (fun s => -B s ω) 0 = 0 := pathDrive_zero (by simp [hB0 ω])
    obtain ⟨hd1, hdrv1, hfin1⟩ := stage_det hV₁c hV₁0 he₁ (p₀ := -pm) (p := -pm) (η := 0)
      (ηs := (ε₁ : ℝ) / 8) (ξ := M * ε₁) (S := (ε₁ : ℝ) ^ 2 * K) h2 (by simp) le_rfl (by positivity)
      (by linarith) (by positivity) t1 d1 m1
    rw [hV₁, hτ₁r] at hd1
    have hpm_dead : ¬ Alive W₀ pm τ₁ := fun h => hd1 (alive_neg_iff.2 h)
    rw [hτ₁r] at hdrv1 hfin1
    have hbd1 : ∀ t ∈ Icc (0 : ℝ) τ₁, pm + ε₁ - ξ₁ < W₀ t ∧ W₀ t < ξ₁ := by
      intro t ht
      have h := hdrv1 t ht
      rw [hV₁] at h
      constructor <;> linarith [h.1, h.2]
    have hfin : |W₀ τ₁ - (pm + ε₁)| < ξ₁ := by
      rw [hV₁] at hfin1
      have h := abs_lt.1 hfin1
      rw [abs_lt]; constructor <;> linarith [h.1, h.2]
    have hfin' := abs_lt.1 hfin
    -- the other three points survive the first stage
    obtain ⟨vp, hvp, hvplow⟩ := exists_isForwardSol_of_forall_add_le hW₀c hτ₁0 (half_pos hpp) (x := pp)
      (fun t ht => by have := (hbd1 t ht).2; linarith)
    obtain ⟨vb, hvb, hvblow⟩ := exists_isForwardSol_of_forall_add_le hW₀c hτ₁0 (half_pos hpp) (x := b)
      (fun t ht => by have := (hbd1 t ht).2; linarith)
    have hDl : 0 < (pm - a) / 2 := by linarith
    obtain ⟨va, hva, hvaup⟩ := exists_isForwardSol_of_forall_le_sub hW₀c hτ₁0 hDl (x := a)
      (fun t ht => by have := (hbd1 t ht).1; linarith)
    have hvpm : ∀ t ∈ Icc (0 : ℝ) τ₁, pp / 2 ≤ (vp t).re := fun t ht => by
      have := hvplow t ht; have := (hbd1 t ht).2; linarith
    have hvpT := re_le_of_isForwardSol hW₀c hW₀0 (half_pos hpp) hvp hvpm τ₁ ⟨hτ₁0, le_rfl⟩
    have hvbT := hvblow τ₁ ⟨hτ₁0, le_rfl⟩
    have hvaT := hvaup τ₁ ⟨hτ₁0, le_rfl⟩
    -- the window of the second stage
    set η₂ : ℝ := ε₁ + ξ₁ + 4 * τ₁ / pp with hη₂
    have hsq : (ε₁ : ℝ) ^ 2 ≤ ε₁ := pow_le_of_le_one he₁.le h1 two_ne_zero
    have hτ₁le : (τ₁ : ℝ) ≤ (1 / 16 + K) * ε₁ := by
      have hK' : (ε₁ : ℝ) ^ 2 * K ≤ ε₁ * K := mul_le_mul_of_nonneg_right hsq hK0
      rw [← hτ₁r]; linarith only [hsq, hK']
    have h4 : 4 * (τ₁ : ℝ) / pp ≤ 4 * (1 / 16 + K) / pp * ε₁ := by
      calc 4 * (τ₁ : ℝ) / pp ≤ 4 * ((1 / 16 + K) * ε₁) / pp := by gcongr
        _ = 4 * (1 / 16 + K) / pp * ε₁ := by ring
    have hη₂le : η₂ ≤ ε₂ / 8 := by
      rw [hη₂]; linarith only [hξ₁le, h4, h6, he₁]
    have hpwin : |(vp τ₁).re - (pp - pm)| ≤ η₂ := by
      have h2T : 2 * (τ₁ : ℝ) / (pp / 2) = 4 * τ₁ / pp := by field_simp; ring
      rw [h2T] at hvpT
      rw [abs_le]; constructor <;> linarith [hvpT.1, hvpT.2]
    -- stage 2
    obtain ⟨t2, d2, m2⟩ := hE₂ ω hω₂
    have hV₂c : Continuous (pathDrive (√κ) fun s => Y s ω) :=
      continuous_pathDrive (((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const)
    have hV₂0 : pathDrive (√κ) (fun s => Y s ω) 0 = 0 := pathDrive_zero (by simp [hY])
    have hpp₂ : 2 * (ε₂ : ℝ) ≤ pp - pm := h7
    obtain ⟨hd2, hdrv2, -⟩ := stage_det hV₂c hV₂0 he₂ (p₀ := pp - pm) (p := (vp τ₁).re) (η := η₂)
      (ηs := (ε₂ : ℝ) / 8) (ξ := M * ε₂) (S := (ε₂ : ℝ) ^ 2 * K) hpp₂ hpwin
      (le_trans (abs_nonneg _) hpwin) (by positivity) (by linarith) (by positivity) t2 d2 m2
    set τ₂ : ℝ := (ε₂ : ℝ) ^ 2 / 16 + (ε₂ : ℝ) ^ 2 * K with hτ₂
    have hτ₂0 : 0 ≤ τ₂ := by positivity
    have hR : ∀ r ∈ Icc (0 : ℝ) τ₂, W₀ (τ₁ + r) - W₀ τ₁ = pathDrive (√κ) (fun s => Y s ω) r :=
      fun r hr => pathDrive_restart (√κ) (fun s => B s ω) τ₁ hr.1
    have hbd2 : ∀ r ∈ Icc (0 : ℝ) τ₂, -ξ₂ < pathDrive (√κ) (fun s => Y s ω) r ∧
        pathDrive (√κ) (fun s => Y s ω) r < pp - pm - ε₂ + ξ₂ := by
      intro r hr
      have h := hdrv2 r hr
      constructor <;> linarith [h.1, h.2]
    refine ⟨τ₁ + τ₂, by positivity, fun h => hpm_dead (h.mono hτ₁0 (by linarith)), ?_, ?_, ?_⟩
    · -- `p_+` is swallowed in the second stage
      refine not_alive_of_restart hW₀c hW₀0 hpp hτ₁0 hτ₂0 hvp le_rfl fun ⟨u, hu⟩ => hd2 ⟨u, ?_⟩
      exact QuantumZipper.isForwardSol_congr_drive hR hu
    · -- `a` survives the second stage
      have hm : 0 < (pm - a) / 4 := by linarith
      obtain ⟨wa, hwa, -⟩ := exists_isForwardSol_of_forall_le_sub hV₂c hτ₂0 hm (x := (va τ₁).re)
        (fun r hr => by have := (hbd2 r hr).1; linarith)
      obtain ⟨u, hu, -⟩ := exists_isForwardSol_glue hW₀c hτ₁0 hτ₂0 hva
        (QuantumZipper.isForwardSol_congr_drive (fun r hr => (hR r hr).symm) hwa)
      exact ⟨u, hu⟩
    · -- `b` survives the second stage
      have hm : 0 < (b - pp) / 4 := by linarith
      obtain ⟨wb, hwb, -⟩ := exists_isForwardSol_of_forall_add_le hV₂c hτ₂0 hm (x := (vb τ₁).re)
        (fun r hr => by have := (hbd2 r hr).2; linarith)
      obtain ⟨u, hu, -⟩ := exists_isForwardSol_glue hW₀c hτ₁0 hτ₂0 hvb
        (QuantumZipper.isForwardSol_congr_drive (fun r hr => (hR r hr).symm) hwb)
      exact ⟨u, hu⟩

/-- Translating the driver translates the real points. -/
theorem alive_const_add_iff (D : ℝ → ℝ) (w x T : ℝ) : Alive (fun t => w + D t) x T ↔ Alive D (x - w) T := by
  have h := ASep.GC.isForwardSol_sub_const (fun t => w + D t) w (x : ℂ) T
  have e1 : (fun s => w + D s - w) = D := by funext s; ring
  have e2 : ((x : ℂ) - (w : ℂ)) = ((x - w : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2] at h
  simp only [Alive, h]

/-- **Lemma LP3** (ordinary-SLE steering input; supplement p. 481). Let `κ > 4`, `a < p_- < w < p_+ < b`, and let
`B` be a Brownian motion with measurable coordinates and continuous paths vanishing at `0`. Ordinary chordal `SLE_κ`
started at `w` (driver `w + √κ B`) has positive probability of swallowing both `p_-` and `p_+` at a finite time `τ`
before swallowing `a` or `b`: on an event `E` of the path of `B` with `P E > 0`, `p_±` are not alive on `[0, τ]`
while `a` and `b` are alive on `[0, τ]`. -/
theorem lp3 {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) {a pm w pp b : ℝ} (ha : a < pm) (hpm : pm < w)
    (hpp : w < pp) (hb : pp < b) :
    ∃ E : Set Ω, MeasurableSet[MeasurableSpace.comap (fun ω (t : ℝ≥0) => B t ω) MeasurableSpace.pi] E ∧
      0 < P E ∧ ∀ ω ∈ E, ∃ τ : ℝ, 0 ≤ τ ∧
        ¬ Alive (fun t => w + drive κ B ω t) pm τ ∧ ¬ Alive (fun t => w + drive κ B ω t) pp τ ∧
        Alive (fun t => w + drive κ B ω t) a τ ∧ Alive (fun t => w + drive κ B ω t) b τ := by
  obtain ⟨E, hEm, hEP, hE⟩ := lp3_zero hB hBm hBc hB0 hκ (a := a - w) (pm := pm - w) (pp := pp - w)
    (b := b - w) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨E, hEm, hEP, fun ω hω => ?_⟩
  obtain ⟨τ, hτ, h1, h2, h3, h4⟩ := hE ω hω
  simp only [alive_const_add_iff]
  exact ⟨τ, hτ, h1, h2, h3, h4⟩

end InteractingSLE.LP.LP3
