/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP3

/-!
# Lemma LP3 with a deterministic time and driver bounds

Packet PROVE-LP17. LP4's collar step (specification p. 483) applies LP3 to ordinary SLE in the mapped-out half-plane
"taking the two force coordinates as protected outer points", and then needs "bounded-energy Girsanov localization":
the force drifts must stay bounded up to the time at which the inner points have been swallowed. The landed
`LP3.lp3_zero` (PROVE-LP15) only records that the outer points are alive. Its two-stage construction runs up to a
**deterministic** time and keeps the **driver** inside the outer interval; `lp3_zero_bdd` records exactly this (same
proof, stronger conclusion):

* `lp3_zero_bdd`: for `a < pm < 0 < pp < b` there are a deterministic `τ > 0` and an event `E` of the Brownian path
  with `P(E) > 0` on which `pm` and `pp` are swallowed by `τ` and `a < W_t < b` on `[0, τ]`.

With the driver in `(a, b)`, every force coordinate outside `[a, b]` keeps a fixed positive gap (the force moves
outward, `V^R_t − W_t ≥ V^R_0 − W_t`), which gives the bounded energy.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE.LP.LP3

universe u

/-- **LP3 with a deterministic time and driver bounds** (the construction of `lp3_zero`). -/
theorem lp3_zero_bdd {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    (hB₀ : IsBrownianReal B₀ P₀) (hB₀m : ∀ t, Measurable (B₀ t)) (hB₀c : ∀ ω, Continuous (B₀ · ω))
    (hB₀0 : ∀ ω, B₀ 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) {a pm pp b : ℝ} (ha : a < pm) (hpm : pm < 0)
    (hpp : 0 < pp) (hb : pp < b) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ},
      IsBrownianReal B P → (∀ t, Measurable (B t)) → (∀ ω, Continuous (B · ω)) → (∀ ω, B 0 ω = 0) →
      ∃ E : Set Ω,
        MeasurableSet[MeasurableSpace.comap (fun ω (t : ℝ≥0) => B t ω) MeasurableSpace.pi] E ∧
        0 < P E ∧ ∀ ω ∈ E, ¬ Alive (drive κ B ω) pm τ ∧ ¬ Alive (drive κ B ω) pp τ ∧
          ∀ t ∈ Icc (0 : ℝ) τ, a < drive κ B ω t ∧ drive κ B ω t < b := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨K, M, hK, hKM⟩ := exists_bessel_constants.{u, u} hB₀ hB₀m hB₀c hB₀0 hκ
  obtain ⟨ε₁, ε₂, hε₁, hε₂, h1, h2, h3, h4b, h5, h6, h7, h8, h9⟩ := lp3_params K M ha hpm hpp hb
  set τ₁ : ℝ≥0 := ε₁ ^ 2 / 16 + ε₁ ^ 2 * K with hτ₁
  have he₁' : (0 : ℝ) < ε₁ := by exact_mod_cast pos_iff_ne_zero.2 hε₁
  have he₂' : (0 : ℝ) < ε₂ := by exact_mod_cast pos_iff_ne_zero.2 hε₂
  refine ⟨(τ₁ : ℝ) + ((ε₂ : ℝ) ^ 2 / 16 + (ε₂ : ℝ) ^ 2 * K), by positivity,
    fun {Ω} {mΩ} {P} {B} hB hBm hBc hB0 => ?_⟩
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
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
    have hε₁b : (ε₁ : ℝ) ≤ (b - pp) / 4 :=
      (le_mul_of_one_le_left he₁.le (by linarith only [hM0])).trans h4b
    refine ⟨fun h => hpm_dead (h.mono hτ₁0 (by linarith only [hτ₂0])), ?_, ?_⟩
    · -- `p_+` is swallowed in the second stage
      refine not_alive_of_restart hW₀c hW₀0 hpp hτ₁0 hτ₂0 hvp le_rfl fun ⟨u, hu⟩ => hd2 ⟨u, ?_⟩
      exact QuantumZipper.isForwardSol_congr_drive hR hu
    · intro t ht
      rcases le_or_gt t τ₁ with htτ | htτ
      · have h := hbd1 t ⟨ht.1, htτ⟩
        exact ⟨by linarith only [h.1, hξ₁le, h3, he₁, ha], by linarith only [h.2, hξ₁le, h5, hb, hpp]⟩
      · have hr : t - τ₁ ∈ Icc (0 : ℝ) τ₂ := ⟨by linarith only [htτ], by linarith only [ht.2]⟩
        have h1 := hR (t - τ₁) hr
        have h2 := hbd2 (t - τ₁) hr
        rw [show (τ₁ : ℝ) + (t - τ₁) = t by ring] at h1
        exact ⟨by linarith only [h1, h2.1, hfin'.1, hξ₁le, h3, hξ₂le, h8, he₁, ha],
          by linarith only [h1, h2.2, hfin'.2, hξ₁le, h4b, hξ₂le, h9, he₂, hε₁b, hb]⟩

end InteractingSLE.LP.LP3
