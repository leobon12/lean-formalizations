/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessPath

/-!
# The retargeted paths in the new clock

Packet PROVE-SEC7-C8. Along a driving path whose new target `V` stays strictly to the right of the driver before a
horizon `T` (`SepUpTo`), the retargeting family `M_t` of `TargetChangeProcessPath.lean` and its clock
`C(t) = ∫₀ᵗ α² q⁻⁴` give new-time paths `u ↦ F(C⁻¹(u))` (`newPath`) on `[0, T̃)`, `T̃ = sup_{S < T} C(S)`
(`newHorizon`). This file proves, for every force point `v ≠ V` (`IsMarkUpTo`):

* the integrated Loewner equation of the image in the new clock (`newPath_mob_eq`):
  `M(v)(u) = M_0(x) + ∫₀ᵘ 2/(M(v) − M(w))`;
* the same for the old target `β` started at `−1` (`newPath_beta_eq`);
* integrability of the new reciprocal gaps (`intervalIntegrable_newPath_inv`) and Lebesgue-nullity of the new
  collision sets (`volume_newCollision`), both from the change of variables `u = C(s)`;
* continuity of the new paths (`continuousOn_newPath`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

variable {w vk : ℝ≥0 → ℝ} {xk : ℝ} {T : ℝ≥0∞}

/-- Before `T` the new target is strictly right of the driver and both are continuous: `IsSep` on every `[0, S]`,
`S < T`. -/
def SepUpTo (w vk : ℝ≥0 → ℝ) (T : ℝ≥0∞) : Prop :=
  ∀ S : ℝ, 0 ≤ S → ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T → IsSep w vk S

/-- The new horizon `T̃ = sup_{S < T} C(S)`. -/
def newHorizon (xk : ℝ) (w vk : ℝ≥0 → ℝ) (T : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ S : ℝ≥0, ⨆ (_ : (S : ℝ≥0∞) < T), ENNReal.ofReal (clk (rate xk w vk) S)

/-- A function of the original real time read in the new clock: `u ↦ F(C⁻¹(u))`. -/
def newPath (xk : ℝ) (w vk : ℝ≥0 → ℝ) (F : ℝ → ℝ) (u : ℝ≥0) : ℝ := F (invClk (rate xk w vk) u)

/-- The image of a force point (or of the driver) in original time, `s ↦ M_s(v_s)`. -/
def mobPath (xk : ℝ) (w vk : ℝ≥0 → ℝ) (v : ℝ≥0 → ℝ) (s : ℝ) : ℝ := mob xk w vk s (v s.toNNReal)

theorem SepUpTo.isSep_of_lt (h : SepUpTo w vk T) {S : ℝ≥0} (hS : (S : ℝ≥0∞) < T) : IsSep w vk S :=
  h S S.coe_nonneg (by rwa [Real.toNNReal_coe])

/-- A new time before `T̃` is the clock of an original time `S < T`, strictly. -/
theorem exists_lt_clk_of_lt_newHorizon {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    ∃ S : ℝ≥0, (S : ℝ≥0∞) < T ∧ (u : ℝ) < clk (rate xk w vk) S := by
  obtain ⟨S, hS⟩ := lt_iSup_iff.1 hu
  obtain ⟨hST, hS'⟩ := lt_iSup_iff.1 hS
  refine ⟨S, hST, ?_⟩
  have h0 : 0 ≤ clk (rate xk w vk) S := by
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (le_of_not_ge hneg)] at hS'
    exact absurd hS' (not_lt.2 bot_le)
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg u.coe_nonneg).1 (by rwa [ENNReal.ofReal_coe_nnreal])

/-- The clock maps `[0, T)` into `[0, T̃)`. -/
theorem clk_lt_newHorizon (h : SepUpTo w vk T) (hxk : 0 < xk) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) :
    ENNReal.ofReal (clk (rate xk w vk) s) < newHorizon xk w vk T := by
  obtain ⟨S', hsS', hS'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hR := (h.isSep_of_lt hS'T).isRate hxk
  have hlt : clk (rate xk w vk) s < clk (rate xk w vk) S' :=
    hR.clk_lt ⟨s.coe_nonneg, by exact_mod_cast hsS'.le⟩ ⟨S'.coe_nonneg, le_rfl⟩ (by exact_mod_cast hsS')
  have h0 : 0 ≤ clk (rate xk w vk) s := hR.clk_nonneg ⟨s.coe_nonneg, by exact_mod_cast hsS'.le⟩
  refine lt_of_lt_of_le ?_ (le_iSup₂_of_le S' hS'T le_rfl)
  exact (ENNReal.ofReal_lt_ofReal_iff (h0.trans_lt hlt)).2 hlt

/-- The data at a new time `u < T̃`: an original time `S < T` with `u < C(S)`; the inverse clock `C⁻¹(u) ∈ [0, S]`
and `C(C⁻¹(u)) = u`. -/
theorem newTime_spec (h : SepUpTo w vk T) (hxk : 0 < xk) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    ∃ S : ℝ≥0, (S : ℝ≥0∞) < T ∧ IsRate (rate xk w vk) S ∧ (u : ℝ) < clk (rate xk w vk) S ∧
      invClk (rate xk w vk) u ∈ Icc 0 (S : ℝ) ∧ clk (rate xk w vk) (invClk (rate xk w vk) u) = u := by
  obtain ⟨S, hST, hu'⟩ := exists_lt_clk_of_lt_newHorizon hu
  have hR := (h.isSep_of_lt hST).isRate hxk
  have hmem : (u : ℝ) ∈ Icc 0 (clk (rate xk w vk) S) := ⟨u.coe_nonneg, hu'.le⟩
  exact ⟨S, hST, hR, hu', hR.invClk_mem hmem, hR.clk_invClk hmem⟩

/-- The inverse clock of a new time before `T̃` is an original time before `T`. -/
theorem invClk_lt (h : SepUpTo w vk T) (hxk : 0 < xk) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    (((invClk (rate xk w vk) u).toNNReal : ℝ≥0) : ℝ≥0∞) < T := by
  obtain ⟨S, hST, -, -, hmem, -⟩ := newTime_spec h hxk hu
  refine lt_of_le_of_lt ?_ hST
  exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hmem.2

/-! ### Force points -/

/-- A force point `v` started at `x` and following the Loewner flow of `w` before `T` (the frozen conjuncts
`vR_eq`, `continuousOn_vR`, `integrable_gapR`, `volume_collisionR`), never meeting the new target `V`. -/
structure IsMarkUpTo (w vk v : ℝ≥0 → ℝ) (x : ℝ) (T : ℝ≥0∞) : Prop where
  eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)
  cont : ContinuousOn v {t | (t : ℝ≥0∞) < T}
  integrable : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t
  collision : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = v s.toNNReal} = 0
  ne : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → v t ≠ vk t

/-- A path continuous before `T` is continuous in real time on every `[0, S]` with `S < T`. -/
theorem continuousOn_real_of_lt {f : ℝ≥0 → ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < T}) {S : ℝ}
    (hS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T) : ContinuousOn (fun s : ℝ => f s.toNNReal) (Icc 0 S) := by
  refine hf.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
  exact lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_toNNReal hs.2) hS

theorem lt_of_mem_Icc {S s : ℝ} (hS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T) (hs : s ∈ Icc 0 S) :
    ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
  lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_toNNReal hs.2) hS

variable {v : ℝ≥0 → ℝ} {x S s : ℝ}

namespace IsMarkUpTo

/-- The real-time form of the integrated equation on `[0, S]`. -/
theorem eq_real (hv : IsMarkUpTo w vk v x T) {S : ℝ} (hS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T) :
    ∀ s ∈ Icc 0 S, v s.toNNReal = x + ∫ u in (0 : ℝ)..s, 2 / (v u.toNNReal - w u.toNNReal) := by
  intro s hs
  rw [hv.eq _ (lt_of_mem_Icc hS hs), Real.coe_toNNReal _ hs.1]

theorem intervalIntegrable_two_div (hv : IsMarkUpTo w vk v x T) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T) :
    IntervalIntegrable (fun u => 2 / (v u.toNNReal - w u.toNNReal)) volume 0 S := by
  have h := (hv.integrable _ hS).const_mul (-2)
  rw [Real.coe_toNNReal _ hS0] at h
  refine h.congr fun u _ => ?_
  rw [div_eq_mul_inv, ← neg_sub, inv_neg]
  ring

theorem ae_ne (hv : IsMarkUpTo w vk v x T) {S : ℝ} (hS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T) :
    ∀ᵐ s, s ∈ Icc 0 S → v s.toNNReal ≠ w s.toNNReal := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hv.collision] with s hs hsI heq
  exact hs ⟨hsI.1, lt_of_mem_Icc hS hsI, heq.symm⟩

end IsMarkUpTo

/-- The new target follows the Loewner flow before `T`: `V = x_k + ∫ 2/(V − w)`. -/
def TargetEq (w vk : ℝ≥0 → ℝ) (xk : ℝ) (T : ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vk t = xk + ∫ s in (0 : ℝ)..t, 2 / (vk s.toNNReal - w s.toNNReal)

theorem TargetEq.eq_real (hk : TargetEq w vk xk T) {S : ℝ} (hS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T) :
    ∀ s ∈ Icc 0 S, vk s.toNNReal = xk + ∫ u in (0 : ℝ)..s, 2 / (vk u.toNNReal - w u.toNNReal) := by
  intro s hs
  rw [hk _ (lt_of_mem_Icc hS hs), Real.coe_toNNReal _ hs.1]

/-- The original-time image of a force point, on `[0, S]`. -/
theorem mobPath_eq_add_integral (h : SepUpTo w vk T) (hxk : 0 < xk) (hk : TargetEq w vk xk T)
    (hv : IsMarkUpTo w vk v x T) {S : ℝ} (hS0 : 0 ≤ S) (hS : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) < T) :
    mobPath xk w vk v S = mob xk w vk 0 x +
      ∫ s in (0 : ℝ)..S, rate xk w vk s * (2 / (mobPath xk w vk v s - mobPath xk w vk w s)) :=
  mob_eq_add_integral (h S hS0 hS) hxk (hk.eq_real hS) (hv.eq_real hS) (hv.intervalIntegrable_two_div hS0 hS)
    (hv.ae_ne hS) fun _ hs => hv.ne _ (lt_of_mem_Icc hS hs)

/-- Reading an original-time integrand in the new clock: `g(C(s)) = G(s)` on `[0, S]`. -/
theorem newPath_clk {S : ℝ} (hR : IsRate (rate xk w vk) S) (F : ℝ → ℝ) {s : ℝ} (hs : s ∈ Icc 0 S) :
    newPath xk w vk F (clk (rate xk w vk) s).toNNReal = F s := by
  simp only [newPath]
  rw [Real.coe_toNNReal _ (hR.clk_nonneg hs), hR.invClk_clk hs]

/-- **The integrated Loewner equation of an image force point in the new clock**:
`M(v)(u) = M_0(x) + ∫₀ᵘ 2/(M(v) − M(w))` for `u < T̃`. -/
theorem newPath_mob_eq (h : SepUpTo w vk T) (hxk : 0 < xk) (hk : TargetEq w vk xk T)
    (hv : IsMarkUpTo w vk v x T) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    newPath xk w vk (mobPath xk w vk v) u = mob xk w vk 0 x +
      ∫ r in (0 : ℝ)..u, 2 / (newPath xk w vk (mobPath xk w vk v) r.toNNReal -
        newPath xk w vk (mobPath xk w vk w) r.toNNReal) := by
  obtain ⟨S, hST, hR, -, hmem, hclk⟩ := newTime_spec h hxk hu
  set S₀ := invClk (rate xk w vk) u with hS₀
  have hR0 : IsRate (rate xk w vk) S₀ := hR.mono hmem.1 hmem.2
  have hS₀T : ((S₀.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hmem.2) hST
  have he := mobPath_eq_add_integral h hxk hk hv hmem.1 hS₀T
  show mobPath xk w vk v S₀ = _
  rw [he, ← hclk, hR0.integral_clk_eq]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hmem.1] at hs
  rw [newPath_clk hR0 _ hs, newPath_clk hR0 _ hs]

/-- **The old target in the new clock**: `β(u) = −1 + ∫₀ᵘ 2/(β − M(w))` for `u < T̃`. -/
theorem newPath_beta_eq (h : SepUpTo w vk T) (hxk : 0 < xk) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    newPath xk w vk (beta xk w vk) u = -1 +
      ∫ r in (0 : ℝ)..u, 2 / (newPath xk w vk (beta xk w vk) r.toNNReal -
        newPath xk w vk (mobPath xk w vk w) r.toNNReal) := by
  obtain ⟨S, hST, hR, -, hmem, hclk⟩ := newTime_spec h hxk hu
  set S₀ := invClk (rate xk w vk) u with hS₀
  have hR0 : IsRate (rate xk w vk) S₀ := hR.mono hmem.1 hmem.2
  have hsep : IsSep w vk S₀ := (h.isSep_of_lt hST).mono hmem.1 hmem.2
  have he := beta_eq_add_integral hsep hxk
  show beta xk w vk S₀ = _
  rw [he, ← hclk, hR0.integral_clk_eq]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hmem.1] at hs
  rw [newPath_clk hR0 _ hs, newPath_clk hR0 _ hs, mobPath]

/-! ### Integrability, collisions and continuity in the new clock -/

/-- `M(w) − M(v) = α (w − v)/(q D)`, `D = V − v`. -/
theorem mobPath_sub (hq : gap w vk s ≠ 0) (hD : vk s.toNNReal - v s.toNNReal ≠ 0) :
    mobPath xk w vk w s - mobPath xk w vk v s =
      alpha xk w vk s * (w s.toNNReal - v s.toNNReal) / (gap w vk s * (vk s.toNNReal - v s.toNNReal)) := by
  simp only [gap] at hq
  simp only [mobPath, mob, gap]
  field_simp
  ring

/-- `rate · (M(w) − M(v))⁻¹ = (α D/q³) (w − v)⁻¹`. -/
theorem rate_mul_inv_mobPath_sub {s : ℝ} (hxk : 0 < xk) (hq : gap w vk s ≠ 0)
    (hD : vk s.toNNReal - v s.toNNReal ≠ 0) :
    rate xk w vk s * (mobPath xk w vk w s - mobPath xk w vk v s)⁻¹ =
      alpha xk w vk s * (vk s.toNNReal - v s.toNNReal) / gap w vk s ^ 3 * (w s.toNNReal - v s.toNNReal)⁻¹ := by
  have hα := (alpha_pos hxk w vk s).ne'
  rw [mobPath_sub hq hD, inv_div, rate]
  rcases eq_or_ne (w s.toNNReal - v s.toNNReal) 0 with h0 | h0
  · simp [h0]
  · field_simp

theorem IsSep.continuousOn_beta (h : IsSep w vk S) : ContinuousOn (beta xk w vk) (Icc 0 S) := by
  have := (h.ac_beta (xk := xk)).continuousOn
  rwa [uIcc_of_le h.nonneg] at this

theorem IsSep.continuousOn_mobPath (h : IsSep w vk S) (hvc : ContinuousOn (fun s : ℝ => v s.toNNReal) (Icc 0 S))
    (hD : ∀ s ∈ Icc 0 S, vk s.toNNReal - v s.toNNReal ≠ 0) : ContinuousOn (mobPath xk w vk v) (Icc 0 S) :=
  h.continuousOn_beta.add (h.continuousOn_alpha.div (h.cont_vk.sub hvc) hD)

theorem IsSep.continuousOn_mobPath_w (h : IsSep w vk S) : ContinuousOn (mobPath xk w vk w) (Icc 0 S) :=
  h.continuousOn_mobPath h.cont_w fun _ hs => h.gap_ne hs

/-- **Integrability of the new reciprocal gaps.** -/
theorem intervalIntegrable_newPath_inv (h : SepUpTo w vk T) (hxk : 0 < xk) (hv : IsMarkUpTo w vk v x T)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    IntervalIntegrable (fun r : ℝ => (newPath xk w vk (mobPath xk w vk w) r.toNNReal -
      newPath xk w vk (mobPath xk w vk v) r.toNNReal)⁻¹) volume 0 u := by
  obtain ⟨S, hST, hR, -, hmem, hclk⟩ := newTime_spec h hxk hu
  set S₀ := invClk (rate xk w vk) u with hS₀
  have hR0 : IsRate (rate xk w vk) S₀ := hR.mono hmem.1 hmem.2
  have hS₀T : ((S₀.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hmem.2) hST
  have hsep : IsSep w vk S₀ := h S₀ hmem.1 hS₀T
  have hD : ∀ s ∈ Icc 0 S₀, vk s.toNNReal - v s.toNNReal ≠ 0 := fun s hs =>
    sub_ne_zero.2 (hv.ne _ (lt_of_mem_Icc hS₀T hs)).symm
  rw [← hclk, hR0.intervalIntegrable_clk_iff]
  have hvc := continuousOn_real_of_lt hv.cont hS₀T
  have hc : ContinuousOn (fun s => alpha xk w vk s * (vk s.toNNReal - v s.toNNReal) / gap w vk s ^ 3)
      (uIcc 0 S₀) := by
    rw [uIcc_of_le hmem.1]
    exact (hsep.continuousOn_alpha.mul (hsep.cont_vk.sub hvc)).div (hsep.continuousOn_gap.pow 3)
      fun s hs => pow_ne_zero 3 (hsep.gap_ne hs)
  have hi := hv.integrable _ hS₀T
  rw [Real.coe_toNNReal _ hmem.1] at hi
  refine (hi.continuousOn_mul hc).congr fun s hs => ?_
  have hs' : s ∈ Icc 0 S₀ := by
    rw [uIoc_of_le hmem.1] at hs; exact Ioc_subset_Icc_self hs
  rw [newPath_clk hR0 _ hs', newPath_clk hR0 _ hs',
    rate_mul_inv_mobPath_sub hxk (hsep.gap_ne hs') (hD s hs')]

/-- **The new collision sets are Lebesgue-null.** -/
theorem volume_newCollision (h : SepUpTo w vk T) (hxk : 0 < xk) (hv : IsMarkUpTo w vk v x T) :
    volume {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < newHorizon xk w vk T ∧
      newPath xk w vk (mobPath xk w vk w) r.toNNReal = newPath xk w vk (mobPath xk w vk v) r.toNNReal} = 0 := by
  set O : Set ℝ := {s | 0 < s ∧ ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < T} with hO
  set C₀ : Set ℝ := {s | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = v s.toNNReal} with hC₀
  have hdiff : DifferentiableOn ℝ (clk (rate xk w vk)) (C₀ ∩ O) := by
    intro s hs
    obtain ⟨S', hsS', hS'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs.2.2
    have hR := (h.isSep_of_lt hS'T).isRate hxk
    have hlt : s < S' := by
      have := hsS'
      rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hs.2.1.le] at this
      exact this
    exact (hR.hasDerivAt_clk ⟨hs.2.1, hlt⟩).differentiableAt.differentiableWithinAt
  have hnull : volume (clk (rate xk w vk) '' (C₀ ∩ O)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff
      (measure_mono_null inter_subset_left hv.collision)
  refine measure_mono_null (t := {0} ∪ clk (rate xk w vk) '' (C₀ ∩ O)) ?_
    (measure_union_null (measure_singleton 0) hnull)
  rintro r ⟨hr0, hrT, hreq⟩
  rcases hr0.eq_or_lt with h0 | hpos
  · exact Or.inl h0.symm
  refine Or.inr ?_
  obtain ⟨S, hST, hR, hu', hmem, hclk⟩ := newTime_spec h hxk hrT
  rw [Real.coe_toNNReal _ hr0] at hu' hmem hclk
  have hs := hR.invClk_mem_Ioo ⟨hpos, hu'⟩
  set s := invClk (rate xk w vk) r with hsdef
  have hsT : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2.le) hST
  refine ⟨s, ⟨⟨hs.1.le, hsT, ?_⟩, hs.1, hsT⟩, hclk⟩
  have hsep : IsSep w vk S := h.isSep_of_lt hST
  have hsI : s ∈ Icc 0 (S : ℝ) := Ioo_subset_Icc_self hs
  have hD : vk s.toNNReal - v s.toNNReal ≠ 0 := sub_ne_zero.2 (hv.ne _ hsT).symm
  have heq : mobPath xk w vk w s - mobPath xk w vk v s = 0 := by
    simp only [newPath, Real.coe_toNNReal _ hr0] at hreq
    rw [hreq, sub_self]
  rw [mobPath_sub (hsep.gap_ne hsI) hD] at heq
  have hα := (alpha_pos hxk w vk s).ne'
  rcases div_eq_zero_iff.1 heq with h1 | h1
  · exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hα)
  · exact absurd h1 (mul_ne_zero (hsep.gap_ne hsI) hD)

/-- **Continuity in the new clock** of a path continuous on every `[0, S]`, `S < T`. -/
theorem continuousOn_newPath (h : SepUpTo w vk T) (hxk : 0 < xk) {F : ℝ → ℝ}
    (hF : ∀ S : ℝ≥0, (S : ℝ≥0∞) < T → ContinuousOn F (Icc 0 S)) :
    ContinuousOn (newPath xk w vk F) {u | (u : ℝ≥0∞) < newHorizon xk w vk T} := by
  intro u₀ hu₀
  obtain ⟨S, hST, hR, hu₀', -, -⟩ := newTime_spec h hxk hu₀
  have hc : ContinuousOn (fun u : ℝ≥0 => F (invClk (rate xk w vk) u)) {u : ℝ≥0 | (u : ℝ) < clk (rate xk w vk) S} :=
    (hF S hST).comp (hR.continuousOn_invClk.comp NNReal.continuous_coe.continuousOn
      fun u hu => ⟨u.coe_nonneg, (show (u : ℝ) < _ from hu).le⟩)
      fun u hu => hR.invClk_mem ⟨u.coe_nonneg, (show (u : ℝ) < _ from hu).le⟩
  exact (hc.continuousAt ((isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hu₀')).continuousWithinAt

/-! ### The old target in the new clock -/

theorem invClk_zero_eq (σ : ℝ → ℝ) : invClk σ 0 = 0 := by
  have h : IsLeast {s : ℝ | 0 ≤ s ∧ (0 : ℝ) ≤ clk σ s} 0 := ⟨⟨le_rfl, by simp⟩, fun _ hs => hs.1⟩
  exact h.csInf_eq

@[simp] theorem newPath_zero (F : ℝ → ℝ) : newPath xk w vk F 0 = F 0 := by
  simp [newPath, invClk_zero_eq]

/-- `M(w) − β = α/q > 0` before `T`. -/
theorem mobPath_w_sub_beta (hxk : 0 < xk) {s : ℝ} (hq : 0 < gap w vk s) :
    0 < mobPath xk w vk w s - beta xk w vk s := by
  rw [mobPath, mob_w, add_sub_cancel_left]
  exact div_pos (alpha_pos hxk w vk s) hq

/-- **The driver never meets the old target** before `T̃`. -/
theorem newPath_w_ne_beta (h : SepUpTo w vk T) (hxk : 0 < xk) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    newPath xk w vk (mobPath xk w vk w) u ≠ newPath xk w vk (beta xk w vk) u := by
  obtain ⟨S, hST, -, -, hmem, -⟩ := newTime_spec h hxk hu
  have := mobPath_w_sub_beta hxk ((h.isSep_of_lt hST).pos _ hmem)
  simp only [newPath]
  linarith

/-- **Integrability of the new reciprocal gap to the old target.** -/
theorem intervalIntegrable_newPath_beta_inv (h : SepUpTo w vk T) (hxk : 0 < xk) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    IntervalIntegrable (fun r : ℝ => (newPath xk w vk (mobPath xk w vk w) r.toNNReal -
      newPath xk w vk (beta xk w vk) r.toNNReal)⁻¹) volume 0 u := by
  obtain ⟨S, hST, hR, -, hmem, hclk⟩ := newTime_spec h hxk hu
  set S₀ := invClk (rate xk w vk) u with hS₀
  have hR0 : IsRate (rate xk w vk) S₀ := hR.mono hmem.1 hmem.2
  have hsep : IsSep w vk S₀ := (h.isSep_of_lt hST).mono hmem.1 hmem.2
  rw [← hclk, hR0.intervalIntegrable_clk_iff]
  have hc : ContinuousOn (fun s => alpha xk w vk s / gap w vk s ^ 3) (uIcc 0 S₀) := by
    rw [uIcc_of_le hmem.1]; exact hsep.continuousOn_alpha_div
  refine hc.intervalIntegrable.congr fun s hs => ?_
  have hs' : s ∈ Icc 0 S₀ := by
    rw [uIoc_of_le hmem.1] at hs; exact Ioc_subset_Icc_self hs
  have hq := hsep.gap_ne hs'
  have hα := (alpha_pos hxk w vk s).ne'
  rw [newPath_clk hR0 _ hs', newPath_clk hR0 _ hs', mobPath, mob_w, add_sub_cancel_left, rate]
  field_simp

end Retarget

end Zhan

end InteractingSLE
