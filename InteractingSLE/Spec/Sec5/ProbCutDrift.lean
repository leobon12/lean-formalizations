/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovCut

/-!
# Lemma 5.10: Girsanov's theorem for a time-dependent cut drift, continuous at almost every time

Packet PROVE-SEC5-B (specification §5.2, proof of Lemma 5.10, `source/spec/p097-144.md` L929–L947, and the
corrected crossing lemma, `source/spec/p433-480.md` §2.2, "Proof of the density bound").

The landed `Girsanov.girsanov_cutDrift` removes a drift `F(W_t, U_t)` with `F` continuous. Lemma 5.10 removes the
sum `U` of the force drifts other than the first right one, which is discontinuous where `W` collides with a mark
("use the integrated force convention at collisions"), and its proof also switches a one-force drift on at a fixed
time. This file proves the same theorem for a *time-dependent* integrand `F(t, W_t, U_t)` that is only measurable,
bounded, and continuous at `(t, W_t, U_t)` for almost every time before the cut, almost surely (the collision times
of an integrated evolution are Lebesgue-null):

* `cutDriftT`: the `limsup` of the left-point dyadic values of `1{t < τ} F(t, W_t, U_t)`, progressive;
* `cutDriftT_eq_of_lt`, `isRiemannRegular_cutDriftT`, `drift_cutDriftT_eq`;
* `girsanov_cutDriftT`: under `Q = Z_{T+1} · P`, `B + ∫₀^· θ` is a Brownian motion of the filtration and
  `B̃_t = B_t + ∫₀ᵗ F(s, W_s, U_s) ds` for `t ≤ τ`.

The proofs follow `Girsanov.GirsanovCut` (packet PROVE-SEC2-GIR) with pointwise continuity in place of global
continuity.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {m : ℕ}

/-- The time-dependent cut integrand `1{t < τ} F(t, W_t, U_t)` (killed coordinates). -/
def cutIntegrandT (τ ζ : Ω → ℝ≥0∞) (F : ℝ≥0 → ℝ → (Fin m → ℝ) → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < τ ω then F t (killed ζ W t ω) (fun j => killed ζ (U j) t ω) else 0

/-- The progressive time-dependent cut drift: the `limsup` of the left-point dyadic values of the cut
integrand. -/
def cutDriftT (τ ζ : Ω → ℝ≥0∞) (F : ℝ≥0 → ℝ → (Fin m → ℝ) → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limsup (fun n => cutIntegrandT τ ζ F W U (grid n (stepIdx n (t : ℝ))) ω) atTop

variable {τ ζ : Ω → ℝ≥0∞} {F : ℝ≥0 → ℝ → (Fin m → ℝ) → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {U : Fin m → ℝ≥0 → Ω → ℝ}

/-- `F` as a function of one variable `(t, w, u)`. -/
def uncurry3 (F : ℝ≥0 → ℝ → (Fin m → ℝ) → ℝ) : ℝ≥0 × ℝ × (Fin m → ℝ) → ℝ := fun p => F p.1 p.2.1 p.2.2

theorem measurable_comp_triple_aux {Ω' : Type*} [MeasurableSpace Ω'] {F : ℝ≥0 → ℝ → (Fin m → ℝ) → ℝ}
    (hF : Measurable (uncurry3 F)) (t : ℝ≥0) {f : Ω' → ℝ} {g : Fin m → Ω' → ℝ} (hf : Measurable f)
    (hg : ∀ j, Measurable (g j)) : Measurable fun ω => F t (f ω) (fun j => g j ω) :=
  hF.comp (measurable_const.prodMk (hf.prodMk (measurable_pi_iff.2 hg)))

theorem measurable_cutIntegrandT (hF : Measurable (uncurry3 F)) (hW : AdaptedBefore 𝓕 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (t : ℝ≥0) : Measurable[𝓕 t] (cutIntegrandT τ ζ F W U t) := by
  have hpair : Measurable[𝓕 t] fun ω => F t (killed ζ W t ω) (fun j => killed ζ (U j) t ω) :=
    @measurable_comp_triple_aux m Ω (𝓕 t) F hF t _ _ (measurable_killed hW t)
      (fun j => measurable_killed (hU j) t)
  have hset : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < τ ω} := by
    have := (hτ t).compl
    convert this using 1
    ext ω
    simp [not_le]
  exact Measurable.ite hset hpair measurable_const

theorem isStronglyProgressive_cutDriftT (hF : Measurable (uncurry3 F)) (hW : AdaptedBefore 𝓕 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) :
    IsStronglyProgressive 𝓕 (cutDriftT τ ζ F W U) := fun t =>
  (@measurable_limsup_gridEval_aux Ω (𝓕 t) t (cutIntegrandT τ ζ F W U)
    (fun s hs => (measurable_cutIntegrandT hF hW hU hτ s).mono (𝓕.mono hs) le_rfl)).stronglyMeasurable

theorem abs_cutIntegrandT_le {M : ℝ} (hFb : ∀ t w u, |F t w u| ≤ M) (t : ℝ≥0) (ω : Ω) :
    |cutIntegrandT τ ζ F W U t ω| ≤ M := by
  unfold cutIntegrandT
  split_ifs
  · exact hFb _ _ _
  · simpa using (abs_nonneg _).trans (hFb 0 0 0)

/-- If eventually `a ≤ x_n ≤ b` for a bounded sequence, its `limsup` lies in `[a, b]`. -/
theorem limsup_mem_Icc_of_eventually {x : ℕ → ℝ} {M a b : ℝ} (hM : ∀ n, |x n| ≤ M)
    (h : ∀ᶠ n in atTop, x n ∈ Icc a b) : limsup x atTop ∈ Icc a b := by
  have hb := fun n => abs_le.1 (hM n)
  constructor
  · refine le_limsup_of_le (isBoundedUnder_of ⟨M, fun n => (hb n).2⟩) fun c hc => ?_
    obtain ⟨n, hn1, hn2⟩ := (h.and hc).exists
    exact hn1.1.trans hn2
  · exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun n => (hb n).1)
      (h.mono fun n hn => hn.2)

theorem abs_cutDriftT_le {M : ℝ} (hFb : ∀ t w u, |F t w u| ≤ M) (t : ℝ≥0) (ω : Ω) :
    |cutDriftT τ ζ F W U t ω| ≤ M := by
  have hb := fun n => abs_cutIntegrandT_le (τ := τ) (ζ := ζ) (W := W) (U := U) hFb
    (grid n (stepIdx n (t : ℝ))) ω
  have := limsup_mem_Icc_of_eventually hb (Eventually.of_forall fun n => abs_le.1 (hb n))
  exact abs_le.2 this

theorem cutDriftT_eq_zero {t : ℝ≥0} {ω : Ω} (h : τ ω < t) : cutDriftT τ ζ F W U t ω = 0 := by
  have hev : ∀ᶠ n in atTop, τ ω < (grid n (stepIdx n (t : ℝ)) : ℝ≥0∞) :=
    ((ENNReal.tendsto_coe.2 (tendsto_grid_stepIdx t)).eventually (lt_mem_nhds h))
  have h0 : ∀ᶠ n in atTop, cutIntegrandT τ ζ F W U (grid n (stepIdx n (t : ℝ))) ω = 0 :=
    hev.mono fun n hn => by simp [cutIntegrandT, not_lt.2 hn.le]
  rw [cutDriftT, limsup_congr h0, limsup_const]

/-- The path `r ↦ F(r, W_r, U_r)` is continuous at every time `t < ζ` at which `F` is continuous. -/
theorem continuousAt_comp_path {ω : Ω}
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (htζ : (t : ℝ≥0∞) < ζ ω)
    (hFc : ContinuousAt (uncurry3 F) (t, W t ω, fun j => U j t ω)) :
    ContinuousAt (fun r => F r (W r ω) (fun j => U j r ω)) t := by
  have hW := tendsto_of_continuousOn_lt hWc htζ
  have hU := fun j => tendsto_of_continuousOn_lt (hUc j) htζ
  have hp : ContinuousAt (fun r : ℝ≥0 => (r, W r ω, fun j => U j r ω)) t :=
    continuousAt_id.prodMk (hW.prodMk (continuousAt_pi.2 hU))
  exact hFc.comp (f := fun r : ℝ≥0 => (r, W r ω, fun j => U j r ω)) hp

/-- Before `τ`, at a time where `F` is continuous, the cut drift is `F(t, W_t, U_t)`. -/
theorem cutDriftT_eq_of_lt {ω : Ω} (hτζ : τ ω ≤ ζ ω)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ ω) (hFc : ContinuousAt (uncurry3 F) (t, W t ω, fun j => U j t ω)) :
    cutDriftT τ ζ F W U t ω = F t (W t ω) (fun j => U j t ω) := by
  have hle : ∀ n, ((grid n (stepIdx n (t : ℝ)) : ℝ≥0) : ℝ≥0∞) < τ ω := fun n =>
    (ENNReal.coe_le_coe.2 (grid_stepIdx_le n t)).trans_lt ht
  have heq : ∀ n, cutIntegrandT τ ζ F W U (grid n (stepIdx n (t : ℝ))) ω
      = F (grid n (stepIdx n (t : ℝ))) (W (grid n (stepIdx n (t : ℝ))) ω)
          (fun j => U j (grid n (stepIdx n (t : ℝ))) ω) :=
    fun n => by
      simp only [cutIntegrandT, hle n, ↓reduceIte, killed_of_lt ((hle n).trans_le hτζ)]
  have htζ : (t : ℝ≥0∞) < ζ ω := ht.trans_le hτζ
  have hlim := (continuousAt_comp_path hWc hUc htζ hFc).tendsto.comp (tendsto_grid_stepIdx t)
  rw [cutDriftT, (hlim.congr fun n => (heq n).symm).limsup_eq]

/-- **Left-continuity of the cut drift** at a time `0 < u < τ` at which `F` is continuous. -/
theorem continuousWithinAt_cutDriftT {M : ℝ} (hFb : ∀ t w u, |F t w u| ≤ M) {ω : Ω}
    (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < τ ω) (hFc : ContinuousAt (uncurry3 F) (u, W u ω, fun j => U j u ω)) :
    ContinuousWithinAt (fun r => cutDriftT τ ζ F W U r ω) (Set.Iic u) u := by
  have huζ : (u : ℝ≥0∞) < ζ ω := hu.trans_le hτζ
  have hG := continuousAt_comp_path hWc hUc huζ hFc
  have hval_u := cutDriftT_eq_of_lt hτζ hWc hUc hu hFc
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  simp only [hval_u]
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hG (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {r} hr hrd => ?_⟩
  have hru : (r : ℝ≥0∞) ≤ u := ENNReal.coe_le_coe.2 hr
  -- eventually the grid points of `r` are within `δ` of `u`
  have hgr : Tendsto (fun n => grid n (stepIdx n (r : ℝ))) atTop (𝓝 r) := tendsto_grid_stepIdx r
  have hev : ∀ᶠ n in atTop, dist (grid n (stepIdx n (r : ℝ))) u < δ :=
    (hgr.eventually (Metric.ball_mem_nhds r (sub_pos.2 hrd))).mono fun n hn => by
      have := dist_triangle (grid n (stepIdx n (r : ℝ))) r u
      linarith
  have hval : ∀ᶠ n in atTop, cutIntegrandT τ ζ F W U (grid n (stepIdx n (r : ℝ))) ω ∈
      Icc (F u (W u ω) (fun j => U j u ω) - ε / 2) (F u (W u ω) (fun j => U j u ω) + ε / 2) := by
    refine hev.mono fun n hn => ?_
    have hgle : ((grid n (stepIdx n (r : ℝ)) : ℝ≥0) : ℝ≥0∞) < τ ω :=
      (ENNReal.coe_le_coe.2 (grid_stepIdx_le n r)).trans_lt (hru.trans_lt hu)
    have hd := hδG hn
    rw [Real.dist_eq] at hd
    simp only [cutIntegrandT, hgle, ↓reduceIte, killed_of_lt (hgle.trans_le hτζ)]
    constructor <;> linarith [abs_lt.1 hd]
  have hmem := limsup_mem_Icc_of_eventually
    (fun n => abs_cutIntegrandT_le (τ := τ) (ζ := ζ) (W := W) (U := U) hFb
      (grid n (stepIdx n (r : ℝ))) ω) hval
  rw [Real.dist_eq, abs_lt]
  simp only [cutDriftT] at hmem ⊢
  constructor <;> linarith [hmem.1, hmem.2]

/-- **Riemann regularity of the cut drift**: left-continuous at almost every time, almost surely, when `F`
is continuous along the path at almost every time before `τ`. -/
theorem isRiemannRegular_cutDriftT {M : ℝ} (hFb : ∀ t w u, |F t w u| ≤ M) (hτζ : ∀ ω, τ ω ≤ ζ ω)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hFc : ∀ᵐ ω ∂P, ∀ᵐ u ∂(volume : Measure ℝ), 0 < u → (u.toNNReal : ℝ≥0∞) < τ ω →
      ContinuousAt (uncurry3 F) (u.toNNReal, W u.toNNReal ω, fun j => U j u.toNNReal ω)) :
    IsRiemannRegular P (cutDriftT τ ζ F W U) := by
  filter_upwards [hcont, hFc] with ω ⟨hWc, hUc⟩ hFω
  filter_upwards [ae_ne_real (τ ω).toReal, hFω] with u hu hFu
  rcases le_or_gt u 0 with h0 | h0
  · have hI : Set.Iic u.toNNReal = {u.toNNReal} := by
      ext r
      simp only [Set.mem_Iic, Set.mem_singleton_iff, Real.toNNReal_of_nonpos h0, nonpos_iff_eq_zero]
    rw [hI]
    exact continuousWithinAt_singleton
  · set s := u.toNNReal
    have hs : (s : ℝ) = u := Real.coe_toNNReal _ h0.le
    rcases lt_trichotomy (s : ℝ≥0∞) (τ ω) with h | h | h
    · exact continuousWithinAt_cutDriftT hFb (hτζ ω) hWc hUc h (hFu h0 h)
    · exfalso
      apply hu
      rw [← h, ← hs, ENNReal.coe_toReal]
    · refine ContinuousAt.continuousWithinAt ?_
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [(isOpen_lt continuous_const ENNReal.continuous_coe).mem_nhds h] with r hr
      exact (cutDriftT_eq_zero hr).symm

/-- **The drift of the cut drift**: `∫₀ᵗ θ = ∫₀ᵗ F(s, W_s, U_s) ds` for `t ≤ τ`. -/
theorem drift_cutDriftT_eq {ω : Ω} (hτζ : τ ω ≤ ζ ω)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hFω : ∀ᵐ u ∂(volume : Measure ℝ), 0 < u → (u.toNNReal : ℝ≥0∞) < τ ω →
      ContinuousAt (uncurry3 F) (u.toNNReal, W u.toNNReal ω, fun j => U j u.toNNReal ω))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ τ ω) :
    drift (cutDriftT τ ζ F W U) t ω
      = ∫ s in (0 : ℝ)..(t : ℝ), F s.toNNReal (W s.toNNReal ω) (fun j => U j s.toNNReal ω) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real (t : ℝ), hFω] with s hst hFs hs
  rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
  have hlt : s < t := lt_of_le_of_ne hs.2 hst
  have h1 : (s.toNNReal : ℝ≥0∞) < τ ω := by
    refine lt_of_lt_of_le ?_ ht
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
    exact hlt
  exact cutDriftT_eq_of_lt hτζ hWc hUc h1 (hFs hs.1 h1)

/-- **Girsanov's theorem for a time-dependent cut drift continuous at almost every time.** Let `B` be a
Brownian motion of `𝓕`, `W`, `U` adapted before `ζ` and continuous on `[0, ζ)` almost surely, `F` measurable and
bounded by `M`, continuous along the path at almost every time before `τ`, almost surely, and `τ ≤ ζ ∧ T` a
stopping time. With `θ = cutDriftT τ ζ F W U` and `Q = Z_{T+1} · P`: `Q` is a probability measure equivalent to
`P`, `B̃ = B + ∫₀^· θ` is a Brownian motion of `𝓕` under `Q`, and almost surely
`B̃_t = B_t + ∫₀ᵗ F(s, W_s, U_s) ds` for every `t ≤ τ`. -/
theorem girsanov_cutDriftT [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBF : IsFilteredBrownianReal 𝓕 B P) (hF : Measurable (uncurry3 F)) {M : ℝ}
    (hFb : ∀ t w u, |F t w u| ≤ M) (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hFc : ∀ᵐ ω ∂P, ∀ᵐ u ∂(volume : Measure ℝ), 0 < u → (u.toNNReal : ℝ≥0∞) < τ ω →
      ContinuousAt (uncurry3 F) (u.toNNReal, W u.toNNReal ω, fun j => U j u.toNNReal ω)) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B (cutDriftT τ ζ F W U) (T + 1)) ∧
    IsFilteredBrownianReal 𝓕 (girsanovProcess B (cutDriftT τ ζ F W U))
      (girsanovMeasure P 𝓕 B (cutDriftT τ ζ F W U) (T + 1)) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      girsanovProcess B (cutDriftT τ ζ F W U) t ω
        = B t ω + ∫ s in (0 : ℝ)..(t : ℝ), F s.toNNReal (W s.toNNReal ω) (fun j => U j s.toNNReal ω) := by
  have hθ := isStronglyProgressive_cutDriftT hF hW hU hτ
  have hθb := abs_cutDriftT_le (τ := τ) (ζ := ζ) (W := W) (U := U) hFb
  have hθreg := isRiemannRegular_cutDriftT (P := P) hFb hτζ hcont hFc
  have hθT : ∀ t ω, T + 1 ≤ t → cutDriftT τ ζ F W U t ω = 0 := fun t ω ht => by
    refine cutDriftT_eq_zero ((hτT ω).trans_lt ?_)
    rw [ENNReal.coe_lt_coe]
    exact (lt_add_one T).trans_le ht
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  refine ⟨isEquivProbMeasure_girsanovMeasure (B := B) hθ.stronglyAdapted hθb hθreg _,
    isFilteredBrownianReal_girsanov hBF hθ hθb hθreg hθT, ?_⟩
  filter_upwards [hcont, hFc] with ω ⟨hWc, hUc⟩ hFω t ht
  rw [girsanovProcess, drift_cutDriftT_eq (hτζ ω) hWc hUc hFω ht]

end Sec5

end InteractingSLE
