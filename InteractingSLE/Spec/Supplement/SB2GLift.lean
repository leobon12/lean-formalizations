/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PieceRun
import InteractingSLE.Spec.Supplement.GW2aContStepAux
import InteractingSLE.Spec.Supplement.WalkSideDom
import InteractingSLE.Spec.Supplement.BHMeanReal
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc

/-!
# Run charts: the lift tends to `0` at every free real point (the route to `hliftR`)

Packet PROVE-T14-SB2FIN2 (Theorem 1.4's SB2, item 2: `hliftR`). For the chart `c` of a run (the recentred identity
followed by real recentrings and centred Loewner stages after regular pieces), the lift `c.2.2` tends to `0` at every
real point `y` near which `ℍ` lies in the chart's domain (`LiftRealOn`). This is `hliftR` for SB2(1)'s left entry chart
in launch form, which is a recentred launch chart of the lower walk (`hliftR_of_liftRealOn`).

* `notMem_image_of_tendsto_inv`: for a conformal chart, a boundary limit of the inverse at a real point is not a value
  of the inverse on `ℍ` (apply the forward map: it would send the real point into `ℍ`);
* **`exists_tendsto_fwd_of_free`**: at a free real point the forward map of a conformal chart with a proper boundary
  extension (`GW1P.HasProperBdryExt`) has a real limit `x`, and the inverse tends back to `y` at `x` (Yuan's cluster-set
  lemma, filter form);
* `notMem_closure_fwdHull_of_free`: if `y` is free for `c.loewner W T`, then `x` is off the closed stage hull;
* **`liftRealOn_loewner`**: `lift' = Im (log f_T′) ∘ fwd + lift`, both terms tend to `0` (`(CA2)`,
  `BHMean.tendsto_im_logDerivFwd_of_notMem_closure`); `liftRealOn_recenter`, `liftRealOn_id_recenter`;
* **`liftRealOn_runChart`**: induction along the run (as `GW1P.isClosed_pieces_run`);
* **`hliftR_of_liftRealOn`**: the `hliftR` form for a domain chart of `ℍ ∖ fill A`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.SB.FinRel

/-- **The lift tends to `0` at every free real point** of the chart's domain. -/
def LiftRealOn (c : Chart) : Prop :=
  ∀ y : ℝ, (∃ ε > 0, ball (y : ℂ) ε ∩ H ⊆ c.dom) → Tendsto c.2.2 (𝓝[(c.dom : Set ℂ)] (y : ℂ)) (𝓝 0)

section Step

variable {c : Chart}

/-- For a conformal chart, a boundary limit of the inverse at a real point is not a value of the inverse on `ℍ`. -/
theorem notMem_image_of_tendsto_inv (hc : c.IsConformal) {x : ℝ} {p : ℂ}
    (hp : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) : p ∉ c.2.1 '' H := by
  rintro ⟨v, hv, rfl⟩
  have hvd : c.2.1 v ∈ c.dom := hc.inv_mem_dom hv
  have hcont : ContinuousAt c.1 (c.2.1 v) :=
    (hc.differentiableOn_fwd _ hvd).differentiableAt (c.dom.isOpen.mem_nhds hvd) |>.continuousAt
  have h1 : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 v) := by
    have := hcont.tendsto.comp hp
    rwa [hc.2.2 v hv] at this
  have h2 : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hc.2.2 z hz).symm)
  have hne : (𝓝[H] (x : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
  have he := tendsto_nhds_unique h1 h2
  have : (0 : ℝ) < v.im := hv
  rw [he, ofReal_im] at this
  exact lt_irrefl _ this

/-- **The forward map lands at a free real point**: it has a real limit `x`, and the inverse tends back to `y` at
`x`. -/
theorem exists_tendsto_fwd_of_free (hc : c.IsConformal) (hP : GW1P.HasProperBdryExt c) {y : ℝ} {ε : ℝ}
    (hε : 0 < ε) (hsub : ball (y : ℂ) ε ∩ H ⊆ c.dom) :
    ∃ x : ℝ, Tendsto c.1 (𝓝[(c.dom : Set ℂ)] (y : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) := by
  obtain ⟨f, C, hf, hC⟩ := hP
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  have hfH : EqOn f c.2.1 H := fun p hp => by
    have hne : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hp)
    have hcont : ContinuousAt c.2.1 p :=
      (hc.1 p hp).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hp) |>.continuousAt
    exact tendsto_nhds_unique (hf p (QuantumZipper.H_subset_Hbar hp))
      (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have hd : DifferentiableOn ℂ f H := hc.1.congr fun z hz => hfH hz
  have hinj : InjOn f H := fun w₁ h₁ w₂ h₂ he => hc.injOn h₁ h₂ (by rwa [hfH h₁, hfH h₂] at he)
  have hR : ∀ x : ℂ, x.im = 0 → f x ∉ f '' H := by
    intro x hx hmem
    have hxr : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [hx])
    rw [image_congr fun z hz => hfH hz] at hmem
    have hlim := hf x (show (0 : ℝ) ≤ x.im by rw [hx])
    rw [hxr] at hlim hmem
    exact notMem_image_of_tendsto_inv hc hlim hmem
  have hyH : ∀ δ > 0, ((y : ℂ) + ((min δ ε / 2 : ℝ) : ℂ) * I) ∈ ball (y : ℂ) (min δ ε) ∩ H := by
    intro δ hδ
    have hm : 0 < min δ ε := lt_min hδ hε
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    · show 0 < ((y : ℂ) + ((min δ ε / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
      positivity
  have hcl : (y : ℂ) ∈ closure (c.dom : Set ℂ) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    refine ⟨_, hsub ⟨ball_subset_ball (min_le_right _ _) (hyH δ hδ).1, (hyH δ hδ).2⟩, ?_⟩
    rw [← mem_ball']
    exact ball_subset_ball (min_le_left _ _) (hyH δ hδ).1
  have hne : (𝓝[(c.dom : Set ℂ)] (y : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hconn : ∀ U ∈ 𝓝[(c.dom : Set ℂ)] (y : ℂ), ∃ S ∈ 𝓝[(c.dom : Set ℂ)] (y : ℂ), S ⊆ U ∧ IsPreconnected S ∧
      ContinuousOn c.1 S := by
    intro U hU
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    set S := ball (y : ℂ) (min δ ε) ∩ H with hS
    have hSdom : S ⊆ c.dom := fun z hz => hsub ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩
    refine ⟨S, ?_, fun z hz => hδU ⟨ball_subset_ball (min_le_left _ _) hz.1, hSdom hz⟩,
      HalfPlaneSep.isPreconnected_ball_inter_H _ _, hc.differentiableOn_fwd.continuousOn.mono hSdom⟩
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨ball (y : ℂ) (min δ ε), ball_mem_nhds _ (lt_min hδ hε),
      fun z hz => ⟨hz.1, hc.dom_subset hz.2⟩⟩
  have hGH : ∀ᶠ w in 𝓝[(c.dom : Set ℂ)] (y : ℂ), c.1 w ∈ Hbar :=
    eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.H_subset_Hbar (hc.fwd_mem hw)
  have hGR : ∀ᶠ w in 𝓝[(c.dom : Set ℂ)] (y : ℂ), ‖c.1 w‖ ≤ ‖(y : ℂ)‖ + 1 + C := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (y : ℂ) one_pos)] with w hw hwb
    have h1 := hC _ (QuantumZipper.H_subset_Hbar (hc.fwd_mem hw))
    rw [hfH (hc.fwd_mem hw), hc.inv_fwd hw] at h1
    have h2 : ‖w‖ ≤ ‖(y : ℂ)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' w (y : ℂ)
      rw [mem_ball, dist_eq_norm] at hwb
      linarith
    have h3 := norm_sub_norm_le (c.1 w) w
    rw [norm_sub_rev] at h1
    linarith
  have hFG : Tendsto (fun w => f (c.1 w)) (𝓝[(c.dom : Set ℂ)] (y : ℂ)) (𝓝 (y : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun w hw => by
      show w = f (c.1 w)
      rw [hfH (hc.fwd_mem hw), hc.inv_fwd hw])
  obtain ⟨ξ, hξ, hfξ, hGξ⟩ :=
    YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter hd hfc hinj hR hconn hGH hGR hFG
  have hξim : ξ.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hξ
    have h1 : f ξ ∈ H := by rw [hfH hpos]; exact hc.2.1 hpos
    rw [hfξ] at h1
    have h2 : (0 : ℝ) < ((y : ℂ)).im := h1
    rw [ofReal_im] at h2
    exact lt_irrefl _ h2
  have hξr : ξ = (ξ.re : ℂ) := Complex.ext (by simp) (by simp [hξim])
  refine ⟨ξ.re, by rw [← hξr]; exact hGξ, ?_⟩
  rw [← hξr, ← hfξ]
  exact hf ξ hξ

/-- If `y` is free for `c.loewner W T` and the inverse of `c` tends to `y` at the real point `x`, then `x` is off the
closed stage hull: hull points near `x` would be carried by the inverse into the new domain. -/
theorem notMem_closure_fwdHull_of_free (hc : c.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) {y ε : ℝ} (hε : 0 < ε) (hsub : ball (y : ℂ) ε ∩ H ⊆ (c.loewner W T).dom) {x : ℝ}
    (hinv : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ))) : (x : ℂ) ∉ closure (fwdHull W T) := by
  intro hx
  have hKH : fwdHull W T ⊆ H := Exist.fwdHull_subset_H hT
  have hne : (𝓝[fwdHull W T] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have hev : ∀ᶠ w in 𝓝[fwdHull W T] (x : ℂ), c.2.1 w ∈ ball (y : ℂ) ε :=
    (hinv.mono_left (nhdsWithin_mono _ hKH)).eventually (ball_mem_nhds _ hε)
  obtain ⟨w, hwb, hwK⟩ := (hev.and self_mem_nhdsWithin).exists
  have hwH := hKH hwK
  have hmem := hsub ⟨hwb, hc.2.1 hwH⟩
  rw [(hc.loewner hW hW0 hT).coe_dom] at hmem
  obtain ⟨v, hv, hve⟩ := hmem
  have hvH := QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT hv
  have heq : fwdMapInv W T v = w := hc.injOn hvH hwH hve
  have hm : fwdMapInv W T v ∈ H \ fwdHull W T := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hT]; exact ⟨v, hv, rfl⟩
  rw [heq] at hm
  exact hm.2 hwK

/-- **A Loewner stage keeps the lift's boundary value `0` at free real points.** -/
theorem liftRealOn_loewner (hc : c.IsConformal) (hP : GW1P.HasProperBdryExt c) (hL : LiftRealOn c) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) : LiftRealOn (c.loewner W T) := by
  rintro y ⟨ε, hε, hsub⟩
  have hdsub : ((c.loewner W T).dom : Set ℂ) ⊆ c.dom := WalkSide.dom_loewner_subset hc hW hW0 hT
  have hsub' : ball (y : ℂ) ε ∩ H ⊆ c.dom := hsub.trans hdsub
  obtain ⟨x, hfx, hinv⟩ := exists_tendsto_fwd_of_free hc hP hε hsub'
  have hx := notMem_closure_fwdHull_of_free hc hW hW0 hT hε hsub hinv
  have h1 : Tendsto c.1 (𝓝[((c.loewner W T).dom : Set ℂ)] (y : ℂ)) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hfx.mono_left (nhdsWithin_mono _ hdsub),
      eventually_nhdsWithin_of_forall fun z hz => hc.fwd_mem (hdsub hz)⟩
  have h2 := (Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure hW hW0 hT hx).comp h1
  have h3 := (hL y ⟨ε, hε, hsub'⟩).mono_left (nhdsWithin_mono _ hdsub)
  have h4 := h2.add h3
  rw [add_zero] at h4
  exact h4

/-- A real recentring keeps the domain and the lift. -/
theorem liftRealOn_recenter (hL : LiftRealOn c) (a : ℝ) : LiftRealOn (c.recenter a) := by
  intro y hy
  rw [WalkSide.dom_recenter] at hy ⊢
  exact hL y hy

/-- The recentred identity chart has lift `0`. -/
theorem liftRealOn_id_recenter (a : ℝ) : LiftRealOn (Chart.id.recenter a) := fun _ _ => tendsto_const_nhds

/-- **`hliftR` from `LiftRealOn`** for a domain chart of `ℍ ∖ fill A`. -/
theorem hliftR_of_liftRealOn {A : Set ℂ} (hD : IsDomainChart (H \ fillH A) c) (hL : LiftRealOn c) :
    ∀ y : ℝ, (y : ℂ) ∉ closure (fillH A) → Tendsto c.2.2 (𝓝[H \ fillH A] (y : ℂ)) (𝓝 0) := by
  have hdom : (c.dom : Set ℂ) = H \ fillH A := by
    show interior (c.2.1 '' H) = H \ fillH A
    rw [hD.image_eq]
    exact hD.isOpen.interior_eq
  intro y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl (y : ℂ) hy
  have hsub : ball (y : ℂ) ε ∩ H ⊆ c.dom := by
    rw [hdom]
    exact fun z hz => ⟨hz.2, fun hzA => hball hz.1 (subset_closure hzA)⟩
  have h := hL y ⟨ε, hε, hsub⟩
  rwa [hdom] at h

end Step

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

open Exist.Staged Exist.StagedLaw GW2aCont in
/-- **The chart of a run whose launched pieces are regular has lift boundary value `0` at every free real point.** -/
theorem liftRealOn_runChart (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    LiftRealOn (ExplState.run κ b jumps spec D n).2.2.2.2.1 := by
  induction n with
  | zero => exact liftRealOn_id_recenter spec.1
  | succ n ih =>
    have hc := (isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n fun j _ => hreg j).1
    have hP := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [ha]
      exact liftRealOn_recenter ih a
    · have hr := hreg n c θ hl
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he]
      rcases eq_or_ne (min (instrTime spec n) (D n).2) ⊤ with htop | htop
      · rw [chart_launch_of_top _ _ _ _ _ htop]
        exact ih
      · rw [chart_launch _ _ _ _ _ htop]
        obtain ⟨hU, hU0⟩ := hr.continuous_stoppedReal
        exact liftRealOn_loewner hc hP ih hU hU0 (NNReal.coe_nonneg _)

end Run

end InteractingSLE.Theorem14.SB.FinRel
