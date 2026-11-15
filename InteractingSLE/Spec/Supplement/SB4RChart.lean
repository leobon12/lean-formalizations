/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.Reflect
import InteractingSLE.Spec.Supplement.SB2JRight

/-!
# The reflected entry chart of SB4's sewing frame

Packet PROVE-T14-SB4LEAF. SB4's sewing frame (`Retain.RetainedTailFrame`) reads the retained upper history `A` in the
reflected plane, where SB2(2)'s right entry prime end over `R = max (A ∩ ℝ)` becomes a left entry prime end over
`−R` (supplement p. 631: "Use S2, reflected for the second assertion"). This file reflects charts through the
imaginary axis, `ρ(z) = −z̄` (`Supp9B.refl`):

* `reflChart`: `(ρ ∘ fwd ∘ ρ, ρ ∘ inv ∘ ρ, −lift ∘ ρ)`;
* `IsDomainChart.reflChart`, `IsDomainChart.recenter`;
* **`IsRightEntryChart.reflChart`**: a right entry chart of `A` at `R` reflects to a left entry chart of `ρ(A)` at
  `−R`;
* **`isRightEntryChart_recenter`**: a domain chart of `ℍ \ fill A` with right entry value `a` at `R`, sending `∞` to
  `∞` and with zero lift right of `R`, recentred at `a` is a right entry chart;
* `tendsto_runChart_lift_zero_right` (mirror of `Lw.tendsto_runChart_lift_zero`);
* `realMin_refl_image`: `min (ρ(A) ∩ ℝ) = −max (A ∩ ℝ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B

theorem refl_eq_reflectC : (refl : ℂ → ℂ) = LP.reflectC := rfl

theorem refl_mem_H {z : ℂ} (hz : z ∈ H) : refl z ∈ H := by
  show 0 < (refl z).im
  rw [refl_im]; exact hz

theorem refl_image_H : refl '' H = H := LP.reflectC_image_H

theorem refl_ofReal (x : ℝ) : refl (x : ℂ) = ((-x : ℝ) : ℂ) := LP.reflectC_ofReal x

theorem norm_refl (z : ℂ) : ‖refl z‖ = ‖z‖ := by simp [Supp9B.refl]

theorem tendsto_refl_nhdsWithin_H (z : ℂ) : Tendsto refl (𝓝[H] z) (𝓝[H] (refl z)) :=
  tendsto_nhdsWithin_iff.2 ⟨continuous_refl.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hw => refl_mem_H hw⟩

theorem tendsto_refl_cobounded : Tendsto refl (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa only [norm_refl] using tendsto_norm_cobounded_atTop

/-! ### Derivatives under the reflection -/

/-- `ρ ∘ F ∘ ρ` has derivative `conj F'` at `z` when `F` has derivative `F'` at `ρ z`. -/
theorem hasDerivAt_refl_comp {F : ℂ → ℂ} {F' z : ℂ} (hF : HasDerivAt F F' (refl z)) :
    HasDerivAt (fun w => refl (F (refl w))) (conj F') z := by
  have h1 : HasDerivAt (fun v => F (-v)) (-F') (conj z) := by
    have hF' : HasDerivAt F F' (-(conj z)) := hF
    have := hF'.comp (conj z) (hasDerivAt_neg (conj z))
    simpa [Function.comp_def] using this
  have h2 := h1.conj_conj
  rw [Complex.conj_conj] at h2
  have h3 := h2.neg
  have hd : -(conj (-F')) = conj F' := by simp
  rw [hd] at h3
  exact h3.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)

theorem differentiableAt_refl_comp {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℂ F (refl z)) :
    DifferentiableAt ℂ (fun w => refl (F (refl w))) z :=
  (hasDerivAt_refl_comp hF.hasDerivAt).differentiableAt

theorem deriv_refl_comp {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℂ F (refl z)) :
    deriv (fun w => refl (F (refl w))) z = conj (deriv F (refl z)) :=
  (hasDerivAt_refl_comp hF.hasDerivAt).deriv

/-- The conjugate `conj ∘ L ∘ ρ` of a holomorphic function is holomorphic. -/
theorem differentiableAt_conj_comp_refl {L : ℂ → ℂ} {z : ℂ} (hL : DifferentiableAt ℂ L (refl z)) :
    DifferentiableAt ℂ (fun w => conj (L (refl w))) z := by
  have h := differentiableAt_refl_comp (F := fun v => -L v) (z := z) hL.neg
  have he : (fun w => conj (L (Supp9B.refl w))) = fun w => Supp9B.refl ((fun v => -L v) (Supp9B.refl w)) := by
    funext w; simp [Supp9B.refl]
  rw [he]; exact h

/-! ### The reflected chart -/

/-- **The chart reflected through the imaginary axis.** -/
def reflChart (c : Chart) : Chart :=
  (fun z => refl (c.1 (refl z)), fun w => refl (c.2.1 (refl w)), fun z => -c.2.2 (refl z))

@[simp] theorem reflChart_fwd (c : Chart) (z : ℂ) : (reflChart c).1 z = refl (c.1 (refl z)) := rfl

@[simp] theorem reflChart_inv (c : Chart) (w : ℂ) : (reflChart c).2.1 w = refl (c.2.1 (refl w)) := rfl

@[simp] theorem reflChart_lift (c : Chart) (z : ℂ) : (reflChart c).2.2 z = -c.2.2 (refl z) := rfl

theorem isConformal_reflChart {c : Chart} (hc : c.IsConformal) : (reflChart c).IsConformal := by
  obtain ⟨hd, hmaps, hinv⟩ := hc
  refine ⟨fun w hw => ?_, fun w hw => refl_mem_H (hmaps (refl_mem_H hw)), fun w hw => ?_⟩
  · have hdw : DifferentiableAt ℂ c.2.1 (refl w) :=
      (hd _ (refl_mem_H hw)).differentiableAt (QuantumZipper.isOpen_H.mem_nhds (refl_mem_H hw))
    exact (differentiableAt_refl_comp hdw).differentiableWithinAt
  · simp only [reflChart_fwd, reflChart_inv, refl_refl]
    rw [hinv _ (refl_mem_H hw), refl_refl]

theorem refl_image_refl_image (S : Set ℂ) : refl '' (refl '' S) = S := by
  rw [image_image]; simp

/-- **A domain chart reflects to a domain chart of the reflected domain.** -/
theorem isDomainChart_reflChart {D : Set ℂ} {c : Chart} (hc : IsDomainChart D c) :
    IsDomainChart (refl '' D) (reflChart c) := by
  obtain ⟨hconf, himg, L, ⟨hLd, hLe⟩, hlift⟩ := hc
  have hD : ∀ z ∈ refl '' D, refl z ∈ D := by
    rintro _ ⟨z, hz, rfl⟩; rwa [refl_refl]
  have hDo : IsOpen D := himg ▸ hconf.isOpen_image
  refine ⟨isConformal_reflChart hconf, ?_, fun z => conj (L (refl z)), ⟨?_, ?_⟩, ?_⟩
  · have : (reflChart c).2.1 '' H = refl '' (c.2.1 '' (refl '' H)) := by
      ext z; simp only [mem_image, reflChart_inv]
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
    rw [this, refl_image_H, himg]
  · intro z hz
    have hLz : DifferentiableAt ℂ L (refl z) :=
      (hLd _ (hD z hz)).differentiableAt (hDo.mem_nhds (hD z hz))
    exact (differentiableAt_conj_comp_refl hLz).differentiableWithinAt
  · intro z hz
    have hne : deriv c.1 (refl z) ≠ 0 := by rw [← hLe _ (hD z hz)]; exact Complex.exp_ne_zero _
    have hdz := differentiableAt_of_deriv_ne_zero hne
    rw [reflChart, deriv_refl_comp hdz, ← hLe _ (hD z hz), ← Complex.exp_conj]
  · intro z hz
    simp only [reflChart_lift, Complex.conj_im]
    rw [hlift (hD z hz)]

/-- Recentring keeps a domain chart. -/
theorem isDomainChart_recenter {D : Set ℂ} {c : Chart} (hc : IsDomainChart D c) (a : ℝ) :
    IsDomainChart D (c.recenter a) := by
  have hHa : ∀ w : ℂ, w ∈ H → w + a ∈ H := fun w hw => (Lw.add_real_mem_H_iff a).2 hw
  obtain ⟨⟨hdiff, hmaps, hinv⟩, himg, L, ⟨hLd, hLe⟩, hlift⟩ := hc
  refine ⟨⟨?_, fun w hw => hmaps (hHa w hw), fun w hw => ?_⟩, ?_, L, ⟨hLd, fun z hz => ?_⟩, hlift⟩
  · show DifferentiableOn ℂ (fun w => c.2.1 (w + a)) H
    exact hdiff.comp (differentiableOn_id.add_const _) fun w hw => hHa w hw
  · show c.1 (c.2.1 (w + a)) - a = w
    rw [hinv _ (hHa w hw), add_sub_cancel_right]
  · rw [← himg]
    ext z
    simp only [Chart.recenter, mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w + a, hHa w hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w - a, ?_, by simp⟩
      simpa [sub_eq_add_neg] using (Lw.add_real_mem_H_iff (-a)).2 hw
  · show exp (L z) = deriv (fun z => c.1 z - a) z
    rw [deriv_sub_const, hLe z hz]

/-! ### Entry charts -/

/-- **A right entry chart reflects to a left entry chart.** -/
theorem isLeftEntryChart_reflChart {A : Set ℂ} {R : ℝ} {c : Chart} (hc : IsRightEntryChart A R c) :
    IsLeftEntryChart (refl '' A) (-R) (reflChart c) := by
  obtain ⟨hD, ⟨e, he, hlim⟩, hcob, hlift⟩ := hc
  have hdom : H \ fillH (refl '' A) = refl '' (H \ fillH A) := by
    rw [refl_eq_reflectC]; exact LP.H_diff_fillH_image_reflectC A
  refine ⟨hdom ▸ isDomainChart_reflChart hD, ⟨fun x => -e (-x), fun x hx => ?_, ?_⟩, ?_, fun x hx => ?_⟩
  · have hr := tendsto_refl_nhdsWithin_H (x : ℂ)
    rw [refl_ofReal] at hr
    have h1 := (he (-x) (by linarith)).comp hr
    have h2 := (continuous_refl.tendsto _).comp h1
    rw [refl_ofReal] at h2
    exact h2
  · have hn : Tendsto (fun x : ℝ => -x) (𝓝[<] (-R)) (𝓝[>] R) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      · have := ((continuous_neg (G := ℝ)).tendsto (-R)).mono_left (nhdsWithin_le_nhds (s := Iio (-R)))
        simpa using this
      · have : x < -R := hx
        show R < -x
        linarith
    have h1 := hlim.comp hn
    simpa using h1.neg
  · have hmaps : Tendsto refl (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH (refl '' A)))
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) := by
      refine tendsto_inf.2 ⟨tendsto_refl_cobounded.mono_left inf_le_left,
        (tendsto_principal_principal.2 fun z hz => ?_).mono_left inf_le_right⟩
      rw [hdom] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rwa [refl_refl]
    exact tendsto_refl_cobounded.comp (hcob.comp hmaps)
  · have hr := tendsto_refl_nhdsWithin_H (x : ℂ)
    rw [refl_ofReal] at hr
    have h1 := (hlift (-x) (by linarith)).comp hr
    have h2 := h1.neg
    rw [neg_zero] at h2
    exact h2

/-- **A recentred domain chart with a right entry value is a right entry chart.** -/
theorem isRightEntryChart_recenter {A : Set ℂ} {R a : ℝ} {c : Chart} (hD : IsDomainChart (H \ fillH A) c)
    (hv : Lx.IsRightEntryValue c R a)
    (hcob : Tendsto c.1 (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (Bornology.cobounded ℂ))
    (hlift : ∀ x > R, Tendsto c.2.2 (𝓝[H] (x : ℂ)) (𝓝 0)) :
    IsRightEntryChart A R (c.recenter a) := by
  obtain ⟨e, he, hlim⟩ := hv
  refine ⟨isDomainChart_recenter hD a, ⟨fun x => e x - a, fun x hx => ?_, ?_⟩, ?_, hlift⟩
  · have := (he x hx).sub_const (a : ℂ)
    push_cast
    exact this
  · simpa using hlim.sub_const a
  · have h := Lw.tendsto_add_cobounded (-(a : ℂ)) le_rfl
    exact (h.comp hcob).congr fun z => by simp [Chart.recenter, sub_eq_add_neg]

/-! ### Run charts -/

open Exist.StagedLaw in
/-- **The run chart's lift tends to `0` right of every real point** of a compact `A` with the prefix's fill (mirror of
`Lw.tendsto_runChart_lift_zero`). -/
theorem tendsto_runChart_lift_zero_right {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {x : ℝ}
    (hx : ∀ y : ℝ, (y : ℂ) ∈ A → y < x) :
    Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.2 (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨M, hK⟩ := Lw.exists_hullModel_fill spec D hreg n hnot
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D n (fun j _ => hreg j)
  obtain ⟨ρ, hρ, hd⟩ := Lx.exists_ball_disjoint_fillH_right hAc hx
  rw [hAf, ← hK] at hd
  exact M.tendsto_lift_zero hN hρ hd le_rfl

/-! ### Real extremes under the reflection -/

theorem realMin_refl_image (A : Set ℂ) : realMin (refl '' A) = -realMax A := by
  have hset : {x : ℝ | (x : ℂ) ∈ refl '' A} = -{x : ℝ | (x : ℂ) ∈ A} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_neg]
    constructor
    · rintro ⟨z, hz, hzx⟩
      have : z = ((-x : ℝ) : ℂ) := by rw [← refl_refl z, hzx, refl_ofReal]
      rwa [this] at hz
    · intro hx
      exact ⟨((-x : ℝ) : ℂ), hx, by rw [refl_ofReal, neg_neg]⟩
  unfold realMin realMax
  rw [hset, Real.sInf_neg]

theorem realMax_refl_image (A : Set ℂ) : realMax (refl '' A) = -realMin A := by
  have h := realMin_refl_image (refl '' A)
  rw [refl_image_refl_image] at h
  linarith

end InteractingSLE.Theorem14.SB.Lf
