/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftOrder
import InteractingSLE.Spec.Sec7.R5LiftPos

/-!
# Lemma R.5's common phase: the reflection at landings inside the pocket

Packet PROVE-R5-LIFT (round 3). The ambient transition `Φ = f_s ∘ old⁻¹` of a reference chart reflects with positive
derivative at every real coordinate `x` whose landing lies in an open set `C` with `old.dom = C ∩ (ℍ ∖ K_s)` (the
interior-visit references of R.5: `C` the pocket, `K_s` the ambient hull at the visit time):

* **`landing_notMem_dom`**: the landing of a real coordinate is not in the chart's domain;
* **`exists_pos_tendsto_deriv_of_landing_mem`**: near `x` every real coordinate lands in `C ∖ old.dom ⊆ K_s`, so `Φ`
  has a real limit there (R5-REFCHART's `R5Ref.exists_ambient_access`); `Φ` is holomorphic and injective on `ℍ` with
  values in `ℍ`; Schwarz reflection with the order-of-vanishing argument
  (`R5Lift.exists_pos_tendsto_deriv_of_reflect'`) gives `Φ′ → b > 0`;
* **`exists_int_common_pathwise'`**: the generic common-integer core of `R5LiftHull` with the reflection given in the
  derivative form (`IsAmbPosDeriv`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open PocketStop PocketTraversal Lemma71C PocketStopSide

/-- **The landing of a real coordinate is not in the chart's domain.** -/
theorem landing_notMem_dom {old : Chart} (hold : old.IsConformal) {u : ℝ} {p : ℂ}
    (hland : Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝 p)) : p ∉ (old.dom : Set ℂ) := by
  intro hp
  have hcont : ContinuousAt old.1 p :=
    (hold.differentiableOn_fwd.continuousOn).continuousAt (old.dom.isOpen.mem_nhds hp)
  have h1 : Tendsto (fun y => old.1 (old.2.1 y)) (𝓝[H] (u : ℂ)) (𝓝 (old.1 p)) := hcont.tendsto.comp hland
  have h2 : Tendsto (fun y : ℂ => y) (𝓝[H] (u : ℂ)) (𝓝 (old.1 p)) :=
    h1.congr' (eventually_nhdsWithin_of_forall fun y hy => hold.2.2 y hy)
  have := nhdsWithin_H_neBot u
  have hu : (u : ℂ) = old.1 p :=
    tendsto_nhds_unique ((tendsto_id (x := 𝓝 (u : ℂ))).mono_left nhdsWithin_le_nhds) h2
  have hpH : old.1 p ∈ H := hold.fwd_mem hp
  rw [← hu] at hpH
  exact absurd (show (0 : ℝ) < (u : ℂ).im from hpH) (by rw [ofReal_im]; exact lt_irrefl 0)

/-- **The positive reflected derivative at a landing inside the pocket.** Let `old` be a conformal chart whose inverse
extends continuously to `ℍ̄` (`Fo`), with `old.dom = C ∩ (ℍ ∖ K_s)` for an open `C ⊆ ℍ`, and `f_s` the Loewner map of a
continuous traced driver. If the landing `Fo x` of a real `x` lies in `C`, the ambient transition `f_s ∘ old⁻¹` has
derivative tending to some `b > 0` within `ℍ` at `x`. -/
theorem exists_pos_tendsto_deriv_of_landing_mem {old : Chart} (hold : old.IsConformal) {Fo : ℂ → ℂ}
    (hFo : EqOn Fo old.2.1 H) (hFoc : ContinuousOn Fo Hbar) {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hdom : (old.dom : Set ℂ) = C ∩ (H \ fwdHull W s)) {x : ℝ} (hx : Fo x ∈ C) :
    ∃ b : ℝ, 0 < b ∧ Tendsto (deriv fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
  have hK : (old.dom : Set ℂ) ⊆ H \ fwdHull W s := by rw [hdom]; exact inter_subset_right
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
  -- a disc about `x` whose closed upper half lands in `C`
  obtain ⟨ρ, hρ, hρC⟩ : ∃ ρ > 0, ∀ z ∈ Hbar ∩ ball (x : ℂ) ρ, Fo z ∈ C := by
    have hcw := hFoc (x : ℂ) hxbar
    have hmem : Fo ⁻¹' C ∈ 𝓝[Hbar] (x : ℂ) := hcw.preimage_mem_nhdsWithin (hCo.mem_nhds hx)
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hmem
    exact ⟨ρ, hρ, fun z hz => hball ⟨hz.2, hz.1⟩⟩
  set Φ : ℂ → ℂ := fun y => fwdMap W s (old.2.1 y) with hΦ
  have hmapsK : ∀ y ∈ H, old.2.1 y ∈ H \ fwdHull W s := fun y hy => hK (hold.inv_mem_dom hy)
  have hΦd : DifferentiableOn ℂ Φ H :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).comp hold.1 hmapsK
  -- real limits at the real points of the disc
  have hreal_lim : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → ∃ x' : ℝ, Tendsto Φ (𝓝[H] (u : ℂ)) (𝓝 (x' : ℂ)) := by
    intro u hu
    have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
    have hland : Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝 (Fo u)) :=
      ((hFoc _ hubar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
        (eventually_nhdsWithin_of_forall fun y hy => hFo hy)
    have hC := hρC _ ⟨hubar, hu⟩
    have hnot := landing_notMem_dom hold hland
    have hpK : Fo u ∈ fwdHull W s := by
      by_contra hk
      exact hnot (by rw [hdom]; exact ⟨hC, hCH hC, hk⟩)
    obtain ⟨x', -, hx'⟩ := R5Ref.exists_ambient_access hη hW hW0 hs hold hK hland hpK
    exact ⟨x', hx'⟩
  -- the boundary-regular extension
  set g := extendFrom H Φ with hg
  have hlim : ∀ z ∈ Hbar ∩ ball (x : ℂ) ρ, ∃ y, Tendsto Φ (𝓝[H] z) (𝓝 y) := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact ⟨Φ z, ((hΦd.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hzH)).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
      obtain ⟨x', hx'⟩ := hreal_lim z.re (hzr ▸ hz.2)
      exact ⟨x', hzr ▸ hx'⟩
  have hgc : ContinuousOn g (Hbar ∩ ball (x : ℂ) ρ) := by
    have hcl : Hbar ∩ ball (x : ℂ) ρ ⊆ closure H := by
      rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]; exact inter_subset_left
    exact continuousOn_extendFrom hcl hlim
  have hgΦ : EqOn Φ g (H ∩ ball (x : ℂ) ρ) := fun z hz => by
    have hzc : z ∈ closure H := subset_closure hz.1
    exact (extendFrom_eq hzc
      ((hΦd.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hz.1)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)).symm
  have hgreal : ∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → (g z).im = 0 := by
    intro z hz hz0
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    obtain ⟨x', hx'⟩ := hreal_lim z.re (hzr ▸ hz)
    have hzc : (z.re : ℂ) ∈ closure H := by
      rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
      show (0 : ℝ) ≤ (z.re : ℂ).im
      rw [ofReal_im]
    rw [hzr, hg, extendFrom_eq hzc hx', ofReal_im]
  have hinj : InjOn g (H ∩ ball (x : ℂ) ρ) := by
    intro z₁ hz₁ z₂ hz₂ h
    rw [← hgΦ hz₁, ← hgΦ hz₂] at h
    have h' := congrArg (fwdMapInv W s) h
    simp only [hΦ] at h'
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs (hmapsK z₁ hz₁.1),
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs (hmapsK z₂ hz₂.1)] at h'
    exact hold.injOn hz₁.1 hz₂.1 h'
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_reflect' hρ
    ((hΦd.mono inter_subset_left).congr fun z hz => (hgΦ hz).symm) hgc hgreal
    (fun z hz => by rw [← hgΦ hz]; exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hmapsK z hz.1)) hinj
  refine ⟨b, hb, hder.congr' ?_⟩
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hρ))] with y hy
  exact (Filter.eventuallyEq_of_mem ((QuantumZipper.isOpen_H.inter isOpen_ball).mem_nhds hy)
    fun z hz => (hgΦ hz).symm).deriv_eq

end InteractingSLE.Sec7.R5Lift
