/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftAccess
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Lemma R.5's common phase: reflection data, local surjectivity, and the increment hull

Packet PROVE-R5-LIFT2. Tools for comparing the lifts of R.5's references with the CURRENT ambient time
`T = T⁰(q)` instead of with each other (which removes the directedness input of `R5Lift.R7LiftGeom'`):

* **`reflect_data_of_hull_landing`**: if every real coordinate of a disc about `x` lands (under a conformal chart
  `old` with `old.dom ⊆ ℍ ∖ K_s`) in the ambient hull `K_s`, the ambient transition `Φ = f_s ∘ old⁻¹` has a
  continuous extension `g = extendFrom ℍ Φ` to the closed half-disc, real on the diameter, holomorphic and injective
  with values in `ℍ` on the open half-disc (the hypothesis of `R5Lift.exists_pos_tendsto_deriv_of_landing_mem`,
  weakened from "the landing of `x` lies in an open set `C` with `old.dom = C ∩ (ℍ ∖ K_s)`");
* **`exists_halfBall_subset_image_of_reflect`**: such a `g` maps the half-disc onto a half-disc about `g x`
  (Schwarz reflection + the open mapping theorem; the reflected map has positive derivative);
* **`notMem_closure_incrHull_of_subset_image`**: if a half-disc about a real `x′` lies in `f_s(ℍ ∖ K_{s′})`, then
  `x′` is off the closed increment hull `K̃_{s′ − s}` of the restarted driver (Markov property of the hulls).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv isOpen_H)
open scoped ComplexConjugate

namespace InteractingSLE.Sec7.R5Lift

/-- **Reflection data at coordinates landing in the hull.** Let `old` be a conformal chart with continuous inverse
extension `Fo` on `ℍ̄` and `old.dom ⊆ ℍ ∖ K_s` (`K_s` the hull of a continuous traced driver). If every real point of
`B(x, ρ)` lands in `K_s`, then `g = extendFrom ℍ (f_s ∘ old⁻¹)` agrees with `f_s ∘ old⁻¹` on the open half-disc, is
continuous on the closed half-disc, real on its diameter, holomorphic and injective with values in `ℍ` on the open
half-disc, and is the boundary limit of `f_s ∘ old⁻¹` at every point of the closed half-disc. -/
theorem reflect_data_of_hull_landing {old : Chart} (hold : old.IsConformal) {Fo : ℂ → ℂ}
    (hFo : EqOn Fo old.2.1 H) (hFoc : ContinuousOn Fo Hbar) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (hK : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    {x ρ : ℝ} (hland : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∈ fwdHull W s) :
    EqOn (fun y => fwdMap W s (old.2.1 y)) (extendFrom H fun y => fwdMap W s (old.2.1 y)) (H ∩ ball (x : ℂ) ρ) ∧
      ContinuousOn (extendFrom H fun y => fwdMap W s (old.2.1 y)) (Hbar ∩ ball (x : ℂ) ρ) ∧
      (∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → ((extendFrom H fun y => fwdMap W s (old.2.1 y)) z).im = 0) ∧
      (∀ z ∈ H ∩ ball (x : ℂ) ρ, (extendFrom H fun y => fwdMap W s (old.2.1 y)) z ∈ H) ∧
      InjOn (extendFrom H fun y => fwdMap W s (old.2.1 y)) (H ∩ ball (x : ℂ) ρ) ∧
      DifferentiableOn ℂ (extendFrom H fun y => fwdMap W s (old.2.1 y)) (H ∩ ball (x : ℂ) ρ) ∧
      ∀ z ∈ Hbar ∩ ball (x : ℂ) ρ, Tendsto (fun y => fwdMap W s (old.2.1 y)) (𝓝[H] z)
        (𝓝 ((extendFrom H fun y => fwdMap W s (old.2.1 y)) z)) := by
  set Φ : ℂ → ℂ := fun y => fwdMap W s (old.2.1 y) with hΦ
  have hmapsK : ∀ y ∈ H, old.2.1 y ∈ H \ fwdHull W s := fun y hy => hK (hold.inv_mem_dom hy)
  have hΦd : DifferentiableOn ℂ Φ H :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).comp hold.1 hmapsK
  -- real limits at the real points of the disc
  have hreal_lim : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → ∃ x' : ℝ, Tendsto Φ (𝓝[H] (u : ℂ)) (𝓝 (x' : ℂ)) := by
    intro u hu
    have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
    have hland' : Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝 (Fo u)) :=
      ((hFoc _ hubar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
        (eventually_nhdsWithin_of_forall fun y hy => hFo hy)
    obtain ⟨x', -, hx'⟩ := R5Ref.exists_ambient_access hη hW hW0 hs hold hK hland' (hland u hu)
    exact ⟨x', hx'⟩
  set g := extendFrom H Φ with hg
  have hlim : ∀ z ∈ Hbar ∩ ball (x : ℂ) ρ, ∃ y, Tendsto Φ (𝓝[H] z) (𝓝 y) := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact ⟨Φ z, ((hΦd.differentiableAt (isOpen_H.mem_nhds hzH)).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
      obtain ⟨x', hx'⟩ := hreal_lim z.re (hzr ▸ hz.2)
      exact ⟨x', hzr ▸ hx'⟩
  have hcl : Hbar ∩ ball (x : ℂ) ρ ⊆ closure H := by
    rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]; exact inter_subset_left
  have hgc : ContinuousOn g (Hbar ∩ ball (x : ℂ) ρ) := continuousOn_extendFrom hcl hlim
  have hgΦ : EqOn Φ g (H ∩ ball (x : ℂ) ρ) := fun z hz => by
    have hzc : z ∈ closure H := subset_closure hz.1
    exact (extendFrom_eq hzc
      ((hΦd.differentiableAt (isOpen_H.mem_nhds hz.1)).continuousAt.tendsto.mono_left
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
  refine ⟨hgΦ, hgc, hgreal, fun z hz => ?_, hinj,
    (hΦd.mono inter_subset_left).congr fun z hz => (hgΦ hz).symm, fun z hz => ?_⟩
  · rw [← hgΦ hz]; exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hmapsK z hz.1)
  · obtain ⟨y, hy⟩ := hlim z hz
    rw [hg, extendFrom_eq (hcl hz) hy]
    exact hy

/-- **The positive reflected derivative at coordinates landing in the hull** (the derivative form of
`reflect_data_of_hull_landing`). -/
theorem exists_pos_tendsto_deriv_of_hull_landing {old : Chart} (hold : old.IsConformal) {Fo : ℂ → ℂ}
    (hFo : EqOn Fo old.2.1 H) (hFoc : ContinuousOn Fo Hbar) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (hK : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    {x ρ : ℝ} (hρ : 0 < ρ) (hland : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∈ fwdHull W s) :
    ∃ b : ℝ, 0 < b ∧ Tendsto (deriv fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
  obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, -⟩ :=
    reflect_data_of_hull_landing hold hFo hFoc hη hW hW0 hs hK hland
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_reflect' hρ hgd hgc hgreal hmaps hinj
  refine ⟨b, hb, hder.congr' ?_⟩
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hρ))] with y hy
  exact (Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy)
    fun z hz => (hgΦ hz).symm).deriv_eq

/-- **A reflecting map covers a half-disc** (Schwarz reflection and the open mapping theorem): a map `g` continuous
on the closed half-disc about a real `x`, real on its diameter, holomorphic and injective with values in `ℍ` on the
open half-disc, maps the open half-disc onto a set containing a half-disc about `g x`. -/
theorem exists_halfBall_subset_image_of_reflect {g : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r)) (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0) (hmaps : ∀ z ∈ H ∩ ball (x : ℂ) r, g z ∈ H)
    (hinj : InjOn g (H ∩ ball (x : ℂ) r)) :
    ∃ ρ > 0, H ∩ ball (g x) ρ ⊆ g '' (H ∩ ball (x : ℂ) r) := by
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_reflect' hr hd hc hreal hmaps hinj
  obtain ⟨G, hG, hGg, hsym⟩ := QuantumZipper.CA.exists_reflection_extension hd hc hreal
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
  have hHB : H ∩ ball (x : ℂ) r ⊆ Hbar ∩ ball (x : ℂ) r :=
    inter_subset_inter_left _ fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)
  -- `G′(x) = b ≠ 0`
  have hGder : deriv G x = (b : ℂ) := by
    have hcontd : ContinuousAt (deriv G) x :=
      ((hG.deriv isOpen_ball).continuousOn).continuousAt (isOpen_ball.mem_nhds hxB)
    have h1 : Tendsto (deriv G) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
      refine hder.congr' ?_
      filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with y hy
      exact (Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy)
        fun z hz => (hGg (hHB hz)).symm).deriv_eq
    have := nhdsWithin_H_neBot x
    exact tendsto_nhds_unique (hcontd.tendsto.mono_left nhdsWithin_le_nhds) h1
  have hGan : AnalyticAt ℂ G x := hG.analyticAt (isOpen_ball.mem_nhds hxB)
  rcases hGan.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · exfalso
    have h0 : deriv G x = 0 := by
      have hev : G =ᶠ[𝓝 (x : ℂ)] fun _ => G x := hconst
      rw [hev.deriv_eq, deriv_const]
    rw [hGder] at h0
    exact (ne_of_gt hb) (by exact_mod_cast h0)
  · have himg : G '' ball (x : ℂ) r ∈ 𝓝 (G x) := hopen (image_mem_map (isOpen_ball.mem_nhds hxB))
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 himg
    have hGx : G x = g x := hGg ⟨hxbar, hxB⟩
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    rw [← hGx] at hw
    obtain ⟨z, hzB, hzw⟩ := hball hw.2
    have hzH : z ∈ H := by
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · exfalso
        have hcz : conj z ∈ H ∩ ball (x : ℂ) r :=
          ⟨show 0 < (conj z).im by rw [conj_im]; linarith, QuantumZipper.CA.conj_mem_ball_ofReal hzB⟩
        have h1 := hsym (conj z) hcz.2
        rw [conj_conj, hGg (hHB hcz)] at h1
        have h2 : (G z).im = -(g (conj z)).im := by rw [h1, conj_im]
        have h3 : 0 < (g (conj z)).im := hmaps _ hcz
        have h4 : 0 < (G z).im := by rw [hzw]; exact hw.1
        linarith
      · exfalso
        have h1 : (G z).im = 0 := by rw [hGg ⟨hzero.ge, hzB⟩]; exact hreal z hzB hzero
        have h4 : 0 < (G z).im := by rw [hzw]; exact hw.1
        linarith
      · exact hpos
    exact ⟨z, ⟨hzH, hzB⟩, by rw [← hGg (hHB ⟨hzH, hzB⟩)]; exact hzw⟩

/-- **A half-disc inside `f_s(ℍ ∖ K_{s′})` is off the closed increment hull** (Markov property of the hulls):
if `ℍ ∩ B(x′, ρ) ⊆ f_s(ℍ ∖ K_{s′})` for some `ρ > 0`, then `x′` is not in the closure of the hull
`K̃_{s′ − s}` of the restarted driver `r ↦ W(s + r) − W(s)`. -/
theorem notMem_closure_incrHull_of_subset_image {W : ℝ → ℝ} (hW : Continuous W) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') {x' : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : H ∩ ball x' ρ ⊆ fwdMap W s '' (H \ fwdHull W s')) :
    x' ∉ closure (fwdHull (fun r => W (s + r) - W s) (s' - s)) := by
  intro hcl
  obtain ⟨w, hwK, hwb⟩ := Metric.mem_closure_iff.1 hcl ρ hρ
  have hwH : w ∈ H := hwK.1
  obtain ⟨z, hz, rfl⟩ := hsub ⟨hwH, by rw [mem_ball, dist_comm]; exact hwb⟩
  have hzs : z ∈ H \ fwdHull W s := Ito.mem_diff_fwdHull_of_le hz hss'
  have hmem : z ∈ fwdHull W (s + (s' - s)) \ fwdHull W s := by
    rw [QuantumZipper.fwdHull_add_diff hW hs (sub_nonneg.2 hss')]
    exact ⟨hzs, hwK⟩
  rw [add_sub_cancel] at hmem
  exact hz.2 hmem.1

end InteractingSLE.Sec7.R5Lift
