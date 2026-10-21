import SmallGammaGeodesics.CC.Prop21Bound
import SmallGammaGeodesics.CC.Prop21Transfer

/-!
# [3] Prop 2.1: `ConfSmallScale` (track CC, packet CC6b; CC0 Details D10)

Source: Gwynne–Miller, *Conformal covariance of the LQG metric*, arXiv:1905.00384 ([3]), Prop 2.1,
in the form planned by `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10**
(with Lemma 2.6 corrected by erratum ER2, CC6a's `lemma26`, and Lemmas 2.3–2.5 replaced by D9,
CC6a's
`lemma23_uniform`).

**`confSmallScale_holds`**: for a canonical γ-LQG metric `D`, `γ ∈ (0, 2)`, the interface
`CC.ConfSmallScale γ D` (`Core/Interfaces.lean`) holds: for every conformal neighbourhood
`(ϕ, W, V)`, compact `K ⊆ V` and `δ, η > 0` there is `r₀ > 0` such that for **every** coupling
`(h, h̄, f)` of `(ϕ, W, V)` on **every** probability space, every `z ∈ K` and `r ∈ (0, r₀]`,
with probability at least `1 − η`, for all `u, v ∈ B_r(z)`,
`|D^ϕ(u, v) − D_h(u, v)| ≤ δ r^{ξQ} e^{ξ h_r(z)}` (two inequalities in `[0, ∞]`).

Proof (D10). `r₀` and the NIC spaces come from `exists_nic_side` (chosen before the probability
space). For the given coupling, the zoom `(h̃, h̄̃, f̃)` at `(z, r)` (`lemma26`) is a coupling of
`(ϕ̃, W̃, Ṽ)` with `h̃` a normalized whole-plane GFF (`isNormalizedWPGFF_lemma26`); restricted to
the local domain `ψ̃(B_{R/2}) ⊆ Ṽ` (`IsConfCoupling.mono_V`), its localized bad event has the
probability of that of the NIC space (`prob_locBad_le`), at most `η`. Off the localized bad event:
* the global metric of `h̃` is realized inside `c⁻¹ B_{R/2}`;
* the conformal localization condition gives `D^{ϕ̃}(u, v) = D^{ϕ̃}(u, v; ψ̃(B_{R/2}))`
  (`ContMetric.internal_eq_of_le_frontier`);
* the two local metrics differ by at most `δ`;
so `|D^{ϕ̃} − D_{h̃}| ≤ δ` on `B_1`, and `ae_lemma26_scale` rescales by
`𝔰_r(z) = r^{ξQ}e^{ξh_r(z)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- A coupling on `V` restricts to any `V' ⊆ V`. -/
theorem IsConfCoupling.mono_V {γ : ℝ} {ϕ : ℂ → ℂ} {W V V' : Set ℂ} {h hbar : DistC}
    {f : C(ℂ, ℝ)} (hc : IsConfCoupling γ ϕ W V h hbar f) (hV : V' ⊆ V) :
    IsConfCoupling γ ϕ W V' h hbar f := fun g τg hg hτ =>
  hc g τg (hg.trans (image_mono hV)) hτ

/-- The zoomed field `h(z + r·) − h_r(z)` of [3] Lemma 2.6 is a normalized whole-plane GFF. -/
theorem isNormalizedWPGFF_lemma26 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    IsNormalizedWPGFF (fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)) P := by
  have hcm : Measurable fun ω => -circleAvg (h ω) r z :=
    ((measurable_circleAvg_left r z).comp hh.measurable).neg
  refine ⟨(hh.affineComp hr z).addConst hcm, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero (hh.affineComp hr z),
    CircleAvg.ae_circleAvg_affineComp hh hr z] with ω h1 h2
  show circleAvg (addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)) 1 0 = 0
  rw [h1, h2]
  ring

set_option linter.unusedVariables false in
/-- **[3] Prop 2.1** (`CC.ConfSmallScale`, CC0 D10): for a canonical γ-LQG metric, `γ ∈ (0, 2)`,
the transported metric `D^ϕ` and `D_h` are uniformly close at small scales, relative to
`r^{ξQ} e^{ξ h_r(z)}`, with `r₀` independent of the coupling and of the probability space.
(The hypothesis `γ < 2` is part of the fixed interface; the proof does not use it.) -/
theorem confSmallScale_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : GaussianLQG.IsCanonicalLQGMetric γ D) : ConfSmallScale γ D := by
  intro ϕ W V hϕ K hK hKV δ hδ η hη
  set ψ : ℂ → ℂ := Function.invFunOn ϕ W with hψdef
  have hψ : ∀ x ∈ W, ψ (ϕ x) = x := fun x hx => hϕ.injOn.leftInvOn_invFunOn hx
  obtain ⟨R, r₀, hR, hr₀, hnic⟩ := exists_nic_side hγ hD hϕ hψ hK hKV hδ hη
  refine ⟨r₀, hr₀, ?_⟩
  intro Ω _ P _ h hbar f hh hhb hf hc z hz r hr
  obtain ⟨hgeom, Ω', mΩ', P', hP', x, hb, f', hx, hhb', hf', hc', hP'bad⟩ := hnic z hz r hr
  have hr0 : 0 < r := hr.1
  obtain ⟨-, -, hhbz, hfz, hcz, -, -⟩ := lemma26 hD.1 hϕ hh hhb hf hc z hr0
  have hxz := isNormalizedWPGFF_lemma26 hh z hr0
  -- the zoomed coupling, restricted to the local domain
  have hc₁ : ∀ᵐ ω ∂P, IsConfCoupling γ (zoomMap ϕ z r) (zoomSet z r W)
      (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) (addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z))
      (affineComp r (ϕ z) (hbar ω)) (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) :=
    hcz.mono fun ω hω => hω.mono_V hgeom.sub
  -- the transfer to the NIC space
  have htr := prob_locBad_le hD.1 hgeom.conf hgeom.ball_sub hgeom.T_sub hgeom.ad_open hgeom.ball_ad
    δ hxz hhbz hfz hc₁ hx hhb' hf' hc'
  -- the bad event lies a.s. in the localized bad event of the zoom
  refine le_trans (measure_mono_ae ?_) (htr.trans hP'bad)
  filter_upwards [ae_lemma26_scale hD.1 hh hhb hf ϕ z hr0] with ω hsc hbad
  by_contra hgood
  apply hbad
  rw [not_locBad_iff] at hgood
  intro u' hu' v' hv'
  set u : ℂ := (u' - z) / r with hudef
  set v : ℂ := (v' - z) / r with hvdef
  have hr0' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hu : u ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_lt_one hr0, ← dist_eq_norm]
    exact hu'
  have hv : v ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hvdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_lt_one hr0, ← dist_eq_norm]
    exact hv'
  have hu'e : z + (r : ℂ) * u = u' := zoomAff_div hr0.ne' z u'
  have hv'e : z + (r : ℂ) * v = v' := zoomAff_div hr0.ne' z v'
  obtain ⟨g1, g2, g3, g4⟩ := hgood u hu v hv
  set X : ContMetric :=
    D (addFun (affineComp r (ϕ z) (hbar ω)) (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)))
    with hXdef
  set hzf : DistC := addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z) with hhzfdef
  -- (a) the global metric of the zoomed field is realized inside `c⁻¹ B_{R/2}`
  have ha : (D hzf).internal ((fun w => deriv ϕ z * w) ⁻¹' ball 0 (R / 2)) u v =
      ENNReal.ofReal ((D hzf).1 (u, v)) :=
    le_antisymm g1 (ContMetric.ofReal_le_internal _ _ _ _)
  -- (b) the conformal localization
  have himgB : zoomMap ϕ z r '' (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) = ball 0 (R / 2) :=
    hgeom.image
  have hb : confMetric D (zoomMap ϕ z r) (zoomSet z r V) (affineComp r (ϕ z) (hbar ω))
      (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v =
      confMetric D (zoomMap ϕ z r) (zoomPsi ϕ ψ z r '' ball 0 (R / 2))
        (affineComp r (ϕ z) (hbar ω)) (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v := by
    rw [confMetric_def, confMetric_def, himgB]
    have hBU : ball (0 : ℂ) (R / 2) ⊆ zoomMap ϕ z r '' zoomSet z r V := by
      rw [← himgB]; exact image_mono hgeom.sub
    have hR4 : (R / 4) ≠ 0 := by positivity
    refine ContMetric.internal_eq_of_le_frontier X hBU isOpen_ball ?_ (hgeom.map_ball u hu)
      fun w hw => ?_
    · rw [closure_ball (0 : ℂ) hR4]
      exact closedBall_subset_ball (by linarith)
    · rw [frontier_ball (0 : ℂ) hR4] at hw
      obtain ⟨w', hw'T, hw'e⟩ := hgeom.T_surj w hw
      have := g2 w' hw'T
      rw [confMetric_def, confMetric_def, himgB, hw'e] at this
      exact this
  -- (c) the comparison at unit scale
  have hc1 : confMetric D (zoomMap ϕ z r) (zoomSet z r V) (affineComp r (ϕ z) (hbar ω))
      (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v ≤
      ENNReal.ofReal ((D hzf).1 (u, v)) + ENNReal.ofReal δ := by
    rw [hb, ← ha]; exact g3
  have hc2 : ENNReal.ofReal ((D hzf).1 (u, v)) ≤
      confMetric D (zoomMap ϕ z r) (zoomSet z r V) (affineComp r (ϕ z) (hbar ω))
        (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v + ENNReal.ofReal δ := by
    rw [hb, ← ha]; exact g4
  -- (d) rescaling by `𝔰_r(z)`
  obtain ⟨e1, e2⟩ := hsc V u v
  rw [hu'e, hv'e] at e1 e2
  set 𝔰 : ℝ := r ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) r z) with h𝔰def
  have h𝔰 : 0 < 𝔰 := mul_pos (Real.rpow_pos_of_pos hr0 _) (Real.exp_pos _)
  have hDhzf : 0 ≤ (D hzf).1 (u, v) := ContMetric.nonneg _ _ _
  have hδ𝔰 : δ * r ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) r z) = 𝔰 * δ := by
    rw [h𝔰def]; ring
  rw [hδ𝔰, e1, e2]
  constructor
  · calc ENNReal.ofReal 𝔰 * confMetric D (zoomMap ϕ z r) (zoomSet z r V)
          (affineComp r (ϕ z) (hbar ω)) (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v
        ≤ ENNReal.ofReal 𝔰 * (ENNReal.ofReal ((D hzf).1 (u, v)) + ENNReal.ofReal δ) :=
          mul_le_mul_right hc1 _
      _ = ENNReal.ofReal (𝔰 * (D hzf).1 (u, v) + 𝔰 * δ) := by
          rw [mul_add, ← ENNReal.ofReal_mul h𝔰.le, ← ENNReal.ofReal_mul h𝔰.le,
            ← ENNReal.ofReal_add (mul_nonneg h𝔰.le hDhzf) (mul_nonneg h𝔰.le hδ.le)]
  · calc ENNReal.ofReal (𝔰 * (D hzf).1 (u, v))
        = ENNReal.ofReal 𝔰 * ENNReal.ofReal ((D hzf).1 (u, v)) :=
          ENNReal.ofReal_mul h𝔰.le
      _ ≤ ENNReal.ofReal 𝔰 * (confMetric D (zoomMap ϕ z r) (zoomSet z r V)
          (affineComp r (ϕ z) (hbar ω)) (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v +
            ENNReal.ofReal δ) := mul_le_mul_right hc2 _
      _ = ENNReal.ofReal 𝔰 * confMetric D (zoomMap ϕ z r) (zoomSet z r V)
          (affineComp r (ϕ z) (hbar ω)) (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v +
            ENNReal.ofReal (𝔰 * δ) := by
          rw [mul_add, ← ENNReal.ofReal_mul h𝔰.le]

end SmallGammaGeodesics.CC
