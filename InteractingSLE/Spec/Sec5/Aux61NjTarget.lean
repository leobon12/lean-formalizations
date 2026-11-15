/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NjBranch
import InteractingSLE.Spec.ZhanGT4.D9Clear
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Foundations.Loewner.Reflect
import InteractingSLE.Spec.Sec7.SideHeightLift

/-!
# The target-side comparison points: `TargetSideBranch` proved; the landing branch integer is one

Packet PROVE-AUX61-NOJUMP. Proof of `Aux61Nj.TargetSideBranch` for every chart whose domain contains a
half-disc at the target `1` (`SourceChartGeometry.target`), given the strict left base gap
`−rightImg(−w)(0)(s) − w s < 0` (which holds at every eastern landing with physical point in `ℍ`,
`WangWu.neg_rightImg_sub_lt_of_extendFrom_mem_H`).

## The hull frame at a free real point

* `exists_ball_disjoint_fwdHull_of_target`: for a real `r` near `1` the hull-frame point `−1/r` has a ball
  disjoint from `fwdHull w s` (`negInv` maps it into the physical half-disc at `1`, inside the chart domain);
* `exists_real_tendsto_fwdMap`: such an untouched real point `ρ < 0` is **alive** for the reflected driver
  (`ZhanGT4.exists_isForwardSol_of_disjoint_ball_gen`, `LP.exists_isForwardSol_neg_iff`,
  `Sec7.Lemma76E.alive_of_isForwardSol`), so `f_s → L` at `ρ` with `L = −flow(−w)(−ρ)(s) < 0` and
  `L ≤ −rightImg(−w)(0)(s) − w s` (`rightImg_le_gImg`).

## The counterflow chart and the two lifts just right of the target

* `exists_isPosReflect_revChart`, `tendsto_revChart_of_target`: `Ψ_s` reflects positively at a free real
  point `t` near `1`, with `Ψ_s(t) = −1/L > 0`;
* `tendsto_im_physicalRestartLog_two_pi`: the chart lift tends to `2π` at `t > 1` (Aux. lemma 57 for the
  canonical logarithm at the untouched real point `t/(1 − t)`; `−2 arg(1 − z) → 2π`);
* `tendsto_im_logDerivPsi_zero`: the counterflow lift tends to `0` (`arg f_s(−1/z) → π`, Aux. lemma 57 in
  the hull frame, `arg z → 0`).

## Main results

* **`targetSideBranch_of_target`**: `TargetSideBranch w s c` for every chart with a half-disc at `1` in its
  domain, given the strict left base gap. The point `y = Ψ_s(t)` with `t = 1 + ε₀` close to `1`; the
  counterflow collar at `y` comes from the local inverse of `Ψ_s` (`IsPosReflect.tendsto_leftInv`);
  `y ≤ junR` from `L ≤ pL < 0`; `T(y) < M` from `mapOut_B(u) − u → 0` at infinity and
  `t/(1 − t) → −∞`; the phase `2π − 0`.
* `gap_of_extendFrom_mem_H`: the gap from a physical landing point in `ℍ`;
* `ae_targetSideBranch`: the source form on the selected records;
* **`ae_height_eq_eastHeight_one`**: almost surely on the selected records, at every counterflow collar
  point east of the junction with physical point in `ℍ`, the relative phase tends to `2π` (branch integer
  `n = 1`) and the word height is `eastHeight S 1` — with no named input.

Deterministic up to the landed a.s. facts of the restart family; nothing here replaces a source
statement. R48/R77 respected.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open scoped Real
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61TwoS Aux61Restart Aux61Cmp WangWu CrossCond.Word49 MartChar.RealFlow
universe u

section HullFrame

variable {w : ℝ → ℝ} {s : ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)

/-- **Untouched hull-frame points near `−1`**: if a half-disc `H ∩ B(1, δ)` lies in a set `D` off the
reflected hull, every real `r ∈ (1 − δ, 1 + δ)` with `r > 0` gives a ball about `−1/r` disjoint from the
hull. -/
theorem exists_ball_disjoint_fwdHull_of_target {D : Set ℂ} (hDK : D ⊆ H \ negInv '' fwdHull w s)
    {δ : ℝ} (hD : ball (1 : ℂ) δ ∩ H ⊆ D) {r : ℝ} (hr0 : 0 < r) (hr : |r - 1| < δ) :
    ∃ ε > 0, Disjoint (ball ((-r⁻¹ : ℝ) : ℂ) ε) (fwdHull w s) := by
  have hρ0 : ((-r⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; exact neg_ne_zero.2 (inv_ne_zero hr0.ne')
  have hnr : negInv ((-r⁻¹ : ℝ) : ℂ) = (r : ℂ) := by
    simp [negInv]
  have hcont := continuousAt_negInv hρ0
  set η : ℝ := δ - |r - 1| with hη
  have hη0 : 0 < η := by simp only [hη]; linarith
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hcont η hη0
  refine ⟨ε, hε, Set.disjoint_left.2 fun u hu hK => ?_⟩
  have huH : u ∈ H := hK.1
  have hd : dist (negInv u) (r : ℂ) < η := by rw [← hnr]; exact hball hu
  have h1 : negInv u ∈ ball (1 : ℂ) δ := by
    rw [mem_ball]
    have h2 : dist (r : ℂ) (1 : ℂ) = |r - 1| := by
      rw [dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    linarith [dist_triangle (negInv u) (r : ℂ) (1 : ℂ)]
  have hmem := hDK (hD ⟨h1, negInv_mem_H huH⟩)
  exact hmem.2 ⟨u, hK, rfl⟩

include hw hw0 hs in
/-- **An untouched real point left of the seed is alive, and `f_s` has a negative real limit there, left
of the left base image.** -/
theorem exists_real_tendsto_fwdMap {ρ : ℝ} (hρ : ρ < 0) {ε : ℝ} (hε : 0 < ε)
    (hd : Disjoint (ball (ρ : ℂ) ε) (fwdHull w s)) :
    ∃ L : ℝ, L < 0 ∧ L ≤ -rightImg (fun r => -w r) 0 s - w s ∧
      Tendsto (fwdMap w s) (𝓝[H] (ρ : ℂ)) (𝓝 (L : ℂ)) := by
  have hρw : ρ ≠ w 0 := by rw [hw0]; exact hρ.ne
  obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball_gen hw hρw hs hε hd
  obtain ⟨u', hu'⟩ := LP.exists_isForwardSol_neg_iff.2 ⟨v, hv⟩
  rw [LP.reflectC_ofReal] at hu'
  have hpos : (-w) 0 < -ρ := by simp only [Pi.neg_apply, hw0, neg_zero]; linarith
  have halive : Alive (fun r => -w r) (-ρ) s :=
    Sec7.Lemma76E.alive_of_isForwardSol hw.neg hs hpos hu'
  have hsol := isForwardSol_neg_of_alive hw halive
  have hρc : -(((-ρ : ℝ)) : ℂ) = (ρ : ℂ) := by push_cast; ring
  rw [hρc] at hsol
  obtain ⟨-, hX⟩ := Alive.isPosSol (w := fun r => -w r) hw.neg halive
  refine ⟨-cflow (fun r => -w r) (-ρ) s, ?_, ?_, ?_⟩
  · exact neg_neg_of_pos (hX s ⟨hs, le_rfl⟩).1
  · have hle : rightImg (fun r => -w r) 0 s ≤ -w s + cflow (fun r => -w r) (-ρ) s :=
      rightImg_le_gImg hw.neg hs (show (0 : ℝ) < -ρ by linarith) halive
    linarith
  · have h := tendsto_fwdMap_of_isForwardSol_real hw hw0 hs hsol
    simpa only [ofReal_neg] using h

end HullFrame

/-! ### The counterflow chart at a free real point near the target -/

section Psi

variable {w : ℝ → ℝ} {s : ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
  {D : Set ℂ} (hDK : D ⊆ H \ negInv '' fwdHull w s) {δ : ℝ} (hD : ball (1 : ℂ) δ ∩ H ⊆ D)

theorem tendsto_negInv_nhdsWithin_ofReal {r : ℝ} (hr : r ≠ 0) :
    Tendsto negInv (𝓝[H] (r : ℂ)) (𝓝[H] ((-r⁻¹ : ℝ) : ℂ)) := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr
  have he : negInv (r : ℂ) = ((-r⁻¹ : ℝ) : ℂ) := negInv_ofReal r
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => negInv_mem_H hz⟩
  rw [← he]
  exact (continuousAt_negInv hr').tendsto.mono_left nhdsWithin_le_nhds

include hw hw0 hs hDK hD in
/-- **The hull-frame image and the counterflow chart at a free real point `r` near `1`**: `f_s ∘ R → L`
and `Ψ_s → −1/L`, with `L < 0` left of the left base image. -/
theorem tendsto_revChart_of_target {r : ℝ} (hr0 : 0 < r) (hr : |r - 1| < δ) :
    ∃ L : ℝ, L < 0 ∧ L ≤ -rightImg (fun r => -w r) 0 s - w s ∧
      Tendsto (fun z => fwdMap w s (negInv z)) (𝓝[H] (r : ℂ)) (𝓝 (L : ℂ)) ∧
      Tendsto (revChart w s) (𝓝[H] (r : ℂ)) (𝓝 ((-L⁻¹ : ℝ) : ℂ)) := by
  obtain ⟨ε, hε, hd⟩ := exists_ball_disjoint_fwdHull_of_target hDK hD hr0 hr
  have hρ : -r⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hr0)
  obtain ⟨L, hL0, hLp, hL⟩ := exists_real_tendsto_fwdMap hw hw0 hs hρ hε hd
  have hf : Tendsto (fun z => fwdMap w s (negInv z)) (𝓝[H] (r : ℂ)) (𝓝 (L : ℂ)) :=
    hL.comp (tendsto_negInv_nhdsWithin_ofReal hr0.ne')
  refine ⟨L, hL0, hLp, hf, ?_⟩
  have hL0' : (L : ℂ) ≠ 0 := ofReal_ne_zero.2 hL0.ne
  rw [← negInv_ofReal L]
  exact (continuousAt_negInv hL0').tendsto.comp hf

include hw hw0 hs hDK hD in
/-- **`Ψ_s` reflects positively at a free real point near the target.** -/
theorem exists_isPosReflect_revChart {t ε : ℝ} (hε : 0 < ε) (hεt : ε < t) (htε : |t - 1| + ε < δ) :
    ∃ G, IsPosReflect (revChart w s) G t ε := by
  have hsub : ∀ z ∈ H ∩ ball (t : ℂ) ε, z ∈ H \ negInv '' fwdHull w s := by
    intro z hz
    refine hDK (hD ⟨?_, hz.1⟩)
    have hzt : dist z (t : ℂ) < ε := hz.2
    rw [mem_ball]
    have h2 : dist (t : ℂ) (1 : ℂ) = |t - 1| := by
      rw [dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    linarith [dist_triangle z (t : ℂ) (1 : ℂ)]
  refine exists_isPosReflect hε (fun z hz => ?_) (fun z hz => revChart_mem_H hw hs (hsub z hz))
    ((injOn_revChart hw hw0 hs).mono hsub) fun x hx => ?_
  · exact (GlueImg.differentiableAt_revChart hw hs (hsub z hz)).differentiableWithinAt
  · have hxt : |x - t| < ε := by
      have := mem_ball.1 hx
      rwa [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs] at this
    have hx0 : 0 < x := by linarith [neg_abs_le (x - t)]
    have hx1 : |x - 1| < δ := by
      have := abs_sub_le x t 1
      linarith
    obtain ⟨L, -, -, -, h⟩ := tendsto_revChart_of_target hw hw0 hs hDK hD hx0 hx1
    have h' := (continuous_im.tendsto _).comp h
    simpa only [Function.comp_def, ofReal_im] using h'

/-! ### The two lifts just right of the target -/

theorem im_physicalRestartLog (B : Set ℂ) (z : ℂ) :
    (physicalRestartLog B z).im = (Restart.canonDerivLog B (stripRightRetarget z)).im - 2 * arg (1 - z) := by
  simp only [physicalRestartLog, stripRightRetargetLog, add_im, mul_im, log_im, log_re]
  norm_num
  ring

theorem im_logDerivPsi (w : ℝ → ℝ) (s : ℝ) (z : ℂ) :
    (GlueImg.logDerivPsi w s z).im = -2 * arg (fwdMap w s (negInv z)) +
      (QuantumZipper.logDerivFwd w s (negInv z)).im - 2 * arg z + 2 * π := by
  simp only [GlueImg.logDerivPsi, add_im, mul_im, log_im, log_re, I_re, I_im]
  norm_num
  ring

theorem stripRightUntarget_eq (z : ℂ) : stripRightUntarget z = z / (z + 1) := by
  simp only [stripRightUntarget, QuantumZipper.CA.realMobius, ofReal_one, one_mul, ofReal_zero, add_zero]

/-- **The chart lift right of the target**: `Im physicalRestartLog → 2π` at a real `t > 1` whose
half-disc neighbourhood lies in the retained domain (Aux. lemma 57 for the canonical logarithm at the
untouched real point `t/(1 − t)`, and the branch `−2 arg(1 − z) → 2π`). -/
theorem tendsto_im_physicalRestartLog_two_pi {D : Set ℂ}
    (hB : IsHPHull (stripTargetHull D)) {δ : ℝ} (hD : ball (1 : ℂ) δ ∩ H ⊆ D) {t : ℝ} (ht1 : 1 < t)
    (htd : |t - 1| < δ) :
    Tendsto (fun z => (physicalRestartLog (stripTargetHull D) z).im) (𝓝[H] (t : ℂ)) (𝓝 (2 * π)) := by
  have h1t : (1 : ℝ) - t ≠ 0 := by linarith
  set x : ℝ := t / (1 - t) with hx
  have hRt : stripRightRetarget (t : ℂ) = (x : ℂ) := by
    rw [stripRightRetarget_eq, hx]; push_cast; rfl
  have hx1 : (x : ℂ) + 1 ≠ 0 := by
    have : x + 1 = 1 / (1 - t) := by rw [hx]; field_simp; ring
    rw [← ofReal_one, ← ofReal_add, this, ofReal_ne_zero]
    exact one_div_ne_zero h1t
  have hUt : stripRightUntarget (x : ℂ) = (t : ℂ) := by
    rw [stripRightUntarget_eq]
    have : x / (x + 1) = t := by rw [hx]; field_simp; ring
    rw [← ofReal_one, ← ofReal_add, ← ofReal_div, this]
  have hUc : ContinuousAt stripRightUntarget (x : ℂ) := by
    have : stripRightUntarget = fun z : ℂ => z / (z + 1) := funext stripRightUntarget_eq
    rw [this]
    exact continuousAt_id.div (continuousAt_id.add continuousAt_const) hx1
  -- the untouched real point of the retargeted hull
  set η : ℝ := δ - |t - 1| with hη
  have hη0 : 0 < η := by simp only [hη]; linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.1 hUc η hη0
  have hd : Disjoint (ball (x : ℂ) ρ) (stripTargetHull D) := by
    refine Set.disjoint_left.2 fun u hu hK => ?_
    have huH : u ∈ H := hK.1
    have hdu : dist (stripRightUntarget u) (t : ℂ) < η := by rw [← hUt]; exact hball hu
    have h2 : dist (t : ℂ) (1 : ℂ) = |t - 1| := by
      rw [dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    have hUH : stripRightUntarget u ∈ H := isConformalBijection_stripRightUntarget.2.mapsTo huH
    have hmem : stripRightUntarget u ∈ D := hD ⟨by
      rw [mem_ball]; linarith [dist_triangle (stripRightUntarget u) (t : ℂ) (1 : ℂ)], hUH⟩
    exact hK.2 ⟨_, hmem, stripRightRetarget_untarget huH⟩
  have h1 := (Restart.isCanonicalDerivLog_canonDerivLog hB).tendsto_im_nhdsWithin_zero hB
    (ConformalImage.isMapOut_mapOut hB) hρ hd
  have ht1' : (t : ℂ) ≠ 1 := by
    rw [← ofReal_one]; exact fun h => (ne_of_gt ht1) (ofReal_injective h)
  have hR : Tendsto stripRightRetarget (𝓝[H] (t : ℂ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
      isConformalBijection_stripRightRetarget.2.mapsTo hz⟩
    rw [← hRt]
    exact (continuousAt_stripRightRetarget ht1').tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℂ => arg (1 - z)) (𝓝[H] (t : ℂ)) (𝓝 (-π)) := by
    have hre : (1 - (t : ℂ)).re < 0 := by simp; linarith
    have him : (1 - (t : ℂ)).im = 0 := by simp
    refine (tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp
      (tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩)
    · exact ((continuous_const.sub continuous_id).tendsto _).mono_left nhdsWithin_le_nhds
    · show (1 - z).im < 0
      have : 0 < z.im := hz
      simp only [sub_im, one_im]; linarith
  have h := (h1.comp hR).sub (h2.const_mul 2)
  refine (h.congr' (Eventually.of_forall fun z => ?_)).trans ?_
  · rw [im_physicalRestartLog]; rfl
  · rw [show (0 : ℝ) - 2 * -π = 2 * π by ring]

include hw hw0 hs hDK hD in
/-- **The counterflow lift right of the target**: `Im log Ψ_s′ → 0` at a real `t > 0` near `1`
(`arg f_s(−1/z) → π` by the negative real limit, Aux. lemma 57 in the hull frame, `arg z → 0`). -/
theorem tendsto_im_logDerivPsi_zero {t : ℝ} (ht0 : 0 < t) (htd : |t - 1| < δ) :
    Tendsto (fun z => (GlueImg.logDerivPsi w s z).im) (𝓝[H] (t : ℂ)) (𝓝 0) := by
  obtain ⟨L, hL0, -, hLf, -⟩ := tendsto_revChart_of_target hw hw0 hs hDK hD ht0 htd
  obtain ⟨ε, hε, hd⟩ := exists_ball_disjoint_fwdHull_of_target hDK hD ht0 htd
  have hnear : ∀ᶠ z in 𝓝[H] (t : ℂ), z ∈ ball (1 : ℂ) δ ∩ H := by
    have hb : ball (1 : ℂ) δ ∈ 𝓝 (t : ℂ) := by
      refine isOpen_ball.mem_nhds ?_
      rw [mem_ball, dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      exact htd
    filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with z h1 h2 using ⟨h1, h2⟩
  have ha1 : Tendsto (fun z => arg (fwdMap w s (negInv z))) (𝓝[H] (t : ℂ)) (𝓝 π) := by
    refine (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (by simpa using hL0) (by simp)).comp
      (tendsto_nhdsWithin_iff.2 ⟨hLf, ?_⟩)
    filter_upwards [hnear] with z hz
    have hK := negInv_notMem_fwdHull (hDK (hD hz))
    exact (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs hK).le
  have ha2 : Tendsto (fun z => (QuantumZipper.logDerivFwd w s (negInv z)).im) (𝓝[H] (t : ℂ)) (𝓝 0) :=
    (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hw hs)
      (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hw hw0 hs) (isMapOut_fwdMap hw hw0 hs) hε hd).comp
      (tendsto_negInv_nhdsWithin_ofReal ht0.ne')
  have ha3 : Tendsto (fun z : ℂ => arg z) (𝓝[H] (t : ℂ)) (𝓝 0) := by
    have hc : ContinuousAt arg (t : ℂ) := continuousAt_arg (Or.inl (by simpa using ht0))
    have h0 : arg (t : ℂ) = 0 := arg_ofReal_of_nonneg ht0.le
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := (((ha1.const_mul (-2)).add ha2).sub (ha3.const_mul 2)).add_const (2 * π)
  refine (h.congr' (Eventually.of_forall fun z => ?_)).trans ?_
  · rw [im_logDerivPsi]
  · rw [show -2 * π + 0 - 2 * 0 + 2 * π = (0 : ℝ) by ring]

end Psi

/-! ### `TargetSideBranch` -/

section Main

variable {w : ℝ → ℝ} {γ : ℝ → ℂ} {s : ℝ}
  (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsLoewnerTrace w γ) (hs : 0 ≤ s)
  {c : Chart} (hc : c.IsConformal) (hsubK : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull w s)
  (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
  (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)

theorem exists_norm_mapOut_sub_lt {B : Set ℂ} (hB : IsHPHull B) :
    ∃ R₀ : ℝ, ∀ u ∈ H \ B, R₀ ≤ ‖u‖ → ‖ConformalImage.mapOut B u - u‖ < 1 := by
  have h := (ConformalImage.isMapOut_mapOut hB).2
  have h1 := h.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  rw [Filter.eventually_inf_principal, ← comap_norm_atTop, Filter.eventually_comap,
    Filter.eventually_atTop] at h1
  obtain ⟨R₀, hR⟩ := h1
  exact ⟨R₀, fun u hu hRu => by simpa [dist_zero_right] using hR ‖u‖ hRu u rfl hu⟩

include hw hw0 hγ hs hc hsubK hB hscale in
/-- **`TargetSideBranch` holds** for a chart whose domain contains a half-disc at the target `1`, given
the strict left base gap. -/
theorem targetSideBranch_of_target (ha : 0 < a) {δ : ℝ} (hδ : 0 < δ)
    (htgt : ball (1 : ℂ) δ ∩ H ⊆ (c.dom : Set ℂ))
    (hgap : -rightImg (fun r => -w r) 0 s - w s < 0) : TargetSideBranch w s c := by
  intro M
  obtain ⟨R₀, hR₀⟩ := exists_norm_mapOut_sub_lt hB
  -- the free real point `t`
  set K : ℝ := max (2 * |R₀| + 2) (|M / a - 1 + ξ| + 1) with hK
  have hK1 : 1 ≤ K := le_trans (by linarith [abs_nonneg R₀]) (le_max_left _ _)
  have hK0 : 0 < K := by linarith
  set ε₀ : ℝ := min (δ / 4) (1 / (2 * K)) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (by linarith) (by positivity)
  have hε₀δ : ε₀ ≤ δ / 4 := min_le_left _ _
  have hε₀K : ε₀ ≤ 1 / (2 * K) := min_le_right _ _
  set t : ℝ := 1 + ε₀ with ht
  have ht1 : 1 < t := by simp only [ht]; linarith
  have ht0 : 0 < t := by linarith
  have htd : |t - 1| < δ := by
    rw [show t - 1 = ε₀ by simp only [ht]; ring, abs_of_pos hε₀pos]; linarith
  set x : ℝ := t / (1 - t) with hx
  have hxeq : x = -(1 + ε₀) / ε₀ := by
    rw [hx, ht, div_eq_div_iff (by linarith) hε₀pos.ne']; ring
  have hxK : x ≤ -(2 * K) := by
    have h1 : 2 * K ≤ 1 / ε₀ := by
      rw [le_div_iff₀ hε₀pos]
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).1 hε₀K
      linarith
    have h2 : 1 / ε₀ ≤ (1 + ε₀) / ε₀ := div_le_div_of_nonneg_right (by linarith) hε₀pos.le
    rw [hxeq, neg_div]
    linarith
  have hRt : stripRightRetarget (t : ℂ) = (x : ℂ) := by
    rw [stripRightRetarget_eq, hx]; push_cast; rfl
  have ht1' : (t : ℂ) ≠ 1 := by
    rw [← ofReal_one]; exact fun h => (ne_of_gt ht1) (ofReal_injective h)
  -- `Ψ_s` reflects at `t`
  set ε₂ : ℝ := ε₀ / 2 with hε₂
  have hε₂pos : 0 < ε₂ := by simp only [hε₂]; linarith
  have hε₂t : ε₂ < t := by simp only [hε₂]; linarith
  have htε₂ : |t - 1| + ε₂ < δ := by
    rw [show t - 1 = ε₀ by simp only [ht]; ring, abs_of_pos hε₀pos]; simp only [hε₂]; linarith
  obtain ⟨GΨ, hGΨ⟩ := exists_isPosReflect_revChart hw hw0 hs hsubK htgt hε₂pos hε₂t htε₂
  obtain ⟨L, hL0, hLp, -, hLΨ⟩ := tendsto_revChart_of_target hw hw0 hs hsubK htgt ht0 htd
  set y : ℝ := -L⁻¹ with hy
  have hy0 : 0 < y := by simp only [hy]; exact neg_pos.2 (inv_lt_zero.2 hL0)
  have hGt : GΨ t = (y : ℂ) := by
    have := GlueImg.nhdsWithin_H_neBot t
    exact tendsto_nhds_unique (hGΨ.tendsto (mem_ball_self hε₂pos)) hLΨ
  have hballt : ∀ ε, ε ≤ ε₂ → ball (t : ℂ) ε ⊆ ball (1 : ℂ) δ := by
    intro ε hε z hz
    have h2 : dist (t : ℂ) (1 : ℂ) = |t - 1| := by
      rw [dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    rw [mem_ball] at hz ⊢
    linarith [dist_triangle z (t : ℂ) (1 : ℂ)]
  have hsub2 : ∀ z ∈ H ∩ ball (t : ℂ) ε₂, z ∈ H \ negInv '' fwdHull w s := fun z hz =>
    hsubK (htgt ⟨hballt ε₂ le_rfl hz.2, hz.1⟩)
  have hinv : Tendsto (revChartInv w s) (𝓝[H] (y : ℂ)) (𝓝[H] (t : ℂ)) := by
    have h := hGΨ.tendsto_leftInv (Θ := revChartInv w s) fun z hz =>
      revChartInv_revChart hw hw0 hs (hsub2 z hz)
    rwa [hGt] at h
  -- the counterflow collar at `y`
  set ε₃ : ℝ := ε₂ / 2 with hε₃
  have hε₃pos : 0 < ε₃ := by simp only [hε₃]; linarith
  have hpre : revChartInv w s ⁻¹' ball (t : ℂ) ε₃ ∈ 𝓝[H] (y : ℂ) :=
    (hinv.mono_right nhdsWithin_le_nhds) (isOpen_ball.mem_nhds (mem_ball_self hε₃pos))
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set ry : ℝ := min r₁ (y / 2) with hry
  have hry0 : 0 < ry := lt_min hr₁ (by linarith)
  have hland : ∀ ζ ∈ H ∩ ball (y : ℂ) ry, revChartInv w s ζ ∈ ball (t : ℂ) ε₃ := fun ζ hζ =>
    hr₁sub ⟨ball_subset_ball (min_le_left _ _) hζ.2, hζ.1⟩
  have hcol : MapsTo (revChartInv w s) (H ∩ ball (y : ℂ) ry) c.dom := fun ζ hζ =>
    htgt ⟨hballt ε₃ (by simp only [hε₃]; linarith) (hland ζ hζ), (revChartInv_mem hw hw0 hs hζ.1).1⟩
  have hfin : ∀ y' : ℝ, (y' : ℂ) ∈ ball (y : ℂ) ry →
      y' ≠ 0 ∧ extendFrom H (fwdMapInv w s) (negInv (y' : ℂ)) ≠ 0 ∧ cfBdry w s y' ≠ 1 := by
    intro y' hy'
    have hyy : |y' - y| < ry := by
      have := mem_ball.1 hy'
      rwa [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs] at this
    have hy'0 : 0 < y' := by linarith [neg_abs_le (y' - y), min_le_right r₁ (y / 2)]
    have hev : ∀ᶠ ζ in 𝓝[H] (y' : ℂ), revChartInv w s ζ ∈ ball (t : ℂ) ε₃ := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hy'), self_mem_nhdsWithin]
        with ζ h1 h2 using hland ζ ⟨h2, h1⟩
    have := GlueImg.nhdsWithin_H_neBot y'
    have hF0 : extendFrom H (fwdMapInv w s) (negInv (y' : ℂ)) ≠ 0 := by
      intro hF0
      have hbar : ((-y'⁻¹ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
      have hlim := ((hγ.hasBdryLimits hw hw0 hs).tendsto hbar).comp
        (tendsto_negInv_nhdsWithin_ofReal hy'0.ne')
      rw [← negInv_ofReal, hF0] at hlim
      have hpos' : (0 : ℝ) < 1 / (t + ε₃) := div_pos one_pos (by linarith)
      have hsmall : ∀ᶠ ζ in 𝓝[H] (y' : ℂ), ‖fwdMapInv w s (negInv ζ)‖ < 1 / (t + ε₃) :=
        (hlim.eventually (Metric.ball_mem_nhds 0 hpos')).mono fun ζ hζ => by
          simpa [dist_zero_right] using hζ
      obtain ⟨ζ, h1, h2⟩ := (hev.and hsmall).exists
      have hn : ‖revChartInv w s ζ‖ = ‖fwdMapInv w s (negInv ζ)‖⁻¹ := by
        simp only [revChartInv, negInv, norm_neg, norm_inv]
      have hb : ‖revChartInv w s ζ - t‖ < ε₃ := by rw [← dist_eq_norm]; exact h1
      have hlow : t - ε₃ < ‖revChartInv w s ζ‖ := by
        have := norm_sub_norm_le (t : ℂ) (revChartInv w s ζ)
        rw [norm_real, Real.norm_eq_abs, abs_of_pos ht0, norm_sub_rev] at this
        linarith
      have hup : ‖revChartInv w s ζ‖ < t + ε₃ := by
        have := norm_le_insert' (revChartInv w s ζ) (t : ℂ)
        rw [norm_real, Real.norm_eq_abs, abs_of_pos ht0] at this
        linarith
      rcases eq_or_ne (fwdMapInv w s (negInv ζ)) 0 with h0 | h0
      · rw [hn, h0, norm_zero, inv_zero] at hlow
        simp only [hε₃, hε₂] at hlow
        linarith
      · have hpos : 0 < ‖fwdMapInv w s (negInv ζ)‖ := norm_pos_iff.2 h0
        have : t + ε₃ < ‖fwdMapInv w s (negInv ζ)‖⁻¹ := by
          rw [lt_inv_comm₀ (by positivity) hpos, ← one_div]; exact h2
        rw [hn] at hup
        linarith
    refine ⟨hy'0.ne', hF0, ?_⟩
    have hlimc := tendsto_revChartInv_cfBdry hw hw0 hγ hs hy'0.ne' hF0
    have hle : dist (cfBdry w s y') (t : ℂ) ≤ ε₃ :=
      le_of_tendsto ((continuous_id.dist continuous_const).continuousAt.tendsto.comp hlimc)
        (hev.mono fun ζ hζ => (mem_ball.1 hζ).le)
    intro h1
    rw [h1] at hle
    have h2 : dist (1 : ℂ) (t : ℂ) = t - 1 := by
      rw [dist_comm, dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    rw [h2] at hle
    simp only [hε₃, hε₂, ht] at hle
    linarith
  obtain ⟨Gy, hGy⟩ := exists_isPosReflect_cfCollar hw hw0 hγ hs hc hsubK hB hscale hry0 hcol hfin
  refine ⟨y, ry, Gy, hGy, fun z hz => ⟨hz.1, hcol hz⟩, ?_, ?_, ?_⟩
  · -- `y ≤ junR`
    rw [junR]
    have h := one_div_le_one_div_of_neg_of_le hgap hLp
    have hy' : y = -(1 / L) := by rw [hy, one_div]
    rw [hy', neg_div]
    linarith
  · -- the transition value at `y` is below `M`
    have := GlueImg.nhdsWithin_H_neBot y
    have hT := hGy.tendsto (mem_ball_self hry0)
    have hz : Tendsto (fun ζ => stripRightRetarget (revChartInv w s ζ)) (𝓝[H] (y : ℂ)) (𝓝 (x : ℂ)) := by
      rw [← hRt]
      exact (continuousAt_stripRightRetarget ht1').tendsto.comp (hinv.mono_right nhdsWithin_le_nhds)
    have hxn : 2 * K ≤ ‖(x : ℂ)‖ := by
      rw [norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
    have hbound : ∀ᶠ ζ in 𝓝[H] (y : ℂ), ((c.1 ∘ revChartInv w s) ζ).re ≤
        a * ((stripRightRetarget (revChartInv w s ζ)).re + 1 - ξ) := by
      have hnorm : ∀ᶠ ζ in 𝓝[H] (y : ℂ), stripRightRetarget (revChartInv w s ζ) ∈ ball (x : ℂ) 1 :=
        hz (Metric.ball_mem_nhds _ one_pos)
      filter_upwards [hnorm, self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hry0))] with ζ hζn hζH hζb
      have hdom : revChartInv w s ζ ∈ (c.dom : Set ℂ) := hcol ⟨hζH, hζb⟩
      set u := stripRightRetarget (revChartInv w s ζ) with hu
      have huB : u ∈ H \ stripTargetHull (c.dom : Set ℂ) := by
        rw [H_diff_stripTargetHull hc.dom_subset]; exact mem_image_of_mem _ hdom
      have hun : R₀ ≤ ‖u‖ := by
        have := norm_sub_norm_le (x : ℂ) u
        have hd : ‖(x : ℂ) - u‖ < 1 := by rw [← dist_eq_norm, dist_comm]; exact hζn
        have := le_abs_self R₀
        have hK2 : 2 * |R₀| + 2 ≤ K := le_max_left _ _
        linarith
      have hm := hR₀ u huB hun
      have hre : (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) u).re ≤ u.re + 1 := by
        have := (re_le_norm (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) u - u)).trans hm.le
        rw [sub_re] at this; linarith
      simp only [Function.comp_apply]
      rw [hscale hdom]
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sub_re]
      have := mul_le_mul_of_nonneg_left (show (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ))
        (stripRightRetarget (revChartInv w s ζ))).re - ξ ≤ u.re + 1 - ξ by rw [← hu]; linarith) ha.le
      linarith
    have hlim2 : Tendsto (fun ζ => a * ((stripRightRetarget (revChartInv w s ζ)).re + 1 - ξ))
        (𝓝[H] (y : ℂ)) (𝓝 (a * (x + 1 - ξ))) := by
      have := ((continuous_re.tendsto _).comp hz)
      simp only [ofReal_re] at this
      exact ((this.add_const 1).sub_const ξ).const_mul a
    have hle := le_of_tendsto_of_tendsto ((continuous_re.tendsto _).comp hT) hlim2 hbound
    have hK3 : |M / a - 1 + ξ| + 1 ≤ K := le_max_right _ _
    have hxM : x + 1 - ξ < M / a := by
      have := neg_abs_le (M / a - 1 + ξ)
      linarith
    have := (lt_div_iff₀ ha).1 hxM
    linarith
  · -- the phase tends to `2π`
    have h1 := (tendsto_im_physicalRestartLog_two_pi hB htgt ht1 htd).comp hinv
    have h2 := (tendsto_im_logDerivPsi_zero hw hw0 hs hsubK htgt ht0 htd).comp hinv
    have h := h1.sub h2
    rw [sub_zero] at h
    exact h

end Main

/-! ### The source form: the branch integer and the landing height, unconditionally -/

/-- **The strict left base gap from a landing in `ℍ`**: if the physical point of `x > 0` is in `ℍ`, the
left base image is strictly left of the driver. -/
theorem gap_of_extendFrom_mem_H {w : ℝ → ℝ} {γ : ℝ → ℂ} {s : ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hγ : IsLoewnerTrace w γ) (hs : 0 ≤ s) {x : ℝ} (hx : 0 < x)
    (hF : extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ∈ H) :
    -rightImg (fun r => -w r) 0 s - w s < 0 := by
  rw [negInv_ofReal] at hF
  have h := neg_rightImg_sub_lt_of_extendFrom_mem_H hγ hw hw0 hs hF
  have : -x⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hx)
  linarith

open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign LawUnique GlueCond Cond44Ref Aux61GWord in
/-- **`TargetSideBranch` on the selected records**: almost surely on the selected records, the record's
chart has the target-side comparison points whenever the strict left base gap holds. -/
theorem ae_targetSideBranch {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i →
      -rightImg (fun r => -cfW S p r) 0 (rationalTime S.s) - cfW S p (rationalTime S.s) < 0 →
      TargetSideBranch (cfW S p) (rationalTime S.s) ((S.marksData F).chart i p) := by
  filter_upwards [hgeometry, S.physical_path, hR.physical_stop i, hcf]
    with p hg hp hstop hcfp hB hgap
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hc : ((S.marksData F).chart i p).IsConformal := (hR.spec i).conf p he
  have hgeo := hg he
  have hW := hp.1.continuous_rpath
  have hW0 : (fun t : ℝ => S.own.W t.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hBh := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo.simply hc.dom_subset hgeo.target
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ cfHullQ (rationalTime S.s) p.2 :=
    fun z hz => ⟨(hgeo.retained hz).1, fun hK => (hgeo.retained hz).2 (Or.inl hK)⟩
  have hKsub : negInv '' fwdHull (cfW S p) (rationalTime S.s) ⊆ cfHullQ (rationalTime S.s) p.2 :=
    image_mono (fwdHull_subset_hullAt (rationalTime S.s) p.2)
  have hsubK : (((S.marksData F).chart i p).dom : Set ℂ) ⊆
      H \ negInv '' fwdHull (cfW S p) (rationalTime S.s) :=
    fun z hz => ⟨(hsub hz).1, fun hK => (hsub hz).2 (hKsub hK)⟩
  obtain ⟨δ, hδ, htgt⟩ := hgeo.target
  exact targetSideBranch_of_target hw hw0 hγ hs hc hsubK hBh hscale ha hδ htgt hgap

open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign LawUnique GlueCond Cond44Ref Aux61GWord in
/-- **The realized landing height is `eastHeight S 1`** (unconditional source form): almost surely on
the selected records, at every chart point `b` with a counterflow collar access (no fibre clause) whose
counterflow point `x` lies east of the junction and has its physical point in `ℍ`, the relative phase
tends to `2π`, and a word height obeying `CfAccess`'s height clause is `eastHeight S 1`
(`= λ + πχ + (θ₂ − θ₁)χ`, satisfying both RefPos's and RefNeg's bounds). -/
theorem ae_height_eq_eastHeight_one {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i →
      ∀ (b ξ₀ δ x : ℝ), 0 < δ → (x : ℂ) ∈ ball (ξ₀ : ℂ) δ →
      MapsTo (revChartInv (cfW S p) (rationalTime S.s)) (H ∩ ball (ξ₀ : ℂ) δ)
        ((S.marksData F).chart i p).dom →
      (∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
        extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x' : ℂ)) ≠ 0 ∧
        cfBdry (cfW S p) (rationalTime S.s) x' ≠ 1) →
      Tendsto (fun z => ((S.marksData F).chart i p).1 (revChartInv (cfW S p) (rationalTime S.s) z))
        (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) →
      junR (cfW S p) (rationalTime S.s) < x →
      extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x : ℂ)) ∈ H →
      Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
        (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
        (𝓝[H] (b : ℂ)) (𝓝 (2 * π)) ∧
      ((∀ phase : ℝ, Tendsto (fun z => ((S.marksData F).chart i p).2.2
          (((S.marksData F).chart i p).2.1 z) -
          (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
          (𝓝[H] (b : ℂ)) (𝓝 phase) →
        (F.data i).bR b = returnedCfData S.κ (sourceCounterBoundary S)
          (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 x + S.θ * chiC S.κ + chiC S.κ * phase) →
        (F.data i).bR b = eastHeight S 1) := by
  filter_upwards [ae_phase_two_pi_of_access hR i hgeometry hcf, ae_targetSideBranch hR i hgeometry hcf,
    hcf] with p hph htsb hcfp hB b ξ₀ δ x hδ hx hcol hfin hxb hxe hF
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hx0 : 0 < x := (Aux61Kernel.junR_nonneg hw hs).trans_lt hxe
  have hgap := gap_of_extendFrom_mem_H hw hw0 hγ hs hx0 hF
  have hphase := hph hB (htsb hB hgap) b ξ₀ δ x hδ hx hcol hfin hxb hxe
  exact ⟨hphase, fun hword => height_eq_eastHeight_one S p hγ hw0 hx0 hF hphase hword⟩

end InteractingSLE.Sec5.Aux61Nj
