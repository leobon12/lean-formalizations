/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgSlit

/-!
# G3 (ii), Proposition 4.9 direction: the per-point inputs of the slit-side limits (R2a–R2c)

Packet PROVE-GLUECOND10 (PROVE-GLUECOND8's "What remains" 2). Notation as in `GlueCondUnionImgSlit`: flow driver `Wα`
with a simple proper trace `α`, flow time `t > 0`; counterflow chart `Ψ = revChart ω s`; image chain `W′` with a
simple proper trace `η′`, image time `T > 0`, `F′_T = fwdMapInv W′ T`, `Φ = Ψ⁻¹ ∘ F′_T`, `Θ = f_t ∘ Φ = imgTheta`.

* **the boundary values of `F′_T` on the real line** (`extendFrom_mem_H_of_chartAL_lt`,
  `extendFrom_chartAL_eq_zero`, `extendFrom_chartAR_eq_zero`, `re_extendFrom_neg_of_lt_chartAL`,
  `re_extendFrom_pos_of_chartAR_lt`): strictly between the two base points (except at the tip `0`) the boundary value
  is a point of the image slit in `ℍ` (R2a); the base points go to `0`; left of `chartAL` (right of `chartAR`) the
  boundary value is a negative (positive) real point;
* **(R2a)** the per-point inputs at the slit points;
* **(R2b)** the per-point inputs at the base points: `Φ → 0` there, so every cluster value of `Θ` is a nonzero real
  point (`F_t` sends it to `0`; the tip `F̄_t(0) = α(t)` is not `0`);
* **(R2c)** the per-point inputs at the physical real points next to the base points, and the branch `→ 0` there
  (Aux. 57 three times).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.GlueImg

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79

/-! ### The boundary values of the inverse map on the real line -/

section Bdry

variable {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- The boundary value of `F′_T` at a real point is a real point or a point of `ℍ`. -/
theorem extendFrom_im_nonneg (hη' : IsLoewnerTrace W' η') (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (x : ℝ) : 0 ≤ (extendFrom H (fwdMapInv W' T) x).im :=
  extendFrom_mem_Hbar hη' hW' hW'0 hT (show (0 : ℝ) ≤ (x : ℂ).im by simp)

/-- A real boundary value of `F′_T` at a real point: `0` only at the base points, a positive value only right of
`chartAR`, a negative value only left of `chartAL`. -/
theorem extendFrom_real_cases (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 < T) {x : ℝ} (him : (extendFrom H (fwdMapInv W' T) x).im = 0) :
    ((extendFrom H (fwdMapInv W' T) x).re = 0 ∧ (x = chartAL W' T ∨ x = chartAR W' T)) ∨
      (0 < (extendFrom H (fwdMapInv W' T) x).re ∧ chartAR W' T < x) ∨
      ((extendFrom H (fwdMapInv W' T) x).re < 0 ∧ x < chartAL W' T) := by
  set r := extendFrom H (fwdMapInv W' T) x with hrdef
  have hF : extendFrom H (fwdMapInv W' T) x = (r.re : ℂ) := by
    rw [← hrdef]; exact Complex.ext (by simp) (by simp [him])
  rcases lt_trichotomy r.re 0 with hneg | h0 | hpos
  · right; right
    refine ⟨hneg, ?_⟩
    rw [eq_neg_gImg_of_extendFrom_neg hη' hη'p hW' hW'0 hT.le hneg hF, chartAL]
    have := rightImg_lt_gImg_of_lt (show Continuous fun s => -W' s from hW'.neg) hT.le
      (alive_neg_of_isProperArc hη' hη'p hW' hW'0 hT.le) le_rfl (neg_pos.2 hneg)
    linarith
  · left
    refine ⟨h0, ?_⟩
    have hF0 : extendFrom H (fwdMapInv W' T) x = 0 := by rw [hF, h0, Complex.ofReal_zero]
    rcases extendFrom_eq_zero_imp hη' hη'p hW' hW'0 hT hF0 with h | h
    · right; rw [chartAR]; linarith
    · left; rw [chartAL]; linarith
  · right; left
    refine ⟨hpos, ?_⟩
    rw [eq_gImg_of_extendFrom_pos hη' hη'p hW' hW'0 hT.le hpos hF, chartAR]
    have := rightImg_lt_gImg_of_lt hW' hT.le (alive_of_isProperArc hη' hη'p hW' hW'0 hT.le) le_rfl hpos
    linarith

/-- **(R2a) Points strictly between the base points (other than the tip) are slit points**: their boundary value
lies in `ℍ`. -/
theorem extendFrom_mem_H_of_chartAL_lt (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 < T) {x : ℝ} (hxL : chartAL W' T < x) (hxR : x < chartAR W' T) :
    extendFrom H (fwdMapInv W' T) x ∈ H := by
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le x).lt_or_eq with hpos | h0
  · exact hpos
  · rcases extendFrom_real_cases hη' hη'p hW' hW'0 hT h0.symm with ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hxL.ne'
    · exact absurd h hxR.ne
    · exact absurd h (not_lt.2 hxR.le)
    · exact absurd h (not_lt.2 hxL.le)

/-- A point with boundary value in `ℍ` lies strictly between the base points. -/
theorem chartAL_lt_of_extendFrom_mem_H (hη' : IsLoewnerTrace W' η') (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hT : 0 ≤ T) {x : ℝ} (hx : extendFrom H (fwdMapInv W' T) x ∈ H) :
    chartAL W' T < x ∧ x < chartAR W' T :=
  ⟨neg_rightImg_sub_lt_of_extendFrom_mem_H hη' hW' hW'0 hT hx, lt_rightImg_sub_of_extendFrom_mem_H hη' hW' hW'0 hT hx⟩

/-- **The left base point goes to `0`.** -/
theorem extendFrom_chartAL_eq_zero (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 < T) : extendFrom H (fwdMapInv W' T) (chartAL W' T) = 0 := by
  have hAR := chartAR_nonneg hW' hT.le (W' := W')
  have hAL := chartAL_nonpos hW' hT.le (W' := W')
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le (chartAL W' T)).lt_or_eq with hpos | h0
  · exact absurd (chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos).1 (lt_irrefl _)
  · rcases extendFrom_real_cases hη' hη'p hW' hW'0 hT h0.symm with ⟨hr, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Complex.ext (by simpa using hr) (by simpa using h0.symm)
    · exact absurd h (not_lt.2 (hAL.trans hAR))
    · exact absurd h (lt_irrefl _)

/-- **The right base point goes to `0`.** -/
theorem extendFrom_chartAR_eq_zero (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 < T) : extendFrom H (fwdMapInv W' T) (chartAR W' T) = 0 := by
  have hAR := chartAR_nonneg hW' hT.le (W' := W')
  have hAL := chartAL_nonpos hW' hT.le (W' := W')
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le (chartAR W' T)).lt_or_eq with hpos | h0
  · exact absurd (chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos).2 (lt_irrefl _)
  · rcases extendFrom_real_cases hη' hη'p hW' hW'0 hT h0.symm with ⟨hr, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Complex.ext (by simpa using hr) (by simpa using h0.symm)
    · exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.2 (hAL.trans hAR))

/-- Left of the left base point the boundary value is a negative real point. -/
theorem re_extendFrom_neg_of_lt_chartAL (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 < T) {x : ℝ} (hx : x < chartAL W' T) :
    (extendFrom H (fwdMapInv W' T) x).im = 0 ∧ (extendFrom H (fwdMapInv W' T) x).re < 0 := by
  have hAR := chartAR_nonneg hW' hT.le (W' := W')
  have hAL := chartAL_nonpos hW' hT.le (W' := W')
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le x).lt_or_eq with hpos | h0
  · exact absurd (chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos).1 (not_lt.2 hx.le)
  · refine ⟨h0.symm, ?_⟩
    rcases extendFrom_real_cases hη' hη'p hW' hW'0 hT h0.symm with ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h hx.ne
    · exact absurd h (by linarith)
    · exact absurd h (by linarith)
    · exact h

/-- Right of the right base point the boundary value is a positive real point. -/
theorem re_extendFrom_pos_of_chartAR_lt (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 < T) {x : ℝ} (hx : chartAR W' T < x) :
    (extendFrom H (fwdMapInv W' T) x).im = 0 ∧ 0 < (extendFrom H (fwdMapInv W' T) x).re := by
  have hAR := chartAR_nonneg hW' hT.le (W' := W')
  have hAL := chartAL_nonpos hW' hT.le (W' := W')
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le x).lt_or_eq with hpos | h0
  · exact absurd (chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos).2 (not_lt.2 hx.le)
  · refine ⟨h0.symm, ?_⟩
    rcases extendFrom_real_cases hη' hη'p hW' hW'0 hT h0.symm with ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by linarith)
    · exact absurd h hx.ne'
    · exact h
    · exact absurd h (by linarith)

end Bdry

/-! ### The base points and the physical real points next to them -/

section Points

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- A ball around a point off the closure of `K` that misses `K`. -/
theorem exists_ball_disjoint_of_notMem_closure {K : Set ℂ} {z : ℂ} (hz : z ∉ closure K) :
    ∃ ρ > 0, Disjoint (ball z ρ) K := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z hz
  exact ⟨ρ, hρ, Set.disjoint_left.2 fun w hw hwK => hball hw (subset_closure hwK)⟩

/-- **`Ψ⁻¹ → 0` at the counterflow's tip `Ψ = 0`**: `Ψ⁻¹ = R ∘ F_s ∘ R`, `R` exchanges `0` and `∞`, and `F_s` moves
points by a bounded amount. -/
theorem tendsto_revChartInv_nhdsWithin_zero (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) :
    Tendsto (revChartInv Wβ s) (𝓝[H] 0) (𝓝 0) := by
  have h1 : Tendsto negInv (𝓝[H] (0 : ℂ)) (Bornology.cobounded ℂ ⊓ 𝓟 H) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_nhdsWithin_of_forall fun z hz => negInv_mem_H hz)⟩
    have hle : 𝓝[H] (0 : ℂ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ fun z hz h0 => by
      rw [mem_singleton_iff.1 h0] at hz
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz |>.trans_eq (by simp))
    exact tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.mono_left hle)
  have h2 := InteractingSLE.tendsto_fwdMapInv_cobounded hWβ hWβ0 hs
  have h3 : Tendsto negInv (Bornology.cobounded ℂ) (𝓝 0) := by
    have := (tendsto_inv₀_cobounded (α := ℂ)).neg
    rwa [neg_zero] at this
  exact h3.comp (h2.comp h1)

/-- The branch of `arg Θ′` read along `Φ`. -/
abbrev imgBranch (Wα : ℝ → ℝ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) (y : ℂ) : ℝ :=
  (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im -
    ((logDerivFwd W' T (fwdMapInv W' T y)).im + (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im)

/-- **(R2b) The per-point inputs at a base point of the image slit**: if `F̄′_T(x) = 0`, then `Θ` has a nonzero real
limit at `x` and the branch tends to a multiple of `2π`. (`Φ → 0`, so every cluster value `p` of the bounded `Θ` has
`F̄_t(p) = 0`: `p ∉ ℍ`, and `p ≠ 0` because `F̄_t(0) = α(t) ∈ ℍ`.) -/
theorem imgTheta_limits_of_extendFrom_eq_zero {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x : ℝ} (hx : extendFrom H (fwdMapInv W' T) x = 0) :
    (∃ p : ℝ, p ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) ∧
      ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)) := by
  have hF : Tendsto (fwdMapInv W' T) (𝓝[H] (x : ℂ)) (𝓝[H] ((0 : ℝ) : ℂ)) :=
    tendsto_fwdMapInv_nhdsWithin_of_real hη' hW' hW'0 hT (by rw [hx]; simp)
  rw [Complex.ofReal_zero] at hF
  have hΦ : Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 0) :=
    (tendsto_revChartInv_nhdsWithin_zero hWβ hWβ0 hs).comp hF
  have := nhdsWithin_H_neBot x
  set U := Ultrafilter.of (𝓝[H] (x : ℂ)) with hUdef
  have hU : (U : Filter ℂ) ≤ 𝓝[H] (x : ℂ) := Ultrafilter.of_le _
  obtain ⟨C, -, hC⟩ := exists_norm_fwdMap_sub_le hWα hWα0 ht.le
  have hmem : ∀ᶠ y in 𝓝[H] (x : ℂ), revChartInv Wβ s (fwdMapInv W' T y) ∈
      H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) :=
    eventually_nhdsWithin_of_forall fun y hy => revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
  have hsmall : ∀ᶠ y in 𝓝[H] (x : ℂ), revChartInv Wβ s (fwdMapInv W' T y) ∈ ball (0 : ℂ) 1 :=
    hΦ (ball_mem_nhds _ one_pos)
  have hbd : ∀ᶠ y in 𝓝[H] (x : ℂ), imgTheta Wα t Wβ s W' T y ∈ closedBall (0 : ℂ) (C + 1) := by
    filter_upwards [hmem, hsmall] with y hy1 hy2
    have h1 := hC _ ⟨hy1.1, fun h => hy1.2 (Or.inl h)⟩
    rw [mem_ball_zero_iff] at hy2
    rw [mem_closedBall_zero_iff]
    calc ‖imgTheta Wα t Wβ s W' T y‖ = ‖(fwdMap Wα t (revChartInv Wβ s (fwdMapInv W' T y)) -
          revChartInv Wβ s (fwdMapInv W' T y)) + revChartInv Wβ s (fwdMapInv W' T y)‖ := by
          rw [sub_add_cancel]; rfl
      _ ≤ C + 1 := (norm_add_le _ _).trans (add_le_add h1 hy2.le)
  obtain ⟨p, -, hp⟩ := (isCompact_closedBall (0 : ℂ) (C + 1)).ultrafilter_le_nhds
    (U.map (imgTheta Wα t Wβ s W' T)) (by rw [Ultrafilter.coe_map]; exact tendsto_principal.2 (hU hbd))
  have hΘU : Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 p) := by rwa [Ultrafilter.coe_map] at hp
  have hΘH : ∀ᶠ y in (U : Filter ℂ), imgTheta Wα t Wβ s W' T y ∈ H := hU (hmem.mono fun y hy =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le ⟨hy.1, fun h => hy.2 (Or.inl h)⟩)
  have hpH : p ∈ Hbar := closure_H ▸ mem_closure_of_tendsto hΘU hΘH
  have hB := hα.hasBdryLimits hWα hWα0 ht.le
  have h1 : Tendsto (fun y => fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y)) U
      (𝓝 (extendFrom H (fwdMapInv Wα t) p)) :=
    (hB.tendsto hpH).comp (tendsto_nhdsWithin_iff.2 ⟨hΘU, hΘH⟩)
  have h2 : Tendsto (fun y => fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y)) U (𝓝 0) := by
    refine (hΦ.mono_left hU).congr' (hU (hmem.mono fun y hy => ?_))
    exact show _ = fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y) from
      (QuantumZipper.RS.fwdMapInv_fwdMap hWα hWα0 ht.le ⟨hy.1, fun h => hy.2 (Or.inl h)⟩).symm
  have hp0 : extendFrom H (fwdMapInv Wα t) p = 0 := tendsto_nhds_unique h1 h2
  have hpR : p.im = 0 := by
    rcases (show (0 : ℝ) ≤ p.im from hpH).lt_or_eq with hpos | h0
    · exfalso
      have e := extendFrom_fwdMapInv_eq hWα hWα0 ht.le (show p ∈ H from hpos)
      have hm := QuantumZipper.RS.fwdMapInv_mem_H hWα hWα0 ht.le (show p ∈ H from hpos)
      rw [← e, hp0] at hm
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hm |>.trans_eq (by simp))
    · exact h0.symm
  have hpne : p.re ≠ 0 := by
    intro h
    have hp' : p = 0 := Complex.ext (by simpa using h) (by simpa using hpR)
    rw [hp', extendFrom_zero hα hWα hWα0 ht.le] at hp0
    have hm := hαp.mem_H t ht
    rw [hp0] at hm
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hm |>.trans_eq (by simp))
  have hpe : p = (p.re : ℂ) := Complex.ext (by simp) (by simp [hpR])
  rw [hpe] at hΘU
  exact imgTheta_limits_of_ultrafilter hα hWα hWα0 ht.le hKt hWβ hWβ0 hs hW' hW'0 hT hGc hdisj hdis hK' hpne hU hΘU


open CrossCond.Word49 (junL junR)

/-- **(R2c) A physical real point left of the left base point** (`F̄′_T(x) = r` with `junL < r < 0`): `Ψ⁻¹` sends `r`
to a negative physical real point `z₀` (`R(r)` lies right of the counterflow's right base image), so `Θ` tends to the
negative real point `f̄_t(z₀)`, and the branch tends to `0` (Aux. 57 for `f_t` at `z₀`, for `f′_T` at `r`, and the
normalized `arg_Ψ` at `z₀`). -/
theorem imgTheta_tendsto_of_extendFrom_neg {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjL : 0 < rightImg Wβ 0 s - Wβ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') {x r : ℝ} (hx : extendFrom H (fwdMapInv W' T) x = r) (hr0 : r < 0)
    (hrj : junL Wβ s < r) :
    (∃ p : ℝ, p < 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set g₀ := rightImg Wβ 0 s - Wβ s with hg₀
  set ρ : ℝ := -r⁻¹ with hρdef
  have hρ : rightImg Wβ 0 s < ρ + Wβ s := by
    have h1 : -1 < r * g₀ := by
      have := hrj
      rw [junL, ← hg₀, div_lt_iff₀ hjL] at this
      exact this
    have h2 : g₀ < ρ := by
      rw [hρdef, show -r⁻¹ = 1 / (-r) by rw [one_div, inv_neg], lt_div_iff₀ (neg_pos.2 hr0)]
      linarith
    linarith
  obtain ⟨y, hy0, hya, hyg⟩ := exists_alive_gImg_eq hWβ hs hρ
  have hu := isForwardSol_of_alive hWβ hya
  have hcf : cflow Wβ y s = ρ := by rw [gImg] at hyg; linarith
  have hFs : extendFrom H (fwdMapInv Wβ s) (ρ : ℂ) = y := by
    have := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hWβ hWβ0 hs (show (0 : ℝ) ≤ (y : ℂ).im by simp) hu
    simpa only [hcf] using this
  have h1 := tendsto_fwdMapInv_nhdsWithin_of_real hη' hW' hW'0 hT hx
  have h2 := (tendsto_negInv_nhdsWithin_H hr0.ne).comp h1
  have h3 : Tendsto (fun y' => fwdMapInv Wβ s (negInv (fwdMapInv W' T y'))) (𝓝[H] (x : ℂ)) (𝓝[H] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y' hy' =>
      QuantumZipper.RS.fwdMapInv_mem_H hWβ hWβ0 hs
        (negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy'))⟩
    have := (hB.tendsto (show (0 : ℝ) ≤ ((ρ : ℝ) : ℂ).im by simp)).comp h2
    rw [hFs] at this
    exact this
  have hΦ : Tendsto (fun y' => revChartInv Wβ s (fwdMapInv W' T y')) (𝓝[H] (x : ℂ))
      (𝓝[H] ((-y⁻¹ : ℝ) : ℂ)) := (tendsto_negInv_nhdsWithin_H hy0.ne').comp h3
  set z₀ : ℝ := -y⁻¹ with hz₀def
  have hz₀ : z₀ < 0 := neg_neg_of_pos (inv_pos.2 hy0)
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hα hαp hWα hWα0 hz₀.ne ht.le
  rcases isForwardSol_real_cases hWα hWα0 ht.le hv with ⟨hpos, -, -⟩ | ⟨-, hal, hvt⟩
  · exact absurd hpos (not_lt.2 hz₀.le)
  refine ⟨⟨-gImg (fun r => -Wα r) (-z₀) t - Wα t, ?_, ?_⟩, ?_⟩
  · have := hal.lt_gImg (show Continuous fun r => -Wα r from hWα.neg) ⟨ht.le, le_rfl⟩
    linarith
  · have := (tendsto_fwdMap_of_isForwardSol hWα ht.le hv).comp hΦ
    rw [hvt] at this
    exact this
  -- the branch
  obtain ⟨ρ₁, hρ₁, hd₁⟩ := exists_ball_disjoint_of_notMem_closure (hKt z₀ hz₀.ne)
  have a1 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hWα ht.le)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hWα hWα0 ht.le) (isMapOut_fwdMap hWα hWα0 ht.le) hρ₁ hd₁).comp hΦ
  obtain ⟨ρ₂, hρ₂, hd₂⟩ := exists_ball_disjoint_fwdHull_of_isProperArc hη' hη'p hT hr0.ne
  have a2 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hW' hT)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW' hW'0 hT) (isMapOut_fwdMap hW' hW'0 hT) hρ₂ hd₂).comp h1
  have hy' : ((-z₀⁻¹ : ℝ) : ℂ) ∉ closure (fwdHull Wβ s) := by
    intro hm
    have := hKs _ hm (by simp)
    rw [hz₀def, inv_neg, neg_neg, inv_inv] at this
    exact hy0.ne' (by exact_mod_cast this)
  obtain ⟨ρ₃, hρ₃, hd₃⟩ := exists_ball_disjoint_of_notMem_closure hy'
  have a3 := (tendsto_im_logDerivPsi hWβ hWβ0 hs hz₀.ne hρ₃ hd₃).comp hΦ
  have h := a1.sub (a2.add a3)
  rw [add_zero, sub_zero] at h
  exact h

/-- **(R2c), right mirror**: a physical real point right of the right base point (`0 < r < junR`): `Θ` tends to a
positive real point and the branch tends to `0`. -/
theorem imgTheta_tendsto_of_extendFrom_pos {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0)
    (hjR : -rightImg (fun r => -Wβ r) 0 s - Wβ s < 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') {x r : ℝ} (hx : extendFrom H (fwdMapInv W' T) x = r) (hr0 : 0 < r)
    (hrj : r < junR Wβ s) :
    (∃ p : ℝ, 0 < p ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set h₀ := -rightImg (fun r => -Wβ r) 0 s - Wβ s with hh₀
  set ρ : ℝ := -r⁻¹ with hρdef
  have hρ : rightImg (fun r => -Wβ r) 0 s < -ρ + -Wβ s := by
    have h1 : r * (-h₀) < 1 := by
      have := hrj
      rw [junR, ← hh₀, lt_div_iff_of_neg hjR] at this
      linarith
    have h2 : ρ < h₀ := by
      have hr' : 0 < r⁻¹ := inv_pos.2 hr0
      have e : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
      rw [hρdef]
      nlinarith
    linarith
  obtain ⟨y, hy0, hya, hyg⟩ := exists_alive_gImg_eq (show Continuous fun r => -Wβ r from hWβ.neg) hs hρ
  have hu := isForwardSol_neg_of_alive hWβ hya
  have hcf : cflow (fun r => -Wβ r) y s = -ρ := by rw [gImg] at hyg; linarith
  have hFs : extendFrom H (fwdMapInv Wβ s) (ρ : ℂ) = -(y : ℂ) := by
    have := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hWβ hWβ0 hs (show (0 : ℝ) ≤ (-(y : ℂ)).im by simp) hu
    simp only [hcf, Complex.ofReal_neg, neg_neg] at this
    exact this
  have h1 := tendsto_fwdMapInv_nhdsWithin_of_real hη' hW' hW'0 hT hx
  have h2 := (tendsto_negInv_nhdsWithin_H hr0.ne').comp h1
  have h3 : Tendsto (fun y' => fwdMapInv Wβ s (negInv (fwdMapInv W' T y'))) (𝓝[H] (x : ℂ))
      (𝓝[H] ((-y : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y' hy' =>
      QuantumZipper.RS.fwdMapInv_mem_H hWβ hWβ0 hs
        (negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy'))⟩
    have := (hB.tendsto (show (0 : ℝ) ≤ ((ρ : ℝ) : ℂ).im by simp)).comp h2
    rw [hFs] at this
    rw [Complex.ofReal_neg]
    exact this
  have hΦ : Tendsto (fun y' => revChartInv Wβ s (fwdMapInv W' T y')) (𝓝[H] (x : ℂ))
      (𝓝[H] ((-(-y)⁻¹ : ℝ) : ℂ)) := (tendsto_negInv_nhdsWithin_H (neg_ne_zero.2 hy0.ne')).comp h3
  set z₀ : ℝ := -(-y)⁻¹ with hz₀def
  have hz₀ : 0 < z₀ := by rw [hz₀def, inv_neg, neg_neg]; exact inv_pos.2 hy0
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hα hαp hWα hWα0 hz₀.ne' ht.le
  rcases isForwardSol_real_cases hWα hWα0 ht.le hv with ⟨-, hal, hvt⟩ | ⟨hneg, -, -⟩
  swap
  · exact absurd hneg (not_lt.2 hz₀.le)
  refine ⟨⟨gImg Wα z₀ t - Wα t, ?_, ?_⟩, ?_⟩
  · have := hal.lt_gImg hWα ⟨ht.le, le_rfl⟩
    linarith
  · have := (tendsto_fwdMap_of_isForwardSol hWα ht.le hv).comp hΦ
    rw [hvt] at this
    exact this
  obtain ⟨ρ₁, hρ₁, hd₁⟩ := exists_ball_disjoint_of_notMem_closure (hKt z₀ hz₀.ne')
  have a1 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hWα ht.le)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hWα hWα0 ht.le) (isMapOut_fwdMap hWα hWα0 ht.le) hρ₁ hd₁).comp hΦ
  obtain ⟨ρ₂, hρ₂, hd₂⟩ := exists_ball_disjoint_fwdHull_of_isProperArc hη' hη'p hT hr0.ne'
  have a2 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hW' hT)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW' hW'0 hT) (isMapOut_fwdMap hW' hW'0 hT) hρ₂ hd₂).comp h1
  have hy' : ((-z₀⁻¹ : ℝ) : ℂ) ∉ closure (fwdHull Wβ s) := by
    intro hm
    have := hKs _ hm (by simp)
    rw [hz₀def, inv_neg, neg_neg, inv_inv] at this
    exact hy0.ne' (neg_eq_zero.1 (by exact_mod_cast this))
  obtain ⟨ρ₃, hρ₃, hd₃⟩ := exists_ball_disjoint_of_notMem_closure hy'
  have a3 := (tendsto_im_logDerivPsi hWβ hWβ0 hs hz₀.ne' hρ₃ hd₃).comp hΦ
  have h := a1.sub (a2.add a3)
  rw [add_zero, sub_zero] at h
  exact h

end Points

/-! ### The slit points and the slit-side limits -/

section Slit

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **(R2a) The per-point inputs at a slit point of the image chart** (`chartAL W′ T < x < chartAR W′ T`, `x ≠ 0`):
the boundary value is `Ψ(α(u))` with `0 < u < t` (not the tip: only `0` goes to the tip), `Φ → α(u)` within
`ℍ ∖ (A ∪ G)`, `Θ` tends to a real point `x₁` strictly between the flow's base points, and the branch tends to a
multiple of `2π`. -/
theorem imgTheta_limits_of_slit {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T)
    {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t)) {x : ℝ}
    (hxL : chartAL W' T < x) (hxR : x < chartAR W' T) (hx0 : x ≠ 0) :
    ∃ u : ℝ, 0 < u ∧ u < t ∧
      Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ))
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] (α u)) ∧
      ∃ x₁ : ℝ, x₁ ≠ 0 ∧ chartAL Wα t < x₁ ∧ x₁ < chartAR Wα t ∧
        Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ)) ∧
        ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)) := by
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hFH := extendFrom_mem_H_of_chartAL_lt hη' hη'p hW' hW'0 hT hxL hxR
  have hlim := (hη'.hasBdryLimits hW' hW'0 hT.le).tendsto hxH
  have hK := boundary_value_notMem hW' hW'0 hT.le hlim
  have hKmem : extendFrom H (fwdMapInv W' T) x ∈ fwdHull W' T := by
    by_contra h; exact hK ⟨hFH, h⟩
  rw [hK', fwdHull_eq_image_Ioc hα hαp ht.le, image_image] at hKmem
  obtain ⟨u, ⟨hu0, hut⟩, hFu⟩ := hKmem
  have hut' : u < t := by
    rcases hut.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h] at hFu
      dsimp only at hFu
      rw [← htip] at hFu
      exact hx0 (eq_zero_of_extendFrom_eq_tip hη' hη'p hW' hW'0 hT hFu.symm)
  have hαu : α u ∈ fwdHull Wα t := by
    rw [fwdHull_eq_image_Ioc hα hαp ht.le]; exact ⟨u, ⟨hu0, hut⟩, rfl⟩
  have hαuG : α u ∈ H \ negInv '' fwdHull Wβ s := ⟨hαp.mem_H u hu0, fun h => disjoint_left.1 hdisj hαu h⟩
  have hΦ : Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] (α u)) := by
    rw [← hFu] at hlim
    have hrH : revChart Wβ s (α u) ∈ H := revChart_mem_H hWβ hs hαuG
    have h2 : ContinuousAt (revChartInv Wβ s) (revChart Wβ s (α u)) :=
      (continuousOn_revChartInv hWβ hWβ0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hrH)
    have h3 := h2.tendsto.comp hlim
    rw [revChartInv_revChart hWβ hWβ0 hs hαuG] at h3
    exact tendsto_nhdsWithin_iff.2 ⟨h3, eventually_nhdsWithin_of_forall fun y hy =>
      revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT.le hK' hy⟩
  obtain ⟨x₁, hx₁0, hFx₁, hΘ, lam, hlam, hd⟩ := tendsto_imgTheta_of_mem_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW'
    hW'0 hT.le hη' hGc hdisj hdis hK' hu0 hut' hFu.symm
  have hx₁ := chartAL_lt_of_extendFrom_mem_H hα hWα hWα0 ht.le (x := x₁) (by rw [hFx₁]; exact hαp.mem_H u hu0)
  exact ⟨u, hu0, hut', hΦ, x₁, hx₁0, hx₁.1, hx₁.2, hΘ,
    exists_int_tendsto_argTheta hWα ht.le hWβ hWβ0 hs hW' hW'0 hT.le hK' hlam hd⟩

/-- The real boundary map of `F′_T` is continuous. -/
theorem continuous_extendFrom_ofReal {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hT : 0 ≤ T) : Continuous fun x : ℝ => extendFrom H (fwdMapInv W' T) (x : ℂ) :=
  ((hη'.hasBdryLimits hW' hW'0 hT).continuousOn).comp_continuous Complex.continuous_ofReal
    fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp


open CrossCond.Word49 (junL junR)

variable {κ : ℝ} {nL nR mL mR : ℕ}

/-- **The slit-side limit on the left side of the image slit** (R2a–R2d assembled, deterministic). With the flow-side
limit of the union mean at every non-tip point `α(u)` of the flow slit (`hFl`, the first limit of
`ae_union_mean_cfGlue`), the candidate `M ∘ Φ + c − (u − χ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ))` tends to `0` at every
point `x ∈ (chartAL W′ T, 0)` of the image chart (`u_A`, `u` the bounded harmonic extensions of the flowed flow word
at `t` and of the flowed image word at `T`). The interval of `tendsto_imgChart_of_slit_left` is
`I = (chartAL − δ, 0)`, with `δ` so small that `F̄′_T` maps `(chartAL − δ, chartAL)` into `(junL, 0)`. -/
theorem tendsto_imgChart_slit_left_of_flow {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjL : 0 < rightImg Wβ 0 s - Wβ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {xL' : Fin mL → ℝ}
    {xR' : Fin mR → ℝ} (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun s => -Wα s) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun s => -Wα s) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR'
        (fun i => -rightImg (fun s => -W' s) (-xL' i) T - W' T) (fun j => rightImg W' (xR' j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun s => -W' s) (-xL' i) T - W' T)
        (fun j => rightImg W' (xR' j) T - W' T)) u)
    {M : ℂ → ℝ} {c χ : ℝ}
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + c - (uA (fwdMap Wα t z) - χ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] (α v)) (𝓝 0))
    {x : ℝ} (hxL0 : chartAL W' T < x) (hx0 : x < 0) :
    Tendsto (fun y => M (revChartInv Wβ s (fwdMapInv W' T y)) + c - (u y - χ * ((logDerivFwd W' T (fwdMapInv W' T y)).im
      + (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hAL := chartAL_nonpos hW' hT.le (W' := W')
  have hAR := chartAR_nonneg hW' hT.le (W' := W')
  -- the physical interval next to the base point
  have hε : 0 < -junL Wβ s := by
    rw [junL, neg_div, neg_neg]; exact div_pos one_pos hjL
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 (continuous_extendFrom_ofReal hη' hW' hW'0 hT.le)
    (chartAL W' T) _ hε
  have hphys : ∀ x' : ℝ, chartAL W' T - δ < x' → x' < chartAL W' T →
      extendFrom H (fwdMapInv W' T) x' = ((extendFrom H (fwdMapInv W' T) x').re : ℂ) ∧
      (extendFrom H (fwdMapInv W' T) x').re < 0 ∧ junL Wβ s < (extendFrom H (fwdMapInv W' T) x').re := by
    intro x' h1 h2
    obtain ⟨him, hre⟩ := re_extendFrom_neg_of_lt_chartAL hη' hη'p hW' hW'0 hT h2
    refine ⟨Complex.ext (by simp) (by simp [him]), hre, ?_⟩
    have hd := hcont x' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [extendFrom_chartAL_eq_zero hη' hη'p hW' hW'0 hT, dist_zero_right] at hd
    have h3 := Complex.abs_re_le_norm (extendFrom H (fwdMapInv W' T) x')
    have h4 := neg_le_abs (extendFrom H (fwdMapInv W' T) x').re
    linarith
  have hR2c : ∀ x' : ℝ, chartAL W' T - δ < x' → x' < chartAL W' T →
      (∃ p : ℝ, p < 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
        Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    intro x' h1 h2
    obtain ⟨he, hneg, hj⟩ := hphys x' h1 h2
    exact imgTheta_tendsto_of_extendFrom_neg hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjL hW' hW'0 hT.le hη' hη'p
      he hneg hj
  set I : Set ℝ := Ioo (chartAL W' T - δ) 0 with hIdef
  have hlim : ∀ x' ∈ I, (∃ p : ℝ, p ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
      ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (2 * π * k)) := by
    intro x' hx'
    rcases lt_trichotomy x' (chartAL W' T) with h | h | h
    · obtain ⟨⟨p, hp, hΘp⟩, ha⟩ := hR2c x' hx'.1 h
      exact ⟨⟨p, hp.ne, hΘp⟩, 0, by simpa using ha⟩
    · rw [h]
      exact imgTheta_limits_of_extendFrom_eq_zero hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT.le hη' hGc hdisj
        hdis hK' (extendFrom_chartAL_eq_zero hη' hη'p hW' hW'0 hT)
    · obtain ⟨-, -, -, -, x₁, hx₁0, -, -, hΘ, hk⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW'
        hW'0 hT hη' hη'p hGc hdisj hdis hK' htip h (by linarith [hx'.2]) hx'.2.ne
      exact ⟨⟨x₁, hx₁0, hΘ⟩, hk⟩
  have hx₀ : chartAL W' T - δ / 2 ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨⟨p₀, hp₀, hΘ₀⟩, ha₀⟩ := hR2c (chartAL W' T - δ / 2) (by linarith) (by linarith)
  have hxI : x ∈ I := ⟨by linarith, hx0⟩
  obtain ⟨v, hv0, hvt, hΦ, x₁, -, hx₁L, hx₁R, hΘ, -⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs
    hW' hW'0 hT hη' hη'p hGc hdisj hdis hK' htip hxL0 (by linarith) hx0.ne
  have hA := (hFl v hv0 hvt).comp hΦ
  have hΘH : ∀ y ∈ H, imgTheta Wα t Wβ s W' T y ∈ H := fun y hy => by
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT.le hK' hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  exact tendsto_imgChart_of_slit_left hWα hW' ht.le hT.le hxL hxR hxL' hxR' huA hu hΘH isPreconnected_Ioo
    (Φ := fun y => revChartInv Wβ s (fwdMapInv W' T y))
    (LA := fun y => (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im)
    (LB := fun y => (logDerivFwd W' T (fwdMapInv W' T y)).im +
      (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im)
    (fun x' hx' => (hlim x' hx').1) (fun x' hx' => (hlim x' hx').2) hx₀ hp₀ hΘ₀ ha₀ hxI hxL0 hx0 hΘ hx₁L hx₁R hA


/-- **The slit-side limit on the right side of the image slit** (the mirror of
`tendsto_imgChart_slit_left_of_flow`; `I = (0, chartAR + δ)`, `F̄′_T` maps `(chartAR, chartAR + δ)` into
`(0, junR)`). -/
theorem tendsto_imgChart_slit_right_of_flow {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjR : -rightImg (fun r => -Wβ r) 0 s - Wβ s < 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {xL' : Fin mL → ℝ}
    {xR' : Fin mR → ℝ} (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) {uA u : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun s => -Wα s) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun s => -Wα s) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR'
        (fun i => -rightImg (fun s => -W' s) (-xL' i) T - W' T) (fun j => rightImg W' (xR' j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun s => -W' s) (-xL' i) T - W' T)
        (fun j => rightImg W' (xR' j) T - W' T)) u)
    {M : ℂ → ℝ} {c χ : ℝ}
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + c - (uA (fwdMap Wα t z) - χ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] (α v)) (𝓝 0))
    {x : ℝ} (hxR0 : x < chartAR W' T) (hx0 : 0 < x) :
    Tendsto (fun y => M (revChartInv Wβ s (fwdMapInv W' T y)) + c - (u y - χ * ((logDerivFwd W' T (fwdMapInv W' T y)).im
      + (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hAL := chartAL_nonpos hW' hT.le (W' := W')
  have hAR := chartAR_nonneg hW' hT.le (W' := W')
  have hε : 0 < junR Wβ s := by
    rw [junR, neg_div, ← div_neg]; exact div_pos one_pos (neg_pos.2 hjR)
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 (continuous_extendFrom_ofReal hη' hW' hW'0 hT.le)
    (chartAR W' T) _ hε
  have hphys : ∀ x' : ℝ, chartAR W' T < x' → x' < chartAR W' T + δ →
      extendFrom H (fwdMapInv W' T) x' = ((extendFrom H (fwdMapInv W' T) x').re : ℂ) ∧
      0 < (extendFrom H (fwdMapInv W' T) x').re ∧ (extendFrom H (fwdMapInv W' T) x').re < junR Wβ s := by
    intro x' h1 h2
    obtain ⟨him, hre⟩ := re_extendFrom_pos_of_chartAR_lt hη' hη'p hW' hW'0 hT h1
    refine ⟨Complex.ext (by simp) (by simp [him]), hre, ?_⟩
    have hd := hcont x' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [extendFrom_chartAR_eq_zero hη' hη'p hW' hW'0 hT, dist_zero_right] at hd
    have h3 := Complex.abs_re_le_norm (extendFrom H (fwdMapInv W' T) x')
    have h4 := le_abs_self (extendFrom H (fwdMapInv W' T) x').re
    linarith
  have hR2c : ∀ x' : ℝ, chartAR W' T < x' → x' < chartAR W' T + δ →
      (∃ p : ℝ, 0 < p ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
        Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    intro x' h1 h2
    obtain ⟨he, hpos, hj⟩ := hphys x' h1 h2
    exact imgTheta_tendsto_of_extendFrom_pos hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hB hKs hjR hW' hW'0 hT.le hη' hη'p
      he hpos hj
  set I : Set ℝ := Ioo 0 (chartAR W' T + δ) with hIdef
  have hlim : ∀ x' ∈ I, (∃ p : ℝ, p ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
      ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (2 * π * k)) := by
    intro x' hx'
    rcases lt_trichotomy x' (chartAR W' T) with h | h | h
    · obtain ⟨-, -, -, -, x₁, hx₁0, -, -, hΘ, hk⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW'
        hW'0 hT hη' hη'p hGc hdisj hdis hK' htip (by linarith [hx'.1]) h hx'.1.ne'
      exact ⟨⟨x₁, hx₁0, hΘ⟩, hk⟩
    · rw [h]
      exact imgTheta_limits_of_extendFrom_eq_zero hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT.le hη' hGc hdisj
        hdis hK' (extendFrom_chartAR_eq_zero hη' hη'p hW' hW'0 hT)
    · obtain ⟨⟨p, hp, hΘp⟩, ha⟩ := hR2c x' h hx'.2
      exact ⟨⟨p, hp.ne', hΘp⟩, 0, by simpa using ha⟩
  have hx₀ : chartAR W' T + δ / 2 ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨⟨p₀, hp₀, hΘ₀⟩, ha₀⟩ := hR2c (chartAR W' T + δ / 2) (by linarith) (by linarith)
  have hxI : x ∈ I := ⟨hx0, by linarith⟩
  obtain ⟨v, hv0, hvt, hΦ, x₁, -, hx₁L, hx₁R, hΘ, -⟩ := imgTheta_limits_of_slit hα hαp hWα hWα0 ht hKt hWβ hWβ0 hs
    hW' hW'0 hT hη' hη'p hGc hdisj hdis hK' htip (by linarith) hxR0 hx0.ne'
  have hA := (hFl v hv0 hvt).comp hΦ
  have hΘH : ∀ y ∈ H, imgTheta Wα t Wβ s W' T y ∈ H := fun y hy => by
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT.le hK' hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  exact tendsto_imgChart_of_slit_right hWα hW' ht.le hT.le hxL hxR hxL' hxR' huA hu hΘH isPreconnected_Ioo
    (Φ := fun y => revChartInv Wβ s (fwdMapInv W' T y))
    (LA := fun y => (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im)
    (LB := fun y => (logDerivFwd W' T (fwdMapInv W' T y)).im +
      (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im)
    (fun x' hx' => (hlim x' hx').1) (fun x' hx' => (hlim x' hx').2) hx₀ hp₀ hΘ₀ ha₀ hxI hxR0 hx0 hΘ hx₁L hx₁R hA

end Slit

end InteractingSLE.Sec5.GlueImg
