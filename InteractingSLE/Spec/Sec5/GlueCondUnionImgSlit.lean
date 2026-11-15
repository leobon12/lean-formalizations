/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgCf
import InteractingSLE.Spec.Sec7.Aux119Reflect

/-!
# G3 (ii), Proposition 4.9 direction: the sides of the flow slit in the image chart

Packet PROVE-GLUECOND8, item 2 (PROVE-GLUECOND6's "What remains" 2). At a real point `x` of the image chart on a side
of the image slit `Ψ(A)`, the inverse transition map `Θ = f_t ∘ Φ` (`imgTheta`, PROVE-GLUECOND4) tends to a real point
`x₁ ≠ 0` of the flow chart on a side of the flow slit, with `Θ′ → λ > 0`. Two global facts are needed that a local
argument does not give: **orientation** (`x₁` is on the same side of the flow tip as `x` is of the image tip) and the
**branch** of the derivative argument (`Im L_t ∘ Φ − Im L′_T ∘ F′_T − arg_Ψ ∘ Φ`, a continuous branch of `arg Θ′`,
tends to `0`, not to another multiple of `2π`). Both follow from one connectedness argument along a real interval that
contains a side of the image slit together with a piece of the physical real line next to its base:

* **`neg_of_forall_tendsto_real`**: if `Θ` has a nonzero real limit at every point of a preconnected `I ⊆ ℝ` and a
  negative one at some point of `I`, all its limits on `I` are negative (the limit function is continuous on `I`,
  `continuousOn_extendFrom`; intermediate values);
* **`tendsto_zero_of_forall_tendsto_two_pi_int`**: if a real function has a limit in `2πℤ` at every point of `I` and
  the limit `0` at some point, its limit is `0` on all of `I`;
* **`tendsto_imgChart_of_slit_left`**, **`tendsto_imgChart_of_slit_right`**: the boundary limit of the candidate at
  the slit sides from these two facts, the flow-side limit of the union mean and the flow word's and image word's
  heights `∓λ` next to their tips.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.GlueImg

/-! ### Two connectedness lemmas along the real line -/

section Connect

theorem nhdsWithin_H_neBot (x : ℝ) : (𝓝[H] (x : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
  show (0 : ℝ) ≤ (x : ℂ).im
  simp

theorem ofReal_mem_closure_H (x : ℝ) : (x : ℂ) ∈ closure H := by
  rw [closure_H]; show (0 : ℝ) ≤ (x : ℂ).im; simp

/-- The limit function along `ℍ` of a function with limits at every point of `I ⊆ ℝ` is continuous on `I`. -/
theorem continuousOn_extendFrom_ofReal {Y : Type*} [TopologicalSpace Y] [RegularSpace Y] {f : ℂ → Y} {I : Set ℝ}
    (hlim : ∀ x ∈ I, ∃ y, Tendsto f (𝓝[H] (x : ℂ)) (𝓝 y)) :
    ContinuousOn (fun x : ℝ => extendFrom H f (x : ℂ)) I := by
  have h : ContinuousOn (extendFrom H f) ((fun x : ℝ => (x : ℂ)) '' I) :=
    continuousOn_extendFrom (by rintro _ ⟨x, -, rfl⟩; exact ofReal_mem_closure_H x)
      (by rintro _ ⟨x, hx, rfl⟩; exact hlim x hx)
  exact h.comp Complex.continuous_ofReal.continuousOn (mapsTo_image _ _)

/-- **Constant sign of the boundary map along an interval.** If `Θ` has a nonzero real limit at every point of a
preconnected `I ⊆ ℝ`, and a negative limit at `x₀ ∈ I`, then its limit at every point of `I` is negative. -/
theorem neg_of_forall_tendsto_real {Θ : ℂ → ℂ} {I : Set ℝ} (hI : IsPreconnected I)
    (hlim : ∀ x ∈ I, ∃ p : ℝ, p ≠ 0 ∧ Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) {x₀ : ℝ} (hx₀ : x₀ ∈ I) {p₀ : ℝ}
    (hp₀ : p₀ < 0) (h₀ : Tendsto Θ (𝓝[H] (x₀ : ℂ)) (𝓝 (p₀ : ℂ))) {x : ℝ} (hx : x ∈ I) {p : ℝ}
    (hp : Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) : p < 0 := by
  set g : ℝ → ℝ := fun x => (extendFrom H Θ (x : ℂ)).re with hg
  have hval : ∀ x' ∈ I, ∀ q : ℝ, Tendsto Θ (𝓝[H] (x' : ℂ)) (𝓝 (q : ℂ)) → g x' = q := fun x' _ q hq => by
    simp only [hg, extendFrom_eq (ofReal_mem_closure_H x') hq, ofReal_re]
  have hgc : ContinuousOn g I :=
    Complex.continuous_re.comp_continuousOn (continuousOn_extendFrom_ofReal fun x hx =>
      let ⟨p, _, hp⟩ := hlim x hx; ⟨_, hp⟩)
  have hne : ∀ x' ∈ I, g x' ≠ 0 := fun x' hx' => by
    obtain ⟨q, hq0, hq⟩ := hlim x' hx'
    rw [hval x' hx' q hq]; exact hq0
  by_contra hle
  have hgx : 0 < g x := by
    rw [hval x hx p hp]
    exact lt_of_le_of_ne (not_lt.1 hle) fun h => (hne x hx) (by rw [hval x hx p hp, h])
  have hgx₀ : g x₀ < 0 := by rw [hval x₀ hx₀ p₀ h₀]; exact hp₀
  obtain ⟨x', hx', h0⟩ := hI.intermediate_value hx₀ hx hgc ⟨hgx₀.le, hgx.le⟩
  exact hne x' hx' h0

/-- **Constancy of an argument branch along an interval.** If a real function has a limit in `2πℤ` at every point of a
preconnected `I ⊆ ℝ`, and the limit `0` at `x₀ ∈ I`, then its limit is `0` at every point of `I`. -/
theorem tendsto_zero_of_forall_tendsto_two_pi_int {a : ℂ → ℝ} {I : Set ℝ} (hI : IsPreconnected I)
    (harg : ∀ x ∈ I, ∃ k : ℤ, Tendsto a (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k))) {x₀ : ℝ} (hx₀ : x₀ ∈ I)
    (h₀ : Tendsto a (𝓝[H] (x₀ : ℂ)) (𝓝 0)) {x : ℝ} (hx : x ∈ I) : Tendsto a (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set g : ℝ → ℝ := fun x => extendFrom H a (x : ℂ) with hg
  have hval : ∀ x' ∈ I, ∀ q : ℝ, Tendsto a (𝓝[H] (x' : ℂ)) (𝓝 q) → g x' = q := fun x' _ q hq =>
    extendFrom_eq (ofReal_mem_closure_H x') hq
  have hgc : ContinuousOn g I := continuousOn_extendFrom_ofReal fun x hx =>
    let ⟨k, hk⟩ := harg x hx; ⟨_, hk⟩
  have hint : ∀ x' ∈ I, ∃ k : ℤ, g x' = 2 * π * k := fun x' hx' => by
    obtain ⟨k, hk⟩ := harg x' hx'
    exact ⟨k, hval x' hx' _ hk⟩
  have hg₀ : g x₀ = 0 := hval x₀ hx₀ 0 h₀
  obtain ⟨k, hk⟩ := harg x hx
  have hgx : g x = 2 * π * k := hval x hx _ hk
  suffices hk0 : k = 0 by rw [hk0, Int.cast_zero, mul_zero] at hk; exact hk
  by_contra hk0
  have hπ := Real.pi_pos
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    obtain ⟨x', hx', hgx'⟩ := hI.intermediate_value hx hx₀ hgc
      (show -π ∈ Icc (g x) (g x₀) by rw [hgx, hg₀]; constructor <;> nlinarith)
    obtain ⟨m, hm⟩ := hint x' hx'
    rw [hgx'] at hm
    have : (2 * m + 1 : ℝ) * π = 0 := by linarith
    have h2 : (2 * m + 1 : ℝ) = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hπ.ne'
    have h3 : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hpos
    obtain ⟨x', hx', hgx'⟩ := hI.intermediate_value hx₀ hx hgc
      (show π ∈ Icc (g x₀) (g x) by rw [hgx, hg₀]; constructor <;> nlinarith)
    obtain ⟨m, hm⟩ := hint x' hx'
    rw [hgx'] at hm
    have : (2 * m - 1 : ℝ) * π = 0 := by linarith
    have h2 : (2 * m - 1 : ℝ) = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hπ.ne'
    have h3 : (2 * m - 1 : ℤ) = 0 := by exact_mod_cast h2
    omega

/-- The mirror of `neg_of_forall_tendsto_real`: a positive limit at one point of `I` makes all limits positive. -/
theorem pos_of_forall_tendsto_real {Θ : ℂ → ℂ} {I : Set ℝ} (hI : IsPreconnected I)
    (hlim : ∀ x ∈ I, ∃ p : ℝ, p ≠ 0 ∧ Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) {x₀ : ℝ} (hx₀ : x₀ ∈ I) {p₀ : ℝ}
    (hp₀ : 0 < p₀) (h₀ : Tendsto Θ (𝓝[H] (x₀ : ℂ)) (𝓝 (p₀ : ℂ))) {x : ℝ} (hx : x ∈ I) {p : ℝ}
    (hp : Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) : 0 < p := by
  have hneg : ∀ {x' : ℝ} {q : ℝ}, Tendsto Θ (𝓝[H] (x' : ℂ)) (𝓝 (q : ℂ)) →
      Tendsto (fun y => -Θ y) (𝓝[H] (x' : ℂ)) (𝓝 ((-q : ℝ) : ℂ)) := fun h => by
    rw [ofReal_neg]; exact h.neg
  have := neg_of_forall_tendsto_real (Θ := fun y => -Θ y) hI (fun x' hx' => by
      obtain ⟨q, hq0, hq⟩ := hlim x' hx'
      exact ⟨-q, neg_ne_zero.2 hq0, hneg hq⟩) hx₀ (neg_neg_of_pos hp₀) (hneg h₀) hx (hneg hp)
  linarith

end Connect

/-! ### The candidate at the sides of the image slit -/

section Slit

open MartChar.RealFlow Restart.RetAux79
open WangWu hiding ratPt exists_ratPt_dist_lt

variable {κ : ℝ} {nL nR mL mR : ℕ}

/-- A flowed force datum is not exceptional on the open slit image `(V̂^{0,L}, V̂^{0,R}) ∖ {0}`. -/
theorem notMem_forceJumpSet_flow_slit {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {y : ℝ} (hy0 : y ≠ 0)
    (hyL : -rightImg (fun s => -w s) 0 t - w t < y) (hyR : y < rightImg w 0 t - w t) :
    y ∉ forceJumpSet (fun i => -rightImg (fun s => -w s) (-xL i) t - w t) (fun j => rightImg w (xR j) t - w t) := by
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or]
  refine ⟨hy0, fun ⟨i, he⟩ => ?_, fun ⟨j, he⟩ => ?_⟩
  · have := rightImg_mono_index (w := fun s => -w s) (show Continuous fun s => -w s from hw.neg) ht
      (neg_nonneg.2 (hxL i)) (x := 0)
    linarith
  · have := rightImg_mono_index hw ht (hxR j) (x := 0)
    linarith

/-- **The candidate at a point of the left side of the image slit** (deterministic). On a preconnected `I ⊆ (−∞, 0)`
of image-chart real points, `Θ` has nonzero real limits and the branch `a` limits in `2πℤ`; at some `x₀ ∈ I` (a
point of the physical real line next to the base of the slit) the limit of `Θ` is negative and that of `a` is `0`.
At a point `x ∈ I` of the left side of the image slit (`W′`-chart: `chartAL W′ T < x < 0`) where the `Θ`-limit lies on
the flow slit (`chartAL Wα t < x₁ < chartAR Wα t`) and the union mean has the flow-side limit
`M ∘ Φ + c − (u_A ∘ Θ − χ L_A) → 0`, the candidate has the boundary limit `0`:
`M ∘ Φ + c − (u − χ L_B) → 0` (`a = L_A − L_B`; `u_A`, `u` the bounded harmonic extensions of the flowed flow word at
`t` and of the flowed image word at `T`). -/
theorem tendsto_imgChart_of_slit_left {Wα W' : ℝ → ℝ} (hWα : Continuous Wα) (hW' : Continuous W') {t T : ℝ}
    (ht : 0 ≤ t) (hT : 0 ≤ T) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
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
    {Θ Φ : ℂ → ℂ} (hΘH : ∀ y ∈ H, Θ y ∈ H) {M LA LB : ℂ → ℝ} {c χ : ℝ} {I : Set ℝ} (hI : IsPreconnected I)
    (hlim : ∀ x ∈ I, ∃ p : ℝ, p ≠ 0 ∧ Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ)))
    (harg : ∀ x ∈ I, ∃ k : ℤ, Tendsto (fun y => LA y - LB y) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) {p₀ : ℝ} (hp₀ : p₀ < 0) (hΘ₀ : Tendsto Θ (𝓝[H] (x₀ : ℂ)) (𝓝 (p₀ : ℂ)))
    (ha₀ : Tendsto (fun y => LA y - LB y) (𝓝[H] (x₀ : ℂ)) (𝓝 0))
    {x : ℝ} (hx : x ∈ I) (hxL0 : chartAL W' T < x) (hx0 : x < 0) {x₁ : ℝ}
    (hΘ : Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ))) (hx₁L : chartAL Wα t < x₁) (hx₁R : x₁ < chartAR Wα t)
    (hA : Tendsto (fun y => M (Φ y) + c - (uA (Θ y) - χ * LA y)) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    Tendsto (fun y => M (Φ y) + c - (u y - χ * LB y)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hx₁0 : x₁ < 0 := neg_of_forall_tendsto_real hI hlim hx₀ hp₀ hΘ₀ hx hΘ
  have ha := tendsto_zero_of_forall_tendsto_two_pi_int hI harg hx₀ ha₀ hx
  have hdA : forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -Wα s) (-xL i) t - Wα t)
      (fun j => rightImg Wα (xR j) t - Wα t) x₁ = -(π / Real.sqrt κ) :=
    forceBoundaryData_flow_slit_left ρL ρR hWα ht hxL hx₁0 hx₁L
  have hdI : forceBoundaryData κ ρL' ρR' (fun i => -rightImg (fun s => -W' s) (-xL' i) T - W' T)
      (fun j => rightImg W' (xR' j) T - W' T) x = -(π / Real.sqrt κ) :=
    forceBoundaryData_flow_slit_left ρL' ρR' hW' hT hxL' hx0 hxL0
  have hΘ' : Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝[H] (x₁ : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hΘ, eventually_nhdsWithin_of_forall hΘH⟩
  have h1 := (huA.2.2 x₁ (notMem_forceJumpSet_flow_slit hWα ht hxL hxR hx₁0.ne hx₁L hx₁R)).comp hΘ'
  have h2 := hu.2.2 x (notMem_forceJumpSet_flow_slit hW' hT hxL' hxR' hx0.ne hxL0
    (hx0.trans_le (by have := chartAR_nonneg hW' hT (W' := W'); unfold chartAR at this; linarith)))
  rw [hdA] at h1
  rw [hdI] at h2
  have h := (hA.add (h1.sub h2)).sub (ha.const_mul χ)
  rw [sub_self, add_zero, mul_zero, sub_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

/-- **The candidate at a point of the right side of the image slit** (the mirror of
`tendsto_imgChart_of_slit_left`; `I ⊆ (0, ∞)`, positive `Θ`-limit at `x₀`). -/
theorem tendsto_imgChart_of_slit_right {Wα W' : ℝ → ℝ} (hWα : Continuous Wα) (hW' : Continuous W') {t T : ℝ}
    (ht : 0 ≤ t) (hT : 0 ≤ T) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
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
    {Θ Φ : ℂ → ℂ} (hΘH : ∀ y ∈ H, Θ y ∈ H) {M LA LB : ℂ → ℝ} {c χ : ℝ} {I : Set ℝ} (hI : IsPreconnected I)
    (hlim : ∀ x ∈ I, ∃ p : ℝ, p ≠ 0 ∧ Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ)))
    (harg : ∀ x ∈ I, ∃ k : ℤ, Tendsto (fun y => LA y - LB y) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) {p₀ : ℝ} (hp₀ : 0 < p₀) (hΘ₀ : Tendsto Θ (𝓝[H] (x₀ : ℂ)) (𝓝 (p₀ : ℂ)))
    (ha₀ : Tendsto (fun y => LA y - LB y) (𝓝[H] (x₀ : ℂ)) (𝓝 0))
    {x : ℝ} (hx : x ∈ I) (hxR0 : x < chartAR W' T) (hx0 : 0 < x) {x₁ : ℝ}
    (hΘ : Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ))) (hx₁L : chartAL Wα t < x₁) (hx₁R : x₁ < chartAR Wα t)
    (hA : Tendsto (fun y => M (Φ y) + c - (uA (Θ y) - χ * LA y)) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    Tendsto (fun y => M (Φ y) + c - (u y - χ * LB y)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hx₁0 : 0 < x₁ := pos_of_forall_tendsto_real hI hlim hx₀ hp₀ hΘ₀ hx hΘ
  have ha := tendsto_zero_of_forall_tendsto_two_pi_int hI harg hx₀ ha₀ hx
  have hdA : forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -Wα s) (-xL i) t - Wα t)
      (fun j => rightImg Wα (xR j) t - Wα t) x₁ = Real.pi / Real.sqrt κ :=
    forceBoundaryData_flow_slit_right ρL ρR hWα ht hxR hx₁0.le hx₁R
  have hdI : forceBoundaryData κ ρL' ρR' (fun i => -rightImg (fun s => -W' s) (-xL' i) T - W' T)
      (fun j => rightImg W' (xR' j) T - W' T) x = Real.pi / Real.sqrt κ :=
    forceBoundaryData_flow_slit_right ρL' ρR' hW' hT hxR' hx0.le hxR0
  have hΘ' : Tendsto Θ (𝓝[H] (x : ℂ)) (𝓝[H] (x₁ : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hΘ, eventually_nhdsWithin_of_forall hΘH⟩
  have h1 := (huA.2.2 x₁ (notMem_forceJumpSet_flow_slit hWα ht hxL hxR hx₁0.ne' hx₁L hx₁R)).comp hΘ'
  have h2 := hu.2.2 x (notMem_forceJumpSet_flow_slit hW' hT hxL' hxR' hx0.ne'
    ((by have := chartAL_nonpos hW' hT (W' := W'); unfold chartAL at this; linarith) : _ < x) hxR0)
  rw [hdA] at h1
  rw [hdI] at h2
  have h := (hA.add (h1.sub h2)).sub (ha.const_mul χ)
  rw [sub_self, add_zero, mul_zero, sub_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

end Slit

/-! ### The branch of `arg Θ′` -/

section Branch

open WangWu hiding ratPt exists_ratPt_dist_lt

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **The derivative of the inverse transition map** `Θ = f_t ∘ Ψ⁻¹ ∘ F′_T` on `ℍ`:
`Θ′ = exp(L_t ∘ Φ − (L′_T ∘ F′_T + L_Ψ ∘ Φ))`, `Φ = Ψ⁻¹ ∘ F′_T` (the chain rule with the two inverse maps). -/
theorem exp_logDeriv_imgTheta (hWα : Continuous Wα) (ht : 0 ≤ t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {y : ℂ} (hy : y ∈ H) :
    exp (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y)) -
      (logDerivFwd W' T (fwdMapInv W' T y) + logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y)))) =
      deriv (imgTheta Wα t Wβ s W' T) y := by
  set ζ := fwdMapInv W' T y with hζdef
  set z := revChartInv Wβ s ζ with hzdef
  have hζ : ζ ∈ H := QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy
  have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
  have hzA : z ∈ H \ fwdHull Wα t := ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have hzG : z ∈ H \ negInv '' fwdHull Wβ s := ⟨hp.1, fun h => hp.2 (Or.inr h)⟩
  have hΨz : revChart Wβ s z = ζ := revChart_revChartInv hWβ hWβ0 hs hζ
  have hζK : ζ ∈ H \ fwdHull W' T := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' hW'0 hT hy
  -- the three derivatives as exponentials
  have e1 := (isDerivLog_fwdMap hWα ht).2 z hzA
  have e2 := (isDerivLog_fwdMap hW' hT).2 ζ hζK
  have e3 := (isDerivLog_revChart hWβ hs).2 z hzG
  -- `F′_T` is the local inverse of `f′_T`
  have hfT : HasDerivAt (fwdMap W' T) (deriv (fwdMap W' T) ζ) ζ :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hT _ hζK).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW' hT).mem_nhds hζK)).hasDerivAt
  have hF : HasDerivAt (fwdMapInv W' T) (deriv (fwdMap W' T) ζ)⁻¹ y := by
    refine HasDerivAt.of_local_left_inverse ?_ hfT (by rw [← e2]; exact exp_ne_zero _) ?_
    · exact ((QuantumZipper.RS.differentiableOn_fwdMapInv hW' hW'0 hT).differentiableAt
        (QuantumZipper.isOpen_H.mem_nhds hy)).continuousAt
    · filter_upwards [QuantumZipper.isOpen_H.mem_nhds hy] with y' hy'
      exact QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT hy'
  -- `Ψ⁻¹` is the local inverse of `Ψ`
  have hΨ : HasDerivAt (revChart Wβ s) (deriv (revChart Wβ s) z) z :=
    (differentiableAt_revChart hWβ hs hzG).hasDerivAt
  have hΨi : HasDerivAt (revChartInv Wβ s) (deriv (revChart Wβ s) z)⁻¹ ζ := by
    refine HasDerivAt.of_local_left_inverse ?_ hΨ (by rw [← e3]; exact exp_ne_zero _) ?_
    · exact (continuousOn_revChartInv hWβ hWβ0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hζ)
    · filter_upwards [QuantumZipper.isOpen_H.mem_nhds hζ] with ζ' hζ'
      exact revChart_revChartInv hWβ hWβ0 hs hζ'
  have hft : HasDerivAt (fwdMap Wα t) (deriv (fwdMap Wα t) z) z :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hWα ht _ hzA).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWα ht).mem_nhds hzA)).hasDerivAt
  have hΦd : HasDerivAt (revChartInv Wβ s ∘ fwdMapInv W' T)
      ((deriv (revChart Wβ s) z)⁻¹ * (deriv (fwdMap W' T) ζ)⁻¹) y :=
    HasDerivAt.comp (h₂ := revChartInv Wβ s) (h := fwdMapInv W' T) y hΨi hF
  have hΘ' : HasDerivAt (fwdMap Wα t ∘ (revChartInv Wβ s ∘ fwdMapInv W' T))
      (deriv (fwdMap Wα t) z * ((deriv (revChart Wβ s) z)⁻¹ * (deriv (fwdMap W' T) ζ)⁻¹)) y :=
    HasDerivAt.comp (h₂ := fwdMap Wα t) (h := revChartInv Wβ s ∘ fwdMapInv W' T) y hft hΦd
  have hΘ : HasDerivAt (imgTheta Wα t Wβ s W' T)
      (deriv (fwdMap Wα t) z * ((deriv (revChart Wβ s) z)⁻¹ * (deriv (fwdMap W' T) ζ)⁻¹)) y := hΘ'
  rw [hΘ.deriv, ← e1, ← e2, ← e3, exp_sub, exp_add]
  field_simp

/-- **The branch of `arg Θ′` at a point where `Θ′ → λ > 0`**: `Im L_t ∘ Φ − (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)` tends to an
integer multiple of `2π`. -/
theorem exists_int_tendsto_argTheta (hWα : Continuous Wα) (ht : 0 ≤ t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x : ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hd : Tendsto (deriv (imgTheta Wα t Wβ s W' T)) (𝓝[H] (x : ℂ)) (𝓝 (lam : ℂ))) :
    ∃ k : ℤ, Tendsto (fun y => (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im -
      ((logDerivFwd W' T (fwdMapInv W' T y)).im + (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))
      (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)) := by
  set Θ := imgTheta Wα t Wβ s W' T with hΘdef
  -- a half-ball on which `Θ′` stays in the right half-plane
  have hev : ∀ᶠ y in 𝓝[H] (x : ℂ), 0 < (deriv Θ y).re :=
    hd.eventually ((isOpen_lt continuous_const continuous_re).mem_nhds (by simpa using hlam))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set S := ball (x : ℂ) δ ∩ H with hSdef
  have hSH : S ⊆ H := inter_subset_right
  have hSc : IsPreconnected S := ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hΘd : DifferentiableOn ℂ Θ H := fun y hy =>
    (differentiableAt_imgTheta hWα ht hWβ hWβ0 hs hW' hW'0 hT hK' hy).differentiableWithinAt
  have hG : ContinuousOn (deriv Θ) S :=
    ((hΘd.deriv QuantumZipper.isOpen_H).continuousOn).mono hSH
  have hF : ContinuousOn (fwdMapInv W' T) H :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hW' hW'0 hT).continuousOn
  have hΦ : ContinuousOn (fun y => revChartInv Wβ s (fwdMapInv W' T y)) H :=
    (continuousOn_revChartInv hWβ hWβ0 hs).comp hF fun y hy => QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy
  have h₂ : ContinuousOn (fun y => logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))) S := by
    refine ContinuousOn.comp (g := logDerivFwd Wα t)
      (fun z hz => (continuousAt_logDerivFwd hWα ht hz).continuousWithinAt) (hΦ.mono hSH) fun y hy => ?_
    have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' (hSH hy)
    exact ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  have h₁ : ContinuousOn (fun y => logDerivFwd W' T (fwdMapInv W' T y) +
      logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))) S := by
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.comp (g := logDerivFwd W' T)
        (fun z hz => (continuousAt_logDerivFwd hW' hT hz).continuousWithinAt) (hF.mono hSH) fun y hy => ?_
      exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' hW'0 hT (hSH hy)
    · refine ContinuousOn.comp (g := logDerivPsi Wβ s) (isDerivLog_revChart hWβ hs).1.continuousOn (hΦ.mono hSH)
        fun y hy => ?_
      have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' (hSH hy)
      exact ⟨hp.1, fun h => hp.2 (Or.inr h)⟩
  have hslit : ∀ y ∈ S, deriv Θ y ∈ slitPlane := fun y hy => Or.inl (hball ⟨hy.1, hy.2⟩)
  have hexp : ∀ y ∈ S, exp (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y)) -
      (logDerivFwd W' T (fwdMapInv W' T y) + logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y)))) =
      deriv Θ y := fun y hy => exp_logDeriv_imgTheta hWα ht hWβ hWβ0 hs hW' hW'0 hT hK' (hSH hy)
  have hSnhds : 𝓝[S] (x : ℂ) = 𝓝[H] (x : ℂ) := by
    rw [hSdef, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hδ))]
  obtain ⟨n, hn⟩ := Sec7.Aux119.exists_int_tendsto_im_sub hSc h₁ h₂ hG hslit hexp
    (F := 𝓝[S] (x : ℂ)) (inf_le_right : 𝓝[S] (x : ℂ) ≤ 𝓟 S) hlam (by rw [hSnhds]; exact hd)
  refine ⟨n, ?_⟩
  rw [hSnhds] at hn
  refine hn.congr fun y => ?_
  simp only [sub_im, add_im]

/-- **The two per-point inputs of the slit theorems at a point with a nonzero real cluster value**: if `Θ` has a
real cluster value `x₁ ≠ 0` along one ultrafilter at the real image-chart point `x`, then `Θ` has the nonzero real limit
`x₁` at `x` and the branch `Im L_t ∘ Φ − (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)` tends to a multiple of `2π` there
(PROVE-GLUECOND4's `tendsto_imgTheta_of_ultrafilter` and `exists_int_tendsto_argTheta`). -/
theorem imgTheta_limits_of_ultrafilter {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hGc : IsClosed (negInv '' fwdHull Wβ s)) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x x₁ : ℝ} (hx₁ : x₁ ≠ 0) {U : Ultrafilter ℂ}
    (hU : (U : Filter ℂ) ≤ 𝓝[H] (x : ℂ)) (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 (x₁ : ℂ))) :
    (∃ p : ℝ, p ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) ∧
      ∃ k : ℤ, Tendsto (fun y => (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im -
        ((logDerivFwd W' T (fwdMapInv W' T y)).im + (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)) := by
  obtain ⟨hlim, lam, hlam, hd⟩ := tendsto_imgTheta_of_ultrafilter hα hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT hGc
    hdisj hdis hK' hx₁ hU hΘ
  exact ⟨⟨x₁, hx₁, hlim⟩, exists_int_tendsto_argTheta hWα ht hWβ hWβ0 hs hW' hW'0 hT hK' hlam hd⟩

end Branch

end InteractingSLE.Sec5.GlueImg