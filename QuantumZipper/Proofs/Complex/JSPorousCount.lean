import QuantumZipper.Proofs.Complex.JSPorousHit
import QuantumZipper.Proofs.Complex.JSPorousRay
import QuantumZipper.Proofs.Complex.JSHolderLayer
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Interval.Finset.Nat

/-!
# EXT-JS node D4, the counting step

Blueprint `blueprint/EXT_JS_BLUEPRINT.md` §2(D) step 3. This module proves the scale-counting
lemma `JS.scale_count_le`, the technical core of node D4: holes at most scales for the image of a
Hölder chart. The public theorem `JS.meanPorous_of_holderChart` is in `JSPorous.lean`, which
imports this file.

* `JS.qhDist`, `JS.qhIntegrand`: the quasihyperbolic denominator and integrand along a vertical
  ray (node D3);
* `JS.scale_count_le`: at least half of the scales `j ∈ [j₀,n]` around `p = F x` carry a hole,
  given the quasihyperbolic length bound of node D3 and the Hölder bottom estimate.

Everything is an **own elementary proof** following Jones–Smirnov, Ark. Mat. 38 (2000) §3 and the
blueprint sketch; see the docstring of `JSPorous.lean` for the full outline.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology Real
open scoped Classical

namespace QuantumZipper
namespace JS

/-- The quasihyperbolic denominator along the vertical ray: the distance from `F (x + t i)` to the
complement of `F '' ℍ`. -/
noncomputable def qhDist (F : ℂ → ℂ) (x : ℝ) (t : ℝ) : ℝ :=
  Metric.infDist (F ((x : ℂ) + (t : ℂ) * Complex.I)) (F '' H)ᶜ

/-- The quasihyperbolic integrand `‖F'‖ / d` along the vertical ray `t ↦ x + t i`. -/
noncomputable def qhIntegrand (F : ℂ → ℂ) (x : ℝ) (t : ℝ) : ℝ :=
  ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ / qhDist F x t

/-- **D4, the scale-counting step.** Fix `p = F x` with `x ∈ [-3R/2, 3R/2]` and `y > 0` with
`‖F (x + y i) - F x‖ ≤ 2^{-(n+1)}`, `y ≤ min 1 (4R)`. If the total quasihyperbolic length of the
ray up to height `1` is at most `M (n - j₀)/4`, then at least `(n - j₀)/2` of the scales
`j ∈ [j₀,n]` carry a hole of radius `(1/M) 2^{-j}` inside `ball (F x) (3 · 2^{-j})`.

The constants are those of the blueprint: `c = 1/M`, `C = 3`, half of the scales. -/
theorem scale_count_le {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hcont : ContinuousOn F (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R)))
    (hholo : DifferentiableOn ℂ F H) (hinj : InjOn F H)
    (hnotmem : ∀ x : ℝ, x ∈ Icc (-2 * R) (2 * R) → F (x : ℂ) ∉ F '' H)
    {j₀ : ℕ} {d₀ : ℝ} (hj₀ : 2 * (2 : ℝ)⁻¹ ^ j₀ ≤ d₀)
    (hd₀le : ∀ x ∈ Icc (-(3 / 2) * R) ((3 / 2) * R),
      d₀ ≤ ‖F ((x : ℂ) + ((min 1 (4 * R) : ℝ) : ℂ) * Complex.I) - F (x : ℂ)‖)
    {n : ℕ} {x y : ℝ} (hx : x ∈ Icc (-(3 / 2) * R) ((3 / 2) * R)) (hjn : j₀ ≤ n)
    (hy0 : 0 < y) (hy1 : y ≤ 1) (hyh : y ≤ min 1 (4 * R))
    (hyH : ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F (x : ℂ)‖ ≤ (2 : ℝ)⁻¹ ^ (n + 1))
    {M : ℝ} (hM1 : 1 ≤ M)
    (hM : (CA.Koebe.koebeCovConst)⁻¹ * Real.log (1 / y) ≤ M * ((n : ℝ) - j₀) / 4) :
    (n - j₀) ≤ 2 * ((Finset.Icc j₀ n).filter (fun j => ∃ q : ℂ,
      ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
        ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \
          (F '' ((fun t : ℝ => (t : ℂ)) '' Icc (-(3 / 2) * R) ((3 / 2) * R))))).card := by
  classical
  set h : ℝ := min 1 (4 * R) with hhdef
  have hh0 : 0 < h := by rw [hhdef]; exact lt_min one_pos (by linarith)
  have hh1 : h ≤ 1 := by rw [hhdef]; exact min_le_left _ _
  have hh4R : h ≤ 4 * R := by rw [hhdef]; exact min_le_right _ _
  have hx2R : x ∈ Icc (-2 * R) (2 * R) := ⟨by linarith [hx.1, hR], by linarith [hx.2, hR]⟩
  set E : Set ℂ := F '' ((fun t : ℝ => (t : ℂ)) '' Icc (-(3 / 2) * R) ((3 / 2) * R)) with hEdef
  have hEsub : E ⊆ (F '' H)ᶜ := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hz
    exact hnotmem t ⟨by linarith [ht.1, hR], by linarith [ht.2, hR]⟩
  have hne : ((F '' H)ᶜ).Nonempty := ⟨F (x : ℂ), hnotmem x hx2R⟩
  -- coordinates of the ray points
  have hre : ∀ t : ℝ, ((x : ℂ) + (t : ℂ) * Complex.I).re = x := fun t => by simp
  have him : ∀ t : ℝ, ((x : ℂ) + (t : ℂ) * Complex.I).im = t := fun t => by simp
  have hbox : ∀ t : ℝ, y ≤ t → t ≤ h →
      ((x : ℂ) + (t : ℂ) * Complex.I) ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
    intro t ht1 ht2
    rw [Complex.mem_reProdIm, hre t, him t]
    exact ⟨hx2R, ⟨le_trans hy0.le ht1, le_trans ht2 hh4R⟩⟩
  -- continuity of the derivative along the ray
  have hderivcont : ContinuousOn (deriv F) H :=
    (hholo.analyticOnNhd isOpen_H).contDiffOn_of_completeSpace
      |>.continuousOn_deriv_of_isOpen isOpen_H le_top
  have hray : ContinuousOn (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (Icc y h) :=
    (((Complex.continuous_ofReal.comp continuous_id).mul continuous_const).const_add
      (x : ℂ)).continuousOn
  have hnumcont : ContinuousOn (fun t : ℝ => deriv F ((x : ℂ) + (t : ℂ) * Complex.I)) (Icc y h) :=
    hderivcont.comp hray fun t ht => by
      show 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im
      rw [him t]
      exact lt_of_lt_of_le hy0 ht.1
  have hnumcont_sub : ∀ {a b : ℝ}, y ≤ a → b ≤ h →
      ContinuousOn (fun t : ℝ => deriv F ((x : ℂ) + (t : ℂ) * Complex.I)) (Icc a b) :=
    fun ha hb => hnumcont.mono (Icc_subset_Icc ha hb)
  -- the crossing function
  set φ : ℝ → ℝ := fun t => ‖F ((x : ℂ) + (t : ℂ) * Complex.I) - F (x : ℂ)‖ with hφdef
  have hφcont_h : ContinuousOn φ (Icc y h) := by
    rw [hφdef]
    exact ((hcont.comp hray (fun t ht => hbox t ht.1 ht.2)).sub continuousOn_const).norm
  have hφcont : ∀ {a b : ℝ}, y ≤ a → b ≤ h → ContinuousOn φ (Icc a b) :=
    fun ha hb => hφcont_h.mono (Icc_subset_Icc ha hb)
  have hφy : φ y ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by rw [hφdef]; exact hyH
  have hφh : d₀ ≤ φ h := by rw [hφdef, hhdef]; exact hd₀le x hx
  -- the levels `2 * (2⁻¹)^j` are crossed, and `φ y` stays strictly below them
  have hlevel : ∀ j ∈ Finset.Icc j₀ n, (2 : ℝ)⁻¹ ^ (n + 1) < 2 * (2 : ℝ)⁻¹ ^ j := by
    intro j hj
    have hjle : j ≤ n := (Finset.mem_Icc.mp hj).2
    have h1 : (2 : ℝ)⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (2 : ℝ)⁻¹ ^ (j + 1) < 2 * (2 : ℝ)⁻¹ ^ j := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) j]
    linarith
  have hlevel' : ∀ j ∈ Finset.Icc j₀ n, (2 : ℝ)⁻¹ ^ (n + 1) < (2 : ℝ)⁻¹ ^ j := by
    intro j hj
    have hjle : j ≤ n := (Finset.mem_Icc.mp hj).2
    have h1 : (2 : ℝ)⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (2 : ℝ)⁻¹ ^ (j + 1) < (2 : ℝ)⁻¹ ^ j := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) j]
    linarith
  have hcross : ∀ j ∈ Finset.Icc j₀ n, ∃ t ∈ Icc y h, 2 * (2 : ℝ)⁻¹ ^ j ≤ φ t := by
    intro j hj
    have hj0 : j₀ ≤ j := (Finset.mem_Icc.mp hj).1
    have h2j : 2 * (2 : ℝ)⁻¹ ^ j ≤ d₀ :=
      le_trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj0) (by norm_num)) hj₀
    exact ⟨h, ⟨hyh, le_rfl⟩, le_trans h2j hφh⟩
  -- first hitting times `b j` of the levels `2 * 2^{-j}`
  have hfirst : ∀ j ∈ Finset.Icc j₀ n, ∃ σ : ℝ, σ ∈ Icc y h ∧ φ σ = 2 * (2 : ℝ)⁻¹ ^ j ∧
      (∀ s ∈ Icc y h, s < σ → φ s < 2 * (2 : ℝ)⁻¹ ^ j) ∧
      (∀ s ∈ Icc y h, 2 * (2 : ℝ)⁻¹ ^ j ≤ φ s → σ ≤ s) := by
    intro j hj
    have hyL : φ y < 2 * (2 : ℝ)⁻¹ ^ j := lt_of_le_of_lt hφy (hlevel j hj)
    obtain ⟨t, ht, hle⟩ := hcross j hj
    exact exists_firstHit hyh hφcont_h hyL ⟨t, ht, hle⟩
  let bb : ℕ → ℝ := fun j =>
    if hj : j ∈ Finset.Icc j₀ n then Classical.choose (hfirst j hj) else y
  have hbb : ∀ (j : ℕ) (hj : j ∈ Finset.Icc j₀ n),
      bb j ∈ Icc y h ∧ φ (bb j) = 2 * (2 : ℝ)⁻¹ ^ j ∧
      (∀ s ∈ Icc y h, s < bb j → φ s < 2 * (2 : ℝ)⁻¹ ^ j) ∧
      (∀ s ∈ Icc y h, 2 * (2 : ℝ)⁻¹ ^ j ≤ φ s → bb j ≤ s) := by
    intro j hj
    have h1 : bb j = Classical.choose (hfirst j hj) := dite_eq_left hj
    rw [h1]
    exact Classical.choose_spec (hfirst j hj)
  have hbb_mem : ∀ j ∈ Finset.Icc j₀ n, bb j ∈ Icc y h := fun j hj => (hbb j hj).1
  have hbb_val : ∀ j ∈ Finset.Icc j₀ n, φ (bb j) = 2 * (2 : ℝ)⁻¹ ^ j := fun j hj => (hbb j hj).2.1
  have hbb_lt : ∀ j ∈ Finset.Icc j₀ n, ∀ s ∈ Icc y h, s < bb j → φ s < 2 * (2 : ℝ)⁻¹ ^ j :=
    fun j hj => (hbb j hj).2.2.1
  have hbb_first : ∀ j ∈ Finset.Icc j₀ n, ∀ s ∈ Icc y h, 2 * (2 : ℝ)⁻¹ ^ j ≤ φ s → bb j ≤ s :=
    fun j hj => (hbb j hj).2.2.2
  -- last hitting times `a j` of the levels `2^{-j}` below `b j`
  have hlast : ∀ j ∈ Finset.Icc j₀ n, ∃ τ : ℝ, τ ∈ Icc y (bb j) ∧ φ τ = (2 : ℝ)⁻¹ ^ j ∧
      ∀ s ∈ Icc y (bb j), τ < s → (2 : ℝ)⁻¹ ^ j < φ s := by
    intro j hj
    have hyle : y ≤ bb j := (hbb_mem j hj).1
    refine exists_lastHit hyle (hφcont le_rfl (hbb_mem j hj).2) ?_ ?_
    · have := hlevel' j hj
      linarith [hφy]
    · rw [hbb_val j hj]
      have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j := pow_pos (by norm_num) j
      linarith
  let aa : ℕ → ℝ := fun j =>
    if hj : j ∈ Finset.Icc j₀ n then Classical.choose (hlast j hj) else y
  have haa : ∀ (j : ℕ) (hj : j ∈ Finset.Icc j₀ n),
      aa j ∈ Icc y (bb j) ∧ φ (aa j) = (2 : ℝ)⁻¹ ^ j ∧
      (∀ s ∈ Icc y (bb j), aa j < s → (2 : ℝ)⁻¹ ^ j < φ s) := by
    intro j hj
    have h1 : aa j = Classical.choose (hlast j hj) := dite_eq_left hj
    rw [h1]
    exact Classical.choose_spec (hlast j hj)
  have haa_mem : ∀ j ∈ Finset.Icc j₀ n, aa j ∈ Icc y (bb j) := fun j hj => (haa j hj).1
  have haa_val : ∀ j ∈ Finset.Icc j₀ n, φ (aa j) = (2 : ℝ)⁻¹ ^ j := fun j hj => (haa j hj).2.1
  have haa_gt : ∀ j ∈ Finset.Icc j₀ n, ∀ s ∈ Icc y (bb j), aa j < s → (2 : ℝ)⁻¹ ^ j < φ s :=
    fun j hj => (haa j hj).2.2
  have haa_le : ∀ j ∈ Finset.Icc j₀ n, aa j ≤ bb j := fun j hj => (haa_mem j hj).2
  have haa_y : ∀ j ∈ Finset.Icc j₀ n, y ≤ aa j := fun j hj => (haa_mem j hj).1
  have haa_h : ∀ j ∈ Finset.Icc j₀ n, aa j ∈ Icc y h :=
    fun j hj => ⟨(haa_mem j hj).1, le_trans (haa_mem j hj).2 (hbb_mem j hj).2⟩
  have haa_lt_bb : ∀ j ∈ Finset.Icc j₀ n, aa j < bb j := by
    intro j hj
    have hne' : aa j ≠ bb j := by
      intro heq
      have h1 := haa_val j hj
      have h2 := hbb_val j hj
      rw [heq] at h1
      have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j := pow_pos (by norm_num) j
      linarith
    exact lt_of_le_of_ne (haa_le j hj) hne'
  -- the arcs are ordered: `b j' ≤ a j` for `j < j'`
  have horder : ∀ j ∈ Finset.Icc j₀ n, ∀ j' ∈ Finset.Icc j₀ n, j < j' → bb j' ≤ aa j := by
    intro j hj j' hj' hlt
    have hle : 2 * (2 : ℝ)⁻¹ ^ j' ≤ φ (aa j) := by
      rw [haa_val j hj]
      have h1 : (2 : ℝ)⁻¹ ^ j' ≤ (2 : ℝ)⁻¹ ^ (j + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      rw [pow_succ] at h1
      nlinarith [h1, pow_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) j]
    exact hbb_first j' hj' (aa j) (haa_h j hj) hle
  -- positivity of the quasihyperbolic denominator along the ray
  have hDpos : ∀ t : ℝ, 0 < t → 0 < qhDist F x t := by
    intro t ht0
    refine infDist_compl_image_pos hholo hinj hne ?_
    show 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im
    rw [him t]
    exact ht0
  have hfcont : ContinuousOn (qhIntegrand F x) (Icc y 1) := by
    rw [show qhIntegrand F x = (fun t : ℝ => ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ /
      Metric.infDist (F ((x : ℂ) + (t : ℂ) * Complex.I)) (F '' H)ᶜ) from rfl]
    exact continuousOn_qhIntegrand hholo hinj hne x hy0
  have hfcont_sub : ∀ {a b : ℝ}, a ≤ b → y ≤ a → b ≤ 1 → ContinuousOn (qhIntegrand F x) (Icc a b) :=
    fun hab ha hb => hfcont.mono (Icc_subset_Icc ha hb)
  have hfcont_sub' : ∀ {a b : ℝ}, a ≤ b → y ≤ a → b ≤ 1 → ContinuousOn (qhIntegrand F x) (uIcc a b) :=
    fun hab ha hb => by
      rw [uIcc_of_le hab]
      exact hfcont_sub hab ha hb
  -- the bad scales
  set badset : Finset ℕ := (Finset.Icc j₀ n).filter (fun j =>
    ∀ t ∈ Icc (aa j) (bb j), qhDist F x t < (1 / M) * (2 : ℝ)⁻¹ ^ j) with hbadset
  have hmem_bad : ∀ j : ℕ, j ∈ badset ↔ (j ∈ Finset.Icc j₀ n ∧
      ∀ t ∈ Icc (aa j) (bb j), qhDist F x t < (1 / M) * (2 : ℝ)⁻¹ ^ j) := by
    intro j
    rw [hbadset, Finset.mem_filter]
  -- a bad scale contributes at least `M` to the quasihyperbolic length of the ray
  have hbadint : ∀ j ∈ badset, M ≤ ∫ t in (aa j)..(bb j), qhIntegrand F x t := by
    intro j hj
    obtain ⟨hjIcc, hjbad⟩ := (hmem_bad j).mp hj
    have hlt : y ≤ aa j := haa_y j hjIcc
    have hle : aa j ≤ bb j := haa_le j hjIcc
    have hle1 : bb j ≤ 1 := le_trans (hbb_mem j hjIcc).2 hh1
    have hpoint : ∀ t ∈ Icc (aa j) (bb j),
        M * (2 : ℝ) ^ j * ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ qhIntegrand F x t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hy0 (le_trans hlt ht.1)
      have hth : t ≤ h := le_trans ht.2 (hbb_mem j hjIcc).2
      have hDt : 0 < qhDist F x t := hDpos t ht0
      have hbad' : qhDist F x t < (1 / M) * (2 : ℝ)⁻¹ ^ j := hjbad t ht
      have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
      have hkey : M * (2 : ℝ) ^ j * qhDist F x t < 1 := by
        have h1 : qhDist F x t * M < (2 : ℝ)⁻¹ ^ j := by
          have h := hbad'
          rw [one_div] at h
          have h2 : ((M)⁻¹ * (2 : ℝ)⁻¹ ^ j) * M = (2 : ℝ)⁻¹ ^ j := by
            rw [mul_assoc, mul_comm ((2 : ℝ)⁻¹ ^ j) M, ← mul_assoc,
              inv_mul_cancel₀ hMpos.ne', one_mul]
          have h3 := mul_lt_mul_of_pos_right h hMpos
          linarith [h3, h2]
        have h2 : (2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j = 1 := by rw [← mul_pow]; norm_num
        calc M * (2 : ℝ) ^ j * qhDist F x t = qhDist F x t * M * (2 : ℝ) ^ j := by ring
          _ < (2 : ℝ)⁻¹ ^ j * (2 : ℝ) ^ j :=
              mul_lt_mul_of_pos_right h1 (pow_pos (by norm_num) j)
          _ = 1 := by rw [mul_comm]; exact h2
      rw [show qhIntegrand F x t = ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ / qhDist F x t
        from rfl, le_div_iff₀ hDt]
      nlinarith [hkey, norm_nonneg (deriv F ((x : ℂ) + (t : ℂ) * Complex.I))]
    -- the FTC chord bound gives `∫ ‖F'‖ ≥ 2^{-j}` on the arc
    have hchord : (2 : ℝ)⁻¹ ^ j ≤ ∫ t in (aa j)..(bb j),
        ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ :=
      le_trans (by
        have h1 : ‖F ((x : ℂ) + (bb j : ℂ) * Complex.I) - F (x : ℂ)‖ -
            ‖F ((x : ℂ) + (aa j : ℂ) * Complex.I) - F (x : ℂ)‖ ≤
            ‖F ((x : ℂ) + (bb j : ℂ) * Complex.I) - F ((x : ℂ) + (aa j : ℂ) * Complex.I)‖ := by
          rw [show F ((x : ℂ) + (bb j : ℂ) * Complex.I) - F ((x : ℂ) + (aa j : ℂ) * Complex.I) =
            (F ((x : ℂ) + (bb j : ℂ) * Complex.I) - F (x : ℂ)) -
              (F ((x : ℂ) + (aa j : ℂ) * Complex.I) - F (x : ℂ)) from by ring]
          exact norm_sub_norm_le _ _
        rw [show ‖F ((x : ℂ) + (bb j : ℂ) * Complex.I) - F (x : ℂ)‖ = φ (bb j) from by
              rw [hφdef],
            show ‖F ((x : ℂ) + (aa j : ℂ) * Complex.I) - F (x : ℂ)‖ = φ (aa j) from by
              rw [hφdef]] at h1
        rw [hbb_val j hjIcc, haa_val j hjIcc] at h1
        linarith [h1])
        (norm_image_sub_le_integral_norm_deriv_ray hholo (lt_of_lt_of_le hy0 hlt) hle)
    have hmono : ∫ t in (aa j)..(bb j),
          M * (2 : ℝ) ^ j * ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        ∫ t in (aa j)..(bb j), qhIntegrand F x t := by
      refine intervalIntegral.integral_mono_on (le_of_lt (haa_lt_bb j hjIcc)) ?_ ?_ hpoint
      · have hc : ContinuousOn (fun t : ℝ => M * (2 : ℝ) ^ j *
            ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖) (uIcc (aa j) (bb j)) := by
          rw [uIcc_of_le hle]
          exact continuousOn_const.mul
            (hnumcont_sub hlt (hbb_mem j hjIcc).2).norm
        exact hc.intervalIntegrable
      · exact (hfcont_sub' hle hlt hle1).intervalIntegrable
    have hconst : ∫ t in (aa j)..(bb j),
        M * (2 : ℝ) ^ j * ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ =
        M * (2 : ℝ) ^ j * ∫ t in (aa j)..(bb j),
          ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ :=
      intervalIntegral.integral_const_mul (M * (2 : ℝ) ^ j)
        (fun t : ℝ => ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖)
    have hMj : 0 < M * (2 : ℝ) ^ j :=
      mul_pos (lt_of_lt_of_le one_pos hM1) (pow_pos (by norm_num) j)
    calc M = M * (2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, mul_one]
      _ ≤ M * (2 : ℝ) ^ j * ∫ t in (aa j)..(bb j),
            ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_left hchord hMj.le
      _ = ∫ t in (aa j)..(bb j),
            M * (2 : ℝ) ^ j * ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ := hconst.symm
      _ ≤ ∫ t in (aa j)..(bb j), qhIntegrand F x t := hmono
  -- summing the bad contributions: disjoint arcs, nonnegative integrand
  have hint_bad : ∀ j ∈ badset, IntegrableOn (qhIntegrand F x) (Ioc (aa j) (bb j)) volume := by
    intro j hj
    have hjIcc := (hmem_bad j).mp hj |>.1
    exact (hfcont_sub (haa_le j hjIcc) (haa_y j hjIcc)
      (le_trans (hbb_mem j hjIcc).2 hh1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hdisj : Set.Pairwise (↑badset)
      (fun j j' => Disjoint (Ioc (aa j) (bb j)) (Ioc (aa j') (bb j'))) := by
    intro j hj j' hj' hne
    have hjIcc := (hmem_bad j).mp hj |>.1
    have hj'Icc := (hmem_bad j').mp hj' |>.1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine disjoint_left.mpr fun v hv hv' => ?_
      have h1 : v ≤ bb j' := hv'.2
      have h2 := horder j hjIcc j' hj'Icc hlt
      have h3 : aa j < v := hv.1
      linarith
    · refine disjoint_left.mpr fun v hv hv' => ?_
      have h1 : v ≤ bb j := hv.2
      have h2 := horder j' hj'Icc j hjIcc hgt
      have h3 : aa j' < v := hv'.1
      linarith
  have hfnonneg : ∀ t ∈ Ioc y 1, 0 ≤ qhIntegrand F x t := by
    intro t ht
    rw [show qhIntegrand F x t = ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ / qhDist F x t
      from rfl]
    exact div_nonneg (norm_nonneg _) (hDpos t (lt_trans hy0 ht.1)).le
  have hsum_le : (badset.card : ℝ) * M ≤ ∫ t in y..1, qhIntegrand F x t := by
    have h1 : ∑ j ∈ badset, M ≤ ∑ j ∈ badset, ∫ t in (aa j)..(bb j), qhIntegrand F x t :=
      Finset.sum_le_sum fun j hj => hbadint j hj
    have h2 : ∑ j ∈ badset, M = (badset.card : ℝ) * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : ∑ j ∈ badset, ∫ t in (aa j)..(bb j), qhIntegrand F x t =
        ∫ t in (⋃ j ∈ badset, Ioc (aa j) (bb j)), qhIntegrand F x t := by
      have hh : ∑ j ∈ badset, ∫ t in (aa j)..(bb j), qhIntegrand F x t =
          ∑ j ∈ badset, ∫ t in Ioc (aa j) (bb j), qhIntegrand F x t :=
        Finset.sum_congr rfl fun j hj =>
          intervalIntegral.integral_of_le (le_of_lt (haa_lt_bb j ((hmem_bad j).mp hj).1))
      rw [hh, ← integral_biUnion_finset badset (fun j _ => measurableSet_Ioc) hdisj hint_bad]
    have h4 : ∫ t in (⋃ j ∈ badset, Ioc (aa j) (bb j)), qhIntegrand F x t ≤
        ∫ t in Ioc y 1, qhIntegrand F x t := by
      refine setIntegral_mono_set ((hfcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self) ?_ ?_
      · show ∀ᵐ t ∂(volume.restrict (Ioc y 1)), 0 ≤ qhIntegrand F x t
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with t ht
        exact hfnonneg t ht
      · filter_upwards with t ht
        simp only [Set.mem_iUnion] at ht
        obtain ⟨j, hj, htij⟩ := ht
        exact ⟨lt_of_le_of_lt (haa_y j ((hmem_bad j).mp hj).1) htij.1,
          le_trans htij.2 (le_trans (hbb_mem j ((hmem_bad j).mp hj).1).2 hh1)⟩
    have h5 : ∫ t in Ioc y 1, qhIntegrand F x t = ∫ t in y..1, qhIntegrand F x t :=
      (intervalIntegral.integral_of_le hy1).symm
    calc (badset.card : ℝ) * M = ∑ j ∈ badset, M := h2.symm
      _ ≤ ∫ t in (⋃ j ∈ badset, Ioc (aa j) (bb j)), qhIntegrand F x t := h3 ▸ h1
      _ ≤ ∫ t in Ioc y 1, qhIntegrand F x t := h4
      _ = ∫ t in y..1, qhIntegrand F x t := h5
  have hD3 : ∫ t in y..1, qhIntegrand F x t ≤ (CA.Koebe.koebeCovConst)⁻¹ * Real.log (1 / y) := by
    rw [show qhIntegrand F x = (fun t : ℝ => ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ /
      Metric.infDist (F ((x : ℂ) + (t : ℂ) * Complex.I)) (F '' H)ᶜ) from rfl]
    exact qhLength_vertical_le hholo hinj x hy0 hy1
  have hbad_card : (badset.card : ℝ) ≤ ((n : ℝ) - j₀) / 4 := by
    have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
    nlinarith [hsum_le, hD3, hM, hMpos]
  -- every scale is good or bad
  have hmain : ∀ j ∈ Finset.Icc j₀ n,
      (∃ q : ℂ, ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
        ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \ E) ∨ j ∈ badset := by
    intro j hj
    by_cases hgood : ∃ t ∈ Icc (aa j) (bb j), (1 / M) * (2 : ℝ)⁻¹ ^ j ≤ qhDist F x t
    · left
      obtain ⟨t₀, ht₀, hDge⟩ := hgood
      refine ⟨F ((x : ℂ) + (t₀ : ℂ) * Complex.I), ?_⟩
      have ht₀_y : y ≤ t₀ := le_trans (haa_y j hj) ht₀.1
      have ht₀_h : t₀ ≤ h := le_trans ht₀.2 (hbb_mem j hj).2
      have hφt₀ : φ t₀ ≤ 2 * (2 : ℝ)⁻¹ ^ j := by
        rcases lt_or_eq_of_le ht₀.2 with hlt | heq
        · exact le_of_lt (hbb_lt j hj t₀ ⟨ht₀_y, ht₀_h⟩ hlt)
        · rw [heq]; exact (hbb_val j hj).le
      have hsubB : ball (F ((x : ℂ) + (t₀ : ℂ) * Complex.I)) ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
          ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) := by
        intro v hv
        rw [mem_ball, dist_comm] at hv ⊢
        have hdist : dist (F (x : ℂ)) (F ((x : ℂ) + (t₀ : ℂ) * Complex.I)) ≤
            2 * (2 : ℝ)⁻¹ ^ j := by
          rw [dist_comm, dist_eq_norm]
          exact hφt₀
        have hthird : (1 / M) * (2 : ℝ)⁻¹ ^ j ≤ 1 * (2 : ℝ)⁻¹ ^ j := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num) j)
          rw [div_le_iff₀ (lt_of_lt_of_le one_pos hM1)]
          linarith
        calc dist (F (x : ℂ)) v ≤ dist (F (x : ℂ)) (F ((x : ℂ) + (t₀ : ℂ) * Complex.I)) +
              dist (F ((x : ℂ) + (t₀ : ℂ) * Complex.I)) v := dist_triangle _ _ _
          _ < 2 * (2 : ℝ)⁻¹ ^ j + (1 / M) * (2 : ℝ)⁻¹ ^ j := by linarith
          _ ≤ 3 * (2 : ℝ)⁻¹ ^ j := by linarith
      have hsubE : ball (F ((x : ℂ) + (t₀ : ℂ) * Complex.I)) ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆ Eᶜ := by
        intro v hv
        have hvnot : v ∉ (F '' H)ᶜ := by
          intro hv'
          have h1 : qhDist F x t₀ ≤ dist (F ((x : ℂ) + (t₀ : ℂ) * Complex.I)) v :=
            Metric.infDist_le_dist_of_mem hv'
          have h2 : dist (F ((x : ℂ) + (t₀ : ℂ) * Complex.I)) v <
              (1 / M) * (2 : ℝ)⁻¹ ^ j := by
            have hv' := Metric.mem_ball.mp hv
            simpa only [dist_comm] using hv'
          linarith
        exact fun hvE => hvnot (hEsub hvE)
      intro v hv
      exact ⟨hsubB hv, hsubE hv⟩
    · right
      rw [hmem_bad j]
      refine ⟨hj, fun t ht => ?_⟩
      by_contra hcon
      exact hgood ⟨t, ht, le_of_not_gt hcon⟩
  -- counting: at most a quarter of the scales are bad, so at least half are good
  set goodset : Finset ℕ := (Finset.Icc j₀ n).filter (fun j => ∃ q : ℂ,
    ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
      ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \ E) with hgoodset
  have hsplit : goodset.card + ((Finset.Icc j₀ n).filter (fun j => ¬ (∃ q : ℂ,
      ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
        ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \ E))).card = (Finset.Icc j₀ n).card :=
    Finset.card_filter_add_card_filter_not _
  have hsub : (Finset.Icc j₀ n).filter (fun j => ¬ (∃ q : ℂ,
      ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
        ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \ E)) ⊆ badset := by
    intro j hj
    obtain ⟨hjIcc, hjnot⟩ := Finset.mem_filter.mp hj
    rcases hmain j hjIcc with hgood | hbad
    · exact absurd hgood hjnot
    · exact hbad
  have hgood_card : ((Finset.Icc j₀ n).filter (fun j => ¬ (∃ q : ℂ,
      ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
        ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \ E))).card ≤ badset.card :=
    Finset.card_le_card hsub
  have hcard_T : (Finset.Icc j₀ n).card = n - j₀ + 1 := by
    rw [Nat.card_Icc]
    omega
  have hreal : ((n : ℝ) - j₀) ≤ 2 * (goodset.card : ℝ) := by
    have hcast : ((Finset.Icc j₀ n).card : ℝ) = (n : ℝ) - j₀ + 1 := by
      rw [hcard_T]
      push_cast [Nat.cast_sub hjn]
      ring
    have h1 : (goodset.card : ℝ) = ((Finset.Icc j₀ n).card : ℝ) -
        (((Finset.Icc j₀ n).filter (fun j => ¬ (∃ q : ℂ,
          ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
            ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \ E))).card : ℝ) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) hsplit
      push_cast at this
      linarith
    have h2 : (((Finset.Icc j₀ n).filter (fun j => ¬ (∃ q : ℂ,
        ball q ((1 / M) * (2 : ℝ)⁻¹ ^ j) ⊆
          ball (F (x : ℂ)) (3 * (2 : ℝ)⁻¹ ^ j) \ E))).card : ℝ) ≤ (badset.card : ℝ) := by
      exact_mod_cast hgood_card
    linarith [hbad_card]
  show (n - j₀) ≤ 2 * goodset.card
  exact_mod_cast hreal

end JS
end QuantumZipper
