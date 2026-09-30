import QuantumZipper.Proofs.Complex.JSPorousCount
import QuantumZipper.Proofs.Complex.JSCounting
import QuantumZipper.Proofs.Complex.JSHolderLayer
import QuantumZipper.Analysis.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# EXT-JS node D4: mean porosity of the boundary image of a Hölder chart

Blueprint `blueprint/EXT_JS_BLUEPRINT.md` §2(D) step 3. Main result
(`JS.meanPorous_of_holderChart`): the image `E = F '' [-3R/2, 3R/2]` of the real segment under a
chart `F` for `K` on the box `[-2R,2R] ×ℂ [0,4R]` is *mean porous*: for every `p ∈ E` and every
`n ≥ n₀` at least `(n - j₀)/2` of the scales `j ∈ [j₀,n]` carry a hole
`ball q (c 2^{-j}) ⊆ ball p (3 · 2^{-j}) \ E`.

## Proof

Let `F` be `α`-Hölder with constant `C' ≥ 1` on the box, `h := min 1 (4R)`, and let `d₀ > 0` be
the minimum of `x ↦ ‖F (x + h i) - F x‖` over `x ∈ [-3R/2, 3R/2]` (continuous on a compact
interval, positive because `F (x + hi) ∈ F '' ℍ` while `F x ∉ F '' ℍ`, `JS.chart_real_notMem_image`).
Fix `p = F x` and `y := ((2⁻¹)^{n+1}/C')^{1/α}`; by Hölder `‖F (x + y i) - p‖ ≤ 2^{-(n+1)}`, and
`y ≤ h` for `n ≥ n₀`.

For `j₀ ≤ j ≤ n` let `b j` be the first time the continuous function `φ t = ‖F (x + t i) - p‖`
reaches the level `2 · 2^{-j}` and `a j` the last time it equals `2^{-j}` below `b j`
(`JS.exists_firstHit`, `JS.exists_lastHit`). Then `φ (a j) = 2^{-j}`, `φ (b j) = 2 · 2^{-j}`, and
`φ < 2 · 2^{-j}` on `[y, b j)`; moreover `b j' ≤ a j` for `j < j'`, so the half-open arcs
`(a j, b j]` are pairwise disjoint.

* If some `t ∈ [a j, b j]` has `d (F (x + t i)) ≥ 2^{-j}/M` (`d = infDist · (F '' ℍ)ᶜ`), then
  `q := F (x + t i)` gives a hole: `ball q (2^{-j}/M) ⊆ ball p (3 · 2^{-j}) \ E` because
  `E ⊆ (F '' ℍ)ᶜ` (`chart_real_notMem_image`) while `ball q (2^{-j}/M) ∩ (F '' ℍ)ᶜ = ∅`.
* Otherwise `d < 2^{-j}/M` on the whole arc, so the quasihyperbolic integrand satisfies
  `‖F'‖/d ≥ M 2^j ‖F'‖` there; integrating and using the FTC chord bound
  `‖F (x + b j i) - F (x + a j i)‖ ≥ φ (b j) - φ (a j) = 2^{-j}` gives `∫_{a j}^{b j} ‖F'‖/d ≥ M`.

Summing over the bad scales (disjoint arcs, nonnegative integrand) and using the D3 bound
`JS.qhLength_vertical_le` for the quasihyperbolic length of the vertical ray, the number of bad
scales is at most `(A n + B)/M ≤ (n - j₀)/4`, which leaves at least half of the scales good.

## Sources

`blueprint/EXT_JS_BLUEPRINT.md` §2(D) step 3. (Jones–Smirnov, *Removability theorems for Sobolev
functions and quasiconformal maps*, Ark. Mat. 38 (2000), Corollary 2 and its proof, p. 267, is the
place where the corresponding covering input is used; the argument there is attributed by them to
"[JM]" (Jones–Makarov), and neither layer decay nor mean porosity is stated in Jones–Smirnov — so
the reference for the *statement* of D4 is the blueprint, not JS; AUDIT10 C10-2.) The individual
steps are elementary
(intermediate value theorem, fundamental theorem of calculus, triangle inequality); the
quasihyperbolic length bound is node D3 (`JS.qhLength_vertical_le`), proved from the weak Koebe
estimate `CA.Koebe.infDist_compl_image_ge`. Everything here is an **own elementary proof**
following the blueprint sketch; no other published argument is transported.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology Real

namespace QuantumZipper
namespace JS

/-- **EXT-JS node D4 (blueprint §2(D) step 3).** The image of the real interval
`[-3R/2, 3R/2]` under a chart `F` for `K` on the box `[-2R,2R] ×ℂ [0,4R]` is mean porous, provided
`F` is Hölder continuous on the box: there are `c > 0` and `C, Kp, j₀, n₀` with `Kp > 0` (here
`c = 1/M`, `C = 3`, `Kp = 2`) such that for every `p ∈ E` and every `n ≥ n₀` at least `(n - j₀)/2`
of the scales `j ∈ [j₀,n]` carry a hole `ball q (c 2^{-j}) ⊆ ball p (C 2^{-j}) \ E`.

This is `JS.IsMeanPorous` (node D5's hypothesis), deduced by `JS.scale_count_le` from the
quasihyperbolic length bound of node D3 and the weak Koebe estimate behind it. Own elementary
proof following Jones–Smirnov, Ark. Mat. 38 (2000), §3 and the blueprint sketch. -/
theorem meanPorous_of_holderChart {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F)
    (hHolder : IsHolderOn F (Set.Icc (-2 * R) (2 * R) ×ℂ Set.Icc 0 (4 * R))) :
    ∃ c C : ℝ, 0 < c ∧ ∃ Kp j₀ n₀ : ℕ, 0 < Kp ∧
      IsMeanPorous (F '' ((fun t : ℝ => (t : ℂ)) '' Set.Icc (-(3 / 2) * R) ((3 / 2) * R)))
        c C Kp j₀ n₀ := by
  classical
  have hR : 0 < R := hF.pos
  have hcont : ContinuousOn F (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R)) := hF.cont
  have hholo : DifferentiableOn ℂ F H := hF.holo
  have hinj : InjOn F H := hF.inj
  obtain ⟨α, Ch, hα, hCh⟩ := hHolder
  -- Step 0: normalise the Hölder constant to be at least `1`
  set C' : ℝ := max Ch 1 with hC'def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos hC'1
  have hCh' : ∀ z ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R),
      ∀ w ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R), ‖F z - F w‖ ≤ C' * ‖z - w‖ ^ α := by
    intro z hz w hw
    exact (hCh z hz w hw).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  -- Step 1: the height `h = min 1 (4R)` and the uniform top distance `d₀`
  set h : ℝ := min 1 (4 * R) with hhdef
  have hh0 : 0 < h := by rw [hhdef]; exact lt_min one_pos (by linarith)
  have hh1 : h ≤ 1 := by rw [hhdef]; exact min_le_left _ _
  have hh4R : h ≤ 4 * R := by rw [hhdef]; exact min_le_right _ _
  have hIcc_ne : (Icc (-(3 / 2) * R) ((3 / 2) * R)).Nonempty :=
    ⟨0, ⟨by linarith, by linarith⟩⟩
  have hψcont : ContinuousOn (fun x : ℝ => ‖F ((x : ℂ) + (h : ℂ) * Complex.I) - F (x : ℂ)‖)
      (Icc (-(3 / 2) * R) ((3 / 2) * R)) := by
    have hxbox : ∀ x ∈ Icc (-(3 / 2) * R) ((3 / 2) * R),
        ((x : ℂ) + (h : ℂ) * Complex.I) ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
      intro x hx
      have himx : ((x : ℂ) + (h : ℂ) * Complex.I).im = h := by simp
      have hrexx : ((x : ℂ) + (h : ℂ) * Complex.I).re = x := by simp
      rw [Complex.mem_reProdIm, hrexx, himx]
      exact ⟨⟨by linarith [hx.1, hR], by linarith [hx.2, hR]⟩, hh0.le, hh4R⟩
    have hzbox : ∀ x ∈ Icc (-(3 / 2) * R) ((3 / 2) * R),
        (x : ℂ) ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
      intro x hx
      rw [Complex.mem_reProdIm, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨⟨by linarith [hx.1, hR], by linarith [hx.2, hR]⟩, ⟨le_refl 0, by linarith [hR]⟩⟩
    have hrayR : ContinuousOn (fun x : ℝ => (x : ℂ) + (h : ℂ) * Complex.I)
        (Icc (-(3 / 2) * R) ((3 / 2) * R)) :=
      (((Complex.continuous_ofReal.comp continuous_id).add continuous_const)).continuousOn
    have hlinR : ContinuousOn (fun x : ℝ => (x : ℂ)) (Icc (-(3 / 2) * R) ((3 / 2) * R)) :=
      Complex.continuous_ofReal.continuousOn
    exact ((hcont.comp hrayR hxbox).sub (hcont.comp hlinR hzbox)).norm
  obtain ⟨x₀, hx₀, hx₀min⟩ := isCompact_Icc.exists_isMinOn hIcc_ne hψcont
  set d₀ : ℝ := ‖F ((x₀ : ℂ) + (h : ℂ) * Complex.I) - F (x₀ : ℂ)‖ with hd₀def
  have hd₀pos : 0 < d₀ := by
    have hx₀2R : x₀ ∈ Icc (-2 * R) (2 * R) := ⟨by linarith [hx₀.1, hR], by linarith [hx₀.2, hR]⟩
    have htop : F ((x₀ : ℂ) + (h : ℂ) * Complex.I) ∈ F '' H :=
      ⟨_, by show 0 < ((x₀ : ℂ) + (h : ℂ) * Complex.I).im; simpa using hh0, rfl⟩
    have hbot : F (x₀ : ℂ) ∉ F '' H := chart_real_notMem_image hF hx₀2R
    rw [hd₀def]
    by_contra hle
    push Not at hle
    have hzero : F ((x₀ : ℂ) + (h : ℂ) * Complex.I) - F (x₀ : ℂ) = 0 :=
      norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    exact hbot ((sub_eq_zero.mp hzero) ▸ htop)
  have hd₀le : ∀ x ∈ Icc (-(3 / 2) * R) ((3 / 2) * R),
      d₀ ≤ ‖F ((x : ℂ) + ((min 1 (4 * R) : ℝ) : ℂ) * Complex.I) - F (x : ℂ)‖ := by
    intro x hx
    rw [← hhdef]
    exact hx₀min hx
  -- Step 2: the scale `j₀` below the top distance, and the starting scale `n₀`
  obtain ⟨j₀, hj₀⟩ : ∃ j : ℕ, 2 * (2 : ℝ)⁻¹ ^ j ≤ d₀ := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < d₀ / 2 by linarith)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨m, le_of_lt (by nlinarith [hm])⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < C' * h ^ α :=
    exists_pow_lt_of_lt_one (mul_pos hC'pos (Real.rpow_pos_of_pos hh0 α))
      (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hpow_mono : ∀ n : ℕ, m₁ ≤ n + 1 → (2 : ℝ)⁻¹ ^ (n + 1) ≤ C' * h ^ α := fun n hn =>
    le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hm₁.le
  set n₀ : ℕ := max (2 * j₀) (max m₁ 1) with hn₀def
  -- Step 3: the constants of the final statement
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcpos : 0 < (CA.Koebe.koebeCovConst)⁻¹ := inv_pos.mpr CA.Koebe.koebeCovConst_pos
  set A : ℝ := (CA.Koebe.koebeCovConst)⁻¹ * (2 * Real.log 2 / α) with hAdef
  set B : ℝ := (CA.Koebe.koebeCovConst)⁻¹ * ((|Real.log C'| + 2 * Real.log 2) / α) with hBdef
  set M : ℝ := 8 * (A + B + 1) with hMdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hcpos.le (div_nonneg (by linarith) hα.le)
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg hcpos.le (div_nonneg (add_nonneg (abs_nonneg _)
      (mul_nonneg (by norm_num) hlog2pos.le)) hα.le)
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    linarith
  refine ⟨1 / M, 3, div_pos one_pos (lt_of_lt_of_le one_pos hM1), 2, j₀, n₀, by norm_num, ?_⟩
  intro p hp n hn
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨x, hx, rfl⟩ := hz
  have hjn : j₀ ≤ n := by
    have h1 : n₀ ≤ n := hn
    rw [hn₀def] at h1
    omega
  have hn1 : 1 ≤ n := by
    have h1 : n₀ ≤ n := hn
    rw [hn₀def] at h1
    omega
  have hm₁n : m₁ ≤ n := by
    have h1 : n₀ ≤ n := hn
    rw [hn₀def] at h1
    omega
  have hn2 : 2 * j₀ ≤ n := by
    have h1 : n₀ ≤ n := hn
    rw [hn₀def] at h1
    omega
  -- the bottom height `y` and its properties
  set y : ℝ := (((2 : ℝ)⁻¹) ^ (n + 1) / C') ^ (1 / α) with hydef
  have hybase : 0 < (2 : ℝ)⁻¹ ^ (n + 1) / C' :=
    div_pos (pow_pos (by norm_num) _) hC'pos
  have hy0 : 0 < y := Real.rpow_pos_of_pos hybase _
  have hyC : C' * y ^ α = (2 : ℝ)⁻¹ ^ (n + 1) := by
    have hexp : (1 / α) * α = 1 := by rw [one_div, inv_mul_cancel₀ hα.ne']
    have hcancel : C' * ((2 : ℝ)⁻¹ ^ (n + 1) / C') = (2 : ℝ)⁻¹ ^ (n + 1) := by
      rw [div_eq_mul_inv, mul_comm ((2 : ℝ)⁻¹ ^ (n + 1)) C'⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hC'pos.ne', one_mul]
    rw [hydef, ← Real.rpow_mul hybase.le, hexp, Real.rpow_one, hcancel]
  have hyh : y ≤ h := by
    have hpoweq : (2 : ℝ)⁻¹ ^ (n + 1) / C' ≤ h ^ α := by
      rw [div_le_iff₀ hC'pos, mul_comm]
      exact hpow_mono n (by omega)
    calc (((2 : ℝ)⁻¹) ^ (n + 1) / C') ^ (1 / α) ≤ (h ^ α) ^ (1 / α) :=
          Real.rpow_le_rpow hybase.le hpoweq (div_nonneg zero_le_one hα.le)
      _ = h := by
          rw [← Real.rpow_mul hh0.le,
            show α * (1 / α) = 1 by rw [one_div, mul_inv_cancel₀ hα.ne'], Real.rpow_one]
  have hy1 : y ≤ 1 := le_trans hyh hh1
  have hyHolder : ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F (x : ℂ)‖ ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
    have hybox : ((x : ℂ) + (y : ℂ) * Complex.I) ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
      have himy : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
      have hrey : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
      rw [Complex.mem_reProdIm, hrey, himy]
      exact ⟨⟨by linarith [hx.1, hR], by linarith [hx.2, hR]⟩,
        ⟨hy0.le, le_trans hyh hh4R⟩⟩
    have hxbox : (x : ℂ) ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
      rw [Complex.mem_reProdIm, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨⟨by linarith [hx.1, hR], by linarith [hx.2, hR]⟩, ⟨le_refl 0, by linarith [hR]⟩⟩
    have h := hCh' _ hybox _ hxbox
    have hnorm : ((x : ℂ) + (y : ℂ) * Complex.I) - (x : ℂ) = (y : ℂ) * Complex.I := by ring
    rw [hnorm, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy0] at h
    exact h.trans (le_of_eq hyC)
  -- the quasihyperbolic length of the ray is at most `M (n - j₀)/4`
  have hMineq : (CA.Koebe.koebeCovConst)⁻¹ * Real.log (1 / y) ≤ M * ((n : ℝ) - j₀) / 4 := by
    have hlog : Real.log (1 / y) = (((n + 1 : ℕ) : ℝ) * Real.log 2 + Real.log C') / α := by
      rw [one_div, Real.log_inv, hydef, Real.log_rpow hybase (1 / α),
        Real.log_div (x := (2 : ℝ)⁻¹ ^ (n + 1)) (y := C') (by positivity) hC'pos.ne',
        Real.log_pow, Real.log_inv (x := (2 : ℝ))]
      ring
    have h1 : (CA.Koebe.koebeCovConst)⁻¹ * Real.log (1 / y) ≤ A * n + B := by
      rw [hlog, hAdef, hBdef]
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      have hkey : ((((n + 1 : ℕ) : ℝ)) * Real.log 2 + Real.log C') / α ≤
          ((|Real.log C'| + 2 * Real.log 2) + 2 * Real.log 2 * n) / α := by
        refine div_le_div_of_nonneg_right ?_ hα.le
        have habs : Real.log C' ≤ |Real.log C'| := le_abs_self _
        rw [hcast]
        nlinarith [habs, hlog2pos, abs_nonneg (Real.log C'),
          show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      calc (CA.Koebe.koebeCovConst)⁻¹ *
            ((((n + 1 : ℕ) : ℝ) * Real.log 2 + Real.log C') / α)
          ≤ (CA.Koebe.koebeCovConst)⁻¹ *
              (((|Real.log C'| + 2 * Real.log 2) + 2 * Real.log 2 * n) / α) :=
            mul_le_mul_of_nonneg_left hkey hcpos.le
        _ = (CA.Koebe.koebeCovConst)⁻¹ * (2 * Real.log 2 / α) * n +
              (CA.Koebe.koebeCovConst)⁻¹ * ((|Real.log C'| + 2 * Real.log 2) / α) := by ring
    have h2 : A * n + B ≤ M * ((n : ℝ) - j₀) / 4 := by
      rw [hMdef]
      have hn2' : 2 * (j₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith [hA0, hB0, hn2', hn1']
    linarith
  exact scale_count_le hR hcont hholo hinj (fun x hx => chart_real_notMem_image hF hx)
    hj₀ hd₀le hx hjn hy0 hy1 (by rw [← hhdef]; exact hyh) hyHolder hM1 hMineq

end JS
end QuantumZipper
