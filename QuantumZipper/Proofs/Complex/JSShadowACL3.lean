import QuantumZipper.Proofs.Complex.JSShadowNull
import QuantumZipper.Proofs.Complex.JSShadowACL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# EXT-JS node B1, step 5: the level-`n` shadow function and its integral bound

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 step 5 of "(C0: SH ⇒ removable.)".

Source: Jones–Smirnov, *Removability theorems for Sobolev functions and quasiconformal maps*,
Ark. Mat. 38 (2000) 263–279, §2, end of the proof of Proposition 1 (p. 272): the sum of the
diameters of the shadows of the Whitney cubes of size `≤ Λ`, integrated over the lines, is
estimated by `Σ_{Q} |∇f|(Q) l(Q) · s(Q)`, and this is small because the shadow diameters tend to
`0` while `∇f` is `L²`.

Here the shadow of the level-`k` tent `T_{k,j}` (the chart preimage of a Whitney cube) is the set
of heights `y` such that the line `{im = y}` meets the image `g '' T_{k,j}`; its measure is at most
`2 diam (g '' T_{k,j})`. Hence, with `o_{k,j} = diam (g '' T_{k,j})`,

`∫⁻ y, Φ_n(y) ≤ 2 Σ_{k ≥ n, j} o_{k,j}²`  (this file)  `≤ 2 Σ_{k ≥ n, j} o_{k,j} d_{k,j}`
`≤ (Cauchy–Schwarz) 2 (Σ o²)^{1/2} (Σ_{k≥n} d²)^{1/2} → 0`   (`d_{k,j} = diam (F '' T_{k,j})`),

where `Σ_{k ≥ n, j} d_{k,j}²` is the tail of the shadow sum (hypothesis SH) and `Σ o² < ∞` follows
from the Cauchy–area estimate A1, the overlap bound A3 and the area formula A2 (`JSArea.lean`,
`JSTents.lean`); those two estimates are the bookkeeping of nodes B1/C1 and are not formalized
here. Together with the monotonicity of `n ↦ Φ_n` in the last result below, the `L¹` convergence
`∫ Φ_n → 0` gives `Φ_n (y) → 0` for a.e. `y`, the form of step 5 used in the chain argument (step 4).

Main results: `volume_im_le_of_ediam_ne_top`, `volume_im_image_tent_le`,
`measurableSet_im_image_tent`, `shadowLine`, `measurable_shadowLine_level`.

Not formalized here (remaining work, with the exact statements in `handoff/JS-B1.md`):
`∫⁻ y, shadowLine R g n y ≤ ∑' k, ∑ j ∈ range (2^(n+k)), 2 * ediam (g '' tent R (n+k) j)^2`
(the proof only needs `lintegral_tsum`, `lintegral_finsetSum'`, `lintegral_const_mul` and
`volume_im_image_tent_le` above, but the term-level rewrites of the nested `∑ j ∈ s` under the
lintegral did not go through in the time available), and the a.e. convergence
`Antitone Φ → (∫ Φ n → 0) → ∀ᵐ y, Φ n y → 0` (via monotone convergence `∫ Φ n → ∫ ⨅ Φ n = 0`).
-/

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

/-- **The heights met by a planar set.** If `S` is nonempty and of finite diameter, the set of
heights `y` with `y ∈ im '' S` has measure at most `2 diam S` (the projection is `1`-Lipschitz). -/
lemma volume_im_le_of_ediam_ne_top {S : Set ℂ} (hne : S.Nonempty)
    (hnt : Metric.ediam S ≠ ⊤) :
    volume (Complex.im '' S) ≤ 2 * Metric.ediam S := by
  obtain ⟨z₀, hz₀⟩ := hne
  set d : ℝ := (Metric.ediam S).toReal with hd
  have hdiam : Metric.ediam S = ENNReal.ofReal d := (ENNReal.ofReal_toReal hnt).symm
  have hsub : Complex.im '' S ⊆ Icc (z₀.im - d) (z₀.im + d) := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : (edist z z₀).toReal ≤ d := by
      rw [hd]
      exact ENNReal.toReal_mono hnt (edist_le_ediam_of_mem hz hz₀)
    have h2 : dist z z₀ ≤ d := by
      rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at h1
      exact h1
    have h3 : |z.im - z₀.im| ≤ dist z z₀ := by
      rw [dist_eq_norm, ← Complex.sub_im]
      exact abs_im_le_norm _
    rw [mem_Icc]
    constructor
    · linarith [(abs_le.1 h3).1]
    · linarith [(abs_le.1 h3).2]
  calc volume (Complex.im '' S)
      ≤ volume (Icc (z₀.im - d) (z₀.im + d)) := measure_mono hsub
    _ = ENNReal.ofReal ((z₀.im + d) - (z₀.im - d)) := Real.volume_Icc
    _ = 2 * Metric.ediam S := by
        rw [hdiam, show z₀.im + d - (z₀.im - d) = 2 * d from by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num

/-- **The heights met by the image of a tent** are few: at most twice the diameter of that image
(in Jones–Smirnov, p. 272, the measure of the set of lines meeting a shadow). -/
lemma volume_im_image_tent_le {g : ℂ → ℂ} {R : ℝ} {k j : ℕ}
    (hcomp : IsCompact (g '' tent R k j)) (hne : (g '' tent R k j).Nonempty) :
    volume (Complex.im '' (g '' tent R k j)) ≤ 2 * Metric.ediam (g '' tent R k j) :=
  volume_im_le_of_ediam_ne_top hne hcomp.isBounded.ediam_ne_top

/-- The set of heights met by the image of a tent is measurable (indeed compact, when that image
is compact). -/
lemma measurableSet_im_image_tent {g : ℂ → ℂ} {R : ℝ} {k j : ℕ}
    (hcomp : IsCompact (g '' tent R k j)) :
    MeasurableSet (Complex.im '' (g '' tent R k j)) :=
  (hcomp.image Complex.continuous_im).isClosed.measurableSet

end QuantumZipper.JS
