import QuantumZipper.Proofs.Complex.JSShadowACL3
import QuantumZipper.Proofs.Complex.JSLayerShadow

/-!
# EXT-JS node B1, steps 3 and 5: line-charged tent weights

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 "(C0: SH ⇒ removable.)", steps 3–5.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, proof of Proposition 1, pp. 270–272
(`literature/JonesSmirnov_Removability_ArkMat2000.pdf`): two points `u_i, u_{i+1}` of a line
lying in one shadow are joined by a curve through the Whitney cubes above them, and
`|f(u_i) - f(u_{i+1})| ≤ C Σ |∇f|(Q) l(Q)`, the sum over the cubes met by the curve; a cube is
charged only if the line meets its shadow, and the set of such lines has measure `≤ s(Q)`.

Here a chart `F` plays the role of the Whitney decomposition: the cubes are the top boxes
`Q_{k,j}` of the dyadic tents `T_{k,j}`, the shadow of `Q_{k,j}` is `F '' T_{k,j}`, the curve
from `F s` (`s ∈ I_{n,j}`) climbs the vertical segment above `s` to the top box `Q_{n,j}`, and
`|∇f|(Q) l(Q)` is replaced by `o_{k,j} = diam (g '' Q_{k,j})`, `g = e ∘ F`. A tent is charged at
the height `y` when the line `{im = y}` meets `F '' T_{k,j}` (`lineW`). The weights charged by
the points of one level-`n` tent `T_{n,j}` only involve the dyadic descendants of `(n,j)`
(`descShadow`); for distinct `j` these are disjoint, so the level-`n` total is the line shadow
function `lineShadow` (this replaces the curve-merging step on p. 272 of the source, which serves
the same purpose: no cube is charged twice).

Main results: `edist_le_three_descShadow` (oscillation of `g` on the base of a level-`n` tent,
at points of one line), `sum_descShadow_eq`, `antitone_lineShadow`, `lintegral_lineShadow_le`.
-/

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

variable {R : ℝ}

/-- The weight `o_{k,j} = diam (g '' Q_{k,j})` of the tent `T_{k,j}`, charged at the height `y`
when the line `{im = y}` meets the shadow `F '' T_{k,j}`. -/
def lineW (R : ℝ) (g F : ℂ → ℂ) (k j : ℕ) (y : ℝ) : ℝ≥0∞ :=
  ediam (g '' topBox R k j) * (Complex.im '' (F '' tent R k j)).indicator (1 : ℝ → ℝ≥0∞) y

/-- The charged weights of the dyadic descendants (of all levels `≥ n`) of the tent `(n,j)`. -/
def descShadow (R : ℝ) (g F : ℂ → ℂ) (n j : ℕ) (y : ℝ) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ j' ∈ Finset.range (2 ^ (n + m)) with j' / 2 ^ m = j, lineW R g F (n + m) j' y

/-- The level-`n` line shadow function `Φ_n(y) = Σ_{k ≥ n} Σ_j o_{k,j} 1{y ∈ im (F '' T_{k,j})}`. -/
def lineShadow (R : ℝ) (g F : ℂ → ℂ) (n : ℕ) (y : ℝ) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ j' ∈ Finset.range (2 ^ (n + m)), lineW R g F (n + m) j' y

/-- A tent whose base carries a point `s` with `F s` on the line at height `y` is charged. -/
lemma lineW_eq_of_mem {g F : ℂ → ℂ} {k j : ℕ} {y s : ℝ} (hR : 0 ≤ R) (hs : s ∈ dyI R k j)
    (hy : (F s).im = y) : lineW R g F k j y = ediam (g '' topBox R k j) := by
  have h : y ∈ Complex.im '' (F '' tent R k j) := ⟨F s, ⟨s, ofReal_mem_tent hR hs, rfl⟩, hy⟩
  simp [lineW, indicator_of_mem h]

/-- The descendant weights of the level-`n` tents add up to the line shadow function. -/
theorem sum_descShadow_eq (R : ℝ) (g F : ℂ → ℂ) (n : ℕ) (y : ℝ) :
    ∑ j ∈ Finset.range (2 ^ n), descShadow R g F n j y = lineShadow R g F n y := by
  unfold descShadow lineShadow
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun m => ?_
  refine Finset.sum_fiberwise_of_maps_to (fun j' hj' => ?_) _
  rw [Finset.mem_range] at hj' ⊢
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  exact hj'

/-- The line shadow functions decrease with the level. -/
theorem antitone_lineShadow (R : ℝ) (g F : ℂ → ℂ) (y : ℝ) :
    Antitone fun n => lineShadow R g F n y := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold lineShadow
  calc ∑' m : ℕ, ∑ j' ∈ Finset.range (2 ^ (n + 1 + m)), lineW R g F (n + 1 + m) j' y
      = ∑' m : ℕ, (fun k : ℕ => ∑ j' ∈ Finset.range (2 ^ (n + k)), lineW R g F (n + k) j' y)
          (m + 1) :=
        tsum_congr fun m => by simp only [show n + 1 + m = n + (m + 1) by omega]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (f := fun m : ℕ => m + 1)
        (add_left_injective 1)
        (fun k : ℕ => ∑ j' ∈ Finset.range (2 ^ (n + k)), lineW R g F (n + k) j' y)

/-- Points above the base of a tent, at a height of at most `2R`, lie in the chart box. -/
lemma mem_chartBox_of_dyI (hR : 0 < R) {n j : ℕ} (hj : j < 2 ^ n) {s t : ℝ}
    (hs : s ∈ dyI R n j) (ht0 : 0 ≤ t) (ht : t ≤ 2 * R) :
    (s : ℂ) + (t : ℂ) * I ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
  have hsR := dyI_subset_Icc hR.le hj hs
  rw [mem_reProdIm, re_ofReal_add_mul_I, im_ofReal_add_mul_I]
  exact ⟨⟨by linarith [hsR.1], by linarith [hsR.2]⟩, ht0, by linarith⟩

/-- **Vertical chain.** From a base point `s ∈ I_{n,j}` with `F s` on the line at height `y`,
the image under `g` of the vertical segment up to the top box `Q_{n,j}` has oscillation at most
the descendant weights of `(n,j)` charged at `y`. -/
theorem edist_vert_le_descShadow (hR : 0 < R) {g F : ℂ → ℂ}
    (hg : ContinuousOn g (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R)))
    {n j : ℕ} (hj : j < 2 ^ n) {s y : ℝ} (hs : s ∈ dyI R n j) (hy : (F s).im = y) :
    edist (g ((s : ℂ) + (dyLen R n : ℂ) * I)) (g s) ≤ descShadow R g F n j y := by
  choose J hJ hJs using fun m => exists_dyI_desc hR.le hs m
  set B := Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) with hB
  set f : ℕ → ℂ := fun m => g ((s : ℂ) + (dyLen R (n + m) : ℂ) * I) with hf
  have hbox : ∀ m, (s : ℂ) + (dyLen R (n + m) : ℂ) * I ∈ B := fun m =>
    mem_chartBox_of_dyI hR hj hs (dyLen_nonneg hR.le _) (dyLen_le hR.le _)
  have hs0 : (s : ℂ) ∈ B := by
    have := mem_chartBox_of_dyI hR hj hs le_rfl (by linarith : (0 : ℝ) ≤ 2 * R)
    rwa [show (s : ℂ) + ((0 : ℝ) : ℂ) * I = s by simp] at this
  have hl : Tendsto (fun m => dyLen R (n + m)) atTop (𝓝 0) :=
    ((tendsto_add_atTop_iff_nat n).2 (tendsto_dyLen R)).congr fun m => by rw [Nat.add_comm]
  have hp : Tendsto (fun m => (s : ℂ) + (dyLen R (n + m) : ℂ) * I) atTop (𝓝[B] (s : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hbox⟩
    have h1 := (tendsto_const_nhds (x := (s : ℂ))).add
      (((continuous_ofReal.tendsto 0).comp hl).mul_const I)
    simpa using h1
  have htend : Tendsto f atTop (𝓝 (g s)) := (hg _ hs0).tendsto.comp hp
  have hstep : ∀ m, edist (f m) (f m.succ) ≤ lineW R g F (n + m) (J m) y := by
    intro m
    rw [lineW_eq_of_mem hR.le (hJs m) hy]
    have hℓ := dyLen_nonneg hR.le (n + m)
    have hsucc : dyLen R (n + m.succ) = dyLen R (n + m) / 2 := dyLen_succ R (n + m)
    refine edist_le_ediam_of_mem ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
    · rw [topBox, mem_reProdIm, re_ofReal_add_mul_I, im_ofReal_add_mul_I]
      exact ⟨hJs m, by linarith, le_rfl⟩
    · rw [topBox, mem_reProdIm, re_ofReal_add_mul_I, im_ofReal_add_mul_I, hsucc]
      exact ⟨hJs m, le_rfl, by linarith⟩
  have hmain := edist_le_tsum_of_edist_le_of_tendsto₀ _ hstep htend
  have h0 : f 0 = g ((s : ℂ) + (dyLen R n : ℂ) * I) := by simp [hf]
  rw [h0] at hmain
  refine hmain.trans (ENNReal.tsum_le_tsum fun m => ?_)
  refine Finset.single_le_sum (f := fun j' => lineW R g F (n + m) j' y) (fun _ _ => zero_le) ?_
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_two_pow_of_div (hJ m) hj), hJ m⟩

/-- The top box weight of `(n,j)` is one of its descendant weights (level `n` itself). -/
theorem ediam_topBox_le_descShadow (hR : 0 < R) {g F : ℂ → ℂ} {n j : ℕ} (hj : j < 2 ^ n)
    {s y : ℝ} (hs : s ∈ dyI R n j) (hy : (F s).im = y) :
    ediam (g '' topBox R n j) ≤ descShadow R g F n j y := by
  rw [← lineW_eq_of_mem hR.le hs hy]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  refine Finset.single_le_sum (f := fun j' => lineW R g F (n + 0) j' y) (fun _ _ => zero_le) ?_
  simp [hj]

/-- **Tent oscillation on a line (blueprint §2 step 3).** For two base points `s, s' ∈ I_{n,j}`
whose chart images lie on the line at height `y`,
`|g s - g s'| ≤ 3 · (descendant weights of (n,j) charged at y)`. -/
theorem edist_le_three_descShadow (hR : 0 < R) {g F : ℂ → ℂ}
    (hg : ContinuousOn g (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R)))
    {n j : ℕ} (hj : j < 2 ^ n) {s s' y : ℝ} (hs : s ∈ dyI R n j) (hs' : s' ∈ dyI R n j)
    (hy : (F s).im = y) (hy' : (F s').im = y) :
    edist (g s) (g s') ≤ 3 * descShadow R g F n j y := by
  set a : ℂ := (s : ℂ) + (dyLen R n : ℂ) * I with ha
  set b : ℂ := (s' : ℂ) + (dyLen R n : ℂ) * I with hb
  have hℓ := dyLen_nonneg hR.le n
  have hatop : a ∈ topBox R n j := by
    rw [ha, topBox, mem_reProdIm, re_ofReal_add_mul_I, im_ofReal_add_mul_I]
    exact ⟨hs, by linarith, le_rfl⟩
  have hbtop : b ∈ topBox R n j := by
    rw [hb, topBox, mem_reProdIm, re_ofReal_add_mul_I, im_ofReal_add_mul_I]
    exact ⟨hs', by linarith, le_rfl⟩
  have h1 := edist_vert_le_descShadow hR hg hj hs hy
  have h3 : edist (g a) (g b) ≤ descShadow R g F n j y :=
    (edist_le_ediam_of_mem (mem_image_of_mem g hatop) (mem_image_of_mem g hbtop)).trans
      (ediam_topBox_le_descShadow hR hj hs hy)
  have h2' := edist_vert_le_descShadow (g := g) (F := F) hR hg hj hs' hy'
  calc edist (g s) (g s') ≤ edist (g s) (g a) + edist (g a) (g b) + edist (g b) (g s') :=
        edist_triangle4 _ _ _ _
    _ ≤ descShadow R g F n j y + descShadow R g F n j y + descShadow R g F n j y := by
        rw [edist_comm (g s)]
        gcongr
    _ = 3 * descShadow R g F n j y := by ring

/-- **Integral of the line shadow function (blueprint §2 step 5, first inequality).**
`∫ Φ_n ≤ Σ_{k ≥ n, j} 2 o_{k,j} d_{k,j}` with `d_{k,j} = diam (F '' T_{k,j})`. -/
theorem lintegral_lineShadow_le (hR : 0 < R) {g F : ℂ → ℂ}
    (hF : ContinuousOn F (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R))) (n : ℕ) :
    ∫⁻ y, lineShadow R g F n y ≤ ∑' m : ℕ, ∑ j ∈ Finset.range (2 ^ (n + m)),
      2 * (ediam (g '' topBox R (n + m) j) * ediam (F '' tent R (n + m) j)) := by
  have hmS : ∀ m, ∀ j ∈ Finset.range (2 ^ (n + m)),
      MeasurableSet (Complex.im '' (F '' tent R (n + m) j)) := fun m j hj =>
    measurableSet_im_image_tent (ShadowNull.isCompact_image_tent hR hF (Finset.mem_range.1 hj))
  have hmW : ∀ m, ∀ j ∈ Finset.range (2 ^ (n + m)), Measurable (lineW R g F (n + m) j) :=
    fun m j hj => (measurable_const.indicator (hmS m j hj)).const_mul _
  unfold lineShadow
  rw [lintegral_tsum fun m => (Finset.measurable_sum _ (hmW m)).aemeasurable]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [lintegral_finsetSum' _ fun j hj => (hmW m j hj).aemeasurable]
  refine Finset.sum_le_sum fun j hj => ?_
  unfold lineW
  rw [lintegral_const_mul _ (measurable_one.indicator (hmS m j hj)),
    lintegral_indicator_one (hmS m j hj)]
  have hc := ShadowNull.isCompact_image_tent hR hF (Finset.mem_range.1 hj)
  have hv := volume_im_image_tent_le hc ((ShadowNull.tent_nonempty hR (n + m) j).image F)
  calc ediam (g '' topBox R (n + m) j) * volume (Complex.im '' (F '' tent R (n + m) j))
      ≤ ediam (g '' topBox R (n + m) j) * (2 * ediam (F '' tent R (n + m) j)) := by gcongr
    _ = 2 * (ediam (g '' topBox R (n + m) j) * ediam (F '' tent R (n + m) j)) := by ring

end QuantumZipper.JS
