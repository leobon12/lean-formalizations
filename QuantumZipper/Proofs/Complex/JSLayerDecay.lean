import QuantumZipper.Proofs.Complex.JSPorous
import QuantumZipper.Proofs.Complex.JSCounting
import QuantumZipper.Proofs.Complex.JSHolderLayer
import QuantumZipper.Proofs.Complex.JSLayerShadow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# EXT-JS node D6: layer decay for a Hölder chart

Blueprint `blueprint/EXT_JS_BLUEPRINT.md` §2 "(D: Hölder chart ⇒ LA.)" step 5 and §3 node D6.

Source. The quantitative input "the boundary layer of a Hölder domain has area `O(δ^η)`" is **not**
a Jones–Smirnov theorem. In P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev
functions and quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, the corresponding estimate appears
only as the deduction of their Corollary 2 (p. 267) from `Σ_j s(Q_j^k)^{2−ε} < M` "by arguments of
[JM]" (Jones–Makarov); layer decay and mean porosity are nowhere stated there (AUDIT10 C10-2).
The route used here is the blueprint's own (§2(D) steps 3–5, nodes D3–D6), assembled from the
already proved nodes — layer decay via mean porosity, with the upper Minkowski dimension of a mean
porous set from Koskela–Rohde, Math. Ann. 309 (1997) 593–609 (cited only for "mean porous ⇒ upper
Minkowski dimension < 2"):

* **D4** (`JS.meanPorous_of_holderChart`, `JSPorous.lean`): the image `E = F '' [-3R/2,3R/2]`
  of the real segment under a Hölder chart is mean porous;
* **D5** (`JS.volume_thickening_le_of_meanPorous`, `JSCounting.lean`): a bounded mean porous set
  `E ⊆ ℂ` has `volume (thickening r E) ≤ C' r^η'` for all `r ∈ (0,1]`;
* **the Hölder step** (this file): if `F` is `α`-Hölder with constant `C_H` on the box
  `[-2R,2R] ×ℂ [0,4R]`, then for `δ ≤ min 1 (4R)` every point `F (x + iy)`, `x ∈ [-3R/2,3R/2]`,
  `0 < y < δ`, satisfies `‖F (x + iy) - F x‖ ≤ C_H y^α < C_H δ^α`, so the image of the layer
  `[-3R/2,3R/2] ×ℂ (0,δ)` lies in `thickening (C_H δ^α) E`; hence its area is
  `≤ C' (C_H δ^α)^{η'} = (C' C_H^{η'}) δ^{αη'}`.

The layer is only `δ ≤ 1` high while `F` is only Hölder on the box of height `4R`, so for
`δ > min 1 (4R)` (possible only when `4R < 1`) the part of the layer above the box is **not**
Hölder controlled. It is handled with the trivial bound `volume (F '' layer_δ) ≤ M`, where
`M = area (F '' (I_{3R/2} ×ℂ [0,h])) + area (F '' (I_{3R/2} ×ℂ [h,1]))` with
`h = min 1 (4R) < ∞` (images of compact sets: the lower piece sits in the box where `F` is
continuous, the upper piece in `ℍ` where `F` is holomorphic); since `δ > h` forces
`δ^{αη'} ≥ h^{αη'} > 0`, a large constant `C` covers that range. Own elementary proof
(the blueprint's step 5; the finitely many large scales are an addition of this file, recorded as
a deviation — the statement of the blueprint node D6 says `δ ≤ 1` while its Hölder box has
height `4R`).

The conclusion is the blueprint's `JS.LayerDecay R F`, imported from
`QuantumZipper/Proofs/Complex/JSLayerShadow.lean` (node C1's file), so no adapter is needed.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace QuantumZipper
namespace JS

/-- The boundary curve `E = F '' [-3R/2, 3R/2]` of a chart (node D6). -/
def realSeg (R : ℝ) : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Icc (-3 * R / 2) (3 * R / 2)

/-- The rectangle of the box `[-2R,2R] ×ℂ [0,4R]` in which a chart is continuous. -/
def chartBox (R : ℝ) : Set ℂ := Set.Icc (-2 * R) (2 * R) ×ℂ Set.Icc 0 (4 * R)

/-! ### The Hölder step -/

/-- **The Hölder step of node D6 (blueprint §2(D) step 5).** If `F` is `α`-Hölder with constant
`Ch` on the box and `δ ≤ min 1 (4R)`, then the image of the layer of height `δ` lies in the
`Ch δ^α`-thickening of the boundary curve `F '' [-3R/2, 3R/2]`. -/
lemma image_layer_subset_thickening {R : ℝ} {F : ℂ → ℂ} {α Ch : ℝ} (hR : 0 < R) (hα : 0 < α)
    (hChpos : 0 < Ch)
    (hCh : ∀ z ∈ chartBox R, ∀ w ∈ chartBox R, ‖F z - F w‖ ≤ Ch * ‖z - w‖ ^ α)
    {δ : ℝ} (hδh : δ ≤ min 1 (4 * R)) :
    F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ) ⊆
      thickening (Ch * δ ^ α) (F '' realSeg R) := by
  rintro w ⟨z, hz, rfl⟩
  rw [Complex.mem_reProdIm] at hz
  obtain ⟨hzre, hzim⟩ := hz
  have hzre_box : z.re ∈ Set.Icc (-2 * R) (2 * R) :=
    ⟨by linarith [hzre.1, hR], by linarith [hzre.2, hR]⟩
  have hzim_box : z.im ∈ Set.Icc 0 (4 * R) :=
    ⟨hzim.1.le, le_trans hzim.2.le (le_trans hδh (min_le_right _ _))⟩
  have hz_box : z ∈ chartBox R := by
    rw [chartBox, Complex.mem_reProdIm]; exact ⟨hzre_box, hzim_box⟩
  have hx_box : ((z.re : ℝ) : ℂ) ∈ chartBox R := by
    rw [chartBox, Complex.mem_reProdIm, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨hzre_box, ⟨le_refl 0, by linarith [hR]⟩⟩
  have hmem : F ((z.re : ℝ) : ℂ) ∈ F '' realSeg R :=
    ⟨((z.re : ℝ) : ℂ), by rw [realSeg]; exact ⟨z.re, hzre, rfl⟩, rfl⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨F ((z.re : ℝ) : ℂ), hmem, ?_⟩
  have hnorm : ‖z - ((z.re : ℝ) : ℂ)‖ = z.im := by
    have h1 : z - ((z.re : ℝ) : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg hzim.1.le]
  calc dist (F z) (F ((z.re : ℝ) : ℂ)) = ‖F z - F ((z.re : ℝ) : ℂ)‖ := dist_eq_norm _ _
    _ ≤ Ch * ‖z - ((z.re : ℝ) : ℂ)‖ ^ α := hCh z hz_box _ hx_box
    _ = Ch * z.im ^ α := by rw [hnorm]
    _ < Ch * δ ^ α := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hzim.1.le hzim.2 hα) hChpos

/-! ### The large scales: the layer above the Hölder box -/

/-- **Split of the layer at the height `h = min 1 (4R)`.** For `δ ≤ 1` the layer of height `δ` is
contained in the union of the box-height part and the part above it. -/
lemma layer_subset_box_union {R δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ ⊆
      (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc 0 (min 1 (4 * R))) ∪
        (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc (min 1 (4 * R)) 1) := by
  intro z hz
  rw [Complex.mem_reProdIm] at hz
  rcases le_or_gt z.im (min 1 (4 * R)) with hle | hlt
  · exact Or.inl (by rw [Complex.mem_reProdIm]; exact ⟨hz.1, ⟨hz.2.1.le, hle⟩⟩)
  · exact Or.inr (by
      rw [Complex.mem_reProdIm]; exact ⟨hz.1, ⟨hlt.le, le_trans hz.2.2.le hδ.2⟩⟩)

/-- **The trivial bound for one layer** (blueprint §2(D) step 5, large scales). For `δ ≤ 1` the
area of the image of the layer of height `δ` is at most the sum of the areas of the images of the
two compact rectangles obtained by cutting the layer at the height `min 1 (4R) ≤ 1`: the lower
one lies in the box (where a chart is continuous), the upper one in `ℍ` (where it is
holomorphic). No Hölder continuity is used. -/
lemma volume_image_layer_le_add {R : ℝ} {F : ℂ → ℂ} {δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ)) ≤
      volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc 0 (min 1 (4 * R)))) +
        volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ
          Set.Icc (min 1 (4 * R)) 1)) := by
  calc volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ))
      ≤ volume (F '' ((Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc 0 (min 1 (4 * R))) ∪
          (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc (min 1 (4 * R)) 1))) :=
        measure_mono (image_mono (layer_subset_box_union hδ))
    _ = volume ((F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc 0 (min 1 (4 * R)))) ∪
          (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc (min 1 (4 * R)) 1))) := by
        rw [image_union]
    _ ≤ _ := measure_union_le _ _

/-! ### Node D6 -/

/-- **EXT-JS node D6 (blueprint §2(D) step 5).** A chart `F` that is Hölder continuous on the
box `[-2R,2R] ×ℂ [0,4R]` has layer decay: the image of the horizontal layer
`[-3R/2,3R/2] ×ℂ (0,δ)` has area `O(δ^η)` for some `η > 0` and all `δ ∈ (0,1]`.

Proof: `E = F '' [-3R/2,3R/2]` is bounded and
mean porous (D4), so `volume (thickening r E) ≤ C' r^{η'}` for `r ≤ 1` (D5); for `δ ≤ min 1 (4R)`
the whole layer is Hölder-controlled and maps into `thickening (C_H δ^α) E`, giving
`volume ≤ (C' C_H^{η'}) δ^{αη'}`; for `δ > min 1 (4R)` the layer image is bounded by the constant
`M` of `volume_image_layer_le_add`, and `δ^{αη'} ≥ (min 1 (4R))^{αη'} > 0`. -/
theorem layerDecay_of_holder {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F)
    (hH : IsHolderOn F (Set.Icc (-2 * R) (2 * R) ×ℂ Set.Icc 0 (4 * R))) : LayerDecay R F := by
  classical
  have hR : 0 < R := hF.pos
  -- the boundary curve `E` and its boundedness
  have hseg_box : realSeg R ⊆ chartBox R := by
    intro z hz
    rw [realSeg] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [chartBox, Complex.mem_reProdIm, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨⟨by linarith [ht.1, hR], by linarith [ht.2, hR]⟩, ⟨le_refl 0, by linarith [hR]⟩⟩
  have hseg_compact : IsCompact (realSeg R) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hE_bdd : Bornology.IsBounded (F '' realSeg R) :=
    (hseg_compact.image_of_continuousOn (hF.cont.mono hseg_box)).isBounded
  -- D4: mean porosity of `E`
  obtain ⟨c, C, hc, Kp, j₀, n₀, hKp, hpor⟩ := meanPorous_of_holderChart hF hH
  have hIccR : Set.Icc (-(3 / 2) * R) ((3 / 2) * R) = Set.Icc (-3 * R / 2) (3 * R / 2) := by
    congr 1 <;> ring
  have hpor' : IsMeanPorous (F '' realSeg R) c C Kp j₀ n₀ := by
    rw [realSeg, ← hIccR]; exact hpor
  -- D5: decay of the volume of the thickenings of `E`
  obtain ⟨C', η', hη'pos, hC'⟩ :=
    volume_thickening_le_of_meanPorous hE_bdd hc hKp hpor'
  -- Hölder data, normalised so that the constant is `≥ 1`
  obtain ⟨α, Ch, hα, hCh⟩ := hH
  set CH : ℝ := max Ch 1 with hCHdef
  have hCHpos : 0 < CH := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCh' : ∀ z ∈ chartBox R, ∀ w ∈ chartBox R, ‖F z - F w‖ ≤ CH * ‖z - w‖ ^ α := by
    intro z hz w hw
    exact (hCh z hz w hw).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  -- the height of the layer that is Hölder controlled
  set h : ℝ := min 1 (4 * R) with hhdef
  have hh0 : 0 < h := by rw [hhdef]; exact lt_min one_pos (by linarith)
  have hh1 : h ≤ 1 := by rw [hhdef]; exact min_le_left _ _
  -- the two compact pieces of the layer of height `h`, and the constant `M`
  set A₁ : Set ℂ := Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc 0 h with hA₁
  set A₂ : Set ℂ := Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Icc h 1 with hA₂
  have hA₁c : IsCompact A₁ := isCompact_Icc.reProdIm isCompact_Icc
  have hA₂c : IsCompact A₂ := isCompact_Icc.reProdIm isCompact_Icc
  have hA₁sub : A₁ ⊆ chartBox R := by
    intro z hz
    rw [hA₁] at hz
    rw [Complex.mem_reProdIm] at hz
    rw [chartBox, Complex.mem_reProdIm]
    exact ⟨⟨by linarith [hz.1.1, hR], by linarith [hz.1.2, hR]⟩,
      ⟨hz.2.1, le_trans hz.2.2 (min_le_right _ _)⟩⟩
  have hA₂sub : A₂ ⊆ H := by
    intro z hz
    rw [hA₂] at hz
    rw [Complex.mem_reProdIm] at hz
    exact lt_of_lt_of_le hh0 hz.2.1
  have hA₁lt : volume (F '' A₁) ≠ ⊤ :=
    (hA₁c.image_of_continuousOn (hF.cont.mono hA₁sub)).measure_ne_top
  have hA₂lt : volume (F '' A₂) ≠ ⊤ :=
    (hA₂c.image_of_continuousOn (hF.holo.continuousOn.mono hA₂sub)).measure_ne_top
  set M : ℝ := (volume (F '' A₁)).toReal + (volume (F '' A₂)).toReal with hMdef
  have hMnonneg : 0 ≤ M := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hMofReal : ENNReal.ofReal M = volume (F '' A₁) + volume (F '' A₂) := by
    rw [hMdef, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hA₁lt, ENNReal.ofReal_toReal hA₂lt]
  have hMbound : ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ)) ≤ ENNReal.ofReal M := by
    intro δ hδ
    calc volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ))
        ≤ volume (F '' A₁) + volume (F '' A₂) := by
          simpa only [hA₁, hA₂, ← hhdef] using volume_image_layer_le_add (F := F) hδ
      _ = ENNReal.ofReal M := hMofReal.symm
  -- the final constant
  set Cfin : ℝ := max (max (C' * CH ^ η') (M * CH ^ η')) (M * h ^ (-(α * η'))) with hCfin
  have hC1 : C' * CH ^ η' ≤ Cfin := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : M * CH ^ η' ≤ Cfin := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3 : M * h ^ (-(α * η')) ≤ Cfin := le_max_right _ _
  have hθpos : 0 < α * η' := mul_pos hα hη'pos
  refine ⟨Cfin, α * η', hθpos, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2
  by_cases hcase : CH * δ ^ α ≤ 1 ∧ δ ≤ h
  · -- small scales: the layer is Hölder controlled and lies in a thickening of `E`
    obtain ⟨hr1, hδh⟩ := hcase
    have hsub := image_layer_subset_thickening hR hα hCHpos hCh'
      (le_trans hδh (le_of_eq hhdef))
    have hD5 := hC' (CH * δ ^ α) ⟨mul_pos hCHpos (Real.rpow_pos_of_pos hδ0 α), hr1⟩
    have hrw : (CH * δ ^ α) ^ η' = CH ^ η' * δ ^ (α * η') := by
      rw [Real.mul_rpow hCHpos.le (Real.rpow_nonneg hδ0.le α), Real.rpow_mul hδ0.le α η']
    calc volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ))
        ≤ volume (thickening (CH * δ ^ α) (F '' realSeg R)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (C' * (CH * δ ^ α) ^ η') := hD5
      _ = ENNReal.ofReal (C' * (CH ^ η' * δ ^ (α * η'))) := by rw [hrw]
      _ ≤ ENNReal.ofReal (Cfin * δ ^ (α * η')) := ENNReal.ofReal_le_ofReal (by
          rw [show C' * (CH ^ η' * δ ^ (α * η')) = (C' * CH ^ η') * δ ^ (α * η') from by ring]
          exact mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg hδ0.le _))
  · -- large scales: the layer image is bounded by the constant `M`
    have hMle : M ≤ Cfin * δ ^ (α * η') := by
      by_cases hδh : δ ≤ h
      · -- `CH δ^α > 1`, so `δ^{αη'} > CH^{-η'}` and `M ≤ (M CH^{η'}) δ^{αη'}`
        have hlt : 1 < CH * δ ^ α := not_le.mp fun hle => hcase ⟨hle, hδh⟩
        have h1 : CH⁻¹ < δ ^ α := by
          rw [inv_eq_one_div]
          exact (div_lt_iff₀ hCHpos).mpr (by rwa [mul_comm] at hlt)
        have h2 : CH⁻¹ ^ η' < (δ ^ α) ^ η' := Real.rpow_lt_rpow (by positivity) h1 hη'pos
        rw [Real.inv_rpow hCHpos.le η', ← Real.rpow_mul hδ0.le α η'] at h2
        have hp : 0 < CH ^ η' := Real.rpow_pos_of_pos hCHpos η'
        have hone : 1 < CH ^ η' * δ ^ (α * η') := by
          calc (1 : ℝ) = CH ^ η' * (CH ^ η')⁻¹ := (mul_inv_cancel₀ hp.ne').symm
            _ < CH ^ η' * δ ^ (α * η') := mul_lt_mul_of_pos_left h2 hp
        calc M ≤ M * (CH ^ η' * δ ^ (α * η')) := le_mul_of_one_le_right hMnonneg hone.le
          _ = (M * CH ^ η') * δ ^ (α * η') := by ring
          _ ≤ Cfin * δ ^ (α * η') :=
              mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hδ0.le _)
      · -- `h < δ`, so `δ^{αη'} ≥ h^{αη'}` and `M ≤ (M h^{-αη'}) δ^{αη'}`
        have hlt : h < δ := not_le.mp hδh
        have h2 : h ^ (α * η') < δ ^ (α * η') := Real.rpow_lt_rpow hh0.le hlt hθpos
        have hone : 1 ≤ h ^ (-(α * η')) * δ ^ (α * η') := by
          calc (1 : ℝ) = h ^ (-(α * η')) * h ^ (α * η') := by
                rw [← Real.rpow_add hh0, neg_add_cancel, Real.rpow_zero]
            _ ≤ h ^ (-(α * η')) * δ ^ (α * η') :=
                mul_le_mul_of_nonneg_left h2.le (Real.rpow_nonneg hh0.le _)
        calc M ≤ M * (h ^ (-(α * η')) * δ ^ (α * η')) := le_mul_of_one_le_right hMnonneg hone
          _ = (M * h ^ (-(α * η'))) * δ ^ (α * η') := by ring
          _ ≤ Cfin * δ ^ (α * η') :=
              mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hδ0.le _)
    calc volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ))
        ≤ ENNReal.ofReal M := hMbound δ hδ
      _ ≤ ENNReal.ofReal (Cfin * δ ^ (α * η')) := ENNReal.ofReal_le_ofReal hMle

end JS

end QuantumZipper
