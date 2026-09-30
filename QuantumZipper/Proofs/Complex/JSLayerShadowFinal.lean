import QuantumZipper.Proofs.Complex.JSLayerTentChain
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# EXT-JS node C1, part 3: layer decay implies a finite shadow sum

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 ("(C1: layer decay LA ⇒ SH.)") and §3 node C1.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2–3 (Proposition 1). With the vertical chain
`ediam_image_tent_le`, the weighted Cauchy–Schwarz `sq_tsum_le_mul_tsum_sq` (weight `Q` with
`1 < Q`, `Q β < 1`, `β = 2^{-η}`) and the layer estimate `volume_image_layer_le`, the shadow sum
is summable:

`shadowSum R F ≤ 64 (1 - Q⁻¹)⁻¹ · B · (1 - β)⁻¹ (1 - Q β)⁻¹ < ⊤`

for any chart `F` with layer decay `LayerDecay R F` — the implication LA ⇒ SH of the blueprint.
-/

noncomputable section

set_option maxHeartbeats 800000

open Set Metric MeasureTheory Complex
open scoped ENNReal

namespace QuantumZipper
namespace JS

/-- Sum/tsum interchange for a finite sum in `ℝ≥0∞`. -/
lemma finset_sum_tsum_swap (s : Finset ℕ) (G : ℕ → ℕ → ℝ≥0∞) :
    ∑ j ∈ s, ∑' k, G j k = ∑' k, ∑ j ∈ s, G j k := by
  have h1 : ∀ j, (∑' k, (if j ∈ s then G j k else 0)) = if j ∈ s then ∑' k, G j k else 0 := by
    intro j
    by_cases hj : j ∈ s
    · rw [if_pos hj]
      exact tsum_congr fun k => if_pos hj
    · rw [if_neg hj]
      simp only [hj, if_false, tsum_zero]
  have h2 : ∀ k, (∑' j, (if j ∈ s then G j k else 0)) = ∑ j ∈ s, G j k := by
    intro k
    rw [tsum_eq_sum (s := s) (fun j hj => if_neg hj)]
    exact Finset.sum_congr rfl fun j hj => if_pos hj
  calc ∑ j ∈ s, ∑' k, G j k
      = ∑ j ∈ s, (if j ∈ s then ∑' k, G j k else 0) :=
        Finset.sum_congr rfl fun j hj => by rw [if_pos hj]
    _ = ∑' j, (if j ∈ s then ∑' k, G j k else 0) :=
        (tsum_eq_sum (s := s) fun j hj => if_neg hj).symm
    _ = ∑' j, ∑' k, (if j ∈ s then G j k else 0) := tsum_congr fun j => (h1 j).symm
    _ = ∑' k, ∑' j, (if j ∈ s then G j k else 0) := ENNReal.tsum_comm
    _ = ∑' k, ∑ j ∈ s, G j k := tsum_congr h2

/-- The descendant partition `sum_range_mul_range` in the form of the handoff. -/
theorem sum_descIdx {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m k : ℕ) :
    ∑ j ∈ Finset.range (2 ^ m), ∑ j' ∈ descIdx j k, g j' =
      ∑ j' ∈ Finset.range (2 ^ (m + k)), g j' := by
  rw [← sum_range_mul_range g m k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [descIdx, Finset.sum_map]
  exact Finset.sum_congr rfl fun t _ => rfl

/-- A1 and the bounded overlap of the enlarged boxes of one level: the sum of the squared image
diameters of a level of top boxes is at most `40` times the area of the layer the enlarged boxes
sit in. -/
lemma sum_topDiam_sq_le_layer {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F) (m k : ℕ) :
    ∑ j ∈ Finset.range (2 ^ m), topDiam R F m j k ^ 2 ≤
      40 * volume (F '' layer R (5 * dyLen R (m + k) / 4)) := by
  have hπ : 2 * ENNReal.ofReal (20 / Real.pi) ≤ (40 : ℝ≥0∞) := by
    have h : (20 : ℝ) / Real.pi ≤ 20 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    calc 2 * ENNReal.ofReal (20 / Real.pi) ≤ 2 * ENNReal.ofReal 20 :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h)
            (by norm_num : (0 : ℝ≥0∞) ≤ 2)
      _ = 40 := by norm_num
  calc ∑ j ∈ Finset.range (2 ^ m), topDiam R F m j k ^ 2
      ≤ ∑ j ∈ Finset.range (2 ^ m), ∑ j' ∈ descIdx j k, ediam (F '' topBox R (m + k) j') ^ 2 :=
        Finset.sum_le_sum fun j _ => topDiam_sq_le_sum R F m j k
    _ = ∑ j' ∈ Finset.range (2 ^ (m + k)), ediam (F '' topBox R (m + k) j') ^ 2 :=
        sum_descIdx (fun j' => ediam (F '' topBox R (m + k) j') ^ 2) m k
    _ ≤ ENNReal.ofReal (20 / Real.pi) *
          ∑ j' ∈ Finset.range (2 ^ (m + k)), volume (F '' bigBox R (m + k) j') := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j' _ => ediam_image_topBox_sq_le hF (m + k) j'
    _ ≤ ENNReal.ofReal (20 / Real.pi) *
          (2 * volume (F '' layerOpen R (5 * dyLen R (m + k) / 4))) :=
        mul_le_mul_of_nonneg_left (sum_volume_image_bigBox_le_layer hF (m + k)) zero_le
    _ = 2 * ENNReal.ofReal (20 / Real.pi) * volume (F '' layerOpen R (5 * dyLen R (m + k) / 4)) :=
        by ring
    _ ≤ 40 * volume (F '' layerOpen R (5 * dyLen R (m + k) / 4)) :=
        mul_le_mul_of_nonneg_right hπ zero_le
    _ ≤ 40 * volume (F '' layer R (5 * dyLen R (m + k) / 4)) :=
        mul_le_mul_of_nonneg_left
          (measure_mono (image_mono (layerOpen_subset_layer _ _))) (by norm_num)

/-- **LA ⇒ SH** (blueprint §2, node C1): for a chart with layer decay, the shadow sum
`Σ_{m,j} diam F(T_{m,j})²` is finite. -/
theorem shadowSum_lt_top_of_layerDecay {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F)
    (hL : LayerDecay R F) : shadowSum R F < ⊤ := by
  obtain ⟨C, η, hC0, hη, hdecay⟩ := hL.exists_nonneg
  have hR := hF.pos
  -- the geometric ratio `β = 2^{-η} ∈ (0,1)` with `2^η β = 1`
  set β : ℝ := (1 / 2 : ℝ) ^ η with hβdef
  have hβ0 : 0 < β := Real.rpow_pos_of_pos (by norm_num) η
  have h2η1 : 1 < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη
  have h2η0 : 0 < (2 : ℝ) ^ η := Real.rpow_pos_of_pos (by norm_num) η
  have h2ηβ : (2 : ℝ) ^ η * β = 1 := by
    rw [hβdef, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  have hβ1 : β < 1 := by nlinarith [h2η1, hβ0, h2ηβ]
  -- the weight `Q ∈ (1, 2^η)`, so that `Q β < 1`
  set q : ℝ := (1 + (2 : ℝ) ^ η) / 2 with hqdef
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hqt : q < (2 : ℝ) ^ η := by rw [hqdef]; linarith
  set Q : ℝ≥0∞ := ENNReal.ofReal q with hQdef
  have hQ1 : 1 < Q := by
    rw [hQdef, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff hq0).2 hq1
  have hQtop : Q ≠ ⊤ := by
    have h : Q < ENNReal.ofReal ((2 : ℝ) ^ η) := by
      rw [hQdef]
      exact (ENNReal.ofReal_lt_ofReal_iff h2η0).2 hqt
    exact ne_of_lt (lt_of_lt_of_le h le_top)
  have hβE : ENNReal.ofReal β < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hβ1
  have hQβ : Q * ENNReal.ofReal β < 1 := by
    have h1 : q * β < 1 := by
      have := mul_lt_mul_of_pos_right hqt hβ0
      rwa [h2ηβ] at this
    rw [hQdef, ← ENNReal.ofReal_mul hq0.le, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 h1
  -- the level from which the layers are short enough
  obtain ⟨N, hN⟩ : ∃ N : ℕ, dyLen R N ≤ 4 / 5 := by
    have hpos : 0 < 4 / 5 / (2 * R + 1) := by positivity
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N, (?_ : dyLen R N < 4 / 5).le⟩
    have h2R : 0 < 2 * R + 1 := by linarith
    calc dyLen R N = 2 * R * (1 / 2 : ℝ) ^ N := dyLen_eq_mul R N
      _ ≤ (2 * R + 1) * (1 / 2 : ℝ) ^ N := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) N]
      _ < (2 * R + 1) * (4 / 5 / (2 * R + 1)) := mul_lt_mul_of_pos_left hN h2R
      _ = 4 / 5 := by field_simp
  -- the whole chart box, and the finiteness of the area of its image
  set box : Set ℂ := Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) with hboxdef
  set M : ℝ≥0∞ := volume (F '' box) with hMdef
  have hMtop : M < ⊤ :=
    ((isCompact_Icc.reProdIm isCompact_Icc).image_of_continuousOn hF.cont).measure_lt_top
  -- the constant absorbing the finitely many levels below the threshold
  set Bc : ℝ := max (40 * (C * (5 / 4) ^ η * (2 * R) ^ η)) (40 * M.toReal / β ^ N) with hBcdef
  have hB0 : (0 : ℝ) ≤ 40 * (C * (5 / 4) ^ η * (2 * R) ^ η) := by
    have h1 : (0 : ℝ) ≤ C * (5 / 4) ^ η * (2 * R) ^ η := by
      have h2 : (0 : ℝ) ≤ (5 / 4 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) η
      have h3 : (0 : ℝ) ≤ (2 * R : ℝ) ^ η := Real.rpow_nonneg (by linarith) η
      have h4 : (0 : ℝ) ≤ C := hC0
      positivity
    linarith
  -- the level bound
  have hlevel : ∀ m k, ∑ j ∈ Finset.range (2 ^ m), topDiam R F m j k ^ 2 ≤
      ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ (m + k) := by
    intro m k
    by_cases hcase : N ≤ m + k
    · have hℓle : 5 * dyLen R (m + k) / 4 ≤ 1 := by
        have h1 : dyLen R (m + k) ≤ dyLen R N := dyLen_le_of_le hR.le hcase
        linarith
      have hconst : (40 : ℝ≥0∞) * ENNReal.ofReal (C * (5 / 4) ^ η * (2 * R) ^ η) ≤
          ENNReal.ofReal Bc := by
        rw [show (40 : ℝ≥0∞) = ENNReal.ofReal 40 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40)]
        exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
      calc ∑ j ∈ Finset.range (2 ^ m), topDiam R F m j k ^ 2
          ≤ 40 * volume (F '' layer R (5 * dyLen R (m + k) / 4)) :=
            sum_topDiam_sq_le_layer hF m k
        _ ≤ 40 * (ENNReal.ofReal (C * (5 / 4) ^ η * (2 * R) ^ η) *
              (ENNReal.ofReal β) ^ (m + k)) :=
            mul_le_mul_of_nonneg_left
              (volume_image_layer_le hC0 hη hdecay hR.le (dyLen_pos hR (m + k)) hℓle)
              (by norm_num)
        _ = 40 * ENNReal.ofReal (C * (5 / 4) ^ η * (2 * R) ^ η) *
              (ENNReal.ofReal β) ^ (m + k) := by ring
        _ ≤ ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ (m + k) :=
            mul_le_mul_of_nonneg_right hconst zero_le
    · push Not at hcase
      have hlayer : layer R (5 * dyLen R (m + k) / 4) ⊆ box := by
        intro w hw
        obtain ⟨hre, him⟩ := mem_reProdIm.1 hw
        have hℓ2 : 5 * dyLen R (m + k) / 4 ≤ 4 * R := by
          have h1 := dyLen_le hR.le (m + k)
          linarith
        rw [hboxdef, mem_reProdIm]
        exact ⟨⟨by linarith [hre.1, hR.le], by linarith [hre.2, hR.le]⟩,
          ⟨by linarith [him.1, hR.le], by linarith [him.2, hℓ2]⟩⟩
      have hβN : (0 : ℝ) < β ^ N := pow_pos hβ0 N
      have hβmk : β ^ N ≤ β ^ (m + k) := pow_le_pow_of_le_one hβ0.le hβ1.le (le_of_lt hcase)
      have hBM : 40 * M.toReal / β ^ N ≤ Bc := le_max_right _ _
      have hstep : (40 : ℝ≥0∞) * M ≤ ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ (m + k) := by
        calc (40 : ℝ≥0∞) * M
            = ENNReal.ofReal 40 * M := by
              rw [show (40 : ℝ≥0∞) = ENNReal.ofReal 40 by norm_num]
          _ = ENNReal.ofReal 40 * ENNReal.ofReal M.toReal := by
              rw [ENNReal.ofReal_toReal hMtop.ne]
          _ = ENNReal.ofReal (40 * M.toReal) :=
              (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40)).symm
          _ = ENNReal.ofReal ((40 * M.toReal / β ^ N) * β ^ N) := by
              rw [div_mul_cancel₀ _ hβN.ne']
          _ = ENNReal.ofReal (40 * M.toReal / β ^ N) * ENNReal.ofReal (β ^ N) :=
              ENNReal.ofReal_mul (by positivity)
          _ ≤ ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ (m + k) := by
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal hBM) ?_
              calc ENNReal.ofReal (β ^ N) ≤ ENNReal.ofReal (β ^ (m + k)) :=
                    ENNReal.ofReal_le_ofReal hβmk
                _ = (ENNReal.ofReal β) ^ (m + k) := ENNReal.ofReal_pow hβ0.le _
      exact (sum_topDiam_sq_le_layer hF m k).trans
        ((mul_le_mul_of_nonneg_left (measure_mono (image_mono hlayer)) (by norm_num)).trans hstep)
  -- the shadow sum, level by level
  have hSm : ∀ m, (∑ j ∈ Finset.range (2 ^ m), ediam (F '' tent R m j) ^ 2) ≤
      64 * (1 - Q⁻¹)⁻¹ * (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m *
        (1 - Q * ENNReal.ofReal β)⁻¹) := by
    intro m
    calc ∑ j ∈ Finset.range (2 ^ m), ediam (F '' tent R m j) ^ 2
        ≤ ∑ j ∈ Finset.range (2 ^ m), (8 * ∑' k, topDiam R F m j k) ^ 2 := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h := ediam_image_tent_le hF (Finset.mem_range.1 hj)
          calc ediam (F '' tent R m j) ^ 2
              = ediam (F '' tent R m j) * ediam (F '' tent R m j) := pow_two _
            _ ≤ (8 * ∑' k, topDiam R F m j k) * (8 * ∑' k, topDiam R F m j k) :=
                mul_le_mul' h h
            _ = (8 * ∑' k, topDiam R F m j k) ^ 2 := (pow_two _).symm
      _ = 64 * ∑ j ∈ Finset.range (2 ^ m), (∑' k, topDiam R F m j k) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 64 * ∑ j ∈ Finset.range (2 ^ m),
            ((1 - Q⁻¹)⁻¹ * ∑' k, Q ^ k * topDiam R F m j k ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by norm_num)
          exact (sq_tsum_le_mul_tsum_sq hQ1 hQtop (fun k => topDiam R F m j k)).trans
            (le_of_eq (mul_comm _ _))
      _ = 64 * (1 - Q⁻¹)⁻¹ *
            ∑ j ∈ Finset.range (2 ^ m), ∑' k, Q ^ k * topDiam R F m j k ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          ring
      _ = 64 * (1 - Q⁻¹)⁻¹ *
            ∑' k, ∑ j ∈ Finset.range (2 ^ m), Q ^ k * topDiam R F m j k ^ 2 := by
          rw [finset_sum_tsum_swap]
      _ = 64 * (1 - Q⁻¹)⁻¹ *
            ∑' k, Q ^ k * (∑ j ∈ Finset.range (2 ^ m), topDiam R F m j k ^ 2) := by
          congr 1
          refine tsum_congr fun k => ?_
          rw [Finset.mul_sum]
      _ ≤ 64 * (1 - Q⁻¹)⁻¹ *
            ∑' k, Q ^ k * (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ (m + k)) := by
          refine mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun k => ?_) zero_le
          exact mul_le_mul_of_nonneg_left (hlevel m k) zero_le
      _ = 64 * (1 - Q⁻¹)⁻¹ * (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m *
            (1 - Q * ENNReal.ofReal β)⁻¹) := by
          congr 1
          calc ∑' k, Q ^ k * (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ (m + k))
              = ∑' k, (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m) *
                  (Q * ENNReal.ofReal β) ^ k := by
                refine tsum_congr fun k => ?_
                rw [pow_add, mul_pow]
                ring
            _ = (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m) *
                  ∑' k, (Q * ENNReal.ofReal β) ^ k := ENNReal.tsum_mul_left
            _ = (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m) *
                  (1 - Q * ENNReal.ofReal β)⁻¹ := by rw [ENNReal.tsum_geometric]
  -- every factor of the bound is finite
  have hQinv : Q⁻¹ < 1 := by
    have h : Q⁻¹ < (1 : ℝ≥0∞)⁻¹ := ENNReal.inv_lt_inv.2 hQ1
    rwa [inv_one] at h
  have hCQtop : (1 - Q⁻¹)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 fun h0 => not_le.2 hQinv (tsub_eq_zero_iff_le.1 h0)
  have hβitop : (1 - ENNReal.ofReal β)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 fun h0 => not_le.2 hβE (tsub_eq_zero_iff_le.1 h0)
  have hQβitop : (1 - Q * ENNReal.ofReal β)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 fun h0 => not_le.2 hQβ (tsub_eq_zero_iff_le.1 h0)
  have hfin : 64 * (1 - Q⁻¹)⁻¹ * (ENNReal.ofReal Bc * (1 - ENNReal.ofReal β)⁻¹ *
      (1 - Q * ENNReal.ofReal β)⁻¹) < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hCQtop)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hβitop) hQβitop)
  calc shadowSum R F
      = ∑' m, ∑ j ∈ Finset.range (2 ^ m), ediam (F '' tent R m j) ^ 2 := rfl
    _ ≤ ∑' m, 64 * (1 - Q⁻¹)⁻¹ * (ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m *
          (1 - Q * ENNReal.ofReal β)⁻¹) := ENNReal.tsum_le_tsum hSm
    _ = 64 * (1 - Q⁻¹)⁻¹ * (∑' m, ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m *
          (1 - Q * ENNReal.ofReal β)⁻¹) := by
        rw [ENNReal.tsum_mul_left]
    _ = 64 * (1 - Q⁻¹)⁻¹ * (ENNReal.ofReal Bc * (1 - ENNReal.ofReal β)⁻¹ *
          (1 - Q * ENNReal.ofReal β)⁻¹) := by
        congr 1
        calc ∑' m, ENNReal.ofReal Bc * (ENNReal.ofReal β) ^ m * (1 - Q * ENNReal.ofReal β)⁻¹
            = ∑' m, (ENNReal.ofReal Bc * (1 - Q * ENNReal.ofReal β)⁻¹) *
                (ENNReal.ofReal β) ^ m := by
              refine tsum_congr fun m => ?_
              ring
          _ = ENNReal.ofReal Bc * (1 - Q * ENNReal.ofReal β)⁻¹ *
                ∑' m, (ENNReal.ofReal β) ^ m := ENNReal.tsum_mul_left
          _ = ENNReal.ofReal Bc * (1 - Q * ENNReal.ofReal β)⁻¹ *
                (1 - ENNReal.ofReal β)⁻¹ := by rw [ENNReal.tsum_geometric]
          _ = ENNReal.ofReal Bc * (1 - ENNReal.ofReal β)⁻¹ *
                (1 - Q * ENNReal.ofReal β)⁻¹ := by ring
    _ < ⊤ := hfin

end JS

end QuantumZipper
