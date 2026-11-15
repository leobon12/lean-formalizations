/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsHorizon
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Aux. lemma 108, driver form: the whole-history energy of a neutral change of weights

Packet PROVE-T14-TIP2. Specification §7.3, **Aux. lemma 108** (`source/spec/p337-384.md` L443–L503, pp. 357–359),
(HBT3): "`∫₀ᵗ a_s² ds = ‖f‖²_∇ − G_{ℍ∖K_t}(v, v) ≤ ‖f‖²_∇`" — the energy of the drift change is bounded **uniformly
in the horizon**, which is what makes the density martingale uniformly integrable and the comparison valid "on the
entire stopped history, including the event of an infinite stopping time". In GB8 (p. 523) the two words have the
same far heights ("their far heights agree exactly"), i.e. the same **side totals**.

In driver form the drift change of the weights `ρ → ρ'` is `Σ_k c_k/(W − V_k)` with charges `c_k = ρ'_k − ρ_k`, and
equal side totals make the charges of each side **neutral** (`Σ_k c_k = 0`). This file proves that, as long as every
gap stays at least `δ > 0`, the energy of a neutral change is bounded by a constant that does **not** depend on the
horizon (`changeEnergy_le_neutralBound`):

* for one side with gaps `X_i = w − v_i ≥ δ` and any anchor `k`, neutrality gives
  `Σ c_i/X_i = Σ c_i (1/X_i − 1/X_k)` and `|1/X_i − 1/X_k| = |v_k − v_i|/(X_k X_i) ≤ 1/δ`;
* the spread of two marks of one side obeys `d(v_k − v_i) = −2 (v_k − v_i)/(X_k X_i) dt` (both follow the Loewner
  flow), so `∫₀ᵀ |v_k − v_i|/(X_k X_i) ≤ |x_k − x_i|/2` for every `T` (`integral_pair_le`): the spread is monotone;
* hence `∫₀ᵀ (Σ c_i/X_i)² ≤ (Σ|c|/δ) Σ_i |c_i| |x_k − x_i|/2` (`integral_sideSum_sq_le`), and the right side by
  reflection.

No Green function and no field are used; this is the driver-form replacement of (HBT3) for the comparisons used in
GB8 (see `Aux108Inf.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace Aux108Inf

/-! ### The bound of one side -/

section Bound

variable {n : ℕ}

/-- The energy bound of one side: `(Σ|c|) · Σ_k Σ_i |c_i| |x_k − x_i|`. -/
def sideBound (c x : Fin n → ℝ) : ℝ :=
  (∑ i, |c i|) * ∑ k, ∑ i, |c i| * |x k - x i|

theorem sideBound_nonneg (c x : Fin n → ℝ) : 0 ≤ sideBound c x := by
  unfold sideBound
  exact mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- One anchor's sum is at most the sum over all anchors. -/
theorem sum_abs_mul_le (c x : Fin n → ℝ) (k : Fin n) :
    ∑ i, |c i| * |x k - x i| ≤ ∑ k', ∑ i, |c i| * |x k' - x i| :=
  single_le_sum (f := fun k' => ∑ i, |c i| * |x k' - x i|)
    (fun _ _ => sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mem_univ k)

end Bound

/-! ### Pointwise algebra -/

section Algebra

variable {n : ℕ}

/-- The drift difference of two marks of one side: `2/(v_k − w) − 2/(v_i − w) = −2 (v_k − v_i)/((w − v_k)(w − v_i))`. -/
theorem two_div_sub_two_div {w vk vi : ℝ} (hk : w - vk ≠ 0) (hi : w - vi ≠ 0) :
    2 / (vk - w) - 2 / (vi - w) = -2 * ((vk - vi) / ((w - vk) * (w - vi))) := by
  have hk' : vk - w ≠ 0 := fun h => hk (by linarith)
  have hi' : vi - w ≠ 0 := fun h => hi (by linarith)
  field_simp
  ring

/-- **Neutral charges** (`Σ c = 0`): `|Σ c_i/X_i| ≤ Σ |c_i| |v_k − v_i|/(X_k X_i)`, with `X_i = w − v_i > 0`. -/
theorem abs_sum_div_le {c v : Fin n → ℝ} {w : ℝ} (hc : ∑ i, c i = 0) (hX : ∀ i, 0 < w - v i) (k : Fin n) :
    |∑ i, c i / (w - v i)| ≤ ∑ i, |c i| * (|v k - v i| / ((w - v k) * (w - v i))) := by
  have e : ∑ i, c i / (w - v i) = ∑ i, c i * (1 / (w - v i) - 1 / (w - v k)) := by
    have h0 : ∑ i, c i * (1 / (w - v k)) = 0 := by rw [← sum_mul, hc, zero_mul]
    rw [← sub_zero (∑ i, c i / (w - v i)), ← h0, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (abs_nonneg _)
  have hk := (hX k).ne'
  have hi := (hX i).ne'
  rw [show 1 / (w - v i) - 1 / (w - v k) = (v i - v k) / ((w - v k) * (w - v i)) by field_simp; ring,
    abs_div, abs_sub_comm (v i) (v k), abs_of_pos (mul_pos (hX k) (hX i))]

/-- The pair term is `|1/X_i − 1/X_k| ≤ 1/δ` when both gaps are at least `δ > 0`. -/
theorem pair_le_inv {vk vi w δ : ℝ} (hδ : 0 < δ) (hk : δ ≤ w - vk) (hi : δ ≤ w - vi) :
    |vk - vi| / ((w - vk) * (w - vi)) ≤ 1 / δ := by
  have hk0 : 0 < w - vk := hδ.trans_le hk
  have hi0 : 0 < w - vi := hδ.trans_le hi
  have e : |vk - vi| / ((w - vk) * (w - vi)) = |1 / (w - vi) - 1 / (w - vk)| := by
    rw [show 1 / (w - vi) - 1 / (w - vk) = (vi - vk) / ((w - vk) * (w - vi)) by
      field_simp; ring, abs_div, abs_sub_comm vi vk, abs_of_pos (mul_pos hk0 hi0)]
  rw [e, abs_sub_le_iff]
  have h1 : 1 / (w - vi) ≤ 1 / δ := one_div_le_one_div_of_le hδ hi
  have h2 : 1 / (w - vk) ≤ 1 / δ := one_div_le_one_div_of_le hδ hk
  have h3 : 0 < 1 / (w - vi) := one_div_pos.2 hi0
  have h4 : 0 < 1 / (w - vk) := one_div_pos.2 hk0
  constructor <;> linarith

end Algebra

/-! ### One side on a horizon -/

section Side

variable {n : ℕ} {w : ℝ≥0 → ℝ} {v : Fin n → ℝ≥0 → ℝ} {x : Fin n → ℝ} {T : ℝ≥0} {δ : ℝ}

theorem toNNReal_le_of_mem_uIcc {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) T) : s.toNNReal ≤ T := by
  rw [uIcc_of_le (NNReal.coe_nonneg T)] at hs
  exact Real.toNNReal_le_iff_le_coe.2 hs.2

variable (hw : ContinuousOn (fun s : ℝ => w s.toNNReal) (uIcc 0 T))
  (hv : ∀ i, ContinuousOn (fun s : ℝ => v i s.toNNReal) (uIcc 0 T))
  (hgap : ∀ s ≤ T, ∀ i, δ ≤ w s - v i s) (hδ : 0 < δ)

include hgap hδ in
theorem gap_pos {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) T) (i : Fin n) : 0 < w s.toNNReal - v i s.toNNReal :=
  hδ.trans_le (hgap _ (toNNReal_le_of_mem_uIcc hs) i)

/-- The pair term `|v_k − v_i|/((w − v_k)(w − v_i))` along the path. -/
def pairAt (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) (k i : Fin n) (s : ℝ) : ℝ :=
  |v k s.toNNReal - v i s.toNNReal| / ((w s.toNNReal - v k s.toNNReal) * (w s.toNNReal - v i s.toNNReal))

include hw hv hgap hδ in
theorem continuousOn_pairAt (k i : Fin n) : ContinuousOn (pairAt w v k i) (uIcc 0 T) :=
  (continuous_abs.comp_continuousOn ((hv k).sub (hv i))).div ((hw.sub (hv k)).mul (hw.sub (hv i)))
    fun _ hs => (mul_pos (gap_pos hgap hδ hs k) (gap_pos hgap hδ hs i)).ne'

include hw hv hgap hδ in
theorem continuousOn_sideSum (c : Fin n → ℝ) :
    ContinuousOn (fun s : ℝ => ∑ i, c i / (w s.toNNReal - v i s.toNNReal)) (uIcc 0 T) :=
  continuousOn_finsetSum _ fun i _ => continuousOn_const.div (hw.sub (hv i))
    fun _ hs => (gap_pos hgap hδ hs i).ne'

include hw hv hgap hδ in
/-- **The spread identity**: `∫₀ᵀ (v_k − v_i)/((w − v_k)(w − v_i)) = ((x_k − x_i) − (v_k(T) − v_i(T)))/2`. -/
theorem integral_spread_eq (heq : ∀ i, v i T = x i + ∫ s in (0 : ℝ)..T, 2 / (v i s.toNNReal - w s.toNNReal))
    (k i : Fin n) :
    ∫ s in (0 : ℝ)..T, (v k s.toNNReal - v i s.toNNReal) /
        ((w s.toNNReal - v k s.toNNReal) * (w s.toNNReal - v i s.toNNReal)) =
      ((x k - x i) - (v k T - v i T)) / 2 := by
  have hint : ∀ j, IntervalIntegrable (fun s : ℝ => 2 / (v j s.toNNReal - w s.toNNReal)) volume 0 T := fun j =>
    ContinuousOn.intervalIntegrable (continuousOn_const.div ((hv j).sub hw) fun _ hs => by
      have := gap_pos hgap hδ hs j
      exact (show v j _ - w _ < 0 by linarith).ne)
  have hc : ∫ s in (0 : ℝ)..T, (2 / (v k s.toNNReal - w s.toNNReal) - 2 / (v i s.toNNReal - w s.toNNReal)) =
      ∫ s in (0 : ℝ)..T, -2 * ((v k s.toNNReal - v i s.toNNReal) /
        ((w s.toNNReal - v k s.toNNReal) * (w s.toNNReal - v i s.toNNReal))) :=
    intervalIntegral.integral_congr fun _ hs =>
      two_div_sub_two_div (gap_pos hgap hδ hs k).ne' (gap_pos hgap hδ hs i).ne'
  rw [intervalIntegral.integral_sub (hint k) (hint i), intervalIntegral.integral_const_mul] at hc
  have h1 := heq k
  have h2 := heq i
  linarith

include hw hv hgap hδ in
/-- **The spread bound**: `∫₀ᵀ |v_k − v_i|/((w − v_k)(w − v_i)) ≤ |x_k − x_i|/2` for every horizon, when the side is
ordered. -/
theorem integral_pairAt_le (heq : ∀ i, v i T = x i + ∫ s in (0 : ℝ)..T, 2 / (v i s.toNNReal - w s.toNNReal))
    (hanti : ∀ s ≤ T, Antitone fun i => v i s) (k i : Fin n) :
    ∫ s in (0 : ℝ)..T, pairAt w v k i s ≤ |x k - x i| / 2 := by
  wlog hki : k ≤ i generalizing k i with H
  · have e : (fun s => pairAt w v k i s) = fun s => pairAt w v i k s := funext fun s => by
      unfold pairAt; rw [abs_sub_comm, mul_comm]
    rw [e, abs_sub_comm]
    exact H i k (le_of_not_ge hki)
  have e : ∫ s in (0 : ℝ)..T, pairAt w v k i s = ∫ s in (0 : ℝ)..T, (v k s.toNNReal - v i s.toNNReal) /
      ((w s.toNNReal - v k s.toNNReal) * (w s.toNNReal - v i s.toNNReal)) :=
    intervalIntegral.integral_congr fun s hs => by
      unfold pairAt
      rw [abs_of_nonneg (sub_nonneg.2 (hanti _ (toNNReal_le_of_mem_uIcc hs) hki))]
  rw [e, integral_spread_eq hw hv hgap hδ heq k i]
  have hT : 0 ≤ v k T - v i T := sub_nonneg.2 (hanti T le_rfl hki)
  have hx : x k - x i ≤ |x k - x i| := le_abs_self _
  linarith

include hw hv hgap hδ in
/-- **The energy of one neutral side on `[0, T]`**: `∫₀ᵀ (Σ c_i/(w − v_i))² ≤ sideBound c x/(2δ)`, uniformly in `T`. -/
theorem integral_sideSum_sq_le (heq : ∀ i, v i T = x i + ∫ s in (0 : ℝ)..T, 2 / (v i s.toNNReal - w s.toNNReal))
    (hanti : ∀ s ≤ T, Antitone fun i => v i s) {c : Fin n → ℝ} (hc : ∑ i, c i = 0) :
    ∫ s in (0 : ℝ)..T, (∑ i, c i / (w s.toNNReal - v i s.toNNReal)) ^ 2 ≤ sideBound c x / (2 * δ) := by
  have hb : 0 ≤ sideBound c x / (2 * δ) := div_nonneg (sideBound_nonneg c x) (by positivity)
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨k⟩⟩
  · simp only [univ_eq_empty, sum_empty]
    norm_num
    exact hb
  set C := (∑ i, |c i|) / δ with hC
  have hC0 : 0 ≤ C := div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) hδ.le
  have hpt : ∀ s ∈ Icc (0 : ℝ) T, (∑ i, c i / (w s.toNNReal - v i s.toNNReal)) ^ 2 ≤
      (∑ i, |c i| * pairAt w v k i s) * C := by
    intro s hs
    have hs' : s ∈ uIcc (0 : ℝ) T := by rwa [uIcc_of_le (NNReal.coe_nonneg T)]
    have hA := abs_sum_div_le (w := w s.toNNReal) (v := fun i => v i s.toNNReal) hc
      (fun i => gap_pos hgap hδ hs' i) k
    have hAC : ∑ i, |c i| * pairAt w v k i s ≤ C := by
      rw [hC, div_eq_mul_one_div, sum_mul]
      refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact pair_le_inv hδ (hgap _ (toNNReal_le_of_mem_uIcc hs') k) (hgap _ (toNNReal_le_of_mem_uIcc hs') i)
    have hL := hA
    rw [← sq_abs]
    calc |∑ i, c i / (w s.toNNReal - v i s.toNNReal)| ^ 2
        = |∑ i, c i / (w s.toNNReal - v i s.toNNReal)| * |∑ i, c i / (w s.toNNReal - v i s.toNNReal)| := sq _
      _ ≤ (∑ i, |c i| * pairAt w v k i s) * C :=
          mul_le_mul hL (hL.trans hAC) (abs_nonneg _) ((abs_nonneg _).trans hL)
  have hint1 : IntervalIntegrable (fun s : ℝ => (∑ i, c i / (w s.toNNReal - v i s.toNNReal)) ^ 2) volume 0 T :=
    ((continuousOn_sideSum hw hv hgap hδ c).pow 2).intervalIntegrable
  have hint2 : ∀ i, IntervalIntegrable (fun s => |c i| * pairAt w v k i s) volume 0 T := fun i =>
    ((continuousOn_pairAt hw hv hgap hδ k i).const_smul |c i|).intervalIntegrable
  have hint3 : IntervalIntegrable (fun s => (∑ i, |c i| * pairAt w v k i s) * C) volume 0 T :=
    ((continuousOn_finsetSum _ fun i _ => (continuousOn_pairAt hw hv hgap hδ k i).const_smul |c i|).mul
      continuousOn_const).intervalIntegrable
  calc ∫ s in (0 : ℝ)..T, (∑ i, c i / (w s.toNNReal - v i s.toNNReal)) ^ 2
      ≤ ∫ s in (0 : ℝ)..T, (∑ i, |c i| * pairAt w v k i s) * C :=
        intervalIntegral.integral_mono_on (NNReal.coe_nonneg T) hint1 hint3 hpt
    _ = (∑ i, |c i| * ∫ s in (0 : ℝ)..T, pairAt w v k i s) * C := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_finsetSum fun i _ => hint2 i]
        simp only [intervalIntegral.integral_const_mul]
    _ ≤ (∑ i, |c i| * (|x k - x i| / 2)) * C := by
        refine mul_le_mul_of_nonneg_right (sum_le_sum fun i _ => ?_) hC0
        exact mul_le_mul_of_nonneg_left (integral_pairAt_le hw hv hgap hδ heq hanti k i) (abs_nonneg _)
    _ = (∑ i, |c i| * |x k - x i|) * C / 2 := by
        rw [sum_mul, sum_mul, sum_div]
        exact sum_congr rfl fun i _ => by ring
    _ ≤ (∑ k', ∑ i, |c i| * |x k' - x i|) * C / 2 := by
        have := sum_abs_mul_le c x k
        have h2 : (∑ i, |c i| * |x k - x i|) * C ≤ (∑ k', ∑ i, |c i| * |x k' - x i|) * C :=
          mul_le_mul_of_nonneg_right this hC0
        linarith
    _ = sideBound c x / (2 * δ) := by
        rw [sideBound, hC]
        field_simp

end Side

/-! ### Both sides along an integrated path -/

section Path

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The horizon-free energy bound** of a neutral change of weights with charges `cL`, `cR` at gap level `δ`. -/
def neutralBound (κ δ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (cL : Fin nL → ℝ) (cR : Fin nR → ℝ) : ℝ :=
  1 / κ * ((sideBound cL xL + sideBound cR xR) / δ)

theorem sideBound_neg (c x : Fin nR → ℝ) : sideBound c (fun j => -x j) = sideBound c x := by
  unfold sideBound
  congr 1
  refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
  rw [show -x k - -x i = -(x k - x i) by ring, abs_neg]

/-- **Aux. lemma 108, (HBT3) in driver form, for a neutral change of weights.** Along an integrated path, if the
side totals of the new weights agree with the old ones and every gap stays at least `δ > 0` on `[0, T]`, `T < ζ`,
then the energy `κ⁻¹ ∫₀ᵀ (Σ (ρ' − ρ)/(W − V))²` of the change is at most `neutralBound`, **independently of `T`**. -/
theorem changeEnergy_le_neutralBound {κ : ℝ} (hκ : 0 < κ) {ρL' : Fin nL → ℝ} {ρR' : Fin nR → ℝ}
    (hL : ∑ i, ρL' i = ∑ i, ρL i) (hR : ∑ j, ρR' j = ∑ j, ρR j) {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : ℝ≥0∞} {ω : Ω}
    (hp : Sec2.IsForcePath xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) ζ)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ s ≤ T, δ ≤ Zhan.minGap (Coupling.stateAt W VL VR s ω)) :
    Zhan.changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤
      neutralBound κ δ xL xR (fun i => ρL' i - ρL i) (fun j => ρR' j - ρR j) := by
  have hlt : ∀ s ≤ T, (s : ℝ≥0∞) < ζ := fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) hT
  have hmaps : MapsTo (fun s : ℝ => s.toNNReal) (uIcc 0 T) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} :=
    fun s hs => hlt _ (toNNReal_le_of_mem_uIcc hs)
  have hwc : ContinuousOn (fun s : ℝ => W s.toNNReal ω) (uIcc 0 T) :=
    hp.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps
  have hvLc : ∀ i, ContinuousOn (fun s : ℝ => VL i s.toNNReal ω) (uIcc 0 T) := fun i =>
    (hp.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn hmaps
  have hvRc : ∀ j, ContinuousOn (fun s : ℝ => VR j s.toNNReal ω) (uIcc 0 T) := fun j =>
    (hp.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps
  have hgL : ∀ s ≤ T, ∀ i, δ ≤ W s ω - VL i s ω := fun s hs i => by
    have h := (Zhan.le_minGap_iff.1 (hgap s hs)).2.1 i
    simp only [Coupling.stateAt] at h
    rwa [abs_of_nonneg (sub_nonneg.2 (hp.vL_le_w (hlt s hs) i))] at h
  have hgR : ∀ s ≤ T, ∀ j, δ ≤ -W s ω - -VR j s ω := fun s hs j => by
    have h := (Zhan.le_minGap_iff.1 (hgap s hs)).2.2 j
    simp only [Coupling.stateAt] at h
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hp.w_le_vR (hlt s hs) j))] at h
    linarith
  -- the left side
  have hcL : ∑ i, (ρL' i - ρL i) = 0 := by rw [sum_sub_distrib, hL, sub_self]
  have hEL := integral_sideSum_sq_le (w := fun t => W t ω) (v := fun i t => VL i t ω) (x := xL) hwc hvLc hgL hδ
    (fun i => hp.vL_eq hT i) (fun s hs => hp.antitone_vL (hlt s hs)) hcL
  -- the right side, by reflection
  have hcR : ∑ j, (ρR' j - ρR j) = 0 := by rw [sum_sub_distrib, hR, sub_self]
  have heqR : ∀ j, -VR j T ω = -xR j + ∫ s in (0 : ℝ)..T, 2 / (-VR j s.toNNReal ω - -W s.toNNReal ω) := by
    intro j
    rw [hp.vR_eq hT j, neg_add, ← intervalIntegral.integral_neg]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show -VR j s.toNNReal ω - -W s.toNNReal ω = -(VR j s.toNNReal ω - W s.toNNReal ω) by ring, div_neg]
  have hER := integral_sideSum_sq_le (w := fun t => -W t ω) (v := fun j t => -VR j t ω) (x := fun j => -xR j)
    hwc.neg (fun j => (hvRc j).neg) hgR hδ heqR
    (fun s hs => fun j j' hjj' => neg_le_neg (hp.monotone_vR (hlt s hs) hjj')) hcR
  rw [sideBound_neg] at hER
  -- the sum over all marks splits into the two sides
  set Lf := fun s : ℝ => ∑ i, (ρL' i - ρL i) / (W s.toNNReal ω - VL i s.toNNReal ω) with hLf
  set Rf := fun s : ℝ => ∑ j, (ρR' j - ρR j) / (-W s.toNNReal ω - -VR j s.toNNReal ω) with hRf
  have hsplit : ∀ s : ℝ, (∑ j, Sec2.weightDiff ρL ρL' ρR ρR' j /
      (W s.toNNReal ω - Girsanov.allMarks VL VR j s.toNNReal ω)) ^ 2 = (Lf s - Rf s) ^ 2 := by
    intro s
    rw [Fin.sum_univ_add]
    simp only [Sec2.weightDiff, Girsanov.allMarks, Fin.addCases_left, Fin.addCases_right, hLf, hRf]
    congr 1
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show -W s.toNNReal ω - -VR j s.toNNReal ω = -(W s.toNNReal ω - VR j s.toNNReal ω) by ring, div_neg,
      neg_neg]
  have hLc : ContinuousOn Lf (uIcc 0 T) := continuousOn_sideSum (w := fun t => W t ω)
    (v := fun i t => VL i t ω) hwc hvLc hgL hδ _
  have hRc : ContinuousOn Rf (uIcc 0 T) := continuousOn_sideSum (w := fun t => -W t ω)
    (v := fun j t => -VR j t ω) hwc.neg (fun j => (hvRc j).neg) hgR hδ _
  have hi1 : IntervalIntegrable (fun s => (Lf s - Rf s) ^ 2) volume 0 T := ((hLc.sub hRc).pow 2).intervalIntegrable
  have hiL : IntervalIntegrable (fun s => Lf s ^ 2) volume 0 T := (hLc.pow 2).intervalIntegrable
  have hiR : IntervalIntegrable (fun s => Rf s ^ 2) volume 0 T := (hRc.pow 2).intervalIntegrable
  have hmain : ∫ s in (0 : ℝ)..T, (Lf s - Rf s) ^ 2 ≤ (sideBound (fun i => ρL' i - ρL i) xL +
      sideBound (fun j => ρR' j - ρR j) xR) / δ := by
    calc ∫ s in (0 : ℝ)..T, (Lf s - Rf s) ^ 2 ≤ ∫ s in (0 : ℝ)..T, (2 * Lf s ^ 2 + 2 * Rf s ^ 2) :=
          intervalIntegral.integral_mono_on (NNReal.coe_nonneg T) hi1 ((hiL.const_mul 2).add (hiR.const_mul 2))
            fun s _ => by nlinarith [sq_nonneg (Lf s + Rf s)]
      _ = 2 * (∫ s in (0 : ℝ)..T, Lf s ^ 2) + 2 * ∫ s in (0 : ℝ)..T, Rf s ^ 2 := by
          rw [intervalIntegral.integral_add (hiL.const_mul 2) (hiR.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ 2 * (sideBound (fun i => ρL' i - ρL i) xL / (2 * δ)) +
            2 * (sideBound (fun j => ρR' j - ρR j) xR / (2 * δ)) := by
          have h1 : ∫ s in (0 : ℝ)..T, Lf s ^ 2 ≤ sideBound (fun i => ρL' i - ρL i) xL / (2 * δ) := hEL
          have h2 : ∫ s in (0 : ℝ)..T, Rf s ^ 2 ≤ sideBound (fun j => ρR' j - ρR j) xR / (2 * δ) := hER
          linarith
      _ = _ := by field_simp
  unfold Zhan.changeEnergy neutralBound
  rw [intervalIntegral.integral_congr fun s _ => hsplit s]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Path

end Aux108Inf

end Supp8

end InteractingSLE
