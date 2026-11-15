/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS1Limit
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Lemma DS1 (uniform inverse-gap occupation)

Packet PROVE-T14-TIP. Specification supplement §12, **Lemma DS1** (`source/spec/p529-576.md` L523–L575,
pp. 551–553):

> Fix `κ > 0`, a finite number of force labels, a time bound `T`, and a uniform bound on the absolute force weights.
> On each side order the nonnegative driver gaps outward as `0 ≤ X₁ ≤ ⋯ ≤ X_m`, `0 ≤ Y₁ ≤ ⋯ ≤ Y_n`. The nearest labels
> include the geometric seed marks; a zero-weight seed label may be inserted when needed. Stop the integrated system
> before a prescribed family of far gaps falls below `g > 0`. On each side all labels before the first such far label
> form its inner block; every uncut label belongs to this block. All labels outward of the first designated far mark
> inherit its lower gap bound by force-coordinate order. Suppose throughout the parameter family that every
> inner-block partial sum satisfies `S_i + 2 ≥ ε > 0` (DS1.1). Suppose also that the cross gap satisfies
> `X₁ + Y₁ ≥ a > 0`. There are `r > 0`, `p ∈ (0, 1)` and `C < ∞`, depending only on these bounds, such that up to the
> stated stop `E ∫₀ᵀ 1{0 < X₁ < δ} dt/X₁ ≤ C δ^{1−p}` (`0 < δ < r`) (DS1.2) […]. Moreover the proof gives a uniform
> regularized bound `E ∫₀ᵀ 1{X₁ < r}(X₁ + ν)^{p−2} dt ≤ C` (`0 < ν < r`) (DS1.3) […]. Integrals here and below are
> stopped integrals; after a stop no artificially frozen zero state is included.

**`ds1`** is this lemma for the nearest **right** gap `X₁ = V^{R,0} − W` of every integrated `SLE_κ(ρ)` evolution
(frozen `IsIntegratedSLEEvolution`, Definition 2.1/2.2):

* *labels*: `n_L` left and `n_R ≥ 1` right labels (the nearest right label is label `0`; a zero-weight seed label is
  allowed), weights bounded by `R` (`|ρ| ≤ R`), the time bound `T`;
* *far block*: the right labels `j ≥ m_R` and the left labels `i ≥ m_L` are the designated far labels (all labels
  outward of the first far label); the stop is `IsAlive`: alive (`t < ζ`) and every far gap at least `g` up to `t`;
* *(DS1.1)*: `S_j + 2 ≥ ε` for every right inner label `j < m_R` (the left inner block does not enter the bound for
  `X₁`; it is the hypothesis of the reflected statement for `Y₁`);
* *cross gap*: `a ≤ x_{R,0} − x_{L,i}` for every left label, at time `0`. The cross gap `V^{R,0} − V^{L,i}` is
  nondecreasing, so this is the source's `X₁ + Y₁ ≥ a` (for every left label);
* *conclusion*: there are `r > 0`, `p ∈ (0, 1)`, `C` depending only on `κ, n_L, n_R, T, R, ε, a, g` such that for every
  such evolution and every choice of far blocks, (DS1.2) and (DS1.3) hold as stopped integrals over the alive times.

**`ds1_left`** is the source's "and the same holds with `Y₁` in place of `X₁`" (`Y₁ = W − V^{L,0}`), by the reflection
`x ↦ −x` (`IsIntegratedSLEEvolution.reflect`), with the left inner block (DS1.1) and the cross gap
`a ≤ x_{R,j} − x_{L,0}`.

## Proof (source's, with the following explicit choices)

`f_ν(x) = ((x + ν)^p − ν^p) φ(x)` with `φ(x) = smoothTransition(2 − x/r)` (`DS1Fun.lean`); `1 − p = min(1/2, ε/κ)`,
`r = min(a/8, g/4, ε/(8(C₀ + 1)))` with `C₀ = n_R R/g + n_L R·4/(3a)`. Itô's formula for `f_ν(X₁)` localized at
`σ_n` (`DS1Loc.lean`), the drift bounds (`DS1Drift.lean`, `DS1Level.lean`: (DS1.4) by Abel summation), the martingale
identity at the bounded time (`DS1Est.lean`), and Fatou's lemma for `ν ↓ 0` and `n → ∞` (`DS1Limit.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DS1

open Supp8.GB5

/-- A pointwise bound `φ ≤ c ψ` passes to the level integrals. -/
theorem levelInt_le_const_mul {Ω : Type*} {φ ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤) (hle : ∀ x, φ x ≤ c * ψ x)
    (σ : Ω → ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) :
    levelInt φ σ X t ω ≤ c * levelInt ψ σ X t ω := by
  unfold levelInt
  rw [← lintegral_const_mul' _ _ hc]
  refine lintegral_mono fun s => ?_
  by_cases hs : s ≤ σ ω
  · rw [Set.indicator_of_mem (show s ∈ {s : ℝ | s ≤ σ ω} from hs),
      Set.indicator_of_mem (show s ∈ {s : ℝ | s ≤ σ ω} from hs)]
    exact hle _
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ | s ≤ σ ω} from hs)]
    exact bot_le

/-- **Lemma DS1** (uniform inverse-gap occupation), for the nearest right gap `X₁ = V^{R,0} − W`: (DS1.2) and
(DS1.3) as stopped integrals, with constants depending only on `κ`, the label counts, `T`, the weight bound `R`,
`ε`, `a` and `g`. -/
theorem ds1 (κ : ℝ) (hκ : 0 < κ) (nL nR : ℕ) (hnR : 0 < nR) (T : ℝ≥0) {Rw ε a g : ℝ} (hR : 0 ≤ Rw)
    (hε : 0 < ε) (ha : 0 < a) (hg : 0 < g) :
    ∃ r : ℝ, 0 < r ∧ ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∃ C : ℝ,
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
        {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
        {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (mL mR : ℕ),
        IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        (∀ i, |ρL i| ≤ Rw) → (∀ j, |ρR j| ≤ Rw) →
        (∀ j : Fin nR, (j : ℕ) < mR → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2) →
        (∀ i : Fin nL, a ≤ xR ⟨0, hnR⟩ - xL i) →
        (∀ δ : ℝ, 0 < δ → δ < r →
          ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | IsAlive mL mR g W VL VR ζ s.toNNReal ω}.indicator
            (fun s => ENNReal.ofReal ({x : ℝ | 0 < x ∧ x < δ}.indicator (fun x => 1 / x)
              (VR ⟨0, hnR⟩ s.toNNReal ω - W s.toNNReal ω))) s) ∂P ≤
            ENNReal.ofReal (C * δ ^ (1 - p))) ∧
        (∀ ν : ℝ, 0 < ν → ν < r →
          ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | IsAlive mL mR g W VL VR ζ s.toNNReal ω}.indicator
            (fun s => ENNReal.ofReal ({x : ℝ | x < r}.indicator (fun x => (x + ν) ^ (p - 2))
              (VR ⟨0, hnR⟩ s.toNNReal ω - W s.toNNReal ω))) s) ∂P ≤ ENNReal.ofReal C) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_smoothTransition
  set q := min (1 / 2 : ℝ) (ε / κ) with hq
  have hq0 : 0 < q := lt_min (by norm_num) (div_pos hε hκ)
  have hq1 : q ≤ 1 / 2 := min_le_left _ _
  set p := 1 - q with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  have hκp : κ * (1 - p) ≤ ε := by
    rw [hpdef, sub_sub_cancel]
    calc κ * q ≤ κ * (ε / κ) := mul_le_mul_of_nonneg_left (min_le_right _ _) hκ.le
      _ = ε := by field_simp
  set C₀ := cst0 nL nR Rw g a with hC₀
  have hC₀0 : 0 ≤ C₀ := cst0_nonneg hR hg ha
  set r := min (min (a / 8) (g / 4)) (ε / (8 * (C₀ + 1))) with hrdef
  have hr : 0 < r := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hr1 : r ≤ min (a / 8) (g / 4) := min_le_left _ _
  have hra : 8 * r ≤ a := by have := hr1.trans (min_le_left (a / 8) (g / 4)); linarith
  have hrg : 2 * r < g := by have := hr1.trans (min_le_right (a / 8) (g / 4)); linarith
  have hrC : 2 * r * C₀ ≤ ε / 4 := by
    have h1 : r ≤ ε / (8 * (C₀ + 1)) := min_le_right _ _
    have h2 : 2 * r * C₀ ≤ 2 * (ε / (8 * (C₀ + 1))) * C₀ :=
      mul_le_mul_of_nonneg_right (by linarith) hC₀0
    have h3 : 2 * (ε / (8 * (C₀ + 1))) * C₀ = ε / 4 * (C₀ / (C₀ + 1)) := by field_simp; ring
    have h4 : C₀ / (C₀ + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have h5 : ε / 4 * (C₀ / (C₀ + 1)) ≤ ε / 4 := by
      have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ ε / 4)
      linarith
    linarith
  set C := ((3 * r) ^ p + cst2 κ p r K nL nR Rw a * T) / (p * ε / 4) with hCdef
  refine ⟨r, hr, p, hp0, hp1, C, ?_⟩
  intro Ω mΩ P 𝓕 xL xR ρL ρR W VL VR B ζ mL mR hE hρL hρR hin hcross
  have hPm : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set i0 : Fin nR := ⟨0, hnR⟩
  -- labels beyond `n_R` are not far labels: work with `m' = min m_R n_R`
  set m' := min mR nR with hm'
  have hm'n : m' ≤ nR := min_le_right _ _
  have hin' : ∀ j : Fin nR, (j : ℕ) < m' → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2 :=
    fun j hj => hin j (lt_of_lt_of_le hj (min_le_left _ _))
  have halive : (fun s ω => IsAlive mL mR g W VL VR ζ s ω) = fun s ω => IsAlive mL m' g W VL VR ζ s ω := by
    have hiff : ∀ j : Fin nR, mR ≤ (j : ℕ) ↔ m' ≤ (j : ℕ) := fun j => by
      rw [hm']; constructor
      · intro h; exact (min_le_left _ _).trans h
      · intro h
        rcases le_total mR nR with h' | h'
        · rwa [min_eq_left h'] at h
        · rw [min_eq_right h'] at h; exact absurd j.2 (not_lt.2 h)
    funext s ω
    simp only [IsAlive, hiff]
  have hal : ∀ s ω, IsAlive mL mR g W VL VR ζ s ω ↔ IsAlive mL m' g W VL VR ζ s ω := fun s ω => by
    rw [show IsAlive mL mR g W VL VR ζ s ω = (fun s ω => IsAlive mL mR g W VL VR ζ s ω) s ω from rfl, halive]
  simp only [hal]
  -- an inadmissible seed has lifetime `0`: nothing is alive
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have hdead : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ¬ IsAlive mL m' g W VL VR ζ s ω := by
      filter_upwards [hE.2.2.2.2] with ω hp s hs
      have hFp := hp.isForcePath
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt bot_le hs.1
      have := hFp.not_threshold h0
      have hw : W 0 ω = 0 := hFp.w_zero
      have hL : (fun i => VL i 0 ω) = xL := funext hFp.vL_zero
      have hR' : (fun i => VR i 0 ω) = xR := funext hFp.vR_zero
      simp only [hw, hL, hR'] at this
      exact this hseed
    have hzero : ∀ φ : ℝ → ℝ≥0∞, ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) T,
        {s : ℝ | IsAlive mL m' g W VL VR ζ s.toNNReal ω}.indicator (fun s => φ (VR i0 s.toNNReal ω -
          W s.toNNReal ω)) s) ∂P = 0 := fun φ => by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hdead] with ω hω
      have : {s : ℝ | IsAlive mL m' g W VL VR ζ s.toNNReal ω} = ∅ :=
        eq_empty_iff_forall_notMem.2 fun s hs => hω _ hs
      simp only [this, indicator_empty, lintegral_zero]
    exact ⟨fun δ _ _ => (hzero fun x => ENNReal.ofReal ({y : ℝ | 0 < y ∧ y < δ}.indicator (fun y => 1 / y) x)).trans_le
      bot_le, fun ν _ _ => (hzero fun x => ENNReal.ofReal ({y : ℝ | y < r}.indicator
        (fun y => (y + ν) ^ (p - 2)) x)).trans_le bot_le⟩
  -- the announcing sequence and the good event
  obtain ⟨Tn, hTann, hTn⟩ := Coupling.exists_isAnnouncingSeq_le hE hκ hseed
  obtain ⟨hT, hTm, hTζ, hTcov⟩ := hTann
  have hae : ∀ᵐ ω ∂P, IsGBGood κ xL xR ρL ρR W VL VR B ζ Tn ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, ae_all_iff.2 hTζ, hTcov]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨G, hGm, hGc, hgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ Tn ω := by
    refine ⟨(toMeasurable P {ω | ¬ IsGBGood κ xL xR ρL ρR W VL VR B ζ Tn ω})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  -- the nearest right label starts to the right of the driver
  have hx0 : 0 ≤ xR i0 := by
    obtain ⟨ω, hω⟩ : G.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, compl_empty, measure_univ] at hGc
      exact one_ne_zero hGc
    have hgω := hgood ω hω
    have hF := hgω.1.isForcePath
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt bot_le (hgω.2.2.2.1 0)
    have := hF.w_le_vR h0 i0
    rwa [hF.w_zero, hF.vR_zero] at this
  -- the regularized bound at every level and every `ν ≤ r`
  have hlev : ∀ n : ℕ, ∀ ν, 0 < ν → ν ≤ r →
      ∫⁻ ω, levelInt (fun x => ENNReal.ofReal (occ p ν r x)) (loc G W VL VR B ζ Tn mL m' n g)
        (gapStop G W VR i0 (xR i0) (loc G W VL VR B ζ Tn mL m' n g)) T ω ∂P ≤ ENNReal.ofReal C :=
    fun n ν hν hνr => lintegral_levelInt_occ_le hE hGm hGc hgood hT hκ hnR hx0 hm'n
      hp0 hp1 hν hνr hr hra hrg hκp hε hrC hR hg ha hρL hρR hin' hcross hK T
  have hmo : ∀ ν, Measurable fun x => ENNReal.ofReal (occ p ν r x) := fun ν =>
    ENNReal.measurable_ofReal.comp (measurable_occ p ν r)
  -- `ν ↓ 0` at every level
  have hlev0 : ∀ n : ℕ, ∫⁻ ω, levelInt (fun x => ENNReal.ofReal (occ0 p r x)) (loc G W VL VR B ζ Tn mL m' n g)
      (gapStop G W VR i0 (xR i0) (loc G W VL VR B ζ Tn mL m' n g)) T ω ∂P ≤ ENNReal.ofReal C := fun n =>
    lintegral_le_of_le_liminf
      (Fs := fun m ω => levelInt (fun x => ENNReal.ofReal (occ p (r / ((m : ℝ) + 2)) r x))
        (loc G W VL VR B ζ Tn mL m' n g) (gapStop G W VR i0 (xR i0) (loc G W VL VR B ζ Tn mL m' n g)) T ω)
      (fun m => measurable_levelInt hE hGm hGc hgood hT _ _ (hmo _) T)
      (Eventually.of_forall fun ω => levelInt_le_liminf (fun m => hmo _) (fun x => occ0_le_liminf x)
        (fun ω => (continuous_gapStop hgood _ _ ω).measurable) T ω)
      (fun m => hlev n _ (by positivity)
        (div_le_self hr.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])))
  refine ⟨fun δ hδ hδr => ?_, fun ν hν hνr => ?_⟩
  · -- (DS1.2)
    have hmδ : Measurable fun x => ENNReal.ofReal ({y : ℝ | 0 < y ∧ y < δ}.indicator (fun y => 1 / y) x) :=
      ENNReal.measurable_ofReal.comp ((measurable_const.div measurable_id).indicator
        ((measurableSet_lt measurable_const measurable_id).inter
          (measurableSet_lt measurable_id measurable_const)))
    refine lintegral_alive_le hE hGm hGc hgood hT hTm hnR hmδ T fun n => ?_
    calc ∫⁻ ω, levelInt (fun x => ENNReal.ofReal ({y : ℝ | 0 < y ∧ y < δ}.indicator (fun y => 1 / y) x))
          (loc G W VL VR B ζ Tn mL m' n g) (gapStop G W VR i0 (xR i0) (loc G W VL VR B ζ Tn mL m' n g)) T ω ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (δ ^ (1 - p)) * levelInt (fun x => ENNReal.ofReal (occ0 p r x))
          (loc G W VL VR B ζ Tn mL m' n g) (gapStop G W VR i0 (xR i0) (loc G W VL VR B ζ Tn mL m' n g)) T ω ∂P :=
          lintegral_mono fun ω => levelInt_le_const_mul ENNReal.ofReal_ne_top (fun x => by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
            exact ENNReal.ofReal_le_ofReal (inv_le_rpow_mul hp1 hδ.le hδr.le x)) _ _ _ ω
      _ = ENNReal.ofReal (δ ^ (1 - p)) * ∫⁻ ω, levelInt (fun x => ENNReal.ofReal (occ0 p r x))
          (loc G W VL VR B ζ Tn mL m' n g) (gapStop G W VR i0 (xR i0) (loc G W VL VR B ζ Tn mL m' n g)) T ω ∂P :=
          lintegral_const_mul _ (measurable_levelInt hE hGm hGc hgood hT _ _
            (ENNReal.measurable_ofReal.comp (measurable_occ0 p r)) T)
      _ ≤ ENNReal.ofReal (δ ^ (1 - p)) * ENNReal.ofReal C := by gcongr; exact hlev0 n
      _ = ENNReal.ofReal (C * δ ^ (1 - p)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), mul_comm]
  · -- (DS1.3)
    exact lintegral_alive_le hE hGm hGc hgood hT hTm hnR (hmo ν) T fun n => hlev n ν hν hνr.le

theorem isAlive_reflect {Ω : Type*} {nL nR : ℕ} (mL mR : ℕ) (g : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (ω : Ω) :
    IsAlive mR mL g (-W) (fun i => -VR i) (fun j => -VL j) ζ s ω ↔ IsAlive mL mR g W VL VR ζ s ω := by
  simp only [IsAlive, Pi.neg_apply, neg_sub_neg]
  refine and_congr_right fun _ => forall_congr' fun u => forall_congr' fun _ => and_comm

/-- **Lemma DS1 for the nearest left gap** `Y₁ = W − V^{L,0}` ("the same holds with `Y₁` in place of `X₁`"): the
reflection of `ds1`, with the left inner block (DS1.1) and the cross gap `a ≤ x_{R,j} − x_{L,0}`. -/
theorem ds1_left (κ : ℝ) (hκ : 0 < κ) (nL nR : ℕ) (hnL : 0 < nL) (T : ℝ≥0) {Rw ε a g : ℝ} (hR : 0 ≤ Rw)
    (hε : 0 < ε) (ha : 0 < a) (hg : 0 < g) :
    ∃ r : ℝ, 0 < r ∧ ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∃ C : ℝ,
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
        {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
        {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (mL mR : ℕ),
        IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        (∀ i, |ρL i| ≤ Rw) → (∀ j, |ρR j| ≤ Rw) →
        (∀ i : Fin nL, (i : ℕ) < mL → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l + 2) →
        (∀ j : Fin nR, a ≤ xR j - xL ⟨0, hnL⟩) →
        (∀ δ : ℝ, 0 < δ → δ < r →
          ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | IsAlive mL mR g W VL VR ζ s.toNNReal ω}.indicator
            (fun s => ENNReal.ofReal ({x : ℝ | 0 < x ∧ x < δ}.indicator (fun x => 1 / x)
              (W s.toNNReal ω - VL ⟨0, hnL⟩ s.toNNReal ω))) s) ∂P ≤
            ENNReal.ofReal (C * δ ^ (1 - p))) ∧
        (∀ ν : ℝ, 0 < ν → ν < r →
          ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | IsAlive mL mR g W VL VR ζ s.toNNReal ω}.indicator
            (fun s => ENNReal.ofReal ({x : ℝ | x < r}.indicator (fun x => (x + ν) ^ (p - 2))
              (W s.toNNReal ω - VL ⟨0, hnL⟩ s.toNNReal ω))) s) ∂P ≤ ENNReal.ofReal C) := by
  obtain ⟨r, hr, p, hp0, hp1, C, h⟩ := ds1 κ hκ nR nL hnL T hR hε ha hg
  refine ⟨r, hr, p, hp0, hp1, C, ?_⟩
  intro Ω mΩ P 𝓕 xL xR ρL ρR W VL VR B ζ mL mR hE hρL hρR hin hcross
  have h' := h (mL := mR) (mR := mL) (hE.reflect) hρR hρL hin
    (fun j => by simp only [Pi.neg_apply, sub_neg_eq_add]; linarith [hcross j])
  have hgap : ∀ (s : ℝ) (ω : Ω), (fun j => -VL j) ⟨0, hnL⟩ s.toNNReal ω - (-W) s.toNNReal ω =
      W s.toNNReal ω - VL ⟨0, hnL⟩ s.toNNReal ω := fun s ω => by simp only [Pi.neg_apply]; ring
  simp only [hgap, isAlive_reflect] at h'
  exact h'

end DS1

end Supp12

end InteractingSLE
