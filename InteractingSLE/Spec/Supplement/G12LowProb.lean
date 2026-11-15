/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowMart

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the expectation bound

Packet PROVE-G12C. Along a good path, between the restart time `q` and the stopping time `σ = lowStop`, the Itô
generator of the Lyapunov observable dominates the two-mark budget minus the drift energy density
(`budget_sub_le_itoGen`, from `G12LowObs.budget_le_itoGen_lowObs`: the cut drift `θ` of `G12LowLoc.lean` is the
uncut drift difference over `√κ` while the monitored gaps exceed `δ_n`). Integrating, and using the stopped
martingale of `G12LowMart.lean` between the deterministic times `q` and `n`, the variable

  `Z = (C + 3) − (M_n − M_q)`

is nonnegative, has mean `C + 3`, and dominates `(∫_q^σ β)/(2c₃)` (`budget_le_lowZ`); Markov's inequality gives
`P(Z ≥ K) ≤ (C + 3)/K` (`measureReal_lowZ_ge_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12Low

open G12 (GCoord gDriftLin gDriftLin₀ g12Dens coordG densG gapStopG locG kbG coordAtG densAtG clockAt kcG
  rhoY)
open Supp8.GB5 (IsGBGood)
open GB7a Girsanov

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {k j₀ : Fin nR} {S : ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {q : ℝ≥0} {C n : ℕ}

/-- The drift difference on the concatenated marks is minus the drift difference of the word. -/
theorem sum_refW_sub_actW (w : ℝ) (u : Fin (nL + nR) → ℝ) :
    ∑ j, (refW nL xR ρR k j₀ S j - actW ρL ρR j) / (w - u j) =
      -((∑ i, ρL i / (w - u (Fin.castAdd nR i))) +
        ∑ j, (ρR j - lowRefW xR ρR k j₀ S j) / (w - u (Fin.natAdd nL j))) := by
  rw [Fin.sum_univ_add, neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [refW, actW, Fin.append_left]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [refW, actW, Fin.append_right]
    ring

/-- The two-mark budget along a path (`G12Det.pairBudget` of the inner mark `k` and the target `j₀`). -/
def lowBudget (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (k j₀ : Fin nR) (ω : Ω) (s : ℝ) : ℝ :=
  G12.pairBudget (W · ω) (VR k · ω) (VR j₀ · ω) s

section Pointwise

variable (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω) (hTn : ∀ n ω, T n ω ≤ n)
  (hy : 0 < xR j₀) (hxk : 0 < xR k) (hkj : k ≤ j₀) (hkjx : xR k < xR j₀)

include hgood hTn hy hxk hkj hkjx in
/-- **The pointwise inequality** on `(q, σ)`: `β/(2c₃) − θ² ≤ itoGen(lowObs)`. -/
theorem budget_sub_le_itoGen (hκ : 0 < κ) (hS : S ≤ -2) (hbp : 0 < lowBp κ S (rhoY xR ρR j₀)) {ω : Ω}
    (hω : ω ∈ G) {s : ℝ} (hs : s ∈ Ioo (q : ℝ) (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω)) :
    lowBudget W VR k j₀ ω s / (2 * lowC3 κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))) -
        lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n s.toNNReal ω ^ 2 ≤
      Ito.itoGen (lowObs κ xL xR ρL ρR k j₀ (lowAlpha κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀)))
          (lowY0 (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))))
        (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densG G W VL VR j₀ s ω) := by
  set σ := lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω with hσdef
  have hF := (hgood ω hω).1.isForcePath
  have hs0 : 0 ≤ s := q.coe_nonneg.trans hs.1.le
  set t := s.toNNReal with htdef
  have ht : (t : ℝ) = s := Real.coe_toNNReal _ hs0
  have hqt : q < t := by rw [← NNReal.coe_lt_coe, ht]; exact hs.1
  have htσ : t < σ := by rw [← NNReal.coe_lt_coe, ht]; exact hs.2
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_zeta_of_le hgood (fun ω => lowStop_le_locG ω) hω htσ.le
  have hsep : (t : ℝ≥0∞) < lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω := by
    have h1 := lowStop_le_sep (κ := κ) (ρL := ρL) (xR := xR) (ρR := ρR) (k := k) (j₀ := j₀) (S := S)
      (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (q := q) (C := C) (n := n) ω
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 htσ) h1
  obtain ⟨-, hgap⟩ := lt_of_lt_sepTime (G12.dlt_pos n).le hsep hqt.le
  have hθ := cmpDrift_eq_of_mem (κ := κ) (σ := fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j)
    (τ := lowSep ρL xR ρR k j₀ S G W VL VR ζ q n) (G12.dlt_pos n) (sepTime_le_lifetime (G12.dlt_pos n).le ω)
    (continuousOn_goodLife_W hgood ω)
    (fun j => continuousOn_goodLife_marks hgood j ω) hqt hsep
  have hsq := shiftIntegrand_sq_eq (κ := κ) (ρ := actW ρL ρR) (ρ' := refW nL xR ρR k j₀ S) hκ (G12.dlt_pos n)
    (w := W t ω) (u := fun j => Girsanov.allMarks VL VR j t ω) fun j hj => by
      refine (hgap j ?_).le
      by_contra hn
      simp only [IsMon, not_or, not_not] at hn
      exact hj (by rw [hn.1, hn.2.1, sub_zero])
  rw [sum_refW_sub_actW] at hsq
  simp only [allMarks_castAdd', allMarks_natAdd', neg_sq] at hsq
  have hθ2 : lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n t ω ^ 2 =
      ((∑ i, ρL i / (W t ω - VL i t ω)) + ∑ j, (ρR j - lowRefW xR ρR k j₀ S j) / (W t ω - VR j t ω)) ^ 2 / κ := by
    rw [lowTheta, hθ, hsq]
  rw [hθ2]
  -- the coordinates at `t`
  have hN := G12.w_eq_gDriftLin (j₀ := j₀) (hgood ω hω).1 htζ
  have ho : 0 < VR k t ω - W t ω := (lowDelta_pos hxk).trans_le (lowDelta_le_gap hgood hω htσ.le)
  have hmem := lowKc_subset hxk hkjx (mem_lowKc hgood hTn hy hkj hkjx htσ.le)
  have he : 0 < VR j₀ t ω - VR k t ω := by
    have := hmem.2
    rwa [lowE_coord hω] at this
  have hgrp : ∀ j, xR j = xR j₀ → VR j t ω = VR j₀ t ω := fun j hj => G12.eq_of_forceEq_right hF hj htζ
  have key := budget_le_itoGen_lowObs κ xL xR ρL ρR k j₀ hκ hS hbp (vL := fun i => VL i t ω)
    (vR := fun j => VR j t ω) (T := clockAt (W · ω) (VR j₀ · ω) t) (b := B t ω) (w := W t ω) hN ho he hgrp
  have hcoord : (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) =
      (((fun i => VL i t ω), (fun j => VR j t ω), clockAt (W · ω) (VR j₀ · ω) t), B t ω) := by
    simp only [coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte, coordAtG]
  have hdens : densG G W VL VR j₀ s ω = g12Dens j₀ (W t ω) (fun i => VL i t ω) (fun j => VR j t ω) := by
    simp only [densG, hω, ↓reduceIte, densAtG]
    rfl
  rw [hcoord, hdens]
  refine le_trans (le_of_eq ?_) key
  simp only [lowBudget, G12.pairBudget, G11.budget]
  rfl

end Pointwise

/-! ### The martingale variable `Z` -/

/-- The stopped Lyapunov martingale `M_t = h(Λ_{t∧σ}) − ∫₀^{t∧σ} itoGen`. -/
def lowMart (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k j₀ : Fin nR)
    (S : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (q : ℝ≥0) (C n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  lowObs κ xL xR ρL ρR k j₀ (lowAlpha κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀)))
      (lowY0 (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀)))
      (coordG xL xR G W VL VR j₀ (min t (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) : ℝ≥0),
      Ito.itoGen (lowObs κ xL xR ρL ρR k j₀ (lowAlpha κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀)))
          (lowY0 (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))))
        (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densG G W VL VR j₀ s ω)

/-- **The variable** `Z = (C + 3) − (M_n − M_q)`. -/
def lowZ (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k j₀ : Fin nR)
    (S : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (q : ℝ≥0) (C n : ℕ) (ω : Ω) : ℝ :=
  (C : ℝ) + 3 - (lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n n ω -
    lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n q ω)

section Z

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
  (hTn : ∀ n ω, T n ω ≤ n) (hy : 0 < xR j₀) (hxk : 0 < xR k) (hkj : k ≤ j₀) (hkjx : xR k < xR j₀)

theorem lowMart_eq_of_le {ω : Ω} (hσ : lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω ≤ q)
    (hσn : lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω ≤ n) :
    lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n n ω =
      lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n q ω := by
  simp only [lowMart, min_eq_right hσ, min_eq_right hσn]

include hE hGm hGc hgood hTn hy hxk hkj hkjx in
/-- **`Z` dominates the budget** between `q` and `σ` on a good path. -/
theorem budget_le_lowZ (hκ : 0 < κ) (hS : S ≤ -2) (hbp : 0 < lowBp κ S (rhoY xR ρR j₀)) {ω : Ω}
    (hω : ω ∈ G) (hqσ : q ≤ lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) :
    (∫ s in (q : ℝ)..(lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : ℝ), lowBudget W VR k j₀ ω s) /
        (2 * lowC3 κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))) ≤
      lowZ κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n ω := by
  set σ := lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω with hσdef
  set bm := lowBm κ S
  set bp := lowBp κ S (rhoY xR ρR j₀)
  set c₃ := lowC3 κ bm bp
  have hbm : bm < 0 := by simp only [bm, lowBm]; linarith
  have hc3 : 0 < c₃ := lowC3_pos hκ hbm hbp
  set Fo := lowObs κ xL xR ρL ρR k j₀ (lowAlpha κ bm bp) (lowY0 bm bp)
  set gen : ℝ → ℝ := fun s => Ito.itoGen Fo
    (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG G W VL VR j₀ s ω)
    with hgen
  set θ := lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n
  have hσn : σ ≤ n := lowStop_le_horizon ω
  have hF := (hgood ω hω).1.isForcePath
  -- the generator is integrable
  have hgσ : IntervalIntegrable gen volume 0 σ :=
    intervalIntegrable_itoGen_lowObs hgood hTn hy hxk hkj hkjx hκ.le _ _ hω
  have hsub : uIcc (0 : ℝ) q ⊆ uIcc 0 σ := by
    rw [uIcc_of_le q.coe_nonneg, uIcc_of_le σ.coe_nonneg]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast hqσ)
  have hgq : IntervalIntegrable gen volume 0 q := hgσ.mono_set hsub
  have hgqσ : IntervalIntegrable gen volume q σ := hgq.symm.trans hgσ
  -- the martingale increment
  have hM : lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n n ω -
      lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n q ω =
      (Fo (coordG xL xR G W VL VR j₀ σ ω, Sec2.TwoSeed.brownG G B σ ω) -
        Fo (coordG xL xR G W VL VR j₀ q ω, Sec2.TwoSeed.brownG G B q ω)) - ∫ s in (q : ℝ)..σ, gen s := by
    simp only [lowMart]
    rw [← hσdef, min_eq_right hσn, min_eq_left hqσ, ← intervalIntegral.integral_interval_sub_left hgσ hgq]
    ring
  have hFb : Fo (coordG xL xR G W VL VR j₀ σ ω, Sec2.TwoSeed.brownG G B σ ω) -
      Fo (coordG xL xR G W VL VR j₀ q ω, Sec2.TwoSeed.brownG G B q ω) ≤ 2 := by
    have h1 := abs_le.1 (abs_lowH_le (lowAlpha κ bm bp) (lowY0 bm bp)
      (Real.log (lowO κ xL xR ρL ρR k (coordG xL xR G W VL VR j₀ σ ω, Sec2.TwoSeed.brownG G B σ ω)) -
        Real.log (lowE k j₀ (coordG xL xR G W VL VR j₀ σ ω, Sec2.TwoSeed.brownG G B σ ω))))
    have h2 := abs_le.1 (abs_lowH_le (lowAlpha κ bm bp) (lowY0 bm bp)
      (Real.log (lowO κ xL xR ρL ρR k (coordG xL xR G W VL VR j₀ q ω, Sec2.TwoSeed.brownG G B q ω)) -
        Real.log (lowE k j₀ (coordG xL xR G W VL VR j₀ q ω, Sec2.TwoSeed.brownG G B q ω))))
    simp only [Fo, lowObs]
    linarith [h1.2, h2.1]
  rcases hqσ.lt_or_eq with hlt | heq
  swap
  · -- `q = σ`: everything vanishes
    have : (q : ℝ) = σ := by exact_mod_cast heq
    rw [this, intervalIntegral.integral_same, zero_div]
    simp only [lowZ]
    rw [hM, this, intervalIntegral.integral_same, ← heq, sub_self, sub_zero, sub_zero]
    positivity
  have hσ0 : 0 < σ := lt_of_le_of_lt (zero_le (a := q)) hlt
  have hqσr : (q : ℝ) ≤ σ := by exact_mod_cast hqσ
  -- integrability of the lower bound
  have hθp := isStronglyProgressive_lowTheta (κ := κ) (k := k) (j₀ := j₀) (S := S) (q := q) (n := n)
    hE hGm hGc hgood
  have hθ2i : IntervalIntegrable (fun s : ℝ => θ s.toNNReal ω ^ 2) volume q σ := by
    have hθ2 : IsStronglyProgressive (usualAugmentation 𝓕 P) (fun t ω => θ t ω ^ 2) := fun t => (hθp t).pow 2
    refine intervalIntegrable_time hθ2 (C := cmpBound κ (G12.dlt n)
      (fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j) ^ 2) (fun t ω => ?_) ω q σ
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_lowTheta_le t ω) 2
  have hmaps : MapsTo Real.toNNReal (Icc (q : ℝ) σ) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun r hr =>
    lt_zeta_of_le hgood (fun ω => lowStop_le_locG ω) hω (Sec2.toNNReal_le_of_mem_Icc ⟨q.coe_nonneg.trans hr.1, hr.2⟩)
  have hcw : ContinuousOn (fun s : ℝ => W s.toNNReal ω) (Icc (q : ℝ) σ) :=
    hF.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps
  have hcv : ∀ j, ContinuousOn (fun s : ℝ => VR j s.toNNReal ω) (Icc (q : ℝ) σ) := fun j =>
    (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps
  have hopos : ∀ s ∈ Icc (q : ℝ) σ, 0 < VR k s.toNNReal ω - W s.toNNReal ω := fun s hs =>
    (lowDelta_pos hxk).trans_le (lowDelta_le_gap hgood hω (Sec2.toNNReal_le_of_mem_Icc ⟨q.coe_nonneg.trans hs.1, hs.2⟩))
  have hepos : ∀ s ∈ Icc (q : ℝ) σ, 0 < VR j₀ s.toNNReal ω - VR k s.toNNReal ω := fun s hs => by
    have hm := (lowKc_subset hxk hkjx (mem_lowKc hgood hTn hy hkj hkjx
      (Sec2.toNNReal_le_of_mem_Icc ⟨q.coe_nonneg.trans hs.1, hs.2⟩))).2
    rwa [lowE_coord hω] at hm
  have hβc : ContinuousOn (lowBudget W VR k j₀ ω) (Icc (q : ℝ) σ) := by
    have hu : ∀ s ∈ Icc (q : ℝ) σ, VR j₀ s.toNNReal ω - W s.toNNReal ω ≠ 0 := fun s hs => by
      have h1 := hopos s hs
      have h2 := hepos s hs
      intro h
      linarith
    show ContinuousOn (fun s : ℝ => 4 * (VR j₀ s.toNNReal ω - VR k s.toNNReal ω) /
      ((VR j₀ s.toNNReal ω - W s.toNNReal ω) ^ 2 * (VR k s.toNNReal ω - W s.toNNReal ω)) +
        4 * (VR j₀ s.toNNReal ω - VR k s.toNNReal ω) / (VR j₀ s.toNNReal ω - W s.toNNReal ω) ^ 3) _
    refine ContinuousOn.add (ContinuousOn.div (continuousOn_const.mul ((hcv j₀).sub (hcv k)))
      ((((hcv j₀).sub hcw).pow 2).mul ((hcv k).sub hcw)) fun s hs =>
        mul_ne_zero (pow_ne_zero 2 (hu s hs)) (hopos s hs).ne')
      (ContinuousOn.div (continuousOn_const.mul ((hcv j₀).sub (hcv k))) (((hcv j₀).sub hcw).pow 3)
        fun s hs => pow_ne_zero 3 (hu s hs))
  have hβi : IntervalIntegrable (lowBudget W VR k j₀ ω) volume q σ := hβc.intervalIntegrable_of_Icc hqσr
  -- the integral inequality
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hqσr ((hβi.div_const (2 * c₃)).sub hθ2i) hgqσ
    fun s hs => budget_sub_le_itoGen hgood hTn hy hxk hkj hkjx hκ hS hbp hω hs
  rw [intervalIntegral.integral_sub (hβi.div_const _) hθ2i, intervalIntegral.integral_div] at hmono
  -- the energy bound
  have hE1 : ∫ s in (q : ℝ)..σ, θ s.toNNReal ω ^ 2 ≤ (C : ℝ) + 1 := by
    have hθ0 : IntervalIntegrable (fun s : ℝ => θ s.toNNReal ω ^ 2) volume 0 σ := by
      have hθ2 : IsStronglyProgressive (usualAugmentation 𝓕 P) (fun t ω => θ t ω ^ 2) := fun t =>
        (hθp t).pow 2
      refine intervalIntegrable_time hθ2 (C := cmpBound κ (G12.dlt n)
        (fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j) ^ 2) (fun t ω => ?_) ω 0 σ
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_lowTheta_le t ω) 2
    have hθq : IntervalIntegrable (fun s : ℝ => θ s.toNNReal ω ^ 2) volume 0 q := hθ0.mono_set hsub
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hθq (hθq.symm.trans hθ0)
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..q, θ s.toNNReal ω ^ 2 :=
      intervalIntegral.integral_nonneg q.coe_nonneg fun s _ => sq_nonneg _
    have hex := lowStop_le_energy (κ := κ) (ρL := ρL) (xR := xR) (ρR := ρR) (k := k) (j₀ := j₀) (S := S)
      (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (q := q) (C := C) (n := n) ω
    have hab := MathFin.abs_le_N_of_le_exitTime (continuous_lowEnergy hE hGm hGc hgood) hσ0 hex
    have hEσ : lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n σ ω = ∫ s in (0 : ℝ)..σ, θ s.toNNReal ω ^ 2 := rfl
    rw [hEσ] at hab
    push_cast at hab
    linarith [(abs_le.1 hab).2]
  simp only [lowZ]
  rw [hM]
  linarith

include hgood hTn hy hxk hkj hkjx in
theorem lowBudget_nonneg {ω : Ω} (hω : ω ∈ G) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω)) :
    0 ≤ lowBudget W VR k j₀ ω s := by
  have ho := (lowDelta_pos hxk).trans_le (lowDelta_le_gap hgood hω (Sec2.toNNReal_le_of_mem_Icc hs))
  have he : 0 < VR j₀ s.toNNReal ω - VR k s.toNNReal ω := by
    have hm := (lowKc_subset hxk hkjx (mem_lowKc hgood hTn hy hkj hkjx (Sec2.toNNReal_le_of_mem_Icc hs))).2
    rwa [lowE_coord hω] at hm
  have hu : 0 < VR j₀ s.toNNReal ω - W s.toNNReal ω := by linarith
  show 0 ≤ 4 * (VR j₀ s.toNNReal ω - VR k s.toNNReal ω) /
      ((VR j₀ s.toNNReal ω - W s.toNNReal ω) ^ 2 * (VR k s.toNNReal ω - W s.toNNReal ω)) +
    4 * (VR j₀ s.toNNReal ω - VR k s.toNNReal ω) / (VR j₀ s.toNNReal ω - W s.toNNReal ω) ^ 3
  positivity

include hE hGm hGc hgood hTn hy hxk hkj hkjx in
/-- **`Z ≥ 0`.** -/
theorem lowZ_nonneg (hκ : 0 < κ) (hS : S ≤ -2) (hbp : 0 < lowBp κ S (rhoY xR ρR j₀)) (ω : Ω) :
    0 ≤ lowZ κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n ω := by
  by_cases h : lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω ≤ q
  · simp only [lowZ]
    rw [lowMart_eq_of_le h (lowStop_le_horizon ω), sub_self, sub_zero]
    positivity
  push Not at h
  have hω : ω ∈ G := by
    by_contra hω
    have h0 := (lowStop_le_locG (κ := κ) (ρL := ρL) (xR := xR) (ρR := ρR) (k := k) (j₀ := j₀) (S := S)
      (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (q := q) (C := C) (n := n) ω).trans
      (G12.locG_of_not_mem hω).le
    exact absurd (h.trans_le h0) (not_lt.2 (zero_le (a := q)))
  have hb := budget_le_lowZ hE hGm hGc hgood hTn hy hxk hkj hkjx hκ hS hbp hω h.le
  have hbm : lowBm κ S < 0 := by simp only [lowBm]; linarith
  have hc3 := lowC3_pos hκ hbm hbp
  have hint : 0 ≤ ∫ s in (q : ℝ)..(lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : ℝ),
      lowBudget W VR k j₀ ω s :=
    intervalIntegral.integral_nonneg (by exact_mod_cast h.le) fun s hs =>
      lowBudget_nonneg hgood hTn hy hxk hkj hkjx hω ⟨q.coe_nonneg.trans hs.1, hs.2⟩
  exact (div_nonneg hint (by positivity)).trans hb

include hE hGm hGc hgood hT hTn hy hxk hkj hkjx in
/-- **`E Z = C + 3`** (optional stopping between the deterministic times `q ≤ n`). -/
theorem integral_lowZ [IsProbabilityMeasure P] (hqn : q ≤ n) :
    ∫ ω, lowZ κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n ω ∂P = (C : ℝ) + 3 := by
  have hM : Martingale (lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n) (usualAugmentation 𝓕 P) P :=
    martingale_lowObs hE hGm hGc hgood hT hTn hy hxk hkj hkjx _ _
  have heq := hM.setIntegral_eq hqn (s := univ) MeasurableSet.univ
  simp only [setIntegral_univ] at heq
  set M := lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n
  have h1 : ∫ ω, ((C : ℝ) + 3 - (M n ω - M q ω)) ∂P = ∫ _ω, ((C : ℝ) + 3) ∂P - ∫ ω, (M n ω - M q ω) ∂P :=
    integral_sub (integrable_const _) ((hM.integrable _).sub (hM.integrable _))
  have h2 : ∫ ω, (M n ω - M q ω) ∂P = ∫ ω, M n ω ∂P - ∫ ω, M q ω ∂P :=
    integral_sub (hM.integrable _) (hM.integrable _)
  simp only [lowZ]
  rw [h1, h2, heq, sub_self, sub_zero, integral_const, probReal_univ, one_smul]

include hE hGm hGc hgood hT hTn hy hxk hkj hkjx in
/-- **Markov's inequality for `Z`.** -/
theorem measureReal_lowZ_ge_le [IsProbabilityMeasure P] (hκ : 0 < κ) (hS : S ≤ -2)
    (hbp : 0 < lowBp κ S (rhoY xR ρR j₀)) (hqn : q ≤ n) {K : ℝ} (hK : 0 < K) :
    P.real {ω | K ≤ lowZ κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n ω} ≤ ((C : ℝ) + 3) / K := by
  have hM : Martingale (lowMart κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n) (usualAugmentation 𝓕 P) P :=
    martingale_lowObs hE hGm hGc hgood hT hTn hy hxk hkj hkjx _ _
  have hZi : Integrable (lowZ κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n) P :=
    (integrable_const _).sub ((hM.integrable _).sub (hM.integrable _))
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => lowZ_nonneg hE hGm hGc hgood hTn hy hxk hkj hkjx hκ hS hbp ω) hZi K
  rw [integral_lowZ hE hGm hGc hgood hT hTn hy hxk hkj hkjx hqn] at hmk
  rw [le_div_iff₀ hK, mul_comm]
  exact hmk

end Z

end G12Low

end Supp7

end InteractingSLE
