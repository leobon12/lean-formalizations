import QuantumZipper.Proofs.Thm18.R18RTCoreDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT2-core (D82): `MaskPullCoreStmt` from log growth and a Beurling mass bound

Sheffield, arXiv:1012.4797, §4.1 p. 48; Berestycki–Powell, arXiv:2404.16642, Thm 8.16 and
Rem 8.10 (p. 283): the unzipped field is determined by `h` off `η`, because `η` is not charged.
Quantitatively, for `ν = (foldedCircle d r).map f_s⁻¹` with the circle off the unzipped remaining
curve, the `k`-th terms of the regularized pairings of `Y` and of the field read off the curve
differ only on the set `A_k` of centres whose circle of radius `2^{-k}` is not off `η`
(`R18RTCoreDet.lean`), where both integrands are `O(k)`; so the difference is `O(k ν(A_k))`.

Proved here: `maskPullCoreStmt_of_growth_mass : CircAvgLogGrowthStmt → PullMassBoundStmt →
MaskPullCoreStmt`. The two inputs are single standard estimates:

* `CircAvgLogGrowthStmt` (probabilistic): a.s., on every bounded set, the raw folded-circle
  averages of the wedge field at radius `2^{-k}` are `O(k + 1)` (log growth in the radius).
  Source: Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab. 38 (2010),
  Prop. 2.1 (a.s. modulus of continuity of the circle-average process, whence
  `sup_{|z| ≤ R} |h_ε(z)| = O(log 1/ε)`), for the free-boundary field by reflection; the wedge
  adds `−α log|·|`, whose averages are `O(k)`, and a radial part continuous on compacts.
* `PullMassBoundStmt` (deterministic, for the a.s. good SLE driver): the pulled-back circle
  measure of the `2^{-k}`-neighbourhood of `η` decays geometrically in `k`. Source: the Beurling
  estimate (Lawler, *Schramm–Loewner evolution*, Park City notes arXiv:0712.3256, Thm 2.10, p. 18;
  as used in Johansson Viklund–Lawler arXiv:0911.3983 p. 12): `Im f_s(w) ≤ C dist(w, η[0,s] ∪ ℝ)^{1/2}`
  on bounded sets, so `f_s(A_k)` lies in a strip of width `O(2^{-k/2})` around `ℝ` (away from the
  remaining curve, which the circle avoids), whose folded-circle mass is `O(2^{-k/4})`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- A circle that is not off `K` has its centre within `r` of `K` or of the reflection of `K`. -/
theorem min_infDist_le_of_not_circleOff {K : Set ℂ} {w : ℂ} {r : ℝ} (h : ¬ CircleOff K w r) :
    min (infDist w K) (infDist w ((starRingEnd ℂ) '' K)) ≤ r := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  by_contra hlt
  push Not at hlt
  apply h
  refine ⟨δ, hδ, fun u hu hK => ?_⟩
  have hd : dist w u < r + δ := by rw [dist_comm]; linarith [(abs_lt.1 hu).2]
  unfold foldH at hK
  split_ifs at hK with him
  · have := infDist_le_dist_of_mem hK (x := w)
    linarith [min_le_left (infDist w K) (infDist w ((starRingEnd ℂ) '' K))]
  · have hm : u ∈ (starRingEnd ℂ) '' K := ⟨(starRingEnd ℂ) u, hK, by simp⟩
    have := infDist_le_dist_of_mem hm (x := w)
    linarith [min_le_right (infDist w K) (infDist w ((starRingEnd ℂ) '' K))]

/-- **Log growth of the circle averages of the wedge field** (Hu–Miller–Peres, Ann. Probab. 38
(2010), Prop. 2.1): a.s., on every bounded set, the raw folded-circle averages at radius `2^{-k}`
(centred at the dyadic approximations of the points) are `O(k + 1)`. -/
def CircAvgLogGrowthStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ) (w : ℂ), ‖w‖ ≤ Rr →
      |Y ω (foldedCircle (dyadicRoundC n w) (radius k))| ≤ C * (k + 1)

/-- **Beurling mass bound for pulled-back circles** (Beurling estimate; Lawler, arXiv:0712.3256,
Thm 2.10): a.s., for every folded dyadic circle off the unzipped remaining curve, its pullback by
`f_s⁻¹` is carried by a bounded set and gives geometrically small mass (in `k`) to the closed
`2^{-k}`-neighbourhood of the curve `η` and of its reflection. -/
def PullMassBoundStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → ∀ a : ℝ, 0 < a → ∀ (d : ℂ) (k₀ : ℕ),
      CircleOff (unzCurve (drive (γ ^ 2) B ω) s a) d (radius k₀) →
      ∃ Rr Cm q : ℝ, 0 ≤ Cm ∧ 0 ≤ q ∧ q < 1 ∧
        (foldedCircle d (radius k₀)).map (fwdMapInv (drive (γ ^ 2) B ω) s)
          {w | ¬ ‖w‖ ≤ Rr} = 0 ∧
        ∀ k : ℕ, (foldedCircle d (radius k₀)).map (fwdMapInv (drive (γ ^ 2) B ω) s)
          {w | min (infDist w (curveOf (drive (γ ^ 2) B ω)))
            (infDist w ((starRingEnd ℂ) '' curveOf (drive (γ ^ 2) B ω))) ≤ radius k} ≤
            ENNReal.ofReal (Cm * q ^ k)

/-- **RT2 core estimate** from log growth of circle averages and the Beurling mass bound. -/
theorem maskPullCoreStmt_of_growth_mass (hG : CircAvgLogGrowthStmt) (hM : PullMassBoundStmt) :
    MaskPullCoreStmt := by
  intro γ Ω _ P _ B Y hS hI
  filter_upwards [hG γ P B Y hS hI, hM γ P B Y hS hI, D74.ae_wedgeConfig_snd_good hS]
    with ω hg hm hgood
  intro s hs a ha d k₀ hoff
  obtain ⟨Rr, Cm, q, hCm, hq0, hq1, hsupp, hmass⟩ := hm s hs a ha d k₀ hoff
  obtain ⟨C, hC, hgr⟩ := hg Rr
  exact evalReg_eq_readOffField_of_bounds (x := wedgeConfig γ B Y ω) hgood.1 hgood.2 hC hCm hq0
    hq1 hsupp hgr fun k =>
      (measure_mono fun w hw => min_infDist_le_of_not_circleOff hw).trans (hmass k)

end R18
end QuantumZipper
