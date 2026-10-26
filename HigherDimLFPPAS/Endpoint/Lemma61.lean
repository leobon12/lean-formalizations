import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Det.InternalBasic

/-!
# Endpoint control along polynomial scales

This file proves Lemma 6.1: the localized LFPP metrics have an almost-sure coarse upper
comparison along `εₙ = n^{-a}`, and their internal distances vanish uniformly on shrinking
endpoint pairs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal

namespace HigherDimLFPPAS.Endpoint

open HigherDimLQGMetric
open HigherDimLFPPAS.Core
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The near-minimizer form of `setDistIn`, used to select endpoints in the small balls. -/
private theorem lemma61_exists_pair_of_setDistIn_lt
    (G : ContMetric d) (V A B : Set (Rd d)) {b : ℝ≥0∞}
    (hb : setDistIn G V A B < b) :
    ∃ x ∈ A, ∃ y ∈ B, G.internal V x y < b := by
  unfold setDistIn at hb
  rcases iInf_lt_iff.mp hb with ⟨x, hx⟩
  rcases iInf_lt_iff.mp hx with ⟨hxA, hx⟩
  rcases iInf_lt_iff.mp hx with ⟨y, hy⟩
  rcases iInf_lt_iff.mp hy with ⟨hyB, hxy⟩
  exact ⟨x, hxA, y, hyB, hxy⟩

/-- For `qstar` and `ν` from (6.1), the endpoint exponent arithmetic. -/
private theorem lemma61_endpoint_power
    {ε q ν ξ Q σ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : q - 1 + ξ * (Q - σ) = ν)
    (hν : 0 < ν) :
    ε ^ q * ε ^ (ξ * Q - 1 - ν / 4) * ε ^ (-ξ * σ) ≤ ε ^ (ν / 2) := by
  rw [← Real.rpow_add hε, ← Real.rpow_add hε]
  have hpow : q + (ξ * Q - 1 - ν / 4) + -ξ * σ = 3 * ν / 4 := by
    calc
      q + (ξ * Q - 1 - ν / 4) + -ξ * σ
          = (q - 1 + ξ * (Q - σ)) - ν / 4 := by ring
      _ = 3 * ν / 4 := by rw [hq]; ring
  rw [hpow]
  exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)

/-- A short straight segment has the `ε^{ν/2}` normalized LFPP cost from (6.4). -/
private theorem lemma61_segment_bound
    {ξ Q ε q ν σ C : ℝ} {κ : Rd d → ℝ} {ω : DistRd d}
    (hξ : 0 < ξ) (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hrad : 0 < locRad ε) (hq0 : 0 < q)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hq : q - 1 + ξ * (Q - σ) = ν) (hν : 0 < ν)
    (haeps : 0 < aEps κ ξ ε)
    (hnorm : ε ^ (1 - ξ * Q + ν / 4) ≤ aEps κ ξ ε)
    (hfield : ∀ z ∈ closedBall (0 : Rd d) (C + 1),
      |locField κ ε ω z| ≤ σ * Real.log ε⁻¹)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) C)
    (hxy : ‖y - x‖ ≤ ε ^ q) :
    (Meps κ ξ ε ω).internal (ball 0 (C + 2)) x y ≤ ENNReal.ofReal (ε ^ (ν / 2)) := by
  let φ : C(Rd d, ℝ) := locFieldC κ ε ω
  let P : ℝ → Rd d := HigherDimLFPP.segPath x y
  have ha := haeps
  have hφc : Continuous (locField κ ε ω) := continuous_locField hκ hrad ω
  have hφ : (φ : Rd d → ℝ) = locField κ ε ω := by
    funext z
    simp [φ, locFieldC, hφc]
  have hfield' : ∀ z ∈ closedBall (0 : Rd d) (C + 1),
      Real.exp (ξ * φ z) ≤ ε ^ (-ξ * σ) := by
    intro z hz
    rw [hφ] at *
    have hval : locField κ ε ω z ≤ σ * Real.log ε⁻¹ :=
      (le_abs_self _).trans (hfield z hz)
    have hmul := mul_le_mul_of_nonneg_left hval hξ.le
    have hexp : Real.exp (ξ * locField κ ε ω z) ≤
        Real.exp (ξ * (σ * Real.log ε⁻¹)) := Real.exp_le_exp.mpr hmul
    have hEq : Real.exp (ξ * (σ * Real.log ε⁻¹)) = ε ^ (-ξ * σ) := by
      rw [Real.rpow_def_of_pos hε]
      rw [Real.log_inv ε]
      congr 1
      ring
    exact hexp.trans_eq hEq
  have hx' : x ∈ closedBall (0 : Rd d) (C + 1) := by
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    linarith
  have hy' : y ∈ closedBall (0 : Rd d) (C + 1) := by
    rw [mem_closedBall, dist_zero_right]
    calc ‖y‖ = ‖x + (y - x)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ C + ε ^ q := by
        exact add_le_add (by simpa [mem_closedBall, dist_zero_right] using hx) hxy
      _ ≤ C + 1 := by linarith [Real.rpow_le_one (le_of_lt hε) hε1.le hq0.le]
  have hseg : MapsTo P (Icc (0 : ℝ) 1) (closedBall (0 : Rd d) (C + 1)) :=
    HigherDimLFPP.mapsTo_segPath (convex_closedBall 0 (C + 1)) hx' hy'
  have hsegcost : HigherDimLFPP.lfppLength ξ φ P ≤ ε ^ (-ξ * σ) * ‖y - x‖ :=
    HigherDimLFPP.lfppLength_segPath_le φ.continuous x y (fun t ht => hfield' (P t) (hseg ht))
  have hsegcost' : HigherDimLFPP.lfppLength ξ φ P ≤ ε ^ (-ξ * σ) * ε ^ q := by
    calc
      HigherDimLFPP.lfppLength ξ φ P ≤ ε ^ (-ξ * σ) * ‖y - x‖ := hsegcost
      _ ≤ ε ^ (-ξ * σ) * ε ^ q :=
        mul_le_mul_of_nonneg_left hxy (Real.rpow_nonneg (le_of_lt hε) _)
  have hnorminv : (aEps κ ξ ε)⁻¹ ≤ ε ^ (ξ * Q - 1 - ν / 4) := by
    have hpowpos : 0 < ε ^ (1 - ξ * Q + ν / 4) := Real.rpow_pos_of_pos hε _
    have hi := (inv_le_inv₀ ha hpowpos).mpr hnorm
    have hpowinv : (ε ^ (1 - ξ * Q + ν / 4))⁻¹ = ε ^ (ξ * Q - 1 - ν / 4) := by
      rw [← Real.rpow_neg hε.le]
      congr 1
      ring
    rw [hpowinv] at hi
    exact hi
  have hpower : ε ^ q * ε ^ (ξ * Q - 1 - ν / 4) * ε ^ (-ξ * σ) ≤ ε ^ (ν / 2) :=
    lemma61_endpoint_power hε hε1.le hq hν
  have hnormalcost : (aEps κ ξ ε)⁻¹ * HigherDimLFPP.lfppLength ξ φ P ≤ ε ^ (ν / 2) := by
    calc
      (aEps κ ξ ε)⁻¹ * HigherDimLFPP.lfppLength ξ φ P ≤
          ε ^ (ξ * Q - 1 - ν / 4) * (ε ^ (-ξ * σ) * ε ^ q) := by
            exact mul_le_mul hnorminv hsegcost'
              (HigherDimLFPP.lfppLength_nonneg ξ φ P) (by positivity)
      _ = ε ^ q * ε ^ (ξ * Q - 1 - ν / 4) * ε ^ (-ξ * σ) := by ring
      _ ≤ ε ^ (ν / 2) := hpower
  have hMeps : Meps κ ξ ε ω =
      (HigherDimLQGMetric.fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha) := by
    simp [Meps, ha, φ]
  rw [hMeps, ContMetric.internal_smul (inv_pos.2 ha)]
  have hcurve :
      (HigherDimLQGMetric.fieldLfppMetric ξ φ).internal (ball 0 (C + 2)) x y ≤
        ENNReal.ofReal (HigherDimLFPP.lfppLength ξ φ P) := by
    have hPU : MapsTo P (Icc (0 : ℝ) 1) (ball 0 (C + 2)) := by
      intro t ht
      have ht' := hseg ht
      rw [mem_closedBall, dist_zero_right] at ht'
      rw [mem_ball, dist_zero_right]
      linarith
    have hlen : (HigherDimLQGMetric.fieldLfppMetric ξ φ).len P 0 1 ≤
        HigherDimLQGMetric.lfppLen ξ φ P :=
      HigherDimLQGMetric.fieldLfppMetric_len_le_lfppLen (ξ := ξ) φ
      (HigherDimLFPP.isPcwC1Path_segPath x y) le_rfl le_rfl
    have hcurve' := (HigherDimLQGMetric.fieldLfppMetric ξ φ).internal_le_len
      (P := P) (a := 0) (b := 1) zero_le_one
      (HigherDimLFPP.isPcwC1Path_segPath x y).continuousOn hPU
    rw [HigherDimLQGMetric.lfppLen_eq_ofReal φ.continuous
      (HigherDimLFPP.isPcwC1Path_segPath x y)] at hlen
    simpa [P] using hcurve'.trans hlen
  calc
    ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
        (HigherDimLQGMetric.fieldLfppMetric ξ φ).internal (ball 0 (C + 2)) x y
        ≤ ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
            ENNReal.ofReal (HigherDimLFPP.lfppLength ξ φ P) :=
          mul_le_mul_of_nonneg_left hcurve (by positivity)
    _ = ENNReal.ofReal ((aEps κ ξ ε)⁻¹ * HigherDimLFPP.lfppLength ξ φ P) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
    _ ≤ ENNReal.ofReal (ε ^ (ν / 2)) := ENNReal.ofReal_le_ofReal hnormalcost

/-- Uniform continuity of the finite internal distance makes short pairs have small internal cost. -/
private theorem lemma61_internal_small
    (G : ContMetric d) (hG : G.IsLength) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
      ‖x - y‖ ≤ δ → G.internal (ball 0 (R + 1)) x y ≤ ENNReal.ofReal η := by
  let U : Set (Rd d) := ball 0 (R + 1)
  have hUconn : IsConnected U := Metric.isConnected_ball (by linarith)
  have hInt := HigherDimLFPPAS.Det.internal_finite_continuous G hG Metric.isOpen_ball hUconn
  have hsub : closedBall (0 : Rd d) R ⊆ U := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    rw [mem_closedBall, dist_zero_right] at hx
    linarith
  let f : Rd d × Rd d → ℝ := fun p => (G.internal U p.1 p.2).toReal
  have hfcont : ContinuousOn f (closedBall 0 R ×ˢ closedBall 0 R) :=
    hInt.2.mono (Set.prod_mono hsub hsub)
  have hK : IsCompact (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) :=
    (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R)
  have hfuc := hK.uniformContinuousOn_of_continuous hfcont
  rw [Metric.uniformContinuousOn_iff_le] at hfuc
  obtain ⟨δ, hδ, hδmod⟩ := hfuc η hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  have hp : dist (x, y) (x, x) ≤ δ := by
    rw [Prod.dist_eq]
    apply max_le_iff.mpr
    constructor
    · simpa using hδ.le
    · simpa only [dist_eq_norm, norm_sub_rev] using hxy
  have hfsmall := hδmod (x, y) ⟨hx, hy⟩ (x, x) ⟨hx, hx⟩ hp
  have hdiag : f (x, x) = 0 := by
    simp only [f]
    rw [G.internal_self (hsub hx)]
    simp
  have hfabs : |(G.internal U x y).toReal| ≤ η := by
    simpa [f, hdiag, Real.dist_eq] using hfsmall
  have hreal : (G.internal U x y).toReal ≤ η := (le_abs_self _).trans hfabs
  have hfinite := hInt.1 x (hsub hx) y (hsub hy)
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Lemma 6.1**: endpoint control along `εₙ = n^{-a}`. -/
theorem lemma61_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (h27 : Core.Lemma27Stmt κ ξ D P h)
    (h23 : Core.Lemma23ii κ P h) (h25 : Core.Lemma25Exponent κ ξ Q) :
    Core.Lemma61Stmt κ ξ D P h := by
  classical
  let gap : ℝ := Q - Real.sqrt (2 * d)
  let η₀ : ℝ := gap / 2
  let qstar : ℝ := max (1 / 2) (1 - ξ * gap / 4)
  let ν : ℝ := qstar - 1 + ξ * gap / 2
  let σ : ℝ := Real.sqrt (2 * d) + η₀
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [hS.subcrit]
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hq0 : 0 < qstar := by
    dsimp [qstar]
    linarith [le_max_left (1 / 2 : ℝ) (1 - ξ * gap / 4)]
  have hq1 : qstar < 1 := by
    dsimp [qstar]
    apply max_lt_iff.mpr
    constructor
    · norm_num
    · have : 0 < ξ * gap := mul_pos hS.xi_pos hgap
      linarith
  have hν : 0 < ν := by
    by_cases hcase : ξ * gap ≤ 2
    · have hqeq : qstar = 1 - ξ * gap / 4 := by
        dsimp [qstar]
        apply max_eq_right
        linarith
      dsimp [ν]
      rw [hqeq]
      have : 0 < ξ * gap := mul_pos hS.xi_pos hgap
      linarith
    · have hqeq : qstar = 1 / 2 := by
        dsimp [qstar]
        apply max_eq_left
        linarith
      dsimp [ν]
      rw [hqeq]
      linarith
  have hqexp : qstar - 1 + ξ * (Q - σ) = ν := by
    dsimp [ν, σ, η₀, gap]
    ring
  have hσpos : 0 < σ := by
    dsimp [σ]
    linarith [Real.sqrt_nonneg (2 * (d : ℝ)), hη₀]
  have hqmem : qstar ∈ Ioo (0 : ℝ) 1 := ⟨hq0, hq1⟩
  obtain ⟨Cs, βs, hCs, hβs, h27q⟩ := h27 qstar hqmem
  have hCspos : 0 < Cs := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hCs
  refine ⟨Cs, βs, hCspos, hβs, ?_⟩
  intro a ha
  have ha0 : 0 < a := by
    by_contra h
    have ha' : a * βs ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hβs.le
    linarith
  let εn : ℕ → ℝ := fun n => (n : ℝ) ^ (-a)
  have htNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have ht0 : Tendsto εn atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0)
    exact (tendsto_rpow_neg_atTop ha0).comp htNat
  have hnPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  have hεPos : ∀ᶠ n : ℕ in atTop, 0 < εn n := by
    filter_upwards [hnPos] with n hn
    exact Real.rpow_pos_of_pos hn _
  have htWithin : Tendsto εn atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ht0, hεPos⟩
  have hnormN : ∀ᶠ n : ℕ in atTop,
      εn n ^ (1 - ξ * Q + ν / 4) ≤ aEps κ ξ (εn n) := by
    filter_upwards [htWithin.eventually (h25 (ν / 4) (by positivity))] with n hn
    exact hn.1
  have hlocN : ∀ᶠ n : ℕ in atTop, 0 < locRad (εn n) := by
    filter_upwards [htWithin.eventually hS.seed.locHyp] with n hn
    exact hn.2.2.1
  have htiny : Tendsto (fun n : ℕ => εn n ^ (ν / 2)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(a * (ν / 2)))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (mul_pos ha0 (by positivity : 0 < ν / 2))).comp htNat
    have heq : (fun n : ℕ => εn n ^ (ν / 2)) =
        fun n : ℕ => (n : ℝ) ^ (-(a * (ν / 2))) := by
      funext n
      change ((n : ℝ) ^ (-a)) ^ (ν / 2) = _
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      ring
    rw [heq]
    exact hpow
  choose K εR hεR h27R using fun R : ℕ => h27q ((R : ℝ) + 1) (by positivity)
  let bad : ℕ → ℕ → Set Ω := fun R n =>
    if hn : n = 0 then ∅ else if he : εn n < εR R then
      {ω | ¬ ∀ x ∈ ball (0 : Rd d) ((R : ℝ) + 1),
        ∀ y ∈ ball (0 : Rd d) ((R : ℝ) + 1),
          setDistIn (Meps κ ξ (εn n) (h ω))
              (thickening (εn n ^ qstar) (ball 0 ((R : ℝ) + 1)))
              (ball x (εn n ^ qstar)) (ball y (εn n ^ qstar)) ≤
            ENNReal.ofReal Cs * (D (h ω)).internal (ball 0 ((R : ℝ) + 1)) x y ∧
          setDistIn (D (h ω)) (thickening (εn n ^ qstar) (ball 0 ((R : ℝ) + 1)))
              (ball x (εn n ^ qstar)) (ball y (εn n ^ qstar)) ≤
            ENNReal.ofReal Cs * (Meps κ ξ (εn n) (h ω)).internal (ball 0 ((R : ℝ) + 1)) x y}
      else ∅
  have hBCeach : ∀ R : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∉ bad R n := by
    intro R
    let K₀ : ℝ := max (K R) 0
    let f : ℕ → ℝ := fun n => K₀ * ((n : ℝ) ^ (a * βs))⁻¹
    have hfnonneg : ∀ n, 0 ≤ f n := by
      intro n
      dsimp [f, K₀]
      positivity
    have hfsum : Summable f := by
      dsimp [f]
      exact (Real.summable_nat_rpow_inv.mpr ha).mul_left K₀
    have hbadBound : ∀ n : ℕ, P (bad R n) ≤ ENNReal.ofReal (f n) := by
      intro n
      by_cases hn : n = 0
      · simp [bad, hn]
      · have hnpos : 0 < (n : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        have hεpos : 0 < εn n := Real.rpow_pos_of_pos hnpos _
        by_cases hεlt : εn n < εR R
        · have hεmem : εn n ∈ Ioo (0 : ℝ) (εR R) := ⟨hεpos, hεlt⟩
          have hmain := h27R R (εn n) hεmem
          have hprob : P (bad R n) ≤ ENNReal.ofReal (K R * εn n ^ βs) := by
            simpa [bad, hn, hεlt] using hmain
          have hpow : εn n ^ βs = ((n : ℝ) ^ (a * βs))⁻¹ := by
            change ((n : ℝ) ^ (-a)) ^ βs = _
            calc
              ((n : ℝ) ^ (-a)) ^ βs = (n : ℝ) ^ ((-a) * βs) :=
                (Real.rpow_mul hnpos.le (-a) βs).symm
              _ = (n : ℝ) ^ (-(a * βs)) := by congr 1 <;> ring
              _ = ((n : ℝ) ^ (a * βs))⁻¹ := Real.rpow_neg hnpos.le (a * βs)
          have hcoef : K R * εn n ^ βs ≤ K₀ * ((n : ℝ) ^ (a * βs))⁻¹ := by
            rw [hpow]
            exact mul_le_mul_of_nonneg_right (le_max_left (K R) 0) (by positivity)
          exact hprob.trans (ENNReal.ofReal_le_ofReal hcoef)
        · simp [bad, hn, hεlt]
    have hsum : (∑' n : ℕ, P (bad R n)) ≠ ∞ := by
      apply ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' n, f n)) ENNReal.ofReal_ne_top
      rw [ENNReal.ofReal_tsum_of_nonneg hfnonneg hfsum]
      exact ENNReal.tsum_le_tsum hbadBound
    exact ae_eventually_notMem hsum
  have hBCall : ∀ᵐ ω ∂P, ∀ R : ℕ, ∀ᶠ n : ℕ in atTop, ω ∉ bad R n := by
    apply ae_all_iff.mpr
    exact hBCeach
  have hlenAE : ∀ᵐ ω ∂P, (D (h ω)).IsLength :=
    hS.strong.length P h hS.field.1.isLGFPlusCont
  filter_upwards [h23, hBCall, hlenAE] with ω h23ω hBCω hlenω
  intro R hR
  have hcoarseAll : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
        (Meps κ ξ (εn n) (h ω)).internal (ball 0 ((R : ℝ) + 2)) x y ≤
          ENNReal.ofReal Cs * (D (h ω)).internal (ball 0 ((R : ℝ) + 1)) x y + ENNReal.ofReal η := by
    intro η hη
    let Rr : ℝ := R
    have hRplus : 0 < Rr + 1 := by dsimp [Rr]; positivity
    have hη₀pos : 0 < η₀ := hη₀
    have hthresholdN : ∀ᶠ n : ℕ in atTop, εn n < εR R :=
      ht0.eventually (Iio_mem_nhds (hεR R))
    have hεltN : ∀ᶠ n : ℕ in atTop, εn n < 1 :=
      ht0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hfieldN : ∀ᶠ n : ℕ in atTop,
        ∀ z ∈ closedBall (0 : Rd d) (Rr + 1),
          |locField κ (εn n) (h ω) z| ≤ σ * Real.log (εn n)⁻¹ := by
      filter_upwards [htWithin.eventually (h23ω (Rr + 1) η₀ hRplus hη₀pos)] with n hn
      exact fun z hz => (hn z hz).2
    have hsmallN : ∀ᶠ n : ℕ in atTop, 2 * (εn n ^ (ν / 2)) ≤ η / 2 := by
      filter_upwards [htiny.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 4))] with n hn
      nlinarith
    filter_upwards [hnormN, hlocN, hfieldN, hsmallN, hBCω R, hthresholdN,
      hεltN, hεPos, hnPos] with n hnorm hloc hfield hsmall hgood hthreshold hεlt hεpos hnpos
    have hqpow : εn n ^ qstar ≤ 1 := Real.rpow_le_one (le_of_lt hεpos) hεlt.le hq0.le
    have hgood' : ∀ x ∈ ball (0 : Rd d) (Rr + 1),
        ∀ y ∈ ball (0 : Rd d) (Rr + 1),
          setDistIn (Meps κ ξ (εn n) (h ω))
              (thickening (εn n ^ qstar) (ball 0 (Rr + 1)))
              (ball x (εn n ^ qstar)) (ball y (εn n ^ qstar)) ≤
            ENNReal.ofReal Cs * (D (h ω)).internal (ball 0 (Rr + 1)) x y ∧
          setDistIn (D (h ω)) (thickening (εn n ^ qstar) (ball 0 (Rr + 1)))
              (ball x (εn n ^ qstar)) (ball y (εn n ^ qstar)) ≤
            ENNReal.ofReal Cs * (Meps κ ξ (εn n) (h ω)).internal (ball 0 (Rr + 1)) x y := by
      have hnN : 0 < n := by exact_mod_cast hnpos
      have hnne : n ≠ 0 := Nat.ne_of_gt hnN
      simpa [bad, hnne, hthreshold, Rr] using hgood
    intro x hx y hy
    have hxU : x ∈ ball (0 : Rd d) (Rr + 1) := by
      rw [mem_ball, dist_zero_right]
      rw [mem_closedBall, dist_zero_right] at hx
      exact lt_of_le_of_lt hx (by dsimp [Rr]; linarith)
    have hyU : y ∈ ball (0 : Rd d) (Rr + 1) := by
      rw [mem_ball, dist_zero_right]
      rw [mem_closedBall, dist_zero_right] at hy
      exact lt_of_le_of_lt hy (by dsimp [Rr]; linarith)
    have hDcont := HigherDimLFPPAS.Det.internal_finite_continuous (D (h ω))
      hlenω (U := ball 0 (Rr + 1)) Metric.isOpen_ball
      (Metric.isConnected_ball (by positivity))
    have hDxy : (D (h ω)).internal (ball 0 (Rr + 1)) x y ≠ ∞ := hDcont.1 x hxU y hyU
    let base : ℝ≥0∞ := ENNReal.ofReal Cs * (D (h ω)).internal (ball 0 (Rr + 1)) x y
    have hbaseNeTop : base ≠ ∞ := by
      dsimp [base]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDxy
    have hhalfNe : ENNReal.ofReal (η / 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hbaseAdd : base < base + ENNReal.ofReal (η / 2) :=
      ENNReal.lt_add_right hbaseNeTop hhalfNe
    have hset := (hgood' x hxU y hyU).1
    have hsetLt : setDistIn (Meps κ ξ (εn n) (h ω))
        (thickening (εn n ^ qstar) (ball 0 (Rr + 1)))
        (ball x (εn n ^ qstar)) (ball y (εn n ^ qstar)) < base + ENNReal.ofReal (η / 2) :=
      lt_of_le_of_lt hset hbaseAdd
    obtain ⟨x', hxball, y', hyball, hxy'⟩ :=
      lemma61_exists_pair_of_setDistIn_lt _ _ _ _ hsetLt
    have hapos : 0 < aEps κ ξ (εn n) := hS.seed.aEps_pos ξ (εn n) hεpos
    have hleft : (Meps κ ξ (εn n) (h ω)).internal (ball 0 (Rr + 2)) x x' ≤
        ENNReal.ofReal (εn n ^ (ν / 2)) := by
      refine lemma61_segment_bound hS.xi_pos hS.seed.kernelSmooth hloc hq0 hεpos hεlt
        hqexp hν hapos hnorm hfield hx ?_
      exact (mem_ball_iff_norm.mp hxball).le
    have hright : (Meps κ ξ (εn n) (h ω)).internal (ball 0 (Rr + 2)) y' y ≤
        ENNReal.ofReal (εn n ^ (ν / 2)) := by
      calc
        _ = (Meps κ ξ (εn n) (h ω)).internal (ball 0 (Rr + 2)) y y' := by
          rw [ContMetric.internal_comm]
        _ ≤ ENNReal.ofReal (εn n ^ (ν / 2)) := by
          refine lemma61_segment_bound hS.xi_pos hS.seed.kernelSmooth hloc hq0 hεpos hεlt
            hqexp hν hapos hnorm hfield hy ?_
          exact (mem_ball_iff_norm.mp hyball).le
    let V : Set (Rd d) := thickening (εn n ^ qstar) (ball 0 (Rr + 1))
    let W : Set (Rd d) := ball (0 : Rd d) (Rr + 2)
    have hVW : V ⊆ W := by
      intro z hz
      obtain ⟨w, hw, hzw⟩ := Metric.mem_thickening_iff.mp hz
      have hw' : ‖w‖ < Rr + 1 := by
        rw [mem_ball, dist_zero_right] at hw
        exact hw
      have hzw' : ‖z - w‖ < εn n ^ qstar := by
        simpa only [dist_eq_norm, norm_sub_rev] using hzw
      rw [mem_ball, dist_zero_right]
      calc
        ‖z‖ = ‖w + (z - w)‖ := by congr 1 <;> abel
        _ ≤ ‖w‖ + ‖z - w‖ := norm_add_le _ _
        _ < (Rr + 1) + εn n ^ qstar := add_lt_add hw' hzw'
        _ ≤ Rr + 2 := by linarith
    have hmid : (Meps κ ξ (εn n) (h ω)).internal W x' y' ≤
        base + ENNReal.ofReal (η / 2) := by
      exact ((Meps κ ξ (εn n) (h ω)).internal_anti hVW x' y').trans hxy'.le
    have hconn : ENNReal.ofReal (εn n ^ (ν / 2)) + ENNReal.ofReal (εn n ^ (ν / 2)) ≤
        ENNReal.ofReal (η / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    have htri : (Meps κ ξ (εn n) (h ω)).internal W x y ≤
        (Meps κ ξ (εn n) (h ω)).internal W x x' +
          ((Meps κ ξ (εn n) (h ω)).internal W x' y' +
            (Meps κ ξ (εn n) (h ω)).internal W y' y) := by
      have ht1 := (Meps κ ξ (εn n) (h ω)).internal_triangle W x x' y
      have ht2 := (Meps κ ξ (εn n) (h ω)).internal_triangle W x' y' y
      calc
        _ ≤ (Meps κ ξ (εn n) (h ω)).internal W x x' +
            (Meps κ ξ (εn n) (h ω)).internal W x' y := ht1
        _ ≤ (Meps κ ξ (εn n) (h ω)).internal W x x' +
            ((Meps κ ξ (εn n) (h ω)).internal W x' y' +
              (Meps κ ξ (εn n) (h ω)).internal W y' y) := by
          gcongr
    have hupper : (Meps κ ξ (εn n) (h ω)).internal W x x' +
        ((Meps κ ξ (εn n) (h ω)).internal W x' y' +
          (Meps κ ξ (εn n) (h ω)).internal W y' y) ≤ base + ENNReal.ofReal η := by
      calc
        _ ≤ ENNReal.ofReal (εn n ^ (ν / 2)) +
            (base + ENNReal.ofReal (η / 2) + ENNReal.ofReal (εn n ^ (ν / 2))) := by
              gcongr
        _ = base + (ENNReal.ofReal (η / 2) +
            (ENNReal.ofReal (εn n ^ (ν / 2)) + ENNReal.ofReal (εn n ^ (ν / 2)))) := by ac_rfl
        _ ≤ base + (ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2)) :=
          by gcongr
        _ = base + ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
    have hchain : (Meps κ ξ (εn n) (h ω)).internal W x y ≤ base + ENNReal.ofReal η :=
      htri.trans hupper
    simpa only [W, base] using hchain
  constructor
  · exact hcoarseAll
  · intro ρ hρ η hη
    let Rr : ℝ := R
    obtain ⟨δ, hδ, hDsmall⟩ :=
      lemma61_internal_small (R := (R : ℝ)) (η := η / (2 * Cs))
        (D (h ω)) hlenω
        (by
          have hR' : 0 < R := lt_of_lt_of_le Nat.zero_lt_one hR
          exact_mod_cast hR')
        (by positivity : 0 < η / (2 * Cs))
    have hρsmall : ∀ᶠ n : ℕ in atTop, ρ n < δ := by
      exact hρ.eventually (Iio_mem_nhds hδ)
    have hcoarse := hcoarseAll (η / 2) (by positivity)
    filter_upwards [hcoarse, hρsmall] with n hnρ hρn
    intro x hx y hy hxy
    have hDs := hDsmall x hx y hy (hxy.trans hρn.le)
    have hDscaled : ENNReal.ofReal Cs * (D (h ω)).internal (ball 0 (Rr + 1)) x y ≤
        ENNReal.ofReal (η / 2) := by
      calc
        ENNReal.ofReal Cs * (D (h ω)).internal (ball 0 (Rr + 1)) x y ≤
            ENNReal.ofReal Cs * ENNReal.ofReal (η / (2 * Cs)) :=
          mul_le_mul_of_nonneg_left hDs (by positivity)
        _ = ENNReal.ofReal (η / 2) := by
          rw [← ENNReal.ofReal_mul hCspos.le]
          congr 1
          field_simp
    calc
      (Meps κ ξ (εn n) (h ω)).internal (ball 0 (Rr + 2)) x y ≤
          ENNReal.ofReal Cs * (D (h ω)).internal (ball 0 (Rr + 1)) x y + ENNReal.ofReal (η / 2) := hnρ x hx y hy
      _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hDscaled le_rfl
      _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end HigherDimLFPPAS.Endpoint
