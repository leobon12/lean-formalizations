/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftAlivePath

/-!
# Lower real points are never swallowed (`κ ≤ 4`): `ConstDriftAliveStatement`

Packet PROVE-ZHAN-A8. Proof of PROVE-ZHAN-A7's named input `ConstDriftAliveStatement κ` for `0 ≤ κ ≤ 4`, hence of
Zhan's height statement and of the strip endpoint theorem for `0 < κ ≤ 4`:

* `ae_exists_pos_sol`: for a filtered Brownian motion with continuous paths started at `0` and `σ ≤ 1`, almost surely
  for every `q > 0` (fixed) and every horizon `T` the lower-gap equation `X = q − (√κ B + σ t) + ∫ C(X)` has a positive
  continuous solution on `[0, T]` (the tamed gap of `ConstDriftAliveHit.lean` at a level it never reaches);
* `ae_exists_lowerGap_sol`: for every Brownian motion `β` and `|σ| ≤ 1`, almost surely for every rational `q ≠ 0`
  (the side `q < 0` by the reflection `β ↦ −β`, `σ ↦ −σ`, `X ↦ −X`, `C` odd);
* `constDriftAliveStatement`: the chordal flow of `e^q − 1` exists on the strip life (`ConstDriftAlivePath.lean`),
  and every real point of `(−1, ∞) ∖ {0}` is reached by monotonicity in the initial point (QuantumZipper's
  `exists_isForwardSol_of_lt` for a driver frozen after `s`, and the reflection `isForwardSol_neg` on the left).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol)

universe u

namespace InteractingSLE

namespace Zhan

namespace LowerGap

open Sec4 (cothHalf)
open Strip

/-! ### Positive solutions of the lower-gap equation -/

section Sol

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ σ q : ℝ}
  {B : ℝ≥0 → Ω → ℝ}

/-- **Positive solutions on every horizon** (filtered Brownian motion with continuous paths, `σ ≤ 1`, `q > 0`). -/
theorem ae_exists_pos_sol [IsProbabilityMeasure P] (hB : IsFilteredBrownianReal 𝓖 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 4) (hσ : σ ≤ 1)
    (hq : 0 < q) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T → ∃ X : ℝ → ℝ, ContinuousOn X (Icc 0 T) ∧ ∀ t ∈ Icc 0 T,
      0 < X t ∧ X t = q - (Real.sqrt κ * B t.toNNReal ω + σ * t) + ∫ r in (0 : ℝ)..t, cothHalf (X r) := by
  filter_upwards [ae_exists_pos_lgProc hB hBc hB0 hκ0 hκ hσ hq] with ω hω
  intro T hT
  obtain ⟨n, hn⟩ := hω ⌈T⌉₊
  have hc := lvl_pos n
  set X : ℝ → ℝ := fun r => lgProc κ σ q (lvl n) B r.toNNReal ω with hXdef
  have hpos : ∀ t ∈ Icc 0 T, lvl n < X t := fun t ht => hn _ (by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast, Real.coe_toNNReal t ht.1]
    exact ht.2.trans (Nat.le_ceil T))
  refine ⟨X, ((continuous_lgProc hc (hBc ω)).comp continuous_real_toNNReal).continuousOn, fun t ht =>
    ⟨hc.trans (hpos t ht), ?_⟩⟩
  rw [hXdef]
  simp only
  rw [lgProc_eq hc (hBc ω) t ht.1]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht.1] at hr
  exact tame_of_le (hpos r ⟨hr.1, hr.2.trans ht.2⟩).le

end Sol

section Brownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {κ σ : ℝ} {β : ℝ≥0 → Ω → ℝ}

/-- **Nonvanishing solutions for every rational initial gap** (every Brownian motion, `|σ| ≤ 1`). -/
theorem ae_exists_lowerGap_sol (hβ : IsBrownianReal β P) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 4) (hσ : |σ| ≤ 1) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ X : ℝ → ℝ, ContinuousOn X (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, X t ≠ 0 ∧
        X t = q - (Real.sqrt κ * β t.toNNReal ω + σ * t) + ∫ r in (0 : ℝ)..t, cothHalf (X r) := by
  have hP : IsProbabilityMeasure P := hβ.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨B, hBm, hBc, hB0, hB, hBeq⟩ := QuantumZipper.RS.exists_good_version0 hβ
  have hBf := OneForce.isFilteredBrownianReal_natFilt hB hBm
  have hBn : IsBrownianReal (-B) P := hB.neg
  have hBnm : ∀ t, Measurable ((-B) t) := fun t => (hBm t).neg
  have hBnf := OneForce.isFilteredBrownianReal_natFilt hBn hBnm
  have hBnc : ∀ ω, Continuous ((-B) · ω) := fun ω => (hBc ω).neg
  have hBn0 : ∀ ω, (-B) 0 ω = 0 := fun ω => by simp [hB0]
  have hσ1 : σ ≤ 1 := (abs_le.1 hσ).2
  have hσ2 : -σ ≤ 1 := by linarith [(abs_le.1 hσ).1]
  have hpos : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < (q : ℝ) → ∀ T : ℝ, 0 ≤ T → ∃ X : ℝ → ℝ, ContinuousOn X (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, 0 < X t ∧
        X t = q - (Real.sqrt κ * B t.toNNReal ω + σ * t) + ∫ r in (0 : ℝ)..t, cothHalf (X r) := by
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [ae_exists_pos_sol hBf hBc hB0 hκ0 hκ hσ1 hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  have hneg : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < -(q : ℝ) → ∀ T : ℝ, 0 ≤ T → ∃ X : ℝ → ℝ, ContinuousOn X (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, 0 < X t ∧
        X t = -(q : ℝ) - (Real.sqrt κ * (-B) t.toNNReal ω + -σ * t) + ∫ r in (0 : ℝ)..t, cothHalf (X r) := by
    intro q
    by_cases hq : 0 < -(q : ℝ)
    · filter_upwards [ae_exists_pos_sol hBnf hBnc hBn0 hκ0 hκ hσ2 hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [ae_all_iff.2 hpos, ae_all_iff.2 hneg, hBeq] with ω hp hn heq
  intro q hq0 T hT
  rcases lt_or_gt_of_ne hq0 with hlt | hgt
  · obtain ⟨X, hXc, hX⟩ := hn q (by linarith) T hT
    refine ⟨fun t => -X t, hXc.neg, fun t ht => ⟨neg_ne_zero.2 (hX t ht).1.ne', ?_⟩⟩
    have e : ∫ r in (0 : ℝ)..t, cothHalf (-X r) = -∫ r in (0 : ℝ)..t, cothHalf (X r) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun r _ => Sec4.cothHalf_neg _
    show -X t = _ + ∫ r in (0 : ℝ)..t, cothHalf (-X r)
    rw [e, (hX t ht).2]
    simp only [Pi.neg_apply, heq]
    ring
  · obtain ⟨X, hXc, hX⟩ := hp q hgt T hT
    refine ⟨X, hXc, fun t ht => ⟨(hX t ht).1.ne', ?_⟩⟩
    rw [(hX t ht).2, heq]

end Brownian

/-! ### Monotonicity in the initial point -/

/-- A real point to the right of a living point `q > w(0)` lives (driver frozen after `s`). -/
theorem exists_isForwardSol_of_lt_of_continuousOn {W : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hWc : ContinuousOn W (Icc 0 s)) {q y : ℝ} (hq : W 0 < q) (hqy : q < y) {u : ℝ → ℂ}
    (hu : IsForwardSol W (q : ℂ) s u) : ∃ u' : ℝ → ℂ, IsForwardSol W (y : ℂ) s u' := by
  set W' : ℝ → ℝ := fun r => W (max 0 (min r s)) with hW'
  have hW'c : Continuous W' :=
    hWc.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      fun r => ⟨le_max_left _ _, max_le hs (min_le_right _ _)⟩
  have hagree : ∀ r ∈ Icc (0 : ℝ) s, W r = W' r := fun r hr => by
    simp only [hW', min_eq_left hr.2, max_eq_right hr.1]
  have h0 : W' 0 = W 0 := (hagree 0 ⟨le_rfl, hs⟩).symm
  obtain ⟨u', hu'⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hW'c hs (h0 ▸ hq) hqy
    (QuantumZipper.isForwardSol_congr_drive hagree hu)
  exact ⟨u', QuantumZipper.isForwardSol_congr_drive (fun r hr => (hagree r hr).symm) hu'⟩

/-- A real point to the left of a living point `q < w(0)` lives (reflection). -/
theorem exists_isForwardSol_of_gt_of_continuousOn {W : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hWc : ContinuousOn W (Icc 0 s)) {q y : ℝ} (hq : q < W 0) (hqy : y < q) {u : ℝ → ℂ}
    (hu : IsForwardSol W (q : ℂ) s u) : ∃ u' : ℝ → ℂ, IsForwardSol W (y : ℂ) s u' := by
  have h1 := QuantumZipper.RS.isForwardSol_neg hu
  have e1 : -((q : ℝ) : ℂ) = ((-q : ℝ) : ℂ) := by push_cast; ring
  rw [e1] at h1
  obtain ⟨u', hu'⟩ := exists_isForwardSol_of_lt_of_continuousOn hs hWc.neg (by simpa using hq)
    (neg_lt_neg hqy) h1
  have h2 := QuantumZipper.RS.isForwardSol_neg hu'
  have e2 : -((-y : ℝ) : ℂ) = ((y : ℝ) : ℂ) := by push_cast; ring
  have e3 : (fun t => -(-W) t) = W := by funext t; simp
  rw [e2, e3] at h2
  exact ⟨_, h2⟩

end LowerGap

variable {κ : ℝ}

open Strip

/-- **PROVE-ZHAN-A7's named input, proved for `0 ≤ κ ≤ 4`: lower real points are never swallowed.** -/
theorem constDriftAliveStatement (hκ0 : 0 ≤ κ) (hκ : κ ≤ 4) : ConstDriftAliveStatement.{u} κ := by
  intro σ hσ Ω mΩ P β hβ
  filter_upwards [LowerGap.ae_exists_lowerGap_sol hβ hκ0 hκ hσ.le] with ω hω
  intro w v ζ hd x hx1 hx0 s hs
  have hsep := hd.1.2.1 s hs
  have hT0 : 0 ≤ stripClock (extPath w) (extPath v) s := hsep.stripClock_nonneg ⟨s.coe_nonneg, le_rfl⟩
  have hw0 : extPath w 0 = 0 := by simp only [extPath, Real.toNNReal_zero]; exact hd.1.1
  -- the chordal flow of `e^q − 1` for rational `q ≠ 0`
  have halive : ∀ q : ℚ, (q : ℝ) ≠ 0 → ∃ u : ℝ → ℂ,
      IsForwardSol (extPath w) ((Real.exp q - 1 : ℝ) : ℂ) s u := by
    intro q hq
    obtain ⟨X, hXc, hX⟩ := hω q hq _ hT0
    refine LowerGap.exists_isForwardSol_of_lowerGap hd hs le_rfl hXc (fun t ht => (hX t ht).1)
      fun t ht => ?_
    rw [(hX t ht).2, Real.coe_toNNReal t ht.1]
  have h1x : 0 < 1 + x := by linarith
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · -- `x ∈ (−1, 0)`: a rational `q ∈ (log(1+x), 0)`
    have hl : Real.log (1 + x) < 0 := Real.log_neg h1x (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hl
    obtain ⟨u, hu⟩ := halive q hq2.ne
    have hlt1 : Real.exp q < 1 := by
      have := Real.exp_lt_exp.2 hq2
      rwa [Real.exp_zero] at this
    have hgt : 1 + x < Real.exp q := by
      have := Real.exp_lt_exp.2 hq1
      rwa [Real.exp_log h1x] at this
    exact LowerGap.exists_isForwardSol_of_gt_of_continuousOn s.coe_nonneg hsep.continuousOn_w
      (by rw [hw0]; linarith) (by linarith) hu
  · -- `x > 0`: a rational `q ∈ (0, log(1+x))`
    have hl : 0 < Real.log (1 + x) := Real.log_pos (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hl
    obtain ⟨u, hu⟩ := halive q hq1.ne'
    have hgt1 : 1 < Real.exp q := Real.one_lt_exp_iff.2 hq1
    have hlt : Real.exp q < 1 + x := by
      have := Real.exp_lt_exp.2 hq2
      rwa [Real.exp_log h1x] at this
    exact LowerGap.exists_isForwardSol_of_lt_of_continuousOn s.coe_nonneg hsep.continuousOn_w
      (by rw [hw0]; linarith) (by linarith) hu

/-- **Zhan's height statement for `0 ≤ κ ≤ 4`** (A7's conditional helper with the input proved). -/
theorem constDriftHeightStatement_of_le_four (hκ0 : 0 ≤ κ) (hκ : κ ≤ 4) : ConstDriftHeightStatement.{u} κ :=
  constDriftHeightStatement_of_alive (constDriftAliveStatement hκ0 hκ)

/-- **Zhan's strip endpoint theorem (ii) for `0 < κ ≤ 4`.** -/
theorem stripEndpointStatement_of_le_four (hκ0 : 0 < κ) (hκ : κ ≤ 4) : StripEndpointStatement.{u} κ :=
  stripEndpointStatement_of_alive hκ0 (constDriftAliveStatement hκ0.le hκ)

end Zhan

end InteractingSLE
