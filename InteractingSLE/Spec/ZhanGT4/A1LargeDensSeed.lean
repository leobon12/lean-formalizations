/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ForcesSnd
import InteractingSLE.Spec.Supplement.GB7aCmpLoewner
import InteractingSLE.Spec.ZhanGT4.DualMarg0

/-!
# Zhan's A.1 (R80): the small curve's seed forces at the image driver

Packet PROVE-A1-LARGEDENS. Source: Astra, *Follow-up proofs* §A.1.6 (`ig1_followup_proofs.txt` L426–L500, R38) and
follow-up 4 §2.5 item 3 (R71): "For positive time, the force ODE and (D1) give `d h_j(V_j^m) = 2A²_{j,1}/(h_j(V_j^m) −
h_j(W_j)) dt_j` … both equations hold integrated from zero, with the correct coincident seed values".

In the small-curve direction of A.1 the image word contains the small curve's own seeds, which start **at** the image
driver: a real point equal to the image start has no forward solution at time `0`, so a seed is not a frozen-chart mark
and PROVE-A1-FORCES's canonical force `rForceSnd` does not cover it (FORCES "What remains" 2). This file supplies a
canonical, measurable seed force and identifies it with the seed's force coordinate:

* **`centredSeed_right`** (deterministic): if `û ≥ 0` solves the centred real Loewner equation from `û(0) = 0` and is
  positive at positive times, then the real point `ε > 0` is alive up to the horizon and its centred flow stays in
  `[û, û + ε]` (aliveness by GB7a's continuation along a force coordinate, `GB7a.exists_isForwardSol_of_le`; both
  bounds by Aux. 25's forward comparison of centred solutions, `Aux25.sub_le_max_of_centredEq`);
  **`centredSeed_left`** is the reflection;
* **`seed_right_image`**, **`seed_left_image`**: the same for an uncentred continuous driver `I` and a force coordinate
  `X` from the image start (`X(0) = I(0)`) solving the integrated force equation: the image of `I(0) ± ε` is alive and
  within `ε` of `X`;
* **`seedPt`**, **`canonSeed`**: the canonical seed force on the side `sgn = ±1`, the limit of A1-FORCES's masked
  canonical forces `canonForce` at the frozen-chart points `I(0) + sgn/(n+1)` (`I` the canonical image driver);
  **`A1Marg.CanonHyp.measurable_canonSeed`**: measurable under A1-MARG's `CanonHyp`;
* **`canonSeed_right_eq`**, **`canonSeed_left_eq`**: on the live event before the canonical image lifetime the
  canonical seed force is `X(t) − I(0)` for every seed force coordinate `X` on its side;
  **`canonSeed_right_eq_of_geometry`**, **`canonSeed_left_eq_of_geometry`**: hence it is the seed coordinate of any
  seeded image geometry (`SeedImageGeometry`, e.g. A22's seeded capacity coordinates) whose capacity driver is the
  canonical image driver relative to its start (A1-FAMILY's `rDrv_eq_seedCapacityDriver`);
* **`rSeedSnd`**, **`measurable_rSeedSnd`**: the family seed force of the small-curve direction (mirror of A1-FORCES's
  `rForceSnd`), jointly measurable in the frozen time and the sample.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1LargeDens

open QuantumZipper (IsForwardSol fwdMap)

section Centred

variable {W : ℝ → ℝ} {T : ℝ} {u : ℝ → ℝ}

/-- **A real point right of a centred seed is alive and stays within its start of the seed.** Let `û ≥ 0` solve the
centred real Loewner equation of the driver `W` (`W 0 = 0`) on `[0, T]` from `û(0) = 0`, positive at positive times,
with integrable reciprocal. Then for `ε > 0` the real point `ε` is alive up to `T`, and its centred flow `v` satisfies
`û ≤ Re v ≤ û + ε` on `[0, T]`. -/
theorem centredSeed_right (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) (huc : ContinuousOn u (Icc 0 T))
    (hu0 : u 0 = 0) (hupos : ∀ s ∈ Ioc 0 T, 0 < u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 T) {ε : ℝ} (hε : 0 < ε) :
    ∃ v, IsForwardSol W (ε : ℂ) T v ∧ ∀ s ∈ Icc (0 : ℝ) T, u s ≤ (v s).re ∧ (v s).re ≤ u s + ε := by
  have hunn : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ u s := fun s hs => by
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, hu0]
    · exact (hupos s ⟨h, hs.2⟩).le
  have hnull : volume {s | s ∈ Icc (0 : ℝ) T ∧ u s = 0} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (measure_singleton (0 : ℝ))
    rcases hs.1.1.eq_or_lt with h | h
    · exact h.symm
    · exact absurd hs.2 (hupos s ⟨h, hs.1.2⟩).ne'
  -- aliveness
  have halive : ∃ v, IsForwardSol W (ε : ℂ) T v := by
    rcases hT.eq_or_lt with hT0 | hTpos
    · subst hT0
      exact InteractingSLE.exists_isForwardSol_zero hW0 hε.ne'
    -- a positive time up to which `ε` is alive
    obtain ⟨q₀, hq₀, hq₀T, v₀, hv₀⟩ : ∃ q₀ : ℝ, 0 < q₀ ∧ q₀ ≤ T ∧ ∃ v, IsForwardSol W (ε : ℂ) q₀ v := by
      by_cases hal : ∃ v, IsForwardSol W (ε : ℂ) T v
      · exact ⟨T, hTpos, le_rfl, hal⟩
      · obtain ⟨σ, hσ, hsw⟩ := InteractingSLE.exists_realSwallowAt hW hW0 hε hT hal
        exact ⟨σ / 2, by linarith [hσ.1], by linarith [hσ.1, hσ.2],
          hsw.2.1 (σ / 2) ⟨by linarith [hσ.1], by linarith [hσ.1]⟩⟩
    -- a positive time at which the flow is still right of the seed
    have hfc : ContinuousOn (fun s => (v₀ s).re - u s) (Icc 0 q₀) :=
      (Complex.continuous_re.comp_continuousOn hv₀.1).sub (huc.mono (Icc_subset_Icc_right hq₀T))
    have hf0 : (v₀ 0).re - u 0 = ε := by
      rw [QuantumZipper.FwdHolo.sol_zero hv₀ hq₀.le, hu0, hW0]
      simp
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hfc 0 ⟨le_rfl, hq₀.le⟩) ε hε
    set q := min q₀ (δ / 2) with hqdef
    have hq : 0 < q := lt_min hq₀ (by linarith)
    have hqq₀ : q ≤ q₀ := min_le_left _ _
    have huq : u q ≤ (v₀ q).re := by
      have h := hδf (x := q) ⟨hq.le, hqq₀⟩ (by
        rw [Real.dist_eq, sub_zero, abs_of_pos hq]; exact (min_le_right _ _).trans_lt (by linarith))
      rw [hf0, Real.dist_eq] at h
      have := (abs_lt.1 h).1
      linarith
    -- the seed is bounded below on `[q, T]`
    obtain ⟨sm, hsm, hsmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (hqq₀.trans hq₀T))
      (huc.mono (Icc_subset_Icc_left hq.le))
    have hc : 0 < u sm := hupos sm ⟨hq.trans_le hsm.1, hsm.2⟩
    refine GB7a.exists_isForwardSol_of_le hW hW0 hε hq.le (hqq₀.trans hq₀T)
      (QuantumZipper.isForwardSol_restrict hv₀ hq.le hqq₀) hc (u := u) (fun s hs => ⟨?_, ?_, ?_⟩)
      (fun s hs => hsmin ⟨hs.1, hs.2.le⟩) huq
    · exact huc.mono (Icc_subset_Icc hq.le hs.2.le)
    · exact fun s₁ h₁ s₂ h₂ h₁₂ => hueq s₁ ⟨hq.le.trans h₁.1, h₁.2.trans hs.2.le⟩ s₂
        ⟨hq.le.trans h₂.1, h₂.2.trans hs.2.le⟩ h₁₂
    · exact huint.mono_set (by
        rw [uIcc_of_le hs.1, uIcc_of_le hT]; exact Icc_subset_Icc hq.le hs.2.le)
  obtain ⟨v, hv⟩ := halive
  refine ⟨v, hv, fun s hs => ?_⟩
  obtain ⟨X, hXc, hXv, hX0, hXeq, hXint⟩ := Aux25.exists_real_of_isForwardSol hW hT hv
  rw [hW0, sub_zero] at hX0
  have hXpos : ∀ r ∈ Icc (0 : ℝ) T, 0 < X r :=
    Aux25.pos_of_ne_zero_of_pos hXc (fun r hr => (hXv r hr).1) (by rw [hX0]; exact hε)
  have hXnull : volume {r | r ∈ Icc (0 : ℝ) T ∧ X r = 0} = 0 := by
    refine measure_mono_null (fun r hr => ?_) measure_empty
    exact absurd hr.2 (hXpos r hr.1).ne'
  have hup := Aux25.sub_le_max_of_centredEq huc hunn hueq huint hnull hXc hXeq hXint s hs
  have hlo := Aux25.sub_le_max_of_centredEq hXc (fun r hr => (hXpos r hr).le) hXeq hXint hXnull huc hueq
    huint s hs
  rw [(hXv s hs).2, Complex.ofReal_re]
  rw [hX0, hu0, sub_zero, max_eq_left hε.le] at hup
  rw [hX0, hu0, zero_sub, max_eq_right (by linarith)] at hlo
  exact ⟨by linarith, by linarith⟩

/-- **The left seed** (reflection of `centredSeed_right`): for `û ≤ 0` from `û(0) = 0`, negative at positive times, the
real point `−ε` is alive up to `T` and its centred flow stays in `[û − ε, û]`. -/
theorem centredSeed_left (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) (huc : ContinuousOn u (Icc 0 T))
    (hu0 : u 0 = 0) (hupos : ∀ s ∈ Ioc 0 T, u s < 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 T) {ε : ℝ} (hε : 0 < ε) :
    ∃ v, IsForwardSol W ((-ε : ℝ) : ℂ) T v ∧ ∀ s ∈ Icc (0 : ℝ) T, u s - ε ≤ (v s).re ∧ (v s).re ≤ u s := by
  have hneg : ∀ a b : ℝ, ∫ s in a..b, 2 / -u s = -∫ s in a..b, 2 / u s := fun a b => by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext s
    rw [div_neg]
  obtain ⟨v, hv, hb⟩ := centredSeed_right (W := fun s => -W s) (u := fun s => -u s) hW.neg
    (by rw [hW0, neg_zero]) hT huc.neg (by rw [hu0, neg_zero]) (fun s hs => neg_pos.2 (hupos s hs))
    (fun s₁ h₁ s₂ h₂ h₁₂ => by rw [hneg]; linarith [hueq s₁ h₁ s₂ h₂ h₁₂])
    (by
      have e : (fun s => 2 / -u s) = -(fun s => 2 / u s) := by funext s; simp [div_neg]
      rw [e]; exact huint.neg) hε
  have hv' := QuantumZipper.RS.isForwardSol_neg hv
  simp only [neg_neg] at hv'
  refine ⟨_, by convert hv' using 2; push_cast; ring, fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hb s hs
  simp only [Complex.neg_re]
  constructor <;> linarith

end Centred

/-! ### Seeds of an uncentred image driver -/

section Image

variable {I : ℝ → ℝ} {T : ℝ} {X : ℝ → ℝ}

/-- The integrated force equation from `X(0) = I(0)` is the centred equation of `X − I` for the driver `I − I(0)`. -/
theorem centredEq_of_forceEq (hXeq : ∀ s ∈ Icc (0 : ℝ) T, X s = X 0 + ∫ r in (0 : ℝ)..s, 2 / (X r - I r))
    (hXint : IntervalIntegrable (fun r => 2 / (X r - I r)) volume 0 T) :
    ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
      (X s₂ - I s₂) - (X s₁ - I s₁) = -((I s₂ - I 0) - (I s₁ - I 0)) + ∫ r in s₁..s₂, 2 / (X r - I r) := by
  intro s₁ h₁ s₂ h₂ _
  have hi : ∀ c ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun r => 2 / (X r - I r)) volume 0 c := fun c hc =>
    hXint.mono_set (by rw [uIcc_of_le hc.1, uIcc_of_le (hc.1.trans hc.2)]; exact Icc_subset_Icc_right hc.2)
  rw [← intervalIntegral.integral_interval_sub_left (hi s₂ h₂) (hi s₁ h₁)]
  have e₁ := hXeq s₁ h₁
  have e₂ := hXeq s₂ h₂
  linarith

/-- **A right seed of an uncentred driver.** Let `I` be continuous and `X` a force coordinate from the image start
(`X(0) = I(0)`), strictly right of the driver at positive times, solving the integrated force equation. Then for
`ε > 0` the real point `I(0) + ε` is alive up to `T` and its image stays in `[X, X + ε]`. -/
theorem seed_right_image (hI : Continuous I) (hT : 0 ≤ T) (hXc : ContinuousOn X (Icc 0 T)) (hX0 : X 0 = I 0)
    (hXgt : ∀ s ∈ Ioc 0 T, I s < X s)
    (hXeq : ∀ s ∈ Icc (0 : ℝ) T, X s = X 0 + ∫ r in (0 : ℝ)..s, 2 / (X r - I r))
    (hXint : IntervalIntegrable (fun r => 2 / (X r - I r)) volume 0 T) {ε : ℝ} (hε : 0 < ε) :
    (∃ v, IsForwardSol I ((I 0 + ε : ℝ) : ℂ) T v) ∧ ∀ s ∈ Icc (0 : ℝ) T,
      X s ≤ (fwdMap I s ((I 0 + ε : ℝ) : ℂ)).re + I s ∧
        (fwdMap I s ((I 0 + ε : ℝ) : ℂ)).re + I s ≤ X s + ε := by
  obtain ⟨v, hv, hb⟩ := centredSeed_right (W := fun s => I s - I 0) (u := fun s => X s - I s)
    (hI.sub continuous_const) (sub_self _) hT (hXc.sub hI.continuousOn) (by rw [hX0, sub_self])
    (fun s hs => sub_pos.2 (hXgt s hs)) (centredEq_of_forceEq hXeq hXint) hXint hε
  have hv' : IsForwardSol I ((I 0 + ε : ℝ) : ℂ) T v :=
    isForwardSol_sub_const_iff.1 (by convert hv using 2; ring)
  refine ⟨⟨v, hv'⟩, fun s hs => ?_⟩
  rw [InteractingSLE.fwdMap_eq_of_isForwardSol hI hv' hs]
  obtain ⟨h1, h2⟩ := hb s hs
  constructor <;> linarith

/-- **A left seed of an uncentred driver** (mirror of `seed_right_image`): the image of `I(0) − ε` is alive and stays
in `[X − ε, X]`. -/
theorem seed_left_image (hI : Continuous I) (hT : 0 ≤ T) (hXc : ContinuousOn X (Icc 0 T)) (hX0 : X 0 = I 0)
    (hXlt : ∀ s ∈ Ioc 0 T, X s < I s)
    (hXeq : ∀ s ∈ Icc (0 : ℝ) T, X s = X 0 + ∫ r in (0 : ℝ)..s, 2 / (X r - I r))
    (hXint : IntervalIntegrable (fun r => 2 / (X r - I r)) volume 0 T) {ε : ℝ} (hε : 0 < ε) :
    (∃ v, IsForwardSol I ((I 0 - ε : ℝ) : ℂ) T v) ∧ ∀ s ∈ Icc (0 : ℝ) T,
      X s - ε ≤ (fwdMap I s ((I 0 - ε : ℝ) : ℂ)).re + I s ∧
        (fwdMap I s ((I 0 - ε : ℝ) : ℂ)).re + I s ≤ X s := by
  obtain ⟨v, hv, hb⟩ := centredSeed_left (W := fun s => I s - I 0) (u := fun s => X s - I s)
    (hI.sub continuous_const) (sub_self _) hT (hXc.sub hI.continuousOn) (by rw [hX0, sub_self])
    (fun s hs => sub_neg.2 (hXlt s hs)) (centredEq_of_forceEq hXeq hXint) hXint hε
  have hv' : IsForwardSol I ((I 0 - ε : ℝ) : ℂ) T v :=
    isForwardSol_sub_const_iff.1 (by convert hv using 2; ring)
  refine ⟨⟨v, hv'⟩, fun s hs => ?_⟩
  rw [InteractingSLE.fwdMap_eq_of_isForwardSol hI hv' hs]
  obtain ⟨h1, h2⟩ := hb s hs
  constructor <;> linarith

end Image

/-! ### The canonical seed force of the masked canonical image chain -/

section Canon

variable {Ω : Type*}

/-- The frozen-chart point `I(0) + e` beside the canonical image start `I(0)` (masked by the live event `L`). -/
def seedPt (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) (e : ℝ)
    (ω : Ω) : ℝ :=
  L.indicator (fun ω => A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0) ω + e

/-- **The canonical seed force** on the side `sgn` (`1`: right seed, `−1`: left seed): the limit of the masked canonical
forces (A1-FORCES's `canonForce`, relative to the image start) of the frozen-chart points `I(0) + sgn/(n+1)`. -/
def canonSeed (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0)
    (sgn : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop fun n : ℕ =>
    A1Forces.canonForce L xj xk wj ζj wk τ (seedPt L xj xk wj ζj wk τ (sgn / ((n : ℝ) + 1))) t ω

/-- **The canonical seed force is measurable** under A1-MARG's `CanonHyp`. -/
theorem _root_.InteractingSLE.ZhanGT4.A1Marg.CanonHyp.measurable_canonSeed [MeasurableSpace Ω] {L : Set Ω}
    {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞} {wk : Ω → ℝ≥0 → ℝ} {ζk : Ω → ℝ≥0∞} {τ : Ω → ℝ≥0}
    (hC : A1Marg.CanonHyp L wj ζj wk ζk τ) (xj xk sgn : ℝ) (t : ℝ≥0) :
    Measurable (canonSeed L xj xk wj ζj wk τ sgn t) := by
  have hp (e : ℝ) : Measurable (seedPt L xj xk wj ζj wk τ e) :=
    (hC.measurable_imgDrv_at xj xk le_rfl).add_const e
  exact (StronglyMeasurable.limUnder fun n : ℕ =>
    (hC.measurable_canonForce xj xk (hp (sgn / ((n : ℝ) + 1))) t).stronglyMeasurable).measurable

variable {L : Set Ω} {xj xk : ℝ} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞} {wk : Ω → ℝ≥0 → ℝ} {τ : Ω → ℝ≥0}
  {ω : Ω} {t : ℝ≥0}

/-- The masked canonical force of a frozen-chart point alive for the stopped canonical image driver is its image
relative to the image start. -/
theorem canonForce_eq_stopDrv (hω : ω ∈ L)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T))
    (hj0 : Strip.extPath (wj ω) 0 = 0) (hk : ∃ τ', (τ ω : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ'))
    (hk0 : Strip.extPath (wk ω) 0 = 0)
    (ht : ENNReal.ofReal t < A1Ref.imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
    {p : Ω → ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol (A1Ref.stopDrv (A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω))
      (τ ω)) t) (p ω : ℂ) t v) :
    A1Forces.canonForce L xj xk wj ζj wk τ p t ω =
      (fwdMap (A1Ref.stopDrv (A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)) t)
        t (p ω : ℂ)).re + A1Ref.stopDrv (A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω))
          (τ ω)) t t - A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0 := by
  set I := A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) with hIdef
  have heq : EqOn (A1Ref.stopDrv I t) I (Icc 0 t) := A1Ref.stopDrv_eqOn I t
  have hv' : IsForwardSol I (p ω : ℂ) t v := QuantumZipper.isForwardSol_congr_drive (fun r hr => heq hr) hv
  rw [A1Forces.canonForce_eq_imgForce hω hj hj0 hk hk0 ht hv', A1MultiMark.imgForce,
    InteractingSLE.Ito.fwdMap_congr_of_eqOn_of_le heq.symm le_rfl, heq ⟨t.coe_nonneg, le_rfl⟩]

/-- **The canonical seed force is the seed's force coordinate** (right seed). On the live event before the canonical
image lifetime, if a force coordinate `X` from the image start (`X(0) = I(0)`, `I` the canonical image driver) is
strictly right of the driver at positive times up to `t` and solves the integrated force equation there, then the
canonical right seed force at `t` is `X(t) − I(0)`. -/
theorem canonSeed_right_eq (hω : ω ∈ L)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T))
    (hj0 : Strip.extPath (wj ω) 0 = 0) (hk : ∃ τ', (τ ω : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ'))
    (hk0 : Strip.extPath (wk ω) 0 = 0)
    (ht : ENNReal.ofReal t < A1Ref.imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
    {X : ℝ → ℝ} (hXc : ContinuousOn X (Icc 0 t))
    (hX0 : X 0 = A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0)
    (hXgt : ∀ s ∈ Ioc (0 : ℝ) t, A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) s < X s)
    (hXeq : ∀ s ∈ Icc (0 : ℝ) t, X s = X 0 + ∫ r in (0 : ℝ)..s,
      2 / (X r - A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) r))
    (hXint : IntervalIntegrable (fun r => 2 / (X r -
      A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) r)) volume 0 t) :
    canonSeed L xj xk wj ζj wk τ 1 t ω =
      X t - A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0 := by
  set I := A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) with hIdef
  have hτ : (0 : ℝ) ≤ τ ω := (τ ω).coe_nonneg
  have hIc : ContinuousOn I (Icc 0 t) := A1Forces.continuousOn_imgDrv_Icc hj hj0 hk hk0 hτ ht
  set Is := A1Ref.stopDrv I t with hIsdef
  have hIs : Continuous Is := A1Ref.continuous_stopDrv hIc t.coe_nonneg
  have heq : EqOn Is I (Icc 0 t) := A1Ref.stopDrv_eqOn I t
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, t.coe_nonneg⟩
  have hIs0 : Is 0 = I 0 := heq h0
  have hsub : ∀ s ∈ Icc (0 : ℝ) t, X s - Is s = X s - I s := fun s hs => by rw [heq hs]
  have hXint' : IntervalIntegrable (fun r => 2 / (X r - Is r)) volume 0 t :=
    hXint.congr fun r hr => by
      rw [uIoc_of_le t.coe_nonneg] at hr
      simp only [hsub r ⟨hr.1.le, hr.2⟩]
  have hXeq' : ∀ s ∈ Icc (0 : ℝ) t, X s = X 0 + ∫ r in (0 : ℝ)..s, 2 / (X r - Is r) := fun s hs => by
    rw [hXeq s hs]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    simp only [hsub r ⟨hr.1, hr.2.trans hs.2⟩]
  have hpt : ∀ n : ℕ, seedPt L xj xk wj ζj wk τ (1 / ((n : ℝ) + 1)) ω = Is 0 + 1 / ((n : ℝ) + 1) := fun n => by
    rw [seedPt, indicator_of_mem hω, hIs0]
  have hval : ∀ n : ℕ, X t - I 0 ≤ A1Forces.canonForce L xj xk wj ζj wk τ
      (seedPt L xj xk wj ζj wk τ (1 / ((n : ℝ) + 1))) t ω ∧
      A1Forces.canonForce L xj xk wj ζj wk τ (seedPt L xj xk wj ζj wk τ (1 / ((n : ℝ) + 1))) t ω ≤
        X t - I 0 + 1 / ((n : ℝ) + 1) := fun n => by
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨⟨v, hv⟩, hb⟩ := seed_right_image hIs t.coe_nonneg hXc (hX0.trans hIs0.symm)
      (fun s hs => by rw [heq ⟨hs.1.le, hs.2⟩]; exact hXgt s hs) hXeq' hXint' hε
    rw [← hpt n] at hv hb
    rw [canonForce_eq_stopDrv hω hj hj0 hk hk0 ht hv]
    obtain ⟨h1, h2⟩ := hb t ⟨t.coe_nonneg, le_rfl⟩
    constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => A1Forces.canonForce L xj xk wj ζj wk τ
      (seedPt L xj xk wj ζj wk τ (1 / ((n : ℝ) + 1))) t ω) atTop (𝓝 (X t - I 0)) := by
    have hup : Tendsto (fun n : ℕ => X t - I 0 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (X t - I 0)) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [add_zero] using (tendsto_const_nhds (x := X t - I 0)).add h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hval n).1)
      fun n => (hval n).2
  exact hlim.limUnder_eq

/-- **The canonical seed force is the seed's force coordinate** (left seed, mirror of `canonSeed_right_eq`). -/
theorem canonSeed_left_eq (hω : ω ∈ L)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T))
    (hj0 : Strip.extPath (wj ω) 0 = 0) (hk : ∃ τ', (τ ω : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ'))
    (hk0 : Strip.extPath (wk ω) 0 = 0)
    (ht : ENNReal.ofReal t < A1Ref.imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
    {X : ℝ → ℝ} (hXc : ContinuousOn X (Icc 0 t))
    (hX0 : X 0 = A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0)
    (hXlt : ∀ s ∈ Ioc (0 : ℝ) t, X s < A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) s)
    (hXeq : ∀ s ∈ Icc (0 : ℝ) t, X s = X 0 + ∫ r in (0 : ℝ)..s,
      2 / (X r - A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) r))
    (hXint : IntervalIntegrable (fun r => 2 / (X r -
      A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) r)) volume 0 t) :
    canonSeed L xj xk wj ζj wk τ (-1) t ω =
      X t - A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0 := by
  set I := A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) with hIdef
  have hτ : (0 : ℝ) ≤ τ ω := (τ ω).coe_nonneg
  have hIc : ContinuousOn I (Icc 0 t) := A1Forces.continuousOn_imgDrv_Icc hj hj0 hk hk0 hτ ht
  set Is := A1Ref.stopDrv I t with hIsdef
  have hIs : Continuous Is := A1Ref.continuous_stopDrv hIc t.coe_nonneg
  have heq : EqOn Is I (Icc 0 t) := A1Ref.stopDrv_eqOn I t
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, t.coe_nonneg⟩
  have hIs0 : Is 0 = I 0 := heq h0
  have hsub : ∀ s ∈ Icc (0 : ℝ) t, X s - Is s = X s - I s := fun s hs => by rw [heq hs]
  have hXint' : IntervalIntegrable (fun r => 2 / (X r - Is r)) volume 0 t :=
    hXint.congr fun r hr => by
      rw [uIoc_of_le t.coe_nonneg] at hr
      simp only [hsub r ⟨hr.1.le, hr.2⟩]
  have hXeq' : ∀ s ∈ Icc (0 : ℝ) t, X s = X 0 + ∫ r in (0 : ℝ)..s, 2 / (X r - Is r) := fun s hs => by
    rw [hXeq s hs]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    simp only [hsub r ⟨hr.1, hr.2.trans hs.2⟩]
  have hpt : ∀ n : ℕ, seedPt L xj xk wj ζj wk τ (-1 / ((n : ℝ) + 1)) ω = Is 0 - 1 / ((n : ℝ) + 1) := fun n => by
    rw [seedPt, indicator_of_mem hω, hIs0, neg_div, ← sub_eq_add_neg]
  have hval : ∀ n : ℕ, X t - I 0 - 1 / ((n : ℝ) + 1) ≤ A1Forces.canonForce L xj xk wj ζj wk τ
      (seedPt L xj xk wj ζj wk τ (-1 / ((n : ℝ) + 1))) t ω ∧
      A1Forces.canonForce L xj xk wj ζj wk τ (seedPt L xj xk wj ζj wk τ (-1 / ((n : ℝ) + 1))) t ω ≤
        X t - I 0 := fun n => by
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨⟨v, hv⟩, hb⟩ := seed_left_image hIs t.coe_nonneg hXc (hX0.trans hIs0.symm)
      (fun s hs => by rw [heq ⟨hs.1.le, hs.2⟩]; exact hXlt s hs) hXeq' hXint' hε
    rw [← hpt n] at hv hb
    rw [canonForce_eq_stopDrv hω hj hj0 hk hk0 ht hv]
    obtain ⟨h1, h2⟩ := hb t ⟨t.coe_nonneg, le_rfl⟩
    constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => A1Forces.canonForce L xj xk wj ζj wk τ
      (seedPt L xj xk wj ζj wk τ (-1 / ((n : ℝ) + 1))) t ω) atTop (𝓝 (X t - I 0)) := by
    have hlo : Tendsto (fun n : ℕ => X t - I 0 - 1 / ((n : ℝ) + 1)) atTop (𝓝 (X t - I 0)) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [sub_zero] using (tendsto_const_nhds (x := X t - I 0)).sub h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun n => (hval n).1)
      fun n => (hval n).2
  exact hlim.limUnder_eq

/-- **The canonical right seed force is the seeded geometry's seed coordinate.** If the canonical image driver is,
up to `t ≤ T`, the capacity driver `w` of a seeded image geometry translated to the image start, then the canonical
right seed force at `t` is the geometry's right force coordinate of every right mark starting at the image start
(`xR j = 0`, a seed). -/
theorem canonSeed_right_eq_of_geometry (hω : ω ∈ L)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T))
    (hj0 : Strip.extPath (wj ω) 0 = 0) (hk : ∃ τ', (τ ω : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ'))
    (hk0 : Strip.extPath (wk ω) 0 = 0)
    (ht : ENNReal.ofReal t < A1Ref.imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}
    (hgeo : SeedImageGeometry xL xR ρL ρR w vL vR T) (j : Fin nR) (hxj : xR j = 0) (htT : t ≤ T)
    (hI : ∀ s ∈ Icc (0 : ℝ) t, A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) s =
      w s.toNNReal + A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0) :
    canonSeed L xj xk wj ζj wk τ 1 t ω = vR j t := by
  set I := A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) with hIdef
  have hle : ∀ s ∈ Icc (0 : ℝ) t, s.toNNReal ≤ T := fun s hs =>
    (Real.toNNReal_le_iff_le_coe.2 hs.2).trans htT
  have hgap : ∀ s ∈ Icc (0 : ℝ) t, (vR j s.toNNReal + I 0) - I s = vR j s.toNNReal - w s.toNNReal :=
    fun s hs => by rw [hI s hs]; ring
  have hint : IntervalIntegrable (fun r => 2 / ((vR j r.toNNReal + I 0) - I r)) volume 0 t := by
    have h := ((hgeo.integrable_right t htT j).const_mul (-2))
    refine h.congr fun r hr => ?_
    rw [uIoc_of_le t.coe_nonneg] at hr
    simp only [hgap r ⟨hr.1.le, hr.2⟩]
    rw [← neg_sub (w r.toNNReal), div_neg, ← neg_div, div_eq_mul_inv]
  rw [canonSeed_right_eq hω hj hj0 hk hk0 ht (X := fun s => vR j s.toNNReal + I 0)
    (((hgeo.continuous_right j).comp continuous_real_toNNReal).add continuous_const).continuousOn
    (by
      show vR j (0 : ℝ).toNNReal + I 0 = I 0
      simp only [Real.toNNReal_zero, hgeo.right_zero, hxj, zero_add])
    (fun s hs => by
      have h := hgeo.right_gt s.toNNReal (Real.toNNReal_pos.2 hs.1) (hle s ⟨hs.1.le, hs.2⟩) j
      show I s < vR j s.toNNReal + I 0
      rw [hI s ⟨hs.1.le, hs.2⟩]
      linarith)
    (fun s hs => by
      show vR j s.toNNReal + I 0 = (vR j (0 : ℝ).toNNReal + I 0) +
        ∫ r in (0 : ℝ)..s, 2 / ((vR j r.toNNReal + I 0) - I r)
      have h1 : ∫ r in (0 : ℝ)..s, 2 / ((vR j r.toNNReal + I 0) - I r) =
          ∫ r in (0 : ℝ)..s, 2 / (vR j r.toNNReal - w r.toNNReal) :=
        intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le hs.1] at hr
          simp only [hgap r ⟨hr.1, hr.2.trans hs.2⟩]
      rw [h1, Real.toNNReal_zero, hgeo.right_zero, hxj, hgeo.force_right s.toNNReal (hle s hs) j, hxj,
        Real.coe_toNNReal _ hs.1]
      ring)
    hint]
  show vR j (t : ℝ).toNNReal + I 0 - I 0 = vR j t
  rw [Real.toNNReal_coe, add_sub_cancel_right]

/-- **The canonical left seed force is the seeded geometry's seed coordinate** (mirror of
`canonSeed_right_eq_of_geometry`, a left mark starting at the image start, `xL i = 0`). -/
theorem canonSeed_left_eq_of_geometry (hω : ω ∈ L)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T))
    (hj0 : Strip.extPath (wj ω) 0 = 0) (hk : ∃ τ', (τ ω : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ'))
    (hk0 : Strip.extPath (wk ω) 0 = 0)
    (ht : ENNReal.ofReal t < A1Ref.imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}
    (hgeo : SeedImageGeometry xL xR ρL ρR w vL vR T) (i : Fin nL) (hxi : xL i = 0) (htT : t ≤ T)
    (hI : ∀ s ∈ Icc (0 : ℝ) t, A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) s =
      w s.toNNReal + A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0) :
    canonSeed L xj xk wj ζj wk τ (-1) t ω = vL i t := by
  set I := A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) with hIdef
  have hle : ∀ s ∈ Icc (0 : ℝ) t, s.toNNReal ≤ T := fun s hs =>
    (Real.toNNReal_le_iff_le_coe.2 hs.2).trans htT
  have hgap : ∀ s ∈ Icc (0 : ℝ) t, (vL i s.toNNReal + I 0) - I s = vL i s.toNNReal - w s.toNNReal :=
    fun s hs => by rw [hI s hs]; ring
  have hint : IntervalIntegrable (fun r => 2 / ((vL i r.toNNReal + I 0) - I r)) volume 0 t := by
    have h := ((hgeo.integrable_left t htT i).const_mul (-2))
    refine h.congr fun r hr => ?_
    rw [uIoc_of_le t.coe_nonneg] at hr
    simp only [hgap r ⟨hr.1.le, hr.2⟩]
    rw [← neg_sub (w r.toNNReal), div_neg, ← neg_div, div_eq_mul_inv]
  rw [canonSeed_left_eq hω hj hj0 hk hk0 ht (X := fun s => vL i s.toNNReal + I 0)
    (((hgeo.continuous_left i).comp continuous_real_toNNReal).add continuous_const).continuousOn
    (by
      show vL i (0 : ℝ).toNNReal + I 0 = I 0
      simp only [Real.toNNReal_zero, hgeo.left_zero, hxi, zero_add])
    (fun s hs => by
      have h := hgeo.left_lt s.toNNReal (Real.toNNReal_pos.2 hs.1) (hle s ⟨hs.1.le, hs.2⟩) i
      show vL i s.toNNReal + I 0 < I s
      rw [hI s ⟨hs.1.le, hs.2⟩]
      linarith)
    (fun s hs => by
      show vL i s.toNNReal + I 0 = (vL i (0 : ℝ).toNNReal + I 0) +
        ∫ r in (0 : ℝ)..s, 2 / ((vL i r.toNNReal + I 0) - I r)
      have h1 : ∫ r in (0 : ℝ)..s, 2 / ((vL i r.toNNReal + I 0) - I r) =
          ∫ r in (0 : ℝ)..s, 2 / (vL i r.toNNReal - w r.toNNReal) :=
        intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le hs.1] at hr
          simp only [hgap r ⟨hr.1, hr.2.trans hs.2⟩]
      rw [h1, Real.toNNReal_zero, hgeo.left_zero, hxi, hgeo.force_left s.toNNReal (hle s hs) i, hxi,
        Real.coe_toNNReal _ hs.1]
      ring)
    hint]
  show vL i (t : ℝ).toNNReal + I 0 - I 0 = vL i t
  rw [Real.toNNReal_coe, add_sub_cancel_right]

end Canon

/-! ### The family seed force of the small-curve direction -/

section Family

variable {X Y : Type*}

/-- **The family seed force** (conditioning curve on `Y`, image curve on `X`; mirror of A1-FORCES's `rForceSnd`): the
canonical seed force on the side `sgn` of the image of curve `j` in the frozen chart of curve `k` stopped at `τ`, masked
by the live event. In A.1's small-curve direction these are the forces of the small curve's seeds (`sgn = 1`: the right
seed, `sgn = −1`: the left seed). -/
abbrev rSeedSnd (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ)
    (τ : Y → ℝ≥0) (sgn : ℝ) : ℝ≥0 → X × Y → ℝ :=
  canonSeed {z : X × Y | live (τ z.2) z.2} xj xk (fun z t => Wj t z.1) (fun z => ζj z.1) (fun z t => Wk t z.2)
    (fun z => τ z.2) sgn

/-- **`FrozenFamily.measurable_VL`/`measurable_VR` for the seeds**: the family seed force at the deterministic frozen
time `σ` is jointly measurable in `(σ, z)` (A1-MARG's standing hypotheses on the two drivers, as in
`A1Forces.measurable_rForceSnd`). -/
theorem measurable_rSeedSnd [MeasurableSpace X] [MeasurableSpace Y] {live : ℝ≥0 → Y → Prop}
    (hlive : MeasurableSet {q : ℝ≥0 × Y | live q.1 q.2}) {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
    {Wk : ℝ≥0 → Y → ℝ} {ζk : Y → ℝ≥0∞} (hlk : ∀ s y, live s y → (s : ℝ≥0∞) < ζk y)
    (hjc : ∀ x, ContinuousOn (Wj · x) {t | (t : ℝ≥0∞) < ζj x}) (hj0 : ∀ x, Wj 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk · y) {t | (t : ℝ≥0∞) < ζk y}) (hk0 : ∀ y, Wk 0 y = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk)
    (xj xk sgn : ℝ) (t : ℝ≥0) :
    Measurable fun q : ℝ≥0 × (X × Y) => rSeedSnd live xj Wj ζj xk Wk (fun _ => q.1) sgn t q.2 := by
  have hC := A1Marg.canonHyp_of_paths (Ω := ℝ≥0 × (X × Y)) (πj := fun q => q.2.1) (πk := fun q => q.2.2)
    (τ := Prod.fst) measurable_snd.fst measurable_snd.snd measurable_fst hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk
  exact hC.measurable_canonSeed xj xk sgn t

end Family

end InteractingSLE.ZhanGT4.A1LargeDens
