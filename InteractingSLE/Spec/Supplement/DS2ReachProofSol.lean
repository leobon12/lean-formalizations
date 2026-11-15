/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofLimit

/-!
# DS2 in reach form, IX: the limit path solves the limiting integrated equations

Packet PROVE-T14-DS (proof of DS2, spec p. 553: "Thus the limiting force coordinates satisfy exactly
`dV_i = 2/(V_i − W) dt` with the integrated convention, and the driver has exactly the limiting weighted reciprocal
drift"). Deterministic: a pair `(f, β)` with `LimitProps` is, before its exit from the outer open buffer, a local
integrated path (`Sec2.IsSLEPathUpTo`) of the limiting word driven by `β` (`isSLEPathUpTo_of_limitProps`).

* `gap_facts`: a finite lintegral identity `∫₀^q Ginv(F) = A/2` makes the zero set of `F` null, `1/F` integrable,
  and `∫₀^q 1/F = A/2`;
* the equations at the times of `qSet` pass to all earlier times by continuity (`exists_seq_qSet`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2
open scoped PathMeas

theorem measurable_Ginv : Measurable Ginv := by
  unfold Ginv
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (ENNReal.measurable_ofReal.comp (measurable_const.div measurable_id)) measurable_const

/-- **From the lintegral identity to the Bochner integral.** -/
theorem gap_facts {F : ℝ → ℝ} (hF : Continuous F) {q A : ℝ} (hA : 0 ≤ A)
    (h : ∫⁻ r in Ioc (0 : ℝ) q, Ginv (F r) = ENNReal.ofReal (A / 2)) :
    (∀ᵐ r ∂volume, r ∈ Ioc (0 : ℝ) q → 0 < F r) ∧ IntegrableOn (fun r => (F r)⁻¹) (Ioc 0 q) ∧
      ∫ r in Ioc (0 : ℝ) q, (F r)⁻¹ = A / 2 := by
  have hm : Measurable fun r => Ginv (F r) := measurable_Ginv.comp hF.measurable
  have hfin : ∫⁻ r in Ioc (0 : ℝ) q, Ginv (F r) ≠ ⊤ := by rw [h]; exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) q), Ginv (F r) < ⊤ := ae_lt_top hm hfin
  have hpos : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) q), 0 < F r := hae.mono fun r hr => by
    by_contra hc
    simp only [Ginv, hc, ↓reduceIte, lt_self_iff_false] at hr
  have hpos' : ∀ᵐ r ∂volume, r ∈ Ioc (0 : ℝ) q → 0 < F r := (ae_restrict_iff' measurableSet_Ioc).1 hpos
  have heq : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) q), Ginv (F r) = ENNReal.ofReal ((F r)⁻¹) :=
    hpos.mono fun r hr => by simp only [Ginv, hr, ↓reduceIte, one_div]
  have hlin : ∫⁻ r in Ioc (0 : ℝ) q, ENNReal.ofReal ((F r)⁻¹) = ENNReal.ofReal (A / 2) := by
    rw [← h]; exact lintegral_congr_ae (heq.mono fun r hr => hr.symm)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) q)] fun r => (F r)⁻¹ :=
    hpos.mono fun r hr => (inv_pos.2 hr).le
  have hmeas : AEStronglyMeasurable (fun r => (F r)⁻¹) (volume.restrict (Ioc (0 : ℝ) q)) :=
    (hF.measurable.inv).aestronglyMeasurable
  have hint : IntegrableOn (fun r => (F r)⁻¹) (Ioc 0 q) :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 (by rw [hlin]; exact ENNReal.ofReal_lt_top)⟩
  refine ⟨hpos', hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, hlin, ENNReal.toReal_ofReal (by positivity)]

/-- Times of `qSet` strictly between `s` and `t`, decreasing to `s`. -/
theorem exists_seq_qSet {s t : ℝ≥0} (hst : s < t) :
    ∃ q : ℕ → ℝ≥0, (∀ n, q n ∈ qSet ∧ s < q n ∧ q n < t) ∧ Antitone q ∧ Tendsto q atTop (𝓝 s) := by
  obtain ⟨u, hu, hmem, hlim⟩ := qSet_dense.exists_seq_strictAnti_tendsto_of_lt hst
  exact ⟨u, fun n => ⟨(hmem n).2, (hmem n).1.1, (hmem n).1.2⟩, hu.antitone, hlim⟩

theorem exists_qSet_between {s t : ℝ≥0} (hst : s < t) : ∃ q ∈ qSet, s < q ∧ q < t := by
  obtain ⟨q, hq, -, -⟩ := exists_seq_qSet hst
  exact ⟨q 0, (hq 0).1, (hq 0).2.1, (hq 0).2.2⟩

/-! ### The equations at the times of `qSet` -/

section Facts

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {R g : ℝ} {T : ℝ≥0} {xL₀ : Fin nL → ℝ} {xR₀ : Fin nR → ℝ}
  {ρL₀ : Fin nL → ℝ} {ρR₀ : Fin nR → ℝ} {f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)}
  {β : C(Set.Icc (0 : ℝ≥0) T, ℝ)}

/-- The coordinates of a path, as functions on `ℝ≥0`. -/
def wF (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) (s : ℝ≥0) : ℝ := (pathAt f s).1

def vLF (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) (i : Fin nL) (s : ℝ≥0) : ℝ := (pathAt f s).2.1 i

def vRF (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) (j : Fin nR) (s : ℝ≥0) : ℝ := (pathAt f s).2.2 j

theorem continuous_wF (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) : Continuous (wF f) :=
  continuous_fst.comp (continuous_pathAt f)

theorem continuous_vLF (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) (i : Fin nL) : Continuous (vLF f i) :=
  (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp (continuous_pathAt f)))

theorem continuous_vRF (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) (j : Fin nR) : Continuous (vRF f j) :=
  (continuous_apply j).comp (continuous_snd.comp (continuous_snd.comp (continuous_pathAt f)))

/-- Staying in the outer open buffer before `t` gives `upSet q` for `q < t`. -/
theorem mem_upSet_of_lt {t q : ℝ≥0} (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g) (hq : q < t) :
    f ∈ upSet mL mR R g q := fun s hs => by
  have := hU s (lt_of_le_of_lt hs hq)
  rwa [pathAt_coe] at this

variable (hLP : LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ f β)
include hLP

theorem LimitProps.ordered (s : ℝ≥0) : IsOrderedState (pathAt f s) := hLP.2.1 _

/-- The right equations at a time `q ∈ qSet` before the exit. -/
theorem LimitProps.facts_R {t q : ℝ≥0} (ht : t ≤ T) (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g)
    (hqQ : q ∈ qSet) (hq : q < t) (j : Fin nR) :
    (∀ᵐ r ∂volume, r ∈ Ioc (0 : ℝ) q → 0 < vRF f j r.toNNReal - wF f r.toNNReal) ∧
      IntegrableOn (fun r : ℝ => (vRF f j r.toNNReal - wF f r.toNNReal)⁻¹) (Ioc 0 q) ∧
      vRF f j q = xR₀ j + ∫ r in (0 : ℝ)..q, 2 / (vRF f j r.toNNReal - wF f r.toNNReal) := by
  obtain ⟨-, hRj, -⟩ := hLP.2.2 q hqQ (hq.le.trans ht) (mem_upSet_of_lt hU hq)
  obtain ⟨hA, hlin⟩ := hRj j
  have hc : Continuous fun r : ℝ => gapR j (pathAt f r.toNNReal) :=
    (continuous_gapR j).comp ((continuous_pathAt f).comp continuous_real_toNNReal)
  obtain ⟨h1, h2, h3⟩ := gap_facts hc hA hlin
  refine ⟨h1, h2, ?_⟩
  have e0 : vRF f j 0 = xR₀ j := by simp only [vRF, hLP.1]
  rw [intervalIntegral.integral_of_le q.coe_nonneg]
  have e : (fun r : ℝ => 2 / (vRF f j r.toNNReal - wF f r.toNNReal)) =
      fun r => 2 * (gapR j (pathAt f r.toNNReal))⁻¹ := by
    funext r; rw [div_eq_mul_inv]; rfl
  rw [e, integral_const_mul]
  have h3' : ∫ r in Ioc (0 : ℝ) q, (gapR j (pathAt f r.toNNReal))⁻¹ =
      ((pathAt f q).2.2 j - (pathAt f 0).2.2 j) / 2 := h3
  rw [h3', ← e0]
  simp only [vRF]
  ring

/-- The left equations at a time `q ∈ qSet` before the exit. -/
theorem LimitProps.facts_L {t q : ℝ≥0} (ht : t ≤ T) (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g)
    (hqQ : q ∈ qSet) (hq : q < t) (i : Fin nL) :
    (∀ᵐ r ∂volume, r ∈ Ioc (0 : ℝ) q → 0 < wF f r.toNNReal - vLF f i r.toNNReal) ∧
      IntegrableOn (fun r : ℝ => (wF f r.toNNReal - vLF f i r.toNNReal)⁻¹) (Ioc 0 q) ∧
      vLF f i q = xL₀ i + ∫ r in (0 : ℝ)..q, 2 / (vLF f i r.toNNReal - wF f r.toNNReal) := by
  obtain ⟨-, -, hLi⟩ := hLP.2.2 q hqQ (hq.le.trans ht) (mem_upSet_of_lt hU hq)
  obtain ⟨hA, hlin⟩ := hLi i
  have hc : Continuous fun r : ℝ => gapL i (pathAt f r.toNNReal) :=
    (continuous_gapL i).comp ((continuous_pathAt f).comp continuous_real_toNNReal)
  obtain ⟨h1, h2, h3⟩ := gap_facts hc hA hlin
  refine ⟨h1, h2, ?_⟩
  have e0 : vLF f i 0 = xL₀ i := by simp only [vLF, hLP.1]
  rw [intervalIntegral.integral_of_le q.coe_nonneg]
  have e : (fun r : ℝ => 2 / (vLF f i r.toNNReal - wF f r.toNNReal)) =
      fun r => -(2 * (gapL i (pathAt f r.toNNReal))⁻¹) := by
    funext r
    simp only [gapL, vLF, wF]
    rw [← neg_sub, div_neg, div_eq_mul_inv]
  rw [e, integral_neg, integral_const_mul]
  have h3' : ∫ r in Ioc (0 : ℝ) q, (gapL i (pathAt f r.toNNReal))⁻¹ =
      ((pathAt f 0).2.1 i - (pathAt f q).2.1 i) / 2 := h3
  rw [h3', ← e0]
  simp only [vLF]
  ring

/-- The linear identity at a time `q ∈ qSet` before the exit. -/
theorem LimitProps.facts_lin {t q : ℝ≥0} (ht : t ≤ T)
    (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g) (hqQ : q ∈ qSet) (hq : q < t) :
    wF f q = Real.sqrt κ * pathAt β q - (∑ i, ρL₀ i / 2 * (vLF f i q - xL₀ i)) -
      ∑ j, ρR₀ j / 2 * (vRF f j q - xR₀ j) := by
  obtain ⟨hlin, -, -⟩ := hLP.2.2 q hqQ (hq.le.trans ht) (mem_upSet_of_lt hU hq)
  simp only [wF, vLF, vRF]
  rw [hlin, hLP.1]

omit hLP in
/-- Limits along `qSet` times: two continuous functions agreeing at the `qSet` times in `(s, t)` agree at `s`. -/
theorem eq_at_of_qSet {s t : ℝ≥0} (hst : s < t) {G H : ℝ≥0 → ℝ} (hG : ContinuousAt G s)
    (hH : ∀ q₀ ∈ qSet, s < q₀ → q₀ < t → ∀ q : ℕ → ℝ≥0, (∀ n, s < q n ∧ q n ≤ q₀) →
      Tendsto q atTop (𝓝 s) → Tendsto (fun n => H (q n)) atTop (𝓝 (H s)))
    (heq : ∀ q ∈ qSet, s < q → q < t → G q = H q) : G s = H s := by
  obtain ⟨q, hq, hanti, hlim⟩ := exists_seq_qSet hst
  have h1 : Tendsto (fun n => G (q n)) atTop (𝓝 (G s)) := hG.tendsto.comp hlim
  have h2 := hH (q 0) (hq 0).1 (hq 0).2.1 (hq 0).2.2 q (fun n => ⟨(hq n).2.1, hanti (Nat.zero_le n)⟩) hlim
  exact tendsto_nhds_unique h1 (h2.congr fun n => (heq (q n) (hq n).1 (hq n).2.1 (hq n).2.2).symm)

omit hLP in
/-- A primitive `x ↦ ∫₀^x φ` of a function integrable on `[0, q₀]` is continuous along sequences in `[0, q₀]`. -/
theorem tendsto_primitive {φ : ℝ → ℝ} {s q₀ : ℝ≥0} (hsq : s < q₀) (hint : IntegrableOn φ (Ioc 0 q₀))
    {q : ℕ → ℝ≥0} (hq : ∀ n, s < q n ∧ q n ≤ q₀) (hlim : Tendsto q atTop (𝓝 s)) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..(q n : ℝ), φ r) atTop (𝓝 (∫ r in (0 : ℝ)..(s : ℝ), φ r)) := by
  have hint' : IntegrableOn φ (Set.uIcc 0 (q₀ : ℝ)) := by
    rw [Set.uIcc_of_le q₀.coe_nonneg, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hint
  have hcont := intervalIntegral.continuousOn_primitive_interval hint'
  have hmem : ∀ x : ℝ≥0, x ≤ q₀ → (x : ℝ) ∈ Set.uIcc 0 (q₀ : ℝ) := fun x hx => by
    rw [Set.uIcc_of_le q₀.coe_nonneg]
    exact ⟨x.coe_nonneg, by exact_mod_cast hx⟩
  exact (hcont s (hmem s hsq.le)).tendsto.comp (tendsto_nhdsWithin_iff.2
    ⟨(NNReal.continuous_coe.tendsto _).comp hlim, Eventually.of_forall fun n => hmem _ (hq n).2⟩)

/-- **The right force equations before the exit.** -/
theorem LimitProps.vR_eq_at {t : ℝ≥0} (ht : t ≤ T) (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g)
    {s : ℝ≥0} (hs : s < t) (j : Fin nR) :
    vRF f j s = xR₀ j + ∫ r in (0 : ℝ)..s, 2 / (vRF f j r.toNNReal - wF f r.toNNReal) := by
  refine eq_at_of_qSet hs ((continuous_vRF f j).continuousAt) (fun q₀ hq₀ hsq hq₀t q hq hlim => ?_)
    fun q hqQ _ hqt => (hLP.facts_R ht hU hqQ hqt j).2.2
  refine tendsto_const_nhds.add (tendsto_primitive hsq ?_ hq hlim)
  have h2 : IntegrableOn (fun r : ℝ => 2 * (vRF f j r.toNNReal - wF f r.toNNReal)⁻¹) (Ioc 0 q₀) :=
    ((hLP.facts_R ht hU hq₀ hq₀t j).2.1).const_mul 2
  exact IntegrableOn.congr_fun h2 (fun r _ => (div_eq_mul_inv _ _).symm) measurableSet_Ioc

/-- **The left force equations before the exit.** -/
theorem LimitProps.vL_eq_at {t : ℝ≥0} (ht : t ≤ T) (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g)
    {s : ℝ≥0} (hs : s < t) (i : Fin nL) :
    vLF f i s = xL₀ i + ∫ r in (0 : ℝ)..s, 2 / (vLF f i r.toNNReal - wF f r.toNNReal) := by
  refine eq_at_of_qSet hs ((continuous_vLF f i).continuousAt) (fun q₀ hq₀ hsq hq₀t q hq hlim => ?_)
    fun q hqQ _ hqt => (hLP.facts_L ht hU hqQ hqt i).2.2
  refine tendsto_const_nhds.add (tendsto_primitive hsq ?_ hq hlim)
  have h2 : IntegrableOn (fun r : ℝ => -(2 * (wF f r.toNNReal - vLF f i r.toNNReal)⁻¹)) (Ioc 0 q₀) :=
    (((hLP.facts_L ht hU hq₀ hq₀t i).2.1).const_mul 2).neg
  refine IntegrableOn.congr_fun h2 (fun r _ => ?_) measurableSet_Ioc
  have e : vLF f i r.toNNReal - wF f r.toNNReal = -(wF f r.toNNReal - vLF f i r.toNNReal) := by ring
  show -(2 * (wF f r.toNNReal - vLF f i r.toNNReal)⁻¹) = 2 / (vLF f i r.toNNReal - wF f r.toNNReal)
  rw [e, div_neg, div_eq_mul_inv]

/-- **The linear driver identity before the exit.** -/
theorem LimitProps.lin_at {t : ℝ≥0} (ht : t ≤ T) (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g)
    {s : ℝ≥0} (hs : s < t) :
    wF f s = Real.sqrt κ * pathAt β s - (∑ i, ρL₀ i / 2 * (vLF f i s - xL₀ i)) -
      ∑ j, ρR₀ j / 2 * (vRF f j s - xR₀ j) := by
  have hc : Continuous fun s : ℝ≥0 => Real.sqrt κ * pathAt β s - (∑ i, ρL₀ i / 2 * (vLF f i s - xL₀ i)) -
      ∑ j, ρR₀ j / 2 * (vRF f j s - xR₀ j) :=
    ((continuous_const.mul (continuous_pathAt β)).sub (continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_vLF f i).sub continuous_const))).sub
      (continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_vRF f j).sub continuous_const))
  exact eq_at_of_qSet hs ((continuous_wF f).continuousAt)
    (fun _ _ _ _ q _ hlim => (hc.tendsto s).comp hlim) fun q hqQ _ hqt => hLP.facts_lin ht hU hqQ hqt

/-- **The limit path is a local integrated path of the limiting word before its exit from the outer open
buffer.** -/
theorem LimitProps.isSLEPathUpTo {Rw ε : ℝ} (hε : 0 < ε) (hg : 0 < g)
    (hw0 : IsDS1Word mL mR Rw ε xL₀ xR₀ ρL₀ ρR₀) {t : ℝ≥0} (ht : t ≤ T)
    (hU : ∀ s : ℝ≥0, s < t → pathAt f s ∈ oBuf mL mR R g) :
    Sec2.IsSLEPathUpTo κ xL₀ xR₀ ρL₀ ρR₀ (wF f) (vLF f) (vRF f) (pathAt β) (t : ℝ≥0∞) := by
  have hlt : ∀ {s : ℝ≥0}, (s : ℝ≥0∞) < t → s < t := fun h => by exact_mod_cast h
  have hord := hLP.ordered
  refine
    { w_zero := by simp only [wF, hLP.1]
      vL_zero := fun i => by simp only [vLF, hLP.1]
      vR_zero := fun j => by simp only [vRF, hLP.1]
      continuousOn_w := (continuous_wF f).continuousOn
      continuousOn_vL := fun i => (continuous_vLF f i).continuousOn
      continuousOn_vR := fun j => (continuous_vRF f j).continuousOn
      antitone_vL := fun {s} _ => (hord s).1
      vL_le_w := fun {s} _ i => (hord s).2.1 i
      w_le_vR := fun {s} _ j => (hord s).2.2.1 j
      monotone_vR := fun {s} _ => (hord s).2.2.2
      integrable_gapL := fun {s} hs i => ?_
      integrable_gapR := fun {s} hs j => ?_
      w_eq := fun {s} hs => ?_
      vL_eq := fun {s} hs i => hLP.vL_eq_at ht hU (hlt hs) i
      vR_eq := fun {s} hs j => hLP.vR_eq_at ht hU (hlt hs) j
      volume_collisionL := fun i => ?_
      volume_collisionR := fun j => ?_
      not_threshold := fun {s} hs => ?_ }
  · obtain ⟨q, hqQ, hsq, hqt⟩ := exists_qSet_between (hlt hs)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg]
    exact (hLP.facts_L ht hU hqQ hqt i).2.1.mono_set (Ioc_subset_Ioc le_rfl (by exact_mod_cast hsq.le))
  · obtain ⟨q, hqQ, hsq, hqt⟩ := exists_qSet_between (hlt hs)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg]
    have := ((hLP.facts_R ht hU hqQ hqt j).2.1.mono_set
      (Ioc_subset_Ioc le_rfl (by exact_mod_cast hsq.le))).neg
    refine IntegrableOn.congr_fun this (fun r _ => ?_) measurableSet_Ioc
    show -(vRF f j r.toNNReal - wF f r.toNNReal)⁻¹ = (wF f r.toNNReal - vRF f j r.toNNReal)⁻¹
    rw [← inv_neg, neg_sub]
  · -- the driving equation from the linear identity and the force equations
    have hl := hLP.lin_at ht hU (hlt hs)
    have hL : ∀ i, ∫ r in (0 : ℝ)..s, ρL₀ i / (wF f r.toNNReal - vLF f i r.toNNReal) =
        -(ρL₀ i / 2 * (vLF f i s - xL₀ i)) := by
      intro i
      simp_rw [div_sub_eq_neg_half_mul (ρL₀ i)]
      rw [intervalIntegral.integral_const_mul, hLP.vL_eq_at ht hU (hlt hs) i]
      ring
    have hR : ∀ j, ∫ r in (0 : ℝ)..s, ρR₀ j / (wF f r.toNNReal - vRF f j r.toNNReal) =
        -(ρR₀ j / 2 * (vRF f j s - xR₀ j)) := by
      intro j
      simp_rw [div_sub_eq_neg_half_mul (ρR₀ j)]
      rw [intervalIntegral.integral_const_mul, hLP.vR_eq_at ht hU (hlt hs) j]
      ring
    simp only [hL, hR, Finset.sum_neg_distrib]
    rw [hl]
    ring
  · -- the collision set is covered by countably many null sets
    have hsub : {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < t ∧ wF f r.toNNReal = vLF f i r.toNNReal} ⊆
        {0} ∪ ⋃ q ∈ qSet ∩ Iio t, {r : ℝ | r ∈ Ioc (0 : ℝ) q ∧ ¬ 0 < wF f r.toNNReal - vLF f i r.toNNReal} := by
      rintro r ⟨hr0, hrt, heq⟩
      rcases eq_or_lt_of_le hr0 with h | h
      · left; exact h.symm
      · right
        obtain ⟨q, hqQ, hrq, hqt⟩ := exists_qSet_between (hlt hrt)
        have hrq' : r ≤ q := by
          have e1 := Real.coe_toNNReal r hr0
          have h2 : (r.toNNReal : ℝ) ≤ q := by exact_mod_cast hrq.le
          linarith
        refine mem_iUnion₂.2 ⟨q, ⟨hqQ, hqt⟩, ⟨h, hrq'⟩, ?_⟩
        rw [heq, sub_self]
        exact lt_irrefl 0
    refine measure_mono_null hsub (measure_union_null (measure_singleton 0) ?_)
    refine (measure_biUnion_null_iff (qSet_countable.mono inter_subset_left)).2 fun q hq => ?_
    have h1 := (hLP.facts_L ht hU hq.1 hq.2 i).1
    exact measure_eq_zero_iff_ae_notMem.2 (h1.mono fun r hr hmem => hmem.2 (hr hmem.1))
  · have hsub : {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < t ∧ wF f r.toNNReal = vRF f j r.toNNReal} ⊆
        {0} ∪ ⋃ q ∈ qSet ∩ Iio t, {r : ℝ | r ∈ Ioc (0 : ℝ) q ∧ ¬ 0 < vRF f j r.toNNReal - wF f r.toNNReal} := by
      rintro r ⟨hr0, hrt, heq⟩
      rcases eq_or_lt_of_le hr0 with h | h
      · left; exact h.symm
      · right
        obtain ⟨q, hqQ, hrq, hqt⟩ := exists_qSet_between (hlt hrt)
        have hrq' : r ≤ q := by
          have e1 := Real.coe_toNNReal r hr0
          have h2 : (r.toNNReal : ℝ) ≤ q := by exact_mod_cast hrq.le
          linarith
        refine mem_iUnion₂.2 ⟨q, ⟨hqQ, hqt⟩, ⟨h, hrq'⟩, ?_⟩
        rw [heq, sub_self]
        exact lt_irrefl 0
    refine measure_mono_null hsub (measure_union_null (measure_singleton 0) ?_)
    refine (measure_biUnion_null_iff (qSet_countable.mono inter_subset_left)).2 fun q hq => ?_
    have h1 := (hLP.facts_R ht hU hq.1 hq.2 j).1
    exact measure_eq_zero_iff_ae_notMem.2 (h1.mono fun r hr hmem => hmem.2 (hr hmem.1))
  · have hmem := InBuffer.inCBuffer (hU s (hlt hs))
    exact not_threshold_of_inCBuffer hε (half_pos hg) hw0 (hord s) hmem

end Facts


end DSReach

end Supp12

end InteractingSLE
