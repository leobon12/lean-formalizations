/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedExistsPath

/-!
# Two seeds: good paths, the null augmentation, and the physical clock

Packet PROVE-SEC2-JAC3. Starting from a Jacobi diffusion `U` in a filtration `𝓗` on the
logarithmic clock:

* `goodSet U`: the paths with Lebesgue-null boundary set and divergent clock (full measure by
  `TwoSeedExistsPath`); `modU U` equals `U` on good paths and the constant path `1/2` elsewhere, so
  that **every** path of `modU U` is good;
* `augF 𝓗 P = 𝓗 ∨ 𝒩_P`: `modU U` is adapted to it, and the martingale identities of `nProc`,
  `qProc` (`TwoSeedExistsMart`) pass to `modU U` in `augF 𝓗 P`;
* `tauP U t = u(t)` (the inverse clock of `modU U`) is an `augF 𝓗 P`-stopping time for `t > 0`, and
  `physF` is the physical-time filtration `𝓖_t = (augF 𝓗 P)_{u(t)}` (`𝓖_0` trivial).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

open Jacobi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Good paths and the modification -/

/-- Paths with Lebesgue-null boundary set and unbounded clock. -/
def goodSet (U : ℝ → Ω → ℝ) : Set Ω :=
  {ω | volume {v | U v ω = 0 ∨ U v ω = 1} = 0} ∩
    ⋂ M : ℕ, ⋃ n : ℕ, {ω | (M : ℝ) ≤ clock (U · ω) n}

/-- `U` on good paths, the constant path `1/2` elsewhere. -/
def modU (U : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ := if ω ∈ goodSet U then U u ω else 1 / 2

theorem clock_half_ge (u : ℝ) (hu : 0 ≤ u) : u / 8 ≤ clock (fun _ => (1 : ℝ) / 2) u := by
  have h01 : ∀ v : ℝ, (fun _ => (1 : ℝ) / 2) v ∈ Icc (0 : ℝ) 1 := fun _ => by norm_num
  have hsub := clock_sub continuous_const h01 0 u
  have hnn := clock_nonneg h01 0
  have hint : u / 8 ≤ ∫ v in (0 : ℝ)..u, clockDensity (fun _ => (1 : ℝ) / 2) v := by
    have : ∫ v in (0 : ℝ)..u, (1 / 8 : ℝ) = u / 8 := by simp; ring
    rw [← this]
    refine intervalIntegral.integral_mono_on hu intervalIntegrable_const
      ((continuous_clockDensity continuous_const).intervalIntegrable _ _) fun v hv => ?_
    simp only [clockDensity]
    have := one_le_exp (show 0 ≤ 2 * v by linarith [hv.1])
    nlinarith
  linarith

variable {κ a b : ℝ} {P : Measure Ω} {𝓗 : Filtration ℝ mΩ} {U : ℝ → Ω → ℝ}

theorem tendsto_clock_of_mem_goodSet (hU : IsJacobiDiffusion κ a b P 𝓗 U) {ω : Ω}
    (hω : ω ∈ goodSet U) : Tendsto (clock (U · ω)) atTop atTop := by
  refine (monotone_clock (hU.continuous ω) fun v => hU.mem_Icc v ω).tendsto_atTop_atTop
    fun B => ?_
  obtain ⟨M, hM⟩ := exists_nat_ge B
  obtain ⟨n, hn⟩ := mem_iUnion.1 (mem_iInter.1 hω.2 M)
  exact ⟨n, hM.trans hn⟩

theorem modU_mem (hU : IsJacobiDiffusion κ a b P 𝓗 U) (u : ℝ) (ω : Ω) :
    modU U u ω ∈ Icc (0 : ℝ) 1 := by
  unfold modU; split_ifs
  · exact hU.mem_Icc u ω
  · norm_num

theorem continuous_modU (hU : IsJacobiDiffusion κ a b P 𝓗 U) (ω : Ω) :
    Continuous fun u => modU U u ω := by
  unfold modU; split_ifs
  · exact hU.continuous ω
  · exact continuous_const

theorem volume_modU_boundary (ω : Ω) : volume {v | modU U v ω = 0 ∨ modU U v ω = 1} = 0 := by
  unfold modU; split_ifs with h
  · exact h.1
  · norm_num

theorem tendsto_clock_modU (hU : IsJacobiDiffusion κ a b P 𝓗 U) (ω : Ω) :
    Tendsto (clock (modU U · ω)) atTop atTop := by
  by_cases h : ω ∈ goodSet U
  · simp only [modU, h, ite_true]
    exact tendsto_clock_of_mem_goodSet hU h
  · simp only [modU, h, ite_false]
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 8))
    filter_upwards [eventually_ge_atTop 0] with u hu
    exact clock_half_ge u hu

theorem measurableSet_goodSet [IsProbabilityMeasure P] (hU : IsJacobiDiffusion κ a b P 𝓗 U) : MeasurableSet (goodSet U) := by
  have hJ := hU.isJacobiMP
  set S : Set (Ω × ℝ) := {p | U p.2 p.1 = 0 ∨ U p.2 p.1 = 1}
  have hSm : MeasurableSet S :=
    (hJ.measurable_uncurry (measurableSet_singleton 0)).union
      (hJ.measurable_uncurry (measurableSet_singleton 1))
  have h1 : MeasurableSet {ω | volume {v | U v ω = 0 ∨ U v ω = 1} = 0} :=
    measurable_measure_prodMk_left hSm (measurableSet_singleton 0)
  have hcl : ∀ n : ℕ, Measurable fun ω => clock (U · ω) n := fun n =>
    (adapted_clock hU.mem_Icc hU.continuous hU.adapted n).mono (𝓗.le _) le_rfl
  exact h1.inter (MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
    measurableSet_le measurable_const (hcl n))

theorem measure_compl_goodSet [IsProbabilityMeasure P] (hU : IsJacobiDiffusion κ a b P 𝓗 U)
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) : P (goodSet U)ᶜ = 0 := by
  have h : ∀ᵐ ω ∂P, ω ∈ goodSet U := by
    filter_upwards [hU.ae_volume_boundary hκ ha hb, hU.ae_tendsto_clock hκ ha hb] with ω h1 h2
    refine ⟨h1, mem_iInter.2 fun M => mem_iUnion.2 ?_⟩
    obtain ⟨n, hn⟩ := (h2.eventually (eventually_ge_atTop (M : ℝ))).exists_forall_of_atTop
    obtain ⟨k, hk⟩ := exists_nat_ge n
    exact ⟨k, hn k hk⟩
  exact ae_iff.1 h

/-! ### The null augmentation of a filtration on `ℝ` -/

/-- The σ-algebra generated by the `P`-null sets. -/
@[instance_reducible]
def nullSigma' (P : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {s | MeasurableSet s ∧ P s = 0}

theorem nullSigma'_le (P : Measure Ω) : nullSigma' P ≤ mΩ :=
  MeasurableSpace.generateFrom_le fun _ hs => hs.1

/-- `𝓗 ∨ 𝒩_P`. -/
def augF (𝓗 : Filtration ℝ mΩ) (P : Measure Ω) : Filtration ℝ mΩ :=
  𝓗 ⊔ Filtration.const ℝ (nullSigma' P) (nullSigma'_le P)

theorem augF_apply (u : ℝ) : augF 𝓗 P u = 𝓗 u ⊔ nullSigma' P := rfl

theorem le_augF (u : ℝ) : 𝓗 u ≤ augF 𝓗 P u := le_sup_left

theorem measurableSet_augF_of_null {s : Set Ω} (hs : MeasurableSet s) (h0 : P s = 0) (u : ℝ) :
    MeasurableSet[augF 𝓗 P u] s :=
  (le_sup_right : nullSigma' P ≤ 𝓗 u ⊔ nullSigma' P) s
    (MeasurableSpace.measurableSet_generateFrom ⟨hs, h0⟩)

theorem exists_ae_eq_of_measurableSet_augF {u : ℝ} {s : Set Ω}
    (hs : MeasurableSet[augF 𝓗 P u] s) : ∃ s', MeasurableSet[𝓗 u] s' ∧ s =ᵐ[P] s' :=
  (sup_le le_eventuallyMeasurableSpace (MeasurableSpace.generateFrom_le fun _ hu =>
      ⟨∅, @MeasurableSet.empty _ (𝓗 u), ae_eq_empty.mpr hu.2⟩) :
    𝓗 u ⊔ nullSigma' P ≤ eventuallyMeasurableSpace (𝓗 u) (ae P)) s hs

theorem measurableSet_goodSet_augF [IsProbabilityMeasure P] (hU : IsJacobiDiffusion κ a b P 𝓗 U)
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) (u : ℝ) : MeasurableSet[augF 𝓗 P u] (goodSet U) := by
  have := measurableSet_augF_of_null (𝓗 := 𝓗) (measurableSet_goodSet hU).compl
    (measure_compl_goodSet hU hκ ha hb) u
  simpa using this.compl

theorem adapted_modU [IsProbabilityMeasure P] (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ)
    (ha : 0 < a) (hb : 0 < b) (u : ℝ) : Measurable[augF 𝓗 P u] (modU U u) :=
  Measurable.ite (measurableSet_goodSet_augF hU hκ ha hb u)
    ((hU.adapted u).mono (le_augF u) le_rfl) measurable_const

theorem ae_modU_eq [IsProbabilityMeasure P] (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ)
    (ha : 0 < a) (hb : 0 < b) : ∀ᵐ ω ∂P, ∀ u, modU U u ω = U u ω := by
  have : ∀ᵐ ω ∂P, ω ∈ goodSet U := ae_iff.2 (measure_compl_goodSet hU hκ ha hb)
  filter_upwards [this] with ω hω u
  simp [modU, hω]

/-- Set-integral martingale identities pass to a.e.-equal processes in the augmented filtration. -/
theorem setIntegral_augF_eq {Y Y' : ℝ → Ω → ℝ} (hYY : ∀ᵐ ω ∂P, ∀ u, Y' u ω = Y u ω)
    (hmart : ∀ w x, w ≤ x → ∀ A, MeasurableSet[𝓗 w] A →
      ∫ ω in A, Y x ω ∂P = ∫ ω in A, Y w ω ∂P) {w x : ℝ} (hwx : w ≤ x) {A : Set Ω}
    (hA : MeasurableSet[augF 𝓗 P w] A) : ∫ ω in A, Y' x ω ∂P = ∫ ω in A, Y' w ω ∂P := by
  obtain ⟨A', hA', hAA⟩ := exists_ae_eq_of_measurableSet_augF hA
  have hx : ∀ u, Y' u =ᵐ[P] Y u := fun u => by filter_upwards [hYY] with ω h; exact h u
  rw [setIntegral_congr_set hAA, setIntegral_congr_set hAA,
    integral_congr_ae (ae_restrict_of_ae (hx x)), integral_congr_ae (ae_restrict_of_ae (hx w))]
  exact hmart w x hwx A' hA'

/-! ### The physical clock -/

/-- The physical-time filtration `𝓖_t = 𝓗'_{τ_t}` for `t > 0`, `𝓖_0` trivial. -/
def physF (𝓗' : Filtration ℝ mΩ) (τ : ℝ≥0 → Ω → ℝ)
    (hτ : ∀ t : ℝ≥0, 0 < t → IsStoppingTime 𝓗' fun ω => ((τ t ω : ℝ) : WithTop ℝ))
    (hmono : ∀ s t : ℝ≥0, 0 < s → s ≤ t → ∀ ω, τ s ω ≤ τ t ω) : Filtration ℝ≥0 mΩ where
  seq t := if h : 0 < t then (hτ t h).measurableSpace else ⊥
  mono' s t hst := by
    by_cases hs : 0 < s
    · have ht : 0 < t := lt_of_lt_of_le hs hst
      simp only [hs, ht, dite_true]
      exact IsStoppingTime.measurableSpace_mono _ _ fun ω =>
        WithTop.coe_le_coe.2 (hmono s t hs hst ω)
    · simp only [hs, dite_false]; exact bot_le
  le' t := by
    by_cases h : 0 < t
    · simp only [h, dite_true]; exact (hτ t h).measurableSpace_le
    · simp only [h, dite_false]; exact bot_le

/-- The inverse clock of the modified path. -/
def tauP (U : ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := invClock (modU U · ω) t

section Phys

variable [IsProbabilityMeasure P] (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ) (ha : 0 < a)
  (hb : 0 < b)
include hU

omit [IsProbabilityMeasure P] in
theorem tauP_le_iff {t : ℝ≥0} (ht : 0 < t) (ω : Ω) (u : ℝ) :
    tauP U t ω ≤ u ↔ (t : ℝ) ≤ clock (modU U · ω) u := by
  rw [← not_lt, tauP, lt_invClock_iff (continuous_modU hU ω) (fun v => modU_mem hU v ω)
    (volume_modU_boundary ω) (tendsto_clock_modU hU ω) (NNReal.coe_pos.2 ht), not_lt]

omit [IsProbabilityMeasure P] in
theorem tauP_mono (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) (ω : Ω) : tauP U s ω ≤ tauP U t ω :=
  (invClock_le_iff (continuous_modU hU ω) (fun v => modU_mem hU v ω) (volume_modU_boundary ω)
    (tendsto_clock_modU hU ω) (NNReal.coe_pos.2 hs)
    (NNReal.coe_pos.2 (lt_of_lt_of_le hs hst))).2 (NNReal.coe_le_coe.2 hst)

include hκ ha hb in
theorem adapted_clock_modU (u : ℝ) : Measurable[augF 𝓗 P u] fun ω => clock (modU U · ω) u :=
  adapted_clock (modU_mem hU) (continuous_modU hU) (adapted_modU hU hκ ha hb) u

include hκ ha hb in
theorem isStopping_tauP {t : ℝ≥0} (ht : 0 < t) (u : ℝ) :
    MeasurableSet[augF 𝓗 P u] {ω | tauP U t ω ≤ u} := by
  simp_rw [tauP_le_iff hU ht]
  exact measurableSet_le measurable_const (adapted_clock_modU hU hκ ha hb u)

include hκ ha hb in
theorem isStoppingTime_tauP (t : ℝ≥0) (ht : 0 < t) :
    IsStoppingTime (augF 𝓗 P) fun ω => ((tauP U t ω : ℝ) : WithTop ℝ) := fun u => by
  simp_rw [WithTop.coe_le_coe]
  exact isStopping_tauP hU hκ ha hb ht u

end Phys

end TwoSeed

end Sec2

end InteractingSLE
