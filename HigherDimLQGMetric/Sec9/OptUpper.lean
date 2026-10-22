import HigherDimLQGMetric.Sec9.Interfaces
import HigherDimLQGMetric.Sharp.E3
import HigherDimLQGMetric.ShellDec.Tail
import HigherDimLQGMetric.Events.TightLaw
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Select.MetricBorel

/-!
# Optimal comparison constants in [S] §9

The almost-sure upper comparison constants form a nonempty upper set bounded away
from zero. The infimum is attained, and normalized-law uniqueness transfers its
strict optimality between all realizations of the whole-space LGF.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd e₁)
open scoped ENNReal

variable {d : ℕ}

private def s8dCompEvent (A B : DistRd d → ContMetric d) (U : ℝ) : Set (DistRd d) :=
  {g | ∀ x y : Rd d, (B g).1 (x, y) ≤ U * (A g).1 (x, y)}

private theorem s8dCompEvent_measurable {A B : DistRd d → ContMetric d}
    (hA : Measurable A) (hB : Measurable B) (U : ℝ) :
    MeasurableSet (s8dCompEvent A B U) := by
  have hc : IsClosed {p : C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) |
      ∀ x y : Rd d, p.2 (x, y) ≤ U * p.1 (x, y)} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_le
      ((continuous_eval_const (x, y)).comp continuous_snd)
      (continuous_const.mul
        ((continuous_eval_const (x, y)).comp continuous_fst))
  have hp : Measurable fun g : DistRd d => ((A g).1, (B g).1) :=
    (measurable_subtype_coe.comp hA).prodMk (measurable_subtype_coe.comp hB)
  exact hc.measurableSet.preimage hp

private theorem s8dCompEvent_normalize
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A) (hB : IsSharpWeakExpMetric d ξ Q B)
    (U : ℝ) :
    ∀ᵐ ω ∂P, h ω ∈ s8dCompEvent A B U ↔
      addConst (h ω) (-sphereAvg (h ω) 1 0) ∈ s8dCompEvent A B U := by
  filter_upwards [hA.ae_apply_addFun_const hh.isLGFPlusCont,
    hB.ae_apply_addFun_const hh.isLGFPlusCont] with ω hAw hBw
  constructor <;> intro hc x y
  · let c := -sphereAvg (h ω) 1 0
    have he : 0 < Real.exp (ξ * c) := Real.exp_pos _
    have hm := (mul_le_mul_iff_of_pos_left he).2 (hc x y)
    have hAe : (A (addConst (h ω) c)).1 (x, y) =
        Real.exp (ξ * c) * (A (h ω)).1 (x, y) := by
      simpa only [addFun_const] using hAw c x y
    have hBe : (B (addConst (h ω) c)).1 (x, y) =
        Real.exp (ξ * c) * (B (h ω)).1 (x, y) := by
      simpa only [addFun_const] using hBw c x y
    rw [hAe, hBe]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  · let c := -sphereAvg (h ω) 1 0
    have he : 0 < Real.exp (ξ * c) := Real.exp_pos _
    have hm := hc x y
    have hAe : (A (addConst (h ω) c)).1 (x, y) =
        Real.exp (ξ * c) * (A (h ω)).1 (x, y) := by
      simpa only [addFun_const] using hAw c x y
    have hBe : (B (addConst (h ω) c)).1 (x, y) =
        Real.exp (ξ * c) * (B (h ω)).1 (x, y) := by
      simpa only [addFun_const] using hBw c x y
    rw [hAe, hBe] at hm
    apply (mul_le_mul_iff_of_pos_left he).1
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm

private theorem s8dCompEvent_law_ae
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistRd d) (h' : Ω' → DistRd d)
    (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P')
    (hd : 2 ≤ d) {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A) (hB : IsSharpWeakExpMetric d ξ Q B)
    (U : ℝ) (hae : ∀ᵐ ω ∂P, h ω ∈ s8dCompEvent A B U) :
    ∀ᵐ ω ∂P', h' ω ∈ s8dCompEvent A B U := by
  let N : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  let N' : Ω' → DistRd d := fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0)
  have hm : Measurable N :=
    (hh.addConst (((measurable_sphereAvg_left (d := d) 1 0).comp hh.measurable).neg)).measurable
  have hm' : Measurable N' :=
    (hh'.addConst (((measurable_sphereAvg_left (d := d) 1 0).comp hh'.measurable).neg)).measurable
  have hE := s8dCompEvent_measurable hA.measurable hB.measurable U
  have hN : ∀ᵐ ω ∂P, N ω ∈ s8dCompEvent A B U := by
    filter_upwards [hae, s8dCompEvent_normalize P h hh hA hB U] with ω ha hn
    exact hn.mp ha
  have hmap : ∀ᵐ g ∂P.map N, g ∈ s8dCompEvent A B U :=
    (ae_map_iff hm.aemeasurable hE).2 hN
  rw [map_normalizedLGF_eq hd hh hh'] at hmap
  have hN' : ∀ᵐ ω ∂P', N' ω ∈ s8dCompEvent A B U :=
    (ae_map_iff hm'.aemeasurable hE).1 hmap
  filter_upwards [hN', s8dCompEvent_normalize P' h' hh' hA hB U] with ω ha hn
  exact hn.mpr ha

private theorem s8d_upperCompSet_lower
    (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A) (hB : IsSharpWeakExpMetric d ξ Q B) :
    ∃ C : ℝ, 0 < C ∧ (∀ U ∈ upperCompSet A B, C⁻¹ ≤ U) ∧
      C ∈ upperCompSet A B := by
  obtain ⟨C, hC, hcomp⟩ := e3_sharp (lemmaA1 (by omega : 1 ≤ d)) hd hξ hA hB
  obtain ⟨Ω, m, P, h, hP, hh⟩ := exists_isWholeSpaceLGF (by omega : 1 ≤ d)
  letI : MeasurableSpace Ω := m
  letI : IsProbabilityMeasure P := hP
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, ?_, ?_⟩
  · intro U hU
    obtain ⟨ω, hω⟩ := Filter.Eventually.exists
      (Filter.Eventually.and (hU P h hh) (hcomp P h hh.isLGFPlusCont))
    let x : Rd d := 0
    let y : Rd d := e₁ d
    have hxy : x ≠ y := (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
    have hAp : 0 < (A (h ω)).1 (x, y) := (A (h ω)).apply_pos hxy
    have hBp : 0 < (B (h ω)).1 (x, y) := (B (h ω)).apply_pos hxy
    have h1 := hω.1 x y
    have h2 := (hω.2 x y).2
    have hUpos : 0 < U := by nlinarith only [h1, hAp, hBp]
    have h3 := mul_le_mul_of_nonneg_left h2 hUpos.le
    have h4 : 1 ≤ U * C := by
      have h5 : (B (h ω)).1 (x, y) ≤ U * C * (B (h ω)).1 (x, y) := by
        nlinarith only [h1, h3]
      nlinarith only [h5, hBp]
    rw [← one_div]
    exact (div_le_iff₀ hCpos).2 (by simpa only [mul_comm] using h4)
  · intro Ω _ P _ h hh
    filter_upwards [hcomp P h hh.isLGFPlusCont] with ω hc x y
    exact (hc x y).1

/-- The infimum of the universal comparison constants is positive, attained,
and strictly optimal on every whole-space LGF realization. -/
theorem optUpperShape : OptUpperShape := by
  intro d hd ξ Q hξ hQ A B hA hB
  obtain ⟨C, hC, hbelow, hCmem⟩ := s8d_upperCompSet_lower hd hξ hA hB
  have hne : (upperCompSet A B).Nonempty := ⟨C, hCmem⟩
  have hbb : BddBelow (upperCompSet A B) := ⟨C⁻¹, hbelow⟩
  have hInf : C⁻¹ ≤ optUpper A B := by
    exact le_csInf hne hbelow
  have hpos : 0 < optUpper A B := (inv_pos.mpr hC).trans_le hInf
  refine ⟨hpos, ?_, ?_⟩
  · intro Ω _ P _ h hh
    have hnear (n : ℕ) : optUpper A B + 1 / ((n : ℝ) + 1) ∈ upperCompSet A B := by
      have hlt : optUpper A B < optUpper A B + 1 / ((n : ℝ) + 1) := by
        have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨U, hU, hU'⟩ := exists_lt_of_csInf_lt hne
        (by simpa only [optUpper] using hlt)
      intro Ω' _ P' _ h' hh'
      filter_upwards [hU P' h' hh'] with ω hw x y
      exact (hw x y).trans
        (mul_le_mul_of_nonneg_right hU'.le ((A (h' ω)).nonneg x y))
    have hae : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ x y : Rd d,
        (B (h ω)).1 (x, y) ≤
          (optUpper A B + 1 / ((n : ℝ) + 1)) * (A (h ω)).1 (x, y) :=
      ae_all_iff.2 fun n => hnear n P h hh
    filter_upwards [hae] with ω hw x y
    have hlim : Filter.Tendsto
        (fun n : ℕ => (optUpper A B + 1 / ((n : ℝ) + 1)) *
          (A (h ω)).1 (x, y)) Filter.atTop
        (nhds (optUpper A B * (A (h ω)).1 (x, y))) := by
      have hzero : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [add_zero] using
        ((tendsto_const_nhds.add hzero).mul_const ((A (h ω)).1 (x, y)))
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hw n x y)
  · intro U hU Ω _ P _ h hh hae
    have hmem : U ∈ upperCompSet A B := by
      intro Ω' _ P' _ h' hh'
      exact s8dCompEvent_law_ae P P' h h' hh hh' (by omega : 2 ≤ d) hA hB U hae
    have hle : optUpper A B ≤ U := csInf_le hbb hmem
    exact (not_lt_of_ge hle) hU

end HigherDimLQGMetric
