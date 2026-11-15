/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafAuxRHistory
import LQGMetric.Field.RandomDistVersion
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Passing joint field--history laws to cofinal prefixes

A normalized killed record is the limit of its cofinal killed prefixes.
The countable distribution code `pairJ` embeds the field--record pair in a
Polish space. Mathlib's almost-sure convergence in distribution and uniqueness
of weak limits therefore pass the prefix joint laws to the limiting record.
No terminal driver or terminal conditional mean is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LQGMetric LawUnique Restart.StoppedExtendWF

/-- Cofinal killing times recover a normalized killed record in the product
topology, including a finite terminal cutoff or infinite lifetime. -/
theorem tendsto_killAt_of_tendsto {nL nR : ℕ} {γ : HistorySpace nL nR}
    (hn : historyNormalize γ = γ) {s : ℕ → ℝ≥0∞} (hs : ∀ n, s n ≤ γ.1)
    (hlim : Tendsto s atTop (𝓝 γ.1)) :
    Tendsto (fun n => killAt γ (s n)) atTop (𝓝 γ) := by
  apply Tendsto.prodMk_nhds hlim
  apply tendsto_pi_nhds.2
  intro p
  apply tendsto_const_nhds.congr'
  by_cases hp : (dyadicTime p : ℝ≥0∞) < γ.1
  · filter_upwards [hlim.eventually (Ioi_mem_nhds hp)] with n hn
    simp only [hn, ↓reduceIte]
  · have hzero := congrFun (congrArg Prod.snd hn) p
    have hg : γ.2 p = 0 := by
      simpa only [historyNormalize, hp, ↓reduceIte] using hzero.symm
    exact Eventually.of_forall fun n => by
      have hnlt : ¬ (dyadicTime p : ℝ≥0∞) < s n := fun h => hp (h.trans_le (hs n))
      simp only [hnlt, ↓reduceIte, hg]

/-- Equality of joint laws at cofinal measurable prefixes implies equality of
the limiting joint laws. The field is kept through its countable Borel code. -/
theorem map_field_history_eq_of_rule_limits
    {nL nR : ℕ} {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {P : Measure Ω} {P₀ : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
    {h : Ω → DistOn upperHalfPlaneOpens} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    {Y : Ω → HistorySpace nL nR} {Y₀ : Ω₀ → HistorySpace nL nR}
    (hh : Measurable h) (hh₀ : Measurable h₀) (hY : Measurable Y) (hY₀ : Measurable Y₀)
    (hn : ∀ᵐ ω ∂P, historyNormalize (Y ω) = Y ω)
    (hn₀ : ∀ᵐ ω ∂P₀, historyNormalize (Y₀ ω) = Y₀ ω)
    {Q : ℕ → HistorySpace nL nR → ℝ≥0∞} (hQ : ∀ n, Measurable (Q n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Q n (Y ω)) atTop (𝓝 (Y ω).1))
    (hlim₀ : ∀ᵐ ω ∂P₀, Tendsto (fun n => Q n (Y₀ ω)) atTop (𝓝 (Y₀ ω).1))
    (hlaw : ∀ n, P.map (fun ω => (h ω, ruleKill (Q n) (Y ω))) =
      P₀.map (fun ω => (h₀ ω, ruleKill (Q n) (Y₀ ω)))) :
    P.map (fun ω => (h ω, Y ω)) = P₀.map (fun ω => (h₀ ω, Y₀ ω)) := by
  let C := Prod.map (pairJ upperHalfPlaneOpens) (id : HistorySpace nL nR → HistorySpace nL nR)
  have hC : MeasurableEmbedding C :=
    (measurableEmbedding_pairJ upperHalfPlaneOpens).prodMap MeasurableEmbedding.id
  have hm : ∀ n, Measurable (fun ω => C (h ω, ruleKill (Q n) (Y ω))) :=
    fun n => hC.measurable.comp (hh.prodMk ((measurable_ruleKill (hQ n)).comp hY))
  have hm₀ : ∀ n, Measurable (fun ω => C (h₀ ω, ruleKill (Q n) (Y₀ ω))) :=
    fun n => hC.measurable.comp (hh₀.prodMk ((measurable_ruleKill (hQ n)).comp hY₀))
  have he : ∀ n, P.map (fun ω => C (h ω, ruleKill (Q n) (Y ω))) =
      P₀.map (fun ω => C (h₀ ω, ruleKill (Q n) (Y₀ ω))) := by
    intro n
    calc
      _ = (P.map (fun ω => (h ω, ruleKill (Q n) (Y ω)))).map C :=
        (Measure.map_map hC.measurable (hh.prodMk ((measurable_ruleKill (hQ n)).comp hY))).symm
      _ = (P₀.map (fun ω => (h₀ ω, ruleKill (Q n) (Y₀ ω)))).map C :=
        congrArg (fun μ => μ.map C) (hlaw n)
      _ = _ := Measure.map_map hC.measurable (hh₀.prodMk ((measurable_ruleKill (hQ n)).comp hY₀))
  have ht : ∀ᵐ ω ∂P, Tendsto (fun n => C (h ω, ruleKill (Q n) (Y ω)))
      atTop (𝓝 (C (h ω, Y ω))) := by
    filter_upwards [hn, hlim] with ω hn hlim
    have hmin : Tendsto (fun n => min (Q n (Y ω)) (Y ω).1) atTop (𝓝 (Y ω).1) := by
      simpa only [min_self] using
        (hlim.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => (Y ω).1) atTop (𝓝 (Y ω).1)))
    exact tendsto_const_nhds.prodMk_nhds (tendsto_killAt_of_tendsto hn
      (fun n => min_le_right _ _) hmin)
  have ht₀ : ∀ᵐ ω ∂P₀, Tendsto (fun n => C (h₀ ω, ruleKill (Q n) (Y₀ ω)))
      atTop (𝓝 (C (h₀ ω, Y₀ ω))) := by
    filter_upwards [hn₀, hlim₀] with ω hn hlim
    have hmin : Tendsto (fun n => min (Q n (Y₀ ω)) (Y₀ ω).1) atTop (𝓝 (Y₀ ω).1) := by
      simpa only [min_self] using
        (hlim.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => (Y₀ ω).1) atTop (𝓝 (Y₀ ω).1)))
    exact tendsto_const_nhds.prodMk_nhds (tendsto_killAt_of_tendsto hn
      (fun n => min_le_right _ _) hmin)
  have hd := tendstoInDistribution_of_ae_tendsto (fun n => (hm n).aemeasurable)
    (hC.measurable.comp (hh.prodMk hY)).aemeasurable ht
  have hd₀ := tendstoInDistribution_of_ae_tendsto (fun n => (hm₀ n).aemeasurable)
    (hC.measurable.comp (hh₀.prodMk hY₀)).aemeasurable ht₀
  have hd' : TendstoInDistribution (fun n ω => C (h ω, ruleKill (Q n) (Y ω)))
      atTop (fun ω => C (h₀ ω, Y₀ ω)) (fun _ => P) P₀ := by
    refine ⟨fun n => (hm n).aemeasurable, hd₀.aemeasurable_limit, ?_⟩
    simpa only [he, Function.comp_def] using hd₀.tendsto
  have heq := tendstoInDistribution_unique _ hd hd'
  apply hC.map_injective
  calc
    _ = P.map (fun ω => C (h ω, Y ω)) := Measure.map_map hC.measurable (hh.prodMk hY)
    _ = P₀.map (fun ω => C (h₀ ω, Y₀ ω)) := heq
    _ = _ := (Measure.map_map hC.measurable (hh₀.prodMk hY₀)).symm

end InteractingSLE.WFS
