/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ZtCof
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding
import InteractingSLE.Spec.Restart.RetEndLimit
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# SB2(1)'s final gluing, part 2: the canonical trace at the relative lifetime

Packet PROVE-T14-SB2DRV (round 16, D4 step 1). Once the relative driver is identified with a canonical conditional
flow-line driver before the relative lifetime `U ≤ ζc` (`ζc` the canonical lifetime), the relative trace converges at
a finite `U`: the canonical flow line has a trace continuous up to its lifetime (Theorem 1.3), so its trace read at
rational times is uniformly continuous below `ζc`.

* **`exists_tendsto_of_finCond`** (deterministic): the finite-horizon trace coding `FinCond w ζ` (uniform continuity of
  the trace of `w` at rational times below `ζ`) gives every function continuous before `U ≤ ζ` that is the trace of
  `w` there a limit at a finite `U > 0`;
* **`ae_mem_traceSet_of_condFlowLine`**: a measurable regular conditional flow-line driver lies almost surely on the
  live event in the Borel trace set `Sec7.RandRestart.traceSet` (Theorem 1.3 under the regular conditional laws, the
  driver limit `Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace` and the coding
  `Sec7.RandRestart.mem_traceSet_iff`, then disintegration).

**R48.** Theorem 1.3 is a hypothesis. No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Zt

open Exist Exist.Staged Restart

/-! ### The trace limit from the rational coding -/

/-- **The coded trace has a limit at a finite horizon below the coding horizon** (deterministic). -/
theorem exists_tendsto_of_finCond {w : ℝ≥0 → ℝ} {ζ U : ℝ≥0∞} (hfc : Sec7.RandRestart.FinCond w ζ) (hUζ : U ≤ ζ)
    (hU : U ≠ ⊤) (hU0 : 0 < U) {f : ℝ≥0 → ℂ} (hfc' : ContinuousOn f {t | (t : ℝ≥0∞) < U})
    (hft : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U → f t = LP.traceAt t w) :
    ∃ z, Tendsto f (𝓝[<] U.toNNReal) (𝓝 z) := by
  set V : ℝ≥0 := U.toNNReal with hVdef
  have hVU : (V : ℝ≥0∞) = U := ENNReal.coe_toNNReal hU
  have hV0 : 0 < V := by rw [← ENNReal.coe_lt_coe, hVU]; exact_mod_cast hU0
  have : (𝓝[<] V).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hV0⟩
  have hlt : ∀ t : ℝ≥0, t < V → (t : ℝ≥0∞) < U := fun t ht => by rw [← hVU]; exact ENNReal.coe_lt_coe.2 ht
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < U} := isOpen_lt ENNReal.continuous_coe continuous_const
  refine (cauchy_map_iff_exists_tendsto (l := 𝓝[<] V)).1 ?_
  refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  obtain ⟨k, hk⟩ := hfc.1 m
  set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set S : Set ℝ≥0 := {s | (V : ℝ) - δ < s ∧ s < V} with hSdef
  have hSo : IsOpen S :=
    (isOpen_lt continuous_const NNReal.continuous_coe).inter (isOpen_lt NNReal.continuous_coe continuous_const)
  have hSm : S ∈ 𝓝[<] V := by
    refine mem_nhdsWithin.2 ⟨{s : ℝ≥0 | (V : ℝ) - δ < s}, isOpen_lt continuous_const NNReal.continuous_coe,
      by show (V : ℝ) - δ < V; linarith, fun s hs => ⟨hs.1, hs.2⟩⟩
  -- every point of `S` is approximated by a rational point of `S` with a close value
  have happrox : ∀ s ∈ S, ∃ p : ℚ≥0, (p : ℝ≥0) ∈ S ∧ dist (f s) (f p) < ε / 3 := by
    intro s hs
    have hsU : (s : ℝ≥0∞) < U := hlt s hs.2
    set O : Set ℝ≥0 := {t | (t : ℝ≥0∞) < U} ∩ f ⁻¹' ball (f s) (ε / 3) with hO
    have hOo : IsOpen (S ∩ O) := hSo.inter (hfc'.isOpen_inter_preimage hopen isOpen_ball)
    obtain ⟨_, ⟨p, rfl⟩, hp⟩ := LocalExt.dense_range_coe_nnrat.exists_mem_open hOo
      ⟨s, hs, hsU, by simp only [mem_preimage, mem_ball, dist_self]; positivity⟩
    refine ⟨p, hp.1, ?_⟩
    have := hp.2.2
    rw [mem_preimage, mem_ball] at this
    rw [dist_comm]; exact this
  refine ⟨f '' S, image_mem_map hSm, ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
  obtain ⟨p, hpS, hp⟩ := happrox s hs
  obtain ⟨p', hp'S, hp'⟩ := happrox s' hs'
  have hpU : ((p : ℝ≥0) : ℝ≥0∞) < U := hlt _ hpS.2
  have hp'U : ((p' : ℝ≥0) : ℝ≥0∞) < U := hlt _ hp'S.2
  have hdist : dist (p : ℝ≥0) (p' : ℝ≥0) < δ := by
    rw [NNReal.dist_eq, abs_lt]
    constructor <;> linarith [hpS.1, hpS.2, hp'S.1, hp'S.2,
      show ((p : ℝ≥0) : ℝ) < V from hpS.2, show ((p' : ℝ≥0) : ℝ) < V from hp'S.2]
  have hmid : dist (f p) (f p') ≤ 1 / ((m : ℝ) + 1) := by
    rw [hft _ hpU, hft _ hp'U]
    exact hk p p' (lt_of_lt_of_le hpU hUζ) (lt_of_lt_of_le hp'U hUζ) hdist
  calc dist (f s) (f s') ≤ dist (f s) (f p) + dist (f p) (f p') + dist (f p') (f s') :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h3 : dist (f p') (f s') < ε / 3 := by rw [dist_comm]; exact hp'
        have hm' : 1 / ((m : ℝ) + 1) < ε / 3 := hm
        linarith
    _ = ε := by ring

/-! ### The trace event of a conditional flow-line driver, at `P` -/

/-- **A regular conditional flow-line driver lies almost surely in the trace set on the live event.** -/
theorem ae_mem_traceSet_of_condFlowLine (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D) (hDr : ∀ ω, IsRegularDriver (D ω))
    (hD : SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc (fun t ω => (D ω).1 t) (fun ω => (D ω).2)) :
    ∀ᵐ ω ∂P, ω ∈ F → D ω ∈ Sec7.RandRestart.traceSet := by
  have hFm : MeasurableSet F := h𝒢 _ hF
  have hTm : MeasurableSet (D ⁻¹' Sec7.RandRestart.traceSet) := hDm Sec7.RandRestart.measurableSet_traceSet
  have hG : MeasurableSet (Fᶜ ∪ D ⁻¹' Sec7.RandRestart.traceSet) := hFm.compl.union hTm
  -- under almost every regular conditional law
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ Fᶜ ∪ D ⁻¹' Sec7.RandRestart.traceSet := by
    filter_upwards [hD, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hF.compl] with ω₀ hD₀ hc₀
    by_cases hω₀ : ω₀ ∈ F
    · obtain ⟨-, h', -, hfl⟩ := hD₀ hω₀
      obtain ⟨X, 𝓕, VL, VR, B, -, hC⟩ := hfl
      have hev := h13 hκ (Theorem15.isOrderedForceWord_flowLine (bc ω₀) (jc ω₀) 0) hC.1
      filter_upwards [hev] with ω hω
      refine Or.inr ?_
      obtain ⟨-, η, hη, htr⟩ := hω
      have hreg := hDr ω
      show (((D ω).1 : ℝ≥0 → ℝ), (D ω).2) ∈ Sec7.RandRestart.traceSet
      refine (Sec7.RandRestart.mem_traceSet_iff hreg.1 hreg.2.1 fun h0 hfin => ?_).2 ⟨η, hη, htr⟩
      have hcoe : (((D ω).2.toNNReal : ℝ≥0) : ℝ≥0∞) = (D ω).2 := ENNReal.coe_toNNReal hfin.ne
      have hη' : IsGeneratingTrace (D ω).1 (((D ω).2.toNNReal : ℝ≥0) : ℝ≥0∞) η := by rw [hcoe]; exact hη
      have hc' : ContinuousOn (D ω).1 {t | (t : ℝ≥0∞) < (((D ω).2.toNNReal : ℝ≥0) : ℝ≥0∞)} := by
        rw [hcoe]; exact hreg.1
      have hpos : 0 < (D ω).2.toNNReal := by
        rw [← ENNReal.coe_lt_coe, hcoe]; exact h0
      exact Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace hη' hc' hreg.2.1 hpos
    · filter_upwards [hc₀ hω₀] with ω hω using Or.inl hω
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hG hker] with ω hω hωF
  rcases hω with h1 | h2
  · exact absurd hωF h1
  · exact h2

end InteractingSLE.Theorem14.SB.Zt
