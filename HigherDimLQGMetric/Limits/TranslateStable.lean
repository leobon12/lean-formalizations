import HigherDimLQGMetric.Limits.TranslatePrelimit
import HigherDimLQGMetric.Limits.ScaleStable
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Translation of stable LFPP limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The metric translation with a scalar Weyl correction is continuous. -/
theorem l6c_continuous_translateMetric {d : ℕ} (ξ : ℝ) (z : Rd d) :
    Continuous (fun q : ℝ × C(Rd d × Rd d, ℝ) =>
      Real.exp (-ξ * q.1) • q.2.comp
        ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul continuous_fst)).smul
      ((ContinuousMap.continuous_precomp _).comp continuous_snd)

/-- Stable convergence transfers to the recentered metric at a fixed point. -/
theorem l6c_stable_translateLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hstable : StablyTendstoLU P h X Y) (ξ : ℝ) (z : Rd d) :
    TendstoInDistribution
      (fun n ω => Real.exp (-ξ * sphereAvg (h ω) 1 z) •
        (X n ω).comp
          ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩)
      atTop
      (fun ω => Real.exp (-ξ * sphereAvg (h ω) 1 z) •
        (Y ω).comp
          ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩)
      (fun _ => P) P := by
  have ha : Measurable (fun g : DistRd d => sphereAvg g 1 z) :=
    measurable_sphereAvg_left 1 z
  have hpair := l6c_stable_adjoin_scalar P h hh X Y hX hY hstable
    (fun g => sphereAvg g 1 z) ha
  exact hpair.continuous_comp (l6c_continuous_translateMetric ξ z)

/-- The law of every recentered normalized LFPP metric equals the unshifted law. -/
theorem l6c_law_lfppSeq_translate {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) (z : Rd d) (n : ℕ) :
    P.map (fun ω => Real.exp (-ξ * sphereAvg (h ω) 1 z) •
      (lfppSeq κ ξ εs (h ω) n).comp
        ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩) =
    P.map (fun ω => lfppSeq κ ξ εs (h ω) n) := by
  let g : Ω → DistRd d := fun ω =>
    addConst (affineComp 1 z (h ω))
      (-sphereAvg (affineComp 1 z (h ω)) 1 0)
  calc
    P.map (fun ω => Real.exp (-ξ * sphereAvg (h ω) 1 z) •
        (lfppSeq κ ξ εs (h ω) n).comp
          ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩) =
      P.map (fun ω => lfppSeq κ ξ εs (g ω) n) := by
      apply Measure.map_congr
      filter_upwards [l6c_ae_lfppSeq_translate hd κ hκ ξ εs hεs P h hh z]
        with ω hω
      apply ContinuousMap.ext
      rintro ⟨u, v⟩
      change Real.exp (-ξ * sphereAvg (h ω) 1 z) *
          lfppSeq κ ξ εs (h ω) n (z + u, z + v) =
        lfppSeq κ ξ εs (g ω) n (u, v)
      rw [hω n u v]
      rw [← mul_assoc, ← Real.exp_add]
      have heq : -ξ * sphereAvg (h ω) 1 z + ξ * sphereAvg (h ω) 1 z = 0 := by ring
      simp only [heq, Real.exp_zero, one_mul, g]
    _ = P.map (fun ω => lfppSeq κ ξ εs (h ω) n) := by
      simpa only [g, lfppSeq] using
        l6c_map_lfppMetric_normalizedTranslate hd κ hκ ξ P h hh
          (εs n) (hεs n) z

/-- A stable LFPP limit has a translation invariant metric marginal after
recentering by its unit sphere average. -/
theorem l6c_law_limit_translate {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1))
    (z : Rd d) :
    P.map (fun ω => Real.exp (-ξ * sphereAvg (h ω) 1 z) •
      (Dh ω).1.comp
        ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩) =
    P.map (fun ω => (Dh ω).1) := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
  have hX (n : ℕ) : AEMeasurable
      (fun ω => lfppSeq κ ξ εs (h ω) n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  have hY : AEMeasurable (fun ω => (Dh ω).1) P :=
    (measurable_subtype_coe.comp hDh).aemeasurable
  have hT := (l6c_stable_translateLaw P h hh.1.measurable
    (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1)
    hX hY hstable ξ z).tendsto
  let ν : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    fun n => ⟨P.map (fun ω => lfppSeq κ ξ εs (h ω) n), inferInstance⟩
  let μ : ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    ⟨P.map (fun ω => (Dh ω).1), inferInstance⟩
  have hO : Tendsto ν atTop (𝓝 μ) := by
    apply l6c_stable_metric_law P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1)
      hX hY hstable
    · intro n; rfl
    · rfl
  have hEq (n : ℕ) :
      (⟨P.map (fun ω => Real.exp (-ξ * sphereAvg (h ω) 1 z) •
        (lfppSeq κ ξ εs (h ω) n).comp
          ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩),
          inferInstance⟩ : ProbabilityMeasure C(Rd d × Rd d, ℝ)) =
      ⟨P.map (fun ω => lfppSeq κ ξ εs (h ω) n), inferInstance⟩ := by
    exact Subtype.ext (l6c_law_lfppSeq_translate hd κ hκ ξ εs hεs P h hh z n)
  have hT' : Tendsto ν atTop
      (𝓝 (⟨P.map (fun ω => Real.exp (-ξ * sphereAvg (h ω) 1 z) •
        (Dh ω).1.comp
          ⟨fun p : Rd d × Rd d => (z + p.1, z + p.2), by fun_prop⟩),
        inferInstance⟩ : ProbabilityMeasure C(Rd d × Rd d, ℝ))) := by
    simpa only [ν, hEq] using hT
  exact congrArg (fun ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) =>
    (ν : Measure C(Rd d × Rd d, ℝ))) (tendsto_nhds_unique hT' hO)

end HigherDimLQGMetric
