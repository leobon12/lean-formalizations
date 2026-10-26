import SmallGammaGeodesics.Lower.TV
import SmallGammaGeodesics.Core.TestFun
import QuantumZipper.Proofs.Zipper.D3PlusN2HeartMix
import LQGMetric.Papers.MQ.ZBCM

/-! Gaussian TV bounds and the local mean-zero pairing carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.TV

open LQGMetric SmallGammaGeodesics

/-- The observable path on mean-zero tests supported in W. -/
def localPairPath (W : Set ℂ) (ξ : TestC0 → ℝ) : TestC0On W → ℝ :=
  fun ψ => ξ ψ.1

theorem measurable_localPairPath (W : Set ℂ) : Measurable (localPairPath W) :=
  measurable_pi_iff.mpr fun ψ => measurable_pi_apply ψ.1

/-- The law of the mean-zero local pairings of a whole-plane distribution. -/
def localPairLaw {Ω : Type*} [MeasurableSpace Ω] (W : Set ℂ)
    (h : Ω → DistC) (P : Measure Ω) : Measure (TestC0On W → ℝ) :=
  (lawPair0 h P).map (localPairPath W)

/-- A deterministic Cameron–Martin shift has small TV on every local mean-zero pairing path. -/
theorem tvDist_localPairLaw_addFun_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (W : Set ℂ) (φ : TestC) :
    QuantumZipper.TV.tvDist
      (localPairLaw W (fun ω => addFun (h ω) (testCont φ)) P)
      (localPairLaw W h P) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (gradEnergy φ) - 1)) := by
  have : IsProbabilityMeasure P := hh.gaussian.isProbabilityMeasure
  have : IsProbabilityMeasure (lawPair0 h P) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pair0_comp hh).aemeasurable).mpr
      inferInstance
  have : IsProbabilityMeasure
      (lawPair0 (fun ω => addFun (h ω) (testCont φ)) P) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pair0_addFun hh φ).aemeasurable).mpr
      inferInstance
  have hbound : QuantumZipper.TV.tvDist
      (lawPair0 (fun ω => addFun (h ω) (testCont φ)) P) (lawPair0 h P) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (gradEnergy φ) - 1)) := by
    apply QuantumZipper.D3Plus.tvDist_le_ofReal_of_abs
    intro A hA
    exact abs_lawPair0_addFun_sub_le hh φ A hA
  exact (QuantumZipper.TV.tvDist_map_le (measurable_localPairPath W)).trans hbound

/-- Local tests on U supported in W and annihilating additive constants. -/
abbrev ZBLocalTest (U : TopologicalSpace.Opens ℂ) (W : Set ℂ) :=
  {ψ : TestOn U // tsupport (ψ : ℂ → ℝ) ⊆ W ∧ ∫ x, ψ x = 0}

/-- Restriction of a path of test-function pairings to mean-zero local tests. -/
def zbLocalPath (U : TopologicalSpace.Opens ℂ) (W : Set ℂ)
    (ξ : TestOn U → ℝ) : ZBLocalTest U W → ℝ :=
  fun ψ => ξ ψ.1

theorem measurable_zbLocalPath (U : TopologicalSpace.Opens ℂ) (W : Set ℂ) :
    Measurable (zbLocalPath U W) :=
  measurable_pi_iff.mpr fun ψ => measurable_pi_apply ψ.1

/-- Cameron–Martin TV bound for a zero-boundary GFF on its full test-function path. -/
theorem tvDist_zb_shift_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : TopologicalSpace.Opens ℂ}
    {X : TestOn U → Ω → ℝ} (hadm : ZBAdmissible U)
    (hne : (U : Set ℂ).Nonempty) (hX : IsZBGFFProcess U X P)
    (f : LQGMetric.MarkovZB.zsSub U) :
    QuantumZipper.TV.tvDist
      (P.map (fun ω j => X j ω + ∫ x, f.1 x * j x))
      (P.map (fun ω j => X j ω)) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (QuantumZipper.dirichletEnergyOn U f.1) - 1)) := by
  have : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  have hm : Measurable (fun ω j => X j ω) :=
    measurable_pi_iff.mpr hX.measurable
  have hms : Measurable (fun ω j => X j ω + ∫ x, f.1 x * j x) :=
    measurable_pi_iff.mpr fun j => (hX.measurable j).add_const _
  have : IsProbabilityMeasure (P.map (fun ω j => X j ω)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (P.map (fun ω j => X j ω + ∫ x, f.1 x * j x)) :=
    (Measure.isProbabilityMeasure_map_iff hms.aemeasurable).mpr inferInstance
  apply QuantumZipper.D3Plus.tvDist_le_ofReal_of_abs
  intro A hA
  have key := QuantumZipper.CameronMartin.abs_measureReal_shift_sub_le
    hX.gaussian hX.measurable hX.centered (LQGMetric.MQ.cmSigma f) A hA
  rw [LQGMetric.MQ.covNorm_cmSigma hadm hX f] at key
  have heq : (fun ω j => X j ω + ∫ x, f.1 x * j x) =
      (fun ω j => X j ω +
        QuantumZipper.CameronMartin.covShift X P (LQGMetric.MQ.cmSigma f) j) := by
    funext ω j
    rw [LQGMetric.MQ.covShift_cmSigma hadm hne hX f j]
  rw [heq]
  exact key

/-- The modulo-constant local version, obtained by data processing. -/
theorem tvDist_zb_local_shift_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : TopologicalSpace.Opens ℂ}
    {X : TestOn U → Ω → ℝ} (hadm : ZBAdmissible U)
    (hne : (U : Set ℂ).Nonempty) (hX : IsZBGFFProcess U X P)
    (W : Set ℂ) (f : LQGMetric.MarkovZB.zsSub U) :
    QuantumZipper.TV.tvDist
      ((P.map (fun ω j => X j ω + ∫ x, f.1 x * j x)).map (zbLocalPath U W))
      ((P.map (fun ω j => X j ω)).map (zbLocalPath U W)) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (QuantumZipper.dirichletEnergyOn U f.1) - 1)) :=
  (QuantumZipper.TV.tvDist_map_le (measurable_zbLocalPath U W)).trans
    (tvDist_zb_shift_le hadm hne hX f)

/-- Countable observables on local mean-zero tests, suitable for maximal coupling. -/
def zbCountablePath (U : TopologicalSpace.Opens ℂ) (W : Set ℂ)
    (e : ℕ → ZBLocalTest U W) (ξ : TestOn U → ℝ) : ℕ → ℝ :=
  fun n => ξ (e n).1

theorem measurable_zbCountablePath (U : TopologicalSpace.Opens ℂ) (W : Set ℂ)
    (e : ℕ → ZBLocalTest U W) : Measurable (zbCountablePath U W e) :=
  measurable_pi_iff.mpr fun n => measurable_pi_apply (e n).1

example : MeasurableEq (ℕ → ℝ) := inferInstance

theorem tvDist_zb_countable_shift_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : TopologicalSpace.Opens ℂ}
    {X : TestOn U → Ω → ℝ} (hadm : ZBAdmissible U)
    (hne : (U : Set ℂ).Nonempty) (hX : IsZBGFFProcess U X P)
    (W : Set ℂ) (e : ℕ → ZBLocalTest U W) (f : LQGMetric.MarkovZB.zsSub U) :
    QuantumZipper.TV.tvDist
      ((P.map (fun ω j => X j ω + ∫ x, f.1 x * j x)).map (zbCountablePath U W e))
      ((P.map (fun ω j => X j ω)).map (zbCountablePath U W e)) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (QuantumZipper.dirichletEnergyOn U f.1) - 1)) :=
  (QuantumZipper.TV.tvDist_map_le (measurable_zbCountablePath U W e)).trans
    (tvDist_zb_shift_le hadm hne hX f)

theorem tvDist_zb_countable_shift_le_min {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : TopologicalSpace.Opens ℂ}
    {X : TestOn U → Ω → ℝ} (hadm : ZBAdmissible U)
    (hne : (U : Set ℂ).Nonempty) (hX : IsZBGFFProcess U X P)
    (W : Set ℂ) (e : ℕ → ZBLocalTest U W) (f : LQGMetric.MarkovZB.zsSub U) :
    QuantumZipper.TV.tvDist
      ((P.map (fun ω j => X j ω + ∫ x, f.1 x * j x)).map (zbCountablePath U W e))
      ((P.map (fun ω j => X j ω)).map (zbCountablePath U W e)) ≤
      min 1 (ENNReal.ofReal (Real.sqrt
        (Real.exp (QuantumZipper.dirichletEnergyOn U f.1) - 1))) := by
  have : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  have hm : Measurable (fun ω j => X j ω) :=
    measurable_pi_iff.mpr hX.measurable
  have hms : Measurable (fun ω j => X j ω + ∫ x, f.1 x * j x) :=
    measurable_pi_iff.mpr fun j => (hX.measurable j).add_const _
  have : IsProbabilityMeasure (P.map (fun ω j => X j ω)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (P.map (fun ω j => X j ω + ∫ x, f.1 x * j x)) :=
    (Measure.isProbabilityMeasure_map_iff hms.aemeasurable).mpr inferInstance
  have he := measurable_zbCountablePath U W e
  have : IsProbabilityMeasure
      ((P.map (fun ω j => X j ω)).map (zbCountablePath U W e)) :=
    (Measure.isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure
      ((P.map (fun ω j => X j ω + ∫ x, f.1 x * j x)).map
        (zbCountablePath U W e)) :=
    (Measure.isProbabilityMeasure_map_iff he.aemeasurable).mpr inferInstance
  exact le_min QuantumZipper.TV.tvDist_le_one
    (tvDist_zb_countable_shift_le hadm hne hX W e f)

/-- The random-shift version on a countable family of mean-zero local tests. -/
theorem tvDist_zb_indep_shift_le {Ω T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace T] {P : Measure Ω} {U : TopologicalSpace.Opens ℂ}
    {X : TestOn U → Ω → ℝ} (hadm : ZBAdmissible U)
    (hne : (U : Set ℂ).Nonempty) (hX : IsZBGFFProcess U X P)
    (W : Set ℂ) (e : ℕ → ZBLocalTest U W) (c : Ω → T)
    (hc : Measurable c)
    (hi : IndepFun (fun ω j => X j ω) c P)
    (f : T → LQGMetric.MarkovZB.zsSub U)
    (hf : ∀ ψ : TestOn U, Measurable (fun t => ∫ x, (f t).1 x * ψ x))
    (hE : Measurable (fun t => QuantumZipper.dirichletEnergyOn U (f t).1)) :
    QuantumZipper.TV.tvDist
      (P.map (fun ω n => X (e n).1 ω + ∫ x, (f (c ω)).1 x * (e n).1 x))
      (P.map (fun ω n => X (e n).1 ω)) ≤
      ∫⁻ t, min 1 (ENNReal.ofReal (Real.sqrt
        (Real.exp (QuantumZipper.dirichletEnergyOn U (f t).1) - 1))) ∂(P.map c) := by
  have : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  let Y : Ω → TestOn U → ℝ := fun ω j => X j ω
  let F : (TestOn U → ℝ) × T → ℕ → ℝ := fun p n =>
    p.1 (e n).1 + ∫ x, (f p.2).1 x * (e n).1 x
  let F₀ : (TestOn U → ℝ) × T → ℕ → ℝ := fun p n => p.1 (e n).1
  let δ : T → ℝ≥0∞ := fun t => min 1 (ENNReal.ofReal (Real.sqrt
    (Real.exp (QuantumZipper.dirichletEnergyOn U (f t).1) - 1)))
  have hY : Measurable Y := measurable_pi_iff.mpr hX.measurable
  have hF : Measurable F := measurable_pi_iff.mpr fun n =>
    ((measurable_pi_apply (e n).1).comp measurable_fst).add
      ((hf (e n).1).comp measurable_snd)
  have hF₀ : Measurable F₀ := measurable_pi_iff.mpr fun n =>
    (measurable_pi_apply (e n).1).comp measurable_fst
  have hδ : Measurable δ := by
    apply Measurable.min measurable_const
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp
        ((Real.continuous_exp.measurable.comp hE).sub_const 1))
  have hslice (t : T) :
      QuantumZipper.TV.tvDist
        ((P.map Y).map fun y => F (y, t))
        ((P.map Y).map fun y => F₀ (y, t)) ≤ δ t := by
    have hFt : Measurable (fun y => F (y, t)) :=
      hF.comp (measurable_id.prodMk measurable_const)
    have hF₀t : Measurable (fun y => F₀ (y, t)) :=
      hF₀.comp (measurable_id.prodMk measurable_const)
    rw [Measure.map_map hFt hY, Measure.map_map hF₀t hY]
    have hsm : Measurable (fun ω j => X j ω + ∫ x, (f t).1 x * j x) :=
      measurable_pi_iff.mpr fun j => (hX.measurable j).add_const _
    have hproj := measurable_zbCountablePath U W e
    have h1 : (P.map (fun ω j => X j ω + ∫ x, (f t).1 x * j x)).map
        (zbCountablePath U W e) = P.map (fun ω => F (Y ω, t)) := by
      rw [Measure.map_map hproj hsm]
      rfl
    have h0 : (P.map Y).map (zbCountablePath U W e) =
        P.map (fun ω => F₀ (Y ω, t)) := by
      rw [Measure.map_map hproj hY]
      rfl
    simp only [Function.comp_def]
    rw [← h1, ← h0]
    exact tvDist_zb_countable_shift_le_min hadm hne hX W e (f t)
  have hmain := QuantumZipper.D3Plus.tvDist_indep_mix_le
    hY.aemeasurable hc.aemeasurable hY.aemeasurable hc.aemeasurable
    hi hi hF hF₀ measurable_id δ hslice
  simpa only [Measure.map_id, QuantumZipper.TV.tvDist_self, add_zero] using hmain

theorem cmBound_tendsto_zero :
    Filter.Tendsto (fun E : ℝ => Real.sqrt (Real.exp E - 1))
      (nhds 0) (nhds 0) := by
  have h : ContinuousAt (fun E : ℝ => Real.sqrt (Real.exp E - 1)) 0 :=
    (Real.continuous_sqrt.comp (Real.continuous_exp.sub continuous_const)).continuousAt
  simpa using h.tendsto



end SupercriticalConformalCovariance.TV
