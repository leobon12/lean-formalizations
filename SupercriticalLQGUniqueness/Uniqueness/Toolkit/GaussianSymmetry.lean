import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LQGMetric.Field.CircleAvgGP
import LQGMetric.Field.CircleAvgRate
import LQGMetric.Field.CircleAvgBridge




 
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

theorem centredGaussian_map_neg_eq_self {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsGaussian μ]
    (hcenter : ∀ L : StrongDual ℝ E, μ[L] = 0) :
    μ.map (fun x => -x) = μ := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  have hmap : (μ.map (fun x : E => -x)).map L = (μ.map L).map (fun x : ℝ => -x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp
  rw [hmap, IsGaussian.map_eq_gaussianReal L, gaussianReal_map_neg,
    hcenter L, neg_zero]


theorem centredGaussian_vector_symmetry {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {Y : Ω → ι → ℝ}
    (hY : HasGaussianLaw Y P)
    (hcenter : ∀ i, ∫ ω, Y ω i ∂P = 0) :
    P.map (fun ω i => -Y ω i) = P.map Y := by
  let μ : Measure (ι → ℝ) := P.map Y
  have hmean : (∫ ω, Y ω ∂P) = (0 : ι → ℝ) := by
    funext i
    have hproj := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) hY.integrable
    simpa [hcenter i] using hproj.symm
  haveI : IsGaussian μ := hY.isGaussian_map
  have hμ : ∀ L : StrongDual ℝ (ι → ℝ), μ[L] = 0 := by
    intro L
    rw [integral_map hY.aemeasurable (by fun_prop)]
    rw [ContinuousLinearMap.integral_comp_comm L hY.integrable, hmean]
    exact map_zero L
  have hsym : μ.map (fun x => -x) = μ :=
    centredGaussian_map_neg_eq_self μ hμ
  calc
    P.map (fun ω i => -Y ω i) = (P.map Y).map (fun x => -x) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY.aemeasurable]
      rfl
    _ = P.map Y := hsym


namespace SupercriticalLQGUniqueness
open LQGMetric (DistC)
open Set

theorem normalized_raw_circleAvg_process {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) :
    IsGaussianProcess (fun p : Ioi (0 : ℝ) × ℂ =>
      fun ω => LQGMetric.circleAvg (h ω) (p.1 : ℝ) p.2) P := by
  let p₀ : Ioi (0 : ℝ) × ℂ := (⟨1, Set.mem_Ioi.mpr one_pos⟩, 0)
  have h0 : ∀ᵐ ω ∂P, LQGMetric.circleAvg (h ω) 1 0 = 0 :=
    hh.2.mono (fun _ hω => hω.limUnder_eq)
  have hGP := (LQGMetric.CircleAvg.isGaussianProcess_incProc hh.1).comp_right
    (fun p : Ioi (0 : ℝ) × ℂ => (p, p₀))
  refine hGP.congr ?_
  intro p
  filter_upwards [h0] with ω hω
  simp [LQGMetric.CircleAvg.incProc, LQGMetric.CircleAvg.cInc, p₀, hω]


theorem finite_circleAverage_symmetry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P)
    (I : Finset (Ioi (0 : ℝ) × ℂ))
    (a : (Ioi (0 : ℝ) × ℂ) → Ω → ℝ)
    (ha : ∀ p ∈ I, ∀ᵐ ω ∂P, IsCircleAverage (h ω) p.1 p.2 (a p ω)) :
    P.map (fun ω (i : I) => -a i.1 ω) = P.map (fun ω (i : I) => a i.1 ω) := by
  classical
  have hold : LQGMetric.IsNormalizedWPGFF h P :=
    ⟨hh.1, hh.2.mono (fun _ hω => hω.limUnder_eq)⟩
  obtain ⟨H, hH, _, hHae⟩ :=
    LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized hold
  let X : Ω → I → ℝ := fun ω i => H i.1.1 i.1.2 ω
  have hGaussian : HasGaussianLaw X P := by
    simpa only [X, Finset.restrict_def] using hH.isGaussianProcess.hasGaussianLaw I
  have hcenter : ∀ i : I, ∫ ω, X ω i ∂P = 0 := by
    intro i
    exact hH.integral_eq_zero i.1.1 i.1.1.2 i.1.2
  have hsym := centredGaussian_vector_symmetry hGaussian hcenter
  have hAe : ∀ i : I, (fun ω => a i.1 ω) =ᵐ[P] (fun ω => X ω i) := by
    intro i
    filter_upwards [ha i.1 i.2,
      hHae i.1.1 i.1.1.2 i.1.2] with ω hω hHω
    have hraw : LQGMetric.circleAvg (h ω) (i.1.1 : ℝ) i.1.2 = a i.1 ω :=
      hω.limUnder_eq
    exact hraw.symm.trans hHω.symm
  have hVec : (fun ω (i : I) => a i.1 ω) =ᵐ[P] X := by
    have hall : ∀ᵐ ω ∂P, ∀ i : I, a i.1 ω = X ω i :=
      ae_all_iff.2 hAe
    filter_upwards [hall] with ω hω
    funext i
    exact hω i
  have hNeg : (fun ω (i : I) => -a i.1 ω) =ᵐ[P]
      (fun ω (i : I) => -X ω i) := hVec.mono fun ω hω => by
    funext i
    exact congrArg Neg.neg (congrFun hω i)
  calc
    P.map (fun ω (i : I) => -a i.1 ω) =
        P.map (fun ω (i : I) => -X ω i) := Measure.map_congr hNeg
    _ = P.map X := hsym
    _ = P.map (fun ω (i : I) => a i.1 ω) := (Measure.map_congr hVec).symm

end SupercriticalLQGUniqueness

