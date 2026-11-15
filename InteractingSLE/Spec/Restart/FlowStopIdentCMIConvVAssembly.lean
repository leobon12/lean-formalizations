/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVTower
import InteractingSLE.Spec.Restart.FCDet

/-!
# Assemble a stopped coupling from the converse, its clock, and locality

The driving equations are supplied by the landed converse theorem. The
pre-stop kernel passes to the reference driving filtration by the tower
property, reaches the terminal stop from below, and lifts to the independent
Brownian enlargement through the existing product-transfer theorem.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (fwdHull)
open LQGMetric (TestOn DistOn)
open Sec7.PocketTraversal StoppedExtend Coupling

/-- The positive-clock converse assembly, with locality as its separate geometric input. -/
theorem exists_stoppedHullCoupling_prod_of_clock
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxLa : Antitone xL) (hxRm : Monotone xR)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hWa : StronglyAdapted 𝓖 W)
    {e : Ω → ℝ≥0∞} (he : IsStoppingTime 𝓖 fun ω => (e ω : WithTop ℝ≥0))
    (hnull : ∀ A, MeasurableSet A → P A = 0 → MeasurableSet[𝓖 0] A)
    {T : ℕ → Ω → ℝ≥0} (hT : IsAnnouncingSeq 𝓖 P e T)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) P)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W
      (geomLW W fun _ => xL) (geomRW W fun _ => xR) e X)
    (hthr : ∀ᵐ ω ∂P, e ω ≤ MartChar.thresholdTime ρL ρR (W · ω)
      (fun i t => geomLW W (fun _ => xL) i t ω) (fun j t => geomRW W (fun _ => xR) j t ω))
    (hXP : IsMeasurableKilledDriving W (geomLW W fun _ => xL) (geomRW W fun _ => xR) e)
    (hle : drivingFiltration P hXP ≤ 𝓖)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime (drivingFiltration P hXP) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσe : ∀ᵐ ω ∂P, ∀ n, (σ n ω : ℝ≥0∞) < e ω)
    (hσlim : ∀ᵐ ω ∂P, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (e ω)))
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (_hτ : IsStoppingTime (drivingFiltration P hXP) τ),
      (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) ≤ e ω ∧ τ ω ≠ ⊤) →
      IsLocalSet (fun ω => fwdHull (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0)) X P) :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν)
      (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × (ℕ → ℝ))))
      (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsStoppedHullCoupling κ xL xR ρL ρR (P.prod ν) 𝓕 (fun t p => W t p.1)
        (fun i t p => geomLW W (fun _ => xL) i t p.1)
        (fun j t p => geomRW W (fun _ => xR) j t p.1) B (fun p => e p.1) (fun p => X p.1) := by
  obtain ⟨ν, hν, 𝓦, B, hE, -, -⟩ := StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
    (𝒢 := ⊥) (F := Set.univ) hκ hnull bot_le MeasurableSet.univ measurable_const measurable_const
    (fun _ => hxL) (fun _ => hxR) (fun _ => hxLa) (fun _ => hxRm) hW0 hWc hWa he hT hint hcf
    (hthr.mono fun ω h _ => h)
  refine ⟨ν, hν, WholeField.prodFiltration 𝓖 𝓦, B, ?_⟩
  obtain ⟨-, -, -, -, hB, hW, hVL, hVR, hp⟩ := hE
  have hreg := FCDet.isForceReg_thr hW0 hWc (fun _ => xL) (fun _ => xR) e
  have hregTop := FCDet.isForceReg_thr hW0 hWc (fun _ => xL) (fun _ => xR) (fun _ => ⊤)
  have hcfD := isCouplingCharFun_driving_of_le hXP hle (ae_of_all _ hreg) hXm hcf
  have hμ : (P.prod ν).map Prod.fst = P := Measure.map_fst_prod.trans (by simp)
  have hXprod := Exist.isMeasurableKilledDriving_comp hXP (measurable_fst (α := Ω) (β := ℕ → ℝ))
  refine ⟨⟨hB, hW, hVL, hVR, hp.mono fun p h => h trivial⟩, ?_, hXm.comp measurable_fst, ?_,
    hXprod, fun τ hτ hτe => ?_⟩
  · exact ae_of_all _ fun p _ _ =>
      ((hWc p.1).prodMk ((continuous_pi fun i => (isForcePath_geomLW hWc (fun _ => xL) p.1 i).1).prodMk
        (continuous_pi fun j => (isForcePath_geomRW hWc (fun _ => xR) p.1 j).1))).continuousOn
  · intro u₀ hu₀
    have hg := hgff u₀ hu₀
    rw [← hμ] at hg
    exact isZBGFFProcess_comp measurable_fst hg
  · obtain ⟨s, hs, hτs⟩ := FlowStopIdentLift.exists_stop_factor hμ hXP hτ
      (hτe.mono fun _ h => h.2)
    have hse : ∀ᵐ ω ∂P, ((s ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ e ω ∧ (s ω : WithTop ℝ≥0) ≠ ⊤ := by
      apply ConverseBefore.ae_of_ae_fst (P₀ := ν)
      filter_upwards [hτe, hτs] with p hp hsω
      rwa [hsω] at hp
    exact FlowStopIdentLift.hullClauses_fst hμ hXm hXP hτ hs hτs
      (ae_of_all _ fun ω => (hWc ω).comp continuous_real_toNNReal |>.continuousOn)
      (hloc _ hs hse) (fun u hu φ => StoppedK2.condExp_cexp_eq_of_le_stop hXP
        (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hXm) hcfD (ae_of_all _ hregTop)
        hσ hσm hσe hσlim hs hse u hu φ)

end InteractingSLE.Restart.FlowStopIdentCMI
