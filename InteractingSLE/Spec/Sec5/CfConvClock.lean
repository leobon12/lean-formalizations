/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvRecord

/-!
# The physical clock of the infinite image trace

Packet PROVE-CFCHART2. Compose the inverse capacity clock with the killed-curve time change.
The result is continuous, strictly increasing, starts at zero, and identifies every positive
time of the image trace with the physical curve in the stopped record chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfConv

open LawUnique CfGiven CfChart Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Sec7.Lemma71C (capInv capInv_nonneg)
open WangWu (negInv)

/-- Physical time as a function of image capacity time. -/
def imageClock (γ : ℝ → ℂ) (S : Set ℝ) (u : ℝ≥0) : ℝ≥0 :=
  (kcTime S (capInv (kcCurve γ S) u)).toNNReal

section Clock

variable {γ : ℝ → ℂ} {S : Set ℝ}

theorem coe_imageClock (hγ : IsKilledCurve γ S) (u : ℝ≥0) :
    (imageClock γ S u : ℝ) = kcTime S (capInv (kcCurve γ S) u) :=
  Real.coe_toNNReal _ (hγ.kcTime_nonneg (capInv_nonneg _ _))

theorem imageClock_zero (hγ : IsKilledCurve γ S) : imageClock γ S 0 = 0 := by
  simp only [imageClock, NNReal.coe_zero, hγ.isDrivenCurve.capInv_of_nonpos le_rfl, kcTime_zero,
    Real.toNNReal_zero]

theorem continuous_imageClock (hγ : IsKilledCurve γ S) (htop : kcLife γ S = ⊤) :
    Continuous (imageClock γ S) := by
  have hinv : Continuous fun u : ℝ≥0 => capInv (kcCurve γ S) u := by
    apply continuous_iff_continuousAt.2
    intro u
    have hlt : ENNReal.ofReal (u : ℝ) < Sec7.Lemma71C.capLife (kcCurve γ S) := by
      change ENNReal.ofReal (u : ℝ) < kcLife γ S
      rw [htop]
      exact ENNReal.ofReal_lt_top
    have h1 := (hγ.isDrivenCurve.continuousWithinAt_capInv u.coe_nonneg hlt).comp
      NNReal.continuous_coe.continuousAt.continuousWithinAt (s := univ) (fun r _ => r.coe_nonneg)
    exact h1.continuousAt Filter.univ_mem
  exact continuous_real_toNNReal.comp
    ((IsKilledCurve.continuousOn_kcTime (P := S)).comp_continuous hinv (fun u => capInv_nonneg _ _))

theorem strictMono_imageClock (hγ : IsKilledCurve γ S) (htop : kcLife γ S = ⊤) :
    StrictMono (imageClock γ S) := by
  intro a b hab
  rw [← NNReal.coe_lt_coe, coe_imageClock hγ, coe_imageClock hγ]
  apply hγ.strictMonoOn_kcTime (capInv_nonneg _ _) (capInv_nonneg _ _)
  apply hγ.isDrivenCurve.capInv_lt_capInv a.coe_nonneg (NNReal.coe_lt_coe.2 hab)
  change ENNReal.ofReal (b : ℝ) < kcLife γ S
  rw [htop]
  exact ENNReal.ofReal_lt_top

theorem imageClock_mem (hγ : IsKilledCurve γ S) (u : ℝ≥0) : (imageClock γ S u : ℝ) ∈ S := by
  rw [coe_imageClock hγ]
  exact hγ.kcTime_mem (capInv_nonneg _ _)

theorem kcTr_eq_imageClock (hγ : IsKilledCurve γ S) (u : ℝ≥0) :
    kcTr γ S u = γ (imageClock γ S u) := by
  rw [coe_imageClock hγ]
  rfl

end Clock

section Physical

variable {Z : Type*} [MeasurableSpace Z] {nL nR : ℕ} {W : ℝ≥0 → Z → ℝ}
  {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ} {ζ : Z → ℝ≥0∞}
  {s : ℝ≥0} {E : Set (Z × HistorySpace 0 0)} {p : Z × HistorySpace 0 0}

/-- The whole image trace pulls back to the physical history in the actual record chart. -/
theorem exists_physical_clock (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E)
    (htop : qT W VL VR ζ s E p = ⊤) (he : IsRegularDriver ((fun t => W t p.1), ζ p.1)) :
    ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
      ∀ u : ℝ≥0, 0 < u → negInv (qTr W VL VR ζ s E p u) ∈ H ∧
        negInv (WangWu.histLine p.2 (ℓ u)) =
          (recChart (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1))).2.1
            (negInv (qTr W VL VR ζ s E p u)) := by
  have hg := hEg p hp
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  change kcLife (qgCurve W s E p) (qgPre W VL VR ζ s E p) = ⊤ at htop
  let ℓ := imageClock (qgCurve W s E p) (qgPre W VL VR ζ s E p)
  refine ⟨ℓ, continuous_imageClock hγ htop, strictMono_imageClock hγ htop, imageClock_zero hγ, ?_⟩
  intro u hu
  have hℓ : 0 < ℓ u := by simpa only [imageClock_zero hγ] using strictMono_imageClock hγ htop hu
  have hmem : (ℓ u : ℝ) ∈ qgPre W VL VR ζ s E p := imageClock_mem hγ u
  rw [qgPre_of_mem hp, qObs_of_good hg] at hmem
  have hqH : qTr W VL VR ζ s E p u ∈ H :=
    hγ.kcTr_mem_H hu (by rw [htop]; exact WithTop.coe_lt_top u)
  refine ⟨WangWu.negInv_mem_H hqH, ?_⟩
  have hqt : qTr W VL VR ζ s E p u = WangWu.revChart (fDrv W p) s (WangWu.histLine p.2 (ℓ u)) := by
    have heq : qTr W VL VR ζ s E p u = qgCurve W s E p (ℓ u) := kcTr_eq_imageClock hγ u
    rwa [qgCurve_of_mem hp, WangWu.imgCurve_of_pos (by exact_mod_cast hℓ)] at heq
  have hback := WangWu.revChartInv_revChart (continuous_fDrv hg) (fDrv_zero hg) s.coe_nonneg
    ⟨histLine_mem_H hg (by exact_mod_cast hℓ), hmem.2 _ ⟨hmem.1, le_rfl⟩⟩
  rw [← hqt] at hback
  have hb := congrArg negInv hback
  rw [WangWu.revChartInv, WangWu.negInv_negInv] at hb
  change negInv _ = (cfChart (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1))).2.1 _
  rw [← fChart_eq_cfChart hg he, fChart_inv_eq hg hqH]
  exact hb.symm

end Physical

/-- Identify the trace read from an infinite counterflow history with any generating trace. -/
theorem ae_histLine_cfHistory_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {η : Ω → ℝ≥0 → ℂ} (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)) :
    ∀ᵐ ω ∂P, WangWu.histLine (Cond44Ref.cfHistory W ζ ω) = fun s : ℝ => η ω s.toNNReal := by
  obtain ⟨b, J, g, _, _, hd⟩ := hcf
  obtain ⟨g', 𝓕, VL, VR, B, _, hC⟩ := hd
  filter_upwards [hζ, hη, hC.1.2.2.2.2] with ω hζω hηω hp
  have hc : Continuous fun t => W t ω := by
    have hc := hp.2.2.2.1
    rw [hζω] at hc
    exact continuousOn_univ.1 (hc.mono fun t _ => ENNReal.coe_lt_top)
  rw [CfRegQ.histLine_eq_traceAt, GlueCond.hDrv_cfHistory hζω hc]
  funext s
  exact LP.traceAt_eq_of_isGeneratingTrace hηω hc.continuousOn hp.1 ENNReal.coe_lt_top

end InteractingSLE.Sec5.CfConv
