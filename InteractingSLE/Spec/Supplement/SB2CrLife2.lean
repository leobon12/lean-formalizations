/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrK2

/-!
# (I4) at the root: the canonical lifetime is the relative lifetime

Packet PROVE-SB2-CONDFIN (round 8, D44). `Ci.ae_canonLife_eq_relLife` for the root's versions in B's own time. The
canonical code's threshold property comes from the law of the chart field given a σ-algebra `𝒢` on an event `FB ∈ 𝒢`
that contains the root event `Fr` (in D44's B-time form: `𝒢 = lineFiltC 𝓖 0`, `FB` the stage event with
`relOff ≥ ℓ` and `0 < ζ_ℓ`, F3LAW's law). Everything else (the stop match, (I4), `V_sup`) is used on `Fr` only.

* **`ae_canonLife_eq_relLife_root`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cr

open Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly Lv Supp8.Q3Stop Ms Mu
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ ψ : ℝ} {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {Fr FB : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
  {Φ : Ω → Chart} {c : Ω → BoundaryWord} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
  {L relLife : Ω → ℝ≥0∞}

/-- **(I4) at the root: the canonical lifetime is the relative lifetime**, almost surely on the root event, with the
law of the chart field on a `𝒢`-event containing the root event. -/
theorem ae_canonLife_eq_relLife_root (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (S : RootVersionS κ ψ P Fr 𝓖 A₁ A₂ Φ c types pc tL L relLife) (h𝒢 : 𝒢 ≤ mΩ)
    (hFB : MeasurableSet[𝒢] FB) (hFrB : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ FB) (hc : Measurable[𝒢] c)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ FB → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y (c ω₀).fn (c ω₀).jumps)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ ψ (c ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c Fr w → ω ∈ seedCell κ ψ c Fr w)
    (hstop : ∀ᵐ ω ∂P, ω ∈ Fr → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ (c ω, Y ω))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c Fr w → relLife ω < ⊤ →
        (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
        FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ c w) (cellXR κ ψ c w) ω ≤ relLife ω) :
    ∀ᵐ ω ∂P, ω ∈ Fr → (driverCode h12p hκ ψ (c ω, Y ω)).2 = relLife ω := by
  have hE : ∀ r : ℚ, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c FB w →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w)
        (frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal) (cellXL κ ψ c w) (cellXR κ ψ c w) ω :=
    fun r w _ => ae_lt_thr_frozenCanon h12p h13 hκ ψ h𝒢 hFB hc hY hlaw w (r : ℝ).toNNReal
  have hL : ∀ r : ℚ, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c Fr w → relLife ω < ⊤ →
      (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal t ω = (S.ver m).W t ω) →
      FCDet.thr (typedRhoL w) (typedRhoR w) (frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal) (cellXL κ ψ c w)
        (cellXR κ ψ c w) ω ≤ relLife ω :=
    fun r w hw => hlife w hw _ (continuous_frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal)
  filter_upwards [ae_all_iff.2 fun r => (ae_ball_iff htypes).2 (hE r),
    ae_all_iff.2 fun r => (ae_ball_iff htypes).2 (hL r), (ae_ball_iff htypes).2 hseed, hcover, hstop, S.V_sup,
    hFrB] with ω hEω hLω hsω hcov hst hsup hrB hFω
  have hst' := hst hFω
  have hge : relLife ω ≤ (driverCode h12p hκ ψ (c ω, Y ω)).2 := by
    rw [← hsup hFω]
    exact le_of_stops hst'
  refine le_antisymm ?_ hge
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (c ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ types := hw₀e ▸ hcov hFω
  have hcell : ω ∈ wordTypeCell κ ψ c Fr w₀ := ⟨hFω, hw₀e⟩
  have hcellB : ω ∈ wordTypeCell κ ψ c FB w₀ := ⟨hrB hFω, hw₀e⟩
  have hseedω := hsω w₀ hw₀ hcell
  have hfin : relLife ω < ⊤ := lt_of_lt_of_le hlt le_top
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have hq : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r := rfl
  have hq1 : relLife ω < (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := hq ▸ hr1
  have hq2 : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 := hq ▸ hr2
  have h1 := hEω r w₀ hw₀ hcellB hq2
  have hcont : ∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω →
      frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal t ω = (S.ver m).W t ω := by
    intro m t ht
    have hVr : S.V m ω ≤ relLife ω := (hsup hFω) ▸ le_iSup (fun m => S.V m ω) m
    have htq : t ≤ (r : ℝ).toNNReal := by
      have : (t : ℝ≥0∞) < (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := lt_of_lt_of_le ht (hVr.trans hq1.le)
      exact (ENNReal.coe_lt_coe.1 this).le
    obtain ⟨-, hagree⟩ := eqOn_of_isStopDrvMatch_of_isDriverCodeMatch (hst' m)
      (isDriverCodeMatch_driverOf h12p hκ ψ (c ω, Y ω)) ((S.ver m).W_cont ω).continuousOn
      (continuousOn_driverOf h12p hκ ψ (c ω, Y ω))
    simp only [frozenCanon, hq2, ↓reduceIte, min_eq_left htq]
    exact (hagree t ht).symm
  have h2 := hLω r w₀ hw₀ hseedω hfin hcont
  exact absurd (lt_of_lt_of_le h1 h2) (not_lt.2 hq1.le)

end InteractingSLE.Theorem14.SB.Cr
