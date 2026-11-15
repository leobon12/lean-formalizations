/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuI4P

/-!
# (I4): the canonical lifetime is the relative lifetime

Packet PROVE-SB2-LCMEAN, round 13 (handoff §R13.4). For SB2(2)'s relative versions at announced stops whose frozen
drivers match the canonical driver code before every stop (`Mu.ae_isStopDrvMatch_of_lines`), with F2b′'s
version-level (I4) (`Mu.SB2LowerStageVersionStatement2`) and the conditional GFF law of the chart field on the live
event, almost surely on the live event the canonical code's lifetime is the relative lifetime:

* `≥`: the stops increase to the relative lifetime and each is at most the code's lifetime (`Mu.le_of_stops`);
* `≤`: otherwise pick a rational `q` strictly between; the canonical driver frozen at `q` continues every frozen
  driver, so F2b′ bounds its threshold time by the relative lifetime `< q`, while the canonical flow line has no
  threshold up to `q` (`Mu.ae_lt_thr_frozenCanon`).

* **`ae_canonLife_eq_relLife`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly Lv Supp8.Q3Stop Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- The canonical driver code matches its own driver. -/
theorem isDriverCodeMatch_driverOf (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (ψ : ℝ)
    (q : BoundaryWord × DistOn upperHalfPlaneOpens) :
    IsDriverCodeMatch (driverCode h12p hκ ψ q) (driverOf h12p hκ ψ q).1 (driverOf h12p hκ ψ q).2 := by
  refine ⟨rfl, ?_, fun n k _ => rfl⟩
  show (driverOf h12p hκ ψ q).1 0 = (driverOf h12p hκ ψ q).1 (dyad 0 0)
  rw [Exist.dyad_zero_zero]

theorem continuousOn_driverOf (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (ψ : ℝ)
    (q : BoundaryWord × DistOn upperHalfPlaneOpens) :
    ContinuousOn (driverOf h12p hκ ψ q).1 {t | (t : ℝ≥0∞) < (driverOf h12p hκ ψ q).2} := by
  obtain ⟨c, f⟩ := q
  rw [driverOf_mk]
  exact (drvOf_regular _).1

variable {κ ψ : ℝ} {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
  {Φ : Ω → Chart} {c : Ω → BoundaryWord} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
  {L relLife : Ω → ℝ≥0∞}

/-- **(I4): the canonical lifetime is the relative lifetime**, almost surely on the live event. -/
theorem ae_canonLife_eq_relLife (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (S : StageVersionS κ ψ P F 𝓖 A₁ A₂ Φ c types pc tL L relLife) (h𝒢 : 𝒢 ≤ mΩ)
    (hF : MeasurableSet[𝒢] F) (hc : Measurable[𝒢] c) {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y (c ω₀).fn (c ω₀).jumps)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (c ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w → ω ∈ seedCell κ ψ c F w)
    (hstop : ∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ (c ω, Y ω))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c F w → relLife ω < ⊤ →
        (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
        FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ c w) (cellXR κ ψ c w) ω ≤ relLife ω) :
    ∀ᵐ ω ∂P, ω ∈ F → (driverCode h12p hκ ψ (c ω, Y ω)).2 = relLife ω := by
  have hE : ∀ r : ℚ, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w)
        (frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal) (cellXL κ ψ c w) (cellXR κ ψ c w) ω :=
    fun r w _ => ae_lt_thr_frozenCanon h12p h13 hκ ψ h𝒢 hF hc hY hlaw w (r : ℝ).toNNReal
  have hL : ∀ r : ℚ, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c F w → relLife ω < ⊤ →
      (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal t ω = (S.ver m).W t ω) →
      FCDet.thr (typedRhoL w) (typedRhoR w) (frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal) (cellXL κ ψ c w)
        (cellXR κ ψ c w) ω ≤ relLife ω :=
    fun r w hw => hlife w hw _ (continuous_frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal)
  filter_upwards [ae_all_iff.2 fun r => (ae_ball_iff htypes).2 (hE r),
    ae_all_iff.2 fun r => (ae_ball_iff htypes).2 (hL r), (ae_ball_iff htypes).2 hseed, hcover, hstop, S.V_sup]
    with ω hEω hLω hsω hcov hst hsup hFω
  have hst' := hst hFω
  have hge : relLife ω ≤ (driverCode h12p hκ ψ (c ω, Y ω)).2 := by
    rw [← hsup hFω]
    exact le_of_stops hst'
  refine le_antisymm ?_ hge
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (c ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ types := hw₀e ▸ hcov hFω
  have hcell : ω ∈ wordTypeCell κ ψ c F w₀ := ⟨hFω, hw₀e⟩
  have hseedω := hsω w₀ hw₀ hcell
  have hfin : relLife ω < ⊤ := lt_of_lt_of_le hlt le_top
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have hq : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r := rfl
  have hq1 : relLife ω < (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := hq ▸ hr1
  have hq2 : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 := hq ▸ hr2
  have h1 := hEω r w₀ hw₀ hcell hq2
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

end InteractingSLE.Theorem14.SB.Mu
