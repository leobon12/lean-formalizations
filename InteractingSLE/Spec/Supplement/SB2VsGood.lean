/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsMeas

/-!
# SB2(1)'s good samples (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19).

* **`LineGeomAt`**: the geometric record at one sample (the conclusion of `Vc.ae_lineGeom_liftOf`).
* **`GoodAt`**: the facts at one sample used to build the stops (those of `sb2_sample`, of `exists_segReading` and
  the geometric record).
* **`ae_goodAt`**: almost surely on the entrance event every sample is good, from Theorem 1.3, Lemma S3 (SB2(1)'s
  form), Lemma G12 (proved), K2's launch inputs and the relative seed (`SB2RelSeedAdmStatement`). With the stop data
  (`SB2VsCons`) this is the only place, besides `exists_segReading` and `ae_lift_inv'`, where Lemma S3 enters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Exist.Staged Exist.StagedLaw Lv Sec7.PocketTraversal Supp8.Q3Stop

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The geometric record at one sample** (the conclusion of `Vc.ae_lineGeom_liftOf` at a launch): for every horizon
`T ≤ ζ` after the entrance and every `0 < S₁` with `T_L + S₁ < T`, the prefix path, the shifted launch chart, the S1
witness and S2 lift, the agreement before `t_L + S₁`, the relative chains, no real arc, and the lift `liftOf`. -/
def LineGeomAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ ζ ω →
    firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < T →
    ∀ S₁ : ℝ, 0 < S₁ →
      (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toReal + S₁ < T →
    ∃ (p : ℝ → ℂ) (g : ℂ → ℂ) (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      (ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
        (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
        p '' Icc 0 1 = (fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω) ∧
      (IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1))
          (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) ∧
        ContinuousOn g {z | 0 ≤ z.im} ∧
        EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
        (∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧
        FinRel.LiftRealOn (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω))) ∧
      (Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧ p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' ∧
        β' tL = realMin (p '' Icc 0 1) ∧
        ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ∧
        Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s, g (γ s) = β' (tL + s)) ∧
      (∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η ω t - u) ∧
      ((∀ S₀ : ℝ, 0 ≤ S₀ → S₀ < S₁ → FinRel.IsSB2RelChain (p '' Icc 0 1)
          (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω))
          β' γ tL S₀ Wr ηr) ∧
        interior {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) ∧
      (∀ s : ℝ≥0, (s : ℝ) < S₁ → γ s = Vc.liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
        (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u tL
        ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω) s)

/-- **The facts at a good sample.** -/
structure GoodAt (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (a : ℝ≥0 → Ω → ℝ≥0∞) (ρ : Ω → ℝ → ℂ) (ω : Ω) : Prop where
  launch : ω ∈ launchSet κ b jumps E (k + 1)
  ent : Ve.entT κ b jumps E k u η ζ ω < ζ ω
  fam1 : ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)
  fam2 : ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
    ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0)
  driven : IsDrivenCurve (ρ ω)
  life : Sec7.Lemma71C.capLife (ρ ω) = Vk.relLife κ b jumps E k u η ζ ω
  clock : ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
    (ζ ω) t
  c0 : Sec7.Lemma71C.capClock (fun r : ℝ => Ve.flowLift κ b jumps E k u η ζ ω r.toNNReal) 0 = 0
  mono : ∀ T₁ : ℝ≥0, (Ve.entT κ b jumps E k u η ζ ω).toNNReal ≤ T₁ → (T₁ : ℝ≥0∞) < ζ ω →
    MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ => Ve.flowLift κ b jumps E k u η ζ ω r.toNNReal)
      (Icc 0 ((T₁ : ℝ) - (Ve.entT κ b jumps E k u η ζ ω).toNNReal))
  inv : ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
    EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
    ∀ r : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
      0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
      g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) - u
  chart : iChart I ω = (Lv.launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω)
  cont : ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω}
  trans : ζ ω = ⊤ → Tendsto (fun t => ‖η ω t‖) atTop atTop
  tip : 0 < ζ ω → ζ ω ≠ ⊤ → IsBadPoint (flowLineXL b jumps u) (flowLineXR b jumps u)
    (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ) (η ω (ζ ω).toNNReal - u)
  avoid : 0 < ζ ω → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t - u ∉ sb2BadClosure κ b jumps u ψ
  cover : angleWordType κ ψ (I.word ω) ∈ I.types
  seed : ¬ ForceWord.ThresholdCondition (typedRhoL (angleWordType κ ψ (I.word ω)))
    (typedRhoR (angleWordType κ ψ (I.word ω))) 0 (cellXL κ ψ I.word (angleWordType κ ψ (I.word ω)) ω)
    (cellXR κ ψ I.word (angleWordType κ ψ (I.word ω)) ω)
  geom : LineGeomAt κ b jumps E k u η ζ ω

/-- **Almost every sample of the entrance event is good.** -/
theorem ae_goodAt (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (hseedS : SB2RelSeedAdmStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    {a : ℝ≥0 → Ω → ℝ≥0∞}
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
        (ζ ω) t)
    {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ D.event → GoodAt η ζ I a ρ ω := by
  have hseed := (ae_ball_iff I.types_countable).2 (hseedS κ b jumps P h E k u ψ η ζ HP I u₀ D)
  filter_upwards [hae, hρ, Vk.ae_isDrivenCurve_family h13 hS3 HP hρ, Vk.ae_capLife_eq h13 hS3 HP hρ,
    D.ae_mem_event_iff, Vd.ae_clockData h13 hS3 HP, ae_lift_inv' h13 hS3 HP, I.chart_eq,
    Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow, ae_tip_bad_of_isFlowLine HP.flow,
    ae_notMem_closure_badSet HP.kappa_pos HP.kappa_lt_four HP.boundary HP.field HP.flow, I.cover, hseed,
    Vc.ae_lineGeom_liftOf h13 hS3 HP]
    with ω hc hfam hdr hcl hev hcd hinv hch hreg htip hnv hcov hsd hgeo hD
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hD
  have hT : Ve.entT κ b jumps E k u η ζ ω < ζ ω := (hev hl).1 hD
  exact ⟨hl, hT, (hfam hl hT).1, (hfam hl hT).2, hdr hl hT, hcl hl hT, hc hl hT, (hcd hl hT).1,
    fun T₁ h1 h2 => ((hcd hl hT).2 T₁ h1 h2).2, hinv hl hT, hch hl, hreg.1, hreg.2.2.2.2, htip, hnv,
    hcov hl, hsd _ (hcov hl) ⟨hD, rfl⟩, hgeo hl⟩

end

end InteractingSLE.Theorem14.SB.Vs
