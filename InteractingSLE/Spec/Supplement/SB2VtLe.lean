/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsVer
import InteractingSLE.Spec.Supplement.SBS3DwVsRead
import InteractingSLE.Spec.Supplement.SBS3DwEntr

/-!
# SB2(1)'s successor versions for upper angles `ψ ≤ π/2` (decision D22)

Packet PROVE-AUX61-NOJUMP (round 19). Decision D22 drops the all-angle Lemma S3
(`Tc.SB2EntranceNoCommonArcStatement`); SB2(1) is used only for `ψ ≤ π/2`, where Lemma S3 is PROVED from Theorems
1.2–1.3 (`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Round 18 isolated S3 in the stop data's constructor; this file
gives the bounded forms of those few steps, with PROVE-R6-CORNER's bounded copies (`SBS3Dw*`, `…Le`):

* `lift_inv_of_lineGeomAt` (deterministic): the inverse chart reads the flow from the whole lift, from one sample's
  geometric record (`Vs.ae_lift_inv'` without S3);
* **`SB2RelSeedAdmLeStatement`**: the relative seed for launch problems with `ψ ≤ π/2`;
* `ae_goodAtLe`, `exists_stopDataLe`: the good samples and the stop data;
* **`nonempty_versionSLe`**, **`sb2LineVersionSLeStatement`** and **`sb2LineVersionSLeStatement_of_thm`**: SB2DRV's
  successor structure `Lv.SB2LineVersionS` for every launch problem with `ψ ≤ π/2`, from Theorems 1.2–1.3 and the
  relative seed;
* `sb2RelSeedAdmLeStatement_of_versionS`: conversely the successor structure forces the relative seed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vt

open Vs Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C Supp8.Q3Stop

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- **One extension of the chart's inverse reads the flow from the whole lift** (`Vs.ae_lift_inv'` at one sample,
from its geometric record). -/
theorem lift_inv_of_lineGeomAt (hrec : LineGeomAt κ b jumps E k u η ζ ω)
    (hT : Ve.entT κ b jumps E k u η ζ ω < ζ ω) :
    ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
      EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
      ∀ r : ℝ≥0,
      (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
      0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
      g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) - u := by
  have hTL : Ve.entT κ b jumps E k u η ζ ω ≠ ⊤ := ne_top_of_lt hT
  set t₀ : ℝ≥0 := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with ht₀
  have hcoe : ((t₀ : ℝ≥0) : ℝ≥0∞) = Ve.entT κ b jumps E k u η ζ ω := ENNReal.coe_toNNReal hTL
  have e2 : (Ve.entT κ b jumps E k u η ζ ω).toReal = (t₀ : ℝ) := rfl
  -- a record with a horizon beyond any given relative time `r` before the life
  have hrecAt : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ (T : ℝ≥0) (S₁ : ℝ), (T : ℝ≥0∞) ≤ ζ ω ∧
      Ve.entT κ b jumps E k u η ζ ω < T ∧ 0 < S₁ ∧ (Ve.entT κ b jumps E k u η ζ ω).toReal + S₁ < T ∧
      (r : ℝ) < S₁ := by
    intro r hr
    by_cases hζ : ζ ω = ⊤
    · refine ⟨t₀ + r + 2, r + 1, by rw [hζ]; exact le_top, ?_, by positivity, ?_, by linarith⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; push_cast; linarith [r.2]
      · rw [e2]; push_cast; linarith
    · set Zt : ℝ≥0 := (ζ ω).toNNReal with hZt
      have hZc : ((Zt : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
      have hr' : (t₀ : ℝ) + r < Zt := by
        rw [← hZc, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add] at hr; exact hr
      refine ⟨Zt, ((r : ℝ) + (Zt - t₀)) / 2, hZc.le, ?_, ?_, ?_, ?_⟩
      · rw [← hcoe, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]; linarith [r.2]
      · linarith [r.2]
      · rw [e2]; linarith
      · linarith
  -- the facts of one record at a relative time below its horizon
  have hread : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
      EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
      0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
      g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω (t₀ + r) - u := by
    intro r hr
    obtain ⟨T, S₁, hTζ, hvis, hS₁, hS₁T, hrS⟩ := hrecAt r hr
    obtain ⟨p, g, β', γ, tL, Wr, ηr, -, ⟨-, hgc, hgi, -, -⟩, ⟨-, -, -, -, htL, hγp, -, hlift⟩, hag, -, hlo⟩ :=
      hrec T hTζ hvis S₁ hS₁ hS₁T
    have htL' : t₀ = tL := by
      have := congrArg ENNReal.toNNReal htL
      rw [ENNReal.toNNReal_coe] at this
      exact this.symm
    have hγr : Ve.flowLift κ b jumps E k u η ζ ω r = γ r := by
      rw [hlo r hrS, ← htL']
      rfl
    refine ⟨g, hgc, hgi, by rw [hγr]; exact hγp.2.2.1 r, ?_⟩
    rw [hγr, hlift r, htL', hag (tL + r) (by push_cast; linarith)]
  -- one extension for all times
  obtain ⟨g₀, hg₀c, hg₀i⟩ : ∃ g₀ : ℂ → ℂ, ContinuousOn g₀ {z | 0 ≤ z.im} ∧
      EqOn g₀ (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H := by
    have h0 : ((t₀ + 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [add_zero, hcoe]; exact hT
    obtain ⟨g, hgc, hgi, -, -⟩ := hread 0 h0
    exact ⟨g, hgc, hgi⟩
  refine ⟨g₀, hg₀c, hg₀i, fun r hr => ?_⟩
  obtain ⟨g, hgc, hgi, him, hval⟩ := hread r hr
  refine ⟨him, ?_⟩
  rw [Vn.eqOn_closedH_of_eqOn_H hg₀c hgc (hg₀i.trans hgi.symm) him]
  exact hval

end

/-- **The relative seed for upper angles `ψ ≤ π/2`** (`Vs.SB2RelSeedAdmStatement` for launch problems with the
bound): almost surely on the entrance event, the relative seed of the launch word's type is not at its threshold. -/
def SB2RelSeedAdmLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀),
    ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ I.word D.event w →
      ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ ψ I.word w ω) (cellXR κ ψ I.word w ω)

/-- The all-angle seed gives the bounded one. -/
theorem sb2RelSeedAdmLeStatement_of_all (h : SB2RelSeedAdmStatement.{u}) : SB2RelSeedAdmLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h' E k u ψ η ζ HP _ I u₀ D => h κ b jumps P h' E k u ψ η ζ HP I u₀ D

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **Almost every sample of the entrance event is good** (`Vs.ae_goodAt` for `ψ ≤ π/2`). -/
theorem ae_goodAtLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (hseedS : SB2RelSeedAdmLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {a : ℝ≥0 → Ω → ℝ≥0∞}
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
  filter_upwards [hae, hρ, Vk.ae_isDrivenCurve_familyLe h13 hS3 HP hρ, Vk.ae_capLife_eqLe h13 hS3 HP hρ,
    D.ae_mem_event_iff, Vd.ae_clockDataLe h13 hS3 HP, I.chart_eq,
    Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow, Vr.ae_tip_bad_of_isFlowLine HP.flow,
    Vr.ae_notMem_closure_badSet HP.kappa_pos HP.kappa_lt_four HP.boundary HP.field HP.flow, I.cover, hseed,
    Vc.ae_lineGeom_liftOfLe h13 hS3 HP]
    with ω hc hfam hdr hcl hev hcd hch hreg htip hnv hcov hsd hgeo hD
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hD
  have hT : Ve.entT κ b jumps E k u η ζ ω < ζ ω := (hev hl).1 hD
  exact ⟨hl, hT, (hfam hl hT).1, (hfam hl hT).2, hdr hl hT, hcl hl hT, hc hl hT, (hcd hl hT).1,
    fun T₁ h1 h2 => ((hcd hl hT).2 T₁ h1 h2).2, lift_inv_of_lineGeomAt (hgeo hl) hT, hch hl, hreg.1,
    hreg.2.2.2.2, htip, hnv, hcov hl, hsd _ (hcov hl) ⟨hD, rfl⟩, hgeo hl⟩

/-- **The stop data exist** (`Vs.exists_stopData` for `ψ ≤ π/2`). -/
theorem exists_stopDataLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (hseedS : SB2RelSeedAdmLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    Nonempty (SB2StopData HP I D) := by
  obtain ⟨a, ha, hac, ham, ha0, hae⟩ := Vg.exists_versionClockLe h13 hS3 HP I D
  have ha' : ∀ t, Measurable (a t) := fun t => (ha t).mono ((D.lineFiltC HP).le t) le_rfl
  obtain ⟨ρ, hρm, hρ⟩ := Vk.exists_drivenFamilyLe h13 hS3 HP I D ha' hae
  obtain ⟨G, hGm, hGnull, hG⟩ := Vf.exists_measurable_conull (ae_goodAtLe h13 hS3 hseedS HP I D hae hρ)
  have hgood : ∀ ω ∈ G ∩ D.event, GoodAt η ζ I a ρ ω := fun ω hω => hG ω hω.1 hω.2
  exact ⟨⟨a, ha, hac, ham, ha0, hae, ρ, hρm, hρ, G, hGm, hGnull, hgood,
    Vs.exists_segReadingLe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull fun ω hω =>
      ⟨(hgood ω hω).launch, (hgood ω hω).ent, (hgood ω hω).driven, (hgood ω hω).life⟩⟩⟩

/-- **SB2(1)'s successor versions exist for `ψ ≤ π/2`.** -/
theorem nonempty_versionSLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (hseedS : SB2RelSeedAdmLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    Nonempty (SB2LineVersionS HP I D) :=
  let ⟨S⟩ := exists_stopDataLe h13 hS3 hseedS HP I D
  ⟨S.versionS⟩

end

/-- **SB2(1)'s successor versions for every launch problem with `ψ ≤ π/2`.** -/
def SB2LineVersionSLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀),
    Nonempty (SB2LineVersionS HP I D)

/-- **`SB2LineVersionSLeStatement` from Theorem 1.3, Lemma S3 for `ψ ≤ π/2` and the relative seed.** -/
theorem sb2LineVersionSLeStatement (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (hseedS : SB2RelSeedAdmLeStatement.{u}) :
    SB2LineVersionSLeStatement.{u} := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP _ I _ D =>
  nonempty_versionSLe h13 hS3 hseedS HP I D

/-- **`SB2LineVersionSLeStatement` from Theorems 1.2–1.3 and the relative seed** (Lemma S3 for `ψ ≤ π/2` PROVED,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). -/
theorem sb2LineVersionSLeStatement_of_thm (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hseedS : SB2RelSeedAdmLeStatement.{u}) : SB2LineVersionSLeStatement.{u} :=
  sb2LineVersionSLeStatement h13 (Tc.sb2EntranceNoCommonArcLeStatement_of_thm h12p h13 h12p₀ h13₀) hseedS

/-- **The successor versions force the relative seed** (for `ψ ≤ π/2`). -/
theorem sb2RelSeedAdmLeStatement_of_versionS (hV : SB2LineVersionSLeStatement.{u}) :
    SB2RelSeedAdmLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h E k u ψ η ζ HP _ I u₀ D =>
    ae_seed_of_versionS (hV κ b jumps P h E k u ψ η ζ HP I u₀ D).some

end InteractingSLE.Theorem14.SB.Vt
