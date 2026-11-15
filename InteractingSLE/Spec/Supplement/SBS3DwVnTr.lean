/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VnTr
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVmSafe
import InteractingSLE.Spec.Supplement.SB2VmSafe
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeAsm
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwViRed
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkAsm
import InteractingSLE.Spec.Supplement.SBS3DwVkEnd
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SBS3DwVkFrz
import InteractingSLE.Spec.Supplement.SBS3DwVkLife
import InteractingSLE.Spec.Supplement.SBS3DwVkLink
import InteractingSLE.Spec.Supplement.SBS3DwVmAd

/-!
# Successor of `SB2VnTr` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VnTr` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_lift_invLe`;
* `ae_not_tendsto_lift_of_topLe`;
* `ae_ne_top_of_capTrace_tendstoLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vn

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **One extension of the chart's inverse reads the flow from the whole lift.** -/
theorem ae_lift_invLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧ ∀ r : ℝ≥0,
        (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
        0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
        g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) - u := by
  filter_upwards [Vc.ae_lineGeom_liftOfLe h13 hS3 HP] with ω hrec hl hT
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
      hrec hl T hTζ hvis S₁ hS₁ hS₁T
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
  refine ⟨g₀, hg₀c, fun r hr => ?_⟩
  obtain ⟨g, hgc, hgi, him, hval⟩ := hread r hr
  refine ⟨him, ?_⟩
  rw [eqOn_closedH_of_eqOn_H hg₀c hgc (hg₀i.trans hgi.symm) him]
  exact hval

/-- **Transience in the launch chart**: on `{ζ = ∞}` the lift has no finite limit at `∞`. -/
theorem ae_not_tendsto_lift_of_topLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω → ζ ω = ⊤ →
      ∀ z : ℂ, ¬ Tendsto (Ve.flowLift κ b jumps E k u η ζ ω) atTop (𝓝 z) := by
  filter_upwards [ae_lift_invLe h13 hS3 HP, Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow]
    with ω hinv hreg hl hT hζ z hz
  obtain ⟨g, hgc, hg⟩ := hinv hl hT
  set t₀ : ℝ≥0 := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with ht₀
  have hlt : ∀ r : ℝ≥0, ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ ω := fun r => by rw [hζ]; exact ENNReal.coe_lt_top
  have hS : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hmem : ∀ r, Ve.flowLift κ b jumps E k u η ζ ω r ∈ {z : ℂ | 0 ≤ z.im} := fun r => (hg r (hlt r)).1
  have hzS : z ∈ {z : ℂ | 0 ≤ z.im} := hS.mem_of_tendsto hz (Eventually.of_forall hmem)
  have hz' : Tendsto (Ve.flowLift κ b jumps E k u η ζ ω) atTop (𝓝[{z : ℂ | 0 ≤ z.im}] z) :=
    tendsto_nhdsWithin_iff.2 ⟨hz, Eventually.of_forall hmem⟩
  -- the flow converges, against transience
  have hη : Tendsto (fun r : ℝ≥0 => η ω (t₀ + r)) atTop (𝓝 (g z + u)) := by
    have := ((hgc z hzS).tendsto.comp hz').add_const (u : ℂ)
    refine this.congr fun r => ?_
    simp only [Function.comp_apply, (hg r (hlt r)).2, sub_add_cancel]
  have htr : Tendsto (fun r : ℝ≥0 => ‖η ω (t₀ + r)‖) atTop atTop :=
    (hreg.2.2.2.2 hζ).comp (tendsto_atTop_mono (fun r => le_add_self) tendsto_id)
  exact not_tendsto_atTop_of_tendsto_nhds (hη.norm) htr

/-- **A finite limit of the family's capacity trace at a finite lifetime forces `ζ < ∞`.** -/
theorem ae_ne_top_of_capTrace_tendstoLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)]
    {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      IsDrivenCurve (ρ ω) → capLife (ρ ω) ≠ ⊤ → ∀ z : ℂ,
        Tendsto (capTrace (ρ ω)) (𝓝[<] (capLife (ρ ω)).toNNReal) (𝓝 z) → ζ ω ≠ ⊤ := by
  filter_upwards [hρ, ae_not_tendsto_lift_of_topLe h13 hS3 HP] with ω hρω hnt hl hT hd hV z hz hζ
  have h1 := (hρω hl hT).1 hζ
  have hc := tendsto_capClock_nhdsLT hd (ENNReal.coe_toNNReal hV).symm
  refine hnt hl hT hζ z ((hz.comp hc).congr fun r => ?_)
  show ρ ω (capInv (ρ ω) ((capClock (ρ ω) r).toNNReal : ℝ)) = _
  rw [Real.coe_toNNReal _ (hd.capClock_nonneg r.coe_nonneg), hd.capInv_eq r.coe_nonneg,
    h1 (show (r : ℝ) ∈ Ici 0 from r.coe_nonneg)]
  show Ve.flowLift κ b jumps E k u η ζ ω (r : ℝ).toNNReal = _
  rw [Real.toNNReal_coe]

end

end InteractingSLE.Theorem14.SB.Vn
