/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SB2VdAe
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe

/-!
# Successor of `SB2VdDrvAe` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VdDrvAe` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_lift_regularLe`;
* `ae_isDrivenCurve_liftLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vd

open Lv Vc Exist.Staged Exist.StagedLaw Sec7.PocketTraversal

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The flow's lift starts at `0` and is continuous before the remaining lifetime**, almost surely. -/
theorem ae_lift_regularLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) 0 = 0 ∧
      ∀ s : ℝ≥0, (((firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal + s : ℝ≥0) :
        ℝ≥0∞) < ζ ω → ContinuousAt (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) s := by
  filter_upwards [ae_lineGeom_liftOfLe h13 hS3 HP] with ω hrec hF hT
  set TL := firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) with hTL
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  -- a record whose horizon exceeds `s`, with its lift equal to `liftOf` below it
  have key : ∀ s : ℝ≥0, ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω → ∃ γ : ℝ≥0 → ℂ, Continuous γ ∧ γ 0 = 0 ∧
      ∃ S₁ : ℝ, (s : ℝ) < S₁ ∧ ∀ s' : ℝ≥0, (s' : ℝ) < S₁ →
        γ s' = (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) s' := by
    intro s hs
    obtain ⟨T, hsT, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    have hsT' : (TL.toNNReal : ℝ) + s < T := by
      have := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hsT); rwa [NNReal.coe_add] at this
    have hvis : TL < T := by
      rw [← hTLc]; refine ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ?_); linarith [s.2]
    set S₁ : ℝ := ((s : ℝ) + ((T : ℝ) - TL.toNNReal)) / 2 with hS₁
    have hS₁pos : 0 < S₁ := by rw [hS₁]; linarith [s.2]
    have hS₁T : TL.toReal + S₁ < T := by rw [hTLr, hS₁]; linarith
    obtain ⟨p, g, β', γ, tL, Wr, ηr, -, -, hw, -, -, hγeq⟩ := hrec hF T hTζ.le hvis S₁ hS₁pos hS₁T
    obtain ⟨-, -, -, -, htL, hγ, hγ0, -⟩ := hw
    have htt : tL = TL.toNNReal := by rw [← ENNReal.coe_inj, hTLc]; exact htL
    subst htt
    exact ⟨γ, hγ.1, hγ0, S₁, by rw [hS₁]; linarith, hγeq⟩
  have hcont : ∀ s : ℝ≥0, ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ContinuousAt (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) s := by
    intro s hs
    obtain ⟨γ, hγc, -, S₁, hsS, hγeq⟩ := key s hs
    have hsS' : s < S₁.toNNReal := Real.lt_toNNReal_iff_coe_lt.2 hsS
    have hev : (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) =ᶠ[𝓝 s] γ := by
      filter_upwards [Iio_mem_nhds hsS'] with s' hs'
      exact (hγeq s' (Real.lt_toNNReal_iff_coe_lt.1 hs')).symm
    exact hγc.continuousAt.congr hev.symm
  refine ⟨?_, hcont⟩
  have h0 : ((TL.toNNReal + 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [add_zero, hTLc]; exact hT
  obtain ⟨γ, -, hγ0, S₁, hsS, hγeq⟩ := key 0 h0
  rw [← hγeq 0 hsS, hγ0]

/-- **The flow's lift (reparametrized when the remaining life is finite) is a driven curve**, almost surely. -/
theorem ae_isDrivenCurve_liftLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      (ζ ω = ⊤ → IsDrivenCurve (liftR (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)))) ∧
      (ζ ω ≠ ⊤ → IsDrivenCurve (relCurve (liftR (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)))
        ((ζ ω).toReal - (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toReal))) := by
  filter_upwards [ae_lift_regularLe h13 hS3 HP, ae_chain_liftOfLe h13 hS3 HP] with ω hreg hch hF hT
  obtain ⟨h0, hcont⟩ := hreg hF hT
  set TL := firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) with hTL
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  -- the chain at `S₀ > 0` from the horizon `T_L + S₀`
  have hchainAt : ∀ S₀ : ℝ, 0 < S₀ → ((TL.toNNReal + S₀.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ∃ (A : Set ℂ) (c : Chart) (β' : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        FinRel.IsSB2RelChain A c β' (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) tL S₀ Wr ηr := by
    intro S₀ hS₀ hlt
    obtain ⟨Wr, ηr, β', hc⟩ := hch hF hT (TL.toNNReal + S₀.toNNReal) le_self_add hlt
    have e : ((TL.toNNReal + S₀.toNNReal : ℝ≥0) : ℝ) - TL.toReal = S₀ := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ hS₀.le, hTLr]; ring
    rw [e] at hc
    exact ⟨_, _, β', _, Wr, ηr, hc⟩
  refine ⟨fun hζ => ?_, fun hζ => ?_⟩
  · refine isDrivenCurve_liftR (continuous_iff_continuousAt.2 fun s => hcont s (by rw [hζ]; exact
      ENNReal.coe_lt_top)) h0 fun S₀ hS₀ => hchainAt S₀ hS₀ (by rw [hζ]; exact ENNReal.coe_lt_top)
  · have hζr : ((ζ ω).toNNReal : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
    have hlt : TL.toNNReal < (ζ ω).toNNReal := by
      rw [← ENNReal.coe_lt_coe, hζr, ENNReal.coe_toNNReal hTLtop]; exact hT
    have hltr : (TL.toNNReal : ℝ) < (ζ ω).toNNReal := NNReal.coe_lt_coe.2 hlt
    have hconv : ∀ x : ℝ≥0, ((TL.toNNReal : ℝ) + x < (ζ ω).toReal) →
        ((TL.toNNReal + x : ℝ≥0) : ℝ≥0∞) < ζ ω := fun x hx => by
      rw [← hζr]; refine ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ?_)
      rw [NNReal.coe_add]; exact hx
    refine isDrivenCurve_relCurve_liftR (by rw [hTLr]; exact sub_pos.2 hltr) (fun s hs => hcont s (hconv s (by
      rw [hTLr] at hs; linarith))) h0 fun S₀ hS₀ hS₀ℓ => hchainAt S₀ hS₀ (hconv _ (by
      rw [Real.coe_toNNReal _ hS₀.le]; rw [hTLr] at hS₀ℓ; linarith))

end

end InteractingSLE.Theorem14.SB.Vd
