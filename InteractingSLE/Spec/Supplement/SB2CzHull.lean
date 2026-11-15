/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CzConn
import InteractingSLE.Spec.Supplement.SB2NcK

/-!
# The retained hull of B's stage `ℓ`, exactly measurable for the retained past

Packet PROVE-SB2-CANON. `Mz.TailCanonAt` asks for the canonical hull `K` dyadic-hit measurable for the uncompleted
retained past `Ms.stageMarks ℓ` (the upper past through `k` and B's past before `ℓ`), compact at every sample, with
`K ∪ {Im ≤ 0}` preconnected at every sample. NOJUMP's `Nc.exists_retHull` gives such a `K` for the completed line
σ-algebra; its stage-set versions `Bu`, `Bl` (`Nc.exists_retVersion`) are already exactly measurable, only the mask is
completed. **`exists_exactRetHull`** masks `K₀ = fillVer (Bu ∪ Bl)` instead by the uncompleted event

`G₁ = {B launches at ℓ (regularized family)} ∩ {K₀ bounded, closure K₀ ∪ {Im ≤ 0} preconnected}`

(measurable by `measurableSet_bounded_conn`). Almost every launch of B's stage `ℓ` lies in `G₁` (`Nc.ae_retGeom`), and
almost surely on `G₁` the fill of `K` is the fill of the retained union `retX = A ∪ B_{<ℓ}`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The retained hull of B's stage `ℓ`, exactly measurable for the retained past.** -/
theorem exists_exactRetHull (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (K : Ω → Set ℂ) (G₁ : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (stageMarks κ b jumps E u l k ℓ) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ MeasurableSet[stageMarks κ b jumps E u l k ℓ] G₁ ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G₁) ∧
      ∀ᵐ ω ∂P, ω ∈ G₁ → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
        fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
  classical
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  set Ew := StagedReg.regFam E w with hEwdef
  obtain ⟨Bu, Bl, hBum, hBlm, hBuc, hBlc, -, -, -, hK₀c, hK₀ae⟩ :=
    Nc.exists_retVersion h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hu₀
  -- the filled version is measurable for the retained past
  have hUm : Measurable[stageMarks κ b jumps E u l k ℓ, hittingSigma] fun ω => Bu ω ∪ Bl ω :=
    @LocalSets.measurable_union_hitting Ω (stageMarks κ b jumps E u l k ℓ) Bu Bl (hBum.mono le_sup_left le_rfl)
      (hBlm.mono le_sup_right le_rfl)
  have hUH : ∀ ω, Bu ω ∪ Bl ω ⊆ H := fun ω => union_subset (hBuc ω).1 (hBlc ω).1
  set K₀ : Ω → Set ℂ := fillVer fun ω => Bu ω ∪ Bl ω with hK₀def
  have hK₀m : Measurable[stageMarks κ b jumps E u l k ℓ, hittingSigma] K₀ := measurable_fillVer hUH hUm
  -- the launch event (regularized family) and the connected-bounded event
  set L₀ : Set Ω := {ω | (ExplState.run κ b jumps w (fun j => Ew j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} with hL₀def
  have hL₀ : MeasurableSet[stageMarks κ b jumps E u l k ℓ] L₀ :=
    le_sup_right (b := pastSigma κ b jumps w Ew ℓ) _
      (Lv.measurableSet_launch_pastSigma (κ := κ) (spec := w) hb (hE' w hw).1 (hreg' w) ℓ)
  set C : Set Ω := {ω | Bornology.IsBounded (K₀ ω) ∧ IsPreconnected (closure (K₀ ω) ∪ Restart.lowerHalf)}
    with hCdef
  have hC : MeasurableSet[stageMarks κ b jumps E u l k ℓ] C :=
    measurableSet_bounded_conn (fun ω => (hK₀c ω).1) hK₀m
  set G₁ : Set Ω := L₀ ∩ C with hG₁def
  have hG₁ : MeasurableSet[stageMarks κ b jumps E u l k ℓ] G₁ := hL₀.inter hC
  set K : Ω → Set ℂ := Mo.retHull K₀ G₁ with hKdef
  have hKm : @Restart.IsDyadicHitMeasurable Ω (stageMarks κ b jumps E u l k ℓ) K :=
    @Mo.isDyadicHitMeasurable_retHull Ω K₀ G₁ (stageMarks κ b jumps E u l k ℓ) hK₀m (fun ω => (hK₀c ω).1) hG₁
  have hKc : ∀ ω, IsCompact (K ω) := Mo.isCompact_retHull fun ω hω => hω.2.1
  have hXc : ∀ ω ∈ G₁, K₀ ω = closure (K₀ ω) ∩ H ∧ IsClosed (closure (K₀ ω)) ∧
      (∀ z ∈ closure (K₀ ω), 0 ≤ z.im) ∧ IsPreconnected (closure (K₀ ω) ∪ Restart.lowerHalf) := by
    intro ω hω
    refine ⟨(Sec7.SideHeight.closure_inter_H_eq (hK₀c ω).1 (hK₀c ω).2).symm, isClosed_closure, ?_, hω.2.2⟩
    have hcl : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    intro z hz
    exact (hcl.closure_subset_iff.2 fun v hv => show 0 ≤ v.im from le_of_lt ((hK₀c ω).1 hv)) hz
  have hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf) := Mo.isPreconnected_retHull_union hXc
  have hgeo := Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ
  -- almost surely: regularized runs are the raw runs, and the filled version is the stage fill
  have hgood : ∀ᵐ ω ∂P, (∀ n, ExplState.run κ b jumps w (fun j => Ew j ω) n =
      ExplState.run κ b jumps w (fun j => E w j ω) n) ∧
      ((ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        K₀ ω = fillH (Nc.retX κ b jumps E u l k ℓ ω) ∧ IsHPHull (fillH (Nc.retX κ b jumps E u l k ℓ ω))) := by
    filter_upwards [hrun w hw, hK₀ae, hgeo] with ω h1 h2 h3
    refine ⟨h1, fun hl => ?_⟩
    obtain ⟨-, -, -, hhull, hfill⟩ := h3 hl
    exact ⟨h2.trans hfill, hhull⟩
  refine ⟨K, G₁, hKm, hKc, hKp, hG₁, ?_, ?_⟩
  · filter_upwards [hgood] with ω hg hl
    obtain ⟨hK₀e, hhull⟩ := hg.2 hl
    refine ⟨?_, ?_, ?_⟩
    · show (ExplState.run κ b jumps w (fun j => Ew j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
      rw [hg.1 (ℓ + 1)]; exact hl
    · rw [hK₀e]; exact hhull.2.1
    · rw [hK₀e]; exact Sec5.Aux61Restart.isPreconnected_closure_union_lowerHalf hhull
  · filter_upwards [hgood] with ω hg hω
    have hl : (ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [← hg.1 (ℓ + 1)]; exact hω.1
    obtain ⟨hK₀e, hhull⟩ := hg.2 hl
    refine ⟨hl, ?_⟩
    have hHP : IsHPHull (K₀ ω) := by rw [hK₀e]; exact hhull
    rw [hKdef, Mo.fillH_retHull_of_mem (X := fun ω => closure (K₀ ω)) hω (hXc ω hω).1,
      Sec5.Aux61Restart.fillH_closure_of_isHPHull hHP, hK₀e]

end InteractingSLE.Theorem14.SB.Cz
