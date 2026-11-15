/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MfSets
import InteractingSLE.Spec.Supplement.WalkSideGeom
import InteractingSLE.Spec.Sec5.Aux61RestartComponent
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# SB2(2)'s stage sets have unbounded lower-union components (almost surely)

Packet PROVE-SB2-LCMEAN, round 4. Round 3's `Mf.sb2Lower_chartTransport_eq_couplingMean` still asked, as hypotheses,
that every component of `lowerUnion S` be unbounded for the two stage sets `S = A ∪ B_{<ℓ}` and `S = B_{≤ℓ,τ}`. They
hold almost surely:

* **`ae_not_isBounded_lowerUnion_stageSet`**: for any staged history with everywhere regular drivers, almost surely,
  at every stage, every lower-union component of the explored set is unbounded (piece regularity of every launched
  piece from Theorem 1.3, `Exist.StagedLaw.ae_pieceRegular_of_regular`; then
  `WalkSide.not_isBounded_lowerUnion_stageSet`);
* **`sb2Lower_chartTransport_eq_couplingMean_unb`**: SB2(2)'s union mean in K2's `hmean` form for the actual retained
  and explored sets with no set-level hypothesis left: only the stage-chart geometry, the mirrored configuration, the
  composite relative chart and the individual-mean formulas remain.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Mg

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Explored sets of a regular staged history have unbounded lower-union components**, almost surely at every
stage. -/
theorem ae_not_isBounded_lowerUnion_stageSet (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ k ω, IsRegularDriver (E k ω)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ z ∈ lowerUnion (WalkLaw.stageSet κ b jumps spec E n ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (WalkLaw.stageSet κ b jumps spec E n ω)) z) := by
  have hall := ae_all_iff.2 fun k => ae_pieceRegular_of_regular h13 hκ hb hS hreg k
  filter_upwards [hall] with ω hω n
  exact not_isBounded_lowerUnion_stageSet spec E ω (fun k c θ hl => hω k c θ hl) n

/-- **SB2(2)'s union mean at a lower line, in K2's `hmean` form, with no set-level hypothesis**: round 3's
`Mf.sb2Lower_chartTransport_eq_couplingMean` with the unbounded lower-union components of the two stage sets
discharged (`ae_not_isBounded_lowerUnion_stageSet`). The remaining hypotheses are the stage-chart geometry
(`Ln.IsStagePullback`), the mirrored configuration, the individual-mean formulas and the composite relative chart. -/
theorem sb2Lower_chartTransport_eq_couplingMean_unb (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ) {θ : ℝ}
    {t : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t))) (τ : ℝ≥0∞)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A₁ A₂ : Ω → Set ℂ,
      (∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
        A₂ ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ω) ∧
      ∀ {g : Ω → DistOn upperHalfPlaneOpens},
        IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P g →
        ∀ {c : Ω → Chart} {gb : Ω → ℂ → ℂ} {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ}
          {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ} {tt ur : Ω → ℝ} {lam : ℝ} {β₀ βE βu : Ω → ℝ → ℝ}
          {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ} {D : Set Ω},
        (∀ᵐ ω ∂P, ω ∈ D → Ln.IsStagePullback (c ω) (gb ω) (A₁ ω) (A₂ ω) (A ω) (fwdHull (w ω) (tt ω))) →
        (∀ᵐ ω ∂P, ω ∈ D → Lm.IsRelConfigJKL (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω)
          (tt ω) (ur ω) (chiC κ) lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω)) →
        (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₁ (centredField h u₀) P g₁ →
          ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => G₀ ω (Ψ ω ((c ω).1 z)) - chiC κ * ((LΨ ω ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₁ ω)) →
        (∀ g₂ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g₂ →
          ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
            EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (tt ω) ((c ω).1 z)) -
              chiC κ * ((logDerivFwd (w ω) (tt ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ ω)) →
        ∀ {crel : Ω → Chart} (hcr : ∀ ω, (crel ω).IsConformal), (∀ ω, ContinuousOn (crel ω).2.2 (crel ω).dom) →
        (∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (crel ω).2.1 y = (c ω).2.1 (Ψi ω y)) → ∀ {ℓ₀ : ℝ},
        (∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (crel ω).2.2 ((crel ω).2.1 y) =
          (LΨ ω (Ψi ω y)).im + (c ω).2.2 ((crel ω).2.1 y) + ℓ₀) →
        ∀ a : ℝ, ∀ᵐ ω ∂P, ω ∈ D → ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wr ω) (ur ω)) →
          Chart.chartTransport (hcr ω) 1 a (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
            ∫ y, couplingMean κ (Wr ω) (ur ω) (fun z => G ω z + (a + chiC κ * ℓ₀)) y * ψ y := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hcap := isStagedHistory_capSpec (τ := τ) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  have hU := ae_not_isBounded_lowerUnion_stageSet h13 hκ hb hup (hreg' _)
  have hC := ae_not_isBounded_lowerUnion_stageSet h13 hκ hb hcap (hreg' _)
  obtain ⟨A₁, A₂, hae, hmain⟩ :=
    sb2Lower_chartTransport_eq_couplingMean h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ τ hu₀
  refine ⟨A₁, A₂, hae, fun hg => hmain hg ?_ ?_⟩
  · filter_upwards [hU, hC] with ω h1 h2
    exact Sec5.Aux61Restart.not_isBounded_lowerUnion_union (h1 k) (h2 ℓ)
  · filter_upwards [hC] with ω h2
    exact h2 (ℓ + 1)

end InteractingSLE.Theorem14.SB.Mg
