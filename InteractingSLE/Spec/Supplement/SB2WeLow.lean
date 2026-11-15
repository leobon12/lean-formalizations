/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwFinal

/-!
# SB2(2)'s mirrored second clause: every left group of the relative lower walk has weight `> −2`

Packet PROVE-T14-SB2WORD (round 2, ruling R120, D10: "LCMEAN's (I4) uses the mirrored clause"). In SB2(2) the
relative curve is the lower walk (angle `φ = −π/2`) launched at the right entry of the upper history `A`; its left
side carries `A`'s old sides and the bridge. The source (p. 632): "If the erased upper history has an old right side
of angle `ψ_j`, its height is `λ − ψ_jχ` [...] All these old groups are admissible"; in weights (LCMEAN's (I4), (T-a)):
old right sides `−2 + (ψ_j − φ)χ/λ`, old left sides `(ψ_j − φ)χ/λ > 0`, low heights `≥ 0`, bridge groups admissible.
The original-real right ray keeps its weights through LIFTSET's boundary correspondence `RayCorr` (the bundle's).

* `cumWeightLeft_side_gt`, `cumWeightLeft_low_gt`: the weight computations;
* `SB2LowerLeftWeightStatement` and **`sb2LowerLeftWeightStatement_of_adm`**: from SB2(2)'s landed word half
  (`Lz.SB2LowerWordAdmStatement`, PROVE-T14-SB2LOW), every left height of the relative lower walk has cumulative weight
  `> −2`; **`sb2LowerLeftWeightStatement_of_theorem13`** (R48: Theorem 1.3 as a hypothesis, Theorem 1.4 only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lz

open Lx Lu Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw

/-- **Old upper sides have left weight `> −2` for the lower flow** (angles `ψ > −π/2`, `0 < κ < 4`). -/
theorem cumWeightLeft_side_gt {κ ψ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hψ : -(Real.pi / 2) < ψ) :
    -2 < cumWeightLeft κ (sleLambda κ - ψ * chiC κ + -(Real.pi / 2) * chiC κ) ∧
      -2 < cumWeightLeft κ (-sleLambda κ - ψ * chiC κ + -(Real.pi / 2) * chiC κ) := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  have hpos : 0 < (ψ + Real.pi / 2) * chiC κ := mul_pos (by linarith) hχ
  unfold cumWeightLeft
  constructor
  · have e : -(sleLambda κ - ψ * chiC κ + -(Real.pi / 2) * chiC κ) / sleLambda κ - 1 =
        -2 + (ψ + Real.pi / 2) * chiC κ / sleLambda κ := by field_simp; ring
    rw [e]
    have := div_pos hpos hl
    linarith
  · have e : -(-sleLambda κ - ψ * chiC κ + -(Real.pi / 2) * chiC κ) / sleLambda κ - 1 =
        (ψ + Real.pi / 2) * chiC κ / sleLambda κ := by field_simp; ring
    rw [e]
    have := div_pos hpos hl
    linarith

/-- **Low heights have left weight `≥ 0 > −2`** for the lower flow. -/
theorem cumWeightLeft_low_gt {κ y : ℝ} (hκ : 0 < κ) (hy : y ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ) :
    -2 < cumWeightLeft κ (y + -(Real.pi / 2) * chiC κ) := by
  have hl := sleLambda_pos hκ
  unfold cumWeightLeft
  have h1 : y + -(Real.pi / 2) * chiC κ ≤ -sleLambda κ := by linarith
  have h2 : 1 ≤ -(y + -(Real.pi / 2) * chiC κ) / sleLambda κ := by
    rw [le_div_iff₀ hl]; linarith
  linarith

/-- **SB2(2)'s mirrored second clause**: in SB2(2)'s setting, at almost every launch of the upper schedule and for
every witness of the launch clause, every left height of the relative lower walk (data `affData 1 m b'`, seed `0`,
`m = −e_R`) has cumulative weight `> −2`. -/
def SB2LowerLeftWeightStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' jumps' →
          ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
            ∀ y, y < 0 → y ∉ affJumps 1 m jumps' →
              -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ)

/-- **SB2(2)'s mirrored second clause from its word half** (`Lz.SB2LowerWordAdmStatement`). -/
theorem sb2LowerLeftWeightStatement_of_adm (h : SB2LowerWordAdmStatement.{u}) :
    SB2LowerLeftWeightStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hω
    c θ hcθ b' jumps' h'' hb' hT hG m hm y hy hyJ
  obtain ⟨hadm, hact⟩ := hω c θ hcθ b' jumps' h'' hb' hT hG m hm
  rcases le_or_gt y m with hym | hym
  · exact hadm y hym hyJ
  · rcases hact y ⟨hym, hy⟩ hyJ with ⟨p, hp, hside | hside⟩ | hlow | ⟨x, hx, hbx⟩
    · rw [hside]
      exact (cumWeightLeft_side_gt hκ hκ4 (hlθ p hp).1).1
    · rw [hside]
      exact (cumWeightLeft_side_gt hκ hκ4 (hlθ p hp).1).2
    · exact cumWeightLeft_low_gt hκ hlow
    · rw [← hbx]
      exact hL x hx.1 hx.2

/-- **SB2(2)'s mirrored second clause from Theorem 1.3** (at universe `0`). -/
theorem sb2LowerLeftWeightStatement_of_theorem13 (h13 : Exist.Theorem13Statement.{0}) :
    SB2LowerLeftWeightStatement.{u} :=
  sb2LowerLeftWeightStatement_of_adm (Lh.sb2LowerWordAdmStatement_of_theorem13 h13)

end InteractingSLE.Theorem14.SB.Lz
