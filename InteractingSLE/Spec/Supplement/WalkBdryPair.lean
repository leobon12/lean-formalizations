/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkBdryAssembly

/-!
# Theorem 1.4's walk pieces share no arc: the height argument

Packet PROVE-T14-WALKBDRY. Theorem GW4, proof (`source/spec/p625-671.md` L235, p. 637): "An interior common open subarc
is impossible: on the same incident side the two exact flow germs differ by `πχ`, whereas an inherited branch change
is an integer multiple of `2πχ`. Apply the marked collar comparison on a compact proper ordinary subarc."

**`walkPiecePairRegStatement_of_side`** proves the named input `WalkPiece.WalkPiecePairRegStatement` from

* the prefix side heights of both walks (`WalkPrefixSideStatement`);
* the local geometry of a common arc (`WalkPairGeomStatement`: a point `p` of both ranges near which both walks are one
  prefix arc, seen from the left of both prefixes, with a continuous transition between the two prefix charts whose
  lift difference tends to `2πn`);
* the walks' proper parametrizations and Theorems 1.2–1.3 (marked locality, for the comparison).

## The argument, at the configuration of `WalkPairGeomStatement`

Write `G_R = w_R + u₀ + χ lift'_R` and `G_L = w_L + u₀ + χ lift'_L`, read through the prefix charts. By the side
heights, `G_R → −λ + (π/2)χ` at `y_R` and `G_L → −λ − (π/2)χ` at `y_L`, hence also along the transition at `y_R`.
Near `p` the two walks are the same set, so by Proposition 3.8 for the two marked walks
(`ae_tendsto_sub_of_walkUnion`) `w_R − w_L → 0` at `p`. Therefore
`G_R − G_L ∘ T = (w_R − w_L) − χ (lift'_L − lift'_R)` tends both to `πχ` and to `−2πnχ`; since `χ > 0`, `1 + 2n = 0`,
impossible for an integer `n`.

R48: Theorems 1.2–1.3 are used as hypotheses; these results serve Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkBdry

open WalkLaw GW3Between LocalSets WalkMean

/-- **The integer contradiction**: the two side heights `−λ + (π/2)χ` and `−λ − (π/2)χ` differ by `πχ`, which is not an
integer multiple of `2πχ` when `χ > 0`. -/
theorem false_of_heights {κ χ : ℝ} (hχ : 0 < χ) {n : ℤ}
    (h : -sleLambda κ - -(Real.pi / 2) * χ - (-sleLambda κ - Real.pi / 2 * χ) = 0 - χ * (2 * Real.pi * n)) :
    False := by
  have hpi := Real.pi_pos
  have h1 : χ * Real.pi * (1 + 2 * (n : ℝ)) = 0 := by linear_combination h
  have h2 : (1 + 2 * (n : ℝ)) = 0 := by
    rcases mul_eq_zero.1 h1 with h3 | h3
    · exact absurd h3 (mul_pos hχ hpi).ne'
    · exact h3
  have h3 : (1 + 2 * n : ℤ) = 0 := by exact_mod_cast h2
  omega

/-- **`WalkPiece.WalkPiecePairRegStatement` from the prefix side heights and the local geometry of a common arc.** -/
theorem walkPiecePairRegStatement_of_side (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hSR : WalkPrefixSideStatement.{u} (-(Real.pi / 2)) true)
    (hSL : WalkPrefixSideStatement.{u} (Real.pi / 2) false) (hPG : WalkPairGeomStatement.{u}) :
    WalkPiece.WalkPiecePairRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  classical
  have hpi := Real.pi_pos
  have hχ : 0 < QuantumZipper.chiC κ := Sec4.chiC_pos hκ hκ4
  -- the regularized family
  obtain ⟨hE₁, hreg₁', hrun⟩ := StagedReg.regFam_spec hb hE hreg
  set E₁ := StagedReg.regFam E with hE₁def
  have hreg₁ : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E₁ spec) := fun spec hs => stagedPiecesRegular_regHist (hreg spec hs)
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  -- the centred field
  set u₀ := bddExt b jumps with hu₀def
  have hu₀ : IsBoundedHarmonicExtension b jumps u₀ := isBoundedHarmonicExtension_bddExt hb
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the two walks and their means
  obtain ⟨AR, -, hARae, hARp, hARm, hARloc⟩ := exists_walkVersion h12p h13 (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith⟩ true hκ hκ4 hb hh hE₁ hreg₁ hreg₁' hu₀
  obtain ⟨AL, -, hALae, hALp, hALm, hALloc⟩ := exists_walkVersion h12p h13 (θ := Real.pi / 2)
    ⟨by linarith, le_rfl⟩ false hκ hκ4 hb hh hE₁ hreg₁ hreg₁' hu₀
  obtain ⟨gR, hgR⟩ := IsLocalSet.exists_isLocalSetMean hh0 hARm hARloc
  obtain ⟨gL, hgL⟩ := IsLocalSet.exists_isLocalSetMean hh0 hALm hALloc
  have hARJ : MeasurableSpace.comap AR hittingSigma ≤ aeSigma (jointPast κ b jumps E₁) P :=
    hARp.comap_le.trans (le_sup_left.trans (le_aeSigma _ P))
  have hALJ : MeasurableSpace.comap AL hittingSigma ≤ aeSigma (jointPast κ b jumps E₁) P :=
    hALp.comap_le.trans (le_sup_right.trans (le_aeSigma _ P))
  have hU : ∀ᵐ ω ∂P, AR ω ∪ AL ω = walkUnionSet κ b jumps E₁ ω := by
    filter_upwards [hARae, hALae] with ω h1 h2
    rw [h1, h2, walkUnionSet]
  have hPRω := hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E₁ hE₁ hreg₁
  have hPLω := hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E₁ hE₁ hreg₁
  have hunbR : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (AR ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (AR ω)) z) := by
    filter_upwards [hPRω, hARae] with ω ⟨γ, hγ, _, hγr⟩ he
    rw [he]
    exact unbounded_lowerUnion_of_range hγ hγr.symm
  have hunbL : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (AL ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (AL ω)) z) := by
    filter_upwards [hPLω, hALae] with ω ⟨γ, hγ, _, hγr⟩ he
    rw [he]
    exact unbounded_lowerUnion_of_range hγ hγr.symm
  have hc := ae_tendsto_sub_of_walkUnion h12p h13 hκ hκ4 hb hh hE₁ hreg₁ hreg₁' hu₀ hARm hALm hARloc hALloc
    hARJ hALJ hU hunbR hunbL hgR hgL
  have hSRω := hSR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E₁ hE₁ hreg₁ hreg₁' u₀ hu₀ AR hARm hARae gR hgR
  have hSLω := hSL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E₁ hE₁ hreg₁ hreg₁' u₀ hu₀ AL hALm hALae gL hgL
  have hPGω := hPG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E₁ hE₁ hreg₁ hreg₁'
  filter_upwards [hPGω, hSRω, hSLω, hc, hgR.2.1, hgL.2.1, hARae, hALae, hrun _ hprR, hrun _ hprL]
    with ω hPGω hSRω hSLω hcω hgRω hgLω hARω hALω hrR hrL
  intro pR hpR pL hpL S hS hSc
  by_contra hns
  have hpR' : pR ∈ (walkRuns κ b jumps E₁ ω).1.1 := by
    simp only [walkRuns]; rw [hrR]; exact hpR
  have hpL' : pL ∈ (walkRuns κ b jumps E₁ ω).2.1 := by
    simp only [walkRuns]; rw [hrL]; exact hpL
  obtain ⟨preR, postR, preL, postL, pcR, pcL, τR, τL, yR, yL, p, r, n, hsR, hτR, hlR, hsL, hτL, hlL, hinvR, hinvL,
    hp, hr, hpreR, hpreL, heq, hevR, hT, hevT, hlift⟩ := hPGω pR hpR' pL hpL' S hS hSc hns
  obtain ⟨wR, hwR, hwRrep⟩ := hgRω
  obtain ⟨wL, hwL, hwLrep⟩ := hgLω
  have hRw : walkSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E₁ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ω = wsetOf (walkRuns κ b jumps E₁ ω).1 :=
    walkSet_eq_wsetOf _ _ _ _ _ ω
  have hLw : walkSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (E₁ (boundaryWalkSpec b jumps (Real.pi / 2) false)) ω = wsetOf (walkRuns κ b jumps E₁ ω).2 :=
    walkSet_eq_wsetOf _ _ _ _ _ ω
  have hARw : AR ω = wsetOf (walkRuns κ b jumps E₁ ω).1 := hARω.trans hRw
  have hALw : AL ω = wsetOf (walkRuns κ b jumps E₁ ω).2 := hALω.trans hLw
  -- the side heights
  have hGR := (hSRω wR hwR hwRrep preR postR pcR hsR τR hτR yR p hinvR
    (Or.inl (hpreR ⟨hp.1, mem_ball_self hr⟩)) ⟨r, hr, by rw [hRw]; exact hpreR⟩).1 hlR
  have hGL := (hSLω wL hwL hwLrep preL postL pcL hsL τL hτL yL p hinvL
    (Or.inl (hpreL ⟨hp.2, mem_ball_self hr⟩)) ⟨r, hr, by rw [hLw]; exact hpreL⟩).1 hlL
  have hTH : Tendsto (fun ζ => (prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ)) (𝓝[H] (yR : ℂ))
      (𝓝[H] (yL : ℂ)) := tendsto_nhdsWithin_iff.2 ⟨hT, hevT.mono fun ζ hζ => hζ.1⟩
  have hGLT := hGL.comp hTH
  -- the comparison of the two walks at `p`
  have hinvR' : Tendsto (prefixChart pcR τR).2.1 (𝓝[H] (yR : ℂ)) (𝓝[H \ (AR ω ∪ AL ω)] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hinvR, ?_⟩
    rw [hARw, hALw]
    exact hevR
  have hcmp := (hcω wR wL hwR hwRrep hwL hwLrep p (by rw [hARw]; exact Or.inl hp.1)
    (by rw [hALw]; exact Or.inl hp.2) ⟨r, hr, by rw [hARw, hALw, ← heq]; exact inter_subset_left⟩
    ⟨r, hr, by rw [hARw, hALw, heq]; exact inter_subset_left⟩).comp hinvR'
  have h1 := (hGR.sub hGLT)
  have h2 := hcmp.sub (hlift.const_mul (QuantumZipper.chiC κ))
  have hNe := Exist.StagedLaw.neBot_nhdsWithin_H_real yR
  refine false_of_heights hχ (tendsto_nhds_unique (h1.congr' ?_) h2)
  filter_upwards [hevT] with ζ hζ
  simp only [Function.comp_apply, hζ.2]
  ring

end InteractingSLE.Theorem14.WalkBdry
