/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkBdryCompare

/-!
# Theorem 1.4's union mean: the chart boundary values from the walks' prefix heights

Packet PROVE-T14-WALKBDRY. **`walkUnionBdryStatement_of_side`** proves PROVE-T14-WALKMEAN's named input
`WalkMean.WalkUnionBdryStatement` from

* the side heights of each walk's own mean in its prefix charts (`WalkPrefixSideStatement`, for `R` at `−π/2` and
  `L` at `π/2`);
* the normalized component charts (`WalkNormChartStatement`, pathwise conformal geometry);
* the walks' proper parametrizations (`WalkCont.RightWalkProperRegStatement`,
  `GW3SidedProof.LeftWalkProperRegStatement`, in the wiring) and Theorems 1.2–1.3 (marked locality).

The selector `normSel` chooses a normalized chart of each component; it is a function of the two final runs and the
component only. At a real point matched with a prefix side point of `R`, the union mean read in the component chart is
(Lemma GW3, proof, p. 636)

`v + u₀ + χ lift_C = (v − w_R) + (w_R + u₀ + χ lift') ∘ c'.inv ∘ T − χ (lift' − lift_C)`,

`T = c'.fwd ∘ c.inv`: the first term tends to `0` by the marked union comparison (Proposition 3.8, near the landing
point the union is `R`), the second to `−λ + (π/2)χ = −Λ` (`WalkPrefixSideStatement`), the third to `0` (the
normalization). At a matched original real point the union mean tends to `0`
(`Sec7.IsLocalSetMean.ae_tendsto_zero_of_real`), `u₀` to `b`, the lift to `0`.

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

/-! ### The two matches, pointwise -/

section Pointwise

/-- **A prefix match transfers the prefix side height to the component chart.** -/
theorem tendsto_of_pieceMatch {s s' : ExplState} {left : Bool} {c : Chart} {x : ℝ} {v w u₀ : ℂ → ℝ}
    {χ hgt : ℝ} {AW AU : Set ℂ} (hm : IsPieceMatch s s' left c x)
    (hcH : ∀ z ∈ H, c.2.1 z ∈ H \ (AW ∪ AU))
    (hS : ∀ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0), s.1 = pre ++ pc :: post →
      (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 → ∀ (y : ℝ) (p : ℂ),
      Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) → p ∈ prefixSet pre pc τ ∪ {z : ℂ | z.im = 0} →
      (∃ r > 0, wsetOf s ∩ ball p r ⊆ prefixSet pre pc τ) →
      (if left then IsLeftSidePt pc τ y else IsRightSidePt pc τ y) →
      Tendsto (fun ζ => w ((prefixChart pc τ).2.1 ζ) + u₀ ((prefixChart pc τ).2.1 ζ) +
        χ * (prefixChart pc τ).2.2 ((prefixChart pc τ).2.1 ζ)) (𝓝[H] (y : ℂ)) (𝓝 hgt))
    (hcmp : ∀ p : ℂ, p ∈ wsetOf s ∪ {z : ℂ | z.im = 0} → (∃ r > 0, wsetOf s' ∩ ball p r ⊆ wsetOf s) →
      Tendsto (fun z => w z - v z) (𝓝[H \ (AW ∪ AU)] p) (𝓝 0)) :
    Tendsto (fun z => v (c.2.1 z) + u₀ (c.2.1 z) + χ * c.2.2 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 hgt) := by
  obtain ⟨pre, post, pc, τ, y, p, r, hs, hτ, hside, hinv, hp, hr, hpre, hs', hT, hev, hlift⟩ := hm
  have hTH : Tendsto (fun z => (prefixChart pc τ).1 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝[H] (y : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hT, hev.mono fun z hz => hz.1⟩
  have hpP : p ∈ prefixSet pre pc τ ∪ {z : ℂ | z.im = 0} := by
    rcases hp with hp | hp
    · exact Or.inl (hpre ⟨hp, mem_ball_self hr⟩)
    · exact Or.inr hp
  have h1 := (hS pre post pc τ hs hτ y p hinv hpP ⟨r, hr, hpre⟩ hside).comp hTH
  have hinvx : Tendsto (fun z => c.2.1 z) (𝓝[H] (x : ℂ)) (𝓝 p) :=
    (hinv.comp hTH).congr' (hev.mono fun z hz => hz.2)
  have hinvx' : Tendsto (fun z => c.2.1 z) (𝓝[H] (x : ℂ)) (𝓝[H \ (AW ∪ AU)] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hinvx, eventually_nhdsWithin_of_forall fun z hz => hcH z hz⟩
  have h2 := (hcmp p hp ⟨r, hr, hs'⟩).comp hinvx'
  have h3 := hlift.const_mul χ
  have h := (h1.sub h2).sub h3
  rw [mul_zero, sub_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hev] with z hz
  simp only [Function.comp_apply, hz.2]
  ring

/-- **A real match gives the original boundary value.** -/
theorem tendsto_of_realMatch {sR sL : ExplState} {b : ℝ → ℝ} {jumps : Finset ℝ} {c : Chart} {x bx : ℝ}
    {v u₀ : ℂ → ℝ} {χ : ℝ} {AU : Set ℂ} (hm : IsRealMatch sR sL b jumps c x bx)
    (hcH : ∀ z ∈ H, c.2.1 z ∈ H \ AU) (hAU : AU ⊆ wsetOf sR ∪ wsetOf sL)
    (hreal : ∀ a : ℝ, (∃ r > 0, Disjoint (ball (a : ℂ) r) AU) → Tendsto v (𝓝[H \ AU] (a : ℂ)) (𝓝 0))
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    Tendsto (fun z => v (c.2.1 z) + u₀ (c.2.1 z) + χ * c.2.2 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 bx) := by
  obtain ⟨a, r, ha, hr, hinv, hdis, hlift, hbx⟩ := hm
  have hinv' : Tendsto (fun z => c.2.1 z) (𝓝[H] (x : ℂ)) (𝓝[H \ AU] (a : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hinv, eventually_nhdsWithin_of_forall fun z hz => hcH z hz⟩
  have h1 := (hreal a ⟨r, hr, hdis.mono_right hAU⟩).comp hinv'
  have h2 := (hu₀.2.2 a ha).comp (hinv'.mono_right (nhdsWithin_mono _ sdiff_subset))
  have h3 := hlift.const_mul χ
  have h := (h1.add h2).add h3
  rw [mul_zero, add_zero, zero_add, ← hbx] at h
  exact h

end Pointwise

/-! ### The selector -/

/-- The run-determined selector: a normalized chart of the component, if there is one. -/
def normSel (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (r : ExplState × ExplState) (C : Set ℂ) :
    Chart × (ℝ → ℝ) × Finset ℝ := by
  classical
  exact if hx : ∃ t, IsNormChart κ b jumps r C t then hx.choose else (Chart.id, fun _ => 0, ∅)

theorem isNormChart_normSel {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {r : ExplState × ExplState} {C : Set ℂ}
    (hx : ∃ t, IsNormChart κ b jumps r C t) : IsNormChart κ b jumps r C (normSel κ b jumps r C) := by
  classical
  unfold normSel
  rw [dite_eq_left hx]
  exact hx.choose_spec

/-! ### The assembly -/

/-- **`WalkMean.WalkUnionBdryStatement` from the prefix side heights of both walks and the normalized charts.** -/
theorem walkUnionBdryStatement_of_side (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hSR : WalkPrefixSideStatement.{u} (-(Real.pi / 2)) true)
    (hSL : WalkPrefixSideStatement.{u} (Real.pi / 2) false) (hN : WalkNormChartStatement.{u}) :
    WalkMean.WalkUnionBdryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hreg hreg' u₀ hu₀ A' hA'm hA'ae g hg
  classical
  have hpi := Real.pi_pos
  refine ⟨normSel κ b jumps, ?_⟩
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  -- the two walks
  obtain ⟨AR, -, hARae, hARp, hARm, hARloc⟩ := exists_walkVersion h12p h13 (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith⟩ true hκ hκ4 hb hh hE hreg hreg' hu₀
  obtain ⟨AL, -, hALae, hALp, hALm, hALloc⟩ := exists_walkVersion h12p h13 (θ := Real.pi / 2)
    ⟨by linarith, le_rfl⟩ false hκ hκ4 hb hh hE hreg hreg' hu₀
  obtain ⟨gR, hgR⟩ := IsLocalSet.exists_isLocalSetMean hh0 hARm hARloc
  obtain ⟨gL, hgL⟩ := IsLocalSet.exists_isLocalSetMean hh0 hALm hALloc
  -- the union
  have hdet := pastDetRegStatement_of_thm12_thm13 h12p h13
  have hRl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith⟩ true
  have hLl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := Real.pi / 2)
    ⟨by linarith, le_rfl⟩ false
  obtain ⟨hUev, hUo, -, hlocU⟩ := walkUnion_markedAE hdet hRl hLl hκ hκ4 hb hh hE hreg hreg' hu₀
  have hA'c : ∀ᵐ ω ∂P, A' ω ⊆ H ∧ IsOpen (H \ A' ω) := by
    filter_upwards [hA'ae, hUo] with ω h1 h2
    rw [h1]
    exact ⟨union_subset (walkSet_subset_H _ _ _ _ _ _) (walkSet_subset_H _ _ _ _ _ _), h2⟩
  have hA'loc : IsLocalSet A' (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hA'm hA'c).out 1 4).1
      (isHistoryAvoidanceLocal_congr_ae (hA'ae.mono fun ω h => h.symm) hlocU).isAvoidanceLocal
  have hA'J : MeasurableSpace.comap A' hittingSigma ≤ aeSigma (jointPast κ b jumps E) P :=
    hitting_comap_le_aeSigma (avoid_aeSigma_congr hA'ae hUev)
  have hARJ : MeasurableSpace.comap AR hittingSigma ≤ aeSigma (jointPast κ b jumps E) P :=
    hARp.comap_le.trans (le_sup_left.trans (le_aeSigma _ P))
  have hALJ : MeasurableSpace.comap AL hittingSigma ≤ aeSigma (jointPast κ b jumps E) P :=
    hALp.comap_le.trans (le_sup_right.trans (le_aeSigma _ P))
  -- unbounded lower unions
  have hPRω := hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  have hPLω := hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
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
  have hunbU : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A' ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A' ω)) z) := by
    filter_upwards [hPRω, hPLω, hA'ae] with ω ⟨γ₁, hγ₁, h₁₀, hγ₁r⟩ ⟨γ₂, hγ₂, h₂₀, hγ₂r⟩ he
    rw [he]
    exact unbounded_lowerUnion_of_range₂ hγ₁ hγ₂ h₁₀ h₂₀ hγ₁r.symm hγ₂r.symm
  -- the comparisons with the union
  have hURae : ∀ᵐ ω ∂P, AR ω ∪ A' ω = walkUnionSet κ b jumps E ω := by
    filter_upwards [hARae, hA'ae] with ω h1 h2
    rw [h1, h2, walkUnionSet]
    exact union_eq_right.2 subset_union_left
  have hULae : ∀ᵐ ω ∂P, AL ω ∪ A' ω = walkUnionSet κ b jumps E ω := by
    filter_upwards [hALae, hA'ae] with ω h1 h2
    rw [h1, h2, walkUnionSet]
    exact union_eq_right.2 subset_union_right
  have hcR := ae_tendsto_sub_of_walkUnion h12p h13 hκ hκ4 hb hh hE hreg hreg' hu₀ hARm hA'm hARloc hA'loc
    hARJ hA'J hURae hunbR hunbU hgR hg
  have hcL := ae_tendsto_sub_of_walkUnion h12p h13 hκ hκ4 hb hh hE hreg hreg' hu₀ hALm hA'm hALloc hA'loc
    hALJ hA'J hULae hunbL hunbU hgL hg
  have hreal := Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hA'm hA'loc hg
  have hSRω := hSR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hreg' u₀ hu₀ AR hARm hARae gR hgR
  have hSLω := hSL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hreg' u₀ hu₀ AL hALm hALae gL hgL
  have hNω := hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hreg'
  filter_upwards [hNω, hSRω, hSLω, hcR, hcL, hreal, hgR.2.1, hgL.2.1, hARae, hALae, hA'ae]
    with ω hNω hSRω hSLω hcRω hcLω hrealω hgRω hgLω hARω hALω hA'ω
  intro C hC
  have hsel := isNormChart_normSel (hNω C hC)
  set t := normSel κ b jumps (walkRuns κ b jumps E ω) C with ht
  obtain ⟨hc, hpc, hcbd, Eℝ, hEf, hmatch⟩ := hsel
  refine ⟨hc, hpc, hcbd, fun v hv hvrep => ?_⟩
  obtain ⟨wR, hwR, hwRrep⟩ := hgRω
  obtain ⟨wL, hwL, hwLrep⟩ := hgLω
  -- the sets at `ω`
  have hRw : walkSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ω = wsetOf (walkRuns κ b jumps E ω).1 :=
    walkSet_eq_wsetOf _ _ _ _ _ ω
  have hLw : walkSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (E (boundaryWalkSpec b jumps (Real.pi / 2) false)) ω = wsetOf (walkRuns κ b jumps E ω).2 :=
    walkSet_eq_wsetOf _ _ _ _ _ ω
  have hA'w : A' ω = wsetOf (walkRuns κ b jumps E ω).1 ∪ wsetOf (walkRuns κ b jumps E ω).2 := by
    rw [hA'ω, walkUnionSet, hRw, hLw]
  have hARw : AR ω = wsetOf (walkRuns κ b jumps E ω).1 := hARω.trans hRw
  have hALw : AL ω = wsetOf (walkRuns κ b jumps E ω).2 := hALω.trans hLw
  -- the chart's inverse avoids both ranges
  have hCsub : C ⊆ H \ (wsetOf (walkRuns κ b jumps E ω).1 ∪ wsetOf (walkRuns κ b jumps E ω).2) := by
    obtain ⟨z, -, -, -, rfl⟩ := hC
    intro w hw
    have hw' := connectedComponentIn_subset _ _ hw
    refine ⟨hw'.1, fun hwU => hw'.2 ?_⟩
    rcases hwU with hw1 | hw2
    · exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.2 (mem_iUnion₂.1 hw1.1))))
    · exact Or.inr (Or.inl (Or.inr (mem_iUnion₂.2 (mem_iUnion₂.1 hw2.1))))
  have hcHR : ∀ z ∈ H, t.1.2.1 z ∈ H \ (AR ω ∪ A' ω) := fun z hz => by
    rw [hARw, hA'w, ← union_assoc, union_self]
    exact hCsub (hc.2.2.1 hz)
  have hcHL : ∀ z ∈ H, t.1.2.1 z ∈ H \ (AL ω ∪ A' ω) := fun z hz => by
    rw [hALw, hA'w, union_comm (wsetOf _) (wsetOf _), ← union_assoc, union_self, union_comm]
    exact hCsub (hc.2.2.1 hz)
  have hcHU : ∀ z ∈ H, t.1.2.1 z ∈ H \ A' ω := fun z hz => by
    rw [hA'w]
    exact hCsub (hc.2.2.1 hz)
  -- the real matches
  have hrealx : ∀ x : ℝ, IsRealMatch (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2 b jumps t.1 x (t.2.1 x) →
      Tendsto (fun w => v (t.1.2.1 w) + u₀ (t.1.2.1 w) + QuantumZipper.chiC κ * t.1.2.2 (t.1.2.1 w))
        (𝓝[H] (x : ℂ)) (𝓝 (t.2.1 x)) := fun x hm =>
    tendsto_of_realMatch hm hcHU hA'w.le (fun a ha => hrealω v hv hvrep a ha) hu₀
  refine ⟨insert 0 Eℝ, hEf.insert 0, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := fun h0 => hx (Or.inl h0)
  have hxE : x ∉ Eℝ := fun h' => hx (Or.inr h')
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rcases (hmatch x hxE).2 hneg with ⟨hpm, hval⟩ | hrm
    · rw [hval, bigLambda]
      refine tendsto_of_pieceMatch (w := wL) hpm hcHL ?_ ?_
      · intro pre post pc τ hs hτ y p hinv hpP hloc hside
        have := (hSLω wL hwL hwLrep pre post pc hs τ hτ y p hinv hpP (by rwa [hLw])).2
          (by simpa using hside)
        exact this
      · intro p hp hloc
        refine hcLω wL v hwL hwLrep hv hvrep p (by rw [hALw]; exact hp) ?_ ?_ ?_
        · rw [hA'w]
          rcases hp with hp | hp
          · exact Or.inl (Or.inr hp)
          · exact Or.inr hp
        · obtain ⟨r, hr, hsub⟩ := hloc
          refine ⟨r, hr, ?_⟩
          rw [hA'w, hALw, union_inter_distrib_right]
          exact union_subset hsub inter_subset_left
        · refine ⟨1, one_pos, ?_⟩
          rw [hA'w, hALw]
          exact inter_subset_left.trans subset_union_right
    · exact hrealx x hrm
  · rcases (hmatch x hxE).1 hpos with ⟨hpm, hval⟩ | hrm
    · rw [hval, bigLambda]
      refine tendsto_of_pieceMatch (w := wR) hpm hcHR ?_ ?_
      · intro pre post pc τ hs hτ y p hinv hpP hloc hside
        have := (hSRω wR hwR hwRrep pre post pc hs τ hτ y p hinv hpP (by rwa [hRw])).1
          (by simpa using hside)
        rw [show -(sleLambda κ - Real.pi / 2 * QuantumZipper.chiC κ) =
          -sleLambda κ - -(Real.pi / 2) * QuantumZipper.chiC κ by ring]
        exact this
      · intro p hp hloc
        refine hcRω wR v hwR hwRrep hv hvrep p (by rw [hARw]; exact hp) ?_ ?_ ?_
        · rw [hA'w]
          rcases hp with hp | hp
          · exact Or.inl (Or.inl hp)
          · exact Or.inr hp
        · obtain ⟨r, hr, hsub⟩ := hloc
          refine ⟨r, hr, ?_⟩
          rw [hA'w, hARw, union_inter_distrib_right]
          exact union_subset inter_subset_left hsub
        · refine ⟨1, one_pos, ?_⟩
          rw [hA'w, hARw]
          exact inter_subset_left.trans subset_union_left
    · exact hrealx x hrm

end InteractingSLE.Theorem14.WalkBdry
