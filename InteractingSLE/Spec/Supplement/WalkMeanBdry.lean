/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMeanAssembly
import InteractingSLE.Spec.Sec7.Lemma78MeanAssembly
import InteractingSLE.Spec.Supplement.GW3Chart

/-!
# Theorem 1.4's union mean: identification from chart boundary values

Packet PROVE-T14-WALKMEAN. Lemma GW3's proof (p. 637): "The only uncomputed physical points are the two component
endpoints, the finitely many original height marks, and the finitely many actual flow/connector junctions. … The same
local-set disk bounds and finite-exception harmonic uniqueness as GB2 remove any singular harmonic term"; follow-up
note A–E, D.6. This file reduces the pathwise union mean `WalkUnionMeanPathStatement` to its **boundary values**:

* `WalkUnionBdryStatement` (named input): a component chart, a piecewise-constant word `bC` with the heights (GW3.1)
  (`IsComponentBoundaryData`), chosen as a **deterministic function of the two final runs** (`sel`), such that, almost
  surely, on every component between the walks the union mean read in the chart (with the derivative-argument
  correction `χ · lift`) tends to `bC x` at every real point `x` outside a finite set;
* **`walkUnionMeanPathStatement_of_bdry`**: `WalkUnionMeanPathStatement` from the boundary values (and Theorems
  1.2–1.3, used only for the marked locality of the union). The identification is Aux. 27–28 on every component,
  bounded or not (`Sec6.ae_eqOn_component_of_tendsto_global`), through the Riemann map `c.inv ∘ cayleyInv`; the
  run-determined mean is `unionMeanOf sel` (the bounded extension of `bC` in the chart minus `χ · lift`).

Deterministic helpers: `isConformalBijection_fwd_of_isComponentChart`, `isConformalBijection_inv_of_isComponentChart`,
`tendsto_disk_of_componentChart` (prime ends in the disk from real points of the chart), `bddExt`
(the bounded harmonic extension of a word), `eq_of_mem_betweenComponents` (a point lies in at most one component).

R48: Theorems 1.2–1.3 are used as hypotheses; these results serve Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (cayley cayleyInv)
open Function (invFunOn)

universe u

namespace InteractingSLE.Theorem14.WalkMean

open WalkLaw GW3Between LocalSets

/-! ### Component charts as conformal bijections -/

section Chart

variable {R L C : Set ℂ} {c : Chart}

/-- The forward map of a component chart is a conformal bijection of the component onto `ℍ`. -/
theorem isConformalBijection_fwd_of_isComponentChart (hc : IsComponentChart R L C c) :
    IsConformalBijection c.1 C {w : ℂ | 0 < w.im} :=
  ⟨hc.1, hc.2.2.2.1.bijOn hc.2.1 hc.2.2.1⟩

/-- The inverse map of a component chart is a conformal bijection of `ℍ` onto the component. -/
theorem isConformalBijection_inv_of_isComponentChart (hc : IsComponentChart R L C c) (hCo : IsOpen C) :
    IsConformalBijection c.2.1 H C := by
  have hbij : BijOn c.1 C H := hc.2.2.2.1.bijOn hc.2.1 hc.2.2.1
  have hf : IsConformalBijection c.1 (⟨C, hCo⟩ : Opens ℂ) (⟨H, QuantumZipper.isOpen_H⟩ : Opens ℂ) := ⟨hc.1, hbij⟩
  have hg := SupercriticalConformalCovariance.GM24.isConformalBijection_invFunOn hf
  have heq : EqOn (invFunOn c.1 C) c.2.1 H := fun w hw => by
    have h1 : c.2.1 w ∈ C := hc.2.2.1 hw
    have h2 : c.1 (c.2.1 w) = w := hc.2.2.2.1.2 hw
    calc invFunOn c.1 C w = invFunOn c.1 C (c.1 (c.2.1 w)) := by rw [h2]
      _ = c.2.1 w := hbij.injOn.leftInvOn_invFunOn h1
  exact ⟨hg.1.congr fun w hw => (heq hw).symm, hg.2.congr heq⟩

end Chart

/-! ### The bounded harmonic extension of a word -/

/-- The bounded harmonic extension of the word `(bC, jumpsC)` (junk `0` if there is none). -/
def bddExt (bC : ℝ → ℝ) (jumpsC : Finset ℝ) : ℂ → ℝ :=
  haveI := Classical.propDecidable
  if hex : ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u then hex.choose else 0

theorem isBoundedHarmonicExtension_bddExt {bC : ℝ → ℝ} {jumpsC : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData bC jumpsC) : IsBoundedHarmonicExtension bC jumpsC (bddExt bC jumpsC) := by
  have hex : ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension bC jumpsC u :=
    (PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb).imp fun _ h => h.1
  rw [bddExt, dite_eq_left hex]
  exact hex.choose_spec

theorem eqOn_bddExt {bC : ℝ → ℝ} {jumpsC : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData bC jumpsC)
    {u : ℂ → ℝ} (hu : IsBoundedHarmonicExtension bC jumpsC u) : EqOn u (bddExt bC jumpsC) H := by
  obtain ⟨w, -, hw⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  exact (hw u hu).trans (hw _ (isBoundedHarmonicExtension_bddExt hb)).symm

/-! ### Prime ends in the disk from real points of a component chart -/

/-- **Chart boundary values give the boundary hypothesis of Aux. 28 in the disk** (as
`Restart.tendsto_disk_of_chartBoundaryLimit`, for a component chart and a bounded harmonic extension `G` of a word). -/
theorem tendsto_disk_of_componentChart {R L C : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c)
    {bC : ℝ → ℝ} {jumpsC : Finset ℝ} {G : ℂ → ℝ} (hG : IsBoundedHarmonicExtension bC jumpsC G) (χ : ℝ)
    {F v : ℂ → ℝ} {Eℝ : Set ℝ}
    (hlim : ∀ x : ℝ, x ∉ Eℝ → Tendsto (fun w => v (c.2.1 w) + F (c.2.1 w) + χ * c.2.2 (c.2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 (bC x))) :
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' (Eℝ ∪ ↑jumpsC)) →
      Tendsto (fun ζ => (v ((c.2.1 ∘ cayleyInv) ζ) + F ((c.2.1 ∘ cayleyInv) ζ)) -
          (G (c.1 ((c.2.1 ∘ cayleyInv) ζ)) - χ * c.2.2 ((c.2.1 ∘ cayleyInv) ζ)))
        (𝓝[ball 0 1] q) (𝓝 0) := by
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h1 => hqE (Set.mem_insert_iff.2 (Or.inl h1))
  set w : ℝ := (cayleyInv q).re with hw
  have hqw : cayleyInv q = (w : ℂ) := Restart.cayleyInv_eq_ofReal_re hq
  have hwE : w ∉ Eℝ ∪ ↑jumpsC := by
    intro hmem
    refine hqE (mem_insert_of_mem _ ⟨w, hmem, ?_⟩)
    show cayley (w : ℂ) = q
    rw [← hqw]
    exact QuantumZipper.CA.cayley_cayleyInv hq1
  have hT : Tendsto cayleyInv (𝓝[ball 0 1] q) (𝓝[H] (w : ℂ)) := by
    rw [← hqw]; exact Sec6.tendsto_cayleyInv_nhdsWithin_ball hq1
  have h1 := (hlim w fun h => hwE (Or.inl h)).comp hT
  have h2 := (hG.2.2 w fun h => hwE (Or.inr h)).comp hT
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hζH : cayleyInv ζ ∈ H := QuantumZipper.CA.cayleyInv_mem_H hζ
  simp only [Function.comp_apply, hc.2.2.2.1.2 hζH]
  ring

/-! ### Components between the walks -/

/-- A point lies in at most one component between the walks. -/
theorem eq_of_mem_betweenComponents {R L C C' : Set ℂ} (hC : C ∈ betweenComponents R L)
    (hC' : C' ∈ betweenComponents R L) {z : ℂ} (hz : z ∈ C) (hz' : z ∈ C') : C = C' := by
  obtain ⟨z₁, -, rfl⟩ := GW3Joint.exists_eq_connectedComponentIn_of_mem_betweenComponents hC
  obtain ⟨z₂, -, rfl⟩ := GW3Joint.exists_eq_connectedComponentIn_of_mem_betweenComponents hC'
  exact (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm

/-! ### The run-determined union mean of a chart selector -/

/-- The union mean determined by a chart selector `sel`: on a component `C` between the walks of the final runs `r`,
the bounded harmonic extension of the selected word read in the selected chart, minus `χ` times the selected lift
(`0` off the components). -/
def unionMeanOf (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (sel : ExplState × ExplState → Set ℂ → Chart × (ℝ → ℝ) × Finset ℝ) (r : ExplState × ExplState) (z : ℂ) : ℝ :=
  haveI := Classical.propDecidable
  if hz : ∃ C ∈ betweenComponents (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2), z ∈ C then
    bddExt (sel r hz.choose).2.1 (sel r hz.choose).2.2 ((sel r hz.choose).1.1 z) -
      QuantumZipper.chiC κ * (sel r hz.choose).1.2.2 z
  else 0

theorem unionMeanOf_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {sel : ExplState × ExplState → Set ℂ → Chart × (ℝ → ℝ) × Finset ℝ} {r : ExplState × ExplState} {C : Set ℂ}
    (hC : C ∈ betweenComponents (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2)) {z : ℂ} (hz : z ∈ C) :
    unionMeanOf κ b jumps sel r z =
      bddExt (sel r C).2.1 (sel r C).2.2 ((sel r C).1.1 z) - QuantumZipper.chiC κ * (sel r C).1.2.2 z := by
  have hex : ∃ C ∈ betweenComponents (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2), z ∈ C := ⟨C, hC, hz⟩
  have hch : hex.choose = C := eq_of_mem_betweenComponents hex.choose_spec.1 hC hex.choose_spec.2 hz
  rw [unionMeanOf, dite_eq_left hex, hch]

/-! ### The named input: boundary values in a run-determined chart -/

/-- **Named input: the boundary values of the union mean in run-determined component charts** (Lemma GW3 and its
proof, pp. 636–637; follow-up note A–E, D.2–D.6). For a measurable version `A'` of the union of the two walks and any
version `g` of its local-set mean for the centred field `h − u₀`, there is a selector `sel` — a **deterministic**
function of the two final runs and of the component — of a component chart `c`, of a piecewise-constant word `bC`
with the heights (GW3.1) and of its marks, such that, almost surely, on every component `C` between the walks: `c` is a
component chart of `C`, `bC` is the component word (`IsComponentBoundaryData`), and for every harmonic representative
`v` of `g` on `ℍ ∖ A'`, the mean read in the chart, `(v + u₀) ∘ c⁻¹ + χ · lift ∘ c⁻¹`, tends to `bC x` at every real
point `x` outside a finite set. (Proof route: the single-walk kernels of GW1 with their heights (D1)–(D2) at real
records, the nested marked collar comparison (Proposition 3.8 for marked local sets) away from the other walk, the
zero lifts of the intervening hydrodynamic maps (Aux. 57), and GB2's connected-interval normalization of the lift in
the active chart of retained prefixes, which makes the choice a function of the runs.) -/
def WalkUnionBdryStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' → (∀ᵐ ω ∂P, A' ω = walkUnionSet κ b jumps E ω) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A' (WholeField.centredField h u₀) P g →
      ∃ sel : ExplState × ExplState → Set ℂ → Chart × (ℝ → ℝ) × Finset ℝ, ∀ᵐ ω ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)),
          IsComponentChart
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) C
              (sel (walkRuns κ b jumps E ω) C).1 ∧
            IsPiecewiseConstantBoundaryData (sel (walkRuns κ b jumps E ω) C).2.1
              (sel (walkRuns κ b jumps E ω) C).2.2 ∧
            IsComponentBoundaryData κ b
              (ExplState.ordinarySet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
              (ExplState.ordinarySet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))
              (sel (walkRuns κ b jumps E ω) C).1.2.1 (sel (walkRuns κ b jumps E ω) C).2.1
              (sel (walkRuns κ b jumps E ω) C).2.2 ∧
            ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A' ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A' ω → g ω φ = ∫ z, v z * φ z) →
              ∃ Eℝ : Set ℝ, Eℝ.Finite ∧ ∀ x : ℝ, x ∉ Eℝ →
                Tendsto (fun w => v ((sel (walkRuns κ b jumps E ω) C).1.2.1 w) +
                    u₀ ((sel (walkRuns κ b jumps E ω) C).1.2.1 w) +
                    QuantumZipper.chiC κ * (sel (walkRuns κ b jumps E ω) C).1.2.2
                      ((sel (walkRuns κ b jumps E ω) C).1.2.1 w))
                  (𝓝[H] (x : ℂ)) (𝓝 ((sel (walkRuns κ b jumps E ω) C).2.1 x))

/-! ### The identification -/

/-- **The pathwise union mean from its chart boundary values** (Aux. 27–28 on every between component). -/
theorem walkUnionMeanPathStatement_of_bdry (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hB : WalkUnionBdryStatement.{u}) : WalkUnionMeanPathStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hreg hreg' u₀ hu₀ A' hA'm hA'ae g hg
  obtain ⟨sel, hsel⟩ := hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hreg' u₀ hu₀ A' hA'm hA'ae g hg
  refine ⟨unionMeanOf κ b jumps sel, ?_⟩
  have hpi := Real.pi_pos
  have hdet := pastDetRegStatement_of_thm12_thm13 h12p h13
  have hRl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith⟩ true
  have hLl := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 (θ := Real.pi / 2)
    ⟨by linarith, le_rfl⟩ false
  obtain ⟨-, hAo, -, -⟩ := walkUnion_markedAE hdet hRl hLl hκ hκ4 hb hh hE hreg hreg' hu₀
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hAc : ∀ᵐ ω ∂P, A' ω ⊆ H ∧ IsOpen (H \ A' ω) := by
    filter_upwards [hA'ae, hAo] with ω h1 h2
    rw [h1]
    exact ⟨union_subset (walkSet_subset_H _ _ _ _ _ _) (walkSet_subset_H _ _ _ _ _ _), h2⟩
  have hlocA : IsLocalSet A' (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hA'm hAc).out 3 4).1 (isGermConditionalLaw_iff.2 ⟨g, hg⟩)
  have hid := Sec6.ae_eqOn_component_of_tendsto_global hh0 hA'm hlocA hg hu₀.1 hu₀.2.1 (QuantumZipper.chiC κ)
  filter_upwards [hsel, hid, hg.2.1, hA'ae, hAo] with ω hselω hidω ⟨v, hv, hvrep⟩ hAω hoω
  have hHA : H \ A' ω = H \ (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ∪
      ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) := by
    rw [hAω, walkUnionSet, H_diff_walkSet_union]
  have hUo : IsOpen (H \ (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ∪
      ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))) := by
    rw [← hHA, hAω]
    exact hoω
  -- the identification on each between component
  have hC : ∀ C ∈ betweenComponents
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)),
      IsOpen C ∧ C ⊆ H \ A' ω ∧ ∀ z ∈ C, v z + u₀ z = unionMeanOf κ b jumps sel (walkRuns κ b jumps E ω) z := by
    intro C hCm
    obtain ⟨hc, hbC, -, hbd⟩ := hselω C hCm
    obtain ⟨z₀, hz₀, hCeq⟩ := GW3Joint.exists_eq_connectedComponentIn_of_mem_betweenComponents hCm
    have hz₀' : z₀ ∈ H \ A' ω := hHA ▸ hz₀
    have hcc : connectedComponentIn (H \ A' ω) z₀ = C := by rw [hHA, hCeq]
    have hCo : IsOpen C := by rw [hCeq]; exact hUo.connectedComponentIn
    have hG := isBoundedHarmonicExtension_bddExt hbC
    obtain ⟨Eℝ, hEfin, hlim⟩ := hbd v hv hvrep
    have hf : IsConformalBijection ((sel (walkRuns κ b jumps E ω) C).1.2.1 ∘ cayleyInv) (ball 0 1)
        (connectedComponentIn (H \ A' ω) z₀) := by
      rw [hcc]
      exact isConformalBijection_comp (isConformalBijection_inv_of_isComponentChart hc hCo)
        isConformalBijection_cayleyInv
    have hφc : IsConformalBijection (sel (walkRuns κ b jumps E ω) C).1.1 (connectedComponentIn (H \ A' ω) z₀)
        {w : ℂ | 0 < w.im} := by
      rw [hcc]
      exact isConformalBijection_fwd_of_isComponentChart hc
    have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) ''
        (Eℝ ∪ ↑(sel (walkRuns κ b jumps E ω) C).2.2))).Finite :=
      ((hEfin.union (sel (walkRuns κ b jumps E ω) C).2.2.finite_toSet).image _).insert 1
    have hLc : ContinuousOn (sel (walkRuns κ b jumps E ω) C).1.2.2 (connectedComponentIn (H \ A' ω) z₀) := by
      rw [hcc]
      exact hc.2.2.2.2.2.1
    have hL : ∀ z ∈ connectedComponentIn (H \ A' ω) z₀, deriv (sel (walkRuns κ b jumps E ω) C).1.1 z =
        ‖deriv (sel (walkRuns κ b jumps E ω) C).1.1 z‖ *
          exp ((sel (walkRuns κ b jumps E ω) C).1.2.2 z * I) := by
      rw [hcc]
      exact hc.2.2.2.2.2.2
    have heq := hidω z₀ hz₀' v hv hvrep _ _ (bddExt (sel (walkRuns κ b jumps E ω) C).2.1
      (sel (walkRuns κ b jumps E ω) C).2.2) _ _ hf hφc hG.1 hG.2.1 hLc hL hEd
      (tendsto_disk_of_componentChart hc hG _ hlim)
    rw [hcc] at heq
    refine ⟨hCo, hcc ▸ connectedComponentIn_subset _ _, fun z hz => ?_⟩
    rw [heq z hz]
    exact (unionMeanOf_eq (r := walkRuns κ b jumps E ω) hCm hz).symm
  have hBU : ∀ z ∈ betweenUnion
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)),
      ∃ C ∈ betweenComponents
        (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω))
        (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)), z ∈ C := fun z hz => by
    obtain ⟨C, hCm, hzC⟩ := mem_sUnion.1 hz
    exact ⟨C, hCm, hzC⟩
  refine ⟨fun z hz => ?_, fun φ hφ => ?_, fun C hCm => ?_⟩
  · obtain ⟨C, hCm, hzC⟩ := hBU z hz
    obtain ⟨hCo, hCA, hCeq⟩ := hC C hCm
    have hev : (fun w => v w + u₀ w) =ᶠ[𝓝 z] unionMeanOf κ b jumps sel (walkRuns κ b jumps E ω) :=
      Filter.eventuallyEq_of_mem (hCo.mem_nhds hzC) fun w hw => hCeq w hw
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).1 ((hv z (hCA hzC)).add (hu₀.1 z (hCA hzC).1))
  · have hφA : tsupport φ ⊆ H \ A' ω := fun z hz => by
      obtain ⟨C, hCm, hzC⟩ := hBU z (hφ hz)
      exact (hC C hCm).2.1 hzC
    rw [hvrep φ hφA]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show v z * φ z = (unionMeanOf κ b jumps sel (walkRuns κ b jumps E ω) z - u₀ z) * φ z
    by_cases hz : z ∈ tsupport φ
    · obtain ⟨C, hCm, hzC⟩ := hBU z (hφ hz)
      rw [← (hC C hCm).2.2 z hzC]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hz]
      ring
  · obtain ⟨hc, hbC, hcb, -⟩ := hselω C hCm
    refine ⟨_, hc, _, _, hbC, hcb, fun u₀' hu₀' w hw => ?_⟩
    have hwC : (sel (walkRuns κ b jumps E ω) C).1.2.1 w ∈ C := hc.2.2.1 hw
    rw [unionMeanOf_eq (r := walkRuns κ b jumps E ω) hCm hwC, hc.2.2.2.1.2 hw, eqOn_bddExt hbC hu₀' hw]
    ring

/-! ### Wrappers -/

/-- **The union-mean leaf from its chart boundary values** (Theorems 1.2–1.3 as hypotheses, R48: Theorem 1.4 only). -/
theorem walkUnionMeanRegAEStatement_of_bdry (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hB : WalkUnionBdryStatement.{u}) : WalkUnionMeanRegAEStatement.{u} :=
  walkUnionMeanRegAEStatement_of_path h12p h13 (walkUnionMeanPathStatement_of_bdry h12p h13 hB)

/-- The union-mean leaf from the roots of the expanded wiring and the chart boundary values. -/
theorem walkUnionMeanRegAEStatement_of_bdry_roots (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hB : WalkUnionBdryStatement.{u}) : WalkUnionMeanRegAEStatement.{u} :=
  walkUnionMeanRegAEStatement_of_bdry (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hB

/-- **GW3's union law on the between components from Theorems 1.2–1.3 and the chart boundary values.** -/
theorem gw3UnionLawBetweenRegStatement_of_bdry (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hB : WalkUnionBdryStatement.{u}) :
    GW3Between.GW3UnionLawBetweenRegStatement.{u} :=
  WalkLeaf.gw3UnionLawBetweenRegStatement_of_unionMean h12p h13 (walkUnionMeanRegAEStatement_of_bdry h12p h13 hB)

end InteractingSLE.Theorem14.WalkMean
