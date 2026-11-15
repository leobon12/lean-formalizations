/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideInputs
import InteractingSLE.Spec.Supplement.WalkBdryCompare

/-!
# Theorem 1.4's walk leaves: `WalkPrefixSideStatement` from the two prefix inputs

Packet PROVE-T14-WALKSIDE. Lemma GW3, proof (`source/spec/p625-671.md` L218, p. 636): "On an ordinary selected subarc
the incoming own germ is, respectively, `λ − (π/2)χ = Λ` or `−λ + (π/2)χ = −Λ`. The other incoming set is separated
from every compact proper subarc. The nested marked collar comparison and the zero lifts of the intervening own
hydrodynamic maps preserve that germ."

For a recorded piece `pc` of the walk (launched by instruction `ℓ`) and a rational own time `τ` before its stop, the
**prefix set** is the explored set of the capped program `capSpec w ℓ θ τ` (`WalkSide.prefixSet_eq_stageSet`) and the
prefix chart is its chart (`prefixChart_eq_chart`). The proof:

1. the prefix set is a marked local set for the capped retained past (`PrefixMarkedLocalStatement`), and its own mean,
   read in the prefix chart, is the bounded harmonic mean of Lemma GW1's stop word (`ae_capMean`, from the landed staged
   law; the chart through the measurable version of `PrefixChartVersionStatement`);
2. the walk's mean and the prefix's mean have the same boundary values where the two sets agree (Proposition 3.8,
   `Sec7.PocketStopSide.ae_tendsto_sub_of_marked_union`: the union is the walk, retained by the walk's past; both lower
   unions are connected, `not_isBounded_lowerUnion_stageSet`);
3. at a side point the stop word is `−λ − θχ` (left) or `λ − θχ` (right) (`stopWord_leftSide`, `stopWord_rightSide`).

* `ratBump`, **`eqOn_of_ratBump`**: harmonic functions with the same rational-bump pairings agree;
* **`tendsto_side_of_eqOn`**: the pathwise limit through the prefix chart;
* **`ae_prefix_limit`**: steps 1–2 for one instruction and one rational time;
* **`walkPrefixSideStatement_of_inputs`**: `WalkBdry.WalkPrefixSideStatement θ right` from the two inputs and
  Theorems 1.2–1.3 (through the walk's marked locality; R48: Theorem 1.4 only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkSide

open Exist.StagedLaw Exist.Staged Restart LocalSets

/-! ### Pathwise lemmas -/

section Path

open Classical in
/-- The rational radial bumps in `ℍ` (`0` for an index whose closed disc leaves `ℍ`). -/
def ratBump (i : ℚ × ℚ × ℚ) : TestOn upperHalfPlaneOpens :=
  if hi : 0 < (i.2.2 : ℝ) ∧ closedBall (WangWu.ratPt i.1 i.2.1) i.2.2 ⊆ (upperHalfPlaneOpens : Set ℂ) then
    GFF.bumpTest (WangWu.ratPt i.1 i.2.1) hi.1 hi.2 else 0

/-- **Harmonic functions with the same pairings against the rational bumps inside an open set agree there** (mean
value property and density of the rational points). -/
theorem eqOn_of_ratBump {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) {v m : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v U) (hm : InnerProductSpace.HarmonicOnNhd m U)
    (h : ∀ i : ℚ × ℚ × ℚ, tsupport (ratBump i) ⊆ U → ∫ z, v z * ratBump i z = ∫ z, m z * ratBump i z) :
    EqOn v m U := by
  have hcont : ∀ {f : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd f U → ContinuousOn f U :=
    fun hf z hz => (hf z hz).1.continuousAt.continuousWithinAt
  have hrat : ∀ a b : ℚ, WangWu.ratPt a b ∈ U → v (WangWu.ratPt a b) = m (WangWu.ratPt a b) := by
    intro a b hab
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hU _ hab
    obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (half_pos hε)
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    have hB : closedBall (WangWu.ratPt a b) r ⊆ U := (closedBall_subset_ball (by linarith)).trans hεO
    have hBH : closedBall (WangWu.ratPt a b) r ⊆ (upperHalfPlaneOpens : Set ℂ) := hB.trans hUH
    have hbi : ratBump (a, b, r) = GFF.bumpTest (WangWu.ratPt a b) hr0' hBH := by
      simp only [ratBump, show 0 < (r : ℝ) ∧ closedBall (WangWu.ratPt a b) r ⊆ (upperHalfPlaneOpens : Set ℂ) from
        ⟨hr0', hBH⟩, and_self, ↓reduceDIte]
    have hsupp : tsupport (ratBump (a, b, r)) ⊆ U := by
      rw [hbi, GFF.coe_bumpTest]
      exact (GFF.tsupport_bumpFun_subset hr0').trans hB
    have e1 := h (a, b, r) hsupp
    rw [hbi, GFF.coe_bumpTest, GFF.integral_mul_bumpFun_of_harmonic hU hv hr0' hB,
      GFF.integral_mul_bumpFun_of_harmonic hU hm hr0' hB] at e1
    have hpos : 0 < (r : ℝ) ^ 2 * GFF.bumpMass := by
      have := GFF.bumpMass_pos; positivity
    exact mul_right_cancel₀ hpos.ne' e1
  refine Set.EqOn.of_subset_closure (s := U ∩ range fun p : ℚ × ℚ => WangWu.ratPt p.1 p.2) ?_
    (hcont hv) (hcont hm) inter_subset_left (WangWu.denseRange_ratPt.open_subset_closure_inter hU)
  rintro z ⟨hz, ⟨a, b⟩, rfl⟩
  exact hrat a b hz

/-- **The limit through the prefix chart.** Let `c` be a conformal chart whose domain avoids `B`, on which a
harmonic function `vB` equals `𝔤 ∘ F − χ ℓ − 𝔥₀` (`𝔤` the mean of a sorted word `β`); let `v − vB → 0` at `p` from
outside `A ∪ B`, `A` inside `B` near `p`, and `c.inv → p` at a real point `y` off the jumps of `β`. Then
`v + 𝔥₀ + χ ℓ`, read through `c`, tends to `β(y)` at `y`. -/
theorem tendsto_side_of_eqOn {A B : Set ℂ} {c : Chart} (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) ⊆ H \ B)
    {β : BoundaryWord} (hβ : β.IsSorted) {u₀ : ℂ → ℝ} {χ : ℝ} {v vB : ℂ → ℝ}
    (heq : EqOn vB (fun z => β.mean (c.1 z) - χ * c.2.2 z - u₀ z) c.dom) {p : ℂ}
    (hcmp : Tendsto (fun z => v z - vB z) (𝓝[H \ (A ∪ B)] p) (𝓝 0)) {y : ℝ} (hy : y ∉ β.jumps)
    (hT : Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝 p)) {r : ℝ} (hr : 0 < r) (hAB : A ∩ ball p r ⊆ B) :
    Tendsto (fun ξ => v (c.2.1 ξ) + u₀ (c.2.1 ξ) + χ * c.2.2 (c.2.1 ξ)) (𝓝[H] (y : ℂ)) (𝓝 (β.fn y)) := by
  have hin : ∀ ξ ∈ H, c.2.1 ξ ∈ (c.dom : Set ℂ) := fun ξ hξ => by
    rw [hc.coe_dom]; exact mem_image_of_mem _ hξ
  have h1 : Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝[H \ (A ∪ B)] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hT, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hT (ball_mem_nhds p hr)] with ξ hξ hball
    have hd := hdom (hin ξ hξ)
    refine ⟨hd.1, ?_⟩
    rintro (hA' | hB')
    · exact hd.2 (hAB ⟨hA', hball⟩)
    · exact hd.2 hB'
  have h2 := hcmp.comp h1
  have h3 : Tendsto β.mean (𝓝[H] (y : ℂ)) (𝓝 (β.fn y)) :=
    (BoundaryWord.isBoundedHarmonicExtension_mean β hβ).2.2 y hy
  have h4 := h2.add h3
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  have hv := heq (hin ξ hξ)
  simp only [Function.comp_apply] at hv ⊢
  rw [hv, hc.2.2 ξ hξ]
  ring

end Path

/-! ### The chart mean and the chart domain -/

section ChartDom

/-- The chart mean `𝔤 ∘ F − χ ℓ − 𝔥₀` is harmonic on the chart domain (harmonic lift). -/
theorem harmonicOnNhd_chartMean {c : Chart} (hc : c.IsConformal)
    (hl : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom) {β : BoundaryWord} (hβ : β.IsSorted) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (χ : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun z => β.mean (c.1 z) - χ * c.2.2 z - u₀ z) c.dom := by
  intro z hz
  have hO : IsOpen (c.dom : Set ℂ) := c.dom.isOpen
  have hfa : AnalyticAt ℂ c.1 z := hc.differentiableOn_fwd.analyticAt (hO.mem_nhds hz)
  have hfz : c.1 z ∈ H := by
    have hz' := hz
    rw [SetLike.mem_coe, ← SetLike.mem_coe, hc.coe_dom] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    rw [hc.2.2 w hw]
    exact hw
  have h1 : InnerProductSpace.HarmonicAt (fun z => β.mean (c.1 z)) z :=
    QuantumZipper.FieldLawler.fl_harmonicAt_comp hfa ((BoundaryWord.isBoundedHarmonicExtension_mean β hβ).1 _ hfz)
  have h2 : InnerProductSpace.HarmonicAt (fun z => χ * c.2.2 z) z := by
    have := (hl z hz).const_smul (c := χ)
    have e : (χ • fun z => c.2.2 z) = fun z => χ * c.2.2 z := by
      funext z; rw [Pi.smul_apply, smul_eq_mul]
    rwa [e] at this
  exact (h1.sub h2).sub (hu₀ z (hc.dom_subset hz))

/-- If the frontier of the chart domain in `ℍ` lies on `B`, the part of `ℍ \ B` off the domain is open. -/
theorem isOpen_diff_dom {B : Set ℂ} {c : Chart} (hBo : IsOpen (H \ B))
    (hfr : ∀ z ∈ H, z ∈ closure (c.dom : Set ℂ) → z ∉ c.dom → z ∈ B) : IsOpen ((H \ B) \ c.dom) := by
  have e : (H \ B) \ (c.dom : Set ℂ) = (H \ B) \ closure (c.dom : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨⟨hzH, hzB⟩, hzD⟩
      exact ⟨⟨hzH, hzB⟩, fun hcl => hzB (hfr z hzH hcl hzD)⟩
    · rintro ⟨hz, hcl⟩
      exact ⟨hz, fun hD => hcl (subset_closure hD)⟩
  rw [e]
  exact hBo.sdiff isClosed_closure

/-- **Named input (deterministic): the domain of the prefix chart avoids the prefix.** For a program `w` whose
instruction `ℓ` is an unstopped angle-`θ` flow that launched, with every launched piece regular, and a time `τ`
before the piece's lifetime: the domain of the chart of the capped run after `ℓ + 1` instructions is disjoint from the
ordinary set of the capped run (the explored pieces lie on the boundary of the current domain, never inside it). -/
def PrefixChartDomStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (w : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ) (θ : ℝ) (τ : ℝ≥0),
    ℓ < w.2.2.length → w.2.2[ℓ]? = some (Sum.inl (θ, ⊤)) →
    (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none → (τ : ℝ≥0∞) < (D ℓ).2 →
    (∀ (k : ℕ) (c : Chart) (θ' : ℝ), (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime w k) (D k).2)) →
    Disjoint ((ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).2.2.2.2.1.dom : Set ℂ)
      (⋃ p ∈ (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).1, p.1.tipSet p.2.1 p.2.2)

end ChartDom

/-! ### One instruction and one rational time -/

section Prefix

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u₀ : ℂ → ℝ} {A : Ω → Set ℂ} {g : Ω → DistOn upperHalfPlaneOpens}

/-- **The walk's mean through the prefix chart, for one instruction `ℓ` and one rational time `τ`.** Almost surely on
the capped launch event, the record of the piece stopped at `τ` is good and, for every harmonic representative `v` of
the walk's mean, `v + 𝔥₀ + χ ℓ` read through the prefix chart tends at every real point `y` off the jumps of the stop
word (whose landing point `p` is a point of the prefix or real, near which the walk is the prefix) to the stop word at
`y`. -/
theorem ae_prefix_limit (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hA : PrefixMarkedLocalStatement.{u} θ right) (hB : PrefixChartVersionStatement.{u} θ right)
    (hC : PrefixChartDomStatement) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg : ∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), IsRegularDriver (E spec k ω))
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] A)
    (hAae : ∀ᵐ ω ∂P, A ω = WalkLaw.walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
      (E (boundaryWalkSpec b jumps θ right)) ω)
    (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) (ℓ : ℕ) (τ : ℚ≥0) :
    ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
      ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) ℓ τ →
      LocalExt.IsDrvGood (recHist (recOf ((τ : ℝ≥0) : ℝ≥0∞) (E (boundaryWalkSpec b jumps θ right) ℓ ω))) ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, v z * φ z) →
        ∀ (y : ℝ) (p : ℂ),
          y ∉ (stopWord κ (β ω, θ, recOf ((τ : ℝ≥0) : ℝ≥0∞) (E (boundaryWalkSpec b jumps θ right) ℓ ω))).jumps →
          Tendsto (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))
            (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1.2.1 (𝓝[H] (y : ℂ)) (𝓝 p) →
          p ∈ WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))
            (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω ∪ {z : ℂ | z.im = 0} →
          (∃ r > 0, WalkLaw.walkSet κ b jumps (boundaryWalkSpec b jumps θ right)
            (E (boundaryWalkSpec b jumps θ right)) ω ∩ ball p r ⊆
              WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))
                (E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω) →
          Tendsto (fun ξ =>
              v ((ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))
                (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1.2.1 ξ) +
              u₀ ((ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))
                (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1.2.1 ξ) +
              chiC κ * (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))
                (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1.2.2
                ((ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ ((τ : ℝ≥0) : ℝ≥0∞))
                  (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1.2.1 ξ))
            (𝓝[H] (y : ℂ))
            (𝓝 ((stopWord κ (β ω, θ, recOf ((τ : ℝ≥0) : ℝ≥0∞) (E (boundaryWalkSpec b jumps θ right) ℓ ω))).fn y)) := by
  classical
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  -- the instruction must be an unstopped angle-`θ` flow of the walk, otherwise the event is empty
  by_cases hcond : ℓ < w.2.2.length ∧ w.2.2[ℓ]? = some (Sum.inl (θ, ⊤))
  swap
  · refine ⟨fun _ => default, Eventually.of_forall fun ω hω => absurd ?_ hcond⟩
    obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω.1
    obtain ⟨hins, -, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w _ hl
    obtain ⟨rfl, ht⟩ := WalkLeaf.boundaryWalkSpec_inl hins
    rw [ht] at hins
    exact ⟨(List.getElem?_eq_some_iff.1 hins).1, hins⟩
  obtain ⟨hℓ, hwℓ⟩ := hcond
  set w' := capSpec w ℓ θ ((τ : ℝ≥0) : ℝ≥0∞) with hw'
  have hEw := hE w hw
  have hRw := hR w hw
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the walk: marked locality; the given version is local
  obtain ⟨hWev, hWo, hWloc⟩ := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13 hθ right
    κ hκ hκ4 b jumps hb P h hh E hE hR hreg u₀ hu₀
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hAae, hWo] with ω h1 h2
    rw [h1]
    exact ⟨WalkLaw.walkSet_subset_H _ _ _ _ _ ω, h2⟩
  have hAmark := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hAae.mono fun ω h => h.symm) hWloc
  have hAloc : IsLocalSet A (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm hAc).out 1 4).1 hAmark.isAvoidanceLocal
  have hAJ : MeasurableSpace.comap A hittingSigma ≤ aeSigma (pastSigma κ b jumps w (E w) w.2.2.length) P :=
    WalkBdry.hitting_comap_le_aeSigma (WalkBdry.avoid_aeSigma_congr hAae hWev)
  -- the prefix: a version, local and marked for the capped past, and its mean
  have hS' : IsStagedHistory κ b jumps P h w' (E w) := isStagedHistory_capSpec hb hEw (hreg w) hℓ hwℓ
  have h𝓗 : pastSigma κ b jumps w' (E w) (ℓ + 1) ≤ mΩ := hS'.2.1 (ℓ + 1)
  obtain ⟨hBev, hBo, hBloc0⟩ := hA κ hκ hκ4 b jumps hb P h hh E hE hR hreg u₀ hu₀ ℓ τ
  obtain ⟨B, hBH, hBae, hBm⟩ := WalkLaw.exists_version_of_aeSigma
    (fun ω => WalkLaw.stageSet_subset_H κ b jumps w' (E w) (ℓ + 1) ω) hBo hBev
  have hBmp : Measurable[pastSigma κ b jumps w' (E w) (ℓ + 1), hittingSigma] B :=
    WalkMean.measurable_hitting_of_avoid (mΩ := pastSigma κ b jumps w' (E w) (ℓ + 1)) le_rfl hBm
  have hBm' : Measurable[mΩ, hittingSigma] B := hBmp.mono h𝓗 le_rfl
  have hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω) := by
    filter_upwards [hBae, hBo] with ω h1 h2
    exact ⟨hBH ω, h1 ▸ h2⟩
  have hBmark := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hBae.mono fun ω h => h.symm) hBloc0
  have hBloc : IsLocalSet B (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hBm' hBc).out 1 4).1 hBmark.isAvoidanceLocal
  obtain ⟨gB, hgB⟩ := IsLocalSet.exists_isLocalSetMean hh0 hBm' hBloc
  -- the chart version and the domain
  obtain ⟨c', hc'c, hc'l, hc'h, hdom, hfwd, hCm, hliftm, hc'eq⟩ := hB κ hκ hκ4 b jumps hb P h hh E hE hR hreg ℓ τ
  have hPR := hRw.ae_pieceRegular
  have hAD : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w (E w) ℓ τ →
      ((c' ω).dom : Set ℂ) ⊆ H \ B ω ∧ IsOpen ((H \ B ω) \ (c' ω).dom) := by
    filter_upwards [hc'eq, hBae, hPR, hBo] with ω hcω hBω hPRω hBoω hω
    have hreg' := pieceRegular_capSpec (fun j => E w j ω) hℓ.le hwℓ hPRω (τ : ℝ≥0)
    have hcc := (GW1RestartFinal.chart_boundaryRange_run w' (fun j => E w j ω) hreg' (ℓ + 1)).1
    have hdis := hC κ b jumps w (fun j => E w j ω) ℓ θ τ hℓ hwℓ hω.1 hω.2 hPRω
    rw [hcω hω, hBω]
    refine ⟨fun z hz => ⟨hcc.dom_subset hz, fun hzB => Set.disjoint_left.1 hdis hz hzB.1⟩, ?_⟩
    refine isOpen_diff_dom hBoω fun z hzH hzcl hzD => ?_
    exact WalkLeaf.mem_stageSet_of_frontier w' (E w) ω hreg' (ℓ + 1) z hzH hzcl hzD
  -- the prefix's own mean
  obtain ⟨β, hgood, hmean⟩ := ae_capMean hκ hb hh hEw (hreg w) hℓ hwℓ (τ : ℝ≥0) hu₀ hBm' hBloc hBmark hc'c hc'l
    hdom hfwd hCm hliftm hc'eq hAD hgB
  have hbumps : ∀ᵐ ω ∂P, ∀ i : ℚ × ℚ × ℚ, ω ∈ capEvent κ b jumps w (E w) ℓ τ →
      tsupport (ratBump i) ⊆ (c' ω).dom →
      gB ω (ratBump i) = (∫ z, ((stopWord κ (β ω, θ, recOf ((τ : ℝ≥0) : ℝ≥0∞) (E w ℓ ω))).mean ((c' ω).1 z) -
        chiC κ * (c' ω).2.2 z) * ratBump i z) - ∫ z, u₀ z * ratBump i z :=
    ae_all_iff.2 fun i => hmean (ratBump i)
  -- the comparison of the walk's mean with the prefix's
  have hBsub : ∀ᵐ ω ∂P, B ω ⊆ A ω := by
    filter_upwards [hBae, hAae] with ω h1 h2
    rw [h1, h2]
    exact stageSet_capSpec_subset_walkSet (E w) ω hℓ hwℓ (hreg w ℓ ω) (τ : ℝ≥0)
  have hmarked : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap A hittingSigma ⊔ MeasurableSpace.comap B hittingSigma) (fun ω => A ω ∪ B ω)
      (WholeField.centredField h u₀) P := by
    have hU : ∀ᵐ ω ∂P, WalkLaw.walkSet κ b jumps w (E w) ω = A ω ∪ B ω := by
      filter_upwards [hAae, hBsub] with ω h1 h2
      rw [union_eq_left.2 h2, h1]
    refine WalkMean.isHistoryAvoidanceLocal_of_le_aeSigma (sup_le hAJ ?_)
      (WalkLaw.isHistoryAvoidanceLocal_congr_ae hU hWloc)
    refine le_trans hBmp.comap_le (le_trans ?_ (le_aeSigma _ P))
    exact le_trans (pastSigma_capSpec_le (E w) hℓ.le hwℓ τ) (pastSigma_mono w (E w) (by omega))
  have hAunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z) := by
    filter_upwards [hAae, hPR] with ω h1 h2
    rw [h1, WalkLaw.walkSet_eq_stageSet]
    exact not_isBounded_lowerUnion_stageSet w (E w) ω h2 _
  have hBunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (B ω)) z) := by
    filter_upwards [hBae, hPR] with ω h1 h2
    rw [h1]
    exact not_isBounded_lowerUnion_stageSet w' (E w) ω
      (pieceRegular_capSpec (fun j => E w j ω) hℓ.le hwℓ h2 (τ : ℝ≥0)) _
  have hcmp := Sec7.PocketStopSide.ae_tendsto_sub_of_marked_union hh0 hAm hBm' hAloc hBloc hmarked hAunb hBunb hg hgB
  -- pathwise
  refine ⟨β, ?_⟩
  filter_upwards [hgood, hbumps, hcmp, hc'eq, hAD, hBae, hAae, hgB.2.1, hBsub] with
    ω hgω hbω hcmpω hcω hADω hBω hAω hgBω hBAω
  intro hω
  refine ⟨hgω hω, fun v hv hvg y p hy hT hp hloc => ?_⟩
  obtain ⟨vB, hvB, hvBg⟩ := hgBω
  obtain ⟨hdomB, -⟩ := hADω hω
  have hβs := isSorted_stopWord κ (β ω, θ, recOf ((τ : ℝ≥0) : ℝ≥0∞) (E w ℓ ω))
  set β' := stopWord κ (β ω, θ, recOf ((τ : ℝ≥0) : ℝ≥0∞) (E w ℓ ω)) with hβ'
  have hcm := harmonicOnNhd_chartMean (hc'c ω) (hc'h ω) hβs hu₀.1 (chiC κ)
  have hdH : ((c' ω).dom : Set ℂ) ⊆ H := (hc'c ω).dom_subset
  have hu₀c : ContinuousOn u₀ (c' ω).dom := fun z hz => (hu₀.1 z (hdH hz)).1.continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z) (c' ω).dom := by
    have h1 : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom :=
      fun z hz => (hcm z hz).1.continuousAt.continuousWithinAt
    refine (h1.add hu₀c).congr fun z _ => ?_
    simp only [Pi.add_apply]
    ring
  have heq : EqOn vB (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom := by
    refine eqOn_of_ratBump (c' ω).dom.isOpen hdH (hvB.mono hdomB) hcm fun i hi => ?_
    have hiB : tsupport (ratBump i) ⊆ H \ B ω := hi.trans hdomB
    rw [← hvBg _ hiB, hbω i hω hi, ← integral_sub (WholeField.integrable_mul_testOn hfc _ hi)
      (WholeField.integrable_mul_testOn hu₀c _ hi)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  have hpB : p ∈ B ω ∪ {z : ℂ | z.im = 0} := by rw [hBω]; exact hp
  have hpA : p ∈ A ω ∪ {z : ℂ | z.im = 0} := hpB.imp_left fun hz => hBAω hz
  obtain ⟨r, hr, hr'⟩ := hloc
  have hAB : A ω ∩ ball p r ⊆ B ω := by rw [hAω, hBω]; exact hr'
  have hlim := hcmpω v vB hv hvg hvB hvBg p hpA hpB ⟨1, one_pos, fun z hz => hBAω hz.1⟩ ⟨r, hr, hAB⟩
  have hTc : Tendsto (c' ω).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) := by rw [hcω hω]; exact hT
  have key := tendsto_side_of_eqOn (hc'c ω) hdomB hβs heq hlim hy hTc hr hAB
  rw [hcω hω] at key
  exact key

end Prefix

/-! ### The statement -/

/-- **`WalkBdry.WalkPrefixSideStatement θ right` from the two prefix inputs** (and the deterministic chart-domain
statement), for an angle in `[−π/2, π/2]`. Theorems 1.2–1.3 enter through the walk's marked locality
(`WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13`); R48: Theorem 1.4 only. -/
theorem walkPrefixSideStatement_of_inputs (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hA : PrefixMarkedLocalStatement.{u} θ right) (hB : PrefixChartVersionStatement.{u} θ right)
    (hC : PrefixChartDomStatement) : WalkBdry.WalkPrefixSideStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hR hreg u₀ hu₀ A hAm hAae g hg
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have key := fun lt : ℕ × ℚ≥0 =>
    ae_prefix_limit h12p h13 hθ hA hB hC hκ hκ4 hb hh hE hR hreg hu₀ hAm hAae hg lt.1 lt.2
  choose β hβ using key
  filter_upwards [ae_all_iff.2 hβ] with ω hω
  intro v hv hvg pre post pc hrun τ hτ y p hT hp hloc
  obtain ⟨ℓ, hℓn, θ', hl, hpre, hpc⟩ := exists_launch_of_pieces_eq w (fun j => E w j ω) w.2.2.length hrun
  obtain ⟨hins, -, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w _ hl
  obtain ⟨hθ', hT'⟩ := WalkLeaf.boundaryWalkSpec_inl hins
  rw [hT', hθ'] at hins
  rw [hT'] at hpc
  subst hpc hpre
  have hτζ : ((τ : ℝ≥0) : ℝ≥0∞) < (E w ℓ ω).2 := by
    have := hτ
    simp only [recPiece, le_top, min_eq_right] at this
    exact this
  have hτ' : ((τ : ℝ≥0) : ℝ≥0∞) < min ⊤ (E w ℓ ω).2 := by rwa [min_eq_right le_top]
  have hcap : ω ∈ capEvent κ b jumps w (E w) ℓ τ := ⟨by rw [hl]; exact Option.some_ne_none _, hτζ⟩
  obtain ⟨hgood, hlim⟩ := hω (ℓ, τ) hcap
  have hchart := prefixChart_eq_chart (E w) ω hℓn.le hins hl (hreg w ℓ ω) hτ'
  have hset := prefixSet_eq_stageSet (E w) ω hℓn.le hins hl (hreg w ℓ ω) hτ'
  rw [hset] at hp hloc
  rw [hchart] at hT ⊢
  refine ⟨fun hside => ?_, fun hside => ?_⟩
  · obtain ⟨hval, hnj⟩ := stopWord_leftSide θ (β (ℓ, τ) ω) _ (hreg w ℓ ω) hτ' hgood hside
    have h1 := hlim v hv hvg y p hnj hT hp hloc
    rwa [hval] at h1
  · obtain ⟨hval, hnj⟩ := stopWord_rightSide θ (β (ℓ, τ) ω) _ (hreg w ℓ ω) hτ' hgood hside
    have h1 := hlim v hv hvg y p hnj hT hp hloc
    rwa [hval] at h1

end InteractingSLE.Theorem14.WalkSide
