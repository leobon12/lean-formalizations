/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7Aux131Word
import InteractingSLE.Spec.Sec7.R7Aux131Walls
import InteractingSLE.Spec.Sec7.StripPocketConfigEvent
import InteractingSLE.Spec.Sec7.PocketLeftFrontier
import InteractingSLE.Spec.Supplement.R7Angles

/-!
# Aux. lemma 131's pocket from two constant-angle walls: the selection and the wiring of Theorem R.7's extremal case

Packet PROVE-R7-AUX131. Specification §7.4.1, proof of Aux. lemma 131 (`source/spec/p385-432.md` L527–L548,
pp. 414–416):

> "Its two constant-angle incoming paths are proper, continuous, simple, and reverse-contained in that counterflow.
> They are ordered by the already proved non-boundary constant-angle monotonicity. They cannot have identical ranges
> […] A noncontact interval exists on the right path. Otherwise its completed range would be contained in the left
> range. […] The left range is compact, so its preimage on the right path is closed; its nonempty complement therefore
> contains an open interval with a rational parameter. Select the first rationally labelled noncontact interval in a
> fixed enumeration. Its two endpoint contacts and their corresponding left-path parameters determine a Jordan pocket
> by Aux. lemma 33. The choice is measurable from the two incoming paths."

and Theorem R.7 (`source/spec/p433-480.md` L1058–L1064, p. 477): "If neither side is outer, at least one is extremal
and the same claims are already the contained reference of Aux. 131."

The landed change pocket `changePocket R L r` of two simple proper walls with increasing contact order is the Jordan
pocket of the noncontact interval of `L` containing a parameter `r` off `R` (the noncontact interval may be taken on
either path: if every point of `L` lay on `R`, the two simple arcs from `0` to `∞` would have equal ranges). Here:

* **`exists_aux131Event`**: a positive rational `q` and a walls' event `G` (up to null sets) of positive probability
  on which `L(q) ∉ R` and the pocket has the configuration `IsChangeConfigInc` (from the walls' reverse visit order);
  the only geometric input is that `L` is not contained in `R` (almost surely `∃ t, L t ∉ range R`);
* **`r7PocketStopStatement_of_aux131Strip`**: `R7PocketStopStatement κ r_L r_R GoodR7` from the pathwise strip inputs
  (walls simple, proper and reverse-contained in the counterflow, `R` entirely visited, distinct ranges, the
  flow-line order `R ∩ leftSide(L) = ∅`, the counterflow's trace, Aux. lemma 37's attachments), the two-seed walls
  inputs, a standard Borel record of the walls and Proposition 5.13; `…_comap`: with the walls' σ-algebra of a
  standard Borel record;
* `Aux131StripInput κ r_L r_R` (**named input**: the strip pocket of Aux. lemma 131 with exactly these hypotheses) and
  **`r7PocketStopStatement_of_aux131StripInput`**;
* **`r7ReferenceStatement_of_aux131_outer`**: Theorem R.7's `hR7` (`R7.R7ReferenceStatement`) from Aux. lemma 131's
  strip input on the extremal pairs `max(r_L, r_R) = κ/2 − 4` and the outer pockets (`R7PocketStopStatement`,
  PROVE-R7-OUTER's part) on the pairs `max(r_L, r_R) > κ/2 − 4`; `aux131_angles_of_max_eq`: on the extremal pairs the
  angles of (CS13.3) satisfy `−π/2 ≤ θ_R < θ_L ≤ π/2` with one of them extremal (R.7's first paragraph).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses; no `h44`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H Hbar)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R7Aux131

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin StripPocketConfig PocketLeftFrontier R7Pocket

universe u

/-! ### The rational noncontact parameter -/

section Select

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A point of `L` off the closed range of `R` is approximated by a positive rational parameter off `R`**
(deterministic): the set of parameters off a closed set is open. -/
theorem exists_rat_notMem_range {R L : ℝ≥0 → ℂ} (hR : IsSimpleProper R) (hL : Continuous L)
    {t : ℝ≥0} (ht : L t ∉ range R) : ∃ q : ℚ, 0 < q ∧ L (StripSys.rt q) ∉ range R := by
  have hcl : IsClosed (range R) := Lemma71Pin.IsSimpleProper.isClosed_range hR
  have hopen : IsOpen (L ⁻¹' (range R)ᶜ) := hcl.isOpen_compl.preimage hL
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen t ht
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < t + δ by linarith)
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt t.coe_nonneg hq1
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  refine ⟨q, hq0', hball ?_⟩
  rw [Metric.mem_ball, NNReal.dist_eq, StripSys.coe_rt hq0'.le, abs_lt]
  constructor <;> linarith

/-- **Aux. lemma 131's rational noncontact parameter and the pocket's configuration event** (p. 415). Let `R` (right)
and `L` (left) be random walls, measurable at fixed times for the walls' σ-algebra `𝓦`, and `η` a counterflow from `0`,
continuous on `[0, ∞)`. Assume, almost surely: the walls are simple proper curves visited in reverse order by the
counterflow (Lemma 5.7), `R` entirely visited, and `L` is not contained in `R`. Then for any family `Q q` of almost
sure properties there are a rational `q > 0` and an event `G`, measurable from the walls up to null sets, of positive
probability, on which `L(q) ∉ R`, the pocket of `R` and `L` at `q` has the configuration `IsChangeConfigInc`, the walls'
reverse visit facts hold and `Q q` holds. -/
theorem exists_aux131Event [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hL : ∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω))
    (hnc : ∀ᵐ ω ∂P, ∃ t, L ω t ∉ range (R ω))
    {Q : ℚ → Ω → Prop} (hQ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Q q ω) :
    ∃ q : ℚ, 0 < q ∧ ∃ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G ∧ 0 < P G ∧
      ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) ∧ IsWallReverseVisit (R ω) (η ω) ∧
        IsWallReverseVisit (L ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧ Q q ω := by
  classical
  have hQall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → Q q ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · filter_upwards [hQ q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  obtain ⟨G₀, hG₀m, hG₀ae, hG₀⟩ := exists_measurableSet_nullSets_ae (P := P) (hR.and (hL.and (hnc.and hQall)))
  set m := 𝓦 ⊔ Ito.nullSets P with hm
  have hG₀m' : MeasurableSet[m] G₀ := le_sup_right (a := 𝓦) _ hG₀m
  -- the events `F q`: `L(q)` off the closed range of `R`
  set F : ℚ → Set Ω := fun q => G₀ ∩ {ω | L ω (StripSys.rt q) ∉ closure (range (R ω))} with hFdef
  have hFm : ∀ q, MeasurableSet[m] (F q) := fun q =>
    StripSys.measurableSet_inter_notMem_closure_range (mΩ := m) hG₀m' (fun ω hω => (hG₀ ω hω).1.1.1)
      (fun q' => (hRm _).mono le_sup_left le_rfl) ((hLm _).mono le_sup_left le_rfl)
  have hcover : ∀ ω ∈ G₀, ∃ q : ℚ, 0 < q ∧ ω ∈ F q := by
    intro ω hω
    obtain ⟨hRω, hLω, ⟨t, ht⟩, -⟩ := hG₀ ω hω
    obtain ⟨q, hq, hqR⟩ := exists_rat_notMem_range hRω.1 hLω.1.1 ht
    refine ⟨q, hq, hω, ?_⟩
    show L ω (StripSys.rt q) ∉ closure (range (R ω))
    rwa [(Lemma71Pin.IsSimpleProper.isClosed_range hRω.1).closure_eq]
  -- some `F q` has positive probability
  have hpos : ∃ q : ℚ, 0 < q ∧ 0 < P (F q) := by
    by_contra hcon
    push Not at hcon
    have hnull : P (⋃ q : ℚ, ⋃ (_ : 0 < q), F q) = 0 :=
      measure_iUnion_null fun q => measure_iUnion_null fun hq => le_antisymm (hcon q hq) zero_le
    have hsub : G₀ ⊆ ⋃ q : ℚ, ⋃ (_ : 0 < q), F q := fun ω hω => by
      obtain ⟨q, hq, hωq⟩ := hcover ω hω
      exact mem_iUnion₂.2 ⟨q, hq, hωq⟩
    obtain ⟨ω, hω, hωn⟩ := (hG₀ae.and (measure_eq_zero_iff_ae_notMem.1 hnull)).exists
    exact hωn (hsub hω)
  obtain ⟨q, hq, hPq⟩ := hpos
  refine ⟨q, hq, F q, hFm q, hPq, fun ω hω => ?_⟩
  obtain ⟨hRω, hLω, -, hQω⟩ := hG₀ ω hω.1
  have hoff : L ω (StripSys.rt q) ∉ range (R ω) := fun h => hω.2 (subset_closure h)
  have hpos' : 0 < StripSys.rt q := Real.toNNReal_pos.2 (Rat.cast_pos.2 hq)
  exact ⟨isChangeConfigInc_of_reverseVisit hRω.1 hLω.1 (hηc ω) (hη0 ω) hRω.2.1 hLω.2 hRω.2.2 hpos' hoff,
    hRω.2.1, hLω.2, hRω.2.2, hQω q hq⟩

end Select

/-! ### The strip level -/

section Strip

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from Aux. lemma 131's strip pocket** (pp. 414–416): the right wall `R`
and the left wall `L` (the two constant-angle incoming paths), measurable at fixed times for the walls' σ-algebra `𝓦`,
and the counterflow `η` from `0` with driver `W`; almost surely: the walls are simple proper curves reverse-contained in
the counterflow (Lemma 5.7), `R` entirely visited, distinct ranges ("They cannot have identical ranges"), the
walls ordered (`R` misses the left side of `L`: "ordered by the already proved non-boundary constant-angle
monotonicity"), the counterflow a Loewner trace of a continuous driver from `0`, and Aux. lemma 37's attachment
constancy at each rational pocket (for the pocket opening at the flow seed also the counterflow's transience and the
visit of every point of `L`); the two-seed walls inputs on every configuration event (`hin`: the walls union law at
`T⁰(q)` and the two-seed side limits); Proposition 5.13; a standard Borel record `E₀` generating `𝓦` up to null sets. -/
theorem r7PocketStopStatement_of_aux131Strip [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hL : ∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω))
    (hne : ∀ᵐ ω ∂P, range (L ω) ≠ range (R ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))))
    (htrace : ∀ᵐ ω ∂P, IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0)
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      TwoSeedWallsInput κ rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u ∧
        TwoSeedWallsInputInf κ rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  have hnc : ∀ᵐ ω ∂P, ∃ t, L ω t ∉ range (R ω) := by
    filter_upwards [hR, hL, hne] with ω hRω hLω hneω using exists_notMem_range_of_range_ne hRω.1 hLω.1 hneω
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ := exists_aux131Event (𝓦 := 𝓦) (P := P) hRm hLm hηc hη0 hR hL hnc
    (Q := fun q ω => (IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0) ∧
      Disjoint (range (R ω)) (leftSideOf (range (L ω))) ∧
      (IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))) ∧
      (IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
          Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
            (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
            (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0))))
    (fun q hq => by
      filter_upwards [htrace, hord, hattach q hq, hattachI q hq] with ω h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩)
  have hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω hpos => by
    obtain ⟨hconf, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, hordω, hatt, -⟩ := hG ω hω
    exact ⟨hconf, hpos, hconf.isFlowChartOriented_of_leftFrontier hconf.left rfl hordω, htr, hWc, hW0, hrevR,
      hrevL, hvisR, hatt hconf hpos⟩
  have hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω h0 => by
    obtain ⟨hconf, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, hordω, -, hattI⟩ := hG ω hω
    obtain ⟨htrans, hvisL, hatt⟩ := hattI hconf h0
    exact ⟨hconf, h0, hconf.isFlowChartOriented_of_leftFrontier hconf.left rfl hordω, htr, hWc, hW0, htrans,
      hrevR, hrevL, hvisR, hvisL, hatt⟩
  obtain ⟨hin1, hin2⟩ := hin q hq G hGm hPG fun ω hω => (hG ω hω).1
  exact r7PocketStop_of_changeConfig (𝓦 := 𝓦 ⊔ Ito.nullSets P) (sup_le h𝓦 (Ito.nullSets_le P))
    (fun t => (hRm t).mono le_sup_left le_rfl) (fun t => (hLm t).mono le_sup_left le_rfl) hGm hPG
    (fun ω hω => (hG ω hω).1) hcfg hcfgI hηc hηm hh₀ hu hub hin1 hin2 (hE₀.mono le_sup_left le_rfl)
    (sup_le hgen le_sup_right) h513

/-- **Aux. lemma 131's strip pocket with the walls' σ-algebra of a standard Borel walls record** `E_w` (the record
hypotheses of `r7PocketStopStatement_of_aux131Strip` then hold trivially). -/
theorem r7PocketStopStatement_of_aux131Strip_comap [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀]
    {Ew : Ω → ε₀} (hEw : Measurable Ew) {R L : Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[MeasurableSpace.comap Ew inferInstance] fun ω => R ω t)
    (hLm : ∀ t, Measurable[MeasurableSpace.comap Ew inferInstance] fun ω => L ω t)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hL : ∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω))
    (hne : ∀ᵐ ω ∂P, range (L ω) ≠ range (R ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))))
    (htrace : ∀ᵐ ω ∂P, IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0)
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[MeasurableSpace.comap Ew inferInstance ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      TwoSeedWallsInput κ rL rR (MeasurableSpace.comap Ew inferInstance ⊔ Ito.nullSets P) P R L (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u ∧
        TwoSeedWallsInputInf κ rL rR (MeasurableSpace.comap Ew inferInstance ⊔ Ito.nullSets P) P R L
          (StripSys.rt q) W η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 :=
  r7PocketStopStatement_of_aux131Strip (𝓦 := MeasurableSpace.comap Ew inferInstance) hEw.comap_le hRm hLm hηm hηc
    hη0 hR hL hne hord htrace hattach hattachI hh₀ hu hub hin h513 (comap_measurable Ew) le_sup_left

end Strip

/-! ### The named input and Theorem R.7's extremal case -/

/-- **Named input: Aux. lemma 131's strip pocket** (the exact hypotheses of `r7PocketStopStatement_of_aux131Strip_comap`
for the two-seed word `(r_L; r_R)`): on a standard Borel probability space, a standard Borel walls record `E_w`, the two
constant-angle incoming paths `R` (angle `θ_R = R7.thetaR κ r_L`) and `L` (angle `θ_L = R7.thetaL κ r_R`) of (CS13.3),
measurable for the record, and the counterflow `η` with driver `W`, with the pathwise strip facts, the two-seed walls
inputs on every configuration event (the walls union law at `T⁰(q)` — `twoSeedWallsInput_of_sideLimit` discharges it
for flow-line walls of a frozen counterflow coupling — and the two-seed side limits, where the angles enter through the
walls' heights, Aux. lemmas 119–120), and Proposition 5.13. **Not proved in Lean**: the strip system does not yet
produce these data for the constant-angle walls. -/
def Aux131StripInput (κ rL rR : ℝ) : Prop :=
  ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (ε₀ : Type u) (_ : MeasurableSpace ε₀) (_ : StandardBorelSpace ε₀) (Ew : Ω → ε₀) (R L : Ω → ℝ≥0 → ℂ)
    (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ),
    Measurable Ew ∧ (∀ t, Measurable[MeasurableSpace.comap Ew inferInstance] fun ω => R ω t) ∧
    (∀ t, Measurable[MeasurableSpace.comap Ew inferInstance] fun ω => L ω t) ∧
    (∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t) ∧ (∀ ω, ContinuousOn (η ω) (Ici 0)) ∧ (∀ ω, η ω 0 = 0) ∧
    (∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω)) ∧
    (∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω)) ∧
    (∀ᵐ ω ∂P, range (L ω) ≠ range (R ω)) ∧
    (∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω)))) ∧
    (∀ᵐ ω ∂P, IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0) ∧
    (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))) ∧
    (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0))) ∧
    IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P ∧ InnerProductSpace.HarmonicOnNhd u H ∧
    (∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) ∧
    (∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[MeasurableSpace.comap Ew inferInstance ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      TwoSeedWallsInput κ rL rR (MeasurableSpace.comap Ew inferInstance ⊔ Ito.nullSets P) P R L (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u ∧
        TwoSeedWallsInputInf κ rL rR (MeasurableSpace.comap Ew inferInstance ⊔ Ito.nullSets P) P R L
          (StripSys.rt q) W η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u) ∧
    (∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from Aux. lemma 131's strip input.** -/
theorem r7PocketStopStatement_of_aux131StripInput {κ rL rR : ℝ} (h : Aux131StripInput.{u} κ rL rR) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  obtain ⟨Ω, _, hSB, P, hP, ε₀, mε₀, hSBε₀, Ew, R, L, W, η, h₀, u, hEw, hRm, hLm, hηm, hηc, hη0, hR, hL, hne, hord,
    htrace, hattach, hattachI, hh₀, hu, hub, hin, h513⟩ := h
  exact r7PocketStopStatement_of_aux131Strip_comap hEw hRm hLm hηm hηc hη0 hR hL hne hord htrace hattach hattachI hh₀
    hu hub hin h513

/-- **R.7's first paragraph on the extremal pairs** (`max(r_L, r_R) = κ/2 − 4`): one weight equals `d = κ/2 − 4` and
the angles of (CS13.3) satisfy `−π/2 ≤ θ_R < θ_L ≤ π/2` (Aux. lemma 131's sector (CS13.1); `R7.cs131_of_not_outer`,
`R7.cs131_angles_of_not_outer`). -/
theorem aux131_angles_of_max_eq {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hmax : max rL rR = κ / 2 - 4) :
    (rL = κ / 2 - 4 ∨ rR = κ / 2 - 4) ∧ -(π / 2) ≤ R7.thetaR κ rL ∧ R7.thetaR κ rL < R7.thetaL κ rR ∧
      R7.thetaL κ rR ≤ π / 2 := by
  have hL' : rL ≤ κ / 2 - 4 := hmax ▸ le_max_left rL rR
  have hR' : rR ≤ κ / 2 - 4 := hmax ▸ le_max_right rL rR
  obtain ⟨h1, h2, h3, -⟩ := R7.cs131_angles_of_not_outer hκ hL hR hmax.ge hL' hR'
  exact ⟨(R7.cs131_of_not_outer hL hR hmax.ge hL' hR').1, h1, h2, h3⟩

/-- **Theorem R.7's reference `hR7` from Aux. lemma 131 on the extremal pairs and the outer pockets on the others**
(R.7, p. 477: "If neither side is outer, at least one is extremal and the same claims are already the contained
reference of Aux. 131"): Aux. lemma 131's strip input for every `κ > 4` and every pair `r_L, r_R > −2` with
`max(r_L, r_R) = κ/2 − 4`, and Theorem R.7's mixed/outer pocket (`R7PocketStopStatement`, PROVE-R7-OUTER's part) for
the pairs with `max(r_L, r_R) > κ/2 − 4`. -/
theorem r7ReferenceStatement_of_aux131_outer
    (h131 : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = κ / 2 - 4 →
      Aux131StripInput.{u} κ rL rR)
    (hout : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 < max rL rR →
      R7PocketStopStatement.{u} κ rL rR GoodR7) :
    R7.R7ReferenceStatement.{u} :=
  r7ReferenceStatement_of_r7PocketStop fun κ hκ rL rR hL hR hmax => by
    rcases hmax.lt_or_eq with hlt | heq
    · exact hout κ hκ rL rR hL hR hlt
    · exact r7PocketStopStatement_of_aux131StripInput (h131 κ hκ rL rR hL hR heq.symm)

end InteractingSLE.Sec7.R7Aux131
