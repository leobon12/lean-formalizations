/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInMixed
import InteractingSLE.Spec.Sec7.R7OuterConfig
import InteractingSLE.Spec.Sec7.R7Aux131Select
import InteractingSLE.Spec.Sec7.Lemma613
import InteractingSLE.Spec.Supplement.GW3SidedProof
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# Theorem R.7's mixed and outer pockets: the selection event and the walls' configuration

Packet PROVE-R7-STOPIN. Supplement §5.1 and the proof of Theorem R.7 (`source/spec/p433-480.md` L956–L966,
L1058–L1063, pp. 471, 477):

> "In the constant-angle construction the arms are globally ordered and their common contacts have increasing order.
> A selected component `C` between consecutive common contacts has boundary the two open-disjoint arcs from `x_C` to
> `y_C` in flow order. This is an actual Jordan component, by Aux. 33, with all other portions of both arms outside it.
> The component is selected measurably from these intended incoming labels alone, for example by a first point in a
> fixed countable dense set." […] "Select an actual between-arm pocket by the first point of a fixed countable dense
> interior set that lies between them; retain its full intended incoming labels. This selection does not use the
> counterflow or an inner frontier pocket."

Results:

* `isChangeConfig_of_closedLeftSide`: two simple proper walls in global closed-side order and a parameter of the left
  wall off the right wall give the landed change-pocket configuration (`PocketCoord.IsChangeConfig`, hence increasing
  contact order);
* **`exists_r7StopInEvent`**: a positive rational parameter and an event, measurable from the walls (up to null sets),
  of positive probability, on which the selected pocket has this configuration — from the walls alone (no counterflow,
  no inner pocket);
* `exists_notMem_range_of_outerRight`, `…_outerLeft`: the walls of a mixed or outer pocket do not have equal ranges
  (an outer arm meeting the contained side only on the certified frontier would share an arc with it);
* `ae_pair_r7`: two incoming lines of Theorem R.7's field with angles `θ₁ < θ₂` are almost surely ordered and share no
  arc (Lemma 6.13, `Lemma613.ae_noCommonArc_of_maps`, with the Borel maps of `IsR7OuterConfig`);
* **`IsR7OuterConfig.ae_rightOuter`**, **`…ae_leftOuter`**, **`…ae_outerOuter`**: almost surely, the walls'
  configuration consumed by `R7StopInMixed` (simple proper walls and frontiers, `WangWu.IsOrderedArcs`, no common
  arcs, the outer containment, global order, distinct ranges) for each shape of Theorem R.7's mixed or outer pocket.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: the only named input is
`Lemma71H.Prop55HalfPlaneStatement` (Proposition 5.5 in `ℍ`, as in PROVE-R7-OUTER); nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R7StopIn

open WangWu Lemma71I PocketCoord PocketJordan R7Outer

universe u

/-! ### The selection -/

section Select

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Global closed-side order gives the change-pocket configuration** (§5.1: "the arms are globally ordered"). -/
theorem isChangeConfig_of_closedLeftSide {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (hR : IsSimpleProper R) (hL : IsSimpleProper L)
    (hord : range L ⊆ closedLeftSide R) (hr : 0 < r) (hoff : L r ∉ range R) : IsChangeConfig R L r :=
  ⟨hR, hL, disjoint_rightSideOf_of_subset_closedLeftSide hR.isProperCurve hR.2.2.1 hord, hr, hoff⟩

/-- **The selection event of a mixed or outer pocket** (§5.1, proof of Theorem R.7). Let `R` (right) and `L` (left) be
random walls, measurable at fixed times for the walls' σ-algebra `𝓦`. Assume, almost surely: both are simple proper
curves, `L` lies in the closed left side of `R`, and `L` is not contained in `R`. Then for any family `Q q` of almost
sure properties there are a rational `q > 0` and an event `G`, measurable from the walls up to null sets, of positive
probability, on which `L(q) ∉ R`, the pocket of `R` and `L` at `q` has the configuration `IsChangeConfig` and `Q q`
holds. The counterflow is not used. -/
theorem exists_r7StopInEvent [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hRL : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsSimpleProper (L ω) ∧ range (L ω) ⊆ closedLeftSide (R ω))
    (hnc : ∀ᵐ ω ∂P, ∃ t, L ω t ∉ range (R ω)) {Q : ℚ → Ω → Prop} (hQ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Q q ω) :
    ∃ q : ℚ, 0 < q ∧ ∃ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G ∧ 0 < P G ∧
      ∀ ω ∈ G, IsChangeConfig (R ω) (L ω) (StripSys.rt q) ∧ Q q ω := by
  classical
  have hQall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → Q q ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · filter_upwards [hQ q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  obtain ⟨G₀, hG₀m, hG₀ae, hG₀⟩ := StripPocketConfig.exists_measurableSet_nullSets_ae (P := P)
    (hRL.and (hnc.and hQall))
  set m := 𝓦 ⊔ Ito.nullSets P with hm
  have hG₀m' : MeasurableSet[m] G₀ := le_sup_right (a := 𝓦) _ hG₀m
  set F : ℚ → Set Ω := fun q => G₀ ∩ {ω | L ω (StripSys.rt q) ∉ closure (range (R ω))} with hFdef
  have hFm : ∀ q, MeasurableSet[m] (F q) := fun q =>
    StripSys.measurableSet_inter_notMem_closure_range (mΩ := m) hG₀m' (fun ω hω => (hG₀ ω hω).1.1.1)
      (fun q' => (hRm _).mono le_sup_left le_rfl) ((hLm _).mono le_sup_left le_rfl)
  have hcover : ∀ ω ∈ G₀, ∃ q : ℚ, 0 < q ∧ ω ∈ F q := by
    intro ω hω
    obtain ⟨⟨hRω, hLω, -⟩, ⟨t, ht⟩, -⟩ := hG₀ ω hω
    obtain ⟨q, hq, hqR⟩ := R7Aux131.exists_rat_notMem_range hRω hLω.1 ht
    refine ⟨q, hq, hω, ?_⟩
    show L ω (StripSys.rt q) ∉ closure (range (R ω))
    rwa [(Lemma71Pin.IsSimpleProper.isClosed_range hRω).closure_eq]
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
  obtain ⟨⟨hRω, hLω, hord⟩, -, hQω⟩ := hG₀ ω hω.1
  have hoff : L ω (StripSys.rt q) ∉ range (R ω) := fun h => hω.2 (subset_closure h)
  have hpos' : 0 < StripSys.rt q := Real.toNNReal_pos.2 (Rat.cast_pos.2 hq)
  exact ⟨isChangeConfig_of_closedLeftSide hRω hLω hord hpos' hoff, hQω q hq⟩

end Select

/-! ### Distinct ranges -/

section Distinct

variable {αR βR βL αL : ℝ≥0 → ℂ}

/-- **The walls of a pocket with an outer right arm have distinct ranges**: if `L ⊆ R` as ranges, the outer arm
`R ⊆ E_R ∪ β_R` would lie on the contained side's closed left side of `β_R`, hence on `β_R`, and `β_R` would share every
arc with `R`. -/
theorem exists_notMem_range_of_outerRight (hαR : IsSimpleProper αR) (hβR : IsSimpleProper βR)
    (hαL : IsSimpleProper αL) (houter : range αR ⊆ rightSideOf (range βR) ∪ range βR)
    (hLβ : range αL ⊆ closedLeftSide βR) (hnc : NoCommonArc βR αR) : ∃ t, αL t ∉ range αR := by
  by_contra hcon
  push Not at hcon
  have hsub : range αL ⊆ range αR := by rintro _ ⟨t, rfl⟩; exact hcon t
  have heq := R7Aux131.range_eq_of_range_subset hαR hαL hsub
  have hdisj := disjoint_rightSideOf_of_subset_closedLeftSide hβR.isProperCurve hβR.2.2.1 hLβ
  have hRβ : range αR ⊆ range βR := fun z hz => by
    rcases houter hz with h | h
    · exact absurd h (Set.disjoint_left.1 hdisj (heq ▸ hz))
    · exact h
  have heq' := R7Aux131.range_eq_of_range_subset hβR hαR hRβ
  obtain ⟨t, -, -, ht⟩ := hnc 1 2 one_pos one_lt_two
  exact ht (heq' ▸ ⟨t, rfl⟩)

/-- **The walls of a pocket with an outer left arm have distinct ranges** (the reflected argument with `β_L`). -/
theorem exists_notMem_range_of_outerLeft (hαR : IsSimpleProper αR) (hβL : IsSimpleProper βL)
    (hαL : IsSimpleProper αL) (houter : range αL ⊆ leftSideOf (range βL) ∪ range βL)
    (hβR : range βL ⊆ closedLeftSide αR) (hnc : NoCommonArc βL αL) : ∃ t, αL t ∉ range αR := by
  by_contra hcon
  push Not at hcon
  have hsub : range αL ⊆ range αR := by rintro _ ⟨t, rfl⟩; exact hcon t
  have heq := R7Aux131.range_eq_of_range_subset hαR hαL hsub
  have hRside := range_subset_rightSideOf_union hαR hβL hβR
  have hdisj := Theorem14.GW3SidedProof.disjoint_leftSideOf_rightSideOf_of_isSimpleProper hβL
  have hLβ : range αL ⊆ range βL := fun z hz => by
    rcases houter hz with h | h
    · rcases hRside (heq ▸ hz) with h' | h'
      · exact absurd h' (Set.disjoint_left.1 hdisj h)
      · exact h'
    · exact h
  have heq' := R7Aux131.range_eq_of_range_subset hβL hαL hLβ
  obtain ⟨t, -, -, ht⟩ := hnc 1 2 one_pos one_lt_two
  exact ht (heq' ▸ ⟨t, rfl⟩)

end Distinct

/-! ### The walls of Theorem R.7's field, almost surely -/

section Field

variable {k rL rR c c' : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Two incoming lines of Theorem R.7's field are ordered and share no arc** (non-boundary flow order, Proposition
5.5 in `ℍ`; Lemma 6.13's (MD1) exclusion), for angles `θ₁ < θ₂` of the R.7 range, each line a Borel function of the
field with infinite lifetime. -/
theorem ae_pair_r7 (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) (h₁ : θ₁ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR))
    (h₂ : θ₂ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR))
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ₂ P h η₂ ζ₂)
    {Φ₁ Φ₂ : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ} (hΦ₁ : Measurable Φ₁) (hΦ₂ : Measurable Φ₂)
    (he₁ : ∀ ω, η₁ ω = Φ₁ (h ω)) (he₂ : ∀ ω, η₂ ω = Φ₂ (h ω)) (hζ : ∀ᵐ ω ∂P, ζ₁ ω = ⊤ ∧ ζ₂ ω = ⊤) :
    ∀ᵐ ω ∂P, range (η₂ ω) ⊆ closedLeftSide (η₁ ω) ∧ NoCommonArc (η₁ ω) (η₂ ω) ∧ NoCommonArc (η₂ ω) (η₁ ω) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hb : sleLambda (16 / k) - θ₁ * chiC (16 / k) ≤ r7B k rL + c' := by
    have := mul_le_mul_of_nonneg_right h₁.1 hχ.le
    simp only [r7B]; linarith
  have ha : sleLambda (16 / k) - π * chiC (16 / k) + θ₂ * chiC (16 / k) ≤ r7A k rR + c := by
    have := mul_le_mul_of_nonneg_right h₂.2 hχ.le
    simp only [r7A]; linarith
  have hord := ae_order_r7 h55 hk4 hc hc' hθ h₁ h₂ hh hη₁ hη₂
  have hmap : ∀ {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {Φ : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ}, Measurable Φ →
      (∀ ω, η ω = Φ (h ω)) → (∀ᵐ ω ∂P, ζ ω = ⊤) → ∃ Ψ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ),
        Measurable Ψ ∧ ∀ᵐ ω ∂P, (Ψ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Ψ (h ω)).2 t = η ω t := by
    intro η ζ Φ hΦ he hζ'
    refine ⟨fun f => ((⊤ : ℝ≥0∞), Φ f), measurable_const.prodMk hΦ, ?_⟩
    filter_upwards [hζ'] with ω hω
    exact ⟨hω.symm, fun t _ => by rw [he ω]⟩
  have hnc := Lemma613.ae_noCommonArc_of_maps hκ hκ4 hθ hb ha hh hη₁ hη₂
    (hmap hΦ₁ he₁ (hζ.mono fun _ h => h.1)) (hmap hΦ₂ he₂ (hζ.mono fun _ h => h.2))
    (hord.mono fun _ h _ _ => h)
  filter_upwards [hord, hnc] with ω h1 h2
  exact ⟨h1, h2⟩

variable {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **The walls' configuration of a mixed pocket with an outer right arm, almost surely** (`θ_R < −π/2`, i.e.
`r_L > d`): the right wall `α_R`, the certified right frontier `β_R` and the left wall `α_L` are simple proper curves,
ordered (`WangWu.IsOrderedArcs α_R β_R α_L`) with no common arc of `β_R` with either wall, `α_R ⊂ E_R ∪ β_R`,
`α_L` is in the closed left side of `α_R`, and the walls have distinct ranges. -/
theorem _root_.InteractingSLE.Sec7.R7Outer.IsR7OuterConfig.ae_rightOuter
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hc : 0 ≤ c)
    (hc' : 0 ≤ c') (hθR : R7.thetaR k rL < -(π / 2)) :
    ∀ᵐ ω ∂P, IsSimpleProper (αR ω) ∧ IsSimpleProper (βR ω) ∧ IsSimpleProper (αL ω) ∧
      range (αL ω) ⊆ closedLeftSide (αR ω) ∧
      WangWu.IsOrderedArcs (Lemma71I.realPath (αR ω)) (Lemma71I.realPath (βR ω)) (Lemma71I.realPath (αL ω)) ∧
      NoCommonArc (βR ω) (αR ω) ∧ NoCommonArc (βR ω) (αL ω) ∧
      range (αR ω) ⊆ rightSideOf (range (βR ω)) ∪ range (βR ω) ∧ ∃ t, αL ω t ∉ range (αR ω) := by
  obtain ⟨ΦαR, ΦβR, _, ΦαL, hmαR, hmβR, _, hmαL, he⟩ := hcfg.borel
  have hp1 := ae_pair_r7 h55 hk4 hc hc' hθR (thetaR_mem_r7 rR hk4 hL) (neg_pi_div_two_mem_r7 k rL rR) hcfg.gff
    hcfg.flow_αR hcfg.flow_βR hmαR hmβR (fun ω => (he ω).1) (fun ω => (he ω).2.1)
    (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩)
  have hp2 := ae_pair_r7 h55 hk4 hc hc' (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
    (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL hmβR hmαL (fun ω => (he ω).2.1)
    (fun ω => (he ω).2.2.2) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
  filter_upwards [hcfg.regular, hcfg.order, hp1, hp2] with ω hreg hord h1 h2
  obtain ⟨hαR, hβR, -, hαL, -⟩ := hreg
  have hout := (hord.2.2.1 hθR).1
  exact ⟨hαR, hβR, hαL, hord.2.1, isOrderedArcs_of_closedLeftSide hαL hαR hβR h1.1 h2.1, h1.2.2, h2.2.1, hout,
    exists_notMem_range_of_outerRight hαR hβR hαL hout h2.1 h1.2.2⟩

/-- **The walls' configuration of a mixed pocket with an outer left arm, almost surely** (`θ_L > π/2`, i.e.
`r_R > d`): as `ae_rightOuter` with the certified left frontier `β_L` and `α_L ⊂ E_L ∪ β_L`. -/
theorem _root_.InteractingSLE.Sec7.R7Outer.IsR7OuterConfig.ae_leftOuter
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hc : 0 ≤ c)
    (hc' : 0 ≤ c') (hθL : π / 2 < R7.thetaL k rR) :
    ∀ᵐ ω ∂P, IsSimpleProper (αR ω) ∧ IsSimpleProper (βL ω) ∧ IsSimpleProper (αL ω) ∧
      range (αL ω) ⊆ closedLeftSide (αR ω) ∧
      WangWu.IsOrderedArcs (Lemma71I.realPath (αR ω)) (Lemma71I.realPath (βL ω)) (Lemma71I.realPath (αL ω)) ∧
      NoCommonArc (βL ω) (αR ω) ∧ NoCommonArc (βL ω) (αL ω) ∧
      range (αL ω) ⊆ leftSideOf (range (βL ω)) ∪ range (βL ω) ∧ ∃ t, αL ω t ∉ range (αR ω) := by
  obtain ⟨ΦαR, _, ΦβL, ΦαL, hmαR, _, hmβL, hmαL, he⟩ := hcfg.borel
  have hp1 := ae_pair_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
    (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL hmαR hmβL (fun ω => (he ω).1)
    (fun ω => (he ω).2.2.1) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
  have hp2 := ae_pair_r7 h55 hk4 hc hc' hθL (pi_div_two_mem_r7 k rL rR) (thetaL_mem_r7 rL hk4 hR) hcfg.gff
    hcfg.flow_βL hcfg.flow_αL hmβL hmαL (fun ω => (he ω).2.2.1) (fun ω => (he ω).2.2.2)
    (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
  filter_upwards [hcfg.regular, hcfg.order, hp1, hp2] with ω hreg hord h1 h2
  obtain ⟨hαR, -, hβL, hαL, -⟩ := hreg
  have hout := (hord.2.2.2.1 hθL).1
  exact ⟨hαR, hβL, hαL, hord.2.1, isOrderedArcs_of_closedLeftSide hαL hαR hβL h1.1 h2.1, h1.2.2, h2.2.1, hout,
    exists_notMem_range_of_outerLeft hαR hβL hαL hout h1.1 h2.2.1⟩

/-- **The walls' configuration of a pocket with two outer arms, almost surely** (`θ_R < −π/2 < π/2 < θ_L`): both
certified frontiers between the walls, ordered, with no common arc with either wall, and both outer containments. -/
theorem _root_.InteractingSLE.Sec7.R7Outer.IsR7OuterConfig.ae_outerOuter
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hc : 0 ≤ c)
    (hc' : 0 ≤ c') (hθR : R7.thetaR k rL < -(π / 2)) (hθL : π / 2 < R7.thetaL k rR) :
    ∀ᵐ ω ∂P, IsSimpleProper (αR ω) ∧ IsSimpleProper (βR ω) ∧ IsSimpleProper (βL ω) ∧ IsSimpleProper (αL ω) ∧
      range (αL ω) ⊆ closedLeftSide (αR ω) ∧
      WangWu.IsOrderedArcs (Lemma71I.realPath (αR ω)) (Lemma71I.realPath (βR ω)) (Lemma71I.realPath (αL ω)) ∧
      WangWu.IsOrderedArcs (Lemma71I.realPath (αR ω)) (Lemma71I.realPath (βL ω)) (Lemma71I.realPath (αL ω)) ∧
      NoCommonArc (βR ω) (αR ω) ∧ NoCommonArc (βR ω) (αL ω) ∧ NoCommonArc (βL ω) (αR ω) ∧
      NoCommonArc (βL ω) (αL ω) ∧ range (αR ω) ⊆ rightSideOf (range (βR ω)) ∪ range (βR ω) ∧
      range (αL ω) ⊆ leftSideOf (range (βL ω)) ∪ range (βL ω) ∧ ∃ t, αL ω t ∉ range (αR ω) := by
  have hr := hcfg.ae_rightOuter h55 hk4 hL hR hc hc' hθR
  have hl := hcfg.ae_leftOuter h55 hk4 hL hR hc hc' hθL
  filter_upwards [hr, hl] with ω h1 h2
  exact ⟨h1.1, h1.2.1, h2.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h2.2.2.2.2.1, h1.2.2.2.2.2.1,
    h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1,
    h1.2.2.2.2.2.2.2.2⟩

omit [IsProbabilityMeasure P] in
/-- **The counterflow of Theorem R.7's configuration in the pocket chart**: on its infinite-lifetime event, every
generating trace on `[0, ∞)`, read on `ℝ`, is a continuous Loewner trace of the extended driver, and its flow-chart
image avoids the exterior sides `E_R ∪ E_L` at every time. -/
theorem _root_.InteractingSLE.Sec7.R7Outer.IsR7OuterConfig.ae_counterflow_real
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ → ∀ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η' →
      IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (fun s : ℝ => η' s.toNNReal) ∧
      ∀ t : ℝ, 0 ≤ t → negInv (η' t.toNNReal) ∉ rightSideOf (range (βR ω)) ∪ leftSideOf (range (βL ω)) := by
  filter_upwards [hcfg.avoid] with ω hω hζ η' hη'
  exact ⟨InteractingSLE.isLoewnerTrace_of_isGeneratingTrace hη', fun t _ => hω hζ η' hη' t.toNNReal⟩

end Field

end InteractingSLE.Sec7.R7StopIn
