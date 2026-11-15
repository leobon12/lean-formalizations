/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketPathWalls

/-!
# Aux. lemma 131's walls: two constant-angle flow lines of the strip system, and distinct ranges

Packet PROVE-R7-AUX131. Specification §7.4.1, proof of Aux. lemma 131 (`source/spec/p385-432.md` L533–L537,
p. 415): "Choose large nonhit strip boundary data and the same centered non-boundary counterflow as above. Its two
constant-angle incoming paths are proper, continuous, simple, and reverse-contained in that counterflow. […] They
cannot have identical ranges […] A noncontact interval exists on the right path. Otherwise its completed range would be
contained in the left range. Parametrize both compactified simple arcs on `[0, 1]`. The inverse parametrization of the
left arc sends the connected right range to a connected subset of `[0, 1]` containing both endpoints, hence to all of
`[0, 1]`. Their ranges would be identical, which was just excluded."

* `isClosedEmbedding_of_isSimpleProper`; **`range_eq_of_range_subset`**: if the range of a simple proper path `L` is
  contained in that of a simple proper path `R`, the ranges are equal (the inverse parametrization `R⁻¹ ∘ L` is a
  continuous map of `[0, ∞)` from `0`, unbounded, hence onto); **`exists_notMem_range_of_range_ne`**: distinct ranges
  give a point of `L` off `R`;
* `StripSys` vocabulary for the constant-angle incoming path `η_θ` (the one-instruction program `constSpec θ`;
  `constSpec (π/2)` is `leftExtremalSpec`): `isBoundaryContinuedProgram_constSpec`, `isStagedHistory_const`;
* `isFlowLineDriver_const`, **`ae_simple_trace_const`**, **`ae_isSimpleProper_const`**: for every angle
  `θ ∈ [−π/2, π/2]`, the driver of `η_θ` is the angle-`θ` flow-line driver of the strip field, almost surely it has a
  simple transient trace, and every version of `η_θ` is almost surely a simple proper curve ("proper, continuous,
  simple"; the left-extremal results of `StripPocketPathWalls` at a general angle, with the (4.4) heights at `θ` from
  the strip heights).

Ruling R48: nothing here uses Theorem 1.2/1.3 or `h44`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R7Aux131

open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open Lemma71I StripPocketPath

/-! ### Distinct ranges -/

section Ranges

variable {R L : ℝ≥0 → ℂ}

/-- A simple proper path is a closed embedding of `[0, ∞)`. -/
theorem isClosedEmbedding_of_isSimpleProper (hR : IsSimpleProper R) : Topology.IsClosedEmbedding R := by
  have hprop : IsProperMap R := isProperMap_iff_tendsto_cocompact.2 ⟨hR.1, by
    rw [← Metric.cobounded_eq_cocompact (α := ℂ)]
    exact (tendsto_norm_atTop_iff_cobounded.1 hR.2.2.2.2).mono_left cocompact_le_atTop⟩
  exact .of_continuous_injective_isClosedMap hR.1 hR.2.1 hprop.isClosedMap

/-- **Two simple proper paths from `0` to `∞`: a range contained in the other is equal to it** (Aux. lemma 131's
proof, p. 415). The inverse parametrization `f = R⁻¹ ∘ L` is continuous (`R` is a closed embedding), `f 0 = 0`, and `f`
is unbounded (`L → ∞` while `R([0, s])` is bounded); by the intermediate value theorem it is onto. -/
theorem range_eq_of_range_subset (hR : IsSimpleProper R) (hL : IsSimpleProper L) (hsub : range L ⊆ range R) :
    range L = range R := by
  refine hsub.antisymm ?_
  have hE := isClosedEmbedding_of_isSimpleProper hR
  choose f hf using fun t => hsub ⟨t, rfl⟩
  have hRf : R ∘ f = L := funext hf
  have hfc : Continuous f := by
    rw [hE.isInducing.continuous_iff, hRf]
    exact hL.1
  have hf0 : f 0 = 0 := hR.2.1 (by rw [hf 0, hL.2.2.1, hR.2.2.1])
  rintro _ ⟨s, rfl⟩
  have hunb : ∃ T, s ≤ f T := by
    by_contra hcon
    push Not at hcon
    obtain ⟨M, hM⟩ := (isCompact_Icc.image hR.1 : IsCompact (R '' Icc 0 s)).isBounded.exists_norm_le
    obtain ⟨T, hT⟩ := (hL.2.2.2.2.eventually_gt_atTop M).exists
    exact absurd (hM _ ⟨f T, ⟨zero_le, (hcon T).le⟩, hf T⟩) (not_le.2 hT)
  obtain ⟨T, hT⟩ := hunb
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ T) hfc.continuousOn
    (show s ∈ Icc (f 0) (f T) from ⟨by rw [hf0]; exact zero_le, hT⟩)
  exact ⟨t, by rw [← hf t, ht]⟩

/-- **Distinct ranges give a point of `L` off `R`** ("A noncontact interval exists"). -/
theorem exists_notMem_range_of_range_ne (hR : IsSimpleProper R) (hL : IsSimpleProper L)
    (hne : range L ≠ range R) : ∃ t, L t ∉ range R := by
  by_contra h
  push Not at h
  exact hne (range_eq_of_range_subset hR hL (by rintro _ ⟨t, rfl⟩; exact h t))

end Ranges

/-! ### The constant-angle incoming paths of the strip system -/

/-- The constant-angle incoming path `η_θ` as a staged history from the common flow seed `x = 0`: the angle-`θ` flow
line through its available lifetime. -/
def constSpec (θ : ℝ) : ExplSpec :=
  (0, false, [Sum.inl (θ, ⊤)])

theorem constSpec_pi_div_two : constSpec (π / 2) = StripSys.leftExtremalSpec := rfl

theorem isBoundaryContinuedProgram_constSpec {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    IsBoundaryContinuedProgram (constSpec θ).2.2 := by
  intro θ' t' hmem
  simp only [constSpec, List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq, Prod.mk.injEq] at hmem
  rw [hmem.1]
  exact hθ

section Const

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The drivers of `η_θ` form a staged history of the strip field. -/
theorem isStagedHistory_const {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es) {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    IsStagedHistory κ b jumps P h (constSpec θ) (Es (constSpec θ)) :=
  hS.staged _ (isBoundaryContinuedProgram_constSpec hθ)

omit mΩ [StandardBorelSpace Ω] in
/-- The only instruction of `constSpec θ` launches the angle-`θ` piece from the root `0` in the identity chart. -/
theorem launches_run_one_constSpec (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (constSpec θ) D (0 + 1)).2.2.2.1 0 = some (Exist.shiftChart 0, θ) := by
  change (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤).2.2.2.1 0 = _
  rw [Exist.Staged.launches_launch, Function.update_self]
  rfl

/-- **The driver of `η_θ` is the angle-`θ` flow-line driver of `h`** with the data `b` (as
`isFlowLineDriver_leftExtremal`). -/
theorem isFlowLineDriver_const (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {θ : ℝ} (hE : IsStagedHistory κ b jumps P h (constSpec θ) E) :
    IsFlowLineDriver κ b jumps θ P h (fun t ω => (E 0 ω).1 t) (fun ω => (E 0 ω).2) := by
  obtain ⟨ω₀, hω₀⟩ := (hE.2.2.2 0).exists
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hω₀ _ _ (launches_run_one_constSpec θ _)
  rw [Theorem14.GW1.pastSigma_zero_eq_bot, Theorem14.GW1.condExpKernel_bot_apply] at hfl
  have hh' : h' = h := funext fun ω => by
    have h2 := Exist.StagedLaw.isChartTransport_shiftChart 0 (chiC κ) (h ω)
    rw [Prop74B.flowField_zero_zero] at h2
    exact IsChartTransport.unique (Exist.isConformal_shiftChart 0) (hT' ω) h2
  rw [hh'] at hfl
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have h1 := Exist.StagedLaw.isFlowLineDriver_word hκ hh₀ hb' hfl
  exact (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
    (fun y hy => hc₀ y hy)).1 h1

/-- **`η_θ` has a simple transient trace** (Remark 2.3 and Proposition 4.12 for its flow-line word, which satisfies
(4.4) by the heights of `b` at `θ`). -/
theorem ae_simple_trace_const (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {θ : ℝ} (hE : IsStagedHistory κ b jumps P h (constSpec θ) E)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + π * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) :
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η ∧ Injective η ∧
      (∀ t, 0 < t → η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := isFlowLineDriver_const hκ hb hh hE
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps 0
  have h44 := StripDet.cond44_flowLine_of_heights hκ hb θ hL0 hR0
  filter_upwards [Sec4.ae_simple_trace_of_cond44 hκ hκ4 hF h44 hC.1, Wire.prop412 hκ hκ4 hF h44 hC.1]
    with ω h1 h2
  obtain ⟨hζ, -, η, hη, hinj, hH, -⟩ := h1
  exact ⟨hζ, η, hη, hinj, hH, h2.2.2 η hη⟩

/-- The (4.4) heights at an angle `θ ∈ [−π/2, π/2]` from Aux. lemma 130's height choice. -/
theorem heights_const (hκ : 0 < κ) (hκ4 : κ < 4)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    (∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + π * chiC κ) ∧
      ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ := by
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => hcumR _ hθ y hy hyJ⟩
  have := hcumL _ hθ y hy hyJ
  linarith

/-- **Every version of the strip system's `η_θ` is almost surely a simple proper curve** (`θ ∈ [−π/2, π/2]`; Aux.
lemma 131: "Its two constant-angle incoming paths are proper, continuous, simple"). -/
theorem ae_isSimpleProper_const {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, Exist.Staged.IsRegularDriver (Es (constSpec θ) 0 ω))
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec θ) 0 ω).1 ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, IsSimpleProper (γ ω) := by
  obtain ⟨hL0, hR0⟩ := heights_const hS.kappa_pos hS.kappa_lt_four hcumL hcumR hθ
  exact ae_isSimpleProper_of_simple_trace hreg (ae_simple_trace_const hS.kappa_pos hS.kappa_lt_four hS.boundaryData
    hS.gff (isStagedHistory_const hS hθ) hL0 hR0) hγc hγ0 hγtr

end Const

end InteractingSLE.Sec7.R7Aux131
