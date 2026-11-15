/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSafeGerm
import InteractingSLE.Spec.Sec7.Aux37WallsConst

/-!
# The constant-angle strip system: Aux. lemma 37's wall inputs for the constant-angle walls

Packet PROVE-STRIPSYS-SAFE. Ports to `StripSafe.IsConstStripSystem` (same statements with the strip-system hypothesis
weakened, same proofs) of PROVE-AUX37-WALLS' `Aux37Walls` lemmas of `Aux37WallsConst.lean`, which read the strip
system's staged histories only at the constant-angle programs `constSpec θ`:

* `ae_trace_const`, `ae_ownTrace_const`: a version of `η_θ` is a simple transient generating trace;
* `exists_ae_const_eq_admDrv`, **`hdet_const`**: Lemma 6.2's determination input (from `h44`);
* `isFlowLine_const`, **`isEntranceHistoryLocal_const`**: Lemma 6.2's locality input;
* `ae_sideHeights_const`, **`ae_ownHeights_union_const`**: the side heights and (G1) for two constant-angle walls.

R48: no Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param`; `h44` (R74) is the walls'
determination input.
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory Set Metric Filter Topology Function Bornology
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open QuantumZipper (H Hbar chiC fwdHull logDerivFwd)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.StripSafe

open Lemma71I PocketCoord PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall StripSideHeightProb
  StripPocketPath LocalSets R7Aux131
open Aux37Walls (constDrv)
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (Port to `IsConstStripSystem`.)
**A version of `η_θ` is almost surely a simple transient generating trace of a driver of infinite lifetime.** -/
theorem ae_trace_const (hS : IsConstStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, IsRegularDriver (E (constSpec θ) 0 ω))
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θ) 0 ω).1 ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, (E (constSpec θ) 0 ω).2 = ⊤ ∧ IsGeneratingTrace (E (constSpec θ) 0 ω).1 ⊤ (γ ω) ∧
      Injective (γ ω) ∧ (∀ t, 0 < t → γ ω t ∈ H) ∧ Tendsto (γ ω) atTop (cobounded ℂ) := by
  obtain ⟨hL0, hR0⟩ := heights_const hS.kappa_pos hS.kappa_lt_four hcumL hcumR hθ
  filter_upwards [ae_simple_trace_const hS.kappa_pos hS.kappa_lt_four hS.boundaryData hS.gff
    (StripSafe.isStagedHistory_const hS hθ) hL0 hR0, StripSafe.ae_isSimpleProper_const hS hcumL hcumR hθ hreg hγc hγ0
    hγtr, hγtr] with ω h1 h2 h3
  exact ⟨h1.1, h3, h2.2.1, h2.2.2.2.1, tendsto_norm_atTop_iff_cobounded.1 h2.2.2.2.2⟩

/-- (Port to `IsConstStripSystem`.)
**The own trace of `η_θ`**: almost surely a version is the Loewner trace of its own continuous driver from `0`. -/
theorem ae_ownTrace_const (hS : IsConstStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, IsRegularDriver (E (constSpec θ) 0 ω))
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θ) 0 ω).1 ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (constDrv E θ ω) (Lemma71I.realPath (γ ω)) ∧ Continuous (constDrv E θ ω) ∧
      constDrv E θ ω 0 = 0 := by
  filter_upwards [StripSafe.ae_trace_const hS hcumL hcumR hθ hreg hγc hγ0 hγtr] with ω hω
  have hc := continuous_of_isRegularDriver (hreg ω) hω.1
  refine ⟨isLoewnerTrace_of_isGeneratingTrace hω.2.1, hc.comp continuous_real_toNNReal, ?_⟩
  show (E (constSpec θ) 0 ω).1 (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero]
  exact (hreg ω).2.1

/-- (Port to `IsConstStripSystem`.)
**The driver of `η_θ` is field-determined** (R48-safe; `StripPocketPath.exists_ae_leftExtremal_eq_admDrv` at a
general angle): almost surely its lifetime is infinite and it is `AdmCode.admDrv θ (c₀, h)`. -/
theorem exists_ae_const_eq_admDrv (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsConstStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    ∃ c₀ : Restart.BoundaryWord, ∀ᵐ ω ∂P, (E (constSpec θ) 0 ω).2 = ⊤ ∧
      (E (constSpec θ) 0 ω).1 = (AdmCode.admDrv h44 hS.kappa_pos hS.kappa_lt_four θ (c₀, h ω)).1 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  obtain ⟨hL0, hR0⟩ := heights_const hκ hκ4 hcumL hcumR hθ
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have h44c : Sec4.Cond44 κ (flowLineRhoL κ c₀.fn c₀.jumps 0 θ) (flowLineRhoR κ c₀.fn c₀.jumps 0 θ) := by
    refine StripDet.cond44_flowLine_of_heights hκ c₀.isPiecewiseConstantBoundaryData θ
      (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hL0 y hy hyJ
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hR0 y hy hyJ
  have hEd := (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
    (fun y hy => hc₀ y hy)).2 (isFlowLineDriver_const hκ hb hS.gff (StripSafe.isStagedHistory_const hS hθ))
  refine ⟨c₀, ?_⟩
  filter_upwards [AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 θ c₀ h44c hEd] with ω h2
  refine ⟨h2.1, funext fun t => ?_⟩
  exact (h2.2.2 t (by rw [h2.1]; exact ENNReal.coe_lt_top)).symm

/-- (Port to `IsConstStripSystem`.)
**Lemma 6.2's determination input for `η_θ`**: every version is, at every time, almost surely a Borel function of
the centred field `h − u₀` (as `StripPocketPath.hdet_leftExtremal`). -/
theorem hdet_const (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsConstStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, IsRegularDriver (E (constSpec θ) 0 ω)) (u₀ : ℂ → ℝ)
    {γ : Ω → ℝ≥0 → ℂ} (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θ) 0 ω).1 ⊤ (γ ω)) :
    ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := by
  obtain ⟨c₀, hD⟩ := StripSafe.exists_ae_const_eq_admDrv h44 hS hcumL hcumR hθ
  intro t
  set c : DistOn upperHalfPlaneOpens :=
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hc
  have hadd : Measurable fun g : DistOn upperHalfPlaneOpens => g + c := Coupling.measurable_add_distOnConst c
  refine ⟨fun g => LP.traceAt t (AdmCode.admDrv h44 hS.kappa_pos hS.kappa_lt_four θ (c₀, g + c)).1, ?_, ?_⟩
  · exact (LP.measurable_traceAt t).comp (measurable_fst.comp
      ((AdmCode.measurable_admDrv h44 hS.kappa_pos hS.kappa_lt_four θ).comp (measurable_const.prodMk hadd)))
  · filter_upwards [hD, hγtr] with ω hω hη
    have hcent : WholeField.centredField h u₀ ω + c = h ω := by
      simp only [WholeField.centredField, hc, sub_add_cancel]
    simp only [hcent, ← hω.2]
    have hcc := continuous_of_isRegularDriver (hreg ω) hω.1
    exact (LP.traceAt_eq_of_isGeneratingTrace hη hcc.continuousOn (hreg ω).2.1 ENNReal.coe_lt_top).symm

/-- (Port to `IsConstStripSystem`.)
A version of `η_θ` is a flow line of `h` of angle `θ` from `0`, with the driver's lifetime. -/
theorem isFlowLine_const (hS : IsConstStripSystem κ b jumps P h W' ζ' E) {θ : ℝ}
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {γ : Ω → ℝ≥0 → ℂ}
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θ) 0 ω).1 (E (constSpec θ) 0 ω).2 (γ ω)) :
    IsFlowLine κ b jumps 0 θ P h γ (fun ω => (E (constSpec θ) 0 ω).2) :=
  isFlowLine_of_isFlowLineDriver (isFlowLineDriver_const hS.kappa_pos hS.boundaryData hS.gff
    (StripSafe.isStagedHistory_const hS hθ)) hγtr

/-- (Port to `IsConstStripSystem`.)
**Lemma 6.2's locality input for `η_θ`**: every version is entrance-history local for the centred field (each
frozen prefix of the flow line, then the complete path by increasing prefixes). -/
theorem isEntranceHistoryLocal_const (hS : IsConstStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, IsRegularDriver (E (constSpec θ) 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θ) 0 ω).1 ⊤ (γ ω)) :
    Sec6.IsEntranceHistoryLocal γ (WholeField.centredField h u₀) P := by
  have htr := StripSafe.ae_trace_const hS hcumL hcumR hθ hreg hγc hγ0 hγtr
  have hfl : IsFlowLine κ b jumps 0 θ P h γ (fun ω => (E (constSpec θ) 0 ω).2) := by
    refine StripSafe.isFlowLine_const hS hθ ?_
    filter_upwards [htr] with ω hω
    rw [hω.1]
    exact hω.2.1
  have hζ : ∀ᵐ ω ∂P, (E (constSpec θ) 0 ω).2 = ⊤ := htr.mono fun ω hω => hω.1
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hS.gff.1 u₀
  have h0H : (0 : ℂ) ∉ H := fun h0' => by
    have h' : (0 : ℝ) < (0 : ℂ).im := h0'
    simp at h'
  refine Lemma71G.isEntranceHistoryLocal_of_capAt hhm hγc hγm (fun ω => by rw [hγ0 ω]; exact h0H) fun n => ?_
  exact Restart.StagedEntrance.isEntranceHistoryLocal_frozenPath_of_isFlowLine hS.kappa_pos hS.kappa_lt_four
    hS.boundaryData hS.gff hfl hζ hu₀ hγc hγm (n : ℝ≥0) (Eventually.of_forall fun ω t _ => rfl)


/-- (Port to `IsConstStripSystem`.)
**The side heights of `η_θ` at rational stops**: almost surely, every wall point `γ(s)`, `s ≠ 0`, off the range of
`ρ` (any path from `0`) has a rational stop `q > s` at which every harmonic representative `v` of the mean `g q` of the
stopped range has the side heights `±λ − θχ` at `γ(s)`, read with the wall's own driver. -/
theorem ae_sideHeights_const (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsConstStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, IsRegularDriver (E (constSpec θ) 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θ) 0 ω).1 ⊤ (γ ω))
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (g q))
    {ρ : Ω → ℝ≥0 → ℂ} (hρ0 : ∀ ω, ρ ω 0 = 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, γ ω s ∉ range (ρ ω) → s ∉ ({0} : Set ℝ≥0) → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          g q ω φ = ∫ z, v z * φ z) →
        StripGeom.HasSideHeights κ θ (γ ω) 0 (E (constSpec θ) 0 ω).1 q (γ ω s) v u₀ := by
  have htr := StripSafe.ae_trace_const hS hcumL hcumR hθ hreg hγc hγ0 hγtr
  have hfl : IsFlowLine κ b jumps 0 θ P h γ (fun ω => (E (constSpec θ) 0 ω).2) := by
    refine StripSafe.isFlowLine_const hS hθ ?_
    filter_upwards [htr] with ω hω
    rw [hω.1]
    exact hω.2.1
  have htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (E (constSpec θ) 0 ω).1 t) ((E (constSpec θ) 0 ω).2)
      (fun t => γ ω t - ((0 : ℝ) : ℂ)) := by
    filter_upwards [htr] with ω hω
    simp only [Complex.ofReal_zero, sub_zero]
    rw [hω.1]
    exact hω.2.1
  have hdet := StripSafe.hdet_const h44 hS hcumL hcumR hθ hreg u₀ hγtr
  have hloc := StripSafe.isEntranceHistoryLocal_const hS hcumL hcumR hθ hreg hu₀ hγc hγ0 hγm hγtr
  have hγH : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → γ ω s ∈ H := htr.mono fun ω hω => hω.2.2.2.1
  have hst1 : ∀ q : ℚ≥0, (0 : ℝ≥0) < (q : ℝ≥0) → ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, 0 < s → s < q → γ ω s ∈ H →
        StripGeom.HasSideHeights κ θ (γ ω) 0 (E (constSpec θ) 0 ω).1 q (γ ω s) v u₀ := by
    intro q _
    have key := Aux119Heights.ae_hasSideHeights_of_isFlowLine hS.kappa_pos hS.boundaryData hS.gff hfl
      (W := fun t ω => (E (constSpec θ) 0 ω).1 t) htr' hu₀ hγc hγ0 hγm hdet hloc (q : ℝ≥0)
      (Eventually.of_forall fun ω t _ _ => rfl) (hg q)
    filter_upwards [key, htr] with ω hk hω v hv hrep s _ hsq hsH
    exact hk (by rw [hω.1]; exact ENNReal.coe_lt_top) v hv hrep s hsq hsH
  have hst0 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ 0 → ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, s < q → γ ω s ∈ H →
        StripGeom.HasSideHeights κ θ (γ ω) 0 (E (constSpec θ) 0 ω).1 q (γ ω s) v u₀ := fun q hq =>
    Eventually.of_forall fun ω v _ _ s hs => absurd (hs.trans_le hq) (not_lt_zero (a := s))
  have key := Aux119Heights.ae_sideHeights_rat_of_stages (W := fun ω => (E (constSpec θ) 0 ω).1) (θ₀ := θ)
    (θ := θ) (t₀ := 0) hγ0 hρ0 hγH hst0 hst1
  filter_upwards [key] with ω hk s hs hs0
  obtain ⟨q, hsq, hq⟩ := hk s hs hs0
  refine ⟨q, hsq, fun v hv hrep => ?_⟩
  have := hq v hv hrep
  rwa [ite_self] at this

/-- (Port to `IsConstStripSystem`.)
**(G1) for two constant-angle walls and any local set `A`** (Aux. lemma 37's flow-side germ; the walls `Lw`, `Rw`
are versions of `η_{θL}`, `η_{θR}`): almost surely, for every harmonic representative `v` of the mean of
`A ∪ walls`, every flow chart of a change pocket on the left of `Rw`, every wall point off the other wall at positive
distance from `A` has an own time `q > s` with `v + u₀ + χ Im log f_q′ → λ − θLχ` on `Lw`, `→ −λ − θRχ` on `Rw`
along the pocket approach (`f_q` the wall's own map). -/
theorem ae_ownHeights_union_const (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsConstStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θL θR : ℝ} (hθL : θL ∈ Icc (-(π / 2)) (π / 2)) (hθR : θR ∈ Icc (-(π / 2)) (π / 2))
    (hregL : ∀ ω, IsRegularDriver (E (constSpec θL) 0 ω)) (hregR : ∀ ω, IsRegularDriver (E (constSpec θR) 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {Lw Rw : Ω → ℝ≥0 → ℂ} (hLc : ∀ ω, Continuous (Lw ω)) (hL0 : ∀ ω, Lw ω 0 = 0)
    (hLm : ∀ t, Measurable fun ω => Lw ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θL) 0 ω).1 ⊤ (Lw ω))
    (hRc : ∀ ω, Continuous (Rw ω)) (hR0 : ∀ ω, Rw ω 0 = 0) (hRm : ∀ t, Measurable fun ω => Rw ω t)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (constSpec θR) 0 ω).1 ⊤ (Rw ω))
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A (WholeField.centredField h u₀) P)
    {g gU : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ wallUnion Lw Rw ω) (WholeField.centredField h u₀) P g)
    (hgU : IsLocalSetMean (wallUnion Lw Rw) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Lw ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Rw ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gR q)) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A ω ∪ wallUnion Lw Rw ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ wallUnion Lw Rw ω) → g ω φ = ∫ z, v z * φ z) →
      ∀ (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (Rw ω) (Lw ω) r Ψ c →
      changePocket (Rw ω) (Lw ω) r ⊆ leftSideOf (range (Rw ω)) →
      (∀ s : ℝ≥0, Lw ω s ∉ range (Rw ω) → (∃ ε > 0, A ω ∩ ball (Lw ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (constDrv E θL ω) q z).im)
          (𝓝[changePocket (Rw ω) (Lw ω) r] (Lw ω s)) (𝓝 (sleLambda κ - θL * chiC κ))) ∧
      (∀ s : ℝ≥0, Rw ω s ∉ range (Lw ω) → (∃ ε > 0, A ω ∩ ball (Rw ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (constDrv E θR ω) q z).im)
          (𝓝[changePocket (Rw ω) (Lw ω) r] (Rw ω s)) (𝓝 (-sleLambda κ - θR * chiC κ))) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have htrL := StripSafe.ae_trace_const hS hcumL hcumR hθL hregL hLc hL0 hLtr
  have htrR := StripSafe.ae_trace_const hS hcumL hcumR hθR hregR hRc hR0 hRtr
  have hLim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Lw ω t).im := by
    filter_upwards [htrL] with ω hω t
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · rw [← ht, hL0 ω, Complex.zero_im]
    · exact (hω.2.2.2.1 t ht).le
  have hRim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Rw ω t).im := by
    filter_upwards [htrR] with ω hω t
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · rw [← ht, hR0 ω, Complex.zero_im]
    · exact (hω.2.2.2.1 t ht).le
  have htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ) := by
    filter_upwards [htrL, htrR] with ω h1 h2
    exact ⟨h1.2.2.2.2, h2.2.2.2.2⟩
  have hsideL := StripSafe.ae_sideHeights_const h44 hS hcumL hcumR hθL hregL hu₀ hLc hL0 hLm hLtr hgL hR0
  have hsideR := StripSafe.ae_sideHeights_const h44 hS hcumL hcumR hθR hregR hu₀ hRc hR0 hRm hRtr hgR hL0
  have key := ae_ownHeights_union hX hLc hL0 hLm (StripSafe.hdet_const h44 hS hcumL hcumR hθL hregL u₀ hLtr)
    (StripSafe.isEntranceHistoryLocal_const hS hcumL hcumR hθL hregL hu₀ hLc hL0 hLm hLtr) hLim hRc hR0 hRm
    (StripSafe.hdet_const h44 hS hcumL hcumR hθR hregR u₀ hRtr)
    (StripSafe.isEntranceHistoryLocal_const hS hcumL hcumR hθR hregR hu₀ hRc hR0 hRm hRtr) hRim htr hAm hAloc hg hgU
    hgL hgR (θL := fun _ => θL) (θR := fun _ => θR) (WL := fun ω => (E (constSpec θL) 0 ω).1)
    (WR := fun ω => (E (constSpec θR) 0 ω).1) hsideL hsideR
  filter_upwards [key, htrL, htrR] with ω hk hL hR v hv hrep r Ψ c hF hCl
  have hcL := continuous_of_isRegularDriver (hregL ω) hL.1
  have hcR := continuous_of_isRegularDriver (hregR ω) hR.1
  obtain ⟨k1, k2⟩ := hk v hv hrep r Ψ c hF hCl hL.2.1 hcL (hregL ω).2.1 hR.2.1 hcR (hregR ω).2.1
  refine ⟨fun s hs hA => k1 s hs (fun h0 => hs ⟨0, ?_⟩) hA, fun s hs hA => k2 s hs (fun h0 => hs ⟨0, ?_⟩) hA⟩
  · rw [mem_singleton_iff.1 h0, hL0, hR0]
  · rw [mem_singleton_iff.1 h0, hL0, hR0]

end InteractingSLE.Sec7.StripSafe
