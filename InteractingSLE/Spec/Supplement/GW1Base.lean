/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1

/-!
# The base of GW1's induction: the first piece of a staged history is the flow line of `h`

Packet PROVE-T14-GW. GW1's induction (`source/spec/p577-624.md` L931–L947, p. 618: "The initial datum is the given
complete counterflow pair targeted at `x`, with the singleton incoming set `A₀ = {x}` … Launch the canonical
lower-extreme flow `β_j` of the conditional field") starts with the first ordinary piece, launched from the root in
the original field. For the frozen staged histories (`IsStagedHistory`), the first piece is described only under the
conditional law given the (trivial) past, with some boundary data `b'` read in the root chart. This file identifies it
with the angle-`θ` flow line of the original field `h` with its original data `b` (`IsFlowLineDriver κ b jumps θ P h`),
the form in which GB6 (`Supp8.GB6.GB6FirstContactStatement`) and every other original-field result apply to it.

* `launches_run_one_of_cons`: a program starting with an ordinary piece launches it from the root chart.
* `lims_eq_of_eq_off_finset`, `jumpSet_eq_of_eq_off`, `isFlowLineDriver_congr`: the flow-line force word depends on the
  boundary data only through its one-sided limits and genuine jumps, which do not see a finite set.
* **`IsStagedHistory.isFlowLineDriver_first`**: the first piece is the angle-`θ` flow line of `h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open LQGMetric (TestOn DistOn)

/-! ### The first launch of a program -/

/-- **A program starting with an ordinary piece launches it from the root**, in the root chart. -/
theorem launches_run_one_of_cons (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {θ : ℝ} {t : ℝ≥0∞}
    {rest : List Instr} (hp : spec.2.2 = Sum.inl (θ, t) :: rest) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps spec D (0 + 1)).2.2.2.1 0 = some (Chart.id.recenter spec.1, θ) := by
  obtain ⟨x, gw2, p⟩ := spec
  simp only at hp
  subst hp
  unfold ExplState.run
  simp only [List.zipIdx_cons, zero_add, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  show (ExplState.launch (ExplState.init x) 0 (D 0) θ t).2.2.2.1 0 = _
  rw [Exist.Staged.launches_launch, Function.update_self]
  rfl

/-! ### The flow-line word sees only one-sided limits and genuine jumps -/

/-- Functions that agree off a finite set have the same one-sided limits everywhere. -/
theorem lims_eq_of_eq_off_finset {f g : ℝ → ℝ} (S : Finset ℝ) (hfg : ∀ y, y ∉ S → f y = g y) (x : ℝ) :
    leftLim f x = leftLim g x ∧ rightLim f x = rightLim g x := by
  have ho : IsOpen ((((S.erase x : Finset ℝ) : Set ℝ))ᶜ) := (S.erase x).finite_toSet.isClosed.isOpen_compl
  have hx : x ∈ (((S.erase x : Finset ℝ) : Set ℝ))ᶜ := by simp
  have he : f =ᶠ[𝓝[≠] x] g := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hx), self_mem_nhdsWithin] with y hy hyx
    exact hfg y fun hyS => hy (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hyx, hyS⟩))
  have hL : Filter.map f (𝓝[<] x) = Filter.map g (𝓝[<] x) :=
    Filter.map_congr (he.filter_mono (nhdsWithin_mono _ fun y hy => ne_of_lt hy))
  have hR : Filter.map f (𝓝[>] x) = Filter.map g (𝓝[>] x) :=
    Filter.map_congr (he.filter_mono (nhdsWithin_mono _ fun y hy => ne_of_gt hy))
  exact ⟨congrArg lim hL, congrArg lim hR⟩

/-- Off its jump candidates, piecewise-constant data have equal one-sided limits. -/
theorem leftLim_eq_rightLim_of_notMem {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {y : ℝ} (hy : y ∉ J) : leftLim b y = rightLim b y := by
  have hc := hb y hy
  have h1 : Tendsto b (𝓝[<] y) (𝓝 (b y)) :=
    tendsto_const_nhds.congr' ((hc.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm)
  have h2 : Tendsto b (𝓝[>] y) (𝓝 (b y)) :=
    tendsto_const_nhds.congr' ((hc.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm)
  show limUnder (𝓝[<] y) b = limUnder (𝓝[>] y) b
  rw [h1.limUnder_eq, h2.limUnder_eq]

/-- **Data with the same one-sided limits have the same genuine jumps.** -/
theorem jumpSet_eq_of_lims {b b' : ℝ → ℝ} {J J' : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hL : leftLim b = leftLim b') (hR : rightLim b = rightLim b') :
    jumpSet b J = jumpSet b' J' := by
  ext y
  simp only [PiecewiseConstantBoundaryData.jumpSet, Finset.mem_filter]
  rw [hL, hR]
  constructor
  · rintro ⟨-, hne⟩
    by_contra hy
    exact hne (leftLim_eq_rightLim_of_notMem hb' fun hy' => hy ⟨hy', hne⟩)
  · rintro ⟨-, hne⟩
    by_contra hy
    rw [← hL, ← hR] at hne
    exact hne (leftLim_eq_rightLim_of_notMem hb fun hy' => hy ⟨hy', by rwa [← hL, ← hR]⟩)

/-- **The flow-line driver predicate depends on the data only through its one-sided limits and genuine jumps.** -/
theorem isFlowLineDriver_congr {κ θ : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ} (hS : jumpSet b J = jumpSet b' J')
    (hL : leftLim b = leftLim b') (hR : rightLim b = rightLim b') {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (H : IsFlowLineDriver κ b J θ P h W ζ) : IsFlowLineDriver κ b' J' θ P h W ζ := by
  have key : ∀ {S S' : Finset ℝ} {L L' R R' : ℝ → ℝ}, S = S' → L = L' → R = R' →
      ∀ Q : Finset ℝ → (ℝ → ℝ) → (ℝ → ℝ) → Prop, Q S L R → Q S' L' R' := by
    intro S S' L L' R R' e1 e2 e3 Q hQ
    subst e1 e2 e3
    exact hQ
  let Q : Finset ℝ → (ℝ → ℝ) → (ℝ → ℝ) → Prop := fun S L R => ∃ (h' : Ω → DistOn upperHalfPlaneOpens)
      (F : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›)
      (VL : Fin ((S.filter (· < 0)).card + 1) → ℝ≥0 → Ω → ℝ)
      (VR : Fin ((S.filter (0 < ·)).card + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      (∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
      IsOptionalHullCoupling κ
        (Fin.cons 0 fun i => (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i) - 0)
        (Fin.cons 0 fun i => (S.filter (0 < ·)).orderEmbOfFin rfl i - 0)
        (Fin.cons (-(L 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) fun i =>
          let y := (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i)
          (R y - L y) / sleLambda κ)
        (Fin.cons ((R 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) fun i =>
          let y := (S.filter (0 < ·)).orderEmbOfFin rfl i
          (R y - L y) / sleLambda κ)
        P F W VL VR B ζ h'
  exact key hS hL hR Q H

/-! ### The first piece -/

/-- **The first piece of a staged history from the root `0` is the angle-`θ` flow line of `h`** with the original
data `b` (GW1's initial datum; "launch the same angle in the current unbounded conditional domain" at the root: the
past is trivial, the chart is the identity, and the conditional data are `b` off a finite set). -/
theorem _root_.InteractingSLE.IsStagedHistory.isFlowLineDriver_first {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0) {θ : ℝ} {t : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    IsFlowLineDriver κ b jumps θ P h (fun t ω => (E 0 ω).1 t) (fun ω => (E 0 ω).2) := by
  obtain ⟨ω₀, hω₀⟩ := (hS.2.2.2 0).exists
  have hl := launches_run_one_of_cons κ b jumps spec hp (fun j => E j ω₀)
  rw [hroot] at hl
  obtain ⟨b', jumps', h', hb', hT, hF⟩ := hω₀ _ _ hl
  rw [pastSigma_zero_eq_bot, condExpKernel_bot_apply] at hF
  -- the conditional field is `h` itself
  have hhh : h' = h := by
    funext ω
    refine DFunLike.ext _ _ fun φ => ?_
    have := hT ω φ φ (by
      intro z hz
      refine ⟨z, ?_, by simp [Chart.recenter, Chart.id]⟩
      exact φ.tsupport_subset hz) (by
      intro z _
      simp [Chart.recenter, Chart.id])
    simpa [Chart.recenter, Chart.id] using this
  subst hhh
  -- the conditional data are the original data off a finite set
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hF
  have hshift : ∀ ω φ, h'' ω φ = h' ω φ + θ * QuantumZipper.chiC κ * ∫ z, φ z := fun ω φ =>
    htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
  have hoff := eq_off_of_isGFF hκ hb hb' θ hh hshift hC.2.2.1
  have hlims := lims_eq_of_eq_off_finset (insert 0 (Exist.flowExcept b' jumps' 0 ∪ jumps))
    (fun y hy => hoff y (fun h0 => hy (Finset.mem_insert.2 (Or.inl h0)))
      fun hm => hy (Finset.mem_insert_of_mem hm))
  have hL : leftLim b' = leftLim b := funext fun x => (hlims x).1
  have hR : rightLim b' = rightLim b := funext fun x => (hlims x).2
  exact isFlowLineDriver_congr (jumpSet_eq_of_lims hb' hb hL hR) hL hR ⟨h'', 𝓕, VL, VR, B, htr, hC⟩

/-! ### Corollary GW6 from GW2a alone -/

/-- **Corollary GW6 from Lemma GW2a** (GW1's threshold input is now proved, `gw1FirstThresholdStatement`). -/
theorem gw6Statement_of_gw2aContainment (hGW2a : GW2aContainmentStatement.{u}) : GW6Statement.{u} :=
  gw6Statement_of_gw2a hGW2a gw1FirstThresholdStatement

end GW1

end Theorem14

end InteractingSLE
