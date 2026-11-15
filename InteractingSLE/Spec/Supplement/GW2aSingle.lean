/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Supplement.GW0
import InteractingSLE.Spec.Supplement.GW1Base
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Sec2.CriticalLifetime
import InteractingSLE.Spec.Sec7.StripSys

/-!
# Theorem 1.4: GW2a for a single ordinary piece from the original target

Packet PROVE-T14-GW2, item (2). Lemma GW2a (supplement p. 623, `source/spec/p577-624.md`): "Every finite such
history is simple, is contained in the counterflow range in reverse first-visit order". Its base case is one ordinary
piece launched at the original target `0` at an angle `θ ∈ [−π/2, π/2]` and run up to its stop `min t ζ` (an own time,
the target, or a finite continuation threshold). By `IsStagedHistory.isFlowLineDriver_first` (PROVE-T14-GW) this
piece is the angle-`θ` flow line of the original field `h` with the original data `b`, which is exactly the setting of
Proposition GB6 (supplement §8.6, pp. 518–520): "any complete simple constant-angle flow with angle in `[−π/2, π/2]` and
these own laws is contained in the ambient counterflow range".

The proof applies GB6's first-contact assertion (from its restart law, `Supp8.GB6.gb6FirstContactStatement_of_restart`)
at every rational own time with an interior tip, and closes up to the stop with the finite-horizon density argument
`CounterflowRange.mem_closure_of_dense_contacts` (GB6's final assertion is stated for complete flows only; a piece of a
history may end at a finite threshold). The stop itself is handled by the trace-closure fact through
`CounterflowRange.tipSet_stopped_eq`, with the driver continuous at a finite positive lifetime (Aux. lemma 3,
`IsIntegratedSLEEvolution.ae_tendsto_threshold`, and the recorded continuous limit of `IsStagedHistory`).

## Named inputs (all three are statements of the project, not proved here)

* `Supp8.GB6.GB6RestartStatement` — GB6's conditional-law half (PROVE-GB6C);
* `GW0.GW0ForwardStatement` — Lemma GW0's forward implication, which makes the counterflow word admissible
  (`GW0.counterflow_admissible`, GB6's `hadm`);
* `Exist.Theorem13Statement` — Theorem 1.3 (exactly the frozen anchor's type): the continuous generating trace of the
  flow line, and the complete transient trace of the counterflow (`16/κ > 4`, infinite lifetime).

## Main results

* **`ae_tipSet_first_subset`**: the first piece of any staged history from `0` lies in the completed counterflow range;
* **`ae_physSet_single_subset`**, **`gw2aContainment_single`**: GW2a for the programs `[flow θ t]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE
namespace Theorem14
namespace GW2aSingle

open CounterflowRange

open Classical in
/-- Theorem 1.3's continuous generating trace (transient when the lifetime is infinite), chosen pathwise (`0` where
none exists). -/
def chosenTrace {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℂ :=
  if hex : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
      (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) then hex.choose else 0

/-- **Theorem 1.3 for a flow-line driver** (named input `Exist.Theorem13Statement`): almost surely the chosen trace is a
continuous generating trace through the lifetime, transient when the lifetime is infinite. -/
theorem ae_chosenTrace (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ P h W ζ) :
    ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (chosenTrace W ζ ω) ∧
      (ζ ω = ⊤ → Tendsto (fun t => ‖chosenTrace W ζ ω t‖) atTop atTop) := by
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  filter_upwards [hT13 hκ (Theorem15.isOrderedForceWord_flowLine b J 0) hC.1] with ω hω
  have hex := hω.2
  unfold chosenTrace
  split_ifs
  exact hex.choose_spec

/-- **The first ordinary piece of a staged history from `0` lies in the completed counterflow range** (GW2a's base
step, from GB6). Conditional on GB6's restart law (`GB6RestartStatement`, PROVE-GB6C), Lemma GW0's forward
implication (`GW0ForwardStatement`, which makes the counterflow word admissible) and Theorem 1.3
(`Exist.Theorem13Statement`, the flow-line trace and the complete transient counterflow trace): almost surely, every
physical point of the first piece, run at angle `θ ∈ [−π/2, π/2]` up to its stop `min t ζ`, is in
`counterflowCompletedRange`. -/
theorem ae_tipSet_first_subset (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hW' : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {t : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    ∀ᵐ ω ∂P, (Chart.id.recenter 0).tipSet
        (fun r : ℝ≥0 => (E 0 ω).1 (min (r : ℝ≥0∞) (min t (E 0 ω).2)).toNNReal) (min t (E 0 ω).2) ⊆
      counterflowCompletedRange (fun s => W' s ω) := by
  have hfl := hS.isFlowLineDriver_first hκ hb hh hroot hp
  obtain ⟨b', J', h', hb', htr, hcf⟩ := hW'
  have hκ' : 0 < 16 / κ := by positivity
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hcf hζ'
  set γ := chosenTrace W' ζ' with hγdef
  set α := chosenTrace (fun t ω => (E 0 ω).1 t) (fun ω => (E 0 ω).2) with hαdef
  have hγ := ae_chosenTrace hT13 hκ' hcf
  have hα := ae_chosenTrace hT13 hκ hfl
  have hcomp : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [hγ, hζ'] with ω hω hζ
    rw [hζ] at hω
    exact ⟨hζ, hω.1, hω.2 rfl⟩
  have hFC := Supp8.GB6.gb6FirstContactStatement_of_restart hGB6 κ θ hκ hκ4 hθ.1 hθ.2 Ω _ P
    inferInstance h b jumps W' (fun t ω => (E 0 ω).1 t) ζ' (fun ω => (E 0 ω).2) γ α b' J' h' hb hh hb' htr
    hcf hadmL hadmR hcomp hfl (hα.mono fun _ hω => hω.1)
  have hall := ae_all_iff.2 fun q : ℚ => hFC (q : ℝ).toNNReal
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hcfd := Supp8.GB6.ae_driver_zero_continuousOn hcf
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hthr := hC.1.ae_tendsto_threshold hκ
  filter_upwards [hcomp, hα, hall, hdrv, hcfd, hthr, hS.2.2.1 0] with ω hcω hαω hqω hdω hcfω hthω hrecω
  -- the completed counterflow range is the closure of the physical counterflow
  have hW'c : Continuous fun s => W' s ω := by
    have := hcfω.2
    rw [hcω.1] at this
    simp only [ENNReal.coe_lt_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  rw [counterflowCompletedRange_eq_preimage_closure hcω.2.1 hW'c hcfω.1 hcω.2.2]
  have h0 : ((0 : ℂ) : OnePoint ℂ) ∈ closure (range fun s => Supp8.GB6.sphereInv (γ ω s : OnePoint ℂ)) :=
    mem_closure_of_tendsto (Supp8.GB6.tendsto_sphereInv_of_tendsto_norm hcω.2.2)
      (Eventually.of_forall fun s => ⟨s, rfl⟩)
  have hfc : ∀ q : ℚ, ((q : ℝ).toNNReal : ℝ≥0∞) < (E 0 ω).2 → α ω (q : ℝ).toNNReal ∈ H →
      ((α ω (q : ℝ).toNNReal : ℂ) : OnePoint ℂ) ∈ range fun s => Supp8.GB6.sphereInv (γ ω s : OnePoint ℂ) := by
    intro q hq hqH
    obtain ⟨T, hT, -⟩ := hqω q hq hqH
    exact ⟨T, hT⟩
  -- the driver is continuous up to the stop
  have hend : (E 0 ω).2 ≠ ⊤ → 0 < (E 0 ω).2 →
      Tendsto (E 0 ω).1 (𝓝[<] (E 0 ω).2.toNNReal) (𝓝 ((E 0 ω).1 (E 0 ω).2.toNNReal)) := by
    intro hne hpos
    have hT : (((E 0 ω).2.toNNReal : ℝ≥0) : ℝ≥0∞) = (E 0 ω).2 := ENNReal.coe_toNNReal hne
    have hTpos : 0 < (E 0 ω).2.toNNReal := ENNReal.toNNReal_pos hpos.ne' hne
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthω _ hTpos hT
    have h1 : Tendsto (E 0 ω).1 (𝓝[<] (E 0 ω).2.toNNReal) (𝓝 w₀) :=
      (continuous_fst.tendsto _).comp hlim
    rw [hrecω hne hpos w₀ h1]
    exact h1
  rw [tipSet_stopped_eq (continuous_recenter_id_inv 0) (hαω.1.mono_horizon (min_le_right _ _))
    (continuousOn_le_min t hdω.2 hend) hdω.1]
  rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  rw [recenter_id_inv]
  simp only [Complex.ofReal_zero, add_zero, mem_preimage]
  exact mem_closure_of_dense_contacts hαω.1 hdω.2 hdω.1 h0 hfc (hr.trans (min_le_right _ _))

/-- **GW2a for a single ordinary instruction** (conditional on the same three named inputs): almost surely the
physical set of the history `(0, ·, [flow θ t])` — its root `0` and the points of its one piece — lies in the
completed counterflow range. -/
theorem ae_physSet_single_subset (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hW' : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {gw2 : Bool} {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {t : ℝ≥0∞} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (0, gw2, [Sum.inl (θ, t)]) E) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps (0, gw2, [Sum.inl (θ, t)]) (fun k => E k ω) ⊆
      counterflowCompletedRange (fun s => W' s ω) := by
  filter_upwards [ae_tipSet_first_subset hGB6 hGW0 hT13 hκ hκ4 hb hh hW' hζ' hS rfl hθ rfl] with ω hω
  rw [physSet_single]
  refine union_subset ?_ hω
  rintro _ rfl
  exact Or.inr (by simp)

/-- **GW2a's containment for every single-instruction program** (the quantifier form of
`Theorem14.GW2aContainmentStatement`, restricted to the programs `[flow θ t]`). -/
theorem gw2aContainment_single (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ (θ : ℝ) (t : ℝ≥0∞), IsBoundaryContinuedProgram [Sum.inl (θ, t)] →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, false, [Sum.inl (θ, t)]⟩
            (fun k => E ⟨0, false, [Sum.inl (θ, t)]⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hW' hζ' E hE θ t hp
  exact ae_physSet_single_subset hGB6 hGW0 hT13 hκ hκ4 hb hh hW' hζ' (hp θ t (List.mem_singleton_self _))
    (hE _ hp)

/-- **The unchanged extremal path `β = η_{π/2}` of the strip system** (Aux. lemma 130) lies in the completed
counterflow range, from the three named inputs of this file instead of the general
`Theorem14.GW2aContainmentStatement` (compare `Sec7.StripSys.IsStripSystem.ae_physSet_leftExtremal_subset`). -/
theorem ae_physSet_leftExtremal_subset (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : Sec7.StripSys.IsStripSystem κ b jumps P h W' ζ' E) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps Sec7.StripSys.leftExtremalSpec
        (fun k => E Sec7.StripSys.leftExtremalSpec k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
  ae_physSet_single_subset hGB6 hGW0 hT13 hS.kappa_pos hS.kappa_lt_four hS.boundaryData hS.gff hS.counterflow
    hS.lifetime Sec7.StripSys.pi_div_two_mem_Icc hS.isStagedHistory_leftExtremal

end GW2aSingle
end Theorem14
end InteractingSLE
