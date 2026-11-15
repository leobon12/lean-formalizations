/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11Proof
import InteractingSLE.Spec.Supplement.GW1LaterR51

/-!
# The barrier input of GB11: from the sample to its conditional law

Packet PROVE-T14-GW4T3, item (2). Theorem GW4's proof (`source/spec/p625-671.md` L229–L262, pp. 637–638) applies
GB11's barrier input to the actual sewn walks under the conditional law `ν = ν(ω₀)` given the two walks' retained
pasts. `GW4Reg.GW4BarrierPocketRegStatement` (PROVE-T14-GW4T2) asks: for `P`-a.e. `ω₀`, parametrizations `α_R`, `α_L`
of the walks **of `ω₀`** such that `ν(ω₀)`-almost surely every generating trace of the ambient counterflow **of `ω`**
satisfies `GB11.IsGB11Barrier α_R α_L γ`. The walk results (SB, GW1, GW8) are proved for the walks and the trace of the
same sample under `P`. This file moves them to the conditional law.

## Main results

* `exists_strictMono_comp_eq` (deterministic): two complete simple flows with the same range differ by a continuous
  strictly increasing reparametrization fixing `0`.
* `isGB11Barrier_of_range_eq` (deterministic): GB11's barrier input depends only on the two ranges (among complete
  simple flows): contact order, no common subarc, (GB11.B) and the reverse first-visit order transfer.
* `ae_ae_physSet_eq`: for a staged history that is `StagedPiecesRegular` and every sub-σ-algebra `m ≤ mΩ` containing
  its retained past, `ν(ω₀)`-almost surely the physical set of `ω` is that of `ω₀`, for `P`-a.e. `ω₀`. (The past map is
  `m`-measurable, so it is `ν(ω₀)`-a.s. constant; the regularized history `StagedReg.regHist` has `P`-a.s. the same runs
  and is regular at every sample, so equal pasts give equal runs.) No modification of the conditioning σ-algebra is
  needed: `IsStagedHistory` already makes every retained past an event (`pastSigma … ≤ mΩ`).
* **`gw4BarrierPocketRegStatement_of_self`**: `GW4BarrierPocketRegStatement` from **`GW4BarrierSelfRegStatement`**, the
  barrier input for the walks and the traces of the same sample (named input, `P`-form).
* `gw4BarrierSelfRegStatement_of_everyReg`: the `P`-form for `StagedPiecesRegular` families from the `P`-form for
  families regular at every sample (`GW4BarrierSelfEveryRegStatement`; regularize, `StagedReg.regFam_spec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Reg

open GW4Traverse GW4Ident

/-! ### Complete simple flows with the same range -/

/-- A complete simple flow is a proper curve (`Supp9B.IsProperCurve`). -/
theorem isProperCurve_of_isCompleteSimpleFlow {α : ℝ≥0 → ℂ} (h : GB11.IsCompleteSimpleFlow α) :
    Supp9B.IsProperCurve α :=
  ⟨h.1, h.2.1, fun t => h.2.2.2.1 t, h.2.2.2.2⟩

/-- **Reparametrization.** Two complete simple flows with the same range differ by a continuous strictly increasing
map `φ` of `[0, ∞)` with `φ 0 = 0`: `α ∘ φ = α'`. -/
theorem exists_strictMono_comp_eq {α α' : ℝ≥0 → ℂ} (h : GB11.IsCompleteSimpleFlow α)
    (h' : GB11.IsCompleteSimpleFlow α') (hr : range α' = range α) :
    ∃ φ : ℝ≥0 → ℝ≥0, Continuous φ ∧ StrictMono φ ∧ φ 0 = 0 ∧ ∀ s, α (φ s) = α' s := by
  have he := (WalkCont.isClosedEmbedding_of_isProperCurve (isProperCurve_of_isCompleteSimpleFlow h)).isEmbedding
  have hmem : ∀ s, α' s ∈ range α := fun s => hr ▸ mem_range_self s
  set φ : ℝ≥0 → ℝ≥0 := fun s => he.toHomeomorph.symm ⟨α' s, hmem s⟩ with hφ
  have hφα : ∀ s, α (φ s) = α' s := fun s => by
    exact congrArg Subtype.val (he.toHomeomorph.apply_symm_apply ⟨α' s, hmem s⟩)
  have hc : Continuous φ :=
    he.toHomeomorph.symm.continuous.comp (h'.1.subtype_mk hmem)
  have hinj : Function.Injective φ := fun s s' e => h'.2.1 (by rw [← hφα s, ← hφα s', e])
  have h0 : φ 0 = 0 := h.2.1 (by rw [hφα 0, h'.2.2.1, h.2.2.1])
  refine ⟨φ, hc, ?_, h0, hφα⟩
  rcases hc.strictMono_of_inj hinj with hm | ha
  · exact hm
  · exfalso
    have := ha (show (0 : ℝ≥0) < 1 from one_pos)
    rw [h0] at this
    exact not_lt_zero this

/-- A continuous monotone map covers the interval between its values. -/
theorem Icc_subset_image_Icc {φ : ℝ≥0 → ℝ≥0} (hc : Continuous φ) {a b : ℝ≥0} (hab : a ≤ b) :
    Icc (φ a) (φ b) ⊆ φ '' Icc a b :=
  intermediate_value_Icc hab hc.continuousOn

/-- **GB11's barrier input depends only on the ranges of the two flows.** If `α_R'`, `α_L'` satisfy the barrier input
with `γ` and `α_R`, `α_L` are complete simple flows with the same ranges, then `α_R`, `α_L` satisfy it with `γ`. -/
theorem isGB11Barrier_of_range_eq {αR αL αR' αL' γ : ℝ≥0 → ℂ} (hfR : GB11.IsCompleteSimpleFlow αR)
    (hfL : GB11.IsCompleteSimpleFlow αL) (hR : range αR = range αR') (hL : range αL = range αL')
    (h : GB11.IsGB11Barrier αR' αL' γ) : GB11.IsGB11Barrier αR αL γ := by
  obtain ⟨hfR', hfL', hord, hnosub, hBB, hrevR, hrevL⟩ := h
  obtain ⟨φ, hφc, hφm, hφ0, hφ⟩ := exists_strictMono_comp_eq hfR' hfR hR
  obtain ⟨ψ, hψc, hψm, hψ0, hψ⟩ := exists_strictMono_comp_eq hfL' hfL hL
  have hpos : ∀ {χ : ℝ≥0 → ℝ≥0}, StrictMono χ → χ 0 = 0 → ∀ {s : ℝ≥0}, 0 < s → 0 < χ s := by
    intro χ hm h0 s hs
    have := hm hs
    rwa [h0] at this
  refine ⟨hfR, hfL, ?_, ?_, ?_, ?_, ?_⟩
  · intro s s' t t' e e'
    rw [← hφ s, ← hψ t] at e
    rw [← hφ s', ← hψ t'] at e'
    exact (hφm.lt_iff_lt.symm.trans (hord _ _ _ _ e e')).trans hψm.lt_iff_lt
  · intro a b hab hsub
    refine hnosub (φ a) (φ b) (hφm hab) ?_
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Icc_subset_image_Icc hφc hab.le hr
    rw [hφ v, ← hL]
    exact hsub ⟨v, hv, rfl⟩
  · intro t ht
    rw [hR, hL]
    exact hBB t ht
  · intro s s' hs hss'
    rw [← hφ s, ← hφ s']
    exact hrevR _ _ (hpos hφm hφ0 hs) (hφm hss')
  · intro s s' hs hss'
    rw [← hψ s, ← hψ s']
    exact hrevL _ _ (hpos hψm hψ0 hs) (hψm hss')

/-! ### The walks of a sample under its conditional law -/

section Transfer

open Exist Exist.Staged Exist.StagedLaw StagedReg

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The physical set of a staged history is fixed by the conditional law given any σ-algebra containing its
retained past** (R51 form): for `P`-a.e. `ω₀`, `ν(ω₀)`-almost surely the physical set of `ω` is that of `ω₀`. The
retained past is `m`-measurable, hence `ν(ω₀)`-a.s. constant; the regularized history has `P`-a.s. the same runs and
is regular at every sample, so equal retained pasts give equal runs. -/
theorem ae_ae_physSet_eq {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) (hm : m ≤ mΩ)
    (hpm : pastSigma κ b jumps spec E spec.2.2.length ≤ m) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P m ω₀),
      ExplState.physSet κ b jumps spec (fun k => E k ω) =
        ExplState.physSet κ b jumps spec (fun k => E k ω₀) := by
  let := upgradeStandardBorel (PastData spec.2.2.length)
  have hf : Measurable[m] (pastMap κ b jumps spec E spec.2.2.length) := by
    rw [measurable_iff_comap_le]
    exact hpm
  have h1 := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hm hf
  have hrun := ae_run_regHist hR
  have hrun' := GW4Traverse.ae_ae_condExpKernel (m := m) hrun
  filter_upwards [h1, hrun, hrun'] with ω₀ h1ω₀ hrω₀ hr'ω₀
  filter_upwards [h1ω₀, hr'ω₀] with ω hfω hrω
  have hpast : ∀ ω' : Ω, (∀ k, ExplState.run κ b jumps spec (fun j => regHist spec E j ω') k =
      ExplState.run κ b jumps spec (fun j => E j ω') k) →
      pastMap κ b jumps spec (regHist spec E) spec.2.2.length ω' =
        pastMap κ b jumps spec E spec.2.2.length ω' := by
    intro ω' hω'
    unfold pastMap
    rw [hω' spec.2.2.length]
  have hreg := run_eq_of_pastMap_eq (κ := κ) (b := b) (jumps := jumps) spec (E := regHist spec E)
    (k := spec.2.2.length) (fun j _ ω' => isRegularDriver_regHist j ω') (ω := ω) (ω' := ω₀)
    (by rw [hpast ω hrω, hpast ω₀ hrω₀, hfω])
  refine physSet_eq_of_run_eq ?_
  rw [← hrω spec.2.2.length, ← hrω₀ spec.2.2.length]
  exact hreg

end Transfer

/-! ### The barrier input for the sample, and its transfer -/

/-- **Named input: GB11's barrier input for the walks and the traces of the same sample, R51 form** (Theorem GW4's
proof, p. 637; SB, GW1, GW8, GB13a; `P`-form). Binders of `GW4BarrierPocketRegStatement` up to the families.
`P`-almost surely the two walks of `ω` are the ranges of complete simple flows `α_R`, `α_L` from `0` to `∞` with the
pocket shape (`WalkPocketShape`), and every generating trace of the ambient counterflow of the same `ω` satisfies
GB11's barrier input with them. -/
def GW4BarrierSelfRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω ∂P, ∃ αR αL : ℝ≥0 → ℂ, range αR = ExplState.physSet κ b jumps wR (fun k => E wR k ω) ∧
        range αL = ExplState.physSet κ b jumps wL (fun k => E wL k ω) ∧
        GB11.IsCompleteSimpleFlow αR ∧ GB11.IsCompleteSimpleFlow αL ∧ WalkPocketShape αR αL ∧
        ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → GB11.IsGB11Barrier αR αL γ

/-- **The barrier input of GB11 under the conditional law, from the barrier input for each sample** (item (2) of
PROVE-T14-GW4T3): for `P`-a.e. `ω₀`, take the flows of `ω₀`; `ν(ω₀)`-almost surely the walks of `ω` are those of
`ω₀` (`ae_ae_physSet_eq`) and the barrier input holds for `ω` (a `P`-a.s. property holds `ν(ω₀)`-a.s.), with flows of
the same ranges, hence with the flows of `ω₀` (`isGB11Barrier_of_range_eq`). -/
theorem gw4BarrierPocketRegStatement_of_self (hS : GW4BarrierSelfRegStatement.{u}) :
    GW4BarrierPocketRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hpR := GW1X.isBoundaryContinuedProgram_walkR b jumps
  have hpL := GW1X.isBoundaryContinuedProgram_walkL b jumps
  have hm : pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length ≤
      ‹MeasurableSpace Ω› := sup_le ((hE wR hpR).2.1 _) ((hE wL hpL).2.1 _)
  have hself := hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hself, ae_ae_physSet_eq (hreg wR hpR) hm le_sup_left,
    ae_ae_physSet_eq (hreg wL hpL) hm le_sup_right,
    GW4Traverse.ae_ae_condExpKernel
      (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) hself]
    with ω₀ hω₀ hRω₀ hLω₀ hSω₀
  obtain ⟨αR, αL, hαR, hαL, hfR, hfL, hP, -⟩ := hω₀
  refine ⟨αR, αL, hαR, hαL, hP, ?_⟩
  filter_upwards [hRω₀, hLω₀, hSω₀] with ω hRω hLω hSω γ hγ
  obtain ⟨αR', αL', hαR', hαL', -, -, -, hbar'⟩ := hSω
  exact isGB11Barrier_of_range_eq hfR hfL (by rw [hαR, hαR', hRω]) (by rw [hαL, hαL', hLω]) (hbar' γ hγ)

/-- **The `P`-form of the barrier input for staged families regular at every sample** (the form in which GW1X and
GW9 state the walk results, `GW1X.GW1ParamEveryRegStatement`). -/
def GW4BarrierSelfEveryRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, Exist.Staged.IsRegularDriver (E spec k ω)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω ∂P, ∃ αR αL : ℝ≥0 → ℂ, range αR = ExplState.physSet κ b jumps wR (fun k => E wR k ω) ∧
        range αL = ExplState.physSet κ b jumps wL (fun k => E wL k ω) ∧
        GB11.IsCompleteSimpleFlow αR ∧ GB11.IsCompleteSimpleFlow αL ∧ WalkPocketShape αR αL ∧
        ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → GB11.IsGB11Barrier αR αL γ

/-- **R51 reduction of the `P`-form**: regularize the family (`StagedReg.regFam_spec`); the walks are almost surely
unchanged and the counterflow is the same. -/
theorem gw4BarrierSelfRegStatement_of_everyReg (hG : GW4BarrierSelfEveryRegStatement.{u}) :
    GW4BarrierSelfRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR wR wL
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hR
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg',
    hrun _ (GW1X.isBoundaryContinuedProgram_walkR b jumps),
    hrun _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)] with ω hω hrR hrL
  obtain ⟨αR, αL, hαR, hαL, hrest⟩ := hω
  exact ⟨αR, αL, hαR.trans (StagedReg.physSet_eq_of_run_eq (hrR _)),
    hαL.trans (StagedReg.physSet_eq_of_run_eq (hrL _)), hrest⟩

/-- **The barrier input under the conditional law from the `P`-form for families regular at every sample.** -/
theorem gw4BarrierPocketRegStatement_of_everyReg (hG : GW4BarrierSelfEveryRegStatement.{u}) :
    GW4BarrierPocketRegStatement.{u} :=
  gw4BarrierPocketRegStatement_of_self (gw4BarrierSelfRegStatement_of_everyReg hG)

end GW4Reg

end Theorem14

end InteractingSLE
