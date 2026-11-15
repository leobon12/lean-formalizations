/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideVisR7
import InteractingSLE.Spec.Sec7.SideVisAnchor

/-!
# The R.7 shared-side witnesses from one live zero-phase time

PROVE-SIDE-VISITS. `OuterPhNext.TwoSeedSharedVisitsInput(Inf)` is consumed only
through `PocketStopSide.ae_phase_anchor_of_countable_visits`, i.e. through one live
positive time with zero phase. Conversely, its phase word supplies the lattice
condition and its antecedent the phase continuity, so one live zero-phase time
gives the countable witnesses with deterministic candidate times
(`SideVis.rat_zero_visits_of_anchor`). The anchor form
`TwoSeedSharedAnchorInput(Inf)` is therefore an equivalent, minimal target for
R.6's selection; it is implied by the fixed-time transfer through the proved
certified visits (`twoSeedSharedVisitsInput_of_transfer`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideVis

open PocketTraversal Lemma71C PocketStop PocketWordAssembly PocketSeedOpen
  PocketCoupling PocketJordan Hsd PhaseClause PocketStopField PocketMarks

section Defs

variable {Ω : Type*}

/-- **R.6's selection in anchor form** (bounded outer pocket): for every coherent
phase word with a continuous phase, almost surely on the test, a positive live
relative time has zero phase. -/
def TwoSeedSharedAnchorInput (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAll R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
        ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0

/-- **R.6's selection in anchor form** for a pocket opening at the flow seed. -/
def TwoSeedSharedAnchorInputInf (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAllInf R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
        ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0

end Defs

section Witness

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
  {P : Measure Ω} {k rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}

/-- **The shared-side witnesses from the anchor form** (bounded outer pocket):
deterministic rational candidate times and the events `{δ r = 0}`. -/
theorem twoSeedSharedVisitsInput_of_anchor (hk : 4 < k)
    (h : TwoSeedSharedAnchorInput k rL rR 𝓦 P R L r η G h₀ u) :
    OuterPhNext.TwoSeedSharedVisitsInput k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont
  obtain ⟨-, hvis⟩ := rat_zero_visits_of_anchor hk (fun q => (hphase q).1) hcont
    (h A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont)
  refine ⟨fun i _ => (((Denumerable.eqv ℚ).symm i : ℚ) : ℝ).toNNReal,
    fun i => {ω | δ (((Denumerable.eqv ℚ).symm i : ℚ) : ℝ).toNNReal ω = 0},
    fun i => Eventually.of_forall fun _ _ h => h, ?_⟩
  filter_upwards [hvis] with ω hv hω hT
  obtain ⟨q, hq, hqT, hq0⟩ := hv hω hT
  refine ⟨Denumerable.eqv ℚ q, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact ⟨hq, hqT, hq0⟩

/-- **The shared-side witnesses from the anchor form** (seed-opening pocket). -/
theorem twoSeedSharedVisitsInputInf_of_anchor (hk : 4 < k)
    (h : TwoSeedSharedAnchorInputInf k rL rR 𝓦 P R L r η G h₀ u) :
    OuterPhNext.TwoSeedSharedVisitsInputInf k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont
  obtain ⟨-, hvis⟩ := rat_zero_visits_of_anchor hk (fun q => (hphase q).1) hcont
    (h A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont)
  refine ⟨fun i _ => (((Denumerable.eqv ℚ).symm i : ℚ) : ℝ).toNNReal,
    fun i => {ω | δ (((Denumerable.eqv ℚ).symm i : ℚ) : ℝ).toNNReal ω = 0},
    fun i => Eventually.of_forall fun _ _ h => h, ?_⟩
  filter_upwards [hvis] with ω hv hω hT
  obtain ⟨q, hq, hqT, hq0⟩ := hv hω hT
  refine ⟨Denumerable.eqv ℚ q, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact ⟨hq, hqT, hq0⟩

/-- The anchor form follows from the fixed-time transfer (through the proved
certified visits) on every bounded outer configuration. -/
theorem twoSeedSharedAnchorInput_of_transfer {βR βL : Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ}
    (htr : TwoSeedSharedTransferInput k rL rR 𝓦 P R L r η G h₀ u βR βL)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (h42 : ∀ᵐ ω ∂P, Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤)
    (hβ : ∀ᵐ ω ∂P, Sec5.Prop55Half.IsSeedProper (βR ω) ∧ Sec5.Prop55Half.IsSeedProper (βL ω)) :
    TwoSeedSharedAnchorInput k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont
  obtain ⟨s, E, hzero, hvisit⟩ := twoSeedSharedVisitsInput_of_transfer htr hcfg h42 hβ
    A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont
  exact PocketStopSide.ae_phase_anchor_of_countable_visits hzero hvisit

end Witness

end InteractingSLE.Sec7.SideVis
