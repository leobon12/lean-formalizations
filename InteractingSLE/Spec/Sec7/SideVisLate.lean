/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LateSide
import InteractingSLE.Spec.Sec7.SideVisAnchor

/-!
# The late side data's shared-side visits from one live zero-phase time

PROVE-SIDE-VISITS. In the late wiring of Theorems 1.2–1.3 the side data
`Late.SideData` carry, besides the reference sets, lifts, phase and probes, a
countable family of candidate visits (`visit`, `event`) and two candidate means
(`currentMean`, `referenceMean`). These four fields occur only in the binders
`hSideJointGerms` and `hSideVisits`, and those binders are used only through
`PocketStopSide.ae_phase_zero_of_joint_germs` and
`PocketStopSide.ae_phase_anchor_of_countable_visits`, i.e. through one live
positive time with zero phase.

This file replaces the four fields by canonical ones (`SideData.anchored`):
the visits are the positive rational relative times, the candidate event at `r`
is `{phase r = 0}`, and both candidate means vanish. For these canonical fields

* the joint-germ binder holds deterministically (`anchored_jointGerms`: the
  identity chart on a one-point interval);
* the visit binder follows from **one** live zero-phase time, the lattice binder
  and the probe binder (`anchored_visits`: the lattice-valued continuous phase is
  constant on the positive lifetime, hence vanishes at every positive rational
  live time);

and conversely the original two binders give that zero-phase time
(`sideAnchor_of_jointGerms_visits`). Nothing else in the side data changes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Late

open Sec7 Sec7.PocketStopSide Sec7.PocketTraversal Sec7.Lemma71C Sec7.PhaseSel

/-- The side data with canonical candidate visits: positive rational relative
times, the candidate event `{phase r = 0}`, and vanishing candidate means. All
other fields are those of `e`. -/
def SideData.anchored {Ω : Type} (e : SideData Ω) : SideData Ω :=
  { e with
    visit := fun r _ => (r : ℝ).toNNReal
    event := fun r => {ω | e.phase (r : ℝ).toNNReal ω = 0}
    currentMean := fun _ _ _ => 0
    referenceMean := fun _ _ _ => 0 }

@[simp] theorem SideData.anchored_phase {Ω : Type} (e : SideData Ω) : e.anchored.phase = e.phase := rfl

theorem schwarzReflect_id : QuantumZipper.CA.schwarzReflect (fun z : ℂ => z) = fun z => z := by
  funext z
  simp only [QuantumZipper.CA.schwarzReflect]
  split_ifs
  · rfl
  · exact Complex.conj_conj z

theorem isRealBoundaryConformal_id (y : ℝ) : R16.IsRealBoundaryConformal (fun z : ℂ => z) y 1 :=
  ⟨differentiableOn_id, continuousOn_id, fun _ _ hz => hz, fun _ hz => hz.1, injOn_id _⟩

/-- **The joint-germ binder for the canonical candidates** holds deterministically:
on the candidate event the phase vanishes at the candidate time, and the identity
chart on `{0}` with the zero logarithm compares the two vanishing means. -/
theorem anchored_jointGerms {Ω : Type} [MeasurableSpace Ω] (e : SideData Ω) (P : Measure Ω)
    (A : Set Ω) (κ : ℝ) :
    ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ e.anchored.event i →
      ∃ (ξ η y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU b : ℝ),
        IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
        (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
        ContinuousOn (fun y : ℝ => L y) J ∧
        (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
        bC = bU ∧ bU = bC + chiC κ * (L y₀).im ∧
        ContinuousWithinAt L Hbar (ξ : ℂ) ∧
        Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) ∧
        Tendsto (e.anchored.currentMean i ω) (𝓝[H] (ξ : ℂ))
          (𝓝 (b + e.anchored.phase (e.anchored.visit i ω) ω)) ∧
        Tendsto (e.anchored.referenceMean i ω) (𝓝[H] (η : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => e.anchored.referenceMean i ω (φ z) - e.anchored.currentMean i ω z -
          chiC κ * (L z).im) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  intro i
  refine Eventually.of_forall fun ω _ hE => ?_
  have hE' : e.phase (i : ℝ).toNNReal ω = 0 := hE
  refine ⟨0, 0, 0, {0}, fun z => z, fun _ => 0, 0, 0, 0, isPreconnected_singleton, rfl, rfl,
    fun y _ => ⟨1, one_pos, isRealBoundaryConformal_id y⟩, continuousOn_const, fun y _ => ?_,
    rfl, by simp, continuousWithinAt_const, tendsto_nhdsWithin_mono_right (subset_refl _) tendsto_id, ?_,
    tendsto_const_nhds, ?_⟩
  · rw [schwarzReflect_id, Complex.exp_zero, deriv_id'']
  · show Tendsto (fun _ : ℂ => (0 : ℝ)) _ (𝓝 (0 + e.phase (i : ℝ).toNNReal ω))
    rw [hE', add_zero]
    exact tendsto_const_nhds
  · show Tendsto (fun _ : ℂ => (0 : ℝ) - 0 - chiC κ * (0 : ℂ).im) _ (𝓝 0)
    simp only [sub_zero, Complex.zero_im, mul_zero]
    exact tendsto_const_nhds

/-- **The visit binder for the canonical candidates** from one live zero-phase
time: the lattice-valued phase, continuous on the positive lifetime (mean
probes), is constant there, so it vanishes at a positive rational live time. -/
theorem anchored_visits {Ω : Type} [MeasurableSpace Ω] (e : SideData Ω) {P : Measure Ω}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {κ : ℝ} (hκ : 4 < κ)
    (hLattice : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, e.phase q ω = m * phaseStep κ)
    (hProbes : ∀ N : ℕ, ∀ᵐ ω ∂P, ω ∈ A →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (e.probe N ω) S ∧ ContinuousOn (e.baseProbe N ω) S ∧ ContinuousOn (e.weight N ω) S ∧
        ∀ t ∈ S, 0 < e.weight N ω t ∧ e.probe N ω t - e.baseProbe N ω t = e.phase t ω * e.weight N ω t)
    (hAnchor : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ e.phase s ω = 0) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ i, 0 < e.anchored.visit i ω ∧ (e.anchored.visit i ω : ℝ≥0∞) < capLife (γ ω) ∧
        ω ∈ e.anchored.event i := by
  filter_upwards [(SideVis.rat_zero_visits_of_anchor hκ hLattice
    (ae_continuous_phase_of_mean_probes hProbes) hAnchor).2] with ω h hω hT
  exact h hω hT

/-- Conversely, the original joint-germ and visit binders give one live zero-phase
time, so the canonical candidates lose nothing. -/
theorem sideAnchor_of_jointGerms_visits {Ω : Type} [MeasurableSpace Ω] (e : SideData Ω)
    {P : Measure Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {κ : ℝ} (hκ : 4 < κ)
    (hJointGerms : ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ e.event i →
      ∃ (ξ η y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU b : ℝ),
        IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
        (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
        ContinuousOn (fun y : ℝ => L y) J ∧
        (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
        bC = bU ∧ bU = bC + chiC κ * (L y₀).im ∧
        ContinuousWithinAt L Hbar (ξ : ℂ) ∧
        Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) ∧
        Tendsto (e.currentMean i ω) (𝓝[H] (ξ : ℂ)) (𝓝 (b + e.phase (e.visit i ω) ω)) ∧
        Tendsto (e.referenceMean i ω) (𝓝[H] (η : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => e.referenceMean i ω (φ z) - e.currentMean i ω z - chiC κ * (L z).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 0))
    (hVisits : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ i, 0 < e.visit i ω ∧ (e.visit i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ e.event i) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ e.phase s ω = 0 :=
  ae_phase_anchor_of_countable_visits (ae_phase_zero_of_joint_germs hκ hJointGerms) hVisits

/-- The side target's parameter is the dual of the both-low parameter. -/
theorem target_kappa {Ω : Type} [MeasurableSpace Ω] (j : Current.SideTest Ω) (i : Current.BothLow)
    (d : Current.WordObjects Ω) : (j.target i d).kappa = 16 / (16 / i.kappa) := by
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft <;> rfl

theorem four_lt_target_kappa {Ω : Type} [MeasurableSpace Ω] (j : Current.SideTest Ω) (i : Current.BothLow)
    (d : Current.WordObjects Ω) : 4 < (j.target i d).kappa := by
  have hk : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  rw [target_kappa, hdual]
  exact i.kappa_gt_four

end InteractingSLE.Wire.Late
