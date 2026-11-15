/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripNoncollision
import InteractingSLE.Spec.Sec7.ContinuityProbCollision

/-!
# The strip endpoint theorem (ii): the first two clauses

Packet PROVE-ZHAN-A3. `Strip.HasStripEndpoint` (Astra §3 (ii), in the R36 form of `StripEndpointStatement.lean`) has
three clauses: (1) the strip clock is unbounded on the strip life; (2) a continuous generating chordal trace on the
strip life exists; (3) every such trace converges along the strip life to a point `x < −1`. For a strip evolution with
`κ > 0`, separated lower marks and the prefix sums of (3.3) this file proves (1) and (2) almost surely
(`ae_hasStripEndpoint_clock_trace`):

* (1) is `ae_hasUnboundedStripClock` (`StripNoncollision.lean`);
* (2): on the strip life no force point meets the driver (`ae_stripLife_noncollision`; the end mark by definition),
  so the landed trace theorem before collisions (`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_lt_of_forall_ne`)
  applies up to the end of the strip life, which is open (`exists_gt_isStripLife`).

Clause (3) (constant drift `|σ| < 1` to the actual trace, whole-tail Girsanov; Astra L1420–L1584) is not proved here;
`ae_hasStripEndpoint_of_convergence` is the distinctly named reduction of (ii) to it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

open Strip

variable {nL nR : ℕ}

/-- **The strip life is open**: every strip-life time is followed by a later one. -/
theorem exists_gt_isStripLife {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    ∃ s' : ℝ≥0, s < s' ∧ IsStripLife w v ζ s' := by
  have hc : ContinuousAt (fun t => w t - v t) s :=
    (hw.sub hv).continuousAt ((Coupling.isOpen_setOf_coe_lt ζ).mem_nhds hs.1)
  have hpos : 0 < w s - v s := sub_pos.2 (hs.2 s le_rfl)
  have hev1 : ∀ᶠ u : ℝ≥0 in 𝓝 s, (u : ℝ≥0∞) < ζ := (Coupling.isOpen_setOf_coe_lt ζ).mem_nhds hs.1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and (hc.eventually (lt_mem_nhds hpos)))
  set ρ : ℝ≥0 := (δ / 2).toNNReal with hρ
  have hρpos : 0 < ρ := Real.toNNReal_pos.2 (by linarith)
  have hρδ : (ρ : ℝ) = δ / 2 := Real.coe_toNNReal _ (by linarith)
  have hclose : ∀ u : ℝ≥0, s ≤ u → u ≤ s + ρ → (u : ℝ≥0∞) < ζ ∧ 0 < w u - v u := fun u h1 h2 => hball (by
    rw [NNReal.dist_eq, abs_lt]
    have h1' : (s : ℝ) ≤ u := by exact_mod_cast h1
    have h2' : (u : ℝ) ≤ s + ρ := by exact_mod_cast h2
    constructor <;> linarith)
  refine ⟨s + ρ, lt_add_of_pos_right s hρpos, (hclose _ le_self_add le_rfl).1, fun r hr => ?_⟩
  rcases le_or_gt r s with hrs | hsr
  · exact hs.2 r hrs
  · have := (hclose r hsr.le hr).2; linarith

variable {κ τm : ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Clause (2) of (ii)**: almost surely a continuous generating chordal trace on the strip life exists. -/
theorem ae_exists_isGeneratingTrace_stripLife (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR)
    (hpre : HasStripPrefixSums κ ρL ρR) (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
      IsGeneratingTrace (W · ω) s η := by
  have : IsProbabilityMeasure P :=
    hE.isFilteredBrownianReal.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  filter_upwards [IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_lt_of_forall_ne hκ hE,
    ae_stripLife_noncollision hκ hsep hpre hE, hE.ae_isIntegratedSLEPath] with ω htr hnc hp
  have hF := hp.isForcePath
  set τ : ℝ≥0∞ := ⨆ (s : ℝ≥0) (_ : IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s), (s : ℝ≥0∞)
    with hτ
  have hτζ : τ ≤ ζ ω := iSup₂_le fun s hs => hs.1.le
  have hbelow : ∀ r : ℝ≥0, (r : ℝ≥0∞) < τ → IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) r := by
    intro r hr
    obtain ⟨s, hs⟩ := lt_iSup_iff.1 hr
    obtain ⟨hsl, hrs⟩ := lt_iSup_iff.1 hs
    exact hsl.mono (by exact_mod_cast hrs.le)
  obtain ⟨η, hη0, hηc, hηf⟩ := htr τ hτζ fun r hr => by
    have hl := hbelow r hr
    obtain ⟨hL, hR⟩ := hnc r hl
    refine ⟨fun i => ?_, fun j => (hR j).ne⟩
    induction i using Fin.lastCases with
    | last => exact (hl.2 r le_rfl).ne'
    | cast i => exact (hL i).ne'
  refine ⟨η, fun s hs => ?_⟩
  obtain ⟨s', hss', hs'⟩ := exists_gt_isStripLife hF.continuousOn_w (hF.continuousOn_vL _) hs
  have hsτ : (s : ℝ≥0∞) < τ := lt_of_lt_of_le (by exact_mod_cast hss')
    (le_iSup₂ (f := fun (s : ℝ≥0) (_ : IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s) =>
      (s : ℝ≥0∞)) s' hs')
  exact ⟨hη0, hηc.mono fun t ht => lt_of_le_of_lt ht hsτ, fun t ht => hηf t (ht.trans hsτ)⟩

/-- **Clauses (1) and (2) of the strip endpoint theorem (ii)**, for every `κ > 0`. -/
theorem ae_hasStripEndpoint_clock_trace (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR)
    (hpre : HasStripPrefixSums κ ρL ρR) (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (∀ T : ℝ, ∃ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s ∧
        T ≤ stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s) ∧
      ∃ η : ℝ≥0 → ℂ, ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
        IsGeneratingTrace (W · ω) s η := by
  filter_upwards [ae_hasUnboundedStripClock hκ hsep hpre hE,
    ae_exists_isGeneratingTrace_stripLife hκ hsep hpre hE] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **Conditional helper (not the source theorem)**: the strip endpoint theorem (ii) for one evolution, given its
third clause (almost sure convergence of every generating trace along the strip life to a point `x < −1`). The
missing proposition is exactly `hconv`; clauses (1) and (2) are proved (`ae_hasStripEndpoint_clock_trace`). -/
theorem ae_hasStripEndpoint_of_convergence (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR)
    (hpre : HasStripPrefixSums κ ρL ρR) (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ)
    (hconv : ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ,
      (∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s → IsGeneratingTrace (W · ω) s η) →
      ∃ x : ℝ, x < -1 ∧ ∀ ε > 0, ∃ s₀ : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s₀ ∧
        ∀ s : ℝ≥0, s₀ ≤ s → IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s → ‖η s - x‖ < ε) :
    ∀ᵐ ω ∂P, HasStripEndpoint (W · ω) (VL (Fin.last nL) · ω) (ζ ω) := by
  filter_upwards [ae_hasStripEndpoint_clock_trace hκ hsep hpre hE, hconv] with ω h12 h3
  exact ⟨h12.1, h12.2, h3⟩

end Zhan

end InteractingSLE
