/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JaStart

/-!
# SB2(2)'s joint stage induction: one lockstep stage with a finite piece, from F2a

Packet PROVE-SB2-LIFTSET (round 20). **`stage_fin_of_canon`**: at a lockstep stage whose actual piece `q` is finite
(lifetime `L₁ > 0`) and runs on the tail of the actual walk, the relative facts `StageRelFinP` and the drivenness of
the run-chart stage curve follow from

* the good-set matching (`goodTp_eq_canonGood_old`) and F2a's canonical drivenness (`Dv.isDrivenCurve_walkStage_old`);
* the physical domain identity (`phys_facts_of_fill`);
* the lifted seed: the relative chart is continuous from `ℍ` there and reads `0` (`chart_zero_of_arcM`,
  `continuousWithinAt_of_arcM` at a restart mark);
* the canonical curve's lift `ζ` before the end (`canon_old_fin`): continuous, in `ℍ̄`;
* the density of the good times, EL's generation, and the relative chart's generic facts.

Proof: the start value (`tendsto_relValp_of_tail` at `0`) carries F2a to the run chart
(`isDrivenCurve_stCurvep_of_canon`); through the clock the stage curve is `ζ`, which gives the limit at `∞` and the
values in `ℍ̄`; then `stageRelFinP_of`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep Sec7.PocketTraversal Sec7.Lemma71C

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- The good times below the lifetime accumulate at `0`. -/
theorem neBot_good_zero {G : Set ℝ≥0} {L : ℝ≥0∞} (hL : L ≠ 0)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure G) :
    (𝓝[G ∩ {t | (t : ℝ≥0∞) < L}] (0 : ℝ≥0)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t', ht'G, -, h2, h3⟩ := exists_good_between hgd (t := 0) (pos_iff_ne_zero.2 hL)
    (Real.toNNReal_pos.2 hε)
  refine ⟨t', ⟨ht'G, h3⟩, ?_⟩
  rw [zero_add] at h2
  rw [NNReal.dist_eq, NNReal.coe_zero, zero_sub, abs_neg, NNReal.abs_eq]
  have := NNReal.coe_lt_coe.2 h2
  rwa [Real.coe_toNNReal _ hε.le] at this

/-- **One lockstep stage with a finite piece, from F2a.** -/
theorem stage_fin_of_canon {s₂ : ExplState} {e₂ : Drv} {X : Set ℂ} {q : ℝ≥0 → ℂ} {L₁ : ℝ≥0} (hL₁ : 0 < L₁)
    {x₀ x₁ : ℝ}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcH' : ∀ w ∈ H, c.2.1 w ∈ H) (hoff : BdryOff c)
    (hPc : ContinuousOn q {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)})
    (htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)}, q t ∈ β₀ '' Ici tL)
    (hgood : goodTp c q L₁ = Dv.canonGood X q L₁) (hF : IsDrivenCurve (Dv.canonCurve X x₀ q L₁))
    (hΦ : ∀ z ∈ H \ fillH X, (stChart s₂).1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH X) x₁).1 z)
    (hΦd : (Mo.physRelChart c (stChart s₂) m).2.1 '' H = H \ fillH X)
    {w₀ : ℂ} (hw₀ : ∀ s, β₀ (tL + s) = q 0 → γ s = w₀)
    (hcw₀ : ContinuousWithinAt (stChart s₂).1 H w₀) (hz₀ : (stChart s₂).1 w₀ = 0)
    {ζ : ℝ≥0 → ℂ} (hζc : Continuous ζ) (hζH : ∀ t, ζ t ∈ Hbar)
    (hcv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (L₁ : ℝ≥0∞) → Dv.canonVal X x₀ q L₁ t = ζ t)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)} ⊆ closure (goodTp c q L₁))
    (he₂ : e₂.2 = capLife (stCurvep c m q L₁ s₂))
    (hgen : ∀ T < capLife (stCurvep c m q L₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m q L₁ s₂)))
    (hreg : IsRegularDriver e₂) (hB₂ : HasBdryLimits (stChart s₂).2.1)
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hc₂ : ∀ y ∈ H, (stChart s₂).2.1 y ∈ H) :
    IsDrivenCurve (stCurvep c m q L₁ s₂) ∧ StageRelFinP c m q L₁ s₂ e₂ := by
  have hL0 : (L₁ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL₁.ne'
  obtain ⟨σ, hσc, hσ⟩ := exists_tailTime hβ hPc htl
  have h0mem : ((0 : ℝ≥0) : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞) := by simp
  have hGsub : goodTp c q L₁ ∩ {t | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)} ⊆ goodTp c q L₁ := inter_subset_left
  -- the start value
  have h0 : Tendsto (relValp c m q s₂) (𝓝[goodTp c q L₁ ∩ {t | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)}] 0) (𝓝 0) := by
    have h := tendsto_relValp_of_tail hγ hcH hc1 hoff hσc hσ hGsub h0mem (hw₀ (σ 0) (hσ 0 h0mem)) hcw₀
    rwa [hz₀] at h
  have hne := neBot_good_zero hL0 hgd
  obtain ⟨hdr, heq⟩ := isDrivenCurve_stCurvep_of_canon hΦ hgood hF h0 hne
  -- the canonical representation: the stage curve is `ζ` through the clock
  have hL : (0 : ℝ) < L₁ := NNReal.coe_pos.2 hL₁
  have hrep : ∀ u : ℝ, 0 ≤ u → stCurvep c m q L₁ s₂ u = ζ (clockOf L₁ u).toNNReal := fun u hu => by
    have hm := clockOf_mem_Ico hL hu
    have hlt : (((clockOf L₁ u).toNNReal : ℝ≥0) : ℝ≥0∞) < (L₁ : ℝ≥0∞) := by
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hm.1]; exact hm.2
    rw [heq]
    unfold Dv.canonCurve
    simp only [ENNReal.coe_ne_top, ↓reduceIte, ENNReal.coe_toReal]
    exact hcv _ hlt
  have hcl : Tendsto (fun u => (clockOf L₁ u).toNNReal) atTop (𝓝 L₁) := by
    have h1 : Tendsto (clockOf L₁) atTop (𝓝 (L₁ : ℝ)) :=
      (Sec7.R7Aux131.tendsto_clockOf hL).mono_right nhdsWithin_le_nhds
    have h2 := (continuous_real_toNNReal.tendsto _).comp h1
    rwa [Real.toNNReal_coe] at h2
  have hz : Tendsto (stCurvep c m q L₁ s₂) atTop (𝓝 (ζ L₁)) :=
    ((hζc.tendsto L₁).comp hcl).congr' ((eventually_ge_atTop 0).mono fun u hu => (hrep u hu).symm)
  have hHbar : ∀ u, 0 ≤ u → stCurvep c m q L₁ s₂ u ∈ Hbar := fun u hu => by
    rw [hrep u hu]; exact hζH _
  -- the domain clause
  have hoffX : ∀ t ∈ goodTp c q L₁, q t ∉ fillH X := fun t ht => by
    rw [hgood] at ht; exact ht.2.2
  have hdom := stage_dom_of_phys hΦd hc1 hcH' hc₂ hoffX
  exact ⟨hdr, stageRelFinP_of hdr he₂ hgen hreg hz hHbar hB₂ hcH₂ hc1₂ hdom⟩

end InteractingSLE.Theorem14.SB.Lk
