/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeS6
import InteractingSLE.Spec.Supplement.GB6Disjoint
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit

/-!
# GB6's relative safe law, part 7: the physical union read in the relative chart

Packet PROVE-GB6-RELSAFE2. The shape clause of the line data (`hBK` of `HasGB6LineLocal`): before the stop, the
complement of the physical union `A ∪ K_t` (`A = −1/K^α_s` the retained flow hull in the counterflow frame, `K_t` the
counterflow hull at the physical time `t`) is the inverse relative chart image of the complement of the relative hull
`K̃_{a(t)}`:

* `image_inv_compl_image_fwd` (deterministic): for a conformal chart with `inv(ℍ) = D` and `K ⊆ D`,
  `inv(ℍ ∖ fwd(K)) = D ∖ K`;
* `fwdHull_record_eq` / `invHull_record_eq`: the record driver and the flow driver have the same hull at `s`
  (both continuous on `[0, s]`, equal there; through a driver frozen after `s`);
* **`ae_compl_union_eq_relChart`**: almost surely, on the good event and `{a(t) < V}`:
  `ℍ ∖ (A ∪ K_t) = relChart(rec).inv (ℍ ∖ K̃_{a(t)})` — `t` is before the first contact (otherwise the physical clock
  would already be `≥ V`), `a(t)` is GB6's clock at `t`, the version maps `K_t` onto `K̃_{a(t)}`, and `K_t` misses `A`
  (`GB6Disjoint`, `Q3Rel.disjoint_closure_invHull`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.RelSafeS

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Theorem14.GW2JointKernel

/-! ### Deterministic: the inverse chart image of a complement -/

theorem image_inv_compl_image_fwd {c : Chart} {D : Set ℂ} (hc : c.IsConformal) (hD : c.2.1 '' H = D)
    {K : Set ℂ} (hK : K ⊆ D) : c.2.1 '' (H \ c.1 '' K) = D \ K := by
  ext x
  constructor
  · rintro ⟨w, ⟨hwH, hwK⟩, rfl⟩
    refine ⟨hD ▸ ⟨w, hwH, rfl⟩, fun hx => hwK ⟨_, hx, hc.2.2 w hwH⟩⟩
  · rintro ⟨hxD, hxK⟩
    have hx' : x ∈ c.2.1 '' H := hD.symm ▸ hxD
    obtain ⟨w, hwH, rfl⟩ := hx'
    refine ⟨w, ⟨hwH, ?_⟩, rfl⟩
    rintro ⟨k, hk, hkw⟩
    have hk' : k ∈ c.2.1 '' H := hD.symm ▸ hK hk
    obtain ⟨v, hv, rfl⟩ := hk'
    rw [hc.2.2 v hv] at hkw
    exact hxK (hkw ▸ hk)

/-! ### The record driver has the flow's hull at `s` -/

section Hull

variable {Ω : Type*} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {ω : Ω}

/-- The record driver and the flow driver have the same hull at `s`. -/
theorem fwdHull_record_eq (hW0 : Wα 0 ω = 0) (hWc : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω})
    (hs : (s : ℝ≥0∞) < ζα ω) :
    fwdHull (rdrv (gb6Rec s Wα ζα ω)) s = fwdHull (fun r : ℝ => Wα r.toNNReal ω) s := by
  -- a time strictly between `s` and the lifetime
  obtain ⟨t₂, hst₂, ht₂⟩ : ∃ t₂ : ℝ≥0, s < t₂ ∧ (t₂ : ℝ≥0∞) < ζα ω := by
    obtain ⟨q, hq1, hq2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    exact ⟨q, ENNReal.coe_lt_coe.1 hq1, hq2⟩
  set U₂ : ℝ → ℝ := fun x => Wα (min x.toNNReal t₂) ω with hU₂
  have hU₂c : Continuous U₂ := by
    have hmt : MapsTo (fun x : ℝ => min x.toNNReal t₂) univ {t | (t : ℝ≥0∞) < ζα ω} := fun x _ =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) ht₂
    exact hWc.comp_continuous (continuous_real_toNNReal.min continuous_const) fun x => hmt (mem_univ x)
  have h1 : fwdHull (fun r : ℝ => Wα r.toNNReal ω) s = fwdHull U₂ s := by
    refine fwdHull_eq_of_eqOn s.coe_nonneg (by exact_mod_cast hst₂) fun r hr => ?_
    have : r.toNNReal ≤ t₂ := Real.toNNReal_le_iff_le_coe.2 hr.2
    simp only [hU₂, min_eq_left this]
  have h2 : fwdHull (rdrv (gb6Rec s Wα ζα ω)) s = fwdHull U₂ s := by
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_rdrv _) hU₂c s.coe_nonneg
      fun r hr => ?_
    rw [gb6Rec, rdrv_recOf_cfE s hW0 hWc hs hr.2]
    have : r.toNNReal ≤ t₂ := (Real.toNNReal_le_iff_le_coe.2 hr.2).trans hst₂.le
    simp only [hU₂, min_eq_left this]
  rw [h1, h2]

theorem invHull_record_eq (hW0 : Wα 0 ω = 0) (hWc : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω})
    (hs : (s : ℝ≥0∞) < ζα ω) :
    Q3Rel.invHull (rdrv (gb6Rec s Wα ζα ω)) s = Q3Rel.invHull (fun r : ℝ => Wα r.toNNReal ω) s := by
  unfold Q3Rel.invHull
  rw [fwdHull_record_eq hW0 hWc hs]

end Hull

/-! ### The shape of the physical union -/

section Shape

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **The complement of the physical union is the inverse relative chart image of the complement of the relative
hull**, almost surely on the good event before the stop. -/
theorem ae_compl_union_eq_relChart (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)
    (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ GT → min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      H \ (Q3Rel.invHull (rdrv (gb6Rec s Wα ζα ω)) s ∪ fwdHull (fun r : ℝ => W r.toNNReal ω) t) =
        (relChart (gb6Rec s Wα ζα ω)).2.1 ''
          (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) := by
  filter_upwards [hver.1.2.2.2.2.2.2] with ω hω hωG hlt
  obtain ⟨⟨hWc, hW0, hγ⟩, ⟨h0, hc, hα⟩, hs, hsH, hg, -⟩ := hGT ω hωG
  obtain ⟨-, hreachV, hhull⟩ := hω hs hsH
  obtain ⟨⟨-, hch, -⟩, -, hr⟩ := hg
  -- `t` is before the first contact
  have htc : (t : ℝ≥0∞) < gb6Tc s γ α ω := by
    by_contra hcon
    have hle : gb6Tc s γ α ω ≤ t := le_of_not_gt hcon
    have hV : V ω ≤ physClock s W Wα ζα GT t ω := by
      rw [physClock_eq_iSup hGT hωG]
      refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
      obtain ⟨t', ht', hut'⟩ := hreachV u hu
      have ht't : t' < t := by
        have := lt_of_lt_of_le ht' hle
        exact_mod_cast this
      refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < gb6Tc s γ α ω) =>
        ENNReal.ofReal (gb6Clock s W Wα ω t')) t' ⟨ht't, ht'⟩)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hut'.le
    rw [min_eq_right hV] at hlt
    exact lt_irrefl _ hlt
  -- the clock at `t`
  have hphys := physClock_eq_gb6Clock hGT hωG htc
  obtain ⟨ha0, hsm, -⟩ := relClock_props_of_traces hα hc h0 hs hsH hγ hWc hW0
  have hnn : 0 ≤ gb6Clock s W Wα ω t := by
    have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < gb6Tc s γ α ω := lt_of_le_of_lt bot_le htc
    have := hsm.monotoneOn h0T htc (bot_le : (0 : ℝ≥0) ≤ t)
    have e0 : relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) ((0 : ℝ≥0) : ℝ) = 0 := by
      rw [NNReal.coe_zero]; exact ha0
    rw [e0] at this
    exact this
  have hlt' : ENNReal.ofReal (gb6Clock s W Wα ω t) < V ω := by
    rw [hphys] at hlt
    exact lt_of_not_ge fun h => lt_irrefl _ (by rwa [min_eq_right h] at hlt)
  have hmin : min (physClock s W Wα ζα GT t ω) (V ω) = ENNReal.ofReal (gb6Clock s W Wα ω t) := by
    rw [hphys]
    exact min_eq_left hlt'.le
  have hreal : (((ENNReal.ofReal (gb6Clock s W Wα ω t)).toNNReal : ℝ≥0) : ℝ) = gb6Clock s W Wα ω t := by
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hnn]
  have hH := hhull t htc hlt'.le
  rw [hmin, hreal, hH]
  -- the relative chart of the record
  have hw := continuous_rdrv (gb6Rec s Wα ζα ω)
  have hw0 := rdrv_zero (gb6Rec s Wα ζα ω)
  have hrel : relMap (fun r : ℝ => Wα r.toNNReal ω) s = relMap (rdrv (gb6Rec s Wα ζα ω)) s := by
    funext z
    change (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s).1 (-z⁻¹) =
      (ownComponentChart (rdrv (gb6Rec s Wα ζα ω)) s).1 (-z⁻¹)
    rw [hch]
  rw [hrel, relChart_eq_jointChart hr,
    show relMap (rdrv (gb6Rec s Wα ζα ω)) s = (jointChart (rdrv (gb6Rec s Wα ζα ω)) s).1 from rfl]
  have hdc := Q3Rel.isDomainChart_rel hw hw0 s.coe_nonneg
  -- the counterflow hull misses the retained set
  have hdis := disjoint_closure_fwdHull_of_lt_firstContactTime hα hc h0 hγ hWc.continuousOn hW0 hs
    ENNReal.coe_lt_top htc
  rw [← fwdHull_record_eq h0 hc hs] at hdis
  have hdis' := Q3Rel.disjoint_closure_invHull hw s.coe_nonneg hdis
  have hK : fwdHull (fun r : ℝ => W r.toNNReal ω) t ⊆ H \ Q3Rel.invHull (rdrv (gb6Rec s Wα ζα ω)) s := by
    intro z hz
    refine ⟨(isHPHull_fwdHull (hWc.comp continuous_real_toNNReal) t.coe_nonneg).1 hz, fun hzA => ?_⟩
    exact Set.disjoint_left.1 hdis' (subset_closure hz) (subset_closure hzA)
  rw [image_inv_compl_image_fwd hdc.1 hdc.2.1 hK, Set.sdiff_sdiff]

end Shape

end InteractingSLE.Supp8.RelSafeS
