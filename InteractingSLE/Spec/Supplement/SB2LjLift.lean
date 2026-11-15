/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LjRule

/-!
# SB2(2): the lift relation at a concrete relative stage

Packet PROVE-SB2-LIFTSET (round 12). `liftRel_of_stage` applied to the concrete rule (`SB2LjRule`): a relative driver
generating the concrete stage curve (as `exists_EL_concrete` gives on the driven events) launches the lift of the
actual piece.

* `isGeneratingTrace_of_forall_lt`: generation below every earlier horizon, continuity through the lifetime and the
  start give generation at the lifetime (the hull condition is only asked strictly before it);
* **`liftRel_of_stage_cl`**: `liftRel_of_stage` with the bookkeeping identity weakened to two inclusions (the values at
  good times lie in the lift target, which lies in their closure) — the endpoint of a finite piece is not a value of
  the clock `clockOf L` but a limit;
* `cTm` (the actual time `clockOf L (capInv ρ τ)` of relative capacity time `τ`), `cGd` (the relative good times);
* **`liftRel_concrete`**: at a finite actual piece, the relative piece launched with a driver generating the stage
  curve is the lift of the actual one, given the chart facts, the actual piece's tip set as the image of its points,
  the lifted good points in the relative chart's domain, and density/cover of the good times. The value identity
  `hval` of `liftRel_of_stage` is **proved** from the definition of the stage curve (`stVal` is `relVal` at good
  times) and the relative chart's inverse identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- **Generation at the lifetime from generation below it**: the hull condition of `IsGeneratingTrace` is only asked
strictly before the horizon. -/
theorem isGeneratingTrace_of_forall_lt {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (h : ∀ T' < T, IsGeneratingTrace w T' η) (h0 : η 0 = 0) (hc : ContinuousOn η {t | (t : ℝ≥0∞) ≤ T}) :
    IsGeneratingTrace w T η := by
  refine ⟨h0, hc, fun t ht => ?_⟩
  obtain ⟨T', htT', hT'⟩ := exists_between ht
  exact (h T' hT').2.2 t htT'

/-- **The lift relation at one stage, closure form** (finite lifetime): as `liftRel_of_stage`, with the bookkeeping
identity replaced by `v '' Gd ⊆ T ⊆ closure (v '' Gd)` for the lift target `T`. -/
theorem liftRel_of_stage_cl {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w)
    (hoff : BdryOff c) {q₁ : Pc} (hTc : IsCompact {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2} ⊆
      closure {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H})
    {s : ExplState} {e : Drv} {α : ℝ≥0 → ℂ} {f : ℂ → ℂ} (hα : IsGeneratingTrace e.1 e.2 α)
    (hW : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ e.2}) (hW0 : e.1 0 = 0)
    (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 → Tendsto (stChart s).2.1 (𝓝[H] (α t)) (𝓝 (f (α t))))
    (hfin : e.2 ≠ ⊤) (hgc : ContinuousOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ e.2})
    {Gd : Set ℝ≥0} {v : ℝ≥0 → ℂ} (hGd : Gd ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2})
    (hdense₂ : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} ⊆ closure Gd) (hval : ∀ t ∈ Gd, f (α t) = v t)
    (hv₁ : v '' Gd ⊆ liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL))
    (hv₂ : liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL) ⊆ closure (v '' Gd)) :
    LiftRel β₀ tL γ q₁ (newPc s e) := by
  have hK : IsCompact {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} := by
    have e' : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} = Iic e.2.toNNReal := by
      ext t
      simp only [mem_ofPred_eq, mem_Iic]
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
    rw [e', ← Icc_bot]
    exact isCompact_Icc
  refine liftRel_of_closure hγ hcH hc1 hoff hTc hdense₁ ?_
  rw [tipSet_newPc_eq hα hW hW0 hc, image_image, image_eq_closure_of_dense hK hgc hGd hdense₂,
    image_congr hval]
  exact Subset.antisymm (closure_mono hv₁) (closure_minimal hv₂ isClosed_closure)

/-- The actual time `clockOf L (capInv ρ τ)` of relative capacity time `τ` (`ρ` the stage curve, `L` the actual
lifetime). -/
def cTm (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (τ : ℝ≥0) : ℝ≥0 :=
  (clockOf e₁.2.toReal (capInv (stCurve c m s₁ e₁ s₂) τ)).toNNReal

/-- The relative good times: before the relative lifetime, with good actual time. -/
def cGd (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (e₂ : Drv) : Set ℝ≥0 :=
  {τ | (τ : ℝ≥0∞) < e₂.2 ∧ cTm c m s₁ e₁ s₂ τ ∈ goodT c s₁ e₁}

/-- **The lift relation at a concrete relative stage** (finite actual piece): a relative driver `e₂` generating the
stage curve `stCurve c m s₁ e₁ s₂` below its capacity lifetime launches, from `s₂`, the lift of the actual piece
launched from `s₁` with `e₁`. The value identity of `liftRel_of_stage` is proved from the stage curve's definition and
the relative chart's inverse identity on its domain. -/
theorem liftRel_concrete {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w)
    (hoff : BdryOff c) {s₁ s₂ : ExplState} {e₁ e₂ : Drv}
    (hTc : IsCompact {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
      closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H})
    (htip₁ : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 =
      pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (he₁ : e₁.2 ≠ ⊤) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H)
    (hdense₂ : {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} ⊆ closure (cGd c m s₁ e₁ s₂ e₂))
    (hcov : liftPt c m '' (pcPt s₁ e₁ '' goodT c s₁ e₁) ⊆
      closure ((fun τ => liftPt c m (pcPt s₁ e₁ (cTm c m s₁ e₁ s₂ τ))) '' cGd c m s₁ e₁ s₂ e₂)) :
    LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) := by
  have hα : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T', htT', hT'⟩ := exists_between ht
    have h := (hgen T' (by rw [← he₂]; exact hT')).2.2 t htT'
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  refine liftRel_of_stage_cl hγ hcH hc1 hoff hTc hdense₁ hα hW hW0 hc hfin hgc (fun τ h => le_of_lt h.1) hdense₂
    (v := fun τ => liftPt c m (pcPt s₁ e₁ (cTm c m s₁ e₁ s₂ τ))) ?_ ?_ ?_
  · rintro τ ⟨hτ, hg⟩
    obtain ⟨z, hz, hzw⟩ := hdom _ hg
    have hατ : α τ = z := by
      rw [hαeq τ hτ]
      show stCurve c m s₁ e₁ s₂ (capInv (stCurve c m s₁ e₁ s₂) τ) = z
      rw [stCurve_of_fin he₁]
      change stVal c m s₁ e₁ s₂ (cTm c m s₁ e₁ s₂ τ) = z
      rw [stVal_of_good hg]
      unfold relVal
      rw [← hzw, hc1₂ z hz]
    have hlim := hc τ (le_of_lt hτ)
    rw [hατ] at hlim
    have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hz)
    rw [hατ, tendsto_nhds_unique hlim (hcH₂ z hz), hzw]
  · rintro _ ⟨τ, ⟨-, hg⟩, rfl⟩
    have hmem : pcPt s₁ e₁ (cTm c m s₁ e₁ s₂ τ) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 := by
      rw [htip₁]
      exact ⟨_, hg.1, rfl⟩
    exact ⟨_, ⟨⟨hmem, hg.2⟩, htail ⟨hmem, hg.2⟩⟩, rfl⟩
  · rintro _ ⟨p, ⟨⟨hp, hpD⟩, -⟩, rfl⟩
    rw [htip₁] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact hcov ⟨_, ⟨t, ⟨ht, hpD⟩, rfl⟩, rfl⟩

end InteractingSLE.Theorem14.SB.Lk
