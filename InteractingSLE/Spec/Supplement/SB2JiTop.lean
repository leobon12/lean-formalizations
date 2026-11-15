/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JiClock

/-!
# SB2(2): the lift relation at a concrete stage for a driven stage curve, finite or infinite lifetime

Packet PROVE-SB2-LIFTSET (round 13).

* `image_eq_closure_of_closed`, **`liftRel_of_stage_closed`**: `liftRel_of_stage_cl` with compactness of the parameter
  interval replaced by closedness of the image (an infinite, transient piece: the boundary image of `[0, ∞)` is
  closed);
* **`liftRel_concrete_driven`** (finite actual lifetime): `liftRel_concrete` with the capacity bookkeeping discharged by
  `hcov_of_driven`, `hdense_of_driven` — the remaining hypotheses concern the upper chart, the actual piece (tip set,
  tail, compact and dense tail times, dense good times, the lifted endpoint), the relative chart and the generated
  trace's endpoint extension;
* **`liftRel_concrete_top`** (infinite actual lifetime): the same with `cTmTop`, `cGdTop`, `hcov_top`, `hdense_top`
  and closedness of the relative boundary image.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- The image of a parameter set with closed image is the closure of the values at dense good parameters. -/
theorem image_eq_closure_of_closed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {g : X → Y}
    {K Gd : Set X} (hcl : IsClosed (g '' K)) (hg : ContinuousOn g K) (hGd : Gd ⊆ K) (hdense : K ⊆ closure Gd) :
    g '' K = closure (g '' Gd) := by
  refine Subset.antisymm ?_ (hcl.closure_subset_iff.2 (image_mono hGd))
  rintro _ ⟨x, hx, rfl⟩
  exact ((hg x hx).mono hGd).mem_closure_image (hdense hx)

/-- **The lift relation at one stage, closed-image form**: as `liftRel_of_stage_cl`, with the closedness of the
relative boundary image in place of a finite lifetime. -/
theorem liftRel_of_stage_closed {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w)
    (hoff : BdryOff c) {q₁ : Pc} (hTc : IsCompact {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2} ⊆
      closure {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H})
    {s : ExplState} {e : Drv} {α : ℝ≥0 → ℂ} {f : ℂ → ℂ} (hα : IsGeneratingTrace e.1 e.2 α)
    (hW : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ e.2}) (hW0 : e.1 0 = 0)
    (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 → Tendsto (stChart s).2.1 (𝓝[H] (α t)) (𝓝 (f (α t))))
    (hclosed : IsClosed ((fun t => f (α t)) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2}))
    (hgc : ContinuousOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ e.2})
    {Gd : Set ℝ≥0} {v : ℝ≥0 → ℂ} (hGd : Gd ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2})
    (hdense₂ : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} ⊆ closure Gd) (hval : ∀ t ∈ Gd, f (α t) = v t)
    (hv₁ : v '' Gd ⊆ liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL))
    (hv₂ : liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL) ⊆ closure (v '' Gd)) :
    LiftRel β₀ tL γ q₁ (newPc s e) := by
  refine liftRel_of_closure hγ hcH hc1 hoff hTc hdense₁ ?_
  rw [tipSet_newPc_eq hα hW hW0 hc, image_image, image_eq_closure_of_closed hclosed hgc hGd hdense₂,
    image_congr hval]
  exact Subset.antisymm (closure_mono hv₁) (closure_minimal hv₂ isClosed_closure)

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₁ s₂ : ExplState} {e₁ e₂ : Drv}

/-- Generation at the relative lifetime by an endpoint extension of the capacity trace. -/
theorem isGeneratingTrace_ext {ρ : ℝ → ℂ} (he₂ : e₂.2 = capLife ρ)
    (hgen : ∀ T < capLife ρ, IsGeneratingTrace e₂.1 T (capTrace ρ)) {α : ℝ≥0 → ℂ}
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) (hα0 : α 0 = 0)
    (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) : IsGeneratingTrace e₂.1 e₂.2 α := by
  refine ⟨hα0, hαc, fun t ht => ?_⟩
  obtain ⟨T', htT', hT'⟩ := exists_between ht
  have h := (hgen T' (by rw [← he₂]; exact hT')).2.2 t htT'
  rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]

/-- **The lift relation at a concrete stage, driven stage curve, finite actual lifetime**: `liftRel_concrete` with
the capacity bookkeeping (`hdense₂`, `hcov`) discharged by the drivenness of the stage curve. -/
theorem liftRel_concrete_driven (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    (hTc : IsCompact {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
      closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H})
    (htip₁ : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 =
      pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (he₁ : e₁.2 ≠ ⊤) (hpos : e₁.2 ≠ 0) (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁))
    (hend : ∀ t ∈ goodT c s₁ e₁, (t : ℝ≥0∞) = e₁.2 → liftPt c m (pcPt s₁ e₁ t) ∈
      closure ((fun t' => liftPt c m (pcPt s₁ e₁ t')) '' (goodT c s₁ e₁ ∩ {t' | (t' : ℝ≥0∞) < e₁.2}))) :
    LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) :=
  liftRel_concrete hγ hcH hc1 hoff hTc hdense₁ htip₁ htail he₁ he₂ hgen hfin hW hW0 hαeq hα0 hαc hc hgc hcH₂ hc1₂
    hdom (hdense_of_driven hρ he₂ he₁ hpos hgd) (hcov_of_driven hρ he₂ he₁ hend)

/-- **The lift relation at a concrete stage, driven stage curve, infinite actual lifetime**: the relative piece
launched with a driver generating the stage curve is the lift of the actual (infinite) piece; the relative boundary
image is assumed closed (transience). -/
theorem liftRel_concrete_top (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    (hTc : IsCompact {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
      closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H})
    (htip₁ : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 =
      pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (he₁ : e₁.2 = ⊤) (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hclosed : IsClosed ((fun τ => f (α τ)) '' {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2}))
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) :
    LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) := by
  have hα := isGeneratingTrace_ext he₂ hgen hαeq hα0 hαc
  refine liftRel_of_stage_closed hγ hcH hc1 hoff hTc hdense₁ hα hW hW0 hc hclosed hgc
    (fun τ h => le_of_lt h.1) (hdense_top hρ he₂ he₁ hgd)
    (v := fun τ => liftPt c m (pcPt s₁ e₁ (cTmTop c m s₁ e₁ s₂ τ))) ?_ ?_ ?_
  · rintro τ ⟨hτ, hg⟩
    obtain ⟨z, hz, hzw⟩ := hdom _ hg
    have hατ : α τ = z := by
      rw [hαeq τ hτ]
      show stCurve c m s₁ e₁ s₂ (capInv (stCurve c m s₁ e₁ s₂) τ) = z
      rw [stCurve_of_top he₁]
      change stVal c m s₁ e₁ s₂ (cTmTop c m s₁ e₁ s₂ τ) = z
      rw [stVal_of_good hg]
      unfold relVal
      rw [← hzw, hc1₂ z hz]
    have hlim := hc τ (le_of_lt hτ)
    rw [hατ] at hlim
    have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hz)
    rw [hατ, tendsto_nhds_unique hlim (hcH₂ z hz), hzw]
  · rintro _ ⟨τ, ⟨-, hg⟩, rfl⟩
    have hmem : pcPt s₁ e₁ (cTmTop c m s₁ e₁ s₂ τ) ∈
        (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 := by
      rw [htip₁]
      exact ⟨_, hg.1, rfl⟩
    exact ⟨_, ⟨⟨hmem, hg.2⟩, htail ⟨hmem, hg.2⟩⟩, rfl⟩
  · rintro _ ⟨p, ⟨⟨hp, hpD⟩, -⟩, rfl⟩
    rw [htip₁] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact hcov_top hρ he₂ ⟨_, ⟨t, ⟨ht, hpD⟩, rfl⟩, rfl⟩

end InteractingSLE.Theorem14.SB.Lk
