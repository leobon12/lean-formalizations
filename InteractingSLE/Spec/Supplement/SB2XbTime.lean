/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LjLift
import InteractingSLE.Spec.Supplement.SB2LkFree
import InteractingSLE.Spec.Supplement.GW4LeafPiece
import InteractingSLE.Spec.Sec7.PocketLife

/-!
# The lift of a concrete relative piece at every time (the per-time trace lift of `FillCorr`)

Packet PROVE-T14-SB2LIFT (round 23). `FillCorr`'s second half (rounds 11–19) compares the two pieces strictly before
their stops, so it needs the relative trace up to `r'` to be the lift of the actual trace up to a matching `r`
(`htr₁`, `htr₂` of `fillCorr_of_stage`). PROVE-SB2-LIFTSET's concrete rule (`SB2LjRule`) gives this at every time,
not only at the stop (`liftRel_concrete`): the relative driver generates the capacity reparametrization of the stage
curve `ρ = stCurve`, whose value at `u` is the intrinsic lift of the actual piece at the actual time `clockOf L u`.

* **`continuousOn_pcPt`**: the actual piece's points depend continuously on the time (a chart with a proper boundary
  extension along a regular trace);
* **`lift_eq_stage`**: for every actual time `t < L` and every tail time `s` of the actual point `pcPt t`, the lift
  curve at `s` is the relative boundary value at the capacity time `φ t = capClock ρ (t / (L − t))`. At good times this
  is the stage curve's definition; elsewhere it follows by continuity along the dense good times (the tail times of
  nearby good points converge, `β₀` being a closed embedding);
* **`image_eq_liftImage_stage`**: hence the relative trace up to `φ r` is the lift of the actual trace up to `r`;
* **`trLift_concrete`**: the per-time lift `htr₁ ∧ htr₂`, from the hypotheses of PROVE-SB2-LIFTSET's per-stage
  geometry at a finite piece (`StageGeomFin` of its `SB2JiGeom`, field by field), the drivenness of the stage curve,
  generation below the capacity lifetime, a regular actual piece and a chart with a proper boundary extension.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- The inverse of the reparametrization `clockOf L`. -/
theorem div_sub_clockOf {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u) : clockOf L u / (L - clockOf L u) = u := by
  unfold clockOf
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : L - L * (u / (1 + u)) = L / (1 + u) := by field_simp; ring
  rw [h2]
  field_simp

/-- **The points of a regular piece depend continuously on the time** in a chart with a proper boundary extension. -/
theorem continuousOn_pcPt {s : ExplState} {e : Drv} (hc : GW1P.HasProperBdryExt (stChart s))
    (hr : GW1P.PieceRegular e.1 e.2) : ContinuousOn (pcPt s e) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} := by
  obtain ⟨f, C, hf, -⟩ := hc
  have hα := LuM.isGeneratingTrace_trOf hr
  have hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 → LuM.trOf e t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hr.2.1.mono fun _ (hs : _ < e.2) => (le_of_lt hs : _ ≤ e.2)) hr.1 ht
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  refine (hfc.comp hα.2.1 fun t ht => hH t ht).congr fun t ht => ?_
  exact LuM.bdVal_eq_of_tendsto (hH t ht) (hf _ (hH t ht))

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The lift curve along the actual piece is the relative boundary value at the matching capacity time.** For an
actual time `t < L` (`L` the finite actual lifetime) and a tail time `s` of `pcPt t`, `γ s = f (α (φ t))` with
`φ t = capClock ρ (t / (L − t))`; moreover every such point is on the tail. -/
theorem lift_eq_stage (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀)
    (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {L₁ : ℝ≥0} (hL₁ : e₁.2 = L₁)
    (hPc : ContinuousOn (pcPt s₁ e₁) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htip₁ : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 =
      pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) :
    (∀ t : ℝ≥0, t < L₁ → pcPt s₁ e₁ t ∈ β₀ '' Ici tL) ∧
    ∀ t : ℝ≥0, t < L₁ → ∀ s : ℝ≥0, β₀ (tL + s) = pcPt s₁ e₁ t →
      γ s = f (α (capClock (stCurve c m s₁ e₁ s₂) ((t : ℝ) / (L₁ - t))).toNNReal) := by
  set ρ := stCurve c m s₁ e₁ s₂ with hρdef
  set φ : ℝ≥0 → ℝ := fun t => capClock ρ ((t : ℝ) / (L₁ - t)) with hφdef
  have he₁ : e₁.2 ≠ ⊤ := by rw [hL₁]; exact ENNReal.coe_ne_top
  have hℓ : e₁.2.toReal = L₁ := by rw [hL₁]; rfl
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e₁.2 ↔ t < L₁ := fun t => by rw [hL₁]; exact ENNReal.coe_lt_coe
  have hu0 : ∀ t : ℝ≥0, t < L₁ → 0 ≤ (t : ℝ) / (L₁ - t) := fun t ht =>
    div_nonneg t.2 (sub_nonneg.2 (NNReal.coe_le_coe.2 ht.le))
  have hφ0 : ∀ t : ℝ≥0, t < L₁ → 0 ≤ φ t ∧ ENNReal.ofReal (φ t) < e₂.2 := fun t ht =>
    ⟨hρ.capClock_nonneg (hu0 t ht), by rw [he₂]; exact hρ.ofReal_capClock_lt (hu0 t ht)⟩
  -- the stage identity at good times
  have hgood : ∀ t ∈ goodT c s₁ e₁, t < L₁ → f (α (φ t).toNNReal) = liftPt c m (pcPt s₁ e₁ t) := by
    intro t hg ht
    obtain ⟨hφn, hφl⟩ := hφ0 t ht
    obtain ⟨z, hz, hzw⟩ := hdom t hg
    have hτ : (((φ t).toNNReal : ℝ≥0) : ℝ≥0∞) < e₂.2 := hφl
    have hαz : α (φ t).toNNReal = z := by
      rw [hαeq _ hτ]
      show ρ (capInv ρ (((φ t).toNNReal : ℝ≥0) : ℝ)) = z
      rw [Real.coe_toNNReal _ hφn, hφdef, hρ.capInv_eq (hu0 t ht), hρdef, stCurve_of_fin he₁, hℓ,
        Sec7.PocketLife.clockOf_div_sub (NNReal.coe_pos.2 (lt_of_le_of_lt zero_le ht))
          (NNReal.coe_lt_coe.2 ht), Real.toNNReal_coe, stVal_of_good hg]
      unfold relVal
      rw [← hzw, hc1₂ z hz]
    have hlim := hc _ hτ.le
    rw [hαz] at hlim
    have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hz)
    rw [hαz, tendsto_nhds_unique hlim (hcH₂ z hz), hzw]
  -- every point of the piece before the stop is on the tail
  have hβe := isClosedEmbedding_of_isProperCurve hβ
  have hcl : IsClosed (β₀ '' Ici tL) := hβe.isClosedMap _ isClosed_Ici
  have hgt : ∀ t ∈ goodT c s₁ e₁, pcPt s₁ e₁ t ∈ β₀ '' Ici tL := fun t hg => by
    refine htail ⟨?_, hg.2⟩
    rw [htip₁]
    exact ⟨t, hg.1, rfl⟩
  have hgoodsub : goodT c s₁ e₁ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2} := fun t hg => hg.1
  have htl : ∀ t : ℝ≥0, t < L₁ → pcPt s₁ e₁ t ∈ β₀ '' Ici tL := fun t ht => by
    have hmem : t ∈ closure (goodT c s₁ e₁) := hgd ((hlt t).2 ht)
    have hcw : ContinuousWithinAt (pcPt s₁ e₁) (goodT c s₁ e₁) t :=
      (hPc t ((hlt t).2 ht).le).mono hgoodsub
    have hsub : pcPt s₁ e₁ '' goodT c s₁ e₁ ⊆ β₀ '' Ici tL := by
      rintro _ ⟨t', ht', rfl⟩
      exact hgt t' ht'
    exact hcl.closure_subset_iff.2 hsub (hcw.mem_closure_image hmem)
  refine ⟨htl, fun t ht s hs => ?_⟩
  -- the filter of good times before the stop, near `t`
  set G := Iio L₁ ∩ goodT c s₁ e₁ with hG
  have hGsub : G ⊆ {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ e₁.2} := fun t' h => hgoodsub h.2
  have hmem : t ∈ closure G :=
    isOpen_Iio.inter_closure (show t ∈ Iio L₁ ∩ closure (goodT c s₁ e₁) from ⟨ht, hgd ((hlt t).2 ht)⟩)
  have : (𝓝[G] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hmem
  -- tail times of the good points
  classical
  set sel : ℝ≥0 → ℝ≥0 := fun t' => if h : ∃ s' : ℝ≥0, β₀ (tL + s') = pcPt s₁ e₁ t' then h.choose else 0
    with hsel
  have hsel_spec : ∀ t' ∈ G, β₀ (tL + sel t') = pcPt s₁ e₁ t' := fun t' h => by
    have hex : ∃ s' : ℝ≥0, β₀ (tL + s') = pcPt s₁ e₁ t' := by
      obtain ⟨x, hx, hxe⟩ := hgt t' h.2
      exact ⟨x - tL, by rw [add_tsub_cancel_of_le (show tL ≤ x from hx)]; exact hxe⟩
    simp only [hsel, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hP : Tendsto (pcPt s₁ e₁) (𝓝[G] t) (𝓝 (pcPt s₁ e₁ t)) :=
    ((hPc t ((hlt t).2 ht).le).mono hGsub).tendsto
  have hβt : Tendsto (fun t' => β₀ (tL + sel t')) (𝓝[G] t) (𝓝 (β₀ (tL + s))) := by
    rw [hs]
    exact hP.congr' (eventually_nhdsWithin_of_forall fun t' h => (hsel_spec t' h).symm)
  have hst : Tendsto (fun t' => tL + sel t') (𝓝[G] t) (𝓝 (tL + s)) :=
    hβe.isInducing.tendsto_nhds_iff.2 hβt
  have hs' : Tendsto sel (𝓝[G] t) (𝓝 s) := by
    have := hst.sub (tendsto_const_nhds (x := tL))
    simpa only [add_tsub_cancel_left] using this
  have h1 : Tendsto (fun t' => γ (sel t')) (𝓝[G] t) (𝓝 (γ s)) := (hγ.2.1.1.tendsto s).comp hs'
  -- the relative boundary values along the good times
  have hφc : ContinuousWithinAt (fun t' : ℝ≥0 => (φ t').toNNReal) (Iio L₁) t := by
    have hden : ((L₁ : ℝ) - t) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_coe.2 ht)).ne'
    have hq : ContinuousAt (fun t' : ℝ≥0 => (t' : ℝ) / (L₁ - t')) t :=
      (NNReal.continuous_coe.continuousAt).div (continuous_const.sub NNReal.continuous_coe).continuousAt hden
    have hcc : ContinuousWithinAt (capClock ρ) (Ici 0) ((t : ℝ) / (L₁ - t)) :=
      hρ.continuousOn_capClock _ (hu0 t ht)
    have hcomp : ContinuousWithinAt (fun t' : ℝ≥0 => capClock ρ ((t' : ℝ) / (L₁ - t'))) (Iio L₁) t :=
      ContinuousWithinAt.comp (f := fun t' : ℝ≥0 => (t' : ℝ) / (L₁ - t')) hcc hq.continuousWithinAt
        fun t' (h : t' ∈ Iio L₁) => hu0 t' h
    exact continuous_real_toNNReal.continuousAt.comp_continuousWithinAt hcomp
  have hmaps : MapsTo (fun t' : ℝ≥0 => (φ t').toNNReal) (Iio L₁) {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} :=
    fun t' h => (hφ0 t' h).2.le
  have h2 : Tendsto (fun t' => f (α (φ t').toNNReal)) (𝓝[G] t) (𝓝 (f (α (φ t).toNNReal))) :=
    ((ContinuousWithinAt.comp (g := fun τ => f (α τ)) (f := fun t' : ℝ≥0 => (φ t').toNNReal) (hgc _ (hmaps ht))
      hφc hmaps).mono inter_subset_left).tendsto
  have h2' : Tendsto (fun t' => γ (sel t')) (𝓝[G] t) (𝓝 (f (α (φ t).toNNReal))) := by
    refine h2.congr' (eventually_nhdsWithin_of_forall fun t' h => ?_)
    have hl := lift_mem_H_iff hγ hcH hc1 hoff (sel t')
    have hD : β₀ (tL + sel t') ∈ c.2.1 '' H := by rw [hsel_spec t' h]; exact h.2.2
    show f (α (φ t').toNNReal) = γ (sel t')
    rw [hl.2 (hl.1.1 hD), hsel_spec t' h, hgood t' h.2 h.1]
  exact tendsto_nhds_unique h1 h2'

/-- The capacity time of the actual time `t < L` is continuous in `t`. -/
theorem continuousOn_capClock_div {ρ : ℝ → ℂ} (hρ : IsDrivenCurve ρ) (L₁ : ℝ≥0) :
    ContinuousOn (fun t : ℝ≥0 => capClock ρ ((t : ℝ) / (L₁ - t))) (Iio L₁) := by
  have hu0 : ∀ t : ℝ≥0, t < L₁ → 0 ≤ (t : ℝ) / (L₁ - t) := fun t ht =>
    div_nonneg t.2 (sub_nonneg.2 (NNReal.coe_le_coe.2 ht.le))
  intro t ht
  have hden : ((L₁ : ℝ) - t) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_coe.2 ht)).ne'
  have hq : ContinuousAt (fun t' : ℝ≥0 => (t' : ℝ) / (L₁ - t')) t :=
    (NNReal.continuous_coe.continuousAt).div (continuous_const.sub NNReal.continuous_coe).continuousAt hden
  exact ContinuousWithinAt.comp (f := fun t' : ℝ≥0 => (t' : ℝ) / (L₁ - t'))
    (hρ.continuousOn_capClock _ (hu0 t ht)) hq.continuousWithinAt fun t' (h : t' ∈ Iio L₁) => hu0 t' h

/-- **The relative trace up to `φ r` is the lift of the actual trace up to `r`** (`r < L`, `φ` as in
`lift_eq_stage`). -/
theorem image_eq_liftImage_stage (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀)
    (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {L₁ : ℝ≥0} (hL₁ : e₁.2 = L₁)
    (hPc : ContinuousOn (pcPt s₁ e₁) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htip₁ : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 =
      pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) {r : ℝ≥0} (hr : r < L₁) :
    LuM.bdVal (stChart s₂) '' (LuM.trOf e₂ ''
        Icc 0 (capClock (stCurve c m s₁ e₁ s₂) ((r : ℝ) / (L₁ - r))).toNNReal) =
      liftImage β₀ tL γ (LuM.bdVal (stChart s₁) '' (LuM.trOf e₁ '' Icc 0 r)) := by
  set ρ := stCurve c m s₁ e₁ s₂ with hρdef
  set φ : ℝ≥0 → ℝ := fun t => capClock ρ ((t : ℝ) / (L₁ - t)) with hφdef
  obtain ⟨hTl, hKey⟩ := lift_eq_stage hγ hβ hcH hc1 hoff hL₁ hPc htip₁ htail hρ he₂ hαeq hc hgc hcH₂ hc1₂ hdom hgd
  have hu0 : ∀ t : ℝ≥0, t < L₁ → 0 ≤ (t : ℝ) / (L₁ - t) := fun t ht =>
    div_nonneg t.2 (sub_nonneg.2 (NNReal.coe_le_coe.2 ht.le))
  -- the relative trace is `α`
  have hαg : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T', htT', hT'⟩ := exists_between ht
    have h := (hgen T' (by rw [← he₂]; exact hT')).2.2 t htT'
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  have hWlt : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) < e₂.2} :=
    hW.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hpr₂ : GW1P.PieceRegular e₂.1 e₂.2 := ⟨hW0, hW, α, hαg, fun h => absurd h hfin⟩
  have hbd₂ : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → LuM.bdVal (stChart s₂) (LuM.trOf e₂ τ) = f (α τ) := by
    intro τ hτ
    rw [GW4Leaf.eqOn_of_isGeneratingTrace hαg (LuM.isGeneratingTrace_trOf hpr₂) hWlt hW0 τ hτ]
    exact LuM.bdVal_eq_of_tendsto (Sec7.IsGeneratingTrace.mem_Hbar hαg hWlt hW0 hτ) (hc τ hτ)
  have hφr0 : 0 ≤ φ r := hρ.capClock_nonneg (hu0 r hr)
  have hφrl : ENNReal.ofReal (φ r) < e₂.2 := by rw [he₂]; exact hρ.ofReal_capClock_lt (hu0 r hr)
  -- the capacity times of `[0, r]` fill `[0, φ r]`
  have hmono : ∀ t : ℝ≥0, t ≤ r → φ t ≤ φ r := fun t ht => by
    have htL : t < L₁ := lt_of_le_of_lt ht hr
    have hq : (t : ℝ) / (L₁ - t) ≤ (r : ℝ) / (L₁ - r) :=
      div_le_div₀ r.2 (NNReal.coe_le_coe.2 ht) (sub_pos.2 (NNReal.coe_lt_coe.2 hr))
        (by have := NNReal.coe_le_coe.2 ht; linarith)
    exact hρ.strictMonoOn_capClock.monotoneOn (hu0 t htL) (hu0 r hr) hq
  have hφ0 : φ 0 = 0 := by
    simp only [hφdef, NNReal.coe_zero, zero_div]
    exact hρ.capClock_zero
  have himg : (fun t => (φ t).toNNReal) '' Icc 0 r = Icc 0 (φ r).toNNReal := by
    ext τ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨zero_le, Real.toNNReal_le_toNNReal (hmono t ht.2)⟩
    · rintro ⟨-, hτ⟩
      have hτ' : (τ : ℝ) ∈ Icc (φ 0) (φ r) := by
        rw [hφ0]
        refine ⟨τ.2, ?_⟩
        have := NNReal.coe_le_coe.2 hτ
        rwa [Real.coe_toNNReal _ hφr0] at this
      have hcont : ContinuousOn φ (Icc 0 r) :=
        (continuousOn_capClock_div hρ L₁).mono fun t ht => lt_of_le_of_lt ht.2 hr
      obtain ⟨t, ht, hte⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ r) hcont hτ'
      exact ⟨t, ht, show (φ t).toNNReal = τ by rw [hte, Real.toNNReal_coe]⟩
  -- both sides are the relative boundary values at the capacity times of `[0, r]`
  have hL : LuM.bdVal (stChart s₂) '' (LuM.trOf e₂ '' Icc 0 (φ r).toNNReal) =
      (fun t => f (α (φ t).toNNReal)) '' Icc 0 r := by
    rw [image_image, ← himg, image_image]
    refine image_congr fun t ht => hbd₂ _ ?_
    exact (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal (hmono t ht.2))).trans hφrl.le
  have hR : liftImage β₀ tL γ (LuM.bdVal (stChart s₁) '' (LuM.trOf e₁ '' Icc 0 r)) =
      (fun t => f (α (φ t).toNNReal)) '' Icc 0 r := by
    rw [image_image]
    ext z
    constructor
    · rintro ⟨s, ⟨t, ht, hts⟩, rfl⟩
      exact ⟨t, ht, (hKey t (lt_of_le_of_lt ht.2 hr) s hts.symm).symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x, hx, hxe⟩ := hTl t (lt_of_le_of_lt ht.2 hr)
      have hs : β₀ (tL + (x - tL)) = pcPt s₁ e₁ t := by
        rw [add_tsub_cancel_of_le (show tL ≤ x from hx)]; exact hxe
      exact ⟨x - tL, ⟨t, ht, hs.symm⟩, hKey t (lt_of_le_of_lt ht.2 hr) _ hs⟩
  rw [hL, hR]

/-- **The per-time lift at a concrete relative stage** (finite positive actual lifetime): every initial part of the
actual piece before its stop has, as its lift, an initial part of the relative piece before its stop, and conversely
(`htr₁`, `htr₂` of `fillCorr_of_stage`). The hypotheses are those of PROVE-SB2-LIFTSET's per-stage geometry at a
finite piece, the drivenness of the stage curve and generation below its capacity lifetime, a regular actual piece and
an actual chart with a proper boundary extension. -/
theorem trLift_concrete (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀)
    (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    {s₁ s₂ : ExplState} {e₁ e₂ : Drv} (hbe₁ : GW1P.HasProperBdryExt (stChart s₁))
    (hr₁ : GW1P.PieceRegular e₁.1 e₁.2) (he₁ : e₁.2 ≠ ⊤) (hpos : e₁.2 ≠ 0)
    (htip₁ : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 =
      pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) :
    (∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ e₁ → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ e₂ ∧
      LuM.bdVal (stChart s₂) '' (LuM.trOf e₂ '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (LuM.bdVal (stChart s₁) '' (LuM.trOf e₁ '' Icc 0 r.toNNReal))) ∧
    (∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ e₂ → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ e₁ ∧
      LuM.bdVal (stChart s₂) '' (LuM.trOf e₂ '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (LuM.bdVal (stChart s₁) '' (LuM.trOf e₁ '' Icc 0 r.toNNReal))) := by
  set ρ := stCurve c m s₁ e₁ s₂ with hρdef
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ≥0, e₁.2 = L₁ := ⟨e₁.2.toNNReal, (ENNReal.coe_toNNReal he₁).symm⟩
  obtain ⟨L₂, hL₂⟩ : ∃ L₂ : ℝ≥0, e₂.2 = L₂ := ⟨e₂.2.toNNReal, (ENNReal.coe_toNNReal hfin).symm⟩
  have hpos' : 0 < L₁ := by
    rw [hL₁] at hpos
    exact pos_iff_ne_zero.2 (by exact_mod_cast hpos)
  have hst₁ : stopTime ⊤ e₁ = L₁ := by simp [stopTime, hL₁]
  have hst₂ : stopTime ⊤ e₂ = L₂ := by simp [stopTime, hL₂]
  have hPc := continuousOn_pcPt hbe₁ hr₁
  have himg := fun (r : ℝ≥0) (hr : r < L₁) => image_eq_liftImage_stage hγ hβ hcH hc1 hoff hL₁ hPc htip₁ htail
    hρ he₂ hgen hfin hW hW0 hαeq hα0 hαc hc hgc hcH₂ hc1₂ hdom hgd hr
  have hu0 : ∀ t : ℝ≥0, t < L₁ → 0 ≤ (t : ℝ) / (L₁ - t) := fun t ht =>
    div_nonneg t.2 (sub_nonneg.2 (NNReal.coe_le_coe.2 ht.le))
  rw [hst₁, hst₂]
  refine ⟨fun r hr0 hr => ?_, fun r' hr'0 hr' => ?_⟩
  · have hrt : r.toNNReal < L₁ := (Real.toNNReal_lt_iff_lt_coe hr0).2 hr
    refine ⟨capClock ρ ((r.toNNReal : ℝ) / (L₁ - r.toNNReal)), hρ.capClock_nonneg (hu0 _ hrt), ?_, himg _ hrt⟩
    have h := hρ.ofReal_capClock_lt (hu0 _ hrt)
    rw [← he₂, hL₂] at h
    have := (ENNReal.ofReal_lt_iff_lt_toReal (hρ.capClock_nonneg (hu0 _ hrt)) ENNReal.coe_ne_top).1 h
    simpa using this
  · have hlt : ENNReal.ofReal r' < capLife ρ := by
      rw [← he₂, hL₂]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hr'0 ENNReal.coe_ne_top).2 (by simpa using hr')
    obtain ⟨hu, hcu⟩ := hρ.capInv_spec hr'0 hlt
    have hr0 := clockOf_nonneg (NNReal.coe_pos.2 hpos') hu
    have hrl := clockOf_lt (NNReal.coe_pos.2 hpos') hu
    refine ⟨clockOf L₁ (capInv ρ r'), hr0, hrl, ?_⟩
    have hrt : (clockOf L₁ (capInv ρ r')).toNNReal < L₁ := (Real.toNNReal_lt_iff_lt_coe hr0).2 hrl
    have h := himg _ hrt
    rw [Real.coe_toNNReal _ hr0, div_sub_clockOf (NNReal.coe_pos.2 hpos') hu, hcu] at h
    exact h

end InteractingSLE.Theorem14.SB.Lk
