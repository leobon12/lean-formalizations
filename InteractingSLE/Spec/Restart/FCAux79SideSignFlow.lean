/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCAux79Side

/-!
# The orientation of the new piece, I: chart transitions of one trace and restrictions of a later line

Packet PROVE-FCSIDE (the deterministic orientation `FCAux79.IsFCSideSign`, spec p. 290). Two single-curve
ingredients and the restriction of a later first-contact line to an earlier capacity.

* `exists_transition`: for a simple generating trace `γ` of a continuous driver `W`, capacities `0 < τ ≤ Q`, and a
  real `y` that the extended inverse `Φ_Q` sends to a point `γ(σ)` with `σ < τ`, the transition map
  `f_τ ∘ f_Q⁻¹` converges at `y` (within `ℍ`) to a real `ξ` with `Φ_τ(ξ) = γ(σ)`, and `ξ` has the sign of `y`.
  Proof: `f_τ ∘ f_Q⁻¹` is the inverse map of the shifted driver `W(τ + ·) − W(τ)` (Rohde–Schramm's flow property),
  whose boundary limit `ξ` exists ([Yua22] Corollary 1.3, `IsLoewnerTrace.exists_tendsto_shift`); `ξ` is real
  (`γ(σ)` is on the hull at `τ`), off the shifted trace (injectivity of `γ`), and adherent to the unbounded domain of
  the shifted hull, hence alive for the shifted flow up to `Q − τ`, which carries it to `y`; real flows preserve
  the side of the driver.
* `lt_of_eq_of_lt`: two simple arcs with the same image and the same initial point are parametrised in the same
  order (the restriction of a continuous injective map of a compact interval is a homeomorphism onto its image, and
  the image of an initial segment is connected).
* `IsFCLine.lt_of_inv_eq`, `IsFCLine.exists_restrict`: the chart path `γ` and the new piece `η₁([s₀, s₀ + t])` are
  parametrised in the same order, so every capacity `0 < τ ≤ Q` is again a later line, at the time of
  `ψ(γ(τ))`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace Restart.FCAux79

open Sec7 Sec7.SideHeightBox Supp7

/-! ### The transition between two capacities of one trace -/

section Transition

variable {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞}

/-- **The transition from capacity `Q` to an earlier capacity `τ` at a point of the earlier trace.** If
`Φ_Q(y) = γ(σ)` with `σ < τ ≤ Q`, then `f_τ ∘ f_Q⁻¹` tends at `y` (within `ℍ`) to a real `ξ` with
`Φ_τ(ξ) = γ(σ)`, and `ξ` lies on the same side of `0` as `y`. -/
theorem exists_transition (hg : IsGeneratingTrace W ζc γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (hi : InjOn γ {s | (s : ℝ≥0∞) ≤ ζc}) {τ Q σ : ℝ≥0} (hτ0 : 0 < τ) (hτQ : τ ≤ Q) (hQ : (Q : ℝ≥0∞) < ζc)
    (hστ : σ < τ) {y : ℝ} (hy : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) y = γ σ) :
    ∃ ξ : ℝ, Tendsto (fun z => fwdMap (fun s : ℝ => W s.toNNReal) τ (fwdMapInv (fun s : ℝ => W s.toNNReal) Q z))
        (𝓝[H] (y : ℂ)) (𝓝[H] (ξ : ℂ)) ∧
      extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) τ) ξ = γ σ ∧ (0 < y → 0 < ξ) ∧ (y < 0 → ξ < 0) := by
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  obtain ⟨Wg, γg, T', hQT', hWgc, hWg0, hγg, hWeq, hγeq⟩ :=
    ReverseArc.exists_global_model hg hW.continuousOn hW0 hQ
  have hτT' : (τ : ℝ) < T' := lt_of_le_of_lt (NNReal.coe_le_coe.2 hτQ) hQT'
  have heq : ∀ r ∈ Icc (0 : ℝ) T', w' r = Wg r := fun r hr => (hWeq r hr).symm
  have hinvQ : fwdMapInv w' Q = fwdMapInv Wg Q := fwdMapInv_eq_of_eqOn Q.coe_nonneg hQT' heq
  have hinvτ : fwdMapInv w' τ = fwdMapInv Wg τ := fwdMapInv_eq_of_eqOn τ.coe_nonneg hτT' heq
  have hfτ : ∀ z, fwdMap w' τ z = fwdMap Wg τ z := fun z =>
    fwdMap_eq_of_eqOn τ.coe_nonneg fun r hr => heq r ⟨hr.1, hr.2.trans hτT'.le⟩
  set u : ℝ := (Q : ℝ) - τ with hu
  have hu0 : 0 ≤ u := sub_nonneg.2 (NNReal.coe_le_coe.2 hτQ)
  have hτu : (τ : ℝ) + u = Q := by rw [hu]; ring
  have hVc := QuantumZipper.RS.continuous_shiftDrive hWgc (τ : ℝ)
  have hV0 : shiftDrive Wg τ 0 = 0 := QuantumZipper.RS.shiftDrive_zero Wg τ
  obtain ⟨ξc, hξH, hFξ, hlim⟩ := hγg.exists_tendsto_shift hWgc hWg0 τ.coe_nonneg hu0 (ofReal_mem_Hbar y)
  -- the transition map is the inverse map of the shifted driver
  have hχ : ∀ z ∈ H, fwdMap w' τ (fwdMapInv w' Q z) = fwdMapInv (shiftDrive Wg τ) u z := by
    intro z hz
    rw [hfτ, hinvQ, QuantumZipper.RS.fwdMapInv_shift_eq hWgc hWg0 τ.coe_nonneg hu0 hz, hτu]
  have hlimχ : Tendsto (fun z => fwdMap w' τ (fwdMapInv w' Q z)) (𝓝[H] (y : ℂ)) (𝓝 ξc) :=
    hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => (hχ z hz).symm)
  -- the boundary value is the trace point
  have hΦξ : extendFrom H (fwdMapInv w' τ) ξc = γ σ := by
    rw [hinvτ, hFξ, hτu, ← hinvQ]
    exact hy
  -- the limit is real
  have hτζ : (τ : ℝ≥0∞) < ζc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hτQ) hQ
  have hch := ReverseArc.isChart hg hW.continuousOn hW0 hi hτζ hτ0
  have hξim : ξc.im = 0 := by
    rcases mem_H_or_im_eq_zero hξH with h | h
    · exfalso
      have hm := hch.inv_mem h
      rw [hΦξ] at hm
      exact hm.2 (ReverseArc.mem_fillH_of_mem_H hστ.le hm.1)
    · exact h
  set ξ : ℝ := ξc.re with hξdef
  have hξc : ξc = (ξ : ℂ) := (ofReal_re_of_im hξim).symm
  -- the shifted trace
  obtain ⟨hγs, hext⟩ := hγg.isLoewnerTrace_shift_and_extendFrom hWgc hWg0 τ.coe_nonneg
  set γs := loewnerTip (shiftDrive Wg τ) with hγsdef
  have hξη : (ξ : ℂ) ∉ γs '' Icc 0 u := by
    rintro ⟨v, hv, hve⟩
    have h1 := hext v hv.1
    rw [hve, ← hξc, ← hinvτ, hΦξ] at h1
    have hle : (τ : ℝ) + v ≤ Q := by rw [← hτu]; linarith [hv.2]
    rw [hγeq (τ + v) ⟨by linarith [hv.1, τ.coe_nonneg], hle.trans hQT'.le⟩] at h1
    have hle' : (((τ + v).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζc := by
      refine le_trans (ENNReal.coe_le_coe.2 ?_) hQ.le
      rw [Real.toNNReal_le_iff_le_coe]; exact hle
    have h2 := hi ((ENNReal.coe_le_coe.2 hστ.le).trans hτζ.le) hle' h1
    have h3 : (σ : ℝ) = τ + v := by
      rw [h2, Real.coe_toNNReal _ (by linarith [hv.1, τ.coe_nonneg])]
    have h4 : (σ : ℝ) < τ := NNReal.coe_lt_coe.2 hστ
    linarith [hv.1]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hξη
    refine ⟨0, ⟨le_rfl, hu0⟩, ?_⟩
    rw [hγsdef, loewnerTip_shiftDrive_zero hWgc, h0, ofReal_zero]
  -- the limit is adherent to the unbounded domain of the shifted hull
  have hneb := neBot_nhdsWithin_H_ofReal y
  have hcl : (ξ : ℂ) ∈ closure (H \ fwdHull (shiftDrive Wg τ) u) := by
    rw [← hξc]
    exact mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun z hz =>
      QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hVc hV0 hu0 hz)
  have hLT : IsLoewnerTraceLT (shiftDrive Wg τ) (u + 1) γs :=
    ⟨hγs.1, hγs.2.1.mono Ico_subset_Ici_self, fun t ht _ => hγs.2.2 t ht⟩
  obtain ⟨v, hv⟩ := GB7a.exists_isForwardSol_of_mem_closure hVc hV0 hLT hu0 (by linarith) hξ0 hξη hcl
  -- the shifted flow carries `ξ` to `y`
  have hvy : v u = (y : ℂ) := by
    have h1 := tendsto_fwdMap_of_isForwardSol hVc hu0 hv
    have h2 : Tendsto (fwdMapInv (shiftDrive Wg τ) u) (𝓝[H] (y : ℂ)) (𝓝[H] (ξ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨by rw [← hξc]; exact hlim, eventually_nhdsWithin_of_forall fun z hz =>
        QuantumZipper.RS.fwdMapInv_mem_H hVc hV0 hu0 hz⟩
    refine tendsto_nhds_unique (h1.comp h2) ?_
    refine (tendsto_nhdsWithin_iff.1 (tendsto_id (x := 𝓝[H] (y : ℂ)))).1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hVc hV0 hu0 hz).symm
  have hyre : y = (v u).re := by rw [hvy, ofReal_re]
  have hside_pos : 0 < ξ → 0 < y := fun h => by
    rw [hyre]
    exact QuantumZipper.re_pos_isForwardSol_real hVc hu0 hv (by rw [hV0]; exact h) u ⟨hu0, le_rfl⟩
  have hside_neg : ξ < 0 → y < 0 := fun h => by
    rw [hyre]
    exact QuantumZipper.re_neg_isForwardSol_real hVc hu0 hv (by rw [hV0]; exact h) u ⟨hu0, le_rfl⟩
  refine ⟨ξ, tendsto_nhdsWithin_iff.2 ⟨by rw [← hξc]; exact hlimχ, eventually_nhdsWithin_of_forall
    fun z hz => ?_⟩, by rw [← hξc]; exact hΦξ, fun hy0 => ?_, fun hy0 => ?_⟩
  · rw [hχ z hz]
    exact QuantumZipper.RS.fwdMapInv_mem_H hVc hV0 hu0 hz
  · rcases lt_or_gt_of_ne hξ0 with h | h
    · linarith [hside_neg h]
    · exact h
  · rcases lt_or_gt_of_ne hξ0 with h | h
    · exact h
    · linarith [hside_pos h]

end Transition

/-! ### Two parametrisations of one simple arc -/

section Order

/-- **Two simple arcs with the same image and the same initial point are parametrised in the same order.** -/
theorem lt_of_eq_of_lt {F G : ℝ≥0 → ℂ} {Q a b : ℝ≥0} (hF : ContinuousOn F (Icc 0 Q)) (hFi : InjOn F (Icc 0 Q))
    (hG : ContinuousOn G (Icc a b)) (hGi : InjOn G (Icc a b)) (himg : F '' Icc 0 Q = G '' Icc a b)
    (h0 : F 0 = G a) {σ₁ σ₂ u₁ u₂ : ℝ≥0} (hσ₂ : σ₂ ≤ Q) (h12 : σ₁ < σ₂) (hu₁ : u₁ ∈ Icc a b)
    (hu₂ : u₂ ∈ Icc a b) (he₁ : F σ₁ = G u₁) (he₂ : F σ₂ = G u₂) : u₁ < u₂ := by
  have hσ₁ : σ₁ ∈ Icc 0 Q := ⟨zero_le, h12.le.trans hσ₂⟩
  have hσ₂' : σ₂ ∈ Icc 0 Q := ⟨zero_le, hσ₂⟩
  have hne : u₁ ≠ u₂ := by
    intro h
    rw [h, ← he₂] at he₁
    exact (ne_of_lt h12) (hFi hσ₁ hσ₂' he₁)
  refine lt_of_le_of_ne (not_lt.1 fun hlt => ?_) hne
  -- the image of `[0, σ₁]`
  set C := F '' Icc 0 σ₁ with hCdef
  have hCsub : C ⊆ G '' Icc a b := by
    rw [← himg]; exact image_mono (Icc_subset_Icc_right hσ₁.2)
  have hCc : IsCompact C := isCompact_Icc.image_of_continuousOn (hF.mono (Icc_subset_Icc_right hσ₁.2))
  have hCpc : IsPreconnected C := isPreconnected_Icc.image _ (hF.mono (Icc_subset_Icc_right hσ₁.2))
  set E := Icc a b ∩ G ⁻¹' C with hEdef
  have hEc : IsCompact E :=
    isCompact_Icc.of_isClosed_subset (hG.preimage_isClosed_of_isClosed isClosed_Icc hCc.isClosed)
      inter_subset_left
  have : CompactSpace E := isCompact_iff_compactSpace.1 hEc
  set g : E → ℂ := fun t => G t with hgdef
  have hgc : Continuous g := hG.comp_continuous continuous_subtype_val fun t => t.2.1
  have hgi : Function.Injective g := fun x y hxy => Subtype.ext (hGi x.2.1 y.2.1 hxy)
  have hemb := hgc.isClosedEmbedding hgi
  have hrange : Set.range g = C := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact t.2.2
    · intro hz
      obtain ⟨t, ht, hte⟩ := hCsub hz
      exact ⟨⟨t, ht, by rw [mem_preimage, hte]; exact hz⟩, hte⟩
  have hEpc : IsPreconnected (univ : Set E) := by
    rw [← hemb.isInducing.isPreconnected_image, image_univ, hrange]
    exact hCpc
  have hEpc' : IsPreconnected E := by
    have := hEpc.image Subtype.val continuous_subtype_val.continuousOn
    rwa [image_univ, Subtype.range_coe] at this
  have haE : a ∈ E := ⟨⟨le_rfl, hu₁.1.trans hu₁.2⟩, by rw [mem_preimage, ← h0]; exact ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
  have hu₁E : u₁ ∈ E := ⟨hu₁, by rw [mem_preimage, ← he₁]; exact ⟨σ₁, ⟨zero_le, le_rfl⟩, rfl⟩⟩
  have hu₂E : u₂ ∈ E := hEpc'.Icc_subset haE hu₁E ⟨hu₂.1, hlt.le⟩
  obtain ⟨σ, hσ, hσe⟩ := hu₂E.2
  rw [← he₂] at hσe
  have := hFi ⟨zero_le, hσ.2.trans hσ₁.2⟩ hσ₂' hσe
  rw [← this] at h12
  exact absurd hσ.2 (not_le.2 h12)

end Order

/-! ### Restricting a later line to an earlier capacity -/

section Restrict

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

/-- The composed reading `σ ↦ ψ(γ(σ))` of the new piece is continuous and injective on `[0, Q]`. -/
theorem IsFCLine.continuousOn_inv_γ (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) :
    ContinuousOn (fun s => d.inv ω (γ s)) (Icc 0 Q) := by
  have hψc : ContinuousOn (d.inv ω) Hbar := (hl.chart hd).2.2.2.2.2.2.2.1
  exact hψc.comp hl.continuousOn_γ fun s hs => hl.γ_mem_Hbar hs.2

theorem IsFCLine.injOn_inv_γ (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) :
    InjOn (fun s => d.inv ω (γ s)) (Icc 0 Q) := fun _ ha _ hb hab =>
  hl.inj ((ENNReal.coe_le_coe.2 ha.2).trans hl.lt.le) ((ENNReal.coe_le_coe.2 hb.2).trans hl.lt.le)
    (inv_injOn_Hbar hd hl (hl.γ_mem_Hbar ha.2) (hl.γ_mem_Hbar hb.2) hab)

theorem IsFCLine.inv_γ_zero (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) :
    d.inv ω (γ 0) = d.η₁ ω (d.s₀ ω) := by
  rw [hl.gen.1]
  exact_mod_cast inv_zero_eq_contact hd hl.mem_E

/-- **The chart path and the new piece are parametrised in the same order.** -/
theorem IsFCLine.lt_of_inv_eq (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) {σ₁ σ₂ u₁ u₂ : ℝ≥0}
    (hσ₂ : σ₂ ≤ Q) (h12 : σ₁ < σ₂) (hu₁ : u₁ ∈ Icc (d.s₀ ω) (d.s₀ ω + t)) (hu₂ : u₂ ∈ Icc (d.s₀ ω) (d.s₀ ω + t))
    (he₁ : d.inv ω (γ σ₁) = d.η₁ ω u₁) (he₂ : d.inv ω (γ σ₂) = d.η₁ ω u₂) : u₁ < u₂ :=
  lt_of_eq_of_lt (hl.continuousOn_inv_γ hd) (hl.injOn_inv_γ hd)
    (hl.continuousOn₁.mono (Icc_subset_Icc_left zero_le)) (hl.injOn₁.mono (Icc_subset_Icc_left zero_le))
    hl.image (hl.inv_γ_zero hd) hσ₂ h12 hu₁ hu₂ he₁ he₂

omit [MeasurableSpace Ω] in
/-- Every point of the chart path reads a point of the new piece. -/
theorem IsFCLine.exists_inv_γ_eq (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {σ : ℝ≥0} (hσ : σ ≤ Q) :
    ∃ u ∈ Icc (d.s₀ ω) (d.s₀ ω + t), d.inv ω (γ σ) = d.η₁ ω u := by
  have h : d.inv ω (γ σ) ∈ d.η₁ ω '' Icc (d.s₀ ω) (d.s₀ ω + t) := hl.image ▸ ⟨σ, ⟨zero_le, hσ⟩, rfl⟩
  obtain ⟨u, hu, he⟩ := h
  exact ⟨u, hu, he.symm⟩

/-- **A later line restricted to an earlier capacity** `0 < τ ≤ Q` is the later line at the time of `ψ(γ(τ))`. -/
theorem IsFCLine.exists_restrict (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) {τ : ℝ≥0}
    (hτ0 : 0 < τ) (hτQ : τ ≤ Q) :
    ∃ t' ≤ t, d.inv ω (γ τ) = d.η₁ ω (d.s₀ ω + t') ∧ IsFCLine d ω x₁ x₂ t' W γ ζc τ := by
  obtain ⟨uτ, huτ, heτ⟩ := hl.exists_inv_γ_eq hτQ
  set t' := uτ - d.s₀ ω with ht'
  have hst' : d.s₀ ω + t' = uτ := add_tsub_cancel_of_le huτ.1
  have ht't : t' ≤ t := by
    rw [ht', tsub_le_iff_left]; exact huτ.2
  refine ⟨t', ht't, by rw [hst']; exact heτ, ⟨hl.mem_E, hl.path₁, hl.path₂, ?_, hl.gen, hl.cont, hl.zero, hl.inj,
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hτQ) hl.lt, hτ0, ?_, by rw [hst']; exact heτ⟩⟩
  · rw [hst']; exact (ENNReal.coe_le_coe.2 huτ.2).trans hl.le_life
  · rw [hst']
    ext z
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨u, hu, he⟩ := hl.exists_inv_γ_eq (hσ.2.trans hτQ)
      refine ⟨u, ⟨hu.1, ?_⟩, he.symm⟩
      rcases lt_or_eq_of_le hσ.2 with h | h
      · exact (hl.lt_of_inv_eq hd hτQ h hu huτ he heτ).le
      · subst h
        exact (hl.injOn₁ ⟨zero_le, hu.2⟩ ⟨zero_le, huτ.2⟩ (he.symm.trans heτ)).le
    · rintro ⟨u, hu, rfl⟩
      have hu' : u ∈ Icc (d.s₀ ω) (d.s₀ ω + t) := ⟨hu.1, hu.2.trans huτ.2⟩
      have hmem : d.η₁ ω u ∈ (fun s => d.inv ω (γ s)) '' Icc 0 Q := by
        rw [hl.image]; exact ⟨u, hu', rfl⟩
      obtain ⟨σ, hσ, he⟩ := hmem
      refine ⟨σ, ⟨zero_le, not_lt.1 fun hτσ => ?_⟩, he⟩
      have := hl.lt_of_inv_eq hd hσ.2 hτσ huτ hu' heτ he
      exact absurd hu.2 (not_le.2 this)

end Restrict

end Restart.FCAux79

end InteractingSLE
