/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvEnd
import InteractingSLE.Spec.Supplement.SB2FinChain
import InteractingSLE.Spec.Supplement.SB2LkFree
import InteractingSLE.Spec.Supplement.SB2LpLift

/-!
# SB2(2): the relative root stage is a reparametrized tail lift (drivenness and relative facts at stage `0`)

Packet PROVE-SB2-LIFTSET (round 18). At relative stage `0` the relative chart is the identity, so the stage curve of
the shifted start piece `p` (a piece of `β₀`'s tail after `t_L`) is, at every time, the tail lift curve `γ` read at
the tail time of the actual point (`β₀` is a closed embedding, so the tail times depend continuously on the actual
time; at good times this is `lift_mem_H_iff`, elsewhere continuity along the dense good times):

* `exists_tailTime`: the continuous tail time `σ` of a piece on the tail;
* **`stValp_eq_tail`**: the stage values are `γ ∘ σ` before the lifetime (identity relative chart);
* `isDrivenCurve_congr_nonneg`, `strictMonoOn_tailTime`;
* **`root_fin`**: at a finite piece the stage curve is driven (it is `relCurve` of a simple proper reparametrization of
  `γ` whose real times have empty interior by the density of good times, `FinRel.isDrivenCurve_relCurve_of_lt`),
  converges at `∞` and stays in `ℍ̄`; **`root_inf`**: at an infinite piece it is driven, transient and in `ℍ̄`;
* **`root_stageRelFinP`**: the relative facts at a finite root (`stageRelFinP_of` with the identity chart).

Deterministic; the inputs are the actual-piece facts of `Stage0Act` and the tail order (`startPiece_order`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-! ### Drivenness depends only on the nonnegative times -/

/-- **Drivenness depends only on the values at nonnegative times.** -/
theorem isDrivenCurve_congr_nonneg {γ₁ γ₂ : ℝ → ℂ} (h : IsDrivenCurve γ₁) (heq : ∀ u, 0 ≤ u → γ₁ u = γ₂ u) :
    IsDrivenCurve γ₂ := by
  have himg : ∀ u : ℝ, γ₁ '' Icc 0 u = γ₂ '' Icc 0 u := fun u =>
    image_congr fun v hv => heq v hv.1
  have hcap : capClock γ₁ = capClock γ₂ := funext fun u => by unfold capClock; rw [himg u]
  refine ⟨h.continuousOn.congr fun u hu => (heq u hu).symm, (heq 0 le_rfl) ▸ h.zero, fun S hS => ?_⟩
  obtain ⟨W, hW, hW0, hc0, hm, hcc, hK⟩ := h.localDriver S hS
  refine ⟨W, hW, hW0, hcap ▸ hc0, hcap ▸ hm, hcap ▸ hcc, fun t ht => ?_⟩
  rw [← hcap, ← himg t]
  exact hK t ht

/-! ### The tail time of a piece on the tail -/

/-- **The continuous tail time** of a continuous piece on the tail of a proper curve. -/
theorem exists_tailTime {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {tL : ℝ≥0} {p : ℝ≥0 → ℂ} {S : Set ℝ≥0}
    (hPc : ContinuousOn p S) (htl : ∀ t ∈ S, p t ∈ β₀ '' Ici tL) :
    ∃ σ : ℝ≥0 → ℝ≥0, ContinuousOn σ S ∧ ∀ t ∈ S, β₀ (tL + σ t) = p t := by
  classical
  set σ : ℝ≥0 → ℝ≥0 := fun t => if h : ∃ s : ℝ≥0, β₀ (tL + s) = p t then h.choose else 0 with hσdef
  have hspec : ∀ t ∈ S, β₀ (tL + σ t) = p t := fun t ht => by
    have hex : ∃ s : ℝ≥0, β₀ (tL + s) = p t := by
      obtain ⟨x, hx, hxe⟩ := htl t ht
      exact ⟨x - tL, by rw [add_tsub_cancel_of_le (show tL ≤ x from hx)]; exact hxe⟩
    simp only [hσdef, hex, ↓reduceDIte]
    exact hex.choose_spec
  refine ⟨σ, fun t ht => ?_, hspec⟩
  have hβe := isClosedEmbedding_of_isProperCurve hβ
  have h1 : Tendsto (fun t' => β₀ (tL + σ t')) (𝓝[S] t) (𝓝 (β₀ (tL + σ t))) := by
    rw [hspec t ht]
    exact (hPc t ht).tendsto.congr' (eventually_nhdsWithin_of_forall fun t' h => (hspec t' h).symm)
  have h2 : Tendsto (fun t' => tL + σ t') (𝓝[S] t) (𝓝 (tL + σ t)) := hβe.isInducing.tendsto_nhds_iff.2 h1
  have h3 := h2.sub (tendsto_const_nhds (x := tL))
  simp only [add_tsub_cancel_left] at h3
  exact h3

/-- The tail time starts at `0` when the piece starts at `β₀ t_L`. -/
theorem tailTime_zero {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {tL : ℝ≥0} {σ : ℝ≥0 → ℝ≥0}
    (h0 : β₀ (tL + σ 0) = β₀ tL) : σ 0 = 0 := by
  have := hβ.2.1 h0
  simpa using this

/-- **The tail time of a piece injective before its end is strictly increasing up to the end.** -/
theorem strictMonoOn_tailTime {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {p : ℝ≥0 → ℂ} {L₁ : ℝ≥0} {σ : ℝ≥0 → ℝ≥0}
    (hσc : ContinuousOn σ (Iic L₁)) (hσ : ∀ t ∈ Iic L₁, β₀ (tL + σ t) = p t) (hinj : InjOn p (Iio L₁))
    (h0 : σ 0 = 0) : StrictMonoOn σ (Iic L₁) := by
  have hlt : ∀ a b : ℝ≥0, a < b → b < L₁ → σ a < σ b := fun a b hab hbL => by
    have hsub : Icc 0 b ⊆ Iic L₁ := fun x hx => hx.2.trans hbL.le
    have hsub' : Icc 0 b ⊆ Iio L₁ := fun x hx => lt_of_le_of_lt hx.2 hbL
    have hm := (hσc.mono hsub).strictMonoOn_of_injOn_Icc zero_le (by rw [h0]; exact zero_le)
      fun x hx x' hx' e => hinj (hsub' hx) (hsub' hx') (by rw [← hσ x (hsub hx), ← hσ x' (hsub hx'), e])
    exact hm ⟨zero_le, hab.le⟩ ⟨zero_le, le_rfl⟩ hab
  intro a ha b hb hab
  rcases (mem_Iic.1 hb).lt_or_eq with hbL | rfl
  · exact hlt a b hab hbL
  · obtain ⟨c, hac, hcL⟩ := exists_between hab
    have hcle : σ c ≤ σ b := by
      have hne : (𝓝[<] b).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨a, hab⟩]; exact mem_Iic.2 le_rfl
      have htend : Tendsto σ (𝓝[<] b) (𝓝 (σ b)) :=
        ((hσc b (mem_Iic.2 le_rfl)).mono fun x (hx : x < b) => le_of_lt hx).tendsto
      refine ge_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsLT hcL] with x hx
      exact (hlt c x hx.1 hx.2).le
    exact lt_of_lt_of_le (hlt a c hac hcL) hcle

/-! ### The stage values at the identity relative chart -/

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **At the identity relative chart the stage values are the tail lift at the tail time.** -/
theorem stValp_eq_tail (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState}
    (hs₂ : ∀ z, (stChart s₂).1 z = z) {σ : ℝ≥0 → ℝ≥0} (hσc : ContinuousOn σ {t | (t : ℝ≥0∞) ≤ L})
    (hσ : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L}, β₀ (tL + σ t) = p t)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L)) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → stValp c m p L s₂ t = γ (σ t) := by
  have hgood : ∀ t ∈ goodTp c p L, relValp c m p s₂ t = γ (σ t) := fun t ht => by
    unfold relValp
    rw [hs₂]
    have hl := lift_mem_H_iff hγ hcH hc1 hoff (σ t)
    have hD : β₀ (tL + σ t) ∈ c.2.1 '' H := by rw [hσ t ht.1]; exact ht.2
    rw [hl.2 (hl.1.1 hD), hσ t ht.1]
  intro t ht
  by_cases hg : t ∈ goodTp c p L
  · rw [stValp_of_good hg, hgood t hg]
  · unfold stValp
    simp only [hg, ↓reduceIte]
    have hne : (𝓝[goodTp c p L] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hgd ht)
    have hcont : ContinuousWithinAt (fun t' => γ (σ t')) (goodTp c p L) t :=
      hγ.2.1.1.continuousAt.comp_continuousWithinAt ((hσc t ht.le).mono fun t' h => h.1)
    exact (hcont.tendsto.congr' (eventually_nhdsWithin_of_forall fun t' h => (hgood t' h).symm)).limUnder_eq

/-- **No open interval of real times** for a curve that equals `γ ∘ σ` on the good times, whose good times are dense:
at a good time `γ (σ t) − m ∈ ℍ`. -/
theorem interior_real_eq_empty (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {σ : ℝ≥0 → ℝ≥0}
    (hσ : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L}, β₀ (tL + σ t) = p t)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L)) {ζ : ℝ → ℂ} {S : ℝ}
    (hζ : ∀ v : ℝ, 0 < v → v < S → ζ v = γ (σ v.toNNReal)) (hSL : ∀ v : ℝ, 0 < v → v < S → (v.toNNReal : ℝ≥0∞) < L) :
    interior {v ∈ Ioo (0 : ℝ) S | (ζ v).im = 0} = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hxset := interior_subset hx
  have hnhds : {v ∈ Ioo (0 : ℝ) S | (ζ v).im = 0} ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hx
  have hx0 : 0 < x := hxset.1.1
  have hcoe : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal _ hx0.le
  have hpre : (fun t : ℝ≥0 => (t : ℝ)) ⁻¹' {v ∈ Ioo (0 : ℝ) S | (ζ v).im = 0} ∈ 𝓝 x.toNNReal :=
    NNReal.continuous_coe.continuousAt.preimage_mem_nhds (by rw [hcoe]; exact hnhds)
  have hcl := hgd (show x.toNNReal ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < L} from hSL x hx0 hxset.1.2)
  obtain ⟨t, htU, htG⟩ := mem_closure_iff_nhds.1 hcl _ hpre
  obtain ⟨⟨ht0, htS⟩, him⟩ := htU
  have hζt : ζ t = γ (σ t) := by rw [hζ t ht0 htS, Real.toNNReal_coe]
  have hl := lift_mem_H_iff hγ hcH hc1 hoff (σ t)
  have hD : β₀ (tL + σ t) ∈ c.2.1 '' H := by rw [hσ t htG.1]; exact htG.2
  have hH := hl.1.1 hD
  have h1 : 0 < (γ (σ t) - (m : ℂ)).im := hH
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero, ← hζt] at h1
  rw [him] at h1
  exact lt_irrefl _ h1

/-- **The relative root at a finite piece**: driven, convergent at `∞`, in `ℍ̄`. -/
theorem root_fin (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {p : ℝ≥0 → ℂ} {L₁ : ℝ≥0} (hL₁ : 0 < L₁)
    {s₂ : ExplState} (hs₂ : ∀ z, (stChart s₂).1 z = z)
    (hPc : ContinuousOn p {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)})
    (hinj : InjOn p {t : ℝ≥0 | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)}) (hp0 : p 0 = β₀ tL)
    (htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)}, p t ∈ β₀ '' Ici tL)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)} ⊆ closure (goodTp c p L₁)) :
    IsDrivenCurve (stCurvep c m p L₁ s₂) ∧ (∃ z, Tendsto (stCurvep c m p L₁ s₂) atTop (𝓝 z)) ∧
      ∀ u, 0 ≤ u → stCurvep c m p L₁ s₂ u ∈ Hbar := by
  have hSI : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)} = Iic L₁ := by ext t; simp
  obtain ⟨σ, hσc, hσ⟩ := exists_tailTime hβ hPc htl
  have hσ' : ∀ t ∈ Iic L₁, β₀ (tL + σ t) = p t := fun t ht => hσ t (by rw [hSI]; exact ht)
  have h0 : σ 0 = 0 := tailTime_zero hβ (by rw [hσ' 0 (show (0 : ℝ≥0) ≤ L₁ from zero_le), hp0])
  have hSI' : {t : ℝ≥0 | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)} = Iio L₁ := by ext t; simp
  have hmono : StrictMonoOn σ (Iic L₁) :=
    strictMonoOn_tailTime (hSI ▸ hσc) hσ' (hSI' ▸ hinj) h0
  have hval := stValp_eq_tail hγ hcH hc1 hoff hs₂ hσc hσ hgd
  have hL₁' : (0 : ℝ) < L₁ := NNReal.coe_pos.2 hL₁
  -- the extended tail time and the reparametrized lift
  set σt : ℝ → ℝ := fun v => (σ (min v L₁).toNNReal : ℝ) + max (v - L₁) 0 with hσt
  have hminL : ∀ v : ℝ, (min v L₁).toNNReal ∈ Iic L₁ := fun v => by
    rw [mem_Iic, ← NNReal.coe_le_coe]
    rcases le_or_gt 0 (min v L₁) with h | h
    · rw [Real.coe_toNNReal _ h]; exact min_le_right _ _
    · rw [Real.toNNReal_of_nonpos h.le, NNReal.coe_zero]; exact L₁.2
  have hσc' : ContinuousOn σ (Iic L₁) := by rw [← hSI]; exact hσc
  have hσtc : Continuous σt := by
    have hin : Continuous fun v : ℝ => (min v (L₁ : ℝ)).toNNReal :=
      continuous_real_toNNReal.comp (continuous_id.min continuous_const)
    have h1 : Continuous fun v : ℝ => σ (min v (L₁ : ℝ)).toNNReal := hσc'.comp_continuous hin hminL
    exact (NNReal.continuous_coe.comp h1).add ((continuous_id.sub continuous_const).max continuous_const)
  have hσt_nn : ∀ v, 0 ≤ σt v := fun v => add_nonneg (σ _).2 (le_max_right _ _)
  have hσt_le : ∀ v : ℝ, 0 ≤ v → v ≤ L₁ → σt v = σ v.toNNReal := fun v _ hvL => by
    simp only [hσt, min_eq_left hvL, max_eq_right (sub_nonpos.2 hvL), add_zero]
  have hσt_mono : StrictMonoOn σt (Ici 0) := by
    intro v hv v' hv' hvv'
    simp only [hσt]
    rcases lt_or_ge v L₁ with hvL | hvL
    · have hpos : 0 < min v' (L₁ : ℝ) := lt_min (lt_of_le_of_lt hv hvv') hL₁'
      have hlt : min v (L₁ : ℝ) < min v' L₁ := by
        rw [min_eq_left hvL.le]; exact lt_min hvv' hvL
      have h1 : (min v (L₁ : ℝ)).toNNReal < (min v' (L₁ : ℝ)).toNNReal :=
        (Real.toNNReal_lt_toNNReal_iff hpos).2 hlt
      have h2 := hmono (hminL v) (hminL v') h1
      have h3 : max (v - L₁) 0 ≤ max (v' - L₁) 0 := max_le_max (by linarith) le_rfl
      exact add_lt_add_of_lt_of_le (NNReal.coe_lt_coe.2 h2) h3
    · rw [min_eq_right hvL, min_eq_right (hvL.trans hvv'.le), max_eq_left (sub_nonneg.2 hvL),
        max_eq_left (sub_nonneg.2 (hvL.trans hvv'.le))]
      linarith
  set ζ : ℝ → ℂ := fun v => γ (σt v).toNNReal with hζdef
  have hζc : Continuous ζ := hγ.2.1.1.comp (continuous_real_toNNReal.comp hσtc)
  have hζinj : InjOn ζ (Ici 0) := fun v hv v' hv' e => hσt_mono.injOn hv hv' (by
    have h1 := congrArg (fun x : ℝ≥0 => (x : ℝ)) (hγ.2.1.2.1 e)
    simpa only [Real.coe_toNNReal _ (hσt_nn v), Real.coe_toNNReal _ (hσt_nn v')] using h1)
  have hζH : MapsTo ζ (Ici 0) Hbar := fun v _ => hγ.2.1.2.2.1 _
  have hσt0 : σt 0 = 0 := by rw [hσt_le 0 le_rfl hL₁'.le, Real.toNNReal_zero, h0, NNReal.coe_zero]
  have hζ0 : ζ 0 = 0 := by
    simp only [hζdef, hσt0, Real.toNNReal_zero]; exact hγ.2.2.1
  have hζinf : Tendsto (fun v => ‖ζ v‖) atTop atTop := by
    have h1 : Tendsto σt atTop atTop := by
      refine tendsto_atTop_mono (fun v => ?_) (tendsto_atTop_add_const_right _ (-(L₁ : ℝ)) tendsto_id)
      have := le_max_left (v - L₁) 0
      have := (σ (min v (L₁ : ℝ)).toNNReal).2
      simp only [hσt, id]; linarith
    exact hγ.2.1.2.2.2.comp (tendsto_real_toNNReal_atTop.comp h1)
  have hlt : ∀ v : ℝ, 0 ≤ v → v < L₁ → (v.toNNReal : ℝ≥0∞) < (L₁ : ℝ≥0∞) := fun v hv0 hv =>
    ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe hv0).2 hv)
  have hR := interior_real_eq_empty hγ hcH hc1 hoff hσ hgd (ζ := ζ) (S := L₁)
    (fun v hv hvS => by simp only [hζdef, hσt_le v hv.le hvS.le, Real.toNNReal_coe])
    (fun v hv hvS => hlt v hv.le hvS)
  have hdr := FinRel.isDrivenCurve_relCurve_of_lt hζc.continuousOn hζinj hζH hζ0 hζinf hL₁' hR
  have heq : ∀ u, 0 ≤ u → relCurve ζ L₁ u = stCurvep c m p L₁ s₂ u := fun u hu => by
    have hcl := clockOf_mem_Ico hL₁' hu
    rw [stCurvep_of_fin ENNReal.coe_ne_top, ENNReal.coe_toReal, hval _ (hlt _ hcl.1 hcl.2)]
    show ζ (clockOf L₁ u) = _
    simp only [hζdef, hσt_le _ hcl.1 hcl.2.le, Real.toNNReal_coe]
  refine ⟨isDrivenCurve_congr_nonneg hdr heq, ⟨ζ L₁, ?_⟩, fun u hu => ?_⟩
  · have h1 : Tendsto (relCurve ζ L₁) atTop (𝓝 (ζ L₁)) :=
      (hζc.tendsto _).comp ((Sec7.R7Aux131.tendsto_clockOf hL₁').mono_right nhdsWithin_le_nhds)
    exact h1.congr' ((eventually_ge_atTop 0).mono heq)
  · rw [← heq u hu]; exact hγ.2.1.2.2.1 _

/-- **The relative root at an infinite piece**: driven, transient, in `ℍ̄`. -/
theorem root_inf (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {p : ℝ≥0 → ℂ} {s₂ : ExplState}
    (hs₂ : ∀ z, (stChart s₂).1 z = z) (hPc : Continuous p) (hinj : Function.Injective p) (hp0 : p 0 = β₀ tL)
    (htl : ∀ t, p t ∈ β₀ '' Ici tL) (hgd : ∀ t, t ∈ closure (goodTp c p ⊤))
    (htrp : Tendsto (fun t => ‖p t‖) atTop atTop) :
    IsDrivenCurve (stCurvep c m p ⊤ s₂) ∧ Tendsto (fun u => ‖stCurvep c m p ⊤ s₂ u‖) atTop atTop ∧
      ∀ u, 0 ≤ u → stCurvep c m p ⊤ s₂ u ∈ Hbar := by
  have hS : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun t => mem_ofPred.2 (le_top (a := (t : ℝ≥0∞)))
  obtain ⟨σ, hσc, hσ⟩ := exists_tailTime hβ (hS ▸ hPc.continuousOn) (S := {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤})
    (fun t _ => htl t)
  have hσall : ∀ t, β₀ (tL + σ t) = p t := fun t => hσ t (by rw [hS]; trivial)
  have h0 : σ 0 = 0 := tailTime_zero hβ (by rw [hσall 0, hp0])
  have hval := stValp_eq_tail hγ hcH hc1 hoff hs₂ hσc hσ (fun t _ => hgd t)
  have hσcont : Continuous σ := by rw [← continuousOn_univ, ← hS]; exact hσc
  have hσinj : Function.Injective σ := fun a b e => hinj (by rw [← hσall a, ← hσall b, e])
  have hσinf : Tendsto σ atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := tL + M)).image hβ.1).isBounded.subset_closedBall 0
    filter_upwards [htrp.eventually_gt_atTop B] with t ht
    by_contra hlt
    push Not at hlt
    have hmem : p t ∈ closedBall (0 : ℂ) B := by
      rw [← hσall t]
      exact hB ⟨tL + σ t, ⟨zero_le, add_le_add_right hlt.le tL⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hmem
    linarith
  set ζ : ℝ → ℂ := fun v => γ (σ v.toNNReal) with hζdef
  have hζc : Continuous ζ := hγ.2.1.1.comp (hσcont.comp continuous_real_toNNReal)
  have hζinj : InjOn ζ (Ici 0) := fun v hv v' hv' e => by
    have h1 := hσinj (hγ.2.1.2.1 e)
    have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h1
    simpa only [Real.coe_toNNReal _ (mem_Ici.1 hv), Real.coe_toNNReal _ (mem_Ici.1 hv')] using h2
  have hζH : MapsTo ζ (Ici 0) Hbar := fun v _ => hγ.2.1.2.2.1 _
  have hζ0 : ζ 0 = 0 := by simp only [hζdef, Real.toNNReal_zero, h0]; exact hγ.2.2.1
  have hζinf : Tendsto (fun v => ‖ζ v‖) atTop atTop :=
    hγ.2.1.2.2.2.comp (hσinf.comp tendsto_real_toNNReal_atTop)
  have hdr : IsDrivenCurve ζ := ⟨hζc.continuousOn, hζ0, fun S hS => by
    have hR := interior_real_eq_empty hγ hcH hc1 hoff hσ (fun t _ => hgd t) (ζ := ζ) (S := S)
      (fun v _ _ => rfl) (fun v _ _ => ENNReal.coe_lt_top)
    exact FinRel.exists_localDriver_of_lt hζc.continuousOn hζinj hζH hζ0 hζinf hR hS le_rfl⟩
  have heq : ∀ u, 0 ≤ u → ζ u = stCurvep c m p ⊤ s₂ u := fun u _ => by
    rw [stCurvep_of_top rfl, hval _ ENNReal.coe_lt_top]
  refine ⟨isDrivenCurve_congr_nonneg hdr heq, hζinf.congr' ((eventually_ge_atTop 0).mono fun u hu => by
    rw [heq u hu]), fun u hu => ?_⟩
  rw [← heq u hu]; exact hγ.2.1.2.2.1 _

/-- The relative root state's chart facts (the identity recentred at `0`). -/
theorem root_chart_facts {s₂ : ExplState} (hs : stChart s₂ = Chart.id.recenter 0) :
    (∀ z, (stChart s₂).1 z = z) ∧ HasBdryLimits (stChart s₂).2.1 ∧ ContinuousOn (stChart s₂).2.1 H ∧
      (∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) ∧
      ∀ q ∈ Hbar, ‖extendFrom H (stChart s₂).2.1 q - q‖ ≤ 0 := by
  have h1 : ∀ z, (stChart s₂).1 z = z := fun z => by simp [hs, Chart.recenter, Chart.id]
  have h2 : ∀ z, (stChart s₂).2.1 z = z := fun z => by simp [hs, Chart.recenter, Chart.id]
  have hc : Continuous (stChart s₂).2.1 := by
    have : (stChart s₂).2.1 = id := funext h2
    rw [this]; exact continuous_id
  have hB : HasBdryLimits (stChart s₂).2.1 := fun x _ => ⟨_, (hc.tendsto x).mono_left nhdsWithin_le_nhds⟩
  refine ⟨h1, hB, hc.continuousOn, fun w _ => by rw [h2, h1], fun q hq => ?_⟩
  have : (𝓝[H] q).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
    exact hq
  have hid : (stChart s₂).2.1 = id := funext h2
  have hq' : extendFrom H (stChart s₂).2.1 q = q := by
    have h3 := hB.tendsto hq
    rw [hid] at h3 ⊢
    exact tendsto_nhds_unique h3 (tendsto_id.mono_left nhdsWithin_le_nhds)
  rw [hq', sub_self, norm_zero]

/-- The lifted good points lie in `ℍ` (the identity relative chart's domain). -/
theorem root_dom (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState}
    (hs : stChart s₂ = Chart.id.recenter 0) : ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H := by
  intro t ht
  obtain ⟨w, hw, hwe⟩ := ht.2
  have hl : liftPt c m (p t) = w + m := by rw [liftPt, ← hwe, hc1 w hw]
  refine ⟨liftPt c m (p t), ?_, by simp [hs, Chart.recenter, Chart.id]⟩
  rw [hl]
  show 0 < (w + (m : ℂ)).im
  have hw' : 0 < w.im := hw
  simpa using hw'

/-- **The relative facts at a finite root.** -/
theorem root_stageRelFinP (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {p : ℝ≥0 → ℂ} {L₁ : ℝ≥0} (hL₁ : 0 < L₁)
    {s₂ : ExplState} (hs : stChart s₂ = Chart.id.recenter 0)
    (hPc : ContinuousOn p {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)})
    (hinj : InjOn p {t : ℝ≥0 | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)}) (hp0 : p 0 = β₀ tL)
    (htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)}, p t ∈ β₀ '' Ici tL)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (L₁ : ℝ≥0∞)} ⊆ closure (goodTp c p L₁)) {e₂ : Drv}
    (he₂ : e₂.2 = capLife (stCurvep c m p L₁ s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L₁ s₂)))
    (hreg : IsRegularDriver e₂) : StageRelFinP c m p L₁ s₂ e₂ := by
  obtain ⟨hs₁, hB, hcH₂, hc1₂, -⟩ := root_chart_facts hs
  obtain ⟨hρ, ⟨z, hz⟩, hHbar⟩ := root_fin hγ hβ hcH hc1 hoff hL₁ hs₁ hPc hinj hp0 htl hgd
  exact stageRelFinP_of hρ he₂ hgen hreg hz hHbar hB hcH₂ hc1₂ (root_dom hc1 hs)

/-- **The relative facts at an infinite root**, given its infinite capacity lifetime. -/
theorem root_stageRelInfP (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {p : ℝ≥0 → ℂ} {s₂ : ExplState}
    (hs : stChart s₂ = Chart.id.recenter 0) (hPc : Continuous p) (hinj : Function.Injective p)
    (hp0 : p 0 = β₀ tL) (htl : ∀ t, p t ∈ β₀ '' Ici tL) (hgd : ∀ t, t ∈ closure (goodTp c p ⊤))
    (htrp : Tendsto (fun t => ‖p t‖) atTop atTop) {e₂ : Drv} (he₂ : e₂.2 = capLife (stCurvep c m p ⊤ s₂))
    (hreg : IsRegularDriver e₂) (htop : capLife (stCurvep c m p ⊤ s₂) = ⊤) : StageRelInfP c m p ⊤ s₂ e₂ := by
  obtain ⟨hs₁, hB, hcH₂, hc1₂, hC⟩ := root_chart_facts hs
  obtain ⟨hρ, htr, hHbar⟩ := root_inf hγ hβ hcH hc1 hoff hs₁ hPc hinj hp0 htl hgd htrp
  exact stageRelInfP_of hρ he₂ hreg htop htr hHbar hB hC hcH₂ hc1₂ (root_dom hc1 hs)

end InteractingSLE.Theorem14.SB.Lk
