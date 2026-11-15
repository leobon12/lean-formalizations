/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XrGood
import InteractingSLE.Spec.Supplement.SB2BqHull
import InteractingSLE.Spec.Supplement.SB2LqPhys

/-!
# The chain clause of the per-stage correspondence at one stage: lift, relative chain with hull fields, lifetime

Packet PROVE-T14-SB2LIFT (round 27). At one stage of PROVE-SB2-LIFTSET's v3 rule (B's shifted piece
`p t = pcPt s₁ e₁ (t₀ + t)` on `[0, L]`, `L = e₁.2 − t₀`, the stage curve `ρ = stCurvep c m p L s₂`):

* **`retained_facts`**: the retained set `X` in B's stage coordinates lies in `ℍ`, is bounded and relatively closed, and
  its fill is itself (`Nq.fillH_eq_self_of_isDomainChart`), given the domain-chart clause (G1);
* **`stageClause`**: the conclusion `∃ tL γ, …` of `Mn.StageChainAtR2` at that stage, with `tL = t₀`:
  - the **lift clause** at every `s` before B's lifetime (`liftClause_of_good`, clustering);
  - the **relative chain** at every `S₀` before B's lifetime, with all fields of `FinRel.IsSB2RelChain`: the core
    (`relChainCore_gen`/`relChainCore_genTop`, driven by `EL`'s driver and its chosen trace) and GEOM2's two hull
    fields (`Bq.isSB2RelChain_of_core_lim`, the growth from the bounded displacement of the relative chart's inverse);
  - the **lifetime clause** (`lifetime_eq_iSup_gen`/`lifetime_eq_iSup_genTop`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk Sec7.PocketTraversal Sec7.Lemma71C
open FinRel (IsSB2RelChain)

/-- **The retained set in B's stage coordinates** lies in `ℍ`, is bounded and relatively closed, and is its own fill. -/
theorem retained_facts {cℓ Φ : Chart} {Y Bp : Set ℂ} (hℓ : IsDomainChart (H \ fillH Bp) cℓ) {Fℓ : ℂ → ℂ} {Cℓ : ℝ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto cℓ.2.1 (𝓝[H] q) (𝓝 (Fℓ q))) (hCℓ : ∀ q ∈ Hbar, ‖Fℓ q - q‖ ≤ Cℓ)
    (hY : IsCompact Y) (hDX : IsDomainChart (H \ stageRetained cℓ Y) Φ) :
    stageRetained cℓ Y ⊆ H ∧ Bornology.IsBounded (stageRetained cℓ Y) ∧
      closure (stageRetained cℓ Y) ∩ H ⊆ stageRetained cℓ Y ∧ fillH (stageRetained cℓ Y) = stageRetained cℓ Y := by
  have hXH : stageRetained cℓ Y ⊆ H := fun v hv => hv.1
  have hFeq : EqOn Fℓ cℓ.2.1 H := fun y hy => by
    have hyH : y ∈ Hbar := QuantumZipper.H_subset_Hbar hy
    have : (𝓝[H] y).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hFℓ y hyH) (hℓ.1.1.continuousOn y hy)
  have hXb : Bornology.IsBounded (stageRetained cℓ Y) := by
    obtain ⟨R, hR⟩ := (isBounded_fillH hY.isClosed hY.isBounded).exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨R + Cℓ, fun v hv => ?_⟩
    have h1 : ‖cℓ.2.1 v - v‖ ≤ Cℓ := by
      rw [← hFeq hv.1]
      exact hCℓ v (QuantumZipper.H_subset_Hbar hv.1)
    have h2 := hR _ hv.2
    calc ‖v‖ = ‖cℓ.2.1 v - (cℓ.2.1 v - v)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖cℓ.2.1 v‖ + ‖cℓ.2.1 v - v‖ := norm_sub_le _ _
      _ ≤ R + Cℓ := add_le_add h2 h1
  have hXc : closure (stageRetained cℓ Y) ∩ H ⊆ stageRetained cℓ Y := by
    rintro v ⟨hvc, hvH⟩
    by_contra hv
    have hopen : IsOpen (H \ stageRetained cℓ Y) := hDX.isOpen
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff_nhds.1 hvc _ (hopen.mem_nhds ⟨hvH, hv⟩)
    exact hz1.2 hz2
  exact ⟨hXH, hXb, hXc, Nq.fillH_eq_self_of_isDomainChart hXH hXb hXc hDX⟩

/-- A capacity extension `α` of the stage curve's capacity trace generates the relative driver on its closed horizon. -/
theorem isGeneratingTrace_ext {ρ : ℝ → ℂ} {e₂ : Drv} {α : ℝ≥0 → ℂ} (he₂ : e₂.2 = capLife ρ)
    (hgen : ∀ T < capLife ρ, IsGeneratingTrace e₂.1 T (capTrace ρ))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) (hα0 : α 0 = 0)
    (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) : IsGeneratingTrace e₂.1 e₂.2 α := by
  refine ⟨hα0, hαc, fun t ht => ?_⟩
  obtain ⟨T'', htT'', hT''⟩ := exists_between ht
  have h := (hgen T'' (by rw [← he₂]; exact hT'')).2.2 t htT''
  rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]

/-- B's time `tL + s` is before B's lifetime iff `s` is before the shifted lifetime. -/
theorem coe_add_lt_iff (t₀ s : ℝ≥0) (e : ℝ≥0∞) :
    ((t₀ + s : ℝ≥0) : ℝ≥0∞) < e ↔ (s : ℝ≥0∞) < e - t₀ := by
  rw [ENNReal.coe_add]
  exact lt_tsub_iff_left.symm

variable {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {t₀ : ℝ≥0} {A Bp : Set ℂ}

/-- **The stage clause of `StageChainAtR2` at one stage of the v3 rule** (lift, relative chain, lifetime). -/
theorem stageClause (hℓ : IsDomainChart (H \ fillH Bp) (stChart s₁)) {Fℓ : ℂ → ℂ} {Cℓ : ℝ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto (stChart s₁).2.1 (𝓝[H] q) (𝓝 (Fℓ q))) (hCℓ : ∀ q ∈ Hbar, ‖Fℓ q - q‖ ≤ Cℓ)
    (hc : c.IsConformal) {ĝ : ℂ → ℂ} {Cg : ℝ} (hĝ : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q)))
    (hCg : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ Cg) (hc₁ : (stChart s₂).IsConformal) {F₁ : ℂ → ℂ} {C₁ : ℝ}
    (hF₁ : ∀ q ∈ Hbar, Tendsto (stChart s₂).2.1 (𝓝[H] q) (𝓝 (F₁ q))) (hC₁ : ∀ q ∈ Hbar, ‖F₁ q - q‖ ≤ C₁)
    (hmaps : ∀ y ∈ H, c.2.1 ((stChart s₂).2.1 y - (m : ℂ)) ∈ H \ fillH (A ∪ Bp))
    (hDX : IsDomainChart (H \ stageRetained (stChart s₁) (A ∪ Bp)) (stageRelChart (stChart s₁) c (stChart s₂) m))
    (hAB : IsCompact (A ∪ Bp)) (hpr₁ : GW1P.PieceRegular e₁.1 e₁.2) (ht₀ : (t₀ : ℝ≥0∞) ≤ e₁.2)
    (hpre : ∀ r ≤ t₀, LuM.trOf e₁ r ∉ H \ fillH (stageRetained (stChart s₁) (A ∪ Bp)))
    (hρ : IsDrivenCurve (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂))
    (hgen : ∀ T < capLife (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂),
      IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂)))
    (hrel : StageRelP c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂ e₂)
    (hdense : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2 - t₀} ⊆
      closure (goodTp c (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀)))
    (hpr₂ : GW1P.PieceRegular e₂.1 e₂.2) (hL0 : e₁.2 - t₀ ≠ 0) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
      (∀ s : ℝ≥0, ((tL + s : ℝ≥0) : ℝ≥0∞) < e₁.2 →
        Tendsto (stageRelChart (stChart s₁) c (stChart s₂) m).2.1 (𝓝[H] (γ s)) (𝓝 (LuM.trOf e₁ (tL + s)))) ∧
      (∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < e₁.2 →
        ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
          (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
            Wr r = e₂.1 r.toNNReal ∧ ηr r = LuM.trOf e₂ r.toNNReal) ∧
          IsSB2RelChain (stageRetained (stChart s₁) (A ∪ Bp)) (stageRelChart (stChart s₁) c (stChart s₂) m)
            (LuM.trOf e₁) γ tL (S₀ : ℝ) Wr ηr) ∧
      e₂.2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < e₁.2),
        ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) := by
  set L : ℝ≥0∞ := e₁.2 - t₀ with hLdef
  set p : ℝ≥0 → ℂ := fun t => pcPt s₁ e₁ (t₀ + t) with hpdef
  set ρ := stCurvep c m p L s₂ with hρdef
  set Φ := stageRelChart (stChart s₁) c (stChart s₂) m with hΦ
  set X := stageRetained (stChart s₁) (A ∪ Bp) with hX
  have hmapsB : ∀ y ∈ H, c.2.1 ((stChart s₂).2.1 y - (m : ℂ)) ∈ H \ fillH Bp := fun y hy =>
    ⟨(hmaps y hy).1, fun h => (hmaps y hy).2 (fillH_mono subset_union_right h)⟩
  -- B's trace
  have hgen₁ := LuM.isGeneratingTrace_trOf hpr₁
  have hW₁lt : ContinuousOn e₁.1 {s | (s : ℝ≥0∞) < e₁.2} := hpr₁.2.1.mono fun _ (hs : _ < e₁.2) => le_of_lt hs
  have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → ((t₀ + t : ℝ≥0) : ℝ≥0∞) ≤ e₁.2 := fun t ht => by
    rw [ENNReal.coe_add]
    calc (t₀ : ℝ≥0∞) + t ≤ t₀ + (e₁.2 - t₀) := add_le_add le_rfl ht
      _ = e₁.2 := add_tsub_cancel_of_le ht₀
  have htrH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → LuM.trOf e₁ (t₀ + t) ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hgen₁ hW₁lt hpr₁.1 (hle t ht)
  have htrc : ContinuousOn (fun t => LuM.trOf e₁ (t₀ + t)) {t | (t : ℝ≥0∞) ≤ L} :=
    hgen₁.2.1.comp (continuous_const.add continuous_id).continuousOn fun t ht => hle t ht
  -- the inverse of the relative chart
  obtain ⟨-, -, hGb, -, -⟩ := stageInv_facts hℓ hc hc₁ hFℓ hCℓ hĝ hCg hF₁ hC₁ hmapsB
  have hgrow : ∀ w ∈ H, ‖w‖ ≤ 1 * ‖Φ.2.1 w‖ + (Cℓ + Cg + C₁ + |m|) := fun w hw => by
    have := hGb w hw
    calc ‖w‖ = ‖Φ.2.1 w - (Φ.2.1 w - w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Φ.2.1 w‖ + ‖Φ.2.1 w - w‖ := norm_sub_le _ _
      _ ≤ 1 * ‖Φ.2.1 w‖ + (Cℓ + Cg + C₁ + |m|) := by rw [one_mul]; exact add_le_add le_rfl this
  obtain ⟨-, -, -, hfX⟩ := retained_facts hℓ hFℓ hCℓ hAB hDX
  have hD' : IsDomainChart (H \ fillH X) Φ := by rw [hfX]; exact hDX
  have hβc : ∀ S₀ : ℝ≥0, ((t₀ + S₀ : ℝ≥0) : ℝ≥0∞) < e₁.2 →
      ContinuousOn (LuM.trOf e₁) (Icc 0 (t₀ + (S₀ : ℝ).toNNReal)) := fun S₀ hS₀ => by
    refine hgen₁.2.1.mono fun r hr => ?_
    rw [Real.toNNReal_coe] at hr
    exact le_trans (ENNReal.coe_le_coe.2 hr.2) hS₀.le
  -- the relative driver's facts and the capacity extension
  have hW₂lt : ContinuousOn e₂.1 {s | (s : ℝ≥0∞) < e₂.2} := hpr₂.2.1.mono fun _ (hs : _ < e₂.2) => le_of_lt hs
  by_cases hLt : L = ⊤
  · -- an infinite piece
    obtain ⟨hW, ⟨α, f, hαeq, hα0, hαc, -, -, -⟩, -, -, hgoodlift⟩ := hrel.2 hLt
    have hαg := isGeneratingTrace_ext he₂ hgen hαeq hα0 hαc
    have htr : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → LuM.trOf e₂ τ = α τ :=
      GW4Leaf.eqOn_of_isGeneratingTrace hαg (LuM.isGeneratingTrace_trOf hpr₂) hW₂lt hpr₂.1
    have hαH : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → α τ ∈ Hbar := fun τ hτ =>
      Sec7.IsGeneratingTrace.mem_Hbar hαg hW₂lt hpr₂.1 hτ
    have hmapsα : ∀ u : ℝ, 0 ≤ u → (((capClock ρ u).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := fun u hu => by
      rw [he₂]; exact le_of_lt (hρ.ofReal_capClock_lt hu)
    set γ := liftCurveTop ρ α with hγdef
    have hγcont : Continuous γ := by
      have hcc : Continuous fun s : ℝ≥0 => (capClock ρ (s : ℝ)).toNNReal :=
        continuous_real_toNNReal.comp (hρ.continuousOn_capClock.comp_continuous NNReal.continuous_coe
          fun s => show (0 : ℝ) ≤ s from s.2)
      exact hαc.comp_continuous hcc fun s => hmapsα s s.2
    have hlift : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L →
        Tendsto Φ.2.1 (𝓝[H] (γ s)) (𝓝 (LuM.trOf e₁ (t₀ + s))) :=
      liftClause_of_good hℓ hFℓ hCℓ hc hĝ hCg hc₁ hF₁ hC₁ hmapsB hdense hgoodlift htrH htrc
        (fun t ht _ => liftCurveTop_good hρ he₂ hαeq hLt ht) (fun s _ => hγcont.continuousAt)
        (fun s _ => hαH _ (hmapsα s s.2))
    have hall : ∀ S₀ : ℝ≥0, ((t₀ + S₀ : ℝ≥0) : ℝ≥0∞) < e₁.2 := fun S₀ => by
      have he₁ : e₁.2 = ⊤ := by
        have := tsub_le_self (a := e₁.2) (b := (t₀ : ℝ≥0∞))
        rw [← hLdef, hLt] at this
        exact top_le_iff.1 this
      rw [he₁]; exact ENNReal.coe_lt_top
    refine ⟨t₀, γ, fun s _ => hlift s (by rw [hLt]; exact ENNReal.coe_lt_top), fun S₀ hS₀ => ?_, ?_⟩
    · obtain ⟨Wr, ηr, hagree, hcore⟩ := relChainCore_genTop hρ he₂ hgen hW hpr₂.1 hαeq hα0 hαc S₀.2
      refine ⟨Wr, ηr, fun r hr0 hr => ?_, ?_⟩
      · obtain ⟨h1, h2⟩ := hagree r hr0 hr
        refine ⟨h1, ?_⟩
        have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := by
          rw [he₂]
          refine le_of_lt (lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt (NNReal.coe_nonneg S₀)))
          rw [← capClock_liftCurveTop hρ he₂ hαeq (NNReal.coe_nonneg S₀)]
          exact ENNReal.ofReal_le_ofReal hr
        rw [h2, htr _ hrle]
      · exact Bq.isSB2RelChain_of_core_lim hcore hD' zero_le_one hgrow le_rfl (hβc S₀ hS₀) hpre
          hγcont.continuousOn (fun s _ => hαH _ (hmapsα s s.2))
          (fun s _ => hlift s (by rw [hLt]; exact ENNReal.coe_lt_top))
    · rw [lifetime_eq_iSup_genTop hρ he₂ hαeq]
      refine iSup_congr fun S₀ => ?_
      rw [iSup_pos (hall S₀)]
  · -- a finite piece
    obtain ⟨hfin, hW, ⟨α, f, hαeq, hα0, hαc, -, -⟩, -, -, hgoodlift⟩ := hrel.1 hLt
    obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ≥0, L = L₁ := ⟨L.toNNReal, (ENNReal.coe_toNNReal hLt).symm⟩
    have hL₁pos : 0 < L₁ := by
      rw [hL₁] at hL0
      exact pos_iff_ne_zero.2 (by exact_mod_cast hL0)
    have hαg := isGeneratingTrace_ext he₂ hgen hαeq hα0 hαc
    have htr : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → LuM.trOf e₂ τ = α τ :=
      GW4Leaf.eqOn_of_isGeneratingTrace hαg (LuM.isGeneratingTrace_trOf hpr₂) hW₂lt hpr₂.1
    have hαH : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → α τ ∈ Hbar := fun τ hτ =>
      Sec7.IsGeneratingTrace.mem_Hbar hαg hW₂lt hpr₂.1 hτ
    have hiff : ∀ s : ℝ≥0, ((t₀ + s : ℝ≥0) : ℝ≥0∞) < e₁.2 ↔ s < L₁ := fun s => by
      rw [coe_add_lt_iff, ← hLdef, hL₁]
      exact ENNReal.coe_lt_coe
    have hu0 : ∀ s : ℝ≥0, s < L₁ → 0 ≤ (s : ℝ) / (L₁ - s) := fun s hs =>
      div_nonneg s.2 (sub_nonneg.2 (NNReal.coe_le_coe.2 hs.le))
    have hmapsα : ∀ s : ℝ≥0, s < L₁ →
        (((capClock ρ ((s : ℝ) / (L₁ - s))).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := fun s hs => by
      rw [he₂]; exact le_of_lt (hρ.ofReal_capClock_lt (hu0 s hs))
    set γ := liftCurve ρ L₁ α with hγdef
    have hγcont : ContinuousOn γ (Iio L₁) :=
      hαc.comp (continuous_real_toNNReal.comp_continuousOn (continuousOn_capClock_div hρ L₁))
        fun s hs => hmapsα s hs
    have hltL : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L → s < L₁ := fun s hs => by
      rw [hL₁] at hs; exact ENNReal.coe_lt_coe.1 hs
    have hlift : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L →
        Tendsto Φ.2.1 (𝓝[H] (γ s)) (𝓝 (LuM.trOf e₁ (t₀ + s))) :=
      liftClause_of_good hℓ hFℓ hCℓ hc hĝ hCg hc₁ hF₁ hC₁ hmapsB hdense hgoodlift htrH htrc
        (fun t ht htL => liftCurve_good hρ he₂ hαeq hL₁ ht (hltL t htL))
        (fun s hs => hγcont.continuousAt (Iio_mem_nhds (hltL s hs)))
        (fun s hs => hαH _ (hmapsα s (hltL s hs)))
    have hlift' : ∀ s : ℝ≥0, ((t₀ + s : ℝ≥0) : ℝ≥0∞) < e₁.2 →
        Tendsto Φ.2.1 (𝓝[H] (γ s)) (𝓝 (LuM.trOf e₁ (t₀ + s))) := fun s hs =>
      hlift s (by rw [hL₁]; exact ENNReal.coe_lt_coe.2 ((hiff s).1 hs))
    refine ⟨t₀, γ, hlift', fun S₀ hS₀ => ?_, ?_⟩
    · have hS₀L : (S₀ : ℝ) < L₁ := NNReal.coe_lt_coe.2 ((hiff S₀).1 hS₀)
      obtain ⟨Wr, ηr, hagree, hcore⟩ :=
        relChainCore_gen hρ he₂ hgen hfin hW hpr₂.1 hαeq hα0 hαc (NNReal.coe_nonneg S₀) hS₀L
      refine ⟨Wr, ηr, fun r hr0 hr => ?_, ?_⟩
      · obtain ⟨h1, h2⟩ := hagree r hr0 hr
        refine ⟨h1, ?_⟩
        have hu0' : 0 ≤ (S₀ : ℝ) / (L₁ - S₀) := div_nonneg (NNReal.coe_nonneg S₀) (sub_nonneg.2 hS₀L.le)
        have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := by
          rw [he₂]
          refine le_of_lt (lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt hu0'))
          rw [← capClock_liftCurve hρ he₂ hαeq (NNReal.coe_nonneg S₀) hS₀L]
          exact ENNReal.ofReal_le_ofReal hr
        rw [h2, htr _ hrle]
      · have hsub : ∀ s : ℝ≥0, (s : ℝ) ≤ S₀ → s < L₁ := fun s hs =>
          NNReal.coe_lt_coe.1 (lt_of_le_of_lt hs hS₀L)
        refine Bq.isSB2RelChain_of_core_lim hcore hD' zero_le_one hgrow le_rfl (hβc S₀ hS₀) hpre
          (hγcont.mono fun s hs => hsub s (by
            have := hs.2; rw [Real.toNNReal_coe] at this; exact NNReal.coe_le_coe.2 this))
          (fun s hs => hαH _ (hmapsα s (hsub s hs))) (fun s hs => ?_)
        exact hlift s (by rw [hL₁]; exact ENNReal.coe_lt_coe.2 (hsub s hs))
    · rw [lifetime_eq_iSup_gen hρ he₂ hαeq hL₁pos]
      exact iSup_congr fun S₀ => iSup_congr_Prop (hiff S₀).symm fun _ => rfl

end InteractingSLE.Theorem14.SB.Mn
