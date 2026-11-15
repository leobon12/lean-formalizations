/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XqLift
import InteractingSLE.Spec.Supplement.SB2XpV3
import InteractingSLE.Spec.Supplement.SB2JiClock

/-!
# The lift clause at a stage of the v3 rule: the good-time identities and the clustering argument

Packet PROVE-T14-SB2LIFT (round 27). At a stage of PROVE-SB2-LIFTSET's v3 rule, B's (shifted) piece is
`p t = pcPt s₁ e₁ (t₀ + t)` on `[0, L]`, the stage curve is `ρ = stCurvep c m p L s₂`, and the relative chain's lift
is `γ = liftCurve ρ L₁ α` (finite `L = L₁`) or `liftCurveTop ρ α` (`L = ∞`), `α` the continuous extension of the
capacity trace of `ρ` (`StageRelP`).

* **`liftCurve_good`**, **`liftCurveTop_good`**: at a good time `t` (B's point in the upper chart's domain), the lift
  is the stage value `c₁.1 (c.1 (p t) + m)`;
* **`stageInv_good`**: there the inverse `G` of the relative chart in B's stage coordinates returns B's own trace,
  `G (γ t) = trOf e₁ (t₀ + t)` (a real trace point would put B's point off B's stage domain);
* **`liftClause_of_good`**: hence, by density of the good times, continuity of `γ` and of B's trace, and clustering
  (`tendsto_stageInv_of_seq`), `G` tends to `trOf e₁ (t₀ + s)` at `γ s` for every `s < L` — at the start point and at
  boundary touches as well.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk Sec7.PocketTraversal Sec7.Lemma71C

variable {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {e₂ : Drv} {α : ℝ≥0 → ℂ}

/-- **The finite-horizon lift at a good time** is the stage value. -/
theorem liftCurve_good (hρ : IsDrivenCurve (stCurvep c m p L s₂)) (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurvep c m p L s₂) τ) {L₁ : ℝ≥0}
    (hL : L = L₁) {t : ℝ≥0} (ht : t ∈ goodTp c p L) (htL : t < L₁) :
    liftCurve (stCurvep c m p L s₂) L₁ α t = (stChart s₂).1 (Lk.liftPt c m (p t)) := by
  have htL' : (t : ℝ) < L₁ := NNReal.coe_lt_coe.2 htL
  have hu0 : 0 ≤ (t : ℝ) / (L₁ - t) := div_nonneg t.2 (sub_nonneg.2 htL'.le)
  have hcap0 : 0 ≤ capClock (stCurvep c m p L s₂) ((t : ℝ) / (L₁ - t)) := hρ.capClock_nonneg hu0
  have hlt : (((capClock (stCurvep c m p L s₂) ((t : ℝ) / (L₁ - t))).toNNReal : ℝ≥0) : ℝ≥0∞) < e₂.2 := by
    rw [he₂]
    exact hρ.ofReal_capClock_lt hu0
  unfold liftCurve
  rw [hαeq _ hlt]
  unfold capTrace
  rw [Real.coe_toNNReal _ hcap0, hρ.capInv_eq hu0, stCurvep_of_fin (by rw [hL]; exact ENNReal.coe_ne_top)]
  have hclk : clockOf L.toReal ((t : ℝ) / (L₁ - t)) = t := by
    rw [hL, ENNReal.coe_toReal]
    exact Lk.clockOf_div_sub ⟨t.2, htL'⟩
  rw [hclk, Real.toNNReal_coe, stValp_of_good ht]
  rfl

/-- **The infinite-horizon lift at a good time** is the stage value. -/
theorem liftCurveTop_good (hρ : IsDrivenCurve (stCurvep c m p L s₂)) (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurvep c m p L s₂) τ) (hL : L = ⊤) {t : ℝ≥0}
    (ht : t ∈ goodTp c p L) :
    liftCurveTop (stCurvep c m p L s₂) α t = (stChart s₂).1 (Lk.liftPt c m (p t)) := by
  have hu0 : (0 : ℝ) ≤ t := t.2
  have hcap0 : 0 ≤ capClock (stCurvep c m p L s₂) (t : ℝ) := hρ.capClock_nonneg hu0
  have hlt : (((capClock (stCurvep c m p L s₂) (t : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) < e₂.2 := by
    rw [he₂]
    exact hρ.ofReal_capClock_lt hu0
  unfold liftCurveTop
  rw [hαeq _ hlt]
  unfold capTrace
  rw [Real.coe_toNNReal _ hcap0, hρ.capInv_eq hu0, stCurvep_of_top hL, Real.toNNReal_coe, stValp_of_good ht]
  rfl

/-- **At a good time the relative chart's inverse in B's stage coordinates returns B's trace.** -/
theorem stageInv_good {s₁ : ExplState} {e₁ : Drv} {t₀ : ℝ≥0} {Bp : Set ℂ}
    (hℓ : IsDomainChart (H \ fillH Bp) (stChart s₁)) {Fℓ : ℂ → ℂ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto (stChart s₁).2.1 (𝓝[H] q) (𝓝 (Fℓ q))) (hc : c.IsConformal)
    (hc₁ : (stChart s₂).IsConformal)
    (hmaps : ∀ y ∈ H, c.2.1 ((stChart s₂).2.1 y - (m : ℂ)) ∈ H \ fillH Bp) {t : ℝ≥0}
    (htrH : LuM.trOf e₁ (t₀ + t) ∈ Hbar)
    (ht : t ∈ goodTp c (fun t => pcPt s₁ e₁ (t₀ + t)) L)
    (hlift : Lk.liftPt c m (pcPt s₁ e₁ (t₀ + t)) ∈ (stChart s₂).2.1 '' H) :
    (stChart s₂).1 (Lk.liftPt c m (pcPt s₁ e₁ (t₀ + t))) ∈ H ∧
      (stageRelChart (stChart s₁) c (stChart s₂) m).2.1
        ((stChart s₂).1 (Lk.liftPt c m (pcPt s₁ e₁ (t₀ + t)))) = LuM.trOf e₁ (t₀ + t) := by
  obtain ⟨w, hwH, hw⟩ := hlift
  have hy : (stChart s₂).1 (Lk.liftPt c m (pcPt s₁ e₁ (t₀ + t))) = w := by rw [← hw, hc₁.2.2 w hwH]
  refine ⟨hy ▸ hwH, ?_⟩
  obtain ⟨w', hw'H, hw'⟩ := ht.2
  replace hw' : c.2.1 w' = pcPt s₁ e₁ (t₀ + t) := hw'
  have hP : (stChart s₂).2.1 w - (m : ℂ) = c.1 (pcPt s₁ e₁ (t₀ + t)) := by
    rw [hw, Lk.liftPt, add_sub_cancel_right]
  have hcc : c.2.1 (c.1 (pcPt s₁ e₁ (t₀ + t))) = pcPt s₁ e₁ (t₀ + t) := by
    rw [← hw', hc.2.2 w' hw'H]
  have hPmem : pcPt s₁ e₁ (t₀ + t) ∈ H \ fillH Bp := by
    have := hmaps w hwH
    rwa [hP, hcc] at this
  rw [stageRelChart_inv, hy, hP, hcc]
  have hbd : pcPt s₁ e₁ (t₀ + t) = Fℓ (LuM.trOf e₁ (t₀ + t)) :=
    LuM.bdVal_eq_of_tendsto htrH (hFℓ _ htrH)
  by_cases hτH : LuM.trOf e₁ (t₀ + t) ∈ H
  · have hFeq : Fℓ (LuM.trOf e₁ (t₀ + t)) = (stChart s₁).2.1 (LuM.trOf e₁ (t₀ + t)) := by
      have hτb : LuM.trOf e₁ (t₀ + t) ∈ Hbar := htrH
      have : (𝓝[H] (LuM.trOf e₁ (t₀ + t))).NeBot := GW1P.neBot_nhdsWithin_H hτb
      exact tendsto_nhds_unique (hFℓ _ hτb) (hℓ.1.1.continuousOn _ hτH)
    rw [hbd, hFeq, hℓ.fwd_inv hτH]
  · exfalso
    have him : (LuM.trOf e₁ (t₀ + t)).im = 0 := le_antisymm (not_lt.1 hτH) htrH
    obtain ⟨x', hx'⟩ : ∃ x' : ℝ, LuM.trOf e₁ (t₀ + t) = (x' : ℂ) :=
      ⟨(LuM.trOf e₁ (t₀ + t)).re, Complex.ext (by simp) (by simp [him])⟩
    have hlim := hFℓ _ htrH
    rw [hx'] at hlim
    have hnot := FinRel.notMem_image_of_tendsto_inv hℓ.1 hlim
    rw [← hx', ← hbd, hℓ.image_eq] at hnot
    exact hnot hPmem

/-- **The lift clause from the good times** (clustering): the relative chart's inverse in B's stage coordinates tends
to B's trace at every point of the lift before B's (shifted) lifetime. -/
theorem liftClause_of_good {s₁ : ExplState} {e₁ : Drv} {t₀ : ℝ≥0} {Bp : Set ℂ}
    (hℓ : IsDomainChart (H \ fillH Bp) (stChart s₁)) {Fℓ : ℂ → ℂ} {Cℓ : ℝ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto (stChart s₁).2.1 (𝓝[H] q) (𝓝 (Fℓ q))) (hCℓ : ∀ q ∈ Hbar, ‖Fℓ q - q‖ ≤ Cℓ)
    (hc : c.IsConformal) {ĝ : ℂ → ℂ} {Cg : ℝ} (hĝ : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q)))
    (hCg : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ Cg) (hc₁ : (stChart s₂).IsConformal) {F₁ : ℂ → ℂ} {C₁ : ℝ}
    (hF₁ : ∀ q ∈ Hbar, Tendsto (stChart s₂).2.1 (𝓝[H] q) (𝓝 (F₁ q))) (hC₁ : ∀ q ∈ Hbar, ‖F₁ q - q‖ ≤ C₁)
    (hmaps : ∀ y ∈ H, c.2.1 ((stChart s₂).2.1 y - (m : ℂ)) ∈ H \ fillH Bp)
    (hdense : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c (fun t => pcPt s₁ e₁ (t₀ + t)) L))
    (hgoodlift : ∀ t ∈ goodTp c (fun t => pcPt s₁ e₁ (t₀ + t)) L,
      Lk.liftPt c m (pcPt s₁ e₁ (t₀ + t)) ∈ (stChart s₂).2.1 '' H)
    (htrH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → LuM.trOf e₁ (t₀ + t) ∈ Hbar)
    (htrc : ContinuousOn (fun t => LuM.trOf e₁ (t₀ + t)) {t | (t : ℝ≥0∞) ≤ L}) {γ : ℝ≥0 → ℂ}
    (hγgood : ∀ t ∈ goodTp c (fun t => pcPt s₁ e₁ (t₀ + t)) L, (t : ℝ≥0∞) < L →
      γ t = (stChart s₂).1 (Lk.liftPt c m (pcPt s₁ e₁ (t₀ + t))))
    (hγc : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L → ContinuousAt γ s) (hγH : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L → γ s ∈ Hbar) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < L →
      Tendsto (stageRelChart (stChart s₁) c (stChart s₂) m).2.1 (𝓝[H] (γ s)) (𝓝 (LuM.trOf e₁ (t₀ + s))) := by
  intro s hs
  obtain ⟨tn, htn, hlim⟩ := mem_closure_iff_seq_limit.1 (hdense hs)
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hev : ∀ᶠ n in atTop, (tn n : ℝ≥0∞) < L := hlim (hopen.mem_nhds hs)
  have hgood : ∀ᶠ n in atTop, γ (tn n) ∈ H ∧
      (stageRelChart (stChart s₁) c (stChart s₂) m).2.1 (γ (tn n)) = LuM.trOf e₁ (t₀ + tn n) := by
    filter_upwards [hev] with n hn
    rw [hγgood _ (htn n) hn]
    exact stageInv_good hℓ hFℓ hc hc₁ hmaps (htrH _ (htn n).1) (htn n) (hgoodlift _ (htn n))
  have hu : Tendsto (fun n => γ (tn n)) atTop (𝓝 (γ s)) := (hγc s hs).tendsto.comp hlim
  have hsL : s ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} := le_of_lt hs
  have htr : Tendsto (fun n => LuM.trOf e₁ (t₀ + tn n)) atTop (𝓝 (LuM.trOf e₁ (t₀ + s))) :=
    (htrc s hsL).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (htn n).1⟩)
  have hw : Tendsto (fun n => (stageRelChart (stChart s₁) c (stChart s₂) m).2.1 (γ (tn n))) atTop
      (𝓝 (LuM.trOf e₁ (t₀ + s))) :=
    htr.congr' (hgood.mono fun n hn => hn.2.symm)
  exact tendsto_stageInv_of_seq hℓ hc hc₁ hFℓ hCℓ hĝ hCg hF₁ hC₁ hmaps (hγH s hs)
    (hgood.mono fun n hn => hn.1) hu hw

end InteractingSLE.Theorem14.SB.Mn
