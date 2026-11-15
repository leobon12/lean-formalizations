/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JyTip

/-!
# SB2(2): the stage curve and its lift relation for a general point map (decision D6, option A)

Packet PROVE-SB2-LIFTSET (round 16). D6's v3 rule reads the start piece of a pure piece entry **from its visit time
`t_R` of `R`**. The stage-curve machinery of `SB2LjRule`/`SB2LjLift`/`SB2JiClock`/`SB2JiTop`/`SB2JyTip`, written for the
point map `pcPt s₁ e₁` on `[0, e₁.2]`, is restated here for a general point map `p` on `[0, L]` (the v3 rule takes
`p = pcPt s₁ e₁ (t_R + ·)`, `L = e₁.2 − t_R`; `t_R = 0` elsewhere). The actual piece enters only through its tip set
in `D`, which is now asked to be the image of the good times (`htipD`) — for the shifted start piece this holds since
the start piece has no good time before `t_R`.

* `goodTp`, `relValp`, `stValp`, **`stCurvep`**, `cTmp`, `cGdp`, `cTmTopp`, `cGdTopp`, with the clock bookkeeping
  (`hcov_of_drivenP`, `hdense_of_drivenP`, `hcov_topP`, `hdense_topP`, …);
* **`liftRel_concreteP`**, **`liftRel_concrete_drivenP`** (finite), **`liftRel_concrete_top2P`** (infinite).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {p : ℝ≥0 → ℂ}
  {L : ℝ≥0∞}

/-- The good times of the piece: up to its lifetime, with the point in the upper chart's domain `c.2.1 '' ℍ`. -/
def goodTp (c : Chart) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) : Set ℝ≥0 :=
  {t | (t : ℝ≥0∞) ≤ L ∧ p t ∈ c.2.1 '' H}

/-- The intrinsic lift `c.1 · + m` of the piece's point at time `t`, read in the relative chart at `s₂`. -/
def relValp (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (s₂ : ExplState) (t : ℝ≥0) : ℂ :=
  (stChart s₂).1 (liftPt c m (p t))

open Classical in
/-- The stage values: `relVal` at good times, its limit along the good times elsewhere. -/
def stValp (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (t : ℝ≥0) : ℂ :=
  if t ∈ goodTp c p L then relValp c m p s₂ t else limUnder (𝓝[goodTp c p L] t) (relValp c m p s₂)

/-- **The stage curve** on `[0, ∞)`: the stage values at actual time `u` (infinite lifetime) or `clockOf L u` (finite
lifetime `L`). -/
def stCurvep (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) : ℝ → ℂ :=
  fun u => stValp c m p L s₂ (if L = ⊤ then u else clockOf L.toReal u).toNNReal

theorem stValp_of_good {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {t : ℝ≥0}
    (ht : t ∈ goodTp c p L) : stValp c m p L s₂ t = relValp c m p s₂ t := by
  unfold stValp
  simp only [ht, ↓reduceIte]

theorem stCurvep_of_fin {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} (he : L ≠ ⊤) (u : ℝ) :
    stCurvep c m p L s₂ u = stValp c m p L s₂ (clockOf L.toReal u).toNNReal := by
  unfold stCurvep
  simp only [he, ↓reduceIte]

theorem stCurvep_of_top {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} (he : L = ⊤) (u : ℝ) :
    stCurvep c m p L s₂ u = stValp c m p L s₂ u.toNNReal := by
  unfold stCurvep
  simp only [he, ↓reduceIte]


/-- The actual time `clockOf L (capInv ρ τ)` of relative capacity time `τ` (`ρ` the stage curve, `L` the actual
lifetime). -/
def cTmp (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (τ : ℝ≥0) : ℝ≥0 :=
  (clockOf L.toReal (capInv (stCurvep c m p L s₂) τ)).toNNReal

/-- The relative good times: before the relative lifetime, with good actual time. -/
def cGdp (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (e₂ : Drv) : Set ℝ≥0 :=
  {τ | (τ : ℝ≥0∞) < e₂.2 ∧ cTmp c m p L s₂ τ ∈ goodTp c p L}

/-- **The lift relation at a concrete relative stage** (finite actual piece): a relative driver `e₂` generating the
stage curve `stCurvep c m p L s₂` below its capacity lifetime launches, from `s₂`, the lift of the actual piece
launched from `s₁` with `e₁`. The value identity of `liftRel_of_stage` is proved from the stage curve's definition and
the relative chart's inverse identity on its domain. -/
theorem liftRel_concreteP {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w)
    (hoff : BdryOff c) {s₁ s₂ : ExplState} {e₁ e₂ : Drv}
    (hTc : IsCompact {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
      closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H})
    (htipD : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H = p '' goodTp c p L)
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (he₁ : L ≠ ⊤) (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurvep c m p L s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H)
    (hdense₂ : {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} ⊆ closure (cGdp c m p L s₂ e₂))
    (hcov : liftPt c m '' (p '' goodTp c p L) ⊆
      closure ((fun τ => liftPt c m (p (cTmp c m p L s₂ τ))) '' cGdp c m p L s₂ e₂)) :
    LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) := by
  have hα : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T', htT', hT'⟩ := exists_between ht
    have h := (hgen T' (by rw [← he₂]; exact hT')).2.2 t htT'
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  refine liftRel_of_stage_cl hγ hcH hc1 hoff hTc hdense₁ hα hW hW0 hc hfin hgc (fun τ h => le_of_lt h.1) hdense₂
    (v := fun τ => liftPt c m (p (cTmp c m p L s₂ τ))) ?_ ?_ ?_
  · rintro τ ⟨hτ, hg⟩
    obtain ⟨z, hz, hzw⟩ := hdom _ hg
    have hατ : α τ = z := by
      rw [hαeq τ hτ]
      show stCurvep c m p L s₂ (capInv (stCurvep c m p L s₂) τ) = z
      rw [stCurvep_of_fin he₁]
      change stValp c m p L s₂ (cTmp c m p L s₂ τ) = z
      rw [stValp_of_good hg]
      unfold relValp
      rw [← hzw, hc1₂ z hz]
    have hlim := hc τ (le_of_lt hτ)
    rw [hατ] at hlim
    have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hz)
    rw [hατ, tendsto_nhds_unique hlim (hcH₂ z hz), hzw]
  · rintro _ ⟨τ, ⟨-, hg⟩, rfl⟩
    have hmem : p (cTmp c m p L s₂ τ) ∈
        (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H := by
      rw [htipD]
      exact ⟨_, hg, rfl⟩
    exact ⟨_, ⟨hmem, htail hmem⟩, rfl⟩
  · rintro _ ⟨z, ⟨hzD, -⟩, rfl⟩
    have hz' : z ∈ p '' goodTp c p L := by rw [← htipD]; exact hzD
    obtain ⟨t, ht, rfl⟩ := hz'
    exact hcov ⟨_, ⟨t, ht, rfl⟩, rfl⟩


theorem cTm_capClockP (hρ : IsDrivenCurve (stCurvep c m p L s₂)) {u : ℝ} (hu : 0 ≤ u) :
    cTmp c m p L s₂ (capClock (stCurvep c m p L s₂) u).toNNReal = (clockOf L.toReal u).toNNReal := by
  unfold cTmp
  rw [Real.coe_toNNReal _ (hρ.capClock_nonneg hu), hρ.capInv_eq hu]

theorem capClock_mem_cGdP (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂)) {u : ℝ} (hu : 0 ≤ u)
    (hg : (clockOf L.toReal u).toNNReal ∈ goodTp c p L) :
    (capClock (stCurvep c m p L s₂) u).toNNReal ∈ cGdp c m p L s₂ e₂ := by
  refine ⟨?_, by rw [cTm_capClockP hρ hu]; exact hg⟩
  rw [he₂]
  exact hρ.ofReal_capClock_lt hu

/-- Every good actual time before the lifetime is the actual time of a relative good time. -/
theorem lift_mem_of_ltP (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂)) (he₁ : L ≠ ⊤) {t : ℝ≥0} (ht : t ∈ goodTp c p L)
    (hlt : (t : ℝ≥0∞) < L) :
    liftPt c m (p t) ∈
      (fun τ => liftPt c m (p (cTmp c m p L s₂ τ))) '' cGdp c m p L s₂ e₂ := by
  have hlt' : (t : ℝ) < L.toReal := (coe_lt_iff_toReal he₁).1 hlt
  have hmem : (t : ℝ) ∈ Ico 0 L.toReal := ⟨NNReal.coe_nonneg t, hlt'⟩
  have hu : 0 ≤ (t : ℝ) / (L.toReal - t) := div_nonneg (NNReal.coe_nonneg t) (by linarith)
  have hc : (clockOf L.toReal ((t : ℝ) / (L.toReal - t))).toNNReal = t := by
    rw [clockOf_div_sub hmem, Real.toNNReal_coe]
  refine ⟨_, capClock_mem_cGdP hρ he₂ hu (by rw [hc]; exact ht), ?_⟩
  simp only [cTm_capClockP hρ hu, hc]

/-- **The cover of the lifted good points** for a driven stage curve: every lifted good point before the lifetime is
a value at a relative good time; the lifted endpoint (when good) is assumed a limit of lifted good points before it. -/
theorem hcov_of_drivenP (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂)) (he₁ : L ≠ ⊤)
    (hend : ∀ t ∈ goodTp c p L, (t : ℝ≥0∞) = L → liftPt c m (p t) ∈
      closure ((fun t' => liftPt c m (p t')) '' (goodTp c p L ∩ {t' | (t' : ℝ≥0∞) < L}))) :
    liftPt c m '' (p '' goodTp c p L) ⊆
      closure ((fun τ => liftPt c m (p (cTmp c m p L s₂ τ))) '' cGdp c m p L s₂ e₂) := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  rcases lt_or_eq_of_le ht.1 with hlt | heq
  · exact subset_closure (lift_mem_of_ltP hρ he₂ he₁ ht hlt)
  · refine closure_minimal ?_ isClosed_closure (hend t ht heq)
    rintro _ ⟨t', ⟨ht', hlt'⟩, rfl⟩
    exact subset_closure (lift_mem_of_ltP hρ he₂ he₁ ht' hlt')

/-- **The density of the relative good times** for a driven stage curve, from the density of the good actual times
in `[0, L)` (the map `t ↦ capClock ρ (t / (L - t))` is continuous on `[0, L)` and sends good times to relative good
times). -/
theorem hdense_of_drivenP (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂)) (he₁ : L ≠ ⊤) (hpos : L ≠ 0)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L)) :
    {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} ⊆ closure (cGdp c m p L s₂ e₂) := by
  have hL0 : 0 < L.toReal := ENNReal.toReal_pos hpos he₁
  have hSo : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hφG : (fun t : ℝ≥0 => (capClock (stCurvep c m p L s₂) ((t : ℝ) / (L.toReal - t))).toNNReal) ''
      (goodTp c p L ∩ {t : ℝ≥0 | (t : ℝ≥0∞) < L}) ⊆ cGdp c m p L s₂ e₂ := by
    rintro _ ⟨t, ⟨ht, hlt⟩, rfl⟩
    have hlt' : (t : ℝ) < L.toReal := (coe_lt_iff_toReal he₁).1 hlt
    have hu : 0 ≤ (t : ℝ) / (L.toReal - t) := div_nonneg (NNReal.coe_nonneg t) (by linarith)
    refine capClock_mem_cGdP hρ he₂ hu ?_
    rw [clockOf_div_sub ⟨NNReal.coe_nonneg t, hlt'⟩, Real.toNNReal_coe]
    exact ht
  have hφc : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < L}, ContinuousWithinAt
      (fun t : ℝ≥0 => (capClock (stCurvep c m p L s₂) ((t : ℝ) / (L.toReal - t))).toNNReal)
      {t : ℝ≥0 | (t : ℝ≥0∞) < L} t := by
    intro t ht
    have hlt' : (t : ℝ) < L.toReal := (coe_lt_iff_toReal he₁).1 ht
    have hg : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ) / (L.toReal - t)) {t : ℝ≥0 | (t : ℝ≥0∞) < L} t :=
      (NNReal.continuous_coe.continuousAt.div (continuous_const.sub NNReal.continuous_coe).continuousAt
        (sub_pos.2 hlt').ne').continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ≥0 => (t : ℝ) / (L.toReal - t)) {t : ℝ≥0 | (t : ℝ≥0∞) < L} (Ici 0) :=
      fun t' ht' => div_nonneg (NNReal.coe_nonneg t') (by linarith [(coe_lt_iff_toReal he₁).1 ht'])
    have hcap := ContinuousWithinAt.comp (f := fun t : ℝ≥0 => (t : ℝ) / (L.toReal - t))
      (g := capClock (stCurvep c m p L s₂)) (hρ.continuousOn_capClock _ (hmaps ht)) hg hmaps
    exact continuous_real_toNNReal.continuousAt.comp_continuousWithinAt hcap
  have hpos₂ : 0 < e₂.2 := by
    rw [he₂]
    simpa [hρ.capClock_zero] using hρ.ofReal_capClock_lt (le_refl (0 : ℝ))
  refine le_subset_closure_of_lt hpos₂ fun τ hτ => ?_
  rw [he₂] at hτ
  have hs : ENNReal.ofReal (τ : ℝ) < capLife (stCurvep c m p L s₂) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hu, hcu⟩ := hρ.capInv_spec (NNReal.coe_nonneg τ) hs
  have ht₀ : ((clockOf L.toReal (capInv (stCurvep c m p L s₂) τ)).toNNReal : ℝ) =
      clockOf L.toReal (capInv (stCurvep c m p L s₂) τ) := Real.coe_toNNReal _ (clockOf_nonneg hL0 hu)
  have ht₀S : (clockOf L.toReal (capInv (stCurvep c m p L s₂) τ)).toNNReal ∈
      {t : ℝ≥0 | (t : ℝ≥0∞) < L} := by
    rw [mem_ofPred_eq, coe_lt_iff_toReal he₁, ht₀]
    exact clockOf_lt hL0 hu
  have hφt₀ : (capClock (stCurvep c m p L s₂)
      (((clockOf L.toReal (capInv (stCurvep c m p L s₂) τ)).toNNReal : ℝ) /
        (L.toReal - (clockOf L.toReal (capInv (stCurvep c m p L s₂) τ)).toNNReal))).toNNReal = τ := by
    rw [ht₀, div_sub_clockOf hL0 hu, hcu, Real.toNNReal_coe]
  have hcl : (clockOf L.toReal (capInv (stCurvep c m p L s₂) τ)).toNNReal ∈
      closure (goodTp c p L ∩ {t : ℝ≥0 | (t : ℝ≥0∞) < L}) := by
    have h := hSo.inter_closure ⟨ht₀S, hgd ht₀S⟩
    rwa [inter_comm] at h
  have h1 := ((hφc _ ht₀S).mono inter_subset_right).mem_closure_image hcl
  rw [hφt₀] at h1
  exact closure_minimal (hφG.trans subset_closure) isClosed_closure h1

/-! ### Infinite actual lifetime -/

/-- The actual time `capInv ρ τ` of relative capacity time `τ` (infinite actual lifetime). -/
def cTmTopp (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (τ : ℝ≥0) : ℝ≥0 :=
  (capInv (stCurvep c m p L s₂) τ).toNNReal

/-- The relative good times (infinite actual lifetime). -/
def cGdTopp (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (e₂ : Drv) : Set ℝ≥0 :=
  {τ | (τ : ℝ≥0∞) < e₂.2 ∧ cTmTopp c m p L s₂ τ ∈ goodTp c p L}

theorem cTmTop_capClockP (hρ : IsDrivenCurve (stCurvep c m p L s₂)) (t : ℝ≥0) :
    cTmTopp c m p L s₂ (capClock (stCurvep c m p L s₂) t).toNNReal = t := by
  unfold cTmTopp
  rw [Real.coe_toNNReal _ (hρ.capClock_nonneg (NNReal.coe_nonneg t)), hρ.capInv_eq (NNReal.coe_nonneg t),
    Real.toNNReal_coe]

theorem capClock_mem_cGdTopP (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂)) {t : ℝ≥0} (hg : t ∈ goodTp c p L) :
    (capClock (stCurvep c m p L s₂) t).toNNReal ∈ cGdTopp c m p L s₂ e₂ :=
  ⟨by rw [he₂]; exact hρ.ofReal_capClock_lt (NNReal.coe_nonneg t), by rw [cTmTop_capClockP hρ]; exact hg⟩

/-- **The cover at infinite actual lifetime**: every lifted good point is a value at a relative good time. -/
theorem hcov_topP (hρ : IsDrivenCurve (stCurvep c m p L s₂)) (he₂ : e₂.2 = capLife (stCurvep c m p L s₂)) :
    liftPt c m '' (p '' goodTp c p L) ⊆
      closure ((fun τ => liftPt c m (p (cTmTopp c m p L s₂ τ))) '' cGdTopp c m p L s₂ e₂) := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  refine subset_closure ⟨_, capClock_mem_cGdTopP hρ he₂ ht, ?_⟩
  simp only [cTmTop_capClockP hρ]

/-- **The density at infinite actual lifetime**, from the density of the good actual times. -/
theorem hdense_topP (hρ : IsDrivenCurve (stCurvep c m p L s₂)) (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (he₁ : L = ⊤) (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L)) :
    {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} ⊆ closure (cGdTopp c m p L s₂ e₂) := by
  have hφc : ∀ t : ℝ≥0, ContinuousAt (fun t : ℝ≥0 => (capClock (stCurvep c m p L s₂) t).toNNReal) t := by
    intro t
    have hcap : ContinuousAt (fun t : ℝ≥0 => capClock (stCurvep c m p L s₂) t) t := by
      have h1 := (hρ.continuousOn_capClock (t : ℝ) (mem_Ici.2 (NNReal.coe_nonneg t))).comp
        NNReal.continuous_coe.continuousWithinAt (s := univ) (fun t' _ => mem_Ici.2 (NNReal.coe_nonneg t'))
      exact continuousWithinAt_univ _ _ |>.1 h1
    exact continuous_real_toNNReal.continuousAt.comp hcap
  have hpos₂ : 0 < e₂.2 := by
    rw [he₂]
    simpa [hρ.capClock_zero] using hρ.ofReal_capClock_lt (le_refl (0 : ℝ))
  refine le_subset_closure_of_lt hpos₂ fun τ hτ => ?_
  rw [he₂] at hτ
  have hs : ENNReal.ofReal (τ : ℝ) < capLife (stCurvep c m p L s₂) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hu, hcu⟩ := hρ.capInv_spec (NNReal.coe_nonneg τ) hs
  have ht₀ : ((capInv (stCurvep c m p L s₂) τ).toNNReal : ℝ) = capInv (stCurvep c m p L s₂) τ :=
    Real.coe_toNNReal _ hu
  have hcl : (capInv (stCurvep c m p L s₂) τ).toNNReal ∈ closure (goodTp c p L) :=
    hgd (by rw [mem_ofPred_eq, he₁]; exact ENNReal.coe_lt_top)
  have h1 := (hφc _).continuousWithinAt.mem_closure_image hcl
  rw [ht₀, hcu, Real.toNNReal_coe] at h1
  refine closure_minimal ?_ isClosed_closure h1
  rintro _ ⟨t, ht, rfl⟩
  exact subset_closure (capClock_mem_cGdTopP hρ he₂ ht)


/-- **The lift relation at a concrete stage, driven stage curve, finite actual lifetime**: `liftRel_concreteP` with
the capacity bookkeeping (`hdense₂`, `hcov`) discharged by the drivenness of the stage curve. -/
theorem liftRel_concrete_drivenP (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    (hTc : IsCompact {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
      closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H})
    (htipD : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H = p '' goodTp c p L)
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (he₁ : L ≠ ⊤) (hpos : L ≠ 0) (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurvep c m p L s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L))
    (hend : ∀ t ∈ goodTp c p L, (t : ℝ≥0∞) = L → liftPt c m (p t) ∈
      closure ((fun t' => liftPt c m (p t')) '' (goodTp c p L ∩ {t' | (t' : ℝ≥0∞) < L}))) :
    LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) :=
  liftRel_concreteP hγ hcH hc1 hoff hTc hdense₁ htipD htail he₁ he₂ hgen hfin hW hW0 hαeq hα0 hαc hc hgc hcH₂ hc1₂
    hdom (hdense_of_drivenP hρ he₂ he₁ hpos hgd) (hcov_of_drivenP hρ he₂ he₁ hend)


/-- **The lift relation at a concrete stage, infinite actual lifetime, closed tail times** (the corrected
`liftRel_concrete_top`). -/
theorem liftRel_concrete_top2P (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    (hTcl : IsClosed {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
      closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H})
    (htipD : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H = p '' goodTp c p L)
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (he₁ : L = ⊤) (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurvep c m p L s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hclosed : IsClosed ((fun τ => f (α τ)) '' {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2}))
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L)) :
    LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) := by
  have hα := isGeneratingTrace_ext he₂ hgen hαeq hα0 hαc
  refine liftRel_of_stage_closed2 hγ hcH hc1 hoff hTcl hdense₁ hα hW hW0 hc hclosed hgc
    (fun τ h => le_of_lt h.1) (hdense_topP hρ he₂ he₁ hgd)
    (v := fun τ => liftPt c m (p (cTmTopp c m p L s₂ τ))) ?_ ?_ ?_
  · rintro τ ⟨hτ, hg⟩
    obtain ⟨z, hz, hzw⟩ := hdom _ hg
    have hατ : α τ = z := by
      rw [hαeq τ hτ]
      show stCurvep c m p L s₂ (capInv (stCurvep c m p L s₂) τ) = z
      rw [stCurvep_of_top he₁]
      change stValp c m p L s₂ (cTmTopp c m p L s₂ τ) = z
      rw [stValp_of_good hg]
      unfold relValp
      rw [← hzw, hc1₂ z hz]
    have hlim := hc τ (le_of_lt hτ)
    rw [hατ] at hlim
    have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hz)
    rw [hατ, tendsto_nhds_unique hlim (hcH₂ z hz), hzw]
  · rintro _ ⟨τ, ⟨-, hg⟩, rfl⟩
    have hmem : p (cTmTopp c m p L s₂ τ) ∈
        (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H := by
      rw [htipD]
      exact ⟨_, hg, rfl⟩
    exact ⟨_, ⟨hmem, htail hmem⟩, rfl⟩
  · rintro _ ⟨z, ⟨hzD, -⟩, rfl⟩
    have hz' : z ∈ p '' goodTp c p L := by rw [← htipD]; exact hzD
    obtain ⟨t, ht, rfl⟩ := hz'
    exact hcov_topP hρ he₂ ⟨_, ⟨t, ht, rfl⟩, rfl⟩


end InteractingSLE.Theorem14.SB.Lk
