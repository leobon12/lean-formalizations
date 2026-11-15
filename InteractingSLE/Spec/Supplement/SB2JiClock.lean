/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LjLift

/-!
# SB2(2): the capacity bookkeeping of a driven concrete stage curve

Packet PROVE-SB2-LIFTSET (round 13). `liftRel_concrete` (`SB2LjLift`) takes two facts about the relative good times
`cGd` (read through the inverse clock `capInv`): their density in `[0, e₂.2]` (`hdense₂`) and the cover of the lifted
good points (`hcov`). When the stage curve is driven (`IsDrivenCurve`, as on the concrete rule's driven events), both
follow from facts about the **actual** piece alone:

* `clockOf_div_sub`, `div_sub_clockOf` (`clockOf L` and `t ↦ t / (L - t)` are inverse on `[0, ∞)`, `[0, L)`),
  `coe_lt_iff_toReal`;
* `cTm_capClock`, `capClock_mem_cGd`, `lift_mem_of_lt` (every good actual time before the lifetime is the actual time of
  a relative good time);
* **`hcov_of_driven`**: the cover, given that the lifted endpoint (when good) is a limit of lifted good points before
  it;
* `le_subset_closure_of_lt`, **`hdense_of_driven`**: the density, given the density of the good actual times in
  `[0, L)`;
* infinite lifetime: `cTmTop`, `cGdTop` (actual time `capInv ρ τ`), **`hcov_top`** (no hypothesis: every good point is
  a value), **`hdense_top`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-! ### The reparametrization -/

/-- `clockOf L` hits every time of `[0, L)`, at `t / (L - t)`. -/
theorem clockOf_div_sub {L t : ℝ} (ht : t ∈ Ico 0 L) : clockOf L (t / (L - t)) = t := by
  have hLv : 0 < L - t := by linarith [ht.2]
  have hL0 : L ≠ 0 := (show (0 : ℝ) < L by linarith [ht.1, ht.2]).ne'
  simp only [clockOf]
  have h1 : 1 + t / (L - t) = L / (L - t) := by field_simp; ring
  rw [h1]
  field_simp

/-- `t ↦ t / (L - t)` inverts `clockOf L` on `[0, ∞)`. -/
theorem div_sub_clockOf {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u) : clockOf L u / (L - clockOf L u) = u := by
  simp only [clockOf]
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : L - L * (u / (1 + u)) = L / (1 + u) := by field_simp; ring
  rw [h2]
  field_simp

theorem coe_lt_iff_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) {t : ℝ≥0} : (t : ℝ≥0∞) < x ↔ (t : ℝ) < x.toReal := by
  conv_lhs => rw [← ENNReal.coe_toNNReal hx]
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, ENNReal.coe_toNNReal_eq_toReal]

/-- A closure statement on `[0, T]` from one on `[0, T)` (`T > 0`). -/
theorem le_subset_closure_of_lt {T : ℝ≥0∞} {A : Set ℝ≥0} (hT : 0 < T)
    (h : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < T → τ ∈ closure A) : {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ T} ⊆ closure A := by
  intro τ hτ
  rcases lt_or_eq_of_le (show (τ : ℝ≥0∞) ≤ T from hτ) with hlt | heq
  · exact h τ hlt
  · have hτ0 : 0 < τ := by rw [← ENNReal.coe_pos, heq]; exact hT
    have hI : τ ∈ closure (Iio τ) := by rw [closure_Iio' (a := τ) ⟨0, hτ0⟩]; exact mem_Iic.2 le_rfl
    refine closure_minimal (fun τ' hτ' => h τ' ?_) isClosed_closure hI
    rw [← heq]
    exact ENNReal.coe_lt_coe.2 hτ'

variable {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₂ : Drv}

/-! ### Finite actual lifetime -/

theorem cTm_capClock (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) {u : ℝ} (hu : 0 ≤ u) :
    cTm c m s₁ e₁ s₂ (capClock (stCurve c m s₁ e₁ s₂) u).toNNReal = (clockOf e₁.2.toReal u).toNNReal := by
  unfold cTm
  rw [Real.coe_toNNReal _ (hρ.capClock_nonneg hu), hρ.capInv_eq hu]

theorem capClock_mem_cGd (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂)) {u : ℝ} (hu : 0 ≤ u)
    (hg : (clockOf e₁.2.toReal u).toNNReal ∈ goodT c s₁ e₁) :
    (capClock (stCurve c m s₁ e₁ s₂) u).toNNReal ∈ cGd c m s₁ e₁ s₂ e₂ := by
  refine ⟨?_, by rw [cTm_capClock hρ hu]; exact hg⟩
  rw [he₂]
  exact hρ.ofReal_capClock_lt hu

/-- Every good actual time before the lifetime is the actual time of a relative good time. -/
theorem lift_mem_of_lt (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂)) (he₁ : e₁.2 ≠ ⊤) {t : ℝ≥0} (ht : t ∈ goodT c s₁ e₁)
    (hlt : (t : ℝ≥0∞) < e₁.2) :
    liftPt c m (pcPt s₁ e₁ t) ∈
      (fun τ => liftPt c m (pcPt s₁ e₁ (cTm c m s₁ e₁ s₂ τ))) '' cGd c m s₁ e₁ s₂ e₂ := by
  have hlt' : (t : ℝ) < e₁.2.toReal := (coe_lt_iff_toReal he₁).1 hlt
  have hmem : (t : ℝ) ∈ Ico 0 e₁.2.toReal := ⟨NNReal.coe_nonneg t, hlt'⟩
  have hu : 0 ≤ (t : ℝ) / (e₁.2.toReal - t) := div_nonneg (NNReal.coe_nonneg t) (by linarith)
  have hc : (clockOf e₁.2.toReal ((t : ℝ) / (e₁.2.toReal - t))).toNNReal = t := by
    rw [clockOf_div_sub hmem, Real.toNNReal_coe]
  refine ⟨_, capClock_mem_cGd hρ he₂ hu (by rw [hc]; exact ht), ?_⟩
  simp only [cTm_capClock hρ hu, hc]

/-- **The cover of the lifted good points** for a driven stage curve: every lifted good point before the lifetime is
a value at a relative good time; the lifted endpoint (when good) is assumed a limit of lifted good points before it. -/
theorem hcov_of_driven (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂)) (he₁ : e₁.2 ≠ ⊤)
    (hend : ∀ t ∈ goodT c s₁ e₁, (t : ℝ≥0∞) = e₁.2 → liftPt c m (pcPt s₁ e₁ t) ∈
      closure ((fun t' => liftPt c m (pcPt s₁ e₁ t')) '' (goodT c s₁ e₁ ∩ {t' | (t' : ℝ≥0∞) < e₁.2}))) :
    liftPt c m '' (pcPt s₁ e₁ '' goodT c s₁ e₁) ⊆
      closure ((fun τ => liftPt c m (pcPt s₁ e₁ (cTm c m s₁ e₁ s₂ τ))) '' cGd c m s₁ e₁ s₂ e₂) := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  rcases lt_or_eq_of_le ht.1 with hlt | heq
  · exact subset_closure (lift_mem_of_lt hρ he₂ he₁ ht hlt)
  · refine closure_minimal ?_ isClosed_closure (hend t ht heq)
    rintro _ ⟨t', ⟨ht', hlt'⟩, rfl⟩
    exact subset_closure (lift_mem_of_lt hρ he₂ he₁ ht' hlt')

/-- **The density of the relative good times** for a driven stage curve, from the density of the good actual times
in `[0, L)` (the map `t ↦ capClock ρ (t / (L - t))` is continuous on `[0, L)` and sends good times to relative good
times). -/
theorem hdense_of_driven (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂)) (he₁ : e₁.2 ≠ ⊤) (hpos : e₁.2 ≠ 0)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) :
    {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} ⊆ closure (cGd c m s₁ e₁ s₂ e₂) := by
  have hL0 : 0 < e₁.2.toReal := ENNReal.toReal_pos hpos he₁
  have hSo : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hφG : (fun t : ℝ≥0 => (capClock (stCurve c m s₁ e₁ s₂) ((t : ℝ) / (e₁.2.toReal - t))).toNNReal) ''
      (goodT c s₁ e₁ ∩ {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2}) ⊆ cGd c m s₁ e₁ s₂ e₂ := by
    rintro _ ⟨t, ⟨ht, hlt⟩, rfl⟩
    have hlt' : (t : ℝ) < e₁.2.toReal := (coe_lt_iff_toReal he₁).1 hlt
    have hu : 0 ≤ (t : ℝ) / (e₁.2.toReal - t) := div_nonneg (NNReal.coe_nonneg t) (by linarith)
    refine capClock_mem_cGd hρ he₂ hu ?_
    rw [clockOf_div_sub ⟨NNReal.coe_nonneg t, hlt'⟩, Real.toNNReal_coe]
    exact ht
  have hφc : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2}, ContinuousWithinAt
      (fun t : ℝ≥0 => (capClock (stCurve c m s₁ e₁ s₂) ((t : ℝ) / (e₁.2.toReal - t))).toNNReal)
      {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} t := by
    intro t ht
    have hlt' : (t : ℝ) < e₁.2.toReal := (coe_lt_iff_toReal he₁).1 ht
    have hg : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ) / (e₁.2.toReal - t)) {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} t :=
      (NNReal.continuous_coe.continuousAt.div (continuous_const.sub NNReal.continuous_coe).continuousAt
        (sub_pos.2 hlt').ne').continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ≥0 => (t : ℝ) / (e₁.2.toReal - t)) {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} (Ici 0) :=
      fun t' ht' => div_nonneg (NNReal.coe_nonneg t') (by linarith [(coe_lt_iff_toReal he₁).1 ht'])
    have hcap := ContinuousWithinAt.comp (f := fun t : ℝ≥0 => (t : ℝ) / (e₁.2.toReal - t))
      (g := capClock (stCurve c m s₁ e₁ s₂)) (hρ.continuousOn_capClock _ (hmaps ht)) hg hmaps
    exact continuous_real_toNNReal.continuousAt.comp_continuousWithinAt hcap
  have hpos₂ : 0 < e₂.2 := by
    rw [he₂]
    simpa [hρ.capClock_zero] using hρ.ofReal_capClock_lt (le_refl (0 : ℝ))
  refine le_subset_closure_of_lt hpos₂ fun τ hτ => ?_
  rw [he₂] at hτ
  have hs : ENNReal.ofReal (τ : ℝ) < capLife (stCurve c m s₁ e₁ s₂) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hu, hcu⟩ := hρ.capInv_spec (NNReal.coe_nonneg τ) hs
  have ht₀ : ((clockOf e₁.2.toReal (capInv (stCurve c m s₁ e₁ s₂) τ)).toNNReal : ℝ) =
      clockOf e₁.2.toReal (capInv (stCurve c m s₁ e₁ s₂) τ) := Real.coe_toNNReal _ (clockOf_nonneg hL0 hu)
  have ht₀S : (clockOf e₁.2.toReal (capInv (stCurve c m s₁ e₁ s₂) τ)).toNNReal ∈
      {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} := by
    rw [mem_ofPred_eq, coe_lt_iff_toReal he₁, ht₀]
    exact clockOf_lt hL0 hu
  have hφt₀ : (capClock (stCurve c m s₁ e₁ s₂)
      (((clockOf e₁.2.toReal (capInv (stCurve c m s₁ e₁ s₂) τ)).toNNReal : ℝ) /
        (e₁.2.toReal - (clockOf e₁.2.toReal (capInv (stCurve c m s₁ e₁ s₂) τ)).toNNReal))).toNNReal = τ := by
    rw [ht₀, div_sub_clockOf hL0 hu, hcu, Real.toNNReal_coe]
  have hcl : (clockOf e₁.2.toReal (capInv (stCurve c m s₁ e₁ s₂) τ)).toNNReal ∈
      closure (goodT c s₁ e₁ ∩ {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2}) := by
    have h := hSo.inter_closure ⟨ht₀S, hgd ht₀S⟩
    rwa [inter_comm] at h
  have h1 := ((hφc _ ht₀S).mono inter_subset_right).mem_closure_image hcl
  rw [hφt₀] at h1
  exact closure_minimal (hφG.trans subset_closure) isClosed_closure h1

/-! ### Infinite actual lifetime -/

/-- The actual time `capInv ρ τ` of relative capacity time `τ` (infinite actual lifetime). -/
def cTmTop (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (τ : ℝ≥0) : ℝ≥0 :=
  (capInv (stCurve c m s₁ e₁ s₂) τ).toNNReal

/-- The relative good times (infinite actual lifetime). -/
def cGdTop (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (e₂ : Drv) : Set ℝ≥0 :=
  {τ | (τ : ℝ≥0∞) < e₂.2 ∧ cTmTop c m s₁ e₁ s₂ τ ∈ goodT c s₁ e₁}

theorem cTmTop_capClock (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (t : ℝ≥0) :
    cTmTop c m s₁ e₁ s₂ (capClock (stCurve c m s₁ e₁ s₂) t).toNNReal = t := by
  unfold cTmTop
  rw [Real.coe_toNNReal _ (hρ.capClock_nonneg (NNReal.coe_nonneg t)), hρ.capInv_eq (NNReal.coe_nonneg t),
    Real.toNNReal_coe]

theorem capClock_mem_cGdTop (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂)) {t : ℝ≥0} (hg : t ∈ goodT c s₁ e₁) :
    (capClock (stCurve c m s₁ e₁ s₂) t).toNNReal ∈ cGdTop c m s₁ e₁ s₂ e₂ :=
  ⟨by rw [he₂]; exact hρ.ofReal_capClock_lt (NNReal.coe_nonneg t), by rw [cTmTop_capClock hρ]; exact hg⟩

/-- **The cover at infinite actual lifetime**: every lifted good point is a value at a relative good time. -/
theorem hcov_top (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂)) :
    liftPt c m '' (pcPt s₁ e₁ '' goodT c s₁ e₁) ⊆
      closure ((fun τ => liftPt c m (pcPt s₁ e₁ (cTmTop c m s₁ e₁ s₂ τ))) '' cGdTop c m s₁ e₁ s₂ e₂) := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  refine subset_closure ⟨_, capClock_mem_cGdTop hρ he₂ ht, ?_⟩
  simp only [cTmTop_capClock hρ]

/-- **The density at infinite actual lifetime**, from the density of the good actual times. -/
theorem hdense_top (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (he₁ : e₁.2 = ⊤) (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) :
    {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} ⊆ closure (cGdTop c m s₁ e₁ s₂ e₂) := by
  have hφc : ∀ t : ℝ≥0, ContinuousAt (fun t : ℝ≥0 => (capClock (stCurve c m s₁ e₁ s₂) t).toNNReal) t := by
    intro t
    have hcap : ContinuousAt (fun t : ℝ≥0 => capClock (stCurve c m s₁ e₁ s₂) t) t := by
      have h1 := (hρ.continuousOn_capClock (t : ℝ) (mem_Ici.2 (NNReal.coe_nonneg t))).comp
        NNReal.continuous_coe.continuousWithinAt (s := univ) (fun t' _ => mem_Ici.2 (NNReal.coe_nonneg t'))
      exact continuousWithinAt_univ _ _ |>.1 h1
    exact continuous_real_toNNReal.continuousAt.comp hcap
  have hpos₂ : 0 < e₂.2 := by
    rw [he₂]
    simpa [hρ.capClock_zero] using hρ.ofReal_capClock_lt (le_refl (0 : ℝ))
  refine le_subset_closure_of_lt hpos₂ fun τ hτ => ?_
  rw [he₂] at hτ
  have hs : ENNReal.ofReal (τ : ℝ) < capLife (stCurve c m s₁ e₁ s₂) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hu, hcu⟩ := hρ.capInv_spec (NNReal.coe_nonneg τ) hs
  have ht₀ : ((capInv (stCurve c m s₁ e₁ s₂) τ).toNNReal : ℝ) = capInv (stCurve c m s₁ e₁ s₂) τ :=
    Real.coe_toNNReal _ hu
  have hcl : (capInv (stCurve c m s₁ e₁ s₂) τ).toNNReal ∈ closure (goodT c s₁ e₁) :=
    hgd (by rw [mem_ofPred_eq, he₁]; exact ENNReal.coe_lt_top)
  have h1 := (hφc _).continuousWithinAt.mem_closure_image hcl
  rw [ht₀, hcu, Real.toNNReal_coe] at h1
  refine closure_minimal ?_ isClosed_closure h1
  rintro _ ⟨t, ht, rfl⟩
  exact subset_closure (capClock_mem_cGdTop hρ he₂ ht)

end InteractingSLE.Theorem14.SB.Lk
