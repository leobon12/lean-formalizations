/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XnTop

/-!
# (G3) for an arbitrary driven stage curve (PROVE-SB2-LIFTSET's v3 rule, D6)

Packet PROVE-T14-SB2LIFT (round 26). The core of the relative chain (`SB2XfChain`, `SB2XnTop`) uses only the
drivenness of the stage curve `ρ`, the identity `α = capTrace ρ` below the relative lifetime and generation; it does not
use that `ρ` is the v2 stage curve `stCurve`. Restated for an arbitrary driven `ρ` (so that it applies to LIFTSET's
v3 stage curves `cρ3`, `stCurvep`, including the shifted start piece):

* `liftCurve ρ L α s = α (capClock ρ (s / (L − s)))` (finite actual horizon `L`), `liftCurveTop ρ α s = α (capClock ρ
    s)`;
* **`capClock_liftCurve`**, **`relChainCore_gen`**, **`lifetime_eq_iSup_gen`** (finite horizon);
* **`capClock_liftCurveTop`**, **`relChainCore_genTop`**, **`lifetime_eq_iSup_genTop`** (infinite horizon).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk Sec7.PocketTraversal Sec7.Lemma71C

/-- The relative chart-coordinate lift of a piece of finite horizon `L` along a driven stage curve `ρ`. -/
def liftCurve (ρ : ℝ → ℂ) (L : ℝ≥0) (α : ℝ≥0 → ℂ) : ℝ≥0 → ℂ :=
  fun s => α (capClock ρ ((s : ℝ) / (L - s))).toNNReal

/-- The relative chart-coordinate lift of a piece of infinite horizon along a driven stage curve `ρ`. -/
def liftCurveTop (ρ : ℝ → ℂ) (α : ℝ≥0 → ℂ) : ℝ≥0 → ℂ := fun s => α (capClock ρ (s : ℝ)).toNNReal

variable {ρ : ℝ → ℂ} {e₁ e₂ : Drv} {α : ℝ≥0 → ℂ}

/-- **The capacity clock of the lift is `φ`**, and the lift traces the same sets as the stage curve. -/
theorem image_liftCurve (hρ : IsDrivenCurve ρ) (he₂ : e₂.2 = capLife ρ)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) {L₁ : ℝ≥0} {s : ℝ≥0} (hs : s < L₁) :
    liftCurve ρ L₁ α '' Icc 0 s =
      α '' Icc 0 (capClock (ρ) ((s : ℝ) / (L₁ - s))).toNNReal ∧
    α '' Icc 0 (capClock (ρ) ((s : ℝ) / (L₁ - s))).toNNReal =
      ρ '' Icc 0 ((s : ℝ) / (L₁ - s)) := by
  set φ : ℝ≥0 → ℝ := fun t => capClock ρ ((t : ℝ) / (L₁ - t)) with hφdef
  have hu0 : ∀ t : ℝ≥0, t < L₁ → 0 ≤ (t : ℝ) / (L₁ - t) := fun t ht =>
    div_nonneg t.2 (sub_nonneg.2 (NNReal.coe_le_coe.2 ht.le))
  have hmono : ∀ t : ℝ≥0, t ≤ s → φ t ≤ φ s := fun t ht => by
    have htL : t < L₁ := lt_of_le_of_lt ht hs
    have hq : (t : ℝ) / (L₁ - t) ≤ (s : ℝ) / (L₁ - s) :=
      div_le_div₀ s.2 (NNReal.coe_le_coe.2 ht) (sub_pos.2 (NNReal.coe_lt_coe.2 hs))
        (by have := NNReal.coe_le_coe.2 ht; linarith)
    exact hρ.strictMonoOn_capClock.monotoneOn (hu0 t htL) (hu0 s hs) hq
  have hφ0 : φ 0 = 0 := by
    simp only [hφdef, NNReal.coe_zero, zero_div]
    exact hρ.capClock_zero
  have hφs0 : 0 ≤ φ s := hρ.capClock_nonneg (hu0 s hs)
  have himg : (fun t => (φ t).toNNReal) '' Icc 0 s = Icc 0 (φ s).toNNReal := by
    ext τ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨zero_le, Real.toNNReal_le_toNNReal (hmono t ht.2)⟩
    · rintro ⟨-, hτ⟩
      have hτ' : (τ : ℝ) ∈ Icc (φ 0) (φ s) := by
        rw [hφ0]
        refine ⟨τ.2, ?_⟩
        have := NNReal.coe_le_coe.2 hτ
        rwa [Real.coe_toNNReal _ hφs0] at this
      have hcont : ContinuousOn φ (Icc 0 s) :=
        (continuousOn_capClock_div hρ L₁).mono fun t ht => lt_of_le_of_lt ht.2 hs
      obtain ⟨t, ht, hte⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ s) hcont hτ'
      exact ⟨t, ht, show (φ t).toNNReal = τ by rw [hte, Real.toNNReal_coe]⟩
  refine ⟨?_, ?_⟩
  · have e : liftCurve ρ L₁ α = fun t => α (φ t).toNNReal := by
      funext t
      simp only [liftCurve, hφdef]
    rw [e, ← image_image (g := α) (f := fun t => (φ t).toNNReal), himg]
  · have hlt : ∀ τ : ℝ≥0, τ ≤ (φ s).toNNReal → (τ : ℝ≥0∞) < e₂.2 := fun τ hτ => by
      rw [he₂]
      refine lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt (hu0 s hs))
      exact (ENNReal.coe_le_coe.2 hτ)
    rw [image_congr fun τ hτ => hαeq τ (hlt τ hτ.2)]
    change (fun τ : ℝ≥0 => ρ (capInv ρ τ)) '' _ = _
    rw [← image_image (g := ρ) (f := fun x : ℝ≥0 => capInv ρ x), image_capInv_Icc hρ (hu0 s hs)]

/-- **The capacity clock of the lift**: `capClock γ s = capClock ρ (s / (L − s))` before the actual lifetime. -/
theorem capClock_liftCurve (hρ : IsDrivenCurve ρ) (he₂ : e₂.2 = capLife ρ)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) {L₁ : ℝ≥0} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < L₁) :
    capClock (fun r : ℝ => liftCurve ρ L₁ α r.toNNReal) s =
      capClock (ρ) (s / (L₁ - s)) := by
  have hs' : s.toNNReal < L₁ := (Real.toNNReal_lt_iff_lt_coe hs0).2 hs
  obtain ⟨h1, h2⟩ := image_liftCurve hρ he₂ hαeq hs'
  unfold capClock
  rw [image_toNNReal_Icc _ hs0, h1, h2, Real.coe_toNNReal _ hs0]

/-- **(G3): the relative chain's core at a concrete stage, driven by `e₂`.** For every `S₀ < L` there are a driver
and a trace agreeing with `e₂`'s on `[0, capClock γ S₀]` for which every field of the relative chain other than the
two hull fields holds (`γ` the stage lift). -/
theorem relChainCore_gen (hρ : IsDrivenCurve ρ)
    (he₂ : e₂.2 = capLife ρ)
    (hgen : ∀ T < capLife ρ, IsGeneratingTrace e₂.1 T (capTrace ρ))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {L₁ : ℝ≥0}
    {S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀L : S₀ < L₁) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => liftCurve ρ L₁ α r.toNNReal) S₀ →
        Wr r = e₂.1 r.toNNReal ∧ ηr r = α r.toNNReal) ∧
      RelChainCore (liftCurve ρ L₁ α) S₀ Wr ηr := by
  have hL₁pos : (0 : ℝ) < L₁ := lt_of_le_of_lt hS₀ hS₀L
  have hu0 : ∀ s : ℝ, 0 ≤ s → s < L₁ → 0 ≤ s / (L₁ - s) := fun s hs0 hs =>
    div_nonneg hs0 (sub_nonneg.2 hs.le)
  have hcap : ∀ s ∈ Icc (0 : ℝ) S₀,
      capClock (fun r : ℝ => liftCurve ρ L₁ α r.toNNReal) s = capClock ρ (s / (L₁ - s)) := fun s hs =>
    capClock_liftCurve hρ he₂ hαeq hs.1 (lt_of_le_of_lt hs.2 hS₀L)
  have hqmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < L₁ → a / (L₁ - a) ≤ b / (L₁ - b) := fun a b ha hab hb =>
    div_le_div₀ (ha.trans hab) hab (sub_pos.2 hb) (by linarith)
  set T' := capClock ρ (S₀ / (L₁ - S₀)) with hT'def
  have hT'0 : 0 ≤ T' := hρ.capClock_nonneg (hu0 S₀ hS₀ hS₀L)
  have hT'L : ENNReal.ofReal T' < e₂.2 := by rw [he₂]; exact hρ.ofReal_capClock_lt (hu0 S₀ hS₀ hS₀L)
  obtain ⟨L₂, hL₂⟩ : ∃ L₂ : ℝ≥0, e₂.2 = L₂ := ⟨e₂.2.toNNReal, (ENNReal.coe_toNNReal hfin).symm⟩
  have hT'L₂ : T' < L₂ := by
    rw [hL₂] at hT'L
    have := (ENNReal.ofReal_lt_iff_lt_toReal hT'0 ENNReal.coe_ne_top).1 hT'L
    simpa using this
  set t₂ := (T' + L₂) / 2 with ht₂def
  have hT't₂ : T' < t₂ := by rw [ht₂def]; linarith
  have ht₂L : t₂ < L₂ := by rw [ht₂def]; linarith
  have ht₂0 : 0 ≤ t₂ := hT'0.trans hT't₂.le
  have hlt₂ : ENNReal.ofReal t₂ < e₂.2 := by
    rw [hL₂]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht₂0 ENNReal.coe_ne_top).2 (by simpa using ht₂L)
  -- the relative trace generates `e₂` up to its lifetime
  have hαg : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T'', htT'', hT''⟩ := exists_between ht
    have h := (hgen T'' (by rw [← he₂]; exact hT'')).2.2 t htT''
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  have hWlt : ContinuousOn e₂.1 {s | (s : ℝ≥0∞) < e₂.2} :=
    hW.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hLT := hαg.isLoewnerTraceLT hlt₂
  have hWc : Continuous (frozenDrive e₂.1 t₂) := continuous_frozenDrive_of_lt hWlt hlt₂
  have hW0' : frozenDrive e₂.1 t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0]; exact hW0
  refine ⟨YuanCorollary13.extDrive (frozenDrive e₂.1 t₂) T',
    YuanCorollary13.extTrace (frozenDrive e₂.1 t₂) (fun s : ℝ => α s.toNNReal) T', fun r hr0 hr => ?_, ?_⟩
  · rw [hcap S₀ ⟨hS₀, le_rfl⟩] at hr
    refine ⟨?_, YuanCorollary13.extTrace_eq hr⟩
    rw [YuanCorollary13.extDrive_eq hr, frozenDrive_eq ⟨hr0, hr.trans hT't₂.le⟩]
  refine ⟨YuanCorollary13.continuous_extDrive hWc, YuanCorollary13.extDrive_zero hW0' hT'0,
    hLT.isLoewnerTrace_ext hWc hW0' hT'0 hT't₂, ?_, fun a ha b hb hab => ?_, ?_, fun s hs => ?_⟩
  · rw [hcap 0 ⟨le_rfl, hS₀⟩, zero_div]
    exact hρ.capClock_zero
  · rw [hcap a ha, hcap b hb]
    refine hρ.strictMonoOn_capClock (hu0 a ha.1 (lt_of_le_of_lt ha.2 hS₀L)) (hu0 b hb.1 (lt_of_le_of_lt hb.2 hS₀L)) ?_
    have hb' : b < L₁ := lt_of_le_of_lt hb.2 hS₀L
    rw [div_lt_div_iff₀ (sub_pos.2 (lt_of_le_of_lt (le_of_lt hab) hb')) (sub_pos.2 hb')]
    nlinarith
  · have hq : ContinuousOn (fun s : ℝ => s / (L₁ - s)) (Icc 0 S₀) := fun s hs =>
      (continuousAt_id.div (continuousAt_const.sub continuousAt_id)
        (sub_pos.2 (lt_of_le_of_lt hs.2 hS₀L)).ne').continuousWithinAt
    refine ((hρ.continuousOn_capClock).comp hq fun s hs => hu0 s hs.1 (lt_of_le_of_lt hs.2 hS₀L)).congr
      fun s hs => hcap s hs
  · have hsL : s < L₁ := lt_of_le_of_lt hs.2 hS₀L
    have hτ0 : 0 ≤ capClock ρ (s / (L₁ - s)) := hρ.capClock_nonneg (hu0 s hs.1 hsL)
    have hτT : capClock ρ (s / (L₁ - s)) ≤ T' :=
      hρ.strictMonoOn_capClock.monotoneOn (hu0 s hs.1 hsL) (hu0 S₀ hS₀ hS₀L) (hqmono s S₀ hs.1 hs.2 hS₀L)
    rw [hcap s hs]
    have hs' : s.toNNReal < L₁ := (Real.toNNReal_lt_iff_lt_coe hs.1).2 hsL
    have hγs : liftCurve ρ L₁ α s.toNNReal = α (capClock ρ (s / (L₁ - s))).toNNReal := by
      simp only [liftCurve, Real.coe_toNNReal _ hs.1]
    refine ⟨hτ0, ?_, ?_⟩
    · rw [YuanCorollary13.extTrace_eq hτT, hγs]
    · rw [hLT.fwdHull_extDrive_of_le hWc hT't₂ hτ0 hτT,
        image_congr fun r hr => YuanCorollary13.extTrace_eq (hr.2.trans hτT), image_toNNReal_Icc α hτ0,
        (image_liftCurve hρ he₂ hαeq hs').1, Real.coe_toNNReal _ hs.1]

/-- **The lifetime clause**: the relative lifetime is the supremum of the lift's capacity clock before the actual
lifetime. -/
theorem lifetime_eq_iSup_gen (hρ : IsDrivenCurve ρ)
    (he₂ : e₂.2 = capLife ρ)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) {L₁ : ℝ≥0} (hpos : 0 < L₁) :
    e₂.2 = ⨆ (S₀ : ℝ≥0) (_ : S₀ < L₁),
      ENNReal.ofReal (capClock (fun r : ℝ => liftCurve ρ L₁ α r.toNNReal) (S₀ : ℝ)) := by
  have hcap : ∀ S₀ : ℝ≥0, S₀ < L₁ →
      capClock (fun r : ℝ => liftCurve ρ L₁ α r.toNNReal) (S₀ : ℝ) =
        capClock (ρ) ((S₀ : ℝ) / (L₁ - S₀)) := fun S₀ h =>
    capClock_liftCurve hρ he₂ hαeq S₀.2 (NNReal.coe_lt_coe.2 h)
  have hlt : ∀ S₀ : ℝ≥0, S₀ < L₁ ↔ S₀ < L₁ := fun S₀ => Iff.rfl
  rw [he₂]
  refine le_antisymm (iSup_le fun n => ?_) (iSup₂_le fun S₀ hS₀ => ?_)
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc0 := clockOf_nonneg (NNReal.coe_pos.2 hpos) hn
    have hcl := clockOf_lt (NNReal.coe_pos.2 hpos) hn
    have hS : (clockOf L₁ n).toNNReal < L₁ := (Real.toNNReal_lt_iff_lt_coe hc0).2 hcl
    refine le_iSup₂_of_le (clockOf L₁ n).toNNReal ((hlt _).2 hS) (le_of_eq ?_)
    rw [hcap _ hS, Real.coe_toNNReal _ hc0, div_sub_clockOf (NNReal.coe_pos.2 hpos) hn]
  · rw [hcap S₀ ((hlt S₀).1 hS₀)]
    exact (hρ.ofReal_capClock_lt (div_nonneg S₀.2 (sub_nonneg.2 (NNReal.coe_le_coe.2 ((hlt S₀).1 hS₀).le)))).le

/-- **The lift traces the same sets as the stage curve.** -/
theorem image_liftCurveTop (hρ : IsDrivenCurve ρ) (he₂ : e₂.2 = capLife ρ)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) (s : ℝ≥0) :
    liftCurveTop ρ α '' Icc 0 s = α '' Icc 0 (capClock (ρ) (s : ℝ)).toNNReal ∧
    α '' Icc 0 (capClock (ρ) (s : ℝ)).toNNReal = ρ '' Icc 0 (s : ℝ) := by
  set φ : ℝ≥0 → ℝ := fun t => capClock ρ (t : ℝ) with hφdef
  have hmono : ∀ t : ℝ≥0, t ≤ s → φ t ≤ φ s := fun t ht =>
    hρ.strictMonoOn_capClock.monotoneOn t.2 s.2 (NNReal.coe_le_coe.2 ht)
  have hφ0 : φ 0 = 0 := by simp only [hφdef, NNReal.coe_zero]; exact hρ.capClock_zero
  have hφs0 : 0 ≤ φ s := hρ.capClock_nonneg s.2
  have himg : (fun t => (φ t).toNNReal) '' Icc 0 s = Icc 0 (φ s).toNNReal := by
    ext τ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨zero_le, Real.toNNReal_le_toNNReal (hmono t ht.2)⟩
    · rintro ⟨-, hτ⟩
      have hτ' : (τ : ℝ) ∈ Icc (φ 0) (φ s) := by
        rw [hφ0]
        refine ⟨τ.2, ?_⟩
        have := NNReal.coe_le_coe.2 hτ
        rwa [Real.coe_toNNReal _ hφs0] at this
      have hcont : ContinuousOn φ (Icc 0 s) :=
        (hρ.continuousOn_capClock.comp NNReal.continuous_coe.continuousOn fun t _ => t.2).mono
          (subset_univ _)
      obtain ⟨t, ht, hte⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ s) hcont hτ'
      exact ⟨t, ht, show (φ t).toNNReal = τ by rw [hte, Real.toNNReal_coe]⟩
  refine ⟨?_, ?_⟩
  · have e : liftCurveTop ρ α = fun t => α (φ t).toNNReal := rfl
    rw [e, ← image_image (g := α) (f := fun t => (φ t).toNNReal), himg]
  · show α '' Icc 0 (capClock ρ (s : ℝ)).toNNReal = ρ '' Icc 0 (s : ℝ)
    have hlt : ∀ τ : ℝ≥0, τ ≤ (capClock ρ (s : ℝ)).toNNReal → (τ : ℝ≥0∞) < e₂.2 := fun τ hτ => by
      rw [he₂]
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hτ) (hρ.ofReal_capClock_lt s.2)
    rw [image_congr fun τ hτ => hαeq τ (hlt τ hτ.2)]
    change (fun τ : ℝ≥0 => ρ (capInv ρ τ)) '' _ = _
    rw [← image_image (g := ρ) (f := fun x : ℝ≥0 => capInv ρ x), image_capInv_Icc hρ (NNReal.coe_nonneg s)]

/-- **The capacity clock of the lift is that of the stage curve.** -/
theorem capClock_liftCurveTop (hρ : IsDrivenCurve ρ)
    (he₂ : e₂.2 = capLife ρ)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) {s : ℝ} (hs0 : 0 ≤ s) :
    capClock (fun r : ℝ => liftCurveTop ρ α r.toNNReal) s = capClock (ρ) s := by
  obtain ⟨h1, h2⟩ := image_liftCurveTop hρ he₂ hαeq s.toNNReal
  unfold capClock
  rw [image_toNNReal_Icc _ hs0, h1, h2, Real.coe_toNNReal _ hs0]

/-- **(G3) at an infinite actual piece**: for every `S₀`, the relative chain's core for `e₂`'s driver frozen at a time
in `(capClock γ S₀, e₂.2)` (finite or infinite relative lifetime), agreeing with `e₂`'s driver and `α` on
`[0, capClock γ S₀]`. -/
theorem relChainCore_genTop (hρ : IsDrivenCurve ρ)
    (he₂ : e₂.2 = capLife ρ)
    (hgen : ∀ T < capLife ρ, IsGeneratingTrace e₂.1 T (capTrace ρ))
    (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {S₀ : ℝ} (hS₀ : 0 ≤ S₀) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => liftCurveTop ρ α r.toNNReal) S₀ →
        Wr r = e₂.1 r.toNNReal ∧ ηr r = α r.toNNReal) ∧
      RelChainCore (liftCurveTop ρ α) S₀ Wr ηr := by
  have hcap : ∀ s ∈ Icc (0 : ℝ) S₀,
      capClock (fun r : ℝ => liftCurveTop ρ α r.toNNReal) s = capClock ρ s := fun s hs =>
    capClock_liftCurveTop hρ he₂ hαeq hs.1
  set T' := capClock ρ S₀ with hT'def
  have hT'0 : 0 ≤ T' := hρ.capClock_nonneg hS₀
  have hT'L : ENNReal.ofReal T' < e₂.2 := by rw [he₂]; exact hρ.ofReal_capClock_lt hS₀
  obtain ⟨q, hq1, hq2⟩ := exists_between hT'L
  have hqt : q ≠ ⊤ := ne_top_of_lt hq2
  set t₂ := q.toReal with ht₂def
  have hT't₂ : T' < t₂ := (ENNReal.ofReal_lt_iff_lt_toReal hT'0 hqt).1 hq1
  have ht₂0 : 0 ≤ t₂ := hT'0.trans hT't₂.le
  have hlt₂ : ENNReal.ofReal t₂ < e₂.2 := by rw [ht₂def, ENNReal.ofReal_toReal hqt]; exact hq2
  have hαg : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T'', htT'', hT''⟩ := exists_between ht
    have h := (hgen T'' (by rw [← he₂]; exact hT'')).2.2 t htT''
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  have hWlt : ContinuousOn e₂.1 {s | (s : ℝ≥0∞) < e₂.2} :=
    hW.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hLT := hαg.isLoewnerTraceLT hlt₂
  have hWc : Continuous (frozenDrive e₂.1 t₂) := continuous_frozenDrive_of_lt hWlt hlt₂
  have hW0' : frozenDrive e₂.1 t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0]; exact hW0
  refine ⟨YuanCorollary13.extDrive (frozenDrive e₂.1 t₂) T',
    YuanCorollary13.extTrace (frozenDrive e₂.1 t₂) (fun s : ℝ => α s.toNNReal) T', fun r hr0 hr => ?_, ?_⟩
  · rw [hcap S₀ ⟨hS₀, le_rfl⟩] at hr
    refine ⟨?_, YuanCorollary13.extTrace_eq hr⟩
    rw [YuanCorollary13.extDrive_eq hr, frozenDrive_eq ⟨hr0, hr.trans hT't₂.le⟩]
  refine ⟨YuanCorollary13.continuous_extDrive hWc, YuanCorollary13.extDrive_zero hW0' hT'0,
    hLT.isLoewnerTrace_ext hWc hW0' hT'0 hT't₂, ?_, fun a ha b hb hab => ?_, ?_, fun s hs => ?_⟩
  · rw [hcap 0 ⟨le_rfl, hS₀⟩]
    exact hρ.capClock_zero
  · rw [hcap a ha, hcap b hb]
    exact hρ.strictMonoOn_capClock ha.1 hb.1 hab
  · exact (hρ.continuousOn_capClock.mono fun s hs => hs.1).congr fun s hs => hcap s hs
  · have hτ0 : 0 ≤ capClock ρ s := hρ.capClock_nonneg hs.1
    have hτT : capClock ρ s ≤ T' := hρ.strictMonoOn_capClock.monotoneOn hs.1 hS₀ hs.2
    rw [hcap s hs]
    have hγs : liftCurveTop ρ α s.toNNReal = α (capClock ρ s).toNNReal := by
      simp only [liftCurveTop, Real.coe_toNNReal _ hs.1]
    refine ⟨hτ0, ?_, ?_⟩
    · rw [YuanCorollary13.extTrace_eq hτT, hγs]
    · rw [hLT.fwdHull_extDrive_of_le hWc hT't₂ hτ0 hτT,
        image_congr fun r hr => YuanCorollary13.extTrace_eq (hr.2.trans hτT), image_toNNReal_Icc α hτ0,
        (image_liftCurveTop hρ he₂ hαeq s.toNNReal).1, Real.coe_toNNReal _ hs.1]

/-- **The lifetime clause at an infinite actual piece.** -/
theorem lifetime_eq_iSup_genTop (hρ : IsDrivenCurve ρ)
    (he₂ : e₂.2 = capLife ρ)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) :
    e₂.2 = ⨆ (S₀ : ℝ≥0),
      ENNReal.ofReal (capClock (fun r : ℝ => liftCurveTop ρ α r.toNNReal) (S₀ : ℝ)) := by
  rw [he₂]
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun S₀ => ?_)
  · refine le_iSup_of_le (n : ℝ≥0) (le_of_eq ?_)
    rw [capClock_liftCurveTop hρ he₂ hαeq (NNReal.coe_nonneg _), NNReal.coe_natCast]
  · rw [capClock_liftCurveTop hρ he₂ hαeq (NNReal.coe_nonneg _)]
    exact (hρ.ofReal_capClock_lt (NNReal.coe_nonneg _)).le

end InteractingSLE.Theorem14.SB.Mn
