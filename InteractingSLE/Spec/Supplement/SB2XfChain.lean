/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XbTime
import InteractingSLE.Spec.Supplement.SB2XcIface
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# (G3) for the corrected per-stage correspondence: `EL`'s stage driver and trace drive the relative chain

Packet PROVE-T14-SB2LIFT (round 25; item (G3) of §R24.2, decision D11 option (A)). At a relative stage of PROVE-SB2-
LIFTSET's concrete rule (the relative driver `e₂` generates the capacity reparametrization of the driven stage curve
`ρ = stCurve`, `e₂.2 = capLife ρ`), the relative chart-coordinate lift of B's finite piece is
`stageLift … s = α (φ s)` with `φ s = capClock ρ (s / (L − s))` (round 23's capacity time). Then:

* **`capClock_stageLift`**: its capacity clock is `φ` (both curves trace the same sets: `γ([0, s]) = ρ([0, s/(L−s)])`);
* **`relChainCore_concrete`**: for every `S₀ < L`, all fields of `FinRel.IsSB2RelChain` except the two hull fields
  (`RelChainCore`) hold for a driver and trace that **agree with `e₂`'s driver and trace on `[0, capClock γ S₀]`**:
  `e₂`'s driver frozen at a time `t₂ ∈ (capClock γ S₀, e₂.2)` is a Loewner driver before `t₂`
  (`IsGeneratingTrace.isLoewnerTraceLT`), and Yuan's slit extension past `capClock γ S₀`
  (`IsLoewnerTraceLT.isLoewnerTrace_ext`) is a continuous Loewner trace on `[0, ∞)`;
* **`lifetime_eq_iSup_capClock`**: `e₂.2 = ⨆_{S₀ < L} capClock γ S₀` (the lifetime clause);
* **`isSB2RelChain_of_core`**: the core with the hull-in and frontier fields (PROVE-GW2-GEOM2's builder) is the chain.

The trace agreement is on `[0, capClock γ S₀]`, not below the whole relative lifetime: the library extends a trace
only from a time strictly before its horizon, and the chain is used only up to `S₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk Sec7.PocketTraversal Sec7.Lemma71C

/-- **The chain fields of `FinRel.IsSB2RelChain` other than the two hull fields.** -/
def RelChainCore (γ : ℝ≥0 → ℂ) (S₀ : ℝ) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) : Prop :=
  Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
    capClock (fun r : ℝ => γ r.toNNReal) 0 = 0 ∧
    StrictMonoOn (capClock (fun r : ℝ => γ r.toNNReal)) (Icc 0 S₀) ∧
    ContinuousOn (capClock (fun r : ℝ => γ r.toNNReal)) (Icc 0 S₀) ∧
    ∀ s ∈ Icc 0 S₀, 0 ≤ capClock (fun r : ℝ => γ r.toNNReal) s ∧
      ηr (capClock (fun r : ℝ => γ r.toNNReal) s) = γ s.toNNReal ∧
      fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) = fillH (γ '' Icc 0 s.toNNReal)

/-- **The core with the two hull fields is the relative chain.** -/
theorem isSB2RelChain_of_core {A : Set ℂ} {c : Chart} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ}
    {ηr : ℝ → ℂ} (hcore : RelChainCore γ S₀ Wr ηr)
    (hin : ∀ s ∈ Icc 0 S₀, ∀ z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal)), z ∉ fillH A →
      c.1 z ∈ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
    (hfr : ∀ s ∈ Icc 0 S₀, ∀ z ∈ H \ fillH A, c.1 z ∈ frontier (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) →
      z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal))) :
    FinRel.IsSB2RelChain A c β' γ tL S₀ Wr ηr := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcore
  exact ⟨h1, h2, h3, h4, h5, h6, fun s hs => ⟨(h7 s hs).1, (h7 s hs).2.1, (h7 s hs).2.2, hin s hs, hfr s hs⟩⟩

/-- **The relative chart-coordinate lift of B's piece** at a concrete relative stage: the relative trace `α` at the
capacity time `φ s = capClock ρ (s / (L − s))`. -/
def stageLift (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (α : ℝ≥0 → ℂ) : ℝ≥0 → ℂ :=
  fun s => α (capClock (stCurve c m s₁ e₁ s₂) ((s : ℝ) / (e₁.2.toReal - s))).toNNReal

/-- The image of `[0, s]` under `r ↦ f r.toNNReal`. -/
theorem image_toNNReal_Icc {X : Type*} (f : ℝ≥0 → X) {s : ℝ} (hs : 0 ≤ s) :
    (fun r : ℝ => f r.toNNReal) '' Icc 0 s = f '' Icc 0 s.toNNReal := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hr.2⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨t.2, ?_⟩, show f (t : ℝ).toNNReal = f t by rw [Real.toNNReal_coe]⟩
    have := NNReal.coe_le_coe.2 ht.2
    rwa [Real.coe_toNNReal _ hs] at this

/-- The inverse capacity clock maps `[0, capClock u]` onto `[0, u]`. -/
theorem image_capInv_Icc {ρ : ℝ → ℂ} (hρ : IsDrivenCurve ρ) {u : ℝ} (hu : 0 ≤ u) :
    (fun x : ℝ≥0 => capInv ρ x) '' Icc 0 (capClock ρ u).toNNReal = Icc 0 u := by
  have hc0 := hρ.capClock_nonneg hu
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨capInv_nonneg ρ x, hρ.capInv_le hu x.2 ?_⟩
    have := NNReal.coe_le_coe.2 hx.2
    rwa [Real.coe_toNNReal _ hc0] at this
  · rintro ⟨hv0, hvu⟩
    refine ⟨(capClock ρ v).toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal
      (hρ.strictMonoOn_capClock.monotoneOn hv0 hu hvu)⟩, ?_⟩
    show capInv ρ ((capClock ρ v).toNNReal : ℝ) = v
    rw [Real.coe_toNNReal _ (hρ.capClock_nonneg hv0), hρ.capInv_eq hv0]

variable {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {α : ℝ≥0 → ℂ}

/-- **The capacity clock of the lift is `φ`**, and the lift traces the same sets as the stage curve. -/
theorem image_stageLift (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) {L₁ : ℝ≥0}
    (hL₁ : e₁.2 = L₁) {s : ℝ≥0} (hs : s < L₁) :
    stageLift c m s₁ e₁ s₂ α '' Icc 0 s =
      α '' Icc 0 (capClock (stCurve c m s₁ e₁ s₂) ((s : ℝ) / (L₁ - s))).toNNReal ∧
    α '' Icc 0 (capClock (stCurve c m s₁ e₁ s₂) ((s : ℝ) / (L₁ - s))).toNNReal =
      stCurve c m s₁ e₁ s₂ '' Icc 0 ((s : ℝ) / (L₁ - s)) := by
  set ρ := stCurve c m s₁ e₁ s₂ with hρdef
  have hℓ : e₁.2.toReal = L₁ := by rw [hL₁]; rfl
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
  · have e : stageLift c m s₁ e₁ s₂ α = fun t => α (φ t).toNNReal := by
      funext t
      simp only [stageLift, hℓ, hφdef, hρdef]
    rw [e, ← image_image (g := α) (f := fun t => (φ t).toNNReal), himg]
  · have hlt : ∀ τ : ℝ≥0, τ ≤ (φ s).toNNReal → (τ : ℝ≥0∞) < e₂.2 := fun τ hτ => by
      rw [he₂]
      refine lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt (hu0 s hs))
      exact (ENNReal.coe_le_coe.2 hτ)
    rw [image_congr fun τ hτ => hαeq τ (hlt τ hτ.2)]
    change (fun τ : ℝ≥0 => ρ (capInv ρ τ)) '' _ = _
    rw [← image_image (g := ρ) (f := fun x : ℝ≥0 => capInv ρ x), image_capInv_Icc hρ (hu0 s hs)]

/-- **The capacity clock of the lift**: `capClock γ s = capClock ρ (s / (L − s))` before the actual lifetime. -/
theorem capClock_stageLift (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) {L₁ : ℝ≥0}
    (hL₁ : e₁.2 = L₁) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < L₁) :
    capClock (fun r : ℝ => stageLift c m s₁ e₁ s₂ α r.toNNReal) s =
      capClock (stCurve c m s₁ e₁ s₂) (s / (L₁ - s)) := by
  have hs' : s.toNNReal < L₁ := (Real.toNNReal_lt_iff_lt_coe hs0).2 hs
  obtain ⟨h1, h2⟩ := image_stageLift hρ he₂ hαeq hL₁ hs'
  unfold capClock
  rw [image_toNNReal_Icc _ hs0, h1, h2, Real.coe_toNNReal _ hs0]

/-- **(G3): the relative chain's core at a concrete stage, driven by `e₂`.** For every `S₀ < L` there are a driver
and a trace agreeing with `e₂`'s on `[0, capClock γ S₀]` for which every field of the relative chain other than the
two hull fields holds (`γ` the stage lift). -/
theorem relChainCore_concrete (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {L₁ : ℝ≥0} (hL₁ : e₁.2 = L₁)
    {S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀L : S₀ < L₁) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => stageLift c m s₁ e₁ s₂ α r.toNNReal) S₀ →
        Wr r = e₂.1 r.toNNReal ∧ ηr r = α r.toNNReal) ∧
      RelChainCore (stageLift c m s₁ e₁ s₂ α) S₀ Wr ηr := by
  set ρ := stCurve c m s₁ e₁ s₂ with hρdef
  have hL₁pos : (0 : ℝ) < L₁ := lt_of_le_of_lt hS₀ hS₀L
  have hℓ : e₁.2.toReal = L₁ := by rw [hL₁]; rfl
  have hu0 : ∀ s : ℝ, 0 ≤ s → s < L₁ → 0 ≤ s / (L₁ - s) := fun s hs0 hs =>
    div_nonneg hs0 (sub_nonneg.2 hs.le)
  have hcap : ∀ s ∈ Icc (0 : ℝ) S₀,
      capClock (fun r : ℝ => stageLift c m s₁ e₁ s₂ α r.toNNReal) s = capClock ρ (s / (L₁ - s)) := fun s hs =>
    capClock_stageLift hρ he₂ hαeq hL₁ hs.1 (lt_of_le_of_lt hs.2 hS₀L)
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
    have hγs : stageLift c m s₁ e₁ s₂ α s.toNNReal = α (capClock ρ (s / (L₁ - s))).toNNReal := by
      simp only [stageLift, hℓ, Real.coe_toNNReal _ hs.1, hρdef]
    refine ⟨hτ0, ?_, ?_⟩
    · rw [YuanCorollary13.extTrace_eq hτT, hγs]
    · rw [hLT.fwdHull_extDrive_of_le hWc hT't₂ hτ0 hτT,
        image_congr fun r hr => YuanCorollary13.extTrace_eq (hr.2.trans hτT), image_toNNReal_Icc α hτ0,
        (image_stageLift hρ he₂ hαeq hL₁ hs').1, Real.coe_toNNReal _ hs.1]

/-- **The lifetime clause**: the relative lifetime is the supremum of the lift's capacity clock before the actual
lifetime. -/
theorem lifetime_eq_iSup_capClock (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) {L₁ : ℝ≥0}
    (hL₁ : e₁.2 = L₁) (hpos : 0 < L₁) :
    e₂.2 = ⨆ (S₀ : ℝ≥0) (_ : (S₀ : ℝ≥0∞) < e₁.2),
      ENNReal.ofReal (capClock (fun r : ℝ => stageLift c m s₁ e₁ s₂ α r.toNNReal) (S₀ : ℝ)) := by
  have hcap : ∀ S₀ : ℝ≥0, S₀ < L₁ →
      capClock (fun r : ℝ => stageLift c m s₁ e₁ s₂ α r.toNNReal) (S₀ : ℝ) =
        capClock (stCurve c m s₁ e₁ s₂) ((S₀ : ℝ) / (L₁ - S₀)) := fun S₀ h =>
    capClock_stageLift hρ he₂ hαeq hL₁ S₀.2 (NNReal.coe_lt_coe.2 h)
  have hlt : ∀ S₀ : ℝ≥0, (S₀ : ℝ≥0∞) < e₁.2 ↔ S₀ < L₁ := fun S₀ => by rw [hL₁]; exact ENNReal.coe_lt_coe
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

end InteractingSLE.Theorem14.SB.Mn
