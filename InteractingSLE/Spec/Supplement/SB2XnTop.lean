/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XmCore

/-!
# (G3) at an infinite actual piece: the relative chain core and the lifetime clause

Packet PROVE-T14-SB2LIFT (round 26). At a stage of PROVE-SB2-LIFTSET's concrete rule whose actual piece has infinite
lifetime (B's last piece), the stage curve reads the actual piece at actual time `u` itself (`stCurve_of_top`), so the
relative chart-coordinate lift is `stageLiftTop … s = α (capClock ρ s)`:

* **`image_stageLiftTop`**, **`capClock_stageLiftTop`**: `γ([0, s]) = ρ([0, s])`, so `capClock γ = capClock ρ`;
* **`relChainCore_top`**: for every `S₀`, the core of the relative chain holds for `e₂`'s driver frozen at a time in
  `(capClock γ S₀, e₂.2)` (the relative lifetime may be infinite) with Yuan's slit extension;
* **`relChain_of_stageGeomInf`**: from LIFTSET's `StageGeomInf`, the chain clause of `StageChainAtR2` without the hull
  fields (agreement with `LuM.trOf e₂`) and the lifetime clause `e₂.2 = ⨆ capClock γ S₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk Sec7.PocketTraversal Sec7.Lemma71C

/-- The relative chart-coordinate lift at an infinite actual piece. -/
def stageLiftTop (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (α : ℝ≥0 → ℂ) : ℝ≥0 → ℂ :=
  fun s => α (capClock (stCurve c m s₁ e₁ s₂) (s : ℝ)).toNNReal

variable {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {α : ℝ≥0 → ℂ}

/-- **The lift traces the same sets as the stage curve.** -/
theorem image_stageLiftTop (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) (s : ℝ≥0) :
    stageLiftTop c m s₁ e₁ s₂ α '' Icc 0 s = α '' Icc 0 (capClock (stCurve c m s₁ e₁ s₂) (s : ℝ)).toNNReal ∧
    α '' Icc 0 (capClock (stCurve c m s₁ e₁ s₂) (s : ℝ)).toNNReal = stCurve c m s₁ e₁ s₂ '' Icc 0 (s : ℝ) := by
  set ρ := stCurve c m s₁ e₁ s₂ with hρdef
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
  · have e : stageLiftTop c m s₁ e₁ s₂ α = fun t => α (φ t).toNNReal := rfl
    rw [e, ← image_image (g := α) (f := fun t => (φ t).toNNReal), himg]
  · show α '' Icc 0 (capClock ρ (s : ℝ)).toNNReal = ρ '' Icc 0 (s : ℝ)
    have hlt : ∀ τ : ℝ≥0, τ ≤ (capClock ρ (s : ℝ)).toNNReal → (τ : ℝ≥0∞) < e₂.2 := fun τ hτ => by
      rw [he₂]
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hτ) (hρ.ofReal_capClock_lt s.2)
    rw [image_congr fun τ hτ => hαeq τ (hlt τ hτ.2)]
    change (fun τ : ℝ≥0 => ρ (capInv ρ τ)) '' _ = _
    rw [← image_image (g := ρ) (f := fun x : ℝ≥0 => capInv ρ x), image_capInv_Icc hρ (NNReal.coe_nonneg s)]

/-- **The capacity clock of the lift is that of the stage curve.** -/
theorem capClock_stageLiftTop (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) {s : ℝ} (hs0 : 0 ≤ s) :
    capClock (fun r : ℝ => stageLiftTop c m s₁ e₁ s₂ α r.toNNReal) s = capClock (stCurve c m s₁ e₁ s₂) s := by
  obtain ⟨h1, h2⟩ := image_stageLiftTop hρ he₂ hαeq s.toNNReal
  unfold capClock
  rw [image_toNNReal_Icc _ hs0, h1, h2, Real.coe_toNNReal _ hs0]

/-- **(G3) at an infinite actual piece**: for every `S₀`, the relative chain's core for `e₂`'s driver frozen at a time
in `(capClock γ S₀, e₂.2)` (finite or infinite relative lifetime), agreeing with `e₂`'s driver and `α` on
`[0, capClock γ S₀]`. -/
theorem relChainCore_top (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {S₀ : ℝ} (hS₀ : 0 ≤ S₀) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => stageLiftTop c m s₁ e₁ s₂ α r.toNNReal) S₀ →
        Wr r = e₂.1 r.toNNReal ∧ ηr r = α r.toNNReal) ∧
      RelChainCore (stageLiftTop c m s₁ e₁ s₂ α) S₀ Wr ηr := by
  set ρ := stCurve c m s₁ e₁ s₂ with hρdef
  have hcap : ∀ s ∈ Icc (0 : ℝ) S₀,
      capClock (fun r : ℝ => stageLiftTop c m s₁ e₁ s₂ α r.toNNReal) s = capClock ρ s := fun s hs =>
    capClock_stageLiftTop hρ he₂ hαeq hs.1
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
    have hγs : stageLiftTop c m s₁ e₁ s₂ α s.toNNReal = α (capClock ρ s).toNNReal := by
      simp only [stageLiftTop, Real.coe_toNNReal _ hs.1, hρdef]
    refine ⟨hτ0, ?_, ?_⟩
    · rw [YuanCorollary13.extTrace_eq hτT, hγs]
    · rw [hLT.fwdHull_extDrive_of_le hWc hT't₂ hτ0 hτT,
        image_congr fun r hr => YuanCorollary13.extTrace_eq (hr.2.trans hτT), image_toNNReal_Icc α hτ0,
        (image_stageLiftTop hρ he₂ hαeq s.toNNReal).1, Real.coe_toNNReal _ hs.1]

/-- **The lifetime clause at an infinite actual piece.** -/
theorem lifetime_eq_iSup_capClock_top (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) (he₁ : e₁.2 = ⊤) :
    e₂.2 = ⨆ (S₀ : ℝ≥0) (_ : (S₀ : ℝ≥0∞) < e₁.2),
      ENNReal.ofReal (capClock (fun r : ℝ => stageLiftTop c m s₁ e₁ s₂ α r.toNNReal) (S₀ : ℝ)) := by
  rw [he₂]
  refine le_antisymm (iSup_le fun n => ?_) (iSup₂_le fun S₀ _ => ?_)
  · refine le_iSup₂_of_le (n : ℝ≥0) (by rw [he₁]; exact ENNReal.coe_lt_top) (le_of_eq ?_)
    rw [capClock_stageLiftTop hρ he₂ hαeq (NNReal.coe_nonneg _), NNReal.coe_natCast]
  · rw [capClock_stageLiftTop hρ he₂ hαeq (NNReal.coe_nonneg _)]
    exact (hρ.ofReal_capClock_lt (NNReal.coe_nonneg _)).le

end InteractingSLE.Theorem14.SB.Mn
