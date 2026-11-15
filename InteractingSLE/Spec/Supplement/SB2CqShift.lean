/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CwChain

/-!
# The chain clause of the canonical driver from a tail start (the root)

Packet PROVE-SB2-CANON, round 5 (`Mz.CanonIdentOn` at `relOff`). At the relative root B's piece enters the retained
union's right end `R` at a time `τ` (B's head before `τ` lies in the retained union's hull), and the relative curve is
the canonical curve of the post-entry piece `p = P(τ + ·)` with lifetime `L` (B's lifetime `BL = τ + L`).
**`chainFor_canon_shift`** is `chainFor_canon` with the chain's tail start `tL = τ`: the hull inputs read B's stage
trace on `[0, τ + s]`, the piece input at `τ + t`. The proof is `chainFor_canon`'s, with the start shifted.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Cz

open Sec7.PocketTraversal Sec7.Lemma71C Dv Exist.Staged

variable {Y : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}

/-- **The chain clause of the canonical driver from a tail start `τ`** (deterministic, one sample). -/
theorem chainFor_canon_shift {cℓ : Chart} (hYc : IsCompact Y) (hA : IsHPHull (fillH Y)) (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve Y x₀ p L)) {β' : ℝ≥0 → ℂ}
    (hcℓ : ∀ z ∈ H \ fillH (Mn.stageRetained cℓ Y), cℓ.2.1 z ∈ H \ fillH Y) (hinj : InjOn cℓ.2.1 H)
    {τ : ℝ≥0} {BL : ℝ≥0∞} (hBL : ∀ S : ℝ≥0, ((τ + S : ℝ≥0) : ℝ≥0∞) < BL ↔ (S : ℝ≥0∞) < L)
    (hin : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L → ∀ z ∈ fillH (β' '' Icc 0 (τ + s)), z ∉ fillH (Mn.stageRetained cℓ Y) →
      cℓ.2.1 z ∈ fillH (Y ∪ p '' Icc 0 s))
    (hpiece : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → p t ∈ H \ fillH Y → β' (τ + t) ∈ H ∧ cℓ.2.1 (β' (τ + t)) = p t)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver e)
    (he1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife (canonCurve Y x₀ p L) → e.1 t = segDriver (canonCurve Y x₀ p L) t)
    (he2 : e.2 = capLife (canonCurve Y x₀ p L)) :
    Mx.ChainFor (Mn.stageRetained cℓ Y) (Mx.stageChartOf cℓ (Mo.hullChart (fillH Y) x₀)) β' BL e := by
  set ρ := canonCurve Y x₀ p L with hρ
  set γ := canonVal Y x₀ p L with hγ
  set Φ := Mo.hullChart (fillH Y) x₀ with hΦ
  refine ⟨τ, γ, fun S₀ hS₀ => ?_, he2.trans ((capLife_eq_iSup_canon hL hdr).trans
    (iSup_congr fun S₀ => iSup_congr_Prop (by rw [zero_add]; exact (hBL S₀).symm) fun _ => rfl))⟩
  replace hS₀ := (hBL S₀).1 hS₀
  have hB₀ : Nc.BeforeL L (S₀ : ℝ) := Nc.beforeL_of_lt hS₀
  have hU₀ : 0 ≤ Nc.uOf L S₀ := Nc.uOf_nonneg hB₀
  have hq₀ := hdr.ofReal_capClock_lt hU₀
  obtain ⟨v', hv'₁, hv'₂⟩ := ENNReal.lt_iff_exists_real_btwn.1 hq₀
  have hc₀ := hdr.capClock_nonneg hU₀
  have hv'0 : 0 < v' := lt_of_le_of_lt hc₀ ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc₀).1 hv'₂.1 |>.trans_le le_rfl)
  set v : ℝ≥0 := v'.toNNReal with hvdef
  have hvpos : 0 < v := Real.toNNReal_pos.2 hv'0
  have hvU : (v : ℝ≥0∞) < capLife ρ := by
    rw [hvdef, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hv'0.le]; exact hv'₂.2
  have hqv : capClock ρ (Nc.uOf L S₀) < v := by
    rw [hvdef, Real.coe_toNNReal _ hv'0.le]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc₀).1 hv'₂.1
  -- the driver is continuous below its lifetime and generates the capacity trace
  have hWc : ContinuousOn e.1 {t | (t : ℝ≥0∞) < capLife ρ} := by rw [← he2]; exact hreg.1
  have hgen : ∀ T : ℝ≥0∞, T < capLife ρ → IsGeneratingTrace e.1 T (capTrace ρ) := fun T hT =>
    Cf.isGeneratingTrace_congr (fun s hs => (he1 s (hs.trans hT)).symm) (hdr.isGeneratingTrace hT)
  obtain ⟨ηr, hLT, heq⟩ := Vs.exists_loewnerTrace_min hvpos hvU hreg.2.1 hWc hgen
  -- the clock and the hulls in B's time
  have hclk : ∀ s ∈ Icc (0 : ℝ) S₀, Nc.BeforeL L s ∧
      capClock (fun r : ℝ => γ r.toNNReal) s = capClock ρ (Nc.uOf L s) ∧ capClock ρ (Nc.uOf L s) < v := by
    intro s hs
    have hB : Nc.BeforeL L s := ⟨hs.1, by
      rcases hB₀.2 with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_lt hs.2 h)⟩
    refine ⟨hB, Nc.capClock_liftR_canonVal hL hB Y x₀ p, ?_⟩
    refine lt_of_le_of_lt ?_ hqv
    rcases (Nc.monotoneOn_uOf hB hB₀ hs.2).lt_or_eq with h | h
    · exact (hdr.strictMonoOn_capClock (Nc.uOf_nonneg hB) hU₀ h).le
    · rw [h]
  have hWr : ∀ r ∈ Icc (0 : ℝ) v, (fun r : ℝ => e.1 (min r.toNNReal v)) r = segDriver ρ r.toNNReal := by
    intro r hr
    have hrv : r.toNNReal ≤ v := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
    show e.1 (min r.toNNReal v) = _
    rw [min_eq_left hrv]
    exact he1 _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hrv) hvU)
  have hhull : ∀ s ∈ Icc (0 : ℝ) S₀, fwdHull (fun r : ℝ => e.1 (min r.toNNReal v)) (capClock ρ (Nc.uOf L s)) =
      fillH (ρ '' Icc 0 (Nc.uOf L s)) := by
    intro s hs
    obtain ⟨hB, -, hlt⟩ := hclk s hs
    have hc0 := hdr.capClock_nonneg (Nc.uOf_nonneg hB)
    rw [Cf.fwdHull_congr hc0 hlt hWr, hdr.fwdHull_segDriver hc0 (hdr.ofReal_capClock_lt (Nc.uOf_nonneg hB)),
      hdr.capInv_eq (Nc.uOf_nonneg hB)]
  refine ⟨fun r : ℝ => e.1 (min r.toNNReal v), ηr, fun r hr0 hr => ?_, ?_⟩
  · -- agreement with the canonical driver below the clock at `S₀`
    obtain ⟨-, hcl, hlt⟩ := hclk S₀ ⟨S₀.2, le_rfl⟩
    have hrv : r.toNNReal ≤ v := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      rw [hcl] at hr; exact hr.trans hlt.le
    show e.1 (min r.toNNReal v) = e.1 r.toNNReal
    rw [min_eq_left hrv]
  -- the relative chain
  have hcont : Continuous fun r : ℝ => e.1 (min r.toNNReal v) := by
    have hm : Continuous fun r : ℝ => min r.toNNReal v := continuous_real_toNNReal.min continuous_const
    refine hWc.comp_continuous hm fun r => ?_
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hvU
  have hstep : ∀ s ∈ Icc (0 : ℝ) S₀, (s.toNNReal : ℝ≥0∞) < L := fun s hs => by
    have h := (hclk s hs).1
    rcases h.2 with h' | h'
    · rw [h']; exact ENNReal.coe_lt_top
    · have hLt : L ≠ ⊤ := by
        rintro rfl
        simp only [ENNReal.toReal_top] at h'
        linarith [h.1]
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ h.1]
      exact (ENNReal.ofReal_lt_iff_lt_toReal h.1 hLt).2 h'
  refine ⟨hcont, by simp [hreg.2.1], hLT, ?_, ?_, ?_, fun s hs => ?_⟩
  · rw [(hclk 0 ⟨le_rfl, S₀.2⟩).2.1, Nc.uOf_zero]; exact hdr.capClock_zero
  · intro s hs t ht hst
    rw [(hclk s hs).2.1, (hclk t ht).2.1]
    exact hdr.strictMonoOn_capClock (Nc.uOf_nonneg (hclk s hs).1) (Nc.uOf_nonneg (hclk t ht).1)
      (strictMonoOn_uOf (hclk s hs).1 (hclk t ht).1 hst)
  · have h1 : ContinuousOn (fun s => capClock ρ (Nc.uOf L s)) (Icc 0 (S₀ : ℝ)) :=
      hdr.continuousOn_capClock.comp (Nc.continuousOn_uOf.mono fun s hs => (hclk s hs).1)
        fun s hs => Nc.uOf_nonneg (hclk s hs).1
    exact h1.congr fun s hs => (hclk s hs).2.1
  obtain ⟨hB, hcl, hlt⟩ := hclk s hs
  have hU : 0 ≤ Nc.uOf L s := Nc.uOf_nonneg hB
  have hcT : Nc.cTime L (Nc.uOf L s) = s.toNNReal := Nc.cTime_uOf hB
  have hfill : fillH (ρ '' Icc 0 (Nc.uOf L s)) = fillH (γ '' Icc 0 s.toNNReal) := by
    rw [hρ, Nc.image_canonCurve_Icc hL hU, hcT]
  rw [hcl]
  refine ⟨hdr.capClock_nonneg hU, ?_, (hhull s hs).trans hfill, fun z hz hzA => ?_, fun z hz hfr => ?_⟩
  · -- the trace at the clock is the relative curve
    have hc0 := hdr.capClock_nonneg hU
    have h := heq (capClock ρ (Nc.uOf L s)).toNNReal (by
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hc0, ← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hvpos)).2 hlt)
    rw [Real.coe_toNNReal _ hc0] at h
    rw [h]
    unfold capTrace
    rw [Real.coe_toNNReal _ hc0, hdr.capInv_eq hU, hρ, Nc.canonCurve_eq, hcT]
  · -- hull transport, inside
    rw [hhull s hs]
    have hzH : z ∈ H := fillH_subset_H _ hz
    have hx := hcℓ z ⟨hzH, hzA⟩
    have hJ := hin s.toNNReal (hstep s hs) z hz hzA
    rw [← hcT] at hJ
    exact (mem_fillH_canon_iff hYc hA hL hpc hdr hU hx).2 hJ
  · -- hull transport, frontier
    rw [hhull s hs] at hfr
    have hx := hcℓ z hz
    have hpx := mem_piece_of_frontier_canon hYc hA hL hpc hdr hU hx hfr
    rw [hcT] at hpx
    obtain ⟨t, ht, hpt⟩ := hpx
    have htL : (t : ℝ≥0∞) < L := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) (hstep s hs)
    obtain ⟨hβH, hβp⟩ := hpiece t htL (by rw [hpt]; exact hx)
    have hzt : β' (τ + t) = z := hinj hβH hz.1 (by rw [hβp, hpt])
    exact Qx.self_inter_H_subset_fillH _ ⟨⟨τ + t, ⟨bot_le, add_le_add_right ht.2 τ⟩, hzt⟩, hz.1⟩

end InteractingSLE.Theorem14.SB.Cz
