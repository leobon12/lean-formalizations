/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WzLift
import InteractingSLE.Spec.Supplement.SB2TcChainAt
import InteractingSLE.Spec.Supplement.SB2GAssembleK

/-!
# SB2(1)'s late (S) line mean, part 11: FIN's configuration at a fixed line time

Packet PROVE-T14-SB2DRV (round 11), the input `hcfg` of FIN's union mean
(`FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK`) from the per-time chain record `Tc.IsSB2LineChainAt` at a
line time `t` after the entrance, given the tip condition (`SB2JxTipStatement`):

* **`mem_image_of_mem_dom_recenter`**: a point of the domain of the recentred chart `c.recenter m` is in `c.2.1 '' ℍ`
  (the form of the tip condition used by the lift lemma);
* **`image_translate_eq_fillH`**: if the recentred chart's domain is `ℍ \ X` and the seed-shifted chart's image of `ℍ`
  is `ℍ \ fill Y`, then `X − u = fill Y` (FIN's retained set, the translated walk fill, is the chain's fill);
* **`exists_relConfigJK_of_chainAt`**: from the per-time chain record at `t`, `T_L < t` and the tip condition, FIN's
  configuration `IsRelConfigJK` at exploration time `t` and relative time `a(t)`, for the record's chart, drivers and
  traces, the relative driver agreeing with `W` below the lifetime, and the exploration trace equal to `η − u` on
  `[0, t₂)` for some `t₂ > t` (`FinRel.isRelConfigJK_of_s2_liftOn` at `s = t − T_L`, its `hγH` from
  `lift_mem_H_of_tip`).

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.SB.Lv

open Supp8.Q3Chain (flowedData flowedJumps initJumps)

/-- **The tip condition in chart-image form.** -/
theorem mem_image_of_mem_dom_recenter {c : Chart} {m : ℝ} (hc : (c.recenter m).IsConformal) {z : ℂ}
    (hz : z ∈ ((c.recenter m).dom : Set ℂ)) : z ∈ c.2.1 '' H := by
  rw [hc.coe_dom] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨y + m, ?_, rfl⟩
  show 0 < (y + (m : ℂ)).im
  have : 0 < y.im := hy
  simpa using this

/-- Real translation of a subset of `ℍ` commutes with `ℍ \ ·`. -/
theorem image_translate_H_sdiff (X : Set ℂ) (u : ℝ) :
    (fun z : ℂ => z - u) '' (H \ X) = H \ (fun z : ℂ => z + (-u : ℝ)) '' X := by
  ext z
  simp only [mem_image, Set.mem_sdiff]
  constructor
  · rintro ⟨y, ⟨hy, hyX⟩, rfl⟩
    refine ⟨show 0 < (y - (u : ℂ)).im by have : 0 < y.im := hy; simpa using this, ?_⟩
    rintro ⟨x, hx, hxe⟩
    have : x = y := by
      have := congrArg (fun v : ℂ => v + u) hxe
      simp only [Complex.ofReal_neg, neg_add_cancel_right, sub_add_cancel] at this
      exact this
    exact hyX (this ▸ hx)
  · rintro ⟨hz, hzX⟩
    refine ⟨z + u, ⟨show 0 < (z + (u : ℂ)).im by have : 0 < z.im := hz; simpa using this, fun h => hzX ?_⟩,
      by ring⟩
    exact ⟨z + u, h, by push_cast; ring⟩

/-- Two subsets of `ℍ` with the same complement in `ℍ` are equal. -/
theorem eq_of_H_sdiff_eq {X Y : Set ℂ} (hX : X ⊆ H) (hY : Y ⊆ H) (h : H \ X = H \ Y) : X = Y := by
  ext z
  constructor
  · intro hz
    by_contra hzY
    have : z ∈ H \ Y := ⟨hX hz, hzY⟩
    rw [← h] at this
    exact this.2 hz
  · intro hz
    by_contra hzX
    have : z ∈ H \ X := ⟨hY hz, hzX⟩
    rw [h] at this
    exact this.2 hz

/-- **FIN's retained set is the chain's fill**: if the recentred chart has domain `ℍ \ X` and the seed-shifted chart's
image of `ℍ` is `ℍ \ fill Y`, then `X − u = fill Y`. -/
theorem image_translate_eq_fillH {c : Chart} {u m : ℝ} (hc : (c.recenter m).IsConformal) {X Y : Set ℂ}
    (hX : X ⊆ H) (hdom : ((c.recenter m).dom : Set ℂ) = H \ X)
    (himg : (Lw.shiftChart c u m).2.1 '' H = H \ fillH Y) :
    (fun z : ℂ => z + (-u : ℝ)) '' X = fillH Y := by
  have e : (Lw.shiftChart c u m).2.1 '' H = (fun z : ℂ => z - u) '' ((c.recenter m).2.1 '' H) := by
    rw [image_image]
    rfl
  rw [← hc.coe_dom, hdom, image_translate_H_sdiff, himg] at e
  refine eq_of_H_sdiff_eq ?_ (fillH_subset_H Y) e.symm
  rintro _ ⟨x, hx, rfl⟩
  show 0 < (x + ((-u : ℝ) : ℂ)).im
  have : 0 < x.im := hX hx
  simpa using this

/-- **FIN's configuration at a fixed line time from the per-time chain record and the tip condition.** -/
theorem exists_relConfigJK_of_chainAt {A : Set ℂ} {u m : ℝ} {c : Chart} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    {W : ℝ≥0 → ℝ} {a : ℝ≥0 → ℝ≥0∞} {V : ℝ≥0∞} {t : ℝ≥0} (hch : Tc.IsSB2LineChainAt A u m c η ζ W a V t)
    (hlate : firstVisit η ζ (realMin A) < (t : ℝ≥0∞)) (htip : η t ∈ c.2.1 '' H) {κ χ : ℝ}
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (w : ℝ → ℝ) (ηw : ℝ → ℂ) (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ),
      (∀ q : ℝ≥0, (q : ℝ≥0∞) < V → W q = Wr q) ∧
      (∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ ∀ r : ℝ, 0 ≤ r → r < t₂ → ηw r = η r.toNNReal - u) ∧
      a t ≠ ⊤ ∧ IsLeftEntryChart ((fun z : ℂ => z - u) '' A) (realMin ((fun z : ℂ => z - u) '' A))
        (Lw.shiftChart c u m) ∧
      EqOn (Lw.shiftChart c u m).2.2 (fun z => (LΨ z).im) (H \ fillH ((fun z : ℂ => z - u) '' A)) ∧
      FinRel.IsRelConfigJK (fillH ((fun z : ℂ => z - u) '' A)) (Lw.shiftChart c u m).1 (Lw.shiftChart c u m).2.1 LΨ ∅ w
        Wr ηw ηr t ((a t).toNNReal : ℝ) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w t) (flowedData κ ρL ρR xL xR Wr ((a t).toNNReal : ℝ))
        (initJumps xL xR) (flowedJumps xL' xR' w t) (flowedJumps xL xR Wr ((a t).toNNReal : ℝ)) G₀ GE G
        (fun z => G (fwdMap Wr ((a t).toNNReal : ℝ) ((Lw.shiftChart c u m).1 z)) -
          χ * ((logDerivFwd Wr ((a t).toNNReal : ℝ) ((Lw.shiftChart c u m).1 z)).im + (LΨ z).im)) := by
  obtain ⟨p, g, β', γ, tL, S, Wr, ηr, w, ηw, htS, ⟨hp, hp0, hpH, -, hpA⟩, ⟨hc, hgc, hgi, hgf, hL⟩,
    ⟨hβ', hβ'0, hA, htL, htLv, hγ, hγ0, hlift⟩, hβη, ⟨-, hchS, hnR⟩, ⟨hw, hw0, hηw, hwt, hηβ⟩,
    ⟨hWr, -, ha⟩⟩ := hch
  have htLt : tL < t := by
    have : ((tL : ℝ≥0) : ℝ≥0∞) < t := htLv ▸ hlate
    exact_mod_cast this
  have htLt' : (tL : ℝ) < t := htLt
  set s : ℝ := (t : ℝ) - tL with hs_def
  have hs0 : 0 < s := by rw [hs_def]; linarith
  have hsS : s < S := by rw [hs_def]; linarith
  have hts : (tL : ℝ) + s = t := by rw [hs_def]; ring
  have hsnn : s.toNNReal = t - tL := by rw [hs_def, ← NNReal.coe_sub htLt.le, Real.toNNReal_coe]
  have hγH : γ s.toNNReal ∈ H := by
    rw [hsnn]
    exact lift_mem_H_of_tip hc.1.1 hgc hgi hγ hlift (hβη t htS) htip htLt.le
  have hηβ' : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), ηw r = β' r.toNNReal := fun r hr =>
    hηβ r hr.1 (by rw [hts] at hr; linarith [hr.2])
  obtain ⟨LΨ, G₀, GE, G, hEq, hcfg⟩ := FinRel.isRelConfigJK_of_s2_liftOn (κ := κ) (χ := χ) (ρL := ρL) (ρR := ρR)
    (ρL' := ρL') (ρR' := ρR') hxL hxR hxL' hxR' hp hp0 hpH hc hgc hgi hgf hL hβ' hβ'0 hA htL hγ hγ0 hlift
    (hchS s hs0.le hsS) hsS hnR ⟨hs0, le_rfl⟩ hw hw0 hηw (hwt s hs0 hsS) hηβ' hγH
  have hat : a t = ((Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s).toNNReal : ℝ≥0∞) :=
    ha t htLt.le htS
  have hcap : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s = ((a t).toNNReal : ℝ) := by
    rw [hat, ENNReal.toNNReal_coe, Real.coe_toNNReal _ hcfg.hu]
  rw [hts, hcap, hpA] at hcfg
  rw [hpA] at hEq hc
  refine ⟨Wr, ηr, w, ηw, LΨ, G₀, GE, G, hWr, ⟨(tL : ℝ) + S, htS, fun r hr0 hrt' => ?_⟩,
    by rw [hat]; exact ENNReal.coe_ne_top, hc, hEq, hcfg⟩
  rw [hηβ r hr0 hrt', hβη _ (by rw [Real.coe_toNNReal _ hr0]; exact hrt')]

end InteractingSLE.Theorem14.SB.Lv
