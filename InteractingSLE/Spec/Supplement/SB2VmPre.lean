/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkAsm

/-!
# SB2(1)'s version half: the family's prefixes read in absolute time (deterministic)

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half; `Vk.SB2DriverAdaptStatement`). The canonical driver of
the driven family `ρ` at capacity `r` is a functional of the prefix images `ρ '' [0, capInv ρ r']`, `r' ≤ r`
(`PocketTraversal.measurable_indicator_segDrv_of_isDrivenCurve`). This file identifies these prefixes with the
absolute lift `T ↦ γ (T − T_L)` over the times where the clock is at most `r'`, and decides their meeting a closed
set from rational readings at times `≤ t`:

* `exists_liftTime`: every family parameter is a lift time with the same capacity;
* `clockOf_le_relSup`: the clock is at most the relative lifetime;
* **`image_capInv_eq`**: `ρ '' [0, capInv ρ r'] = absLift '' {T : clock T ≤ r'}` when `r'` is below the clock at `t`;
* **`nonempty_inter_image_iff`**: for a closed nonempty `Q`, `Q` meets `f '' {T : A T ≤ r'}` iff for every `m` some
  rational `q ≤ t` has `A q ≤ r' + 1/(m+1)` and its reading within `1/(m+1)` of `Q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vm

open Sec7.PocketTraversal Sec7.Lemma71C

section Det

variable {γ : ℝ≥0 → ℂ} {TL Z : ℝ≥0∞} {ρ : ℝ → ℂ}

/-- **Every family parameter is a lift time** with the same capacity. -/
theorem exists_liftTime (hTZ : TL < Z) (h1 : Z = ⊤ → EqOn ρ (Vd.liftR γ) (Ici 0))
    (h2 : Z ≠ ⊤ → EqOn ρ (relCurve (Vd.liftR γ) (Z.toReal - TL.toReal)) (Ici 0)) {x : ℝ} (hx : 0 ≤ x) :
    ∃ y : ℝ≥0, ((TL.toNNReal + y : ℝ≥0) : ℝ≥0∞) < Z ∧ ρ x = γ y ∧
      capClock ρ x = capClock (Vd.liftR γ) y := by
  by_cases hZ : Z = ⊤
  · refine ⟨x.toNNReal, by rw [hZ]; exact ENNReal.coe_lt_top, ?_, ?_⟩
    · rw [h1 hZ (show x ∈ Ici 0 from hx)]; rfl
    · rw [Vk.capClock_congr_Ici (h1 hZ) x, Real.coe_toNNReal _ hx]
  · have hTL : TL ≠ ⊤ := ne_top_of_lt hTZ
    set ℓ : ℝ := Z.toReal - TL.toReal with hℓ
    have hℓ0 : 0 < ℓ := by rw [hℓ, sub_pos]; exact (ENNReal.toReal_lt_toReal hTL hZ).2 hTZ
    have hc := clockOf_mem_Ico hℓ0 hx
    refine ⟨(clockOf ℓ x).toNNReal, ?_, ?_, ?_⟩
    · rw [← ENNReal.coe_toNNReal hZ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add,
        Real.coe_toNNReal _ hc.1]
      have e1 : Z.toReal = (Z.toNNReal : ℝ) := rfl
      have e2 : TL.toReal = (TL.toNNReal : ℝ) := rfl
      have := hc.2
      have hℓ' : ℓ = (Z.toNNReal : ℝ) - (TL.toNNReal : ℝ) := by rw [hℓ, e1, e2]
      linarith
    · rw [h2 hZ (show x ∈ Ici 0 from hx)]; rfl
    · rw [Vk.capClock_congr_Ici (h2 hZ) x, Vk.capClock_relCurve hℓ0 hx, Real.coe_toNNReal _ hc.1]

/-- **The clock is at most the relative lifetime.** -/
theorem clockOf_le_relSup (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Z : ℝ≥0∞) (t : ℝ≥0) :
    Vc.clockOf γ tL Z t ≤ ⨆ (s : ℝ≥0) (_ : ((tL + s : ℝ≥0) : ℝ≥0∞) < Z),
      ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) s) := by
  unfold Vc.clockOf
  exact iSup₂_le fun s _ => iSup_le fun hs => le_iSup₂_of_le s hs le_rfl

/-- After the lifetime the clock is at least its value at any time. -/
theorem clockOf_le_of_le (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) {Z : ℝ≥0∞} (t : ℝ≥0) {T : ℝ≥0} (hT : Z ≤ T) :
    Vc.clockOf γ tL Z t ≤ Vc.clockOf γ tL Z T := by
  rw [Vd.clockOf_eq_sup_of_le hT]
  exact clockOf_le_relSup γ tL Z t

/-- **The prefix of the family up to capacity `r'` is the absolute lift over the times with clock `≤ r'`.** -/
theorem image_capInv_eq (hρ : IsDrivenCurve ρ) (hTZ : TL < Z) (h1 : Z = ⊤ → EqOn ρ (Vd.liftR γ) (Ici 0))
    (h2 : Z ≠ ⊤ → EqOn ρ (relCurve (Vd.liftR γ) (Z.toReal - TL.toReal)) (Ici 0))
    (hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ((TL.toNNReal + y.toNNReal : ℝ≥0) : ℝ≥0∞) < Z →
      capClock (Vd.liftR γ) x ≤ capClock (Vd.liftR γ) y)
    {t : ℝ≥0} {r' : ℝ} (hr' : 0 ≤ r') (hrt : ENNReal.ofReal r' < Vc.clockOf γ TL.toNNReal Z t)
    (hlife : Vc.clockOf γ TL.toNNReal Z t ≤ capLife ρ) :
    ρ '' Icc 0 (capInv ρ r') =
      (fun T : ℝ≥0 => γ (T - TL.toNNReal)) '' {T | Vc.clockOf γ TL.toNNReal Z T ≤ ENNReal.ofReal r'} := by
  have hTL : TL ≠ ⊤ := ne_top_of_lt hTZ
  set tL := TL.toNNReal with htL
  have hr'L : ENNReal.ofReal r' < capLife ρ := hrt.trans_le hlife
  obtain ⟨hinv0, hinv⟩ := hρ.capInv_spec hr' hr'L
  have hρ0 : ρ 0 = γ 0 := by
    by_cases hZ : Z = ⊤
    · rw [h1 hZ (show (0 : ℝ) ∈ Ici (0 : ℝ) from Set.self_mem_Ici)]
      show γ (0 : ℝ).toNNReal = γ 0
      rw [Real.toNNReal_zero]
    · rw [h2 hZ (show (0 : ℝ) ∈ Ici (0 : ℝ) from Set.self_mem_Ici)]
      show γ (clockOf _ 0).toNNReal = γ 0
      rw [clockOf_zero, Real.toNNReal_zero]
  -- the clock before the lifetime
  have hA : ∀ y : ℝ≥0, ((tL + y : ℝ≥0) : ℝ≥0∞) < Z →
      Vc.clockOf γ tL Z (tL + y) = ENNReal.ofReal (capClock (Vd.liftR γ) y) := fun y hy => by
    have e : ((tL + y : ℝ≥0) : ℝ) - tL = y := by rw [NNReal.coe_add]; ring
    have hm : MonotoneOn (capClock fun r : ℝ => γ r.toNNReal) (Icc 0 (((tL + y : ℝ≥0) : ℝ) - tL)) := by
      rw [e]
      intro x hx z hz hxz
      refine hmono x z hx.1 hxz (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add le_rfl ?_)) hy)
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hx.1.trans hxz)]
      exact hz.2
    rw [Vc.clockOf_eq le_self_add hy hm, e]
    rfl
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hρy, hcy⟩ := exists_liftTime hTZ h1 h2 hx.1
    refine ⟨tL + y, ?_, by simp only [add_tsub_cancel_left, hρy]⟩
    show Vc.clockOf γ tL Z (tL + y) ≤ _
    rw [hA y hy, ← hcy]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hinv]
    exact hρ.strictMonoOn_capClock.monotoneOn hx.1 hinv0 hx.2
  · rintro ⟨T, hT, rfl⟩
    simp only [mem_ofPred_eq] at hT
    rcases le_or_gt T tL with hTt | hTt
    · refine ⟨0, ⟨le_rfl, hinv0⟩, ?_⟩
      show ρ 0 = γ (T - tL)
      rw [hρ0, tsub_eq_zero_of_le hTt]
    · have hTZ' : (T : ℝ≥0∞) < Z := by
        by_contra hc
        rw [not_lt] at hc
        exact absurd (hT.trans_lt hrt) (not_lt.2 (clockOf_le_of_le γ tL t hc))
      set y := T - tL with hy
      have hTy : tL + y = T := add_tsub_cancel_of_le hTt.le
      rw [← hTy] at hT hTZ'
      rw [hA y hTZ'] at hT
      have hcy : capClock (Vd.liftR γ) y ≤ r' := (ENNReal.ofReal_le_ofReal_iff hr').1 hT
      obtain ⟨x, hx0, hcx, hρx⟩ := Vk.exists_relTime hTZ h1 h2 hTZ'
      refine ⟨x, ⟨hx0, ?_⟩, ?_⟩
      · by_contra hlt
        rw [not_le] at hlt
        have := hρ.strictMonoOn_capClock hinv0 hx0 hlt
        rw [hinv, ← hcx] at this
        linarith
      · rw [hρx]; show γ (y : ℝ).toNNReal = γ (T - tL); rw [Real.toNNReal_coe]

/-- **Meeting a closed set, decided by rational readings.** -/
theorem nonempty_inter_image_iff {f : ℝ≥0 → ℂ} {A : ℝ≥0 → ℝ≥0∞} {R : ℚ≥0 → ℂ} {Q : Set ℂ} (hQ : IsClosed Q)
    (hQne : Q.Nonempty) (hAc : Continuous A) (hAm : Monotone A) {t : ℝ≥0} {r' : ℝ}
    (hrt : ENNReal.ofReal r' < A t) (hZ : ∀ T : ℝ≥0, A T < A t → (T : ℝ≥0∞) < Z)
    (hfc : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Z → ContinuousAt f T)
    (hR : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < Z → R q = f q) :
    (Q ∩ f '' {T | A T ≤ ENNReal.ofReal r'}).Nonempty ↔
      ∀ m : ℕ, ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧ A q ≤ ENNReal.ofReal (r' + 1 / ((m : ℝ) + 1)) ∧
        infDist (R q) Q < 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨z, hzQ, T, hT, rfl⟩ m
    simp only [mem_ofPred_eq] at hT
    have hTt : A T < A t := hT.trans_lt hrt
    have hTZ := hZ T hTt
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 (hfc T hTZ) _ hm
    obtain ⟨q, hqT, hqd⟩ := Vi.exists_nnrat_le_near T hδ
    have hqZ : (((q : ℝ≥0) : ℝ≥0∞)) < Z := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hqT) hTZ
    refine ⟨q, ?_, ?_, ?_⟩
    · by_contra hc
      rw [not_le] at hc
      exact absurd (hAm (hc.le.trans hqT)) (not_le.2 hTt)
    · exact (hAm hqT).trans (hT.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    · rw [hR q hqZ]
      exact lt_of_le_of_lt (infDist_le_dist_of_mem hzQ) (hδf hqd)
  · intro h
    choose q hqt hqA hqd using h
    -- a convergent subsequence in `[0, t]`
    have hmem : ∀ m, ((q m : ℝ≥0)) ∈ Icc (0 : ℝ≥0) t := fun m => ⟨zero_le, hqt m⟩
    obtain ⟨T, hTI, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    -- the clock at the limit
    have hAT : A T ≤ ENNReal.ofReal r' := by
      have h1 : Tendsto (fun j => A (q (φ j))) atTop (𝓝 (A T)) := (hAc.tendsto T).comp hlim
      have h2 : Tendsto (fun j => ENNReal.ofReal (r' + 1 / ((φ j : ℝ) + 1))) atTop (𝓝 (ENNReal.ofReal r')) := by
        have h3 : Tendsto (fun j => r' + 1 / ((φ j : ℝ) + 1)) atTop (𝓝 (r' + 0)) :=
          tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
        rw [add_zero] at h3
        exact ENNReal.tendsto_ofReal h3
      exact le_of_tendsto_of_tendsto' h1 h2 fun j => hqA (φ j)
    have hTt : A T < A t := hAT.trans_lt hrt
    have hTZ := hZ T hTt
    refine ⟨f T, ?_, T, hAT, rfl⟩
    -- the readings tend to `f T`, and their distance to `Q` to `0`
    have hev : ∀ᶠ j in atTop, R (q (φ j)) = f (q (φ j)) := by
      have h1 : Tendsto (fun j => A (q (φ j))) atTop (𝓝 (A T)) := (hAc.tendsto T).comp hlim
      filter_upwards [h1.eventually (gt_mem_nhds hTt)] with j hj
      exact hR _ (hZ _ hj)
    have hf : Tendsto (fun j => R (q (φ j))) atTop (𝓝 (f T)) :=
      ((hfc T hTZ).tendsto.comp hlim).congr' (hev.mono fun j hj => hj.symm)
    have hd : Tendsto (fun j => infDist (R (q (φ j))) Q) atTop (𝓝 (infDist (f T) Q)) :=
      ((continuous_infDist_pt Q).tendsto _).comp hf
    have hd0 : infDist (f T) Q ≤ 0 := by
      refine le_of_tendsto_of_tendsto hd
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop) (Eventually.of_forall fun j => ?_)
      exact (hqd (φ j)).le
    rw [← hQ.closure_eq]
    exact (mem_closure_iff_infDist_zero hQne).2 (le_antisymm hd0 infDist_nonneg)

end Det

end InteractingSLE.Theorem14.SB.Vm
