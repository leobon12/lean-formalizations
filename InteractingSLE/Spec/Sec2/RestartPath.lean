/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Restarting a solution path at a time before its lifetime

Packet PROVE-RESTART. The pathwise content of the restart: if `(w, v^{i,q}, b)` satisfies the frozen
`IsIntegratedSLEPath` with lifetime `ζ` and `σ < ζ`, then the shifted path seen from the driver at `σ`,

  `w'_t = w_{σ+t} − w_σ`, `v'^{i,q}_t = v^{i,q}_{σ+t} − w_σ`, `b'_t = b_{σ+t} − b_σ`,

satisfies `IsIntegratedSLEPath` for the force word with positions `x' = v_σ − w_σ` and the same weights,
with lifetime `ζ − σ` (`IsIntegratedSLEPath.restart`). Coincident marks need no special treatment: the
frozen definition allows several marks at one position (the threshold condition sums the weights of the
marks at the driver), so the shifted word is used with its marks as they are.

* `integral_shift`, `intervalIntegrable_shift`: time shifts of the integrals `∫₀ᵗ G(s) ds` of a path;
* `ForceWord.thresholdCondition_sub_iff`: the threshold condition is translation invariant;
* `IsIntegratedSLEPath.restart`: the restart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Restart

/-! ### Time shifts of integrals -/

theorem toNNReal_add_of_nonneg (σ : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    ((σ : ℝ) + s).toNNReal = σ + s.toNNReal := by
  rw [Real.toNNReal_add σ.coe_nonneg hs, Real.toNNReal_coe]

theorem coe_lt_sub_iff {ζ : ℝ≥0∞} (σ t : ℝ≥0) :
    (t : ℝ≥0∞) < ζ - σ ↔ ((σ + t : ℝ≥0) : ℝ≥0∞) < ζ := by
  rw [lt_tsub_iff_left, ENNReal.coe_add]

/-- On `[0, t]` the shifted integrand `G(σ + s)` agrees with `G((σ + s)⁺)`. -/
theorem eqOn_shift (G : ℝ≥0 → ℝ) (σ t : ℝ≥0) :
    EqOn (fun s : ℝ => G ((σ : ℝ) + s).toNNReal) (fun s : ℝ => G (σ + s.toNNReal))
      (uIcc (0 : ℝ) t) := by
  intro s hs
  rw [uIcc_of_le t.coe_nonneg] at hs
  simp only [toNNReal_add_of_nonneg σ hs.1]

theorem intervalIntegrable_mono_start {G : ℝ≥0 → ℝ} {σ t : ℝ≥0}
    (hG : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 ((σ + t : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume σ ((σ + t : ℝ≥0) : ℝ) := by
  refine hG.mono_set ?_
  rw [uIcc_of_le (by exact_mod_cast le_self_add), uIcc_of_le (σ + t).coe_nonneg]
  exact Icc_subset_Icc σ.coe_nonneg le_rfl

theorem intervalIntegrable_start {G : ℝ≥0 → ℝ} {σ t : ℝ≥0}
    (hG : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 ((σ + t : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 σ := by
  refine hG.mono_set ?_
  rw [uIcc_of_le σ.coe_nonneg, uIcc_of_le (σ + t).coe_nonneg]
  exact Icc_subset_Icc le_rfl (by exact_mod_cast le_self_add)

/-- Interval integrability of the shifted integrand on `[0, t]`. -/
theorem intervalIntegrable_shift {G : ℝ≥0 → ℝ} {σ t : ℝ≥0}
    (hG : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 ((σ + t : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => G (σ + s.toNNReal)) volume 0 t := by
  have h2 := (intervalIntegrable_mono_start hG).comp_add_left (σ : ℝ)
  have e1 : (σ : ℝ) - σ = 0 := sub_self _
  have e2 : ((σ + t : ℝ≥0) : ℝ) - σ = t := by push_cast; ring
  rw [e1, e2] at h2
  exact h2.congr_uIoo fun s hs => eqOn_shift G σ t (uIoo_subset_uIcc_self hs)

/-- The integral of the shifted integrand over `[0, t]` is the increment of the integral between `σ` and
`σ + t`. -/
theorem integral_shift {G : ℝ≥0 → ℝ} {σ t : ℝ≥0}
    (hG : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 ((σ + t : ℝ≥0) : ℝ)) :
    ∫ s in (0 : ℝ)..t, G (σ + s.toNNReal) =
      (∫ s in (0 : ℝ)..((σ + t : ℝ≥0) : ℝ), G s.toNNReal) - ∫ s in (0 : ℝ)..σ, G s.toNNReal := by
  rw [← intervalIntegral.integral_congr (eqOn_shift G σ t),
    intervalIntegral.integral_comp_add_left (fun s : ℝ => G s.toNNReal) (σ : ℝ), add_zero,
    show (σ : ℝ) + t = ((σ + t : ℝ≥0) : ℝ) by push_cast; ring]
  rw [eq_sub_iff_add_eq, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_start hG)
      (intervalIntegrable_mono_start hG)]

/-! ### Translation invariance of the threshold condition -/

theorem _root_.InteractingSLE.ForceWord.thresholdCondition_sub_iff {nL nR : ℕ} (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (w c : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR (w - c) (fun i => vL i - c) (fun j => vR j - c) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  simp only [sub_left_inj]

/-! ### The restart -/

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- Integrability of `c / (w − v)` on `[0, t]` from that of the reciprocal gap. -/
theorem intervalIntegrable_div_gap {f g : ℝ≥0 → ℝ} {t : ℝ} (c : ℝ)
    (h : IntervalIntegrable (fun s : ℝ => (f s.toNNReal - g s.toNNReal)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => c / (f s.toNNReal - g s.toNNReal)) volume 0 t := by
  simpa only [div_eq_mul_inv] using h.const_mul c

theorem intervalIntegrable_two_div_gap {f g : ℝ≥0 → ℝ} {t : ℝ}
    (h : IntervalIntegrable (fun s : ℝ => (f s.toNNReal - g s.toNNReal)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => 2 / (g s.toNNReal - f s.toNNReal)) volume 0 t := by
  simpa only [two_div_sub_eq] using h.const_mul (-2)

/-- **The restart of a solution path at a time before its lifetime.** If `(w, v, b)` satisfies
`IsIntegratedSLEPath` with lifetime `ζ` and `σ < ζ`, then the path restarted at `σ` and seen from the
driver (`w_{σ+·} − w_σ`, `v_{σ+·} − w_σ`, `b_{σ+·} − b_σ`) satisfies `IsIntegratedSLEPath` for the force
word with positions `v_σ − w_σ`, the same weights, and lifetime `ζ − σ`. -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.restart
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    IsIntegratedSLEPath a (fun i => vL i σ - w σ) (fun j => vR j σ - w σ) ρL ρR
      (fun t => w (σ + t) - w σ) (fun i t => vL i (σ + t) - w σ) (fun j t => vR j (σ + t) - w σ)
      (fun t => b (σ + t) - b σ) (ζ - σ) := by
  have hp := h.isForcePath
  have hd := h.driverEq
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ - σ → ((σ + t : ℝ≥0) : ℝ≥0∞) < ζ := fun ht =>
    (coe_lt_sub_iff σ _).1 ht
  -- continuity of a shifted path on `{t < ζ − σ}`
  have hcont : ∀ {f : ℝ≥0 → ℝ} (c : ℝ), ContinuousOn f {t | (t : ℝ≥0∞) < ζ} →
      ContinuousOn (fun t => f (σ + t) - c) {t | (t : ℝ≥0∞) < ζ - σ} := by
    intro f c hf
    refine ContinuousOn.sub ?_ continuousOn_const
    exact hf.comp (continuous_const.add continuous_id).continuousOn fun t ht => hlt ht
  -- the gaps of the shifted path are those of the original path
  have gapL : ∀ (i : Fin nL) (s : ℝ),
      (w (σ + s.toNNReal) - w σ) - (vL i (σ + s.toNNReal) - w σ) =
        w (σ + s.toNNReal) - vL i (σ + s.toNNReal) := fun i s => sub_sub_sub_cancel_right _ _ _
  have gapR : ∀ (j : Fin nR) (s : ℝ),
      (w (σ + s.toNNReal) - w σ) - (vR j (σ + s.toNNReal) - w σ) =
        w (σ + s.toNNReal) - vR j (σ + s.toNNReal) := fun j s => sub_sub_sub_cancel_right _ _ _
  have gapL' : ∀ (i : Fin nL) (s : ℝ),
      (vL i (σ + s.toNNReal) - w σ) - (w (σ + s.toNNReal) - w σ) =
        vL i (σ + s.toNNReal) - w (σ + s.toNNReal) := fun i s => sub_sub_sub_cancel_right _ _ _
  have gapR' : ∀ (j : Fin nR) (s : ℝ),
      (vR j (σ + s.toNNReal) - w σ) - (w (σ + s.toNNReal) - w σ) =
        vR j (σ + s.toNNReal) - w (σ + s.toNNReal) := fun j s => sub_sub_sub_cancel_right _ _ _
  refine IsIntegratedSLEPath.iff_isForcePath_and_driverEq.2 ⟨?_, ?_⟩
  · refine
      { w_zero := by simp
        vL_zero := fun i => by simp
        vR_zero := fun j => by simp
        continuousOn_w := hcont _ hp.continuousOn_w
        continuousOn_vL := fun i => hcont _ (hp.continuousOn_vL i)
        continuousOn_vR := fun j => hcont _ (hp.continuousOn_vR j)
        antitone_vL := fun ht _ _ hij => sub_le_sub_right (hp.antitone_vL (hlt ht) hij) _
        vL_le_w := fun ht i => sub_le_sub_right (hp.vL_le_w (hlt ht) i) _
        w_le_vR := fun ht j => sub_le_sub_right (hp.w_le_vR (hlt ht) j) _
        monotone_vR := fun ht _ _ hij => sub_le_sub_right (hp.monotone_vR (hlt ht) hij) _
        integrable_gapL := fun {t} ht i => by
          simp only [gapL]
          exact intervalIntegrable_shift (G := fun u => (w u - vL i u)⁻¹)
            (hp.integrable_gapL (hlt ht) i)
        integrable_gapR := fun {t} ht j => by
          simp only [gapR]
          exact intervalIntegrable_shift (G := fun u => (w u - vR j u)⁻¹)
            (hp.integrable_gapR (hlt ht) j)
        vL_eq := fun {t} ht i => by
          simp only [gapL']
          rw [integral_shift (G := fun u => 2 / (vL i u - w u))
            (intervalIntegrable_two_div_gap (hp.integrable_gapL (hlt ht) i)),
            hp.vL_eq (hlt ht) i, hp.vL_eq hσ i]
          ring
        vR_eq := fun {t} ht j => by
          simp only [gapR']
          rw [integral_shift (G := fun u => 2 / (vR j u - w u))
            (intervalIntegrable_two_div_gap (hp.integrable_gapR (hlt ht) j)),
            hp.vR_eq (hlt ht) j, hp.vR_eq hσ j]
          ring
        volume_collisionL := fun i => ?_
        volume_collisionR := fun j => ?_
        not_threshold := fun {t} ht => by
          rw [ForceWord.thresholdCondition_sub_iff]
          exact hp.not_threshold (hlt ht)
        threshold_of_eq_zero := fun h0 => absurd h0 (tsub_pos_of_lt hσ).ne'
        threshold_of_tendsto := fun {T} hT hTζ {w₀ vL₀ vR₀} hlim => ?_ }
    · refine measure_mono_null (t := (fun s : ℝ => (σ : ℝ) + s) ⁻¹'
        {u : ℝ | 0 ≤ u ∧ (u.toNNReal : ℝ≥0∞) < ζ ∧ w u.toNNReal = vL i u.toNNReal}) ?_ ?_
      · rintro s ⟨hs0, hsζ, hseq⟩
        simp only [mem_preimage, mem_ofPred_eq]
        rw [toNNReal_add_of_nonneg σ hs0]
        exact ⟨add_nonneg σ.coe_nonneg hs0, hlt hsζ, sub_left_inj.1 hseq⟩
      · rw [measure_preimage_add]
        exact hp.volume_collisionL i
    · refine measure_mono_null (t := (fun s : ℝ => (σ : ℝ) + s) ⁻¹'
        {u : ℝ | 0 ≤ u ∧ (u.toNNReal : ℝ≥0∞) < ζ ∧ w u.toNNReal = vR j u.toNNReal}) ?_ ?_
      · rintro s ⟨hs0, hsζ, hseq⟩
        simp only [mem_preimage, mem_ofPred_eq]
        rw [toNNReal_add_of_nonneg σ hs0]
        exact ⟨add_nonneg σ.coe_nonneg hs0, hlt hsζ, sub_left_inj.1 hseq⟩
      · rw [measure_preimage_add]
        exact hp.volume_collisionR j
    · -- the lifetime `ζ = σ + T`
      have hζtop : ζ ≠ ⊤ := fun h => by
        rw [h, ENNReal.top_sub_coe] at hTζ
        exact ENNReal.coe_ne_top hTζ
      have hζ : ((σ + T : ℝ≥0) : ℝ≥0∞) = ζ := by
        rw [ENNReal.coe_add, hTζ, add_tsub_cancel_of_le hσ.le]
      have hσT : σ < σ + T := lt_add_of_pos_right σ hT
      -- the time change `u ↦ u − σ`
      have hφ : Tendsto (fun u : ℝ≥0 => u - σ) (𝓝[<] (σ + T)) (𝓝[<] T) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have h : Tendsto (fun u : ℝ≥0 => u - σ) (𝓝 (σ + T)) (𝓝 (σ + T - σ)) :=
            tendsto_id.sub tendsto_const_nhds
          rw [add_tsub_cancel_left] at h
          exact h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds hσT)] with u hu hσu
          exact (tsub_lt_iff_left hσu.le).2 hu
      set c := w σ with hc
      set Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
        fun p => (p.1 + c, fun i => p.2.1 i + c, fun j => p.2.2 j + c) with hΦ
      have hΦc : Continuous Φ :=
        (continuous_fst.add continuous_const).prodMk
          ((continuous_pi fun i => ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).add
            continuous_const).prodMk
          (continuous_pi fun j => ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).add
            continuous_const))
      have hlim' := ((hΦc.tendsto _).comp hlim).comp hφ
      have hev : ∀ᶠ u in 𝓝[<] (σ + T), (Φ ∘ (fun t => (w (σ + t) - w σ, fun i => vL i (σ + t) - w σ,
          fun j => vR j (σ + t) - w σ)) ∘ fun u => u - σ) u = (w u, fun i => vL i u, fun j => vR j u) := by
        filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds hσT)] with u hσu
        have hu : σ + (u - σ) = u := add_tsub_cancel_of_le hσu.le
        simp only [Function.comp_apply, hΦ, hu, sub_add_cancel, hc]
      have hthr := hp.threshold_of_tendsto (T := σ + T) (lt_of_le_of_lt bot_le hσT) hζ
        (hlim'.congr' hev)
      have := (ForceWord.thresholdCondition_sub_iff ρL ρR (w₀ + c) c (fun i => vL₀ i + c)
        (fun j => vR₀ j + c)).2 hthr
      simpa only [add_sub_cancel_right] using this
  · intro t ht
    have hσt := hlt ht
    simp only [gapL, gapR]
    rw [Finset.sum_congr rfl fun i _ => integral_shift (G := fun u => ρL i / (w u - vL i u))
        (intervalIntegrable_div_gap (ρL i) (hp.integrable_gapL hσt i)),
      Finset.sum_congr rfl fun j _ => integral_shift (G := fun u => ρR j / (w u - vR j u))
        (intervalIntegrable_div_gap (ρR j) (hp.integrable_gapR hσt j)),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, hd _ hσt, hd _ hσ]
    ring

end Restart

end Sec2

end InteractingSLE
