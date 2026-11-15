/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12RemFar
import InteractingSLE.Spec.Sec5.CrossCondStagedK2Path

/-!
# Lemma G12 at a right mark, for a trace up to the mark's first contact

Packet PROVE-STAGED9 (ruling R78). Lemma G12 (supplement §7.9, p. 504; `Supp7.G12.ae_trace_ne_right_of_near`) is
proved for a generating trace through the whole lifetime. Its probability is trace-free (the observable bound
`Supp7.G12.ae_abs_phi_lt` on the localization); the trace enters only in the final pathwise step
(`Supp7.G12.trace_ne_of_phi_bound`). Here the pathwise step is run with a trace on `[0, T]` only, `T < ζ` the first
contact of the mark: the path restricted to `[0, T)` is an integrated path with the contact weights
(`StagedK2.isIntegratedSLEPath_contact`), whose force path carries the landed deterministic trace lemmas
(`Supp7.G12.trace_ne_of_budget_lt`), and the budget bound comes from the original path.

* `exists_budget_bound_of_phi_bound`: the budget bound of `trace_ne_of_phi_bound`'s proof, as a lemma (proof copied
  from `Supp7.G12.trace_ne_of_phi_bound`, unchanged);
* `exists_farAt_le_of_contact`: with no right mark beyond `y`, the far terms are bounded on the life of the mark by
  continuity on `[0, T]`;
* **`trace_ne_of_phi_bound_contact`**: the pathwise step on `[0, T]`;
* **`ae_trace_ne_right_contact`**: Lemma G12 at the outermost right mark (no mark beyond it, a mark strictly before
  it, `S' > −2`, `S_y > κ/2 − 4`), almost surely for every first contact `T < ζ` and every trace on `[0, T]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedK2

open Supp7 Supp7.G12
open G11 (IsMarkLife)
open Supp8.GB5 (IsGBGood)

section Path

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {i₀ j₀ : Fin nR}

/-- **The budget bound of Lemma G12's pathwise step** (the core of `Supp7.G12.trace_ne_of_phi_bound`, proof copied):
if the life of the mark is bounded by `t`, the far terms are bounded above on it, and the observable satisfies
`|Φ − Φ₀| < a + αT` there, the pair budget is bounded on the whole life of the mark. -/
theorem exists_budget_bound_of_phi_bound (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hord : IsOrderedForceWord xL xR) (hi₀ : ∀ k, i₀ ≤ k) (hx : xR i₀ < xR j₀) (hS' : -2 < nearW xR ρR j₀)
    (hS : κ / 2 - 4 < nearW xR ρR j₀ + rhoY xR ρR j₀) {t : ℝ≥0}
    (hlt : ∀ s, IsMarkLife w (vR j₀) ζ s → s < t) {Fb : ℝ}
    (hFbs : ∀ s, IsMarkLife w (vR j₀) ζ s → farAt xR ρL ρR j₀ vL vR s ≤ Fb) {Φ₀ a : ℝ}
    (hΦ : ∀ s, IsMarkLife w (vR j₀) ζ s →
      |phiAt κ xL xR ρL ρR j₀ w vL vR b s - Φ₀| < a + escRate κ xR ρR j₀ * clockAt w (vR j₀) s) :
    ∃ C, ∀ s, IsMarkLife w (vR j₀) ζ s → ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C := by
  have hF := hp.isForcePath
  have hx0 : 0 ≤ xR i₀ := hord.2.2.2 i₀
  set α := escRate κ xR ρR j₀ with hαdef
  have hα : 0 < α := by rw [hαdef, escRate]; linarith
  set A := 1 + nearW xR ρR j₀ / 2 with hAdef
  set c' := chargeY κ xR ρR j₀ with hc'
  have h2A : 2 * A - c' = 2 * α := by rw [hAdef, hc', hαdef, chargeY, escRate]; ring
  set K₀ := A * Real.log (xR j₀ - xR i₀) + thetaMax xR ρR i₀ j₀ + Fb with hK₀
  have hesc : ∀ s, IsMarkLife w (vR j₀) ζ s →
      α * clockAt w (vR j₀) s - (K₀ + a - Φ₀) ≤ Real.log (vR j₀ s - w s) - Real.log (vR j₀ s - vR i₀ s) := by
    intro s hs
    have h1 := log_sub_log_ge (b := b) hp hord hi₀ hx hS' hs (hFbs s hs)
    have h2 := hΦ s hs
    rw [abs_lt] at h2
    rw [← hAdef, ← hc', h2A] at h1
    linarith [h2.1]
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, IsMarkLife w (vR j₀) ζ s →
      ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C := by
    by_cases hunb : ∀ T : ℝ, ∃ s, IsMarkLife w (vR j₀) ζ s ∧ T < clockAt w (vR j₀) s
    · exact budget_bound_of_escape hF hi₀ hx hα hesc hunb
    push Not at hunb
    obtain ⟨Tm, hTm⟩ := hunb
    have hTm0 : ∀ s, IsMarkLife w (vR j₀) ζ s → 0 ≤ clockAt w (vR j₀) s := fun s _ => clockAt_nonneg s
    set K₂ := -Φ₀ + a + α * |Tm| + |c'| * |Tm| + thetaMax xR ρR i₀ j₀ + Fb with hK₂
    -- `log u ≥ −(S'/2) log e − K₂`
    have hlogu : ∀ s, IsMarkLife w (vR j₀) ζ s →
        -(nearW xR ρR j₀ / 2) * Real.log (vR j₀ s - vR i₀ s) - K₂ ≤ Real.log (vR j₀ s - w s) := by
      intro s hs
      have hnear : ∀ k ∈ nearR xR j₀, 0 < vR j₀ s - vR k s := fun k hk =>
        (near_bounds hF hord hi₀ hx (by simpa [nearR] using hk) hs).1
      obtain ⟨T₂, hsT₂, hT₂, P0⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
      have he := P0.span_pos s ⟨s.coe_nonneg, le_rfl⟩
      simp only [Real.toNNReal_coe] at he
      have hid := log_sub_log_eq (b := b) hp hs.1 hnear he
      have hΘ := thetaAt_le hF hord hi₀ hx hs
      have hFb' := hFbs s hs
      have h2 := hΦ s hs
      rw [abs_lt] at h2
      have hT0 := hTm0 s hs
      have hTs := hTm s hs
      have hc1 : c' * clockAt w (vR j₀) s ≤ |c'| * |Tm| := by
        calc c' * clockAt w (vR j₀) s ≤ |c'| * clockAt w (vR j₀) s :=
              mul_le_mul_of_nonneg_right (le_abs_self c') hT0
          _ ≤ |c'| * |Tm| := mul_le_mul_of_nonneg_left (hTs.trans (le_abs_self Tm)) (abs_nonneg c')
      have hc2 : α * clockAt w (vR j₀) s ≤ α * |Tm| :=
        mul_le_mul_of_nonneg_left (hTs.trans (le_abs_self Tm)) hα.le
      rw [← hAdef, ← hc'] at hid
      rw [hAdef] at hid
      nlinarith [h2.1]
    have hℓ : ∀ s, IsMarkLife w (vR j₀) ζ s → Real.log (vR j₀ s - vR i₀ s) ≤ Real.log (xR j₀ - xR i₀) := by
      intro s hs
      obtain ⟨T₂, hsT₂, hT₂, P0⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
      have he := P0.span_pos s ⟨s.coe_nonneg, le_rfl⟩
      have hle := P0.span_le s ⟨s.coe_nonneg, le_rfl⟩
      simp only [Real.toNNReal_coe] at he hle
      exact Real.log_le_log he hle
    rcases le_or_gt 0 (nearW xR ρR j₀) with hS0 | hS0
    · -- `S' ≥ 0`: the gap stays above `u₀`
      set u₀ := Real.exp (-(nearW xR ρR j₀ / 2) * Real.log (xR j₀ - xR i₀) - K₂) with hu₀
      refine budget_bound_of_small (u₀ := u₀) hF hi₀ hx0 hx hlt hTm (Real.exp_pos _) fun s hs hsmall => ?_
      exfalso
      have hu : 0 < vR j₀ s - w s := sub_pos.2 (hs.2 s le_rfl)
      have h1 := hlogu s hs
      have h2 := hℓ s hs
      have h3 : -(nearW xR ρR j₀ / 2) * Real.log (xR j₀ - xR i₀) ≤
          -(nearW xR ρR j₀ / 2) * Real.log (vR j₀ s - vR i₀ s) :=
        mul_le_mul_of_nonpos_left h2 (by linarith)
      have h4 : Real.log u₀ ≤ Real.log (vR j₀ s - w s) := by rw [hu₀, Real.log_exp]; linarith
      have h5 := Real.log_lt_log hu hsmall
      linarith
    · -- `−2 < S' < 0`: a small gap forces `X ≥ log 2`
      set q := -(nearW xR ρR j₀ / 2) with hq
      have hq0 : 0 < q := by rw [hq]; linarith
      have hq1 : q < 1 := by rw [hq]; linarith
      set m := (Real.log 2 + K₂ / q) / (1 / q - 1) with hm
      have hq' : 0 < 1 / q - 1 := by rw [sub_pos, lt_div_iff₀ hq0]; linarith
      refine budget_bound_of_small hF hi₀ hx0 hx hlt hTm (Real.exp_pos (-m)) fun s hs hsmall => ?_
      have hu : 0 < vR j₀ s - w s := sub_pos.2 (hs.2 s le_rfl)
      obtain ⟨T₂, hsT₂, hT₂, P0⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
      have he := P0.span_pos s ⟨s.coe_nonneg, le_rfl⟩
      simp only [Real.toNNReal_coe] at he
      have h1 := hlogu s hs
      have hlu : Real.log (vR j₀ s - w s) < -m := by
        have := Real.log_lt_log hu hsmall; rwa [Real.log_exp] at this
      -- `log e ≤ (log u + K₂)/q`
      have hle : Real.log (vR j₀ s - vR i₀ s) ≤ (Real.log (vR j₀ s - w s) + K₂) / q := by
        rw [le_div_iff₀ hq0]; linarith
      -- `X ≥ log 2`
      have hX : Real.log 2 ≤ Real.log (vR j₀ s - w s) - Real.log (vR j₀ s - vR i₀ s) := by
        have hmm : (1 / q - 1) * m = Real.log 2 + K₂ / q := by
          rw [hm, mul_comm]; exact div_mul_cancel₀ _ hq'.ne'
        have : Real.log (vR j₀ s - w s) - (Real.log (vR j₀ s - w s) + K₂) / q =
            (1 / q - 1) * (-Real.log (vR j₀ s - w s)) - K₂ / q := by field_simp; ring
        have h6 : (1 / q - 1) * m < (1 / q - 1) * (-Real.log (vR j₀ s - w s)) :=
          mul_lt_mul_of_pos_left (by linarith) hq'
        linarith
      have hratio : (vR j₀ s - vR i₀ s) / (vR j₀ s - w s) ≤ 1 / 2 := by
        rw [div_le_iff₀ hu]
        have := Real.exp_le_exp.2 hX
        rw [Real.exp_sub, Real.exp_log hu, Real.exp_log he, Real.exp_log two_pos, le_div_iff₀ he] at this
        linarith
      rw [div_le_iff₀ hu] at hratio
      linarith
  exact ⟨C, hC⟩

/-- With no right mark beyond `y = x_{j₀}`, the far terms `F = Σᵢ (ρ_{i,L}/2) log(V^{j₀} − V^{i,L})` are bounded above
on the life of the mark when the life ends before a time `T < ζ`: the gaps are at least `x_{j₀} > 0` and continuous on
the compact `[0, T]`. -/
theorem exists_farAt_le_of_contact (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hord : IsOrderedForceWord xL xR) (hy : 0 < xR j₀) (hfar : ∀ k, xR k ≤ xR j₀) {T : ℝ≥0}
    (hTζ : (T : ℝ≥0∞) < ζ) (hlt : ∀ s, IsMarkLife w (vR j₀) ζ s → s < T) :
    ∃ Fb, ∀ s, IsMarkLife w (vR j₀) ζ s → farAt xR ρL ρR j₀ vL vR s ≤ Fb := by
  have hF := hp.isForcePath
  have hfarR : farR xR j₀ = ∅ := by
    ext k
    simp only [farR, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
    exact hfar k
  have hsub : Icc (0 : ℝ≥0) T ⊆ {t | (t : ℝ≥0∞) < ζ} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans_lt hTζ
  have hpos : ∀ i, ∀ s ∈ Icc (0 : ℝ≥0) T, 0 < vR j₀ s - vL i s := fun i s hs => by
    have h1 := hF.xR_le_vR (hsub hs) j₀
    have h2 := hF.vL_le_xL (hsub hs) i
    have h3 : xL i ≤ 0 := hord.2.1 i
    linarith
  have hc : ContinuousOn (fun s => farAt xR ρL ρR j₀ vL vR s) (Icc 0 T) := by
    simp only [farAt, hfarR, Finset.sum_empty, add_zero]
    refine continuousOn_finsetSum _ fun i _ => ContinuousOn.mul continuousOn_const ?_
    exact ContinuousOn.log (((hF.continuousOn_vR j₀).mono hsub).sub ((hF.continuousOn_vL i).mono hsub))
      fun s hs => (hpos i s hs).ne'
  obtain ⟨s₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le) hc
  exact ⟨_, fun s hs => hmax ⟨zero_le, (hlt s hs).le⟩⟩

/-- **Lemma G12's pathwise step for a trace up to the mark's first contact.** Let `T < ζ` be the first time the right
mark `j₀` (no right mark beyond it, a mark `i₀ ≤` every mark strictly before it) meets the driver, and `η` a generating
trace on `[0, T]` only. If the observable satisfies `|Φ − Φ₀| < a + αT` on the life of the mark, `η` does not visit
`x_{j₀}` on `[0, T]`. -/
theorem trace_ne_of_phi_bound_contact (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 < κ)
    (hord : IsOrderedForceWord xL xR) (hi₀ : ∀ k, i₀ ≤ k) (hx : xR i₀ < xR j₀) (hfar : ∀ k, xR k ≤ xR j₀)
    (hS' : -2 < nearW xR ρR j₀) (hS : κ / 2 - 4 < nearW xR ρR j₀ + rhoY xR ρR j₀)
    {T : ℝ≥0} (hT0 : 0 < T) (hTζ : (T : ℝ≥0∞) < ζ) (hbefore : ∀ t < T, w t < vR j₀ t)
    (hmeet : vR j₀ T = w T) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η) {Φ₀ a : ℝ}
    (hΦ : ∀ s, IsMarkLife w (vR j₀) ζ s →
      |phiAt κ xL xR ρL ρR j₀ w vL vR b s - Φ₀| < a + escRate κ xR ρR j₀ * clockAt w (vR j₀) s) :
    ∀ t : ℝ≥0, t ≤ T → η t ≠ xR j₀ := by
  have hx0 : 0 ≤ xR i₀ := hord.2.2.2 i₀
  have hlt : ∀ s, IsMarkLife w (vR j₀) ζ s → s < T := fun s hs => by
    by_contra h
    push Not at h
    have := hs.2 T h
    rw [hmeet] at this
    exact lt_irrefl _ this
  obtain ⟨Fb, hFb⟩ := exists_farAt_le_of_contact hp hord (lt_of_le_of_lt hx0 hx) hfar hTζ hlt
  obtain ⟨C, hC⟩ := exists_budget_bound_of_phi_bound hp hord hi₀ hx hS' hS hlt hFb hΦ
  have hF' := (isIntegratedSLEPath_contact hp hκ hT0 hTζ hbefore hmeet).isForcePath
  intro t ht
  exact trace_ne_of_budget_lt hF' (hi₀ j₀) hx0 hx hη (ENNReal.coe_le_coe.2 ht)
    fun s hs _ => hC s ⟨hs.1.trans hTζ, hs.2⟩

end Path

section Evolution

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {i₀ j₀ : Fin nR}

/-- **Lemma G12 at the outermost right mark, for traces up to its first contact** (supplement §7.9, p. 504; the
probability of `Supp7.G12.ae_trace_ne_right_of_near`, the pathwise step `trace_ne_of_phi_bound_contact`). For an
integrated evolution of an ordered force word, a right mark `j₀` with no mark beyond it and a mark `i₀` (the first)
strictly before it, `S' = Σ_{x_k < y} ρ_k > −2` and `S_y = Σ_{x_k ≤ y} ρ_k > κ/2 − 4`: almost surely, for every first
contact time `0 < T < ζ` of the mark and every generating trace `η` on `[0, T]`, `η` does not visit `x_{j₀}` on
`[0, T]`. -/
theorem ae_trace_ne_right_contact [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hi₀ : ∀ k, i₀ ≤ k)
    (hx : xR i₀ < xR j₀) (hfar : ∀ k, xR k ≤ xR j₀)
    (hS' : -2 < ∑ k ∈ univ.filter (fun k => xR k < xR j₀), ρR k)
    (hS : κ / 2 - 4 < ∑ k ∈ univ.filter (fun k => xR k ≤ xR j₀), ρR k) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) < ζ ω → (∀ t < T, W t ω < VR j₀ t ω) → VR j₀ T ω = W T ω →
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η → ∀ t : ℝ≥0, t ≤ T → η t ≠ xR j₀ := by
  have hx0 : 0 ≤ xR i₀ := hord.2.2.2 i₀
  have hy : 0 < xR j₀ := lt_of_le_of_lt hx0 hx
  have hxL : ∀ i, xL i ≤ 0 := hord.2.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- the lifetime vanishes: no contact time before it
    filter_upwards [hE.2.2.2.2] with ω hp T _ hTζ
    exfalso
    have hζ : ζ ω = 0 := by
      by_contra hne
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
      have := hp.isForcePath.not_threshold h0
      have hw : W 0 ω = 0 := hp.isForcePath.w_zero
      have hL : (fun i => VL i 0 ω) = xL := funext hp.isForcePath.vL_zero
      have hR : (fun i => VR i 0 ω) = xR := funext hp.isForcePath.vR_zero
      simp only [hw, hL, hR] at this
      exact this hseed
    rw [hζ] at hTζ
    exact ENNReal.not_lt_zero hTζ
  obtain ⟨Tn, hTann, hTn⟩ := Coupling.exists_isAnnouncingSeq_le hE hκ hseed
  obtain ⟨hT, hTm, hTζ, hTcov⟩ := hTann
  have hae : ∀ᵐ ω ∂P, IsGBGood κ xL xR ρL ρR W VL VR B ζ Tn ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, ae_all_iff.2 hTζ, hTcov]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨G, hGm, hGc, hgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ Tn ω := by
    refine ⟨(toMeasurable P {ω | ¬ IsGBGood κ xL xR ρL ρR W VL VR B ζ Tn ω})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hα : 0 < escRate κ xR ρR j₀ := by
    rw [escRate, ← sum_le_eq_nearW_add]; linarith
  have hbound := ae_abs_phi_lt (j₀ := j₀) hE hGm hGc hgood hT hTm hTn hy hxL hκ hα
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  filter_upwards [hbound, hGae] with ω hb hωG
  obtain ⟨a, ha⟩ := hb hωG
  have hω := hgood ω hωG
  have hS2 : κ / 2 - 4 < nearW xR ρR j₀ + rhoY xR ρR j₀ := by rw [← sum_le_eq_nearW_add]; exact hS
  intro T hT0 hTζ' hbefore hmeet η hη
  refine trace_ne_of_phi_bound_contact (b := fun t => B t ω) hω.1 hκ hord hi₀ hx hfar
    (by simpa [nearW, nearR] using hS') hS2 hT0 hTζ' hbefore hmeet hη (Φ₀ := phi0 κ xL xR ρL ρR j₀) (a := a)
    fun s hs => ?_
  obtain ⟨n, hn⟩ := exists_le_locG hord hi₀ hx hTm hgood hωG hs
  have h := ha n s hn
  simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at h
  exact h

end Evolution

end InteractingSLE.Sec5.CrossCond.StagedK2
