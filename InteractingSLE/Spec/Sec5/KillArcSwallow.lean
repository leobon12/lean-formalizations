/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailLandingGap
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal

/-!
# Loewner swallowing at the first real contact of a killed arc

Packet PROVE-KILLARC (the named input `KilledArcSwallowStatement` of PROVE-STAGED-REP, rulings R48, R71 Part (3),
R78). Let `γ` be a killed arc on `P` (`WangWu.IsKilledArc`: a simple arc from `0` into `ℍ` on an initial interval of
`[0, ∞)` open at its right end) with finite terminal capacity `T = kLife γ P`, whose capacity-time trace converges at
`T⁻` to a real point `x₀ ≠ 0`. Then (deterministically):

* **the driver closes** (`exists_closed_driver_ne`): the killed capacity driver agrees on `[0, T)` with a continuous
  driver `U` on `ℝ` whose Loewner trace before `T` is the trace closed by `x₀` at `T`. This is PROVE-WW-B27's
  `SeedTail.exists_closed_driver` (stated there for `x₀ > 0`) for every nonzero real landing: the closed arc is simple
  and the driving criterion applies to it (`closedKTrace_spec_ne`, the landed proof with `x₀ ≠ 0` in place of
  `x₀ > 0`);
* **a geometric image whose gap stays open keeps every farther real point alive** (`rightImg_eq_of_not_alive`): for a
  continuous driver `U`, `U 0 = 0`, and marks `0 ≤ a < x`, if `U < R^a` on `(0, T)` and `x` is not alive at `T`, then
  `R^a_T = U_T`. (If the gap at `T` were positive, the gap of `x`, which dominates it, would stay bounded below on
  `[0, T]` and `x` would be alive at `T`: `MartChar.RealFlow.Alive.of_forall_le_cflow`.) This is PROVE-WW-B27's
  `SeedTail.rightImg_zero_eq_of_real_terminal` with the mark `0⁺` replaced by any mark `a ∈ [0, x)`;
* the landing point is not alive at `T`: the Loewner tip of `U` at `T` is `x₀` (`TraceClose`), and a real point alive at
  `T` has no tip on it (`Supp8.GB6.not_isForwardSol_of_tip`); on the left the reflected driver and
  `exists_isForwardSol_neg_iff`.

**`killedArc_swallow`**: the killed driver and every killed mark have left limits at `T` (the values of `U` and of the
geometric images of `U` at `T`), and the driver's limit equals the limit of the outermost mark on the side of `x₀`.

Deterministic; no probabilistic input; nothing here replaces a source theorem. R48: no result taking Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.KillArc

open WangWu WangWu.ImgWord WangWu.SeedTail MartChar.RealFlow Sec7.Lemma71C

variable {γ : ℝ → ℂ} {P : Set ℝ}

/-! ### The closed arc at a nonzero real landing -/

/-- **Closing at a nonzero real limit** preserves simplicity and supplies all compact-arc hypotheses of the driving
criterion (PROVE-WW-B27's `closedKTrace_spec`, which assumes `0 < x`; only `x ≠ 0` is used). -/
theorem closedKTrace_spec_ne (hγ : IsKilledArc γ P) {τ : ℝ≥0} (hτ0 : 0 < τ)
    (hτ : (τ : WithTop ℝ≥0) = kLife γ P) {x : ℝ} (hx : x ≠ 0)
    (hlim : Tendsto (kTrace γ P) (𝓝[<] τ) (𝓝 (x : ℂ))) :
    ContinuousOn (closedKTrace γ P τ x) (Icc 0 τ) ∧
      InjOn (closedKTrace γ P τ x) (Icc 0 τ) ∧ closedKTrace γ P τ x 0 = 0 ∧
      MapsTo (closedKTrace γ P τ x) (Ioo 0 τ) H ∧
      MapsTo (closedKTrace γ P τ x) (Icc 0 τ) Hbar := by
  have hτR : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ0
  have hlt : ∀ t ∈ Ico (0 : ℝ) τ, (t.toNNReal : WithTop ℝ≥0) < kLife γ P := by
    intro t ht
    rw [← hτ, WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe ht.1]
    exact ht.2
  have hzero : kTrace γ P 0 = 0 :=
    (hγ.isGeneratingTraceIcc_kTrace (by rw [← hτ]; exact_mod_cast hτ0)).1.1
  have hηzero : closedKTrace γ P τ x 0 = 0 := by
    rw [closedKTrace_of_lt hτR, Real.toNNReal_zero, hzero]
  have hηH : MapsTo (closedKTrace γ P τ x) (Ioo 0 τ) H := by
    intro t ht
    rw [closedKTrace_of_lt ht.2]
    exact hγ.kTrace_mem_H (Real.toNNReal_pos.2 ht.1) (hlt t ⟨ht.1.le, ht.2⟩)
  have hηne : ∀ t ∈ Ico (0 : ℝ) τ, closedKTrace γ P τ x t ≠ (x : ℂ) := by
    intro t ht
    rcases ht.1.eq_or_lt with he | hp
    · subst t
      rw [hηzero]
      exact_mod_cast hx.symm
    · intro he
      have him := hηH ⟨hp, ht.2⟩
      rw [he] at him
      exact lt_irrefl _ (show (0 : ℝ) < (x : ℂ).im from him)
  have hcont : ContinuousOn (closedKTrace γ P τ x) (Icc 0 τ) := by
    apply continuousOn_update_iff.2
    rw [Icc_sdiff_right]
    refine ⟨(continuousOn_kTrace_lt hγ hτ).comp continuous_real_toNNReal.continuousOn ?_, ?_⟩
    · intro t ht
      change t.toNNReal < τ
      rw [Real.toNNReal_lt_iff_lt_coe ht.1]
      exact ht.2
    · intro _
      have hto : Tendsto (fun t : ℝ => t.toNNReal) (𝓝[<] (τ : ℝ)) (𝓝[<] τ) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · simpa only [Real.toNNReal_coe] using
            (continuous_real_toNNReal.tendsto (τ : ℝ)).mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsLT hτR] with t ht
          exact (Real.toNNReal_lt_iff_lt_coe ht.1.le).2 ht.2
      exact (hlim.comp hto).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
  refine ⟨hcont, ?_, hηzero, hηH, ?_⟩
  · intro a ha b hb he
    rcases ha.2.lt_or_eq with hat | hat
    · rcases hb.2.lt_or_eq with hbt | hbt
      · have hab := hγ.kTrace_injOn (hlt a ⟨ha.1, hat⟩) (hlt b ⟨hb.1, hbt⟩)
          (by simpa only [closedKTrace_of_lt hat, closedKTrace_of_lt hbt] using he)
        have := congrArg (fun r : ℝ≥0 => (r : ℝ)) hab
        simpa only [Real.coe_toNNReal _ ha.1, Real.coe_toNNReal _ hb.1] using this
      · subst b
        exact False.elim (hηne a ⟨ha.1, hat⟩ (by simpa only [closedKTrace_end] using he))
    · subst a
      rcases hb.2.lt_or_eq with hbt | hbt
      · exact False.elim (hηne b ⟨hb.1, hbt⟩ (by simpa only [closedKTrace_end] using he.symm))
      · exact hbt.symm
  · intro t ht
    rcases ht.2.lt_or_eq with hlt | he
    · rcases ht.1.eq_or_lt with hz | hp
      · subst t
        rw [hηzero]
        exact (show (0 : ℝ) ≤ (0 : ℂ).im from le_refl _)
      · exact (show (0 : ℝ) < (closedKTrace γ P τ x t).im from hηH ⟨hp, hlt⟩).le
    · subst t
      rw [closedKTrace_end]
      exact (show (0 : ℝ) ≤ (x : ℂ).im from le_refl _)

/-- **The killed capacity driver closes at a nonzero real landing**: it agrees on `[0, τ)` with a continuous driver
whose Loewner trace before `τ` is the closed trace (PROVE-WW-B27's `exists_closed_driver` for `x ≠ 0`). -/
theorem exists_closed_driver_ne (hγ : IsKilledArc γ P) {τ : ℝ≥0} (hτ0 : 0 < τ)
    (hτ : (τ : WithTop ℝ≥0) = kLife γ P) {x : ℝ} (hx : x ≠ 0)
    (hlim : Tendsto (kTrace γ P) (𝓝[<] τ) (𝓝 (x : ℂ))) :
    ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ EqOn (kPath γ P) U (Ico 0 τ) ∧
      IsLoewnerTraceLT U τ (closedKTrace γ P τ x) := by
  obtain ⟨hc, hi, h0, hH, hHb⟩ := closedKTrace_spec_ne hγ hτ0 hτ hx hlim
  obtain ⟨U, hU, hU0, σ, -, -, -, hσ⟩ :=
    exists_driver_of_open_simple (NNReal.coe_pos.2 hτ0) hc hi h0 hH hHb
  have hσid : ∀ t ∈ Ico (0 : ℝ) τ, σ t = t := by
    intro t ht
    have he := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hU hU0 (hσ t ⟨ht.1, ht.2.le⟩).1
      (hσ t ⟨ht.1, ht.2.le⟩).2.1
    have he' := hcapSet_closedKTrace hγ hτ (x := x) ht.1 ht.2
    linarith only [he, he']
  have hLT : IsLoewnerTraceLT U τ (closedKTrace γ P τ x) := by
    refine ⟨h0, hc.mono Ico_subset_Icc_self, fun t ht0 htτ => ?_⟩
    simpa only [hσid t ⟨ht0, htτ⟩] using (hσ t ⟨ht0, htτ.le⟩).2.1
  refine ⟨U, hU, hU0, ?_, hLT⟩
  intro r hr
  obtain ⟨R, hrR, hRτ⟩ := exists_between hr.2
  have hR0 : 0 ≤ R := hr.1.trans hrR.le
  have hRL : (R.toNNReal : WithTop ℝ≥0) < kLife γ P := by
    rw [← hτ, WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hR0]
    exact hRτ
  obtain ⟨S, -, -, hRS, w, hw, hw0, hEq, -⟩ := hγ.exists_kPath_trace hRL
  rw [Real.coe_toNNReal _ hR0] at hRS
  have hew : EqOn w U (Icc 0 R) := Sec6.eqOn_of_fwdHull_eq hw hU hw0 hU0 hR0 fun t ht => by
    exact (LocalExt.fwdHull_congr_of_eqOn_of_lt ht.1 (ht.2.trans_lt hRS) hEq.symm).trans
      ((fwdHull_kPath_closedKTrace hγ hτ (x := x) ht.1 (ht.2.trans_lt hRτ)).trans
        (hLT.2.2 t ht.1 (ht.2.trans_lt hRτ)).symm)
  exact (hEq ⟨hr.1, hrR.le.trans hRS.le⟩).trans (hew ⟨hr.1, hrR.le⟩)

/-! ### A geometric image whose gap stays open keeps the farther real points alive -/

/-- **The gap of a mark closes when a farther real point dies.** For a continuous driver `U` with `U 0 = 0`, marks
`0 ≤ a < x` and a time `T > 0`: if the geometric image `R^a` stays strictly right of `U` on `(0, T)` and `x` is not
alive at `T`, then `R^a_T = U_T` (PROVE-WW-B27's `rightImg_zero_eq_of_real_terminal`, for any mark `a ∈ [0, x)`). -/
theorem rightImg_eq_of_not_alive {U : ℝ → ℝ} {T a x : ℝ} (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 < T)
    (ha : 0 ≤ a) (hax : a < x) (hsep : ∀ t ∈ Ioo 0 T, U t < rightImg U a t) (hx : ¬ Alive U x T) :
    rightImg U a T = U T := by
  by_contra hne
  have hx0 : 0 < x := ha.trans_lt hax
  have hpos : 0 < rightImg U a T - U T :=
    sub_pos.2 (lt_of_le_of_ne (le_rightImg hU a hT.le) (Ne.symm hne))
  have hgap : ∀ t ∈ Icc (0 : ℝ) T, 0 < rightImg U x t - U t := by
    intro t ht
    rcases ht.1.eq_or_lt with he | ht0
    · subst t
      rw [rightImg_zero hU hU0 hx0.le, hU0, sub_zero]
      exact hx0
    · have hmono := rightImg_mono_index hU ht.1 hax.le
      rcases ht.2.lt_or_eq with htt | he
      · exact lt_of_lt_of_le (sub_pos.2 (hsep t ⟨ht0, htt⟩)) (sub_le_sub_right hmono _)
      · subst t
        exact hpos.trans_le (sub_le_sub_right hmono _)
  have hgc : ContinuousOn (fun t => rightImg U x t - U t) (Icc 0 T) :=
    ((continuousOn_rightImg hU x).mono Icc_subset_Ici_self).sub hU.continuousOn
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le) hgc
  have hA0 : Alive U x 0 := alive_zero_iff.2 (by rw [hU0, sub_zero]; exact hx0)
  refine hx (hA0.of_forall_le_cflow hU le_rfl (hgap b hb) fun t ht hal => ?_)
  have h := hmin ht
  change rightImg U x b - U b ≤ rightImg U x t - U t at h
  rw [rightImg_eq_gImg hU ht.1 hal, gImg] at h
  linarith only [h]

/-! ### Swallowing at the first real contact -/

/-- **Loewner swallowing at the first real contact of a killed arc.** Let `γ` be a killed arc on `P` with finite
terminal capacity `T`, and marks `xL ≤ 0 ≤ xR`. If the killed trace converges at `T⁻` to a real point `x₀` strictly
beyond the last mark of one side, then the killed driver and every killed mark have left limits at `T`, and the
driver's limit is the limit of that last mark (the mark is swallowed at `T`). The limits are the values at `T` of the
closed driver `U` and of its geometric images. -/
theorem killedArc_swallow (hγ : IsKilledArc γ P) {n m : ℕ} (xL : Fin (n + 1) → ℝ) (xR : Fin (m + 1) → ℝ)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {T : ℝ≥0} {x₀ : ℝ} (hT : (T : WithTop ℝ≥0) = kLife γ P)
    (hx : x₀ < xL (Fin.last n) ∨ xR (Fin.last m) < x₀)
    (hlim : Tendsto (kTrace γ P) (𝓝[<] T) (𝓝 (x₀ : ℂ))) :
    ∃ (w₀ : ℝ) (vL₀ : Fin (n + 1) → ℝ) (vR₀ : Fin (m + 1) → ℝ), Tendsto (kW γ P) (𝓝[<] T) (𝓝 w₀) ∧
      (∀ i, Tendsto (kVL γ P xL i) (𝓝[<] T) (𝓝 (vL₀ i))) ∧ (∀ j, Tendsto (kVR γ P xR j) (𝓝[<] T) (𝓝 (vR₀ j))) ∧
      (x₀ < xL (Fin.last n) → w₀ = vL₀ (Fin.last n)) ∧ (xR (Fin.last m) < x₀ → w₀ = vR₀ (Fin.last m)) := by
  have hT0 : 0 < T := by
    have h := hγ.zero_lt_kLife
    rw [← hT] at h
    exact_mod_cast h
  have hTR : (0 : ℝ) < T := NNReal.coe_pos.2 hT0
  have hx0 : x₀ ≠ 0 := by
    rcases hx with h | h
    · exact (h.trans_le (hxL _)).ne
    · exact ((hxR _).trans_lt h).ne'
  obtain ⟨U, hU, hU0, hEq, hLT⟩ := exists_closed_driver_ne hγ hT0 hT hx0 hlim
  have hUn : Continuous (fun r => -U r) := hU.neg
  -- the tip of `U` at `T` is `x₀`, so `x₀` has no forward solution through `T`
  have hc := (closedKTrace_spec_ne hγ hT0 hT hx0 hlim).1
  have htip := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT hLT hU hU0 hTR hc
  rw [closedKTrace_end] at htip
  have hnosol : ∀ v, ¬ QuantumZipper.IsForwardSol U (x₀ : ℂ) T v := fun v hv =>
    Supp8.GB6.not_isForwardSol_of_tip hU hU0 hTR.le htip hv
  -- before `T` the killed objects are read on `U`
  have hltL : ∀ t : ℝ≥0, t < T → (t : WithTop ℝ≥0) < kLife γ P := fun t ht => by
    rw [← hT]
    exact_mod_cast ht
  have hkW : ∀ t : ℝ≥0, t < T → kW γ P t = U t := fun t ht => by
    rw [← kPath_coe]
    exact hEq ⟨t.coe_nonneg, ht⟩
  have hEqI : ∀ t : ℝ≥0, t < T → ∀ r ∈ Icc (0 : ℝ) t, kPath γ P r = U r := fun t ht r hr =>
    hEq ⟨hr.1, hr.2.trans_lt ht⟩
  have hkVR : ∀ j, ∀ t : ℝ≥0, t < T → kVR γ P xR j t = rightImg U (xR j) t := fun j t ht => by
    rw [kVR_of_lt xR j (hltL t ht), kVRr, kImg]
    exact Supp8.GB6.rightImg_congr hU t.coe_nonneg (hEqI t ht)
  have hkVL : ∀ i, ∀ t : ℝ≥0, t < T → kVL γ P xL i t = -rightImg (fun r => -U r) (-xL i) t :=
    fun i t ht => by
      rw [kVL_of_lt xL i (hltL t ht), kVLr, kImg]
      congr 1
      exact Supp8.GB6.rightImg_congr hUn t.coe_nonneg fun r hr => by simp only [hEqI t ht r hr]
  -- continuity in time
  have hcR : ∀ V : ℝ → ℝ, Continuous V → ∀ x : ℝ, Continuous (fun t : ℝ≥0 => rightImg V x t) :=
    fun V hV x => (continuousOn_rightImg hV x).comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg
  have hlimit : ∀ {f g : ℝ≥0 → ℝ}, Continuous g → (∀ t, t < T → f t = g t) →
      Tendsto f (𝓝[<] T) (𝓝 (g T)) := fun {f g} hg hfg =>
    ((hg.tendsto T).mono_left nhdsWithin_le_nhds).congr' (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hfg t ht).symm)
  refine ⟨U T, fun i => -rightImg (fun r => -U r) (-xL i) T, fun j => rightImg U (xR j) T,
    hlimit (hU.comp NNReal.continuous_coe) hkW, fun i => hlimit (hcR _ hUn _).neg (hkVL i),
    fun j => hlimit (hcR _ hU _) (hkVR j), fun hxl => ?_, fun hxr => ?_⟩
  · -- the left side, through the reflected driver
    have hsep : ∀ t ∈ Ioo (0 : ℝ) T,
        (fun r => -U r) t < rightImg (fun r => -U r) (-xL (Fin.last n)) t := by
      intro t ht
      have htT : t.toNNReal < T := (Real.toNNReal_lt_iff_lt_coe ht.1.le).2 ht.2
      have hp := hγ.kVLr_lt_kW hxL (Real.toNNReal_pos.2 ht.1) (hltL _ htT) (Fin.last n)
      rw [← kVL_of_lt xL _ (hltL _ htT), hkVL _ _ htT, hkW _ htT, Real.coe_toNNReal _ ht.1.le] at hp
      show -U t < _
      linarith
    have hnot : ¬ Alive (fun r => -U r) (-x₀) T := fun hal => by
      obtain ⟨v, hv⟩ := exists_isForwardSol_neg_iff.1 ⟨_, WangWu.isForwardSol_of_alive hUn hal⟩
      exact hnosol v hv
    have he := rightImg_eq_of_not_alive hUn (by simp only [hU0, neg_zero]) hTR
      (neg_nonneg.2 (hxL _)) (neg_lt_neg hxl) hsep hnot
    simp only [he, neg_neg]
  · -- the right side
    have hsep : ∀ t ∈ Ioo (0 : ℝ) T, U t < rightImg U (xR (Fin.last m)) t := by
      intro t ht
      have htT : t.toNNReal < T := (Real.toNNReal_lt_iff_lt_coe ht.1.le).2 ht.2
      have hp := hγ.kW_lt_kVRr hxR (Real.toNNReal_pos.2 ht.1) (hltL _ htT) (Fin.last m)
      rw [← kVR_of_lt xR _ (hltL _ htT), hkVR _ _ htT, hkW _ htT, Real.coe_toNNReal _ ht.1.le] at hp
      exact hp
    have hnot : ¬ Alive U x₀ T := fun hal => hnosol _ (WangWu.isForwardSol_of_alive hU hal)
    exact (rightImg_eq_of_not_alive hU hU0 hTR (hxR _) hxr hsep hnot).symm

end InteractingSLE.Sec5.KillArc
