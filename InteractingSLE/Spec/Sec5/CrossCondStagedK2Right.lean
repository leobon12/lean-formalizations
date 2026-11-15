/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedK2G12
import InteractingSLE.Spec.Sec5.Aux61R45Visit
import InteractingSLE.Spec.Supplement.GB8InputsRight

/-!
# Lemma GB8, input 3, for traces up to the first contact

Packet PROVE-STAGED9 (ruling R78). `Supp8.GB8.rightNoContactStatement` (no contact of the outermost right mark with the
driver before the lifetime) assumes a generating trace through the whole lifetime. The killed premise
`CompPremiseFarK` supplies a trace only up to the first far contact. This file proves the contact-localized form: for
the GB8 word, almost surely there is **no first contact `T < ζ` of the outermost right mark at which the driver has a
generating trace on `[0, T]`** (p. 523: "Lemma GB7a protects the open right tail, and G12 protects its junction `x₊`
because `c_κ > d_κ`"):

* all right marks at `x₊`: GB7a's comparison picture at the contact (`Supp8.GB8.exists_rightCmp_of_meet`), trace-free;
* a right mark below `x₊`: the stopped GB7a (`Aux61R45.rightCmpPath_of_visit_upTo`, with Aux. lemma 25 on `[0, T]` from
  `StagedK2.injOn_le_of_contact`) keeps the trace off `(x₊, ∞)` on `[0, T]`; Lemma G12 for traces up to the contact
  (`StagedK2.ae_trace_ne_right_contact`) keeps it off `x₊`; the hull at `T` is then the filling of `η([0, T])`
  (`Sec7.IsGeneratingTrace.isGeneratingTraceIcc_of_lt`), a ball around `x₊` is outside it and `x₊` is alive at `T`
  (`w_lt_vR_of_trace_avoid_Icc`), contradicting the contact.

## Main results

* `w_lt_vR_of_trace_avoid_Icc`: GB8's deterministic bridge at the trace's horizon;
* `rightCmp_of_rightCmpPath_le`: the comparison picture before `T ≤ ζ` is the comparison picture before `ζ`;
* **`ae_not_isGeneratingTrace_right_contact`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol fwdHull)

namespace InteractingSLE.Sec5.CrossCond.StagedK2

/-- **A point whose ray the trace avoids up to the horizon is alive at the horizon** (GB8's
`w_lt_vR_of_trace_avoid` with the trace on `[0, t₀]` only, `t₀ < ζ`; proof unchanged except that the hull at `t₀` is
the filling of `η([0, t₀])` by `Sec7.IsGeneratingTrace.isGeneratingTraceIcc_of_lt`). -/
theorem w_lt_vR_of_trace_avoid_Icc {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {x : ℝ} (hx : 0 < x)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hvc : ContinuousOn v {s | (s : ℝ≥0∞) < ζ})
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t ≤ v t) {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w t₀ η) (havoid : ∀ t : ℝ≥0, t ≤ t₀ → ∀ y : ℝ, x ≤ y → η t ≠ y) :
    w t₀ < v t₀ := by
  by_contra hcon
  have heq : v t₀ = w t₀ := le_antisymm (not_lt.1 hcon) (hle t₀ ht₀)
  have hv0 : v 0 = x := by
    have := hveq 0 (lt_of_le_of_lt (zero_le (a := (t₀ : ℝ≥0∞))) ht₀)
    simpa using this
  have ht₀pos : 0 < t₀ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hv0, hw0] at heq
    linarith
  obtain ⟨t₂, h02, h2ζ⟩ : ∃ t₂ : ℝ≥0, t₀ < t₂ ∧ (t₂ : ℝ≥0∞) < ζ := by
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
    exact ⟨r, ENNReal.coe_lt_coe.1 hr1, hr2⟩
  have hW2 : ContinuousOn w (Set.Iic t₂) := hwc.mono fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) h2ζ
  set W' : ℝ → ℝ := fun s => Sec5.Aux22Strip.freezeAt w t₂ s.toNNReal with hW'def
  have hW'c : Continuous W' := Sec5.Aux22Strip.continuous_freezeAt hW2
  have hW'0 : W' 0 = 0 := by
    simp only [hW'def, Real.toNNReal_zero]
    rw [Sec5.Aux22Strip.freezeAt_of_le zero_le, hw0]
  have hW'w : ∀ t : ℝ≥0, t ≤ t₂ → W' t = w t := fun t ht => by
    simp only [hW'def, Real.toNNReal_coe]
    exact Sec5.Aux22Strip.freezeAt_of_le ht
  -- the hull at `t₀` is the filling of the trace
  set A := η '' Set.Icc 0 t₀ with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun s hs => ENNReal.coe_le_coe.2 hs.2)
  have hKeq := (fillH_eq_iff_isFilling_of_isClosed hAc.isBounded hAc.isClosed
    ((QuantumZipper.fwdHull_mono).2 _)).1 (Sec7.IsGeneratingTrace.isGeneratingTraceIcc_of_lt hη ht₀ hwc hw0).2.1
  have hK' : fwdHull (fun s : ℝ => w s.toNNReal) t₀ = fwdHull W' t₀ := by
    refine fwdHull_eq_of_eqOn t₀.coe_nonneg (NNReal.coe_lt_coe.2 h02) fun r hr => ?_
    have hr' : r.toNNReal ≤ t₂ := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    exact (Sec5.Aux22Strip.freezeAt_of_le hr').symm
  -- a ball around `x` outside the hull
  obtain ⟨R₀, hR₀⟩ := hAc.isBounded.subset_closedBall 0
  have hAR : A ⊆ Metric.closedBall 0 (max R₀ 0) :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨ρ, hρ, hball⟩ := Sec5.Aux22Strip.exists_ball_notMem_fillH_aux hAc hAR (a := x)
    (b := max x (max R₀ 0 + 1)) (e := max x (max R₀ 0 + 1))
    (fun r hr ⟨s, hs, hsr⟩ => havoid s hs.2 r hr.1 hsr)
    ⟨le_rfl, le_max_left _ _⟩ ⟨le_max_left _ _, le_rfl⟩ (by
      rw [abs_of_pos (lt_of_lt_of_le hx (le_max_left _ _))]
      linarith [le_max_right x (max R₀ 0 + 1)])
  have hdisj : Disjoint (Metric.ball (x : ℂ) ρ) (fwdHull W' t₀) := by
    rw [← hK', hKeq, Set.disjoint_left]
    exact fun z hz => hball z hz
  obtain ⟨u, hu⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW'c hW'0 hx.ne' t₀.coe_nonneg hρ hdisj
  -- the gap tends to `0` at `t₀`, impossible for an alive point
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hlim : Tendsto (fun t => v t - w t) (𝓝[<] t₀) (𝓝 0) := by
    have hc : ContinuousAt (fun t => v t - w t) t₀ :=
      (hvc.continuousAt (hopen.mem_nhds ht₀)).sub (hwc.continuousAt (hopen.mem_nhds ht₀))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio t₀))
    rwa [heq, sub_self] at this
  have hsub : Set.Iio t₀ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_trans (ENNReal.coe_lt_coe.2 hs) ht₀
  exact Sec5.Aux22Strip.not_isForwardSol_of_tendsto_gap hW'c ht₀pos
    (fun t ht => hW'w t (ht.le.trans h02.le)) (hwc.mono hsub) (hvc.mono hsub)
    (fun t ht => hveq t (hsub ht)) hlim hu

/-! ### No traced contact of the outermost right mark -/

section Evolution

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The comparison picture before a time `T ≤ ζ` is a comparison picture before `ζ`. -/
theorem rightCmp_of_rightCmpPath_le {k : Fin nR} {k2 : Option (Fin nR)} {S : ℝ} {q : ℝ≥0} {ω : Ω}
    {T : ℝ≥0∞} (hT : T ≤ ζ ω)
    (h : GB7a.RightCmpPath ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) T k k2 S q) :
    GB7a.RightCmp ρL ρR W VL VR ζ k k2 S q ω := by
  obtain ⟨T', hqT, hT'T, h1, h2, h3⟩ := h
  exact ⟨T', hqT, hT'T.trans hT, h1, h2, h3⟩

/-- **GB8's input 3 for traces up to the contact** (p. 523). For the GB8 right word (outermost right mark `x₊ > 0`,
right total `κ/2 − 2`, right partial sums before the last above `−2`), `0 < κ < 4`: almost surely, at no first contact
time `T < ζ` of the outermost right mark with the driver does the driver have a generating trace on `[0, T]`. -/
theorem ae_not_isGeneratingTrace_right_contact (hκ : 0 < κ) (hκ4 : κ < 4) (hnR : 0 < nR)
    (hF : IsOrderedForceWord xL xR) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω → (∀ t < T, W t ω < VR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ t ω) →
      VR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ T ω = W T ω →
        ∀ η : ℝ≥0 → ℂ, ¬ IsGeneratingTrace (fun t => W t ω) T η := by
  set k : Fin nR := ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ with hk
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlast : ∀ j, xR j ≤ xR k := fun j => hF.2.2.1 (Fin.le_iff_val_le_val.2 (by simp only [hk]; omega))
  have hfilt : ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i = κ / 2 - 2 := by
    rw [Finset.filter_true_of_mem (fun i _ => hlast i)]
    exact hsR
  have hnull : P (⋃ q : ℚ, {ω | GB7a.RightCmp ρL ρR W VL VR ζ k none (κ / 2 - 2) (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => GB7a.measure_rightCmp_eq_zero hκ hκ4.le hE (by simp) le_rfl _
  by_cases hex : ∃ j, xR j < xR k
  · -- a right mark below `x₊`: the stopped GB7a, Lemma G12 up to the contact, and the hull at the contact
    set i₀ : Fin nR := ⟨0, hnR⟩ with hi₀def
    have hi₀ : ∀ j, i₀ ≤ j := fun j => Fin.le_iff_val_le_val.2 (Nat.zero_le _)
    have hx : xR i₀ < xR k := by
      obtain ⟨j, hj⟩ := hex
      exact lt_of_le_of_lt (hF.2.2.1 (hi₀ j)) hj
    have hS' : -2 < ∑ j ∈ univ.filter (fun j => xR j < xR k), ρR j := by
      classical
      set S := univ.filter (fun j => xR j < xR k) with hSdef
      have hSne : S.Nonempty := by
        obtain ⟨j, hj⟩ := hex
        exact ⟨j, by simp [hSdef, hj]⟩
      set m := S.max' hSne with hmdef
      have hmS : m ∈ S := S.max'_mem hSne
      have hmk : xR m < xR k := (Finset.mem_filter.1 hmS).2
      have hm : (m : ℕ) < nR - 1 := by
        have hle : (m : ℕ) ≤ nR - 1 := by have := m.isLt; omega
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso
          have hmk' : m = k := Fin.ext (by simp only [hk]; exact h)
          rw [hmk'] at hmk
          exact lt_irrefl _ hmk
      have he : S = univ.filter (fun l => l ≤ m) := by
        ext j
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hj
          exact S.le_max' j (by simp [hSdef, hj])
        · intro hj
          exact lt_of_le_of_lt (hF.2.2.1 hj) hmk
      rw [he]
      exact hpsR m hm
    have hG12 := ae_trace_ne_right_contact hκ hF hE hi₀ hx hlast hS' (by rw [hfilt]; linarith)
    have hloc := hE.ae_exists_localization hκ hκ4.le
    have hR := Aux25.endpointExclusionStatement κ hκ hκ4 xL xR ρL ρR P 𝓕 W VL VR B ζ hE
    have hL := Aux25.endpointExclusionStatement κ hκ hκ4 (-xR) (-xL) ρR ρL P 𝓕 (-W) (fun i => -VR i)
      (fun i => -VL i) (-B) ζ hE.reflect
    filter_upwards [hE.2.2.2.2, hG12, measure_eq_zero_iff_ae_notMem.1 hnull, hloc, hR, hL]
      with ω hp hg hgb hlocω hRω hLω T hTζ hbefore hmeet η hη
    have hpf := hp.isForcePath
    have hT0 : 0 < T := by
      refine pos_iff_ne_zero.2 fun h0 => ?_
      have h := hmeet
      rw [h0, hpf.vR_zero k, hpf.w_zero] at h
      linarith
    have hinj := injOn_le_of_contact hp hκ hT0 hTζ hbefore hmeet hlocω hRω hLω hη
    have hup : Sec2.IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (B · ω) T := hp.isSLEPathUpTo hTζ.le
    have hlimT : ∀ T' : ℝ≥0, 0 < T' → (T' : ℝ≥0∞) = (T : ℝ≥0∞) →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T') (𝓝 (w₀, vL₀, vR₀)) := by
      intro T' _ hT'
      have hTT : T' = T := ENNReal.coe_injective hT'
      subst hTT
      exact ⟨_, _, _, tendsto_state_of_lt hp hTζ⟩
    have havoid : ∀ t : ℝ≥0, t ≤ T → ∀ y : ℝ, xR k ≤ y → η t ≠ y := by
      intro t ht y hy he
      rcases hy.lt_or_eq with hy | hy
      · obtain ⟨n, hn⟩ := exists_nat_gt (y - xR k)
        obtain ⟨q, hq⟩ := Aux61R45.rightCmpPath_of_visit_upTo hup hF hη hinj hlimT (k := k)
          (a' := xR k + n + 1) (fun j hj => absurd (hlast j) (not_le.2 hj))
          ⟨t, ENNReal.coe_le_coe.2 ht, y, ⟨hy, by linarith⟩, he⟩
        rw [hfilt] at hq
        exact hgb (Set.mem_iUnion.2 ⟨q, rightCmp_of_rightCmpPath_le hTζ.le hq⟩)
      · exact hg T hT0 hTζ hbefore hmeet η hη t ht (by rw [hy]; exact he)
    have hlt := w_lt_vR_of_trace_avoid_Icc hxp hpf.continuousOn_w hpf.w_zero (hpf.continuousOn_vR k)
      (fun t ht => hpf.vR_eq ht k) (fun t ht => hpf.w_le_vR ht k) hTζ hη havoid
    rw [hmeet] at hlt
    exact lt_irrefl _ hlt
  · -- every right mark at `x₊`: GB7a's comparison picture at the contact, trace-free
    have hco : ∀ j, xR j = xR k := fun j => le_antisymm (hlast j) (not_lt.1 fun h => hex ⟨j, h⟩)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull, hE.ae_isIntegratedSLEPath]
      with ω hω hp T hTζ _ hmeet η _
    obtain ⟨q, hq⟩ := Supp8.GB8.exists_rightCmp_of_meet hp.isForcePath hF.2.1 hxp hco hsR hTζ
      (by rw [hmeet]; exact lt_irrefl _)
    exact hω (Set.mem_iUnion.2 ⟨q, hq⟩)

end Evolution

end InteractingSLE.Sec5.CrossCond.StagedK2
