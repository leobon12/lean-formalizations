/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmpChart
import InteractingSLE.Spec.Supplement.GB7aB
import InteractingSLE.Spec.Sec4.Aux25Path
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Foundations.Loewner.FiniteEndpointStatement

/-!
# GB7a's pathwise comparison input: one path

Packet PROVE-GB7A3. For one path of an integrated `SLE_κ(ρ)` evolution (the force part `Sec2.IsForcePath`) with
a continuous generating trace `η` that is injective up to the lifetime and whose state converges at a finite
positive lifetime (Aux. lemma 3), a visit of the open interval `I = (x_k, a')` between a right mark `k` and the
next right mark produces the comparison picture `RightCmp` of `GB7aB.lean` at a rational restart time `q`:

1. *(the first real contact)* Pick a rational time `p` just before a visit time `t₀` with `η(p) ∈ ℍ`, and let
   `T` be the first real contact after `p`. Then `η(T) ∈ I` and `η ∈ ℍ` on `[p, T)`; take `q ∈ (p, T)` rational.
2. *(marks off the driver)* No force coordinate meets the driver on `[p, T)`: at a collision the tip is real
   (`IsLoewnerTraceLT.exists_tip_real_of_collision_right/left`).
3. *(the chart)* The limit point `y = η(T)` is alive at `q`; the right marks at or left of `x_k` sit strictly
   between the driver and the target `f_q(y)` in the chart, the others strictly beyond it (`lt_re_of_centred`,
   `re_lt_of_centred`).
4. *(collision at `T`)* `V_k − W → 0` at `T⁻` (`eq_zero_of_tendsto_restart`).
5. *(energy)* the comparison drift has bounded energy on `[q, T)` (`exists_energy_bound_of_restart`): the
   weights between the driver and the target sum to `∑_{x_j ≤ x_k} ρ_j − S = 0`.

The driver is read on `ℝ` as a continuous `U` that agrees with `w` before `T`: frozen after a time in `(T, ζ)`
if `T < ζ`, extended by its limit (`FiniteEndpoint.extDriver`) if `T = ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)

variable {nL nR : ℕ}

/-- **The comparison picture of one path** (`RightCmp` read on the path of one `ω`). -/
def RightCmpPath (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (k : Fin nR) (k2 : Option (Fin nR)) (S : ℝ) (q : ℝ≥0) : Prop :=
  ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ ∧
    (∀ t : ℝ≥0, q ≤ t → t < T → (∀ i, ρL i ≠ 0 → w t ≠ vL i t) ∧
      ∀ j, (ρR j ≠ 0 ∨ refWeightR k k2 S j ≠ 0 ∨ j = k) → w t ≠ vR j t) ∧
    (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
      (∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (refWeightR k k2 S j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2) ≤ C) ∧
    Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 0)

theorem rightCmp_iff {Ω : Type*} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {k : Fin nR}
    {k2 : Option (Fin nR)} {S : ℝ} {q : ℝ≥0} {ω : Ω} :
    RightCmp ρL ρR W VL VR ζ k k2 S q ω ↔
      RightCmpPath ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) k k2 S q :=
  Iff.rfl

/-! ### Reading the path on `ℝ` -/

section Transfer

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- A continuous driver on `ℝ` that agrees with `w` before `T ≤ ζ` is driven by the trace before `T`. -/
theorem isLoewnerTraceLT_of_agree (hη : IsGeneratingTrace w ζ η) {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ)
    {U : ℝ → ℝ} (hUw : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal) :
    IsLoewnerTraceLT U T (fun s : ℝ => η s.toNNReal) := by
  refine ⟨by simpa using hη.1, ?_, fun t ht0 htT => ?_⟩
  · refine hη.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ
    refine le_trans ?_ hTζ
    exact ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hs.2.le)
  · set t₂ := (t + T) / 2 with ht₂
    have htt₂ : t < t₂ := by rw [ht₂]; linarith
    have ht₂T : t₂ < T := by rw [ht₂]; linarith
    have ht₂ζ : ENNReal.ofReal t₂ < ζ := by
      refine lt_of_lt_of_le ?_ hTζ
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ht₂T
    have hL := hη.isLoewnerTraceLT ht₂ζ
    rw [← hL.2.2 t ht0 htt₂]
    refine fwdHull_eq_of_eqOn ht0 htt₂ fun r hr => ?_
    rw [hUw r hr.1 (hr.2.trans_lt ht₂T), frozenDrive_eq hr]

/-- **The centred force coordinate `v − w` on `[0, s]`, `s < T`, with any driver agreeing with `w` before `T`.** -/
theorem centredPkg {v : ℝ≥0 → ℝ} {x : ℝ} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hv : ContinuousOn v {s | (s : ℝ≥0∞) < ζ})
    (hint : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 s)
    (heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ →
      v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal))
    (hnull : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = v s.toNNReal} = 0)
    {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ) {U : ℝ → ℝ} (hUw : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal)
    {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T) :
    ContinuousOn (fun r : ℝ => v r.toNNReal - w r.toNNReal) (Icc 0 s) ∧
      (∀ s₁ ∈ Icc (0 : ℝ) s, ∀ s₂ ∈ Icc (0 : ℝ) s, s₁ ≤ s₂ →
        (v s₂.toNNReal - w s₂.toNNReal) - (v s₁.toNNReal - w s₁.toNNReal) =
          -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / (v r.toNNReal - w r.toNNReal)) ∧
      IntervalIntegrable (fun r => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 s ∧
      volume {r | r ∈ Icc (0 : ℝ) s ∧ v r.toNNReal - w r.toNNReal = 0} = 0 := by
  have hsζ : ENNReal.ofReal s < ζ := by
    refine lt_of_lt_of_le ?_ hTζ
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (hs0.trans_lt hsT)).2 hsT
  obtain ⟨hc, he, hi, hn⟩ := Aux25.centred_eq_of_frozen hw hv hint heq hnull hsζ hs0 le_rfl
  have hE : EqOn (Aux25.centred v (frozenDrive w s)) (fun r : ℝ => v r.toNNReal - w r.toNNReal) (Icc 0 s) :=
    fun r hr => by simp only [Aux25.centred, frozenDrive_eq hr]
  have hD : ∀ r ∈ Icc (0 : ℝ) s, frozenDrive w s r = U r := fun r hr => by
    rw [frozenDrive_eq hr, hUw r hr.1 (hr.2.trans_lt hsT)]
  refine ⟨hc.congr hE.symm, fun s₁ h₁ s₂ h₂ h₁₂ => ?_, ?_, ?_⟩
  · have h := he s₁ h₁ s₂ h₂ h₁₂
    rw [hE h₁, hE h₂, hD s₁ h₁, hD s₂ h₂] at h
    rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr' : r ∈ Icc (0 : ℝ) s := uIcc_subset_Icc h₁ h₂ hr
    simp only [hE hr']
  · rw [intervalIntegrable_iff] at hi ⊢
    refine hi.congr_fun (fun r hr => ?_) measurableSet_uIoc
    rw [uIoc_of_le hs0] at hr
    simp only [hE ⟨hr.1.le, hr.2⟩]
  · refine measure_mono_null (fun r hr => ?_) hn
    exact ⟨hr.1, by rw [hE hr.1]; exact hr.2⟩

end Transfer

/-! ### The first real contact after an interior time -/

section FirstContact

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The first real contact after an interior rational time.** If the trace visits a point of an open real
interval `(a, b)`, `a ≥ 0`, at a time `t₀ ≤ ζ`, there are a rational `p > 0` and a time `T ∈ (p, t₀]` such that
`η ∈ ℍ` on `[p, T)` and `η(T)` is a real point of `(a, b)`. -/
theorem exists_firstContact (hη : IsGeneratingTrace w ζ η) (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {a b : ℝ} (ha : 0 ≤ a) {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ) {y : ℝ}
    (hy : y ∈ Ioo a b) (he : η t₀ = y) :
    ∃ (p : ℚ) (T : ℝ≥0) (y' : ℝ), 0 < (p : ℝ) ∧ (p : ℝ) < T ∧ T ≤ t₀ ∧ y' ∈ Ioo a b ∧ η T = y' ∧
      ∀ s : ℝ≥0, (p : ℝ) ≤ s → s < T → η s ∈ H := by
  have ht₀0 : 0 < t₀ := by
    rcases eq_zero_or_pos t₀ with h | h
    · exfalso
      rw [h, hη.1] at he
      have : y = 0 := by exact_mod_cast he.symm
      linarith [hy.1]
    · exact h
  set r := min (y - a) (b - y) with hr
  have hr0 : 0 < r := lt_min (by linarith [hy.1]) (by linarith [hy.2])
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hη.2.1 t₀ ht₀) r hr0
  set δ' := min δ (t₀ : ℝ) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (NNReal.coe_pos.2 ht₀0)
  have hδ't : δ' ≤ t₀ := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  set s₁ : ℝ≥0 := ((t₀ : ℝ) - δ').toNNReal with hs₁def
  set s₂ : ℝ≥0 := ((t₀ : ℝ) - δ' / 2).toNNReal with hs₂def
  have hs₁ : (s₁ : ℝ) = t₀ - δ' := Real.coe_toNNReal _ (by linarith)
  have hs₂ : (s₂ : ℝ) = t₀ - δ' / 2 := Real.coe_toNNReal _ (by linarith)
  have h12 : s₁ < s₂ := by rw [← NNReal.coe_lt_coe, hs₁, hs₂]; linarith
  have h2ζ : (s₂ : ℝ≥0∞) < ζ :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, hs₂]; linarith)) ht₀
  obtain ⟨p, hp1, hp2, hpH⟩ := Aux25.exists_rat_mem_H_btwn hη hwc hw0 h12 h2ζ
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt s₁.coe_nonneg hp1
  set pN : ℝ≥0 := (p : ℝ).toNNReal with hpNdef
  have hpN : (pN : ℝ) = p := Real.coe_toNNReal _ hp0.le
  have hpH' : 0 < (η pN).im := hpH
  have hpt₀ : pN ≤ t₀ := by rw [← NNReal.coe_le_coe, hpN]; linarith
  -- the real contacts in `[p, t₀]`
  set Z : Set ℝ≥0 := Icc pN t₀ ∩ η ⁻¹' {z : ℂ | z.im = 0} with hZ
  have hZc : IsClosed Z :=
    (hη.2.1.mono fun s hs => (show (s : ℝ≥0∞) ≤ ζ from
      (ENNReal.coe_le_coe.2 hs.2).trans ht₀)).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_eq Complex.continuous_im continuous_const)
  have ht₀Z : t₀ ∈ Z := ⟨⟨hpt₀, le_rfl⟩, by simp [he]⟩
  set T := sInf Z with hT
  have hTZ : T ∈ Z := hZc.csInf_mem ⟨t₀, ht₀Z⟩ (OrderBot.bddBelow Z)
  have hTle : T ≤ t₀ := csInf_le (OrderBot.bddBelow Z) ht₀Z
  have hpT : pN < T := by
    refine lt_of_le_of_ne hTZ.1.1 fun h => ?_
    have h1 : (η T).im = 0 := hTZ.2
    rw [← h] at h1
    linarith
  have hH : ∀ s : ℝ≥0, (p : ℝ) ≤ s → s < T → η s ∈ H := fun s hps hsT => by
    have hsZ : s ∉ Z := notMem_of_lt_csInf hsT (OrderBot.bddBelow Z)
    have hs_le : s ≤ t₀ := hsT.le.trans hTle
    have hpNs : pN ≤ s := by rw [← NNReal.coe_le_coe, hpN]; exact hps
    have him : (η s).im ≠ 0 := fun h0 => hsZ ⟨⟨hpNs, hs_le⟩, h0⟩
    have hbar := Sec7.IsGeneratingTrace.mem_Hbar hη hwc hw0 ((ENNReal.coe_le_coe.2 hs_le).trans ht₀)
    exact lt_of_le_of_ne hbar (Ne.symm him)
  have hdist : dist T t₀ < δ := by
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hTle))]
    have h1 : (pN : ℝ) < T := hpT
    rw [hpN] at h1
    linarith
  have hηT := hball ((ENNReal.coe_le_coe.2 hTle).trans ht₀) hdist
  rw [he] at hηT
  set y' := (η T).re with hy'
  have hηTy' : η T = y' := Complex.ext (by simp [hy']) (by simpa using hTZ.2)
  refine ⟨p, T, y', hp0, by rw [← hpN]; exact hpT, hTle, ?_, hηTy', hH⟩
  rw [hηTy', Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hηT
  have h1 := neg_abs_le (y' - y)
  have h2 := le_abs_self (y' - y)
  have h3 : r ≤ y - a := min_le_left _ _
  have h4 : r ≤ b - y := min_le_right _ _
  exact ⟨by linarith, by linarith⟩

end FirstContact

/-! ### The driver on `ℝ` up to the first real contact -/

section Driver

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **A continuous driver on `ℝ` agreeing with `w` before `T ≤ ζ`**, and limits of the right gaps at `T⁻`: frozen
after a time in `(T, ζ)` if `T < ζ`; extended by the limit of the state (Aux. lemma 3) if `T = ζ`. -/
theorem exists_driver (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ)
    (hT0 : 0 < T)
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀))) :
    ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ (∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal) ∧
      ∀ j, ∃ L : ℝ, Tendsto (fun t => vR j t - w t) (𝓝[<] T) (𝓝 L) := by
  rcases hTζ.lt_or_eq with hlt | heq
  · obtain ⟨t₂, hTt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hlt
    have ht₂0 : 0 ≤ t₂ := T.coe_nonneg.trans hTt₂.le
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    refine ⟨frozenDrive w t₂, continuous_frozenDrive_of_lt h.continuousOn_w ht₂ζ, ?_,
      fun s hs0 hsT => frozenDrive_eq ⟨hs0, hsT.le.trans hTt₂.le⟩, fun j => ⟨vR j T - w T, ?_⟩⟩
    · rw [frozenDrive_eq ⟨le_rfl, ht₂0⟩]
      simpa using h.w_zero
    · have hc := ((h.continuousOn_vR j).sub h.continuousOn_w).continuousAt (hopen.mem_nhds hlt)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · obtain ⟨w₀, vL₀, vR₀, hl⟩ := hlimζ T hT0 heq
    have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hl
    have hwc : ContinuousOn w (Iio T) := h.continuousOn_w.mono fun t ht => by
      show (t : ℝ≥0∞) < ζ
      rw [← heq]
      exact ENNReal.coe_lt_coe.2 ht
    refine ⟨FiniteEndpoint.extDriver w T w₀, FiniteEndpoint.continuous_extDriver hwc hw, ?_,
      fun s hs0 hsT => FiniteEndpoint.extDriver_of_lt hs0 hsT, fun j => ⟨vR₀ j - w₀, ?_⟩⟩
    · rw [FiniteEndpoint.extDriver_of_lt le_rfl (NNReal.coe_pos.2 hT0)]
      simpa using h.w_zero
    · have hv : Tendsto (fun t => vR j t) (𝓝[<] T) (𝓝 (vR₀ j)) :=
        (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).tendsto _).comp hl
      exact hv.sub hw

end Driver

/-! ### The comparison picture from a visit -/

section Main

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- Along `s ↑ T` in `ℝ`, `η(s⁺) → η(T)` (`η` continuous on `[0, ζ]`, `T ≤ ζ`). -/
theorem tendsto_comp_toNNReal (hη : IsGeneratingTrace w ζ η) {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ)
    (hT0 : 0 < T) : Tendsto (fun s : ℝ => η s.toNNReal) (𝓝[<] (T : ℝ)) (𝓝 (η T)) := by
  have h1 : Tendsto η (𝓝[<] T) (𝓝 (η T)) :=
    (hη.2.1 T hTζ).mono_left (nhdsWithin_mono _ fun t ht =>
      (ENNReal.coe_le_coe.2 (le_of_lt ht)).trans hTζ)
  have h2 := Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T
  rw [nhdsWithin_Ico_eq_nhdsLT (NNReal.coe_pos.2 hT0)] at h2
  exact h1.comp h2

/-- A limit of `f` at `T⁻` in `ℝ≥0` is a limit of `f(s⁺)` at `T⁻` in `ℝ`. -/
theorem tendsto_comp_toNNReal' {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hT0 : 0 < T) {L : ℝ}
    (hf : Tendsto f (𝓝[<] T) (𝓝 L)) : Tendsto (fun s : ℝ => f s.toNNReal) (𝓝[<] (T : ℝ)) (𝓝 L) := by
  have h2 := Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T
  rw [nhdsWithin_Ico_eq_nhdsLT (NNReal.coe_pos.2 hT0)] at h2
  exact hf.comp h2

/-- **The comparison picture from a visit (one path).** For one path of an integrated `SLE_κ(ρ)` evolution
(force part), with a continuous generating trace injective up to the lifetime and a converging state at a finite
positive lifetime: if the trace visits `(x_k, a')`, where `a'` is at most the next right mark after `x_k`, then
`RightCmpPath` holds at some rational restart time, for the comparison weight `S = ∑_{xᵢ ≤ x_k} ρᵢ`. -/
theorem rightCmpPath_of_visit (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k : Fin nR} {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo (xR k) a', η t = y) :
    ∃ q : ℚ, RightCmpPath ρL ρR w vL vR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal := by
  obtain ⟨t₀, ht₀, y, hy, he⟩ := hvis
  have hwc := h.continuousOn_w
  have hw0 := h.w_zero
  have hxk : 0 ≤ xR k := hord.2.2.2 k
  obtain ⟨p, T, y', hp0, hpT, hTt₀, hy', hηT, hH⟩ := exists_firstContact hη hwc hw0 hxk ht₀ hy he
  have hTζ : (T : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hTt₀).trans ht₀
  have hT0 : 0 < T := NNReal.coe_pos.1 (hp0.trans hpT)
  obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn hpT
  have hq0 : 0 < (q : ℝ) := hp0.trans hpq
  have hqN : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  obtain ⟨U, hU, hU0, hUw, hlimV⟩ := exists_driver h hTζ hT0 hlimζ
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  have hηR : IsLoewnerTraceLT U T ηR := isLoewnerTraceLT_of_agree hη hTζ hUw
  have hltζ : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht =>
    (ENNReal.coe_lt_coe.2 ht).trans_le hTζ
  -- the centred force coordinates and their packages on `[0, s]`, `s < T`
  set ûR : Fin nR → ℝ → ℝ := fun j r => vR j r.toNNReal - w r.toNNReal with hûR
  set ûL : Fin nL → ℝ → ℝ := fun i r => vL i r.toNNReal - w r.toNNReal with hûL
  have pkgR := fun j (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) => centredPkg hwc (h.continuousOn_vR j)
    (fun t ht => h.integrable_gapR ht j) (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hTζ hUw hs0 hsT
  have pkgL := fun i (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) => centredPkg hwc (h.continuousOn_vL i)
    (fun t ht => h.integrable_gapL ht i) (fun t ht => h.vL_eq ht i) (h.volume_collisionL i) hTζ hUw hs0 hsT
  -- (2) no force coordinate meets the driver on `[p, T)`
  have hoffR : ∀ t : ℝ≥0, (p : ℝ) ≤ t → t < T → ∀ j, w t ≠ vR j t := by
    intro t hpt htT j heq
    have htT' : (t : ℝ) < T := NNReal.coe_lt_coe.2 htT
    obtain ⟨hc, hue, hi, hn⟩ := pkgR j t t.coe_nonneg htT'
    obtain ⟨x, hx, -, -⟩ := hηR.exists_tip_real_of_collision_right hU hU0 t.coe_nonneg htT' hc
      (fun s hs => sub_nonneg.2 (h.w_le_vR (hltζ _ (lt_of_le_of_lt
        (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2) htT)) j)) hue hi hn
      (by simp [heq])
    have hHt := hH t hpt htT
    have : (η t).im = 0 := by
      have hx' : η t = x := by simpa [hηRdef] using hx
      rw [hx', Complex.ofReal_im]
    exact absurd this (ne_of_gt hHt)
  have hoffL : ∀ t : ℝ≥0, (p : ℝ) ≤ t → t < T → ∀ i, w t ≠ vL i t := by
    intro t hpt htT i heq
    have htT' : (t : ℝ) < T := NNReal.coe_lt_coe.2 htT
    obtain ⟨hc, hue, hi, hn⟩ := pkgL i t t.coe_nonneg htT'
    obtain ⟨x, hx, -, -⟩ := hηR.exists_tip_real_of_collision_left hU hU0 t.coe_nonneg htT' hc
      (fun s hs => sub_nonpos.2 (h.vL_le_w (hltζ _ (lt_of_le_of_lt
        (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2) htT)) i)) hue hi hn
      (by simp [heq])
    have hHt := hH t hpt htT
    have : (η t).im = 0 := by
      have hx' : η t = x := by simpa [hηRdef] using hx
      rw [hx', Complex.ofReal_im]
    exact absurd this (ne_of_gt hHt)
  have hy'0 : 0 < y' := lt_of_le_of_lt hxk hy'.1
  have hqT' : (q : ℝ) < T := hqT
  -- the trace on `(q, T)`
  have hHR : ∀ s ∈ Ioo (q : ℝ) T, ηR s ∈ H := fun s hs => by
    have hs0 : 0 ≤ s := (hq0.trans hs.1).le
    refine hH s.toNNReal ?_ ?_
    · rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.2
  have hmemζ : ∀ r : ℝ, r ≤ T → ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun r hr =>
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr)).trans hTζ
  have hinjR : ∀ s ∈ Ioo (q : ℝ) T, ηR s ∉ ηR '' Icc 0 q := by
    rintro s hs ⟨r, hr, hrs⟩
    have hrs' := hinj (hmemζ r (hr.2.trans hqT'.le)) (hmemζ s hs.2.le) hrs
    have hs0 : 0 ≤ s := (hq0.trans hs.1).le
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hrs'
    simp only [Real.coe_toNNReal _ hr.1, Real.coe_toNNReal _ hs0] at this
    linarith [hr.2, hs.1]
  have hyq : (y' : ℂ) ∉ ηR '' Icc 0 q := by
    rintro ⟨r, hr, hry⟩
    rw [← hηT] at hry
    have hrT := hinj (hmemζ r (hr.2.trans hqT'.le)) hTζ hry
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hrT
    simp only [Real.coe_toNNReal _ hr.1] at this
    linarith [hr.2]
  have hlimR : Tendsto ηR (𝓝[<] (T : ℝ)) (𝓝 (y' : ℂ)) := by
    rw [← hηT]
    exact tendsto_comp_toNNReal hη hTζ hT0
  -- (3) the limit point is alive at `q`; strict order of the right marks
  obtain ⟨v, hv⟩ := exists_isForwardSol_at_restart hηR hU hU0 hq0.le hqT' hHR hinjR hy'0.ne' hlimR hyq
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_re_of_isForwardSol hU hU0 hy'0 hq0.le hv
  have hV : 0 < (v q).re := hc₁.trans_le (hc₁le q ⟨hq0.le, le_rfl⟩)
  have hsT : ∀ s : ℝ, 0 ≤ s → s < T → s.toNNReal < T := fun s hs0 hsT => by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hsT
  have hnnR : ∀ j, ∀ s : ℝ, 0 ≤ s → s < T → 0 ≤ ûR j s := fun j s hs0 hsT' =>
    sub_nonneg.2 (h.w_le_vR (hltζ _ (hsT s hs0 hsT')) j)
  have hnpL : ∀ i, ∀ s : ℝ, 0 ≤ s → s < T → ûL i s ≤ 0 := fun i s hs0 hsT' =>
    sub_nonpos.2 (h.vL_le_w (hltζ _ (hsT s hs0 hsT')) i)
  have hneR : ∀ j, ∀ s ∈ Ico (q : ℝ) T, ûR j s ≠ 0 := by
    intro j s hs h0
    have hs0 : 0 ≤ s := hq0.le.trans hs.1
    refine hoffR s.toNNReal (by rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]) (hsT s hs0 hs.2) j ?_
    simp only [hûR] at h0
    linarith
  have hneL : ∀ i, ∀ s ∈ Ico (q : ℝ) T, ûL i s ≠ 0 := by
    intro i s hs h0
    have hs0 : 0 ≤ s := hq0.le.trans hs.1
    refine hoffL s.toNNReal (by rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]) (hsT s hs0 hs.2) i ?_
    simp only [hûL] at h0
    linarith
  have hûR0 : ∀ j, ûR j 0 = xR j := fun j => by simp [hûR, h.vR_zero j, h.w_zero]
  have hpkgq := fun j => pkgR j q hq0.le hqT'
  have hlo : ∀ j, xR j ≤ xR k → ûR j q < (v q).re := fun j hj =>
    lt_re_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1
      (by rw [hûR0]; linarith [hy'.1])
  have hhi : ∀ j, xR k < xR j → (v q).re < ûR j q := fun j hj =>
    re_lt_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1 (hpkgq j).2.2.1 (hpkgq j).2.2.2
      (by rw [hûR0]; linarith [hnext j hj, hy'.2])
  -- packages on `[q, s]`
  have rpkgR := fun j (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgR j s (hq0.le.trans hs.1) hs.2)
  have rpkgL := fun i (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgL i s (hq0.le.trans hs.1) hs.2)
  -- (4) collision of `k` at `T`
  obtain ⟨L, hL⟩ := hlimV k
  have hL0 : L = 0 :=
    eq_zero_of_tendsto_restart hηR hU hU0 hq0.le hqT' hHR hy'0 hlimR hv (u := ûR k)
      (fun s hs => ⟨(rpkgR k s hs).1, (rpkgR k s hs).2.1, (rpkgR k s hs).2.2.1⟩)
      (fun s hs => lt_of_le_of_ne (hnnR k s (hq0.le.trans hs.1) hs.2) (hneR k s hs).symm)
      (hlo k le_rfl).le (tendsto_comp_toNNReal' hT0 hL)
  -- (5) the energy bound
  set S := ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i with hS
  set c : Fin nL ⊕ Fin nR → ℝ := Sum.elim ρL (fun j => ρR j - refWeightR k none S j) with hc
  set û : Fin nL ⊕ Fin nR → ℝ → ℝ := Sum.elim ûL ûR with hû
  have hpkg : ∀ j, ∀ s ∈ Ico (q : ℝ) T, ContinuousOn (û j) (Icc q s) ∧
      ∀ s₁ ∈ Icc (q : ℝ) s, ∀ s₂ ∈ Icc (q : ℝ) s, s₁ ≤ s₂ →
        û j s₂ - û j s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / û j r := by
    rintro (i | j) s hs
    · exact ⟨(rpkgL i s hs).1, (rpkgL i s hs).2.1⟩
    · exact ⟨(rpkgR j s hs).1, (rpkgR j s hs).2.1⟩
  have hne : ∀ j, ∀ s ∈ Ico (q : ℝ) T, û j s ≠ 0 := by
    rintro (i | j) s hs
    exacts [hneL i s hs, hneR j s hs]
  have hûLq : ∀ i, ûL i q < 0 := fun i =>
    lt_of_le_of_ne (hnpL i q hq0.le hqT') (hneL i q ⟨le_rfl, hqT'⟩)
  have hûRq : ∀ j, 0 < ûR j q := fun j =>
    lt_of_le_of_ne (hnnR j q hq0.le hqT') (hneR j q ⟨le_rfl, hqT'⟩).symm
  have hsep : ∀ j, û j q ≠ (v q).re := by
    rintro (i | j)
    · exact ((hûLq i).trans hV).ne
    · rcases le_or_gt (xR j) (xR k) with hj | hj
      · exact (hlo j hj).ne
      · exact (hhi j hj).ne'
  have hright : ∀ j : Fin nR, (0 < û (Sum.inr j) q ∧ û (Sum.inr j) q < (v q).re) ↔ xR j ≤ xR k := by
    intro j
    constructor
    · rintro ⟨-, h2⟩
      by_contra hj
      exact absurd (hhi j (not_le.1 hj)) (not_lt.2 h2.le)
    · intro hj
      exact ⟨hûRq j, hlo j hj⟩
  have hcore : ∑ j ∈ univ.filter (fun j => 0 < û j q ∧ û j q < (v q).re), c j = 0 := by
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    have hleft : ∑ i : Fin nL, (if 0 < û (Sum.inl i) q ∧ û (Sum.inl i) q < (v q).re
        then c (Sum.inl i) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun hh => absurd hh.1 (not_lt.2 (hûLq i).le)
    rw [hleft, zero_add]
    simp_rw [hright]
    rw [← Finset.sum_filter]
    simp only [hc, Sum.elim_inr]
    rw [Finset.sum_sub_distrib]
    have href : ∑ j ∈ univ.filter (fun j => xR j ≤ xR k), refWeightR k none S j = S := by
      simp only [refWeightR, reduceCtorEq, ite_false, sub_zero]
      rw [Finset.sum_ite_eq']
      simp
    rw [href, sub_self]
  obtain ⟨C, hC⟩ := exists_energy_bound_of_restart hηR hU hU0 hq0.le hqT' hHR hinjR hy'0 hlimR hv
    û c hpkg hne hsep hcore
  have hqt : ∀ t : ℝ≥0, (q : ℝ).toNNReal ≤ t → (q : ℝ) ≤ t := fun t ht => by
    rw [← hqN]; exact NNReal.coe_le_coe.2 ht
  refine ⟨q, T, by rw [← NNReal.coe_lt_coe, hqN]; exact hqT', hTζ, fun t hqt' htT =>
    ⟨fun i _ => hoffL t (by linarith [hqt t hqt']) htT i,
      fun j _ => hoffR t (by linarith [hqt t hqt']) htT j⟩, ⟨C, fun t hqt' htT => ?_⟩, ?_⟩
  · have hb := hC t ⟨hqt t hqt', NNReal.coe_lt_coe.2 htT⟩
    rw [hqN]
    refine le_of_eq_of_le (intervalIntegral.integral_congr fun s _ => ?_) hb
    simp only [Fintype.sum_sum_type, hû, hc, Sum.elim_inl, Sum.elim_inr, hûL, hûR]
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_div, ← div_neg, neg_sub]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← neg_sub (ρR j), ← neg_sub (vR j s.toNNReal), neg_div_neg_eq]
  · rw [← hL0]
    exact hL

end Main

end GB7a

end InteractingSLE
