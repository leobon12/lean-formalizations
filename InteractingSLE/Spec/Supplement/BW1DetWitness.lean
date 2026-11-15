/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1DetIdent

/-!
# BW1's terminal relation: the tip clause and the exact witness characterization

Packet PROVE-BW1-DET. For a chart `c` with a proper boundary extension `f` (here `termChart D`), regular drivers
`U`, `V` with traces `Γ`, `γ`, the tips of `U` through `c` and the inversion at time `r` are those of `V` at time
`s` iff `Γ r = 0 ↔ γ s = 0` and, when `Γ r ≠ 0`, `f(−1/Γ r) = −1/γ s` (`tipRel_iff_traces`). For continuous
`Γ`, `γ ∘ ℓ` this holds at every time once it holds at rational times (`tipRel_of_rat`; the inverted traces leave
every compact set together). The boundary value `f(w)` is the limit along `w + i/(n+1)` (`vert_tendsto_iff`).
Together with `BW1DetIdent`, every test of `witnessSet` is identified (`mem_witnessSet_iff`), and the clock of a
witness is determined by the codes and the record alone (`clock_eq_of_mem_witnessSet`, no regularity of the record
needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.BW1Det

open Exist Exist.StagedLaw GW1Borel BW1Term

/-! ### Vertical limits -/

theorem add_I_div_mem_H {w : ℂ} (hw : w ∈ Hbar) (n : ℕ) : w + Complex.I / ((n : ℂ) + 1) ∈ H := by
  have h1 : 0 ≤ w.im := hw
  have h2 : (Complex.I / ((n : ℂ) + 1)).im = 1 / ((n : ℝ) + 1) := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im, Complex.I_im]
  change 0 < (w + Complex.I / ((n : ℂ) + 1)).im
  rw [Complex.add_im, h2]
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem vert_tendsto {w : ℂ} (hw : w ∈ Hbar) :
    Tendsto (fun n : ℕ => w + Complex.I / ((n : ℂ) + 1)) atTop (𝓝[H] w) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => add_I_div_mem_H hw n⟩
  have h : Tendsto (fun n : ℕ => Complex.I / ((n : ℂ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.const_mul Complex.I
    rw [Complex.ofReal_zero, mul_zero] at h2
    refine h2.congr fun n => ?_
    push_cast
    ring
  simpa only [add_zero] using (tendsto_const_nhds (x := w)).add h

/-- **The boundary value as a vertical limit.** -/
theorem vert_tendsto_iff {c : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {w : ℂ} (hw : w ∈ Hbar) (z : ℂ) :
    Tendsto (fun n : ℕ => c.2.1 (w + Complex.I / ((n : ℂ) + 1))) atTop (𝓝 z) ↔ f w = z := by
  have h := (hf w hw).comp (vert_tendsto hw)
  constructor
  · exact fun hz => tendsto_nhds_unique h hz
  · rintro rfl
    exact h

/-! ### The tip clause -/

section Tip

variable {c : Chart} {f : ℂ → ℂ} {C : ℝ}

theorem tipAt_trans_iff_trace (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    {U : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace U ⊤ Γ) (hU : Continuous U) (hU0 : U 0 = 0)
    (r : ℝ≥0) (z : ℂ) :
    (c.trans infinitySourceChart).tipAt U r z ↔ Γ r ≠ 0 ∧ z = f (negInv (Γ r)) := by
  rw [GW1Det.tipAt_trans_iff_exists hf hC hΓ hU hU0]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hne, rfl⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hΓ hU hU0 r p).1 hp
    exact ⟨hne, rfl⟩
  · rintro ⟨hne, rfl⟩
    exact ⟨_, (GW4Leaf.tipAt_infinitySourceChart_iff hΓ hU hU0 r _).2 ⟨hne, rfl⟩, rfl⟩

/-- **The tip relation at one time, through the traces.** -/
theorem tipRel_iff_traces (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    {U V : ℝ≥0 → ℝ} {Γ γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace U ⊤ Γ) (hU : Continuous U) (hU0 : U 0 = 0)
    (hγ : IsGeneratingTrace V ⊤ γ) (hV : Continuous V) (hV0 : V 0 = 0) (r s : ℝ≥0) :
    (∀ z, (c.trans infinitySourceChart).tipAt U r z ↔ infinitySourceChart.tipAt V s z) ↔
      (Γ r = 0 ↔ γ s = 0) ∧ (Γ r ≠ 0 → f (negInv (Γ r)) = negInv (γ s)) := by
  simp only [tipAt_trans_iff_trace hf hC hΓ hU hU0, GW4Leaf.tipAt_infinitySourceChart_iff hγ hV hV0]
  constructor
  · intro h
    have hAB : Γ r ≠ 0 → γ s ≠ 0 ∧ f (negInv (Γ r)) = negInv (γ s) := fun hA => by
      obtain ⟨hB, he⟩ := (h _).1 ⟨hA, rfl⟩
      exact ⟨hB, he⟩
    have hBA : γ s ≠ 0 → Γ r ≠ 0 := fun hB => ((h _).2 ⟨hB, rfl⟩).1
    exact ⟨⟨fun h0 => by_contra fun hB => hBA hB h0, fun h0 => by_contra fun hA => (hAB hA).1 h0⟩,
      fun hA => (hAB hA).2⟩
  · rintro ⟨hz, he⟩ z
    by_cases hA : Γ r = 0
    · exact iff_of_false (fun h => h.1 hA) (fun h => h.1 (hz.1 hA))
    · have hB : γ s ≠ 0 := fun h0 => hA (hz.2 h0)
      rw [he hA]
      exact ⟨fun h => ⟨hB, h.2⟩, fun h => ⟨hA, h.2⟩⟩

theorem tendsto_norm_negInv_atTop {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝 0)) (hne : ∀ᶠ m in atTop, u m ≠ 0) :
    Tendsto (fun m => ‖negInv (u m)‖) atTop atTop := by
  simp only [negInv, norm_neg, norm_inv]
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, hne.mono fun m hm => norm_pos_iff.2 hm⟩)
  simpa only [norm_zero] using hu.norm

/-- **The tip clause at rational times gives it at every time.** -/
theorem tipRel_of_rat (hfc : ContinuousOn f Hbar) (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    {Γ δ : ℝ≥0 → ℂ} (hΓc : Continuous Γ) (hδc : Continuous δ) (hΓH : ∀ r, Γ r ∈ Hbar)
    (h : ∀ q : ℚ≥0, (Γ q = 0 ↔ δ q = 0) ∧ (Γ q ≠ 0 → f (negInv (Γ q)) = negInv (δ q))) (r : ℝ≥0) :
    (Γ r = 0 ↔ δ r = 0) ∧ (Γ r ≠ 0 → f (negInv (Γ r)) = negInv (δ r)) := by
  obtain ⟨qs, -, hqs⟩ := exists_seq_nnrat_le_tendsto r
  have hΓlim : Tendsto (fun m => Γ (qs m)) atTop (𝓝 (Γ r)) := (hΓc.tendsto r).comp hqs
  have hδlim : Tendsto (fun m => δ (qs m)) atTop (𝓝 (δ r)) := (hδc.tendsto r).comp hqs
  have hnegH : ∀ m, negInv (Γ (qs m)) ∈ Hbar := fun m => GW4Traverse.negInv_mem_Hbar (hΓH _)
  have hlow : ∀ m, ‖negInv (Γ (qs m))‖ - C ≤ ‖f (negInv (Γ (qs m)))‖ := fun m => by
    have h1 := hC _ (hnegH m)
    have h2 := norm_sub_norm_le (negInv (Γ (qs m))) (f (negInv (Γ (qs m))))
    rw [norm_sub_rev] at h2
    linarith
  by_cases ha : Γ r = 0
  · have hb : δ r = 0 := by
      by_contra hb
      have hev : ∀ᶠ m in atTop, δ (qs m) ≠ 0 := hδlim.eventually_ne hb
      have hev' : ∀ᶠ m in atTop, Γ (qs m) ≠ 0 := hev.mono fun m hm h0 => hm ((h (qs m)).1.1 h0)
      have hconv : Tendsto (fun m => f (negInv (Γ (qs m)))) atTop (𝓝 (negInv (δ r))) := by
        refine ((hδlim.inv₀ hb).neg).congr' ?_
        filter_upwards [hev'] with m hm
        exact ((h (qs m)).2 hm).symm
      have h1 := tendsto_norm_negInv_atTop (by rwa [ha] at hΓlim) hev'
      have hinf : Tendsto (fun m => ‖f (negInv (Γ (qs m)))‖) atTop atTop :=
        tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ (-C) h1)
      exact not_tendsto_atTop_of_tendsto_nhds hconv.norm hinf
    exact ⟨iff_of_true ha hb, fun h' => absurd ha h'⟩
  · have hev : ∀ᶠ m in atTop, Γ (qs m) ≠ 0 := hΓlim.eventually_ne ha
    have hconv : Tendsto (fun m => f (negInv (Γ (qs m)))) atTop (𝓝 (f (negInv (Γ r)))) :=
      (hfc _ (GW4Traverse.negInv_mem_Hbar (hΓH r))).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨(hΓlim.inv₀ ha).neg, Eventually.of_forall hnegH⟩)
    have hconv' : Tendsto (fun m => negInv (δ (qs m))) atTop (𝓝 (f (negInv (Γ r)))) := by
      refine hconv.congr' ?_
      filter_upwards [hev] with m hm
      exact (h (qs m)).2 hm
    have hb : δ r ≠ 0 := by
      intro hb
      have hev2 : ∀ᶠ m in atTop, δ (qs m) ≠ 0 := hev.mono fun m hm h0 => hm ((h (qs m)).1.2 h0)
      have hinf := tendsto_norm_negInv_atTop (by rwa [hb] at hδlim) hev2
      exact not_tendsto_atTop_of_tendsto_nhds hconv'.norm hinf
    exact ⟨iff_of_false ha hb, fun _ => tendsto_nhds_unique hconv' (hδlim.inv₀ hb).neg⟩

end Tip

/-! ### The witness characterization -/

/-- **The tests of `witnessSet` are exactly the relation**, for codes of regular drivers and the record of a regular
piece with finite lifetime: canonical clock code, and the coded clock is a prefix clock of `U` after the piece. -/
theorem mem_witnessSet_iff (u v : RegularCode) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : GW1P.PieceRegular D.1 (min ⊤ D.2))
    (hfin : D.2 ≠ ⊤) (c : Code) :
    (((u, v), recOf ⊤ D), c) ∈ witnessSet ↔
      (∀ q : ℚ≥0, c q = (clock c q : ℝ)) ∧
        GW1LaunchClock.IsPrefixClock (termChart D) (driver v.1) (driver u.1) (termSet D) (clock c) := by
  obtain ⟨f, C, hf, hC⟩ := hasProperBdryExt_termChart hD hfin
  obtain ⟨hW0, hWc', α, hα', -⟩ := hD
  have hWc : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ D.2} := by rwa [min_top_left] at hWc'
  have hα : IsGeneratingTrace D.1 D.2 α := by rwa [min_top_left] at hα'
  set L := D.2.toNNReal with hLdef
  have hDL : D.2 = (L : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  have hαc : ContinuousOn α (Icc 0 L) := hα.2.1.mono fun t ht => by
    show (t : ℝ≥0∞) ≤ D.2
    rw [hDL]
    exact ENNReal.coe_le_coe.2 ht.2
  have hβ : ∀ p : ℝ≥0, p ≤ L → WalkLeaf.recPath (recOf ⊤ D) p = α p := fun p hp =>
    recPath_recOf hα hWc hW0 (by rw [hDL]; exact ENNReal.coe_le_coe.2 hp)
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  have hchart := recChart_recOf hWc hW0
  have hL : (recOf ⊤ D).2.1 = (L : ℝ≥0∞) := recOf_snd_fst.trans hDL
  have hΓ := (trace_properties u).1
  have hγ := (trace_properties v).1
  have hℓc := continuous_clock c
  have hℓ0 := clock_zero c
  have hγc := continuous_trace v
  have hft := firstTipTime_eq_hitTime hα hWc hW0 hfin hγ (continuous_driver _) (driver_zero _)
  have hnegH : ∀ q : ℚ≥0, negInv (trace u q) ∈ Hbar := fun q => GW4Traverse.negInv_mem_Hbar (trace_mem_Hbar u q)
  change ((∀ q : ℚ≥0, c q = (clock c q : ℝ)) ∧
    (∀ a b : ℚ≥0, a < b → clock c a < clock c b) ∧
    (∀ n : ℕ, ∃ k : ℕ, ∀ q p : ℚ≥0, (q : ℝ≥0) ≤ clock c n → ((p : ℝ≥0) : ℝ≥0∞) ≤ (recOf ⊤ D).2.1 →
      WalkLeaf.recPath (recOf ⊤ D) p ≠ 0 →
        (1 : ℝ) / ((k : ℝ) + 1) ≤ ‖trace v q - negInv (WalkLeaf.recPath (recOf ⊤ D) p)‖) ∧
    ((⨆ n : ℕ, (clock c n : ℝ≥0∞)) < ⊤ → ∀ k : ℕ, ∃ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) ≤ (recOf ⊤ D).2.1 ∧
      WalkLeaf.recPath (recOf ⊤ D) p ≠ 0 ∧
      ‖trace v (⨆ n : ℕ, (clock c n : ℝ≥0∞)).toNNReal - negInv (WalkLeaf.recPath (recOf ⊤ D) p)‖ <
        (1 : ℝ) / ((k : ℝ) + 1)) ∧
    (∀ q : ℚ≥0, (trace u q = 0 ↔ trace v (clock c q) = 0)) ∧
    (∀ q : ℚ≥0, trace u q ≠ 0 →
      Tendsto (fun n : ℕ => (recChart (recOf ⊤ D)).2.1 (negInv (trace u q) + Complex.I / ((n : ℂ) + 1))) atTop
        (𝓝 (negInv (trace v (clock c q)))))) ↔ _
  rw [hL, hchart]
  unfold GW1LaunchClock.IsPrefixClock
  rw [hft]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hm : StrictMono (clock c) := (strictMono_iff_rat hℓc).2 h2
    refine ⟨h1, hℓc, hm, (range_iff_tests hγc hαc hβ hℓc hm hℓ0).2 ⟨h3, h4⟩, fun r => ?_⟩
    refine (tipRel_iff_traces hf hC hΓ (continuous_driver _) (driver_zero _) hγ (continuous_driver _)
      (driver_zero _) r (clock c r)).2 ?_
    exact tipRel_of_rat hfc hC (continuous_trace u) (hγc.comp hℓc) (trace_mem_Hbar u)
      (fun q => ⟨h5 q, fun hq => (vert_tendsto_iff hf (hnegH q) _).1 (h6 q hq)⟩) r
  · rintro ⟨h1, -, hm, hrange, htip⟩
    have hrel := fun r => (tipRel_iff_traces hf hC hΓ (continuous_driver _) (driver_zero _) hγ
      (continuous_driver _) (driver_zero _) r (clock c r)).1 (htip r)
    obtain ⟨h3, h4⟩ := (range_iff_tests hγc hαc hβ hℓc hm hℓ0).1 hrange
    exact ⟨h1, (strictMono_iff_rat hℓc).1 hm, h3, h4, fun q => (hrel q).1,
      fun q hq => (vert_tendsto_iff hf (hnegH q) _).2 ((hrel q).2 hq)⟩

/-! ### The clock of a witness is unique -/

/-- Two continuous monotone clocks from `0` along which a generating trace takes the same values are equal
(equal trace prefixes, equal hulls, equal capacities). -/
theorem clock_eq_of_trace_eq {V : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace V ⊤ γ) (hV : Continuous V)
    {ℓ₁ ℓ₂ : ℝ≥0 → ℝ≥0} (hc₁ : Continuous ℓ₁) (hc₂ : Continuous ℓ₂) (hm₁ : Monotone ℓ₁) (hm₂ : Monotone ℓ₂)
    (h0₁ : ℓ₁ 0 = 0) (h0₂ : ℓ₂ 0 = 0) (heq : ∀ r, γ (ℓ₁ r) = γ (ℓ₂ r)) : ℓ₁ = ℓ₂ := by
  have himg₁ (r : ℝ≥0) : ℓ₁ '' Icc 0 r = Icc 0 (ℓ₁ r) := by
    rw [hc₁.continuousOn.image_Icc_of_monotoneOn zero_le (hm₁.monotoneOn _), h0₁]
  have himg₂ (r : ℝ≥0) : ℓ₂ '' Icc 0 r = Icc 0 (ℓ₂ r) := by
    rw [hc₂.continuousOn.image_Icc_of_monotoneOn zero_le (hm₂.monotoneOn _), h0₂]
  have hQc := hV.comp continuous_real_toNNReal
  funext r
  have htrace : γ '' Icc 0 (ℓ₁ r) = γ '' Icc 0 (ℓ₂ r) := by
    rw [← himg₁, ← himg₂, image_image, image_image]
    exact congrArg (fun f : ℝ≥0 → ℂ => f '' Icc 0 r) (funext heq)
  have hhull : QuantumZipper.fwdHull (fun s : ℝ => V s.toNNReal) (ℓ₁ r) =
      QuantumZipper.fwdHull (fun s : ℝ => V s.toNNReal) (ℓ₂ r) := by
    rw [Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ ENNReal.coe_lt_top,
      Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ ENNReal.coe_lt_top, htrace]
  have hcap := HPHull.hcap_congr
    (A := ⟨_, isHPHull_fwdHull hQc (ℓ₁ r).coe_nonneg⟩)
    (B := ⟨_, isHPHull_fwdHull hQc (ℓ₂ r).coe_nonneg⟩) hhull
  rw [GW4Ident.hcap_fwdHull_eq hQc (ℓ₁ r).coe_nonneg,
    GW4Ident.hcap_fwdHull_eq hQc (ℓ₂ r).coe_nonneg] at hcap
  exact NNReal.coe_injective (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hcap)

/-- **The clock code of a witness is determined by the two codes and the record** (any record). -/
theorem clock_eq_of_mem_witnessSet {x y : Wsp} (hx : x ∈ witnessSet) (hy : y ∈ witnessSet) (hxy : x.1 = y.1) :
    x.2 = y.2 := by
  obtain ⟨hx1, hx2, -, -, hx5, hx6⟩ := hx
  obtain ⟨hy1, hy2, -, -, hy5, hy6⟩ := hy
  rw [← hxy] at hy5 hy6
  have hq : ∀ q : ℚ≥0, trace x.1.1.2 (clock x.2 q) = trace x.1.1.2 (clock y.2 q) := by
    intro q
    by_cases h0 : trace x.1.1.1 q = 0
    · rw [(hx5 q).1 h0, (hy5 q).1 h0]
    · have h := tendsto_nhds_unique (hx6 q h0) (hy6 q h0)
      simpa only [negInv, neg_inj, inv_inj] using h
  have hγc := continuous_trace x.1.1.2
  have hcx := continuous_clock x.2
  have hcy := continuous_clock y.2
  have hall : ∀ r, trace x.1.1.2 (clock x.2 r) = trace x.1.1.2 (clock y.2 r) := by
    intro r
    obtain ⟨qs, -, hqs⟩ := exists_seq_nnrat_le_tendsto r
    exact tendsto_nhds_unique (((hγc.comp hcx).tendsto r).comp hqs)
      ((((hγc.comp hcy).tendsto r).comp hqs).congr fun m => (hq (qs m)).symm)
  have hmx : StrictMono (clock x.2) := (strictMono_iff_rat hcx).2 hx2
  have hmy : StrictMono (clock y.2) := (strictMono_iff_rat hcy).2 hy2
  have hcl := clock_eq_of_trace_eq (trace_properties x.1.1.2).1 (continuous_driver _) hcx hcy hmx.monotone
    hmy.monotone (clock_zero _) (clock_zero _) hall
  funext q
  rw [hx1 q, hy1 q, hcl]

end InteractingSLE.Theorem14.BW1Det
