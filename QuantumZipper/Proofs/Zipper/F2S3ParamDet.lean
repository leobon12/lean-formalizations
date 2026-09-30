import QuantumZipper.Proofs.Zipper.F2S3Weld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F2 step (3), `Step3WeldParamStmt`: deterministic part (capture times, transport of lengths)

Theorem 1.3, node F2, step (3) (Sheffield, arXiv:1012.4797, §5.4, pp. 70–72). Deterministic
bookkeeping for `F2S3Param.lean`.

* `captureFn a h`: the inverse of a continuous strictly increasing boundary position map
  `a : [0,h] → [a 0, a h]` (the capture time of a boundary point), built as a supremum so that it
  is monotone, hence measurable, on all of `ℝ` (`captureFn_spec`, `captureFn_le_iff`).
* `LeftArc`, `RightArc`: one stage of the `Γ⁰` picture (boundary position maps `a`, `b` of the two
  sides with `ν_Γ[O⁻, a r] = L⁻_r`, `ν_Γ[b r, O⁺] = L⁺_r`), as in `F1.LswArcs`.
* `map_restrict_eq`: two finite image measures on `ℝ` with the same distribution function agree
  (`Measure.ext_of_Iic`); applied to the capture-time images of `ν_Γ` on `(O⁻, a s]` at two
  horizons, whose distribution function is `r ↦ L⁻_{min r s} − L⁻_0` at both (`left_map_eq`,
  `right_map_eq`).

Own elementary measure-theoretic bookkeeping (no published proof is needed for these steps).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## Capture function -/

/-- The capture time of `w` for a boundary position map `a` on `[0,h]`. -/
def captureFn (a : ℝ → ℝ) (h : ℝ) (w : ℝ) : ℝ :=
  sSup (insert 0 {r | r ∈ Icc 0 h ∧ a r ≤ w})

theorem captureFn_mono {a : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) : Monotone (captureFn a h) := by
  intro w w' hw
  unfold captureFn
  apply csSup_le_csSup
  · refine ⟨h, ?_⟩
    rintro r (rfl | ⟨hr, -⟩)
    · exact hh
    · exact hr.2
  · exact ⟨0, mem_insert _ _⟩
  · exact insert_subset_insert fun r ⟨hr, har⟩ => ⟨hr, har.trans hw⟩

theorem measurable_captureFn {a : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) : Measurable (captureFn a h) :=
  (captureFn_mono hh).measurable

theorem captureFn_spec {a : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) (ha : Continuous a)
    (hm : StrictMonoOn a (Icc 0 h)) {w : ℝ} (hw : w ∈ Icc (a 0) (a h)) :
    captureFn a h w ∈ Icc 0 h ∧ a (captureFn a h w) = w := by
  obtain ⟨r0, hr0, hr0w⟩ := intermediate_value_Icc hh ha.continuousOn hw
  have hset : insert 0 {r | r ∈ Icc 0 h ∧ a r ≤ w} = Icc 0 r0 := by
    ext r
    constructor
    · rintro (rfl | ⟨hr, har⟩)
      · exact ⟨le_rfl, hr0.1⟩
      · refine ⟨hr.1, ?_⟩
        rw [← hr0w] at har
        exact (hm.le_iff_le hr hr0).1 har
    · rintro ⟨h0, hr⟩
      have hr' : r ∈ Icc 0 h := ⟨h0, hr.trans hr0.2⟩
      refine Or.inr ⟨hr', ?_⟩
      rw [← hr0w]
      exact (hm.le_iff_le hr' hr0).2 hr
  have : captureFn a h w = r0 := by
    unfold captureFn
    rw [hset, csSup_Icc hr0.1]
  rw [this]
  exact ⟨hr0, hr0w⟩

theorem captureFn_le_iff {a : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) (ha : Continuous a)
    (hm : StrictMonoOn a (Icc 0 h)) {w : ℝ} (hw : w ∈ Icc (a 0) (a h)) {r : ℝ}
    (hr : r ∈ Icc 0 h) : captureFn a h w ≤ r ↔ w ≤ a r := by
  obtain ⟨h1, h2⟩ := captureFn_spec hh ha hm hw
  conv_rhs => rw [← h2]
  exact (hm.le_iff_le h1 hr).symm

/-! ## Distribution functions of image measures -/

theorem map_restrict_Iic {ν : Measure ℝ} {D : Set ℝ} {φ : ℝ → ℝ} (hφ : Measurable φ)
    {s : ℝ} (hs : 0 ≤ s) (hD : ∀ w ∈ D, φ w ∈ Icc 0 s) {F : ℝ → ℝ≥0∞}
    (hS : ∀ m ∈ Icc 0 s, ν (D ∩ φ ⁻¹' Iic m) = F m) (r : ℝ) :
    ((ν.restrict D).map φ) (Iic r) = if r < 0 then 0 else F (min r s) := by
  rw [Measure.map_apply hφ measurableSet_Iic, Measure.restrict_apply (hφ measurableSet_Iic),
    inter_comm]
  split_ifs with hr
  · rw [inter_preimage_Iic_neg hD hr, measure_empty]
  · rw [inter_preimage_Iic_min hD r]
    exact hS _ ⟨le_min (not_lt.1 hr) hs, min_le_right _ _⟩

theorem map_restrict_eq {ν₁ ν₂ : Measure ℝ} {D₁ D₂ : Set ℝ} {φ₁ φ₂ : ℝ → ℝ}
    (hφ₁ : Measurable φ₁) (hφ₂ : Measurable φ₂) {s : ℝ} (hs : 0 ≤ s)
    (hD₁ : ∀ w ∈ D₁, φ₁ w ∈ Icc 0 s) (hD₂ : ∀ w ∈ D₂, φ₂ w ∈ Icc 0 s) {F : ℝ → ℝ≥0∞}
    (hS₁ : ∀ m ∈ Icc 0 s, ν₁ (D₁ ∩ φ₁ ⁻¹' Iic m) = F m)
    (hS₂ : ∀ m ∈ Icc 0 s, ν₂ (D₂ ∩ φ₂ ⁻¹' Iic m) = F m) (hfin : ν₁ D₁ ≠ ⊤) :
    (ν₁.restrict D₁).map φ₁ = (ν₂.restrict D₂).map φ₂ := by
  have : IsFiniteMeasure (ν₁.restrict D₁) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  refine Measure.ext_of_Iic _ _ fun r => ?_
  rw [map_restrict_Iic hφ₁ hs hD₁ hS₁, map_restrict_Iic hφ₂ hs hD₂ hS₂]

/-- A set integral of `ρ = ρ' ∘ φ` is the integral of `ρ'` against the image measure. -/
theorem setLIntegral_eq_map {ν : Measure ℝ} {D : Set ℝ} (hD : MeasurableSet D) {φ : ℝ → ℝ}
    (hφ : Measurable φ) {ρ ρ' : ℝ → ℝ≥0∞} (hρ' : Measurable ρ')
    (h : ∀ w ∈ D, ρ w = ρ' (φ w)) :
    ∫⁻ w in D, ρ w ∂ν = ∫⁻ r, ρ' r ∂((ν.restrict D).map φ) := by
  rw [lintegral_map hρ' hφ]
  exact setLIntegral_congr_fun hD h

/-! ## One side of one stage -/

/-- Left side of one stage: `a` continuous, strictly increasing on `[0,h]` from `O` to `0`,
`ν[O, a r] = L r < ∞`. -/
def LeftArc (ν : Measure ℝ) (O h : ℝ) (L : ℝ → ℝ≥0∞) (a : ℝ → ℝ) : Prop :=
  0 ≤ h ∧ Continuous a ∧ StrictMonoOn a (Icc 0 h) ∧ a 0 = O ∧ a h = 0 ∧
    ∀ r ∈ Icc 0 h, ν (Icc O (a r)) = L r ∧ L r ≠ ⊤

/-- Right side of one stage: `b` continuous, strictly decreasing on `[0,h]` from `O` to `0`,
`ν[b r, O] = L r < ∞`. -/
def RightArc (ν : Measure ℝ) (O h : ℝ) (L : ℝ → ℝ≥0∞) (b : ℝ → ℝ) : Prop :=
  0 ≤ h ∧ Continuous b ∧ StrictAntiOn b (Icc 0 h) ∧ b 0 = O ∧ b h = 0 ∧
    ∀ r ∈ Icc 0 h, ν (Icc (b r) O) = L r ∧ L r ≠ ⊤

section Left

variable {ν : Measure ℝ} {O h : ℝ} {L : ℝ → ℝ≥0∞} {a : ℝ → ℝ}

theorem LeftArc.mem (H : LeftArc ν O h L a) {r : ℝ} (hr : r ∈ Icc 0 h) : a r ∈ Icc O 0 := by
  obtain ⟨hh, -, hm, ha0, hah, -⟩ := H
  refine ⟨?_, ?_⟩
  · rw [← ha0]; exact (hm.le_iff_le ⟨le_rfl, hh⟩ hr).2 hr.1
  · rw [← hah]; exact (hm.le_iff_le hr ⟨hh, le_rfl⟩).2 hr.2

theorem LeftArc.cap (H : LeftArc ν O h L a) {w : ℝ} (hw : w ∈ Icc O 0) :
    captureFn a h w ∈ Icc 0 h ∧ a (captureFn a h w) = w := by
  obtain ⟨hh, hc, hm, ha0, hah, -⟩ := H
  exact captureFn_spec hh hc hm (by rw [ha0, hah]; exact hw)

theorem LeftArc.cap_le_iff (H : LeftArc ν O h L a) {w : ℝ} (hw : w ∈ Icc O 0) {r : ℝ}
    (hr : r ∈ Icc 0 h) : captureFn a h w ≤ r ↔ w ≤ a r := by
  obtain ⟨hh, hc, hm, ha0, hah, -⟩ := H
  exact captureFn_le_iff hh hc hm (by rw [ha0, hah]; exact hw) hr

theorem LeftArc.cap_pos (H : LeftArc ν O h L a) {w : ℝ} (hw : w ∈ Icc O 0) (hOw : O < w) :
    0 < captureFn a h w := by
  have h0 : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, H.1⟩
  refine lt_of_not_ge fun hle => ?_
  have := (H.cap_le_iff hw h0).1 hle
  rw [H.2.2.2.1] at this
  exact absurd hOw (not_lt.2 this)

/-- `{w ∈ (O, a s] : φ w ≤ m} = (O, a m]`. -/
theorem LeftArc.Ioc_inter_preimage (H : LeftArc ν O h L a) {s m : ℝ} (hs : s ∈ Icc 0 h)
    (hm : m ∈ Icc 0 s) :
    Ioc O (a s) ∩ captureFn a h ⁻¹' Iic m = Ioc O (a m) := by
  have hm' : m ∈ Icc 0 h := ⟨hm.1, hm.2.trans hs.2⟩
  have has : a m ≤ a s := (H.2.2.1.le_iff_le hm' hs).2 hm.2
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨⟨hOw, hws⟩, hc⟩
    have hw : w ∈ Icc O 0 := ⟨hOw.le, hws.trans (H.mem hs).2⟩
    exact ⟨hOw, (H.cap_le_iff hw hm').1 hc⟩
  · rintro ⟨hOw, hwm⟩
    have hw : w ∈ Icc O 0 := ⟨hOw.le, hwm.trans (H.mem hm').2⟩
    exact ⟨⟨hOw, hwm.trans has⟩, (H.cap_le_iff hw hm').2 hwm⟩

theorem LeftArc.measure_Ioc (H : LeftArc ν O h L a) {m : ℝ} (hm : m ∈ Icc 0 h) :
    ν (Ioc O (a m)) = L m - L 0 := by
  have h0 : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, H.1⟩
  have hO : ν {O} = L 0 := by
    have := (H.2.2.2.2.2 0 h0).1
    rwa [H.2.2.2.1, Icc_self] at this
  have hsub : ({O} : Set ℝ) ⊆ Icc O (a m) := singleton_subset_iff.2 ⟨le_rfl, (H.mem hm).1⟩
  rw [← Icc_sdiff_left, measure_sdiff hsub (measurableSet_singleton O).nullMeasurableSet (by rw [hO]; exact (H.2.2.2.2.2 0 h0).2),
    hO, (H.2.2.2.2.2 m hm).1]

theorem LeftArc.cap_mem (H : LeftArc ν O h L a) {s : ℝ} (hs : s ∈ Icc 0 h) :
    ∀ w ∈ Ioc O (a s), captureFn a h w ∈ Icc 0 s := by
  intro w hw
  have hw' : w ∈ Icc O 0 := ⟨hw.1.le, hw.2.trans (H.mem hs).2⟩
  exact ⟨(H.cap hw').1.1, (H.cap_le_iff hw' hs).2 hw.2⟩

/-- **Left transport between two horizons.** -/
theorem left_map_eq {ν₁ ν₂ : Measure ℝ} {O₁ O₂ h₁ h₂ : ℝ} {L : ℝ → ℝ≥0∞} {a₁ a₂ : ℝ → ℝ}
    (H₁ : LeftArc ν₁ O₁ h₁ L a₁) (H₂ : LeftArc ν₂ O₂ h₂ L a₂) {s : ℝ} (hs₁ : s ∈ Icc 0 h₁)
    (hs₂ : s ∈ Icc 0 h₂) :
    (ν₁.restrict (Ioc O₁ (a₁ s))).map (captureFn a₁ h₁) =
      (ν₂.restrict (Ioc O₂ (a₂ s))).map (captureFn a₂ h₂) := by
  refine map_restrict_eq (measurable_captureFn H₁.1) (measurable_captureFn H₂.1) hs₁.1
    (H₁.cap_mem hs₁) (H₂.cap_mem hs₂) (F := fun m => L m - L 0) (fun m hm => ?_)
    (fun m hm => ?_) ?_
  · rw [H₁.Ioc_inter_preimage hs₁ hm, H₁.measure_Ioc ⟨hm.1, hm.2.trans hs₁.2⟩]
  · rw [H₂.Ioc_inter_preimage hs₂ hm, H₂.measure_Ioc ⟨hm.1, hm.2.trans hs₂.2⟩]
  · rw [H₁.measure_Ioc hs₁]
    exact ne_top_of_le_ne_top (H₁.2.2.2.2.2 s hs₁).2 tsub_le_self

end Left

section Right

variable {ν : Measure ℝ} {O h : ℝ} {L : ℝ → ℝ≥0∞} {b : ℝ → ℝ}

/-- The capture function of the right side (through the reflected position map `−b`). -/
def rcaptureFn (b : ℝ → ℝ) (h : ℝ) (w : ℝ) : ℝ := captureFn (fun r => -b r) h (-w)

theorem measurable_rcaptureFn {b : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h) : Measurable (rcaptureFn b h) :=
  (measurable_captureFn hh).comp measurable_neg

theorem RightArc.mem (H : RightArc ν O h L b) {r : ℝ} (hr : r ∈ Icc 0 h) : b r ∈ Icc 0 O := by
  obtain ⟨hh, -, hm, hb0, hbh, -⟩ := H
  refine ⟨?_, ?_⟩
  · rw [← hbh]; exact (hm.le_iff_ge ⟨hh, le_rfl⟩ hr).2 hr.2
  · rw [← hb0]; exact (hm.le_iff_ge hr ⟨le_rfl, hh⟩).2 hr.1

theorem RightArc.neg_mono (H : RightArc ν O h L b) : StrictMonoOn (fun r => -b r) (Icc 0 h) :=
  fun _ hx _ hy hxy => neg_lt_neg (H.2.2.1 hx hy hxy)

theorem RightArc.neg_mem (H : RightArc ν O h L b) {w : ℝ} (hw : w ∈ Icc 0 O) :
    -w ∈ Icc ((fun r => -b r) 0) ((fun r => -b r) h) := by
  simp only [H.2.2.2.1, H.2.2.2.2.1, neg_zero]
  exact ⟨neg_le_neg hw.2, neg_nonpos.2 hw.1⟩

theorem RightArc.cap (H : RightArc ν O h L b) {w : ℝ} (hw : w ∈ Icc 0 O) :
    rcaptureFn b h w ∈ Icc 0 h ∧ b (rcaptureFn b h w) = w := by
  obtain ⟨h1, h2⟩ := captureFn_spec H.1 H.2.1.neg H.neg_mono (H.neg_mem hw)
  exact ⟨h1, neg_injective h2⟩

theorem RightArc.cap_le_iff (H : RightArc ν O h L b) {w : ℝ} (hw : w ∈ Icc 0 O) {r : ℝ}
    (hr : r ∈ Icc 0 h) : rcaptureFn b h w ≤ r ↔ b r ≤ w := by
  exact (captureFn_le_iff (a := fun r => -b r) H.1 H.2.1.neg H.neg_mono (H.neg_mem hw) hr).trans
    neg_le_neg_iff

theorem RightArc.cap_pos (H : RightArc ν O h L b) {w : ℝ} (hw : w ∈ Icc 0 O) (hwO : w < O) :
    0 < rcaptureFn b h w := by
  have h0 : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, H.1⟩
  refine lt_of_not_ge fun hle => ?_
  have := (H.cap_le_iff hw h0).1 hle
  rw [H.2.2.2.1] at this
  exact absurd hwO (not_lt.2 this)

theorem RightArc.Ico_inter_preimage (H : RightArc ν O h L b) {s m : ℝ} (hs : s ∈ Icc 0 h)
    (hm : m ∈ Icc 0 s) :
    Ico (b s) O ∩ rcaptureFn b h ⁻¹' Iic m = Ico (b m) O := by
  have hm' : m ∈ Icc 0 h := ⟨hm.1, hm.2.trans hs.2⟩
  have hbs : b s ≤ b m := (H.2.2.1.le_iff_ge hs hm').2 hm.2
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ico]
  constructor
  · rintro ⟨⟨hsw, hwO⟩, hc⟩
    have hw : w ∈ Icc 0 O := ⟨(H.mem hs).1.trans hsw, hwO.le⟩
    exact ⟨(H.cap_le_iff hw hm').1 hc, hwO⟩
  · rintro ⟨hmw, hwO⟩
    have hw : w ∈ Icc 0 O := ⟨(H.mem hm').1.trans hmw, hwO.le⟩
    exact ⟨⟨hbs.trans hmw, hwO⟩, (H.cap_le_iff hw hm').2 hmw⟩

theorem RightArc.measure_Ico (H : RightArc ν O h L b) {m : ℝ} (hm : m ∈ Icc 0 h) :
    ν (Ico (b m) O) = L m - L 0 := by
  have h0 : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, H.1⟩
  have hO : ν {O} = L 0 := by
    have := (H.2.2.2.2.2 0 h0).1
    rwa [H.2.2.2.1, Icc_self] at this
  have hsub : ({O} : Set ℝ) ⊆ Icc (b m) O := singleton_subset_iff.2 ⟨(H.mem hm).2, le_rfl⟩
  rw [← Icc_sdiff_right, measure_sdiff hsub (measurableSet_singleton O).nullMeasurableSet (by rw [hO]; exact (H.2.2.2.2.2 0 h0).2),
    hO, (H.2.2.2.2.2 m hm).1]

theorem RightArc.cap_mem (H : RightArc ν O h L b) {s : ℝ} (hs : s ∈ Icc 0 h) :
    ∀ w ∈ Ico (b s) O, rcaptureFn b h w ∈ Icc 0 s := by
  intro w hw
  have hw' : w ∈ Icc 0 O := ⟨(H.mem hs).1.trans hw.1, hw.2.le⟩
  exact ⟨(H.cap hw').1.1, (H.cap_le_iff hw' hs).2 hw.1⟩

/-- **Right transport between two horizons.** -/
theorem right_map_eq {ν₁ ν₂ : Measure ℝ} {O₁ O₂ h₁ h₂ : ℝ} {L : ℝ → ℝ≥0∞} {b₁ b₂ : ℝ → ℝ}
    (H₁ : RightArc ν₁ O₁ h₁ L b₁) (H₂ : RightArc ν₂ O₂ h₂ L b₂) {s : ℝ} (hs₁ : s ∈ Icc 0 h₁)
    (hs₂ : s ∈ Icc 0 h₂) :
    (ν₁.restrict (Ico (b₁ s) O₁)).map (rcaptureFn b₁ h₁) =
      (ν₂.restrict (Ico (b₂ s) O₂)).map (rcaptureFn b₂ h₂) := by
  refine map_restrict_eq (measurable_rcaptureFn H₁.1) (measurable_rcaptureFn H₂.1) hs₁.1
    (H₁.cap_mem hs₁) (H₂.cap_mem hs₂) (F := fun m => L m - L 0) (fun m hm => ?_)
    (fun m hm => ?_) ?_
  · rw [H₁.Ico_inter_preimage hs₁ hm, H₁.measure_Ico ⟨hm.1, hm.2.trans hs₁.2⟩]
  · rw [H₂.Ico_inter_preimage hs₂ hm, H₂.measure_Ico ⟨hm.1, hm.2.trans hs₂.2⟩]
  · rw [H₁.measure_Ico hs₁]
    exact ne_top_of_le_ne_top (H₁.2.2.2.2.2 s hs₁).2 tsub_le_self

end Right

end F2
end QuantumZipper
