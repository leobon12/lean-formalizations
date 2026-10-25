import SupercriticalLQGUniqueness.B2.Median.HeatShift
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.LeftRightLim

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum

theorem compactPathInf_mono_sets (d : LSCMetric)
    {K K' A A' B B' : Set ℂ}
    (hK : K' ⊆ K) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    compactPathInf d K A B ≤ compactPathInf d K' A' B' := by
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hK' => le_iInf fun hA' =>
    le_iInf fun hB' => ?_
  exact compactPathInf_le_of_curve d K A B P a b hP
    (fun t ht => hK (hK' t ht)) (hA hA') (hB hB')

def upperPathInf (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) : ℝ≥0∞ :=
  compactPathInf d
    (V ∩ {z | s ≤ z.im})
    (A ∩ {z | s ≤ z.im})
    (B ∩ {z | s ≤ z.im})

def lowerPathInf (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) : ℝ≥0∞ :=
  compactPathInf d
    (V ∩ {z | z.im ≤ s})
    (A ∩ {z | z.im ≤ s})
    (B ∩ {z | z.im ≤ s})

theorem upperPathInf_monotone (d : LSCMetric) (V A B : Set ℂ) :
    Monotone (upperPathInf d V A B) := by
  intro s t hst
  apply compactPathInf_mono_sets d
  all_goals
    intro z hz
    exact ⟨hz.1, hst.trans hz.2⟩

theorem lowerPathInf_antitone (d : LSCMetric) (V A B : Set ℂ) :
    Antitone (lowerPathInf d V A B) := by
  intro s t hst
  apply compactPathInf_mono_sets d
  all_goals
    intro z hz
    exact ⟨hz.1, hz.2.trans hst⟩

theorem measurable_upperPathInf_fixed
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) (s : ℝ) :
    Measurable (fun d : LSCMetric => upperPathInf d V A B s) := by
  apply Uniqueness.Toolkit.CompactPathInfimum.compactPathInf_measurable
  · exact hV.inter_right (isClosed_le continuous_const Complex.continuous_im)
  · exact hA.inter_right (isClosed_le continuous_const Complex.continuous_im)
  · exact hB.inter_right (isClosed_le continuous_const Complex.continuous_im)

theorem measurable_lowerPathInf_fixed
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) (s : ℝ) :
    Measurable (fun d : LSCMetric => lowerPathInf d V A B s) := by
  apply Uniqueness.Toolkit.CompactPathInfimum.compactPathInf_measurable
  · exact hV.inter_right (isClosed_le Complex.continuous_im continuous_const)
  · exact hA.inter_right (isClosed_le Complex.continuous_im continuous_const)
  · exact hB.inter_right (isClosed_le Complex.continuous_im continuous_const)

theorem ae_continuousAt_upperPathInf (d : LSCMetric) (V A B : Set ℂ) :
    ∀ᵐ s : ℝ ∂volume, ContinuousAt (upperPathInf d V A B) s := by
  have hcount := (upperPathInf_monotone d V A B).countable_not_continuousAt
  filter_upwards [hcount.ae_notMem volume] with s hs
  exact not_not.mp hs

theorem ae_continuousAt_lowerPathInf (d : LSCMetric) (V A B : Set ℂ) :
    ∀ᵐ s : ℝ ∂volume, ContinuousAt (lowerPathInf d V A B) s := by
  have hcount := (lowerPathInf_antitone d V A B).countable_not_continuousAt
  filter_upwards [hcount.ae_notMem volume] with s hs
  exact not_not.mp hs

 


theorem exists_curve_of_compactPathInf_lt (d : LSCMetric)
    (K A B : Set ℂ) {L : ℝ≥0∞} (hL : compactPathInf d K A B < L) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ K) ∧ P a ∈ A ∧ P b ∈ B ∧ d.len P a b < L := by
  unfold compactPathInf at hL
  simp only [iInf_lt_iff] at hL
  obtain ⟨P, a, b, hP, hK, hA, hB, hlen⟩ := hL
  exact ⟨P, a, b, hP, hK, hA, hB, hlen⟩

 


theorem exists_upper_curve_of_rightContinuousWithinAt (d : LSCMetric)
    (V A B : Set ℂ) {L : ℝ≥0∞}
    (hcont : ContinuousWithinAt (upperPathInf d V A B) (Ioi 0) 0)
    (hL : upperPathInf d V A B 0 < L) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ V ∧ 0 < (P t).im) ∧
      P a ∈ A ∧ 0 < (P a).im ∧
      P b ∈ B ∧ 0 < (P b).im ∧ d.len P a b < L := by
  have hevent : ∀ᶠ s in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ),
      upperPathInf d V A B s < L :=
    hcont.eventually (isOpen_Iio.mem_nhds hL)
  obtain ⟨s, hs⟩ := (hevent.and self_mem_nhdsWithin).exists
  have hs0 : 0 < s := hs.2
  obtain ⟨P, a, b, hP, hK, hA, hB, hlen⟩ :=
    exists_curve_of_compactPathInf_lt d
      (V ∩ {z | s ≤ z.im}) (A ∩ {z | s ≤ z.im})
      (B ∩ {z | s ≤ z.im}) hs.1
  exact ⟨P, a, b, hP, (fun t ht => ⟨(hK t ht).1, hs0.trans_le (hK t ht).2⟩),
    hA.1, hs0.trans_le hA.2, hB.1, hs0.trans_le hB.2, hlen⟩

 

theorem exists_lower_curve_of_leftContinuousWithinAt (d : LSCMetric)
    (V A B : Set ℂ) {L : ℝ≥0∞}
    (hcont : ContinuousWithinAt (lowerPathInf d V A B) (Iio 1) 1)
    (hL : lowerPathInf d V A B 1 < L) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ V ∧ (P t).im < 1) ∧
      P a ∈ A ∧ (P a).im < 1 ∧
      P b ∈ B ∧ (P b).im < 1 ∧ d.len P a b < L := by
  have hevent : ∀ᶠ s in 𝓝[Set.Iio (1 : ℝ)] (1 : ℝ),
      lowerPathInf d V A B s < L :=
    hcont.eventually (isOpen_Iio.mem_nhds hL)
  obtain ⟨s, hs⟩ := (hevent.and self_mem_nhdsWithin).exists
  have hs1 : s < 1 := hs.2
  obtain ⟨P, a, b, hP, hK, hA, hB, hlen⟩ :=
    exists_curve_of_compactPathInf_lt d
      (V ∩ {z | z.im ≤ s}) (A ∩ {z | z.im ≤ s})
      (B ∩ {z | z.im ≤ s}) hs.1
  exact ⟨P, a, b, hP, (fun t ht => ⟨(hK t ht).1, (hK t ht).2.trans_lt hs1⟩),
    hA.1, hA.2.trans_lt hs1, hB.1, hB.2.trans_lt hs1, hlen⟩

theorem exists_upper_curve_of_continuousAt (d : LSCMetric)
    (V A B : Set ℂ) {L : ℝ≥0∞}
    (hcont : ContinuousAt (upperPathInf d V A B) 0)
    (hL : upperPathInf d V A B 0 < L) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ V ∧ 0 < (P t).im) ∧
      P a ∈ A ∧ 0 < (P a).im ∧
      P b ∈ B ∧ 0 < (P b).im ∧ d.len P a b < L :=
  exists_upper_curve_of_rightContinuousWithinAt d V A B hcont.continuousWithinAt hL

theorem exists_lower_curve_of_continuousAt (d : LSCMetric)
    (V A B : Set ℂ) {L : ℝ≥0∞}
    (hcont : ContinuousAt (lowerPathInf d V A B) 1)
    (hL : lowerPathInf d V A B 1 < L) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ V ∧ (P t).im < 1) ∧
      P a ∈ A ∧ (P a).im < 1 ∧
      P b ∈ B ∧ (P b).im < 1 ∧ d.len P a b < L :=
  exists_lower_curve_of_leftContinuousWithinAt d V A B hcont.continuousWithinAt hL

 


def upperLeftEnvelope (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, if (q : ℝ) < s then upperPathInf d V A B q else 0

 
def upperRightEnvelope (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) : ℝ≥0∞ :=
  ⨅ q : ℚ, if s < (q : ℝ) then upperPathInf d V A B q else ∞

 


theorem measurable_upperLeftEnvelope
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) :
    Measurable (fun p : LSCMetric × ℝ =>
      upperLeftEnvelope p.1 V A B p.2) := by
  unfold upperLeftEnvelope
  apply Measurable.iSup
  intro q
  have hq : Measurable (fun p : LSCMetric × ℝ =>
      upperPathInf p.1 V A B q) :=
    (measurable_upperPathInf_fixed hV hA hB q).comp measurable_fst
  exact Measurable.ite
    (measurableSet_lt measurable_const measurable_snd) hq measurable_const

theorem measurable_upperRightEnvelope
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) :
    Measurable (fun p : LSCMetric × ℝ =>
      upperRightEnvelope p.1 V A B p.2) := by
  unfold upperRightEnvelope
  apply Measurable.iInf
  intro q
  have hq : Measurable (fun p : LSCMetric × ℝ =>
      upperPathInf p.1 V A B q) :=
    (measurable_upperPathInf_fixed hV hA hB q).comp measurable_fst
  exact Measurable.ite
    (measurableSet_lt measurable_snd measurable_const) hq measurable_const

theorem measurableSet_upperEnvelope_jump
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) :
    MeasurableSet {p : LSCMetric × ℝ |
      upperLeftEnvelope p.1 V A B p.2 <
        upperRightEnvelope p.1 V A B p.2} :=
  measurableSet_lt (measurable_upperLeftEnvelope hV hA hB)
    (measurable_upperRightEnvelope hV hA hB)

 

theorem upperLeftEnvelope_eq_leftLim
    (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) :
    upperLeftEnvelope d V A B s =
      Function.leftLim (upperPathInf d V A B) s := by
  rw [(upperPathInf_monotone d V A B).leftLim_eq_sSup]
  rw [sSup_image]
  unfold upperLeftEnvelope
  apply le_antisymm
  · refine iSup_le fun q => ?_
    split_ifs with hq
    · exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hq le_rfl)
    · exact bot_le
  · refine iSup_le fun x => iSup_le fun hx => ?_
    obtain ⟨y, hxy, hys⟩ := exists_between (show x < s from hx)
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open
      isOpen_Ioo ⟨y, hxy, hys⟩
    have hqs : (q : ℝ) < s := hq.2
    calc
      upperPathInf d V A B x ≤ upperPathInf d V A B q :=
        (upperPathInf_monotone d V A B) (hq.1.le)
      _ ≤ ⨆ q : ℚ, if (q : ℝ) < s then upperPathInf d V A B q else 0 := by
        exact le_iSup_of_le q (by simp [hqs])

 
theorem upperRightEnvelope_eq_rightLim
    (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) :
    upperRightEnvelope d V A B s =
      Function.rightLim (upperPathInf d V A B) s := by
  rw [(upperPathInf_monotone d V A B).rightLim_eq_sInf]
  rw [sInf_image]
  unfold upperRightEnvelope
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => ?_
    obtain ⟨y, hsy, hyx⟩ := exists_between (show s < x from hx)
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open
      isOpen_Ioo ⟨y, hsy, hyx⟩
    have hsq : s < (q : ℝ) := hq.1
    calc
      (⨅ q : ℚ, if s < (q : ℝ) then upperPathInf d V A B q else ∞)
          ≤ upperPathInf d V A B q := by
            exact iInf_le_of_le q (by simp [hsq])
      _ ≤ upperPathInf d V A B x :=
        (upperPathInf_monotone d V A B) hq.2.le
  · refine le_iInf fun q => ?_
    split_ifs with hq
    · exact iInf_le_of_le (q : ℝ) (iInf_le_of_le hq le_rfl)
    · exact le_top

 

theorem upperEnvelope_jump_iff_not_continuousAt
    (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) :
    upperLeftEnvelope d V A B s < upperRightEnvelope d V A B s ↔
      ¬ ContinuousAt (upperPathInf d V A B) s := by
  rw [upperLeftEnvelope_eq_leftLim, upperRightEnvelope_eq_rightLim]
  let hm := upperPathInf_monotone d V A B
  have hle := hm.leftLim_le_rightLim (le_refl s)
  have hiff := hm.continuousAt_iff_leftLim_eq_rightLim (x := s)
  constructor
  · intro hlt hc
    exact (ne_of_lt hlt) (hiff.mp hc)
  · intro hn
    exact lt_of_le_of_ne hle (fun heq => hn (hiff.mpr heq))

 



theorem ae_height_ae_continuousAt_upperPathInf
    (μ : Measure LSCMetric) [SFinite μ]
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) :
    ∀ᵐ s : ℝ ∂volume, ∀ᵐ d ∂μ,
      ContinuousAt (upperPathInf d V A B) s := by
  have hmeas : MeasurableSet {p : LSCMetric × ℝ |
      ContinuousAt (upperPathInf p.1 V A B) p.2} := by
    have heq : {p : LSCMetric × ℝ |
        ContinuousAt (upperPathInf p.1 V A B) p.2} =
        {p : LSCMetric × ℝ |
          ¬ upperLeftEnvelope p.1 V A B p.2 <
            upperRightEnvelope p.1 V A B p.2} := by
      ext p
      simpa only [Set.mem_ofPred_eq, not_not] using
        (upperEnvelope_jump_iff_not_continuousAt p.1 V A B p.2).not.symm
    rw [heq]
    exact (measurableSet_upperEnvelope_jump hV hA hB).compl
  have hfirst : ∀ᵐ d ∂μ, ∀ᵐ s : ℝ ∂volume,
      ContinuousAt (upperPathInf d V A B) s := by
    filter_upwards [] with d
    exact ae_continuousAt_upperPathInf d V A B
  exact (Measure.ae_ae_comm hmeas).mp hfirst

 

def lowerLeftEnvelope (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) : ℝ≥0∞ :=
  ⨅ q : ℚ, if (q : ℝ) < s then lowerPathInf d V A B q else ∞

def lowerRightEnvelope (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, if s < (q : ℝ) then lowerPathInf d V A B q else 0

theorem measurable_lowerLeftEnvelope
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) :
    Measurable (fun p : LSCMetric × ℝ =>
      lowerLeftEnvelope p.1 V A B p.2) := by
  unfold lowerLeftEnvelope
  apply Measurable.iInf
  intro q
  have hq : Measurable (fun p : LSCMetric × ℝ =>
      lowerPathInf p.1 V A B q) :=
    (measurable_lowerPathInf_fixed hV hA hB q).comp measurable_fst
  exact Measurable.ite
    (measurableSet_lt measurable_const measurable_snd) hq measurable_const

theorem measurable_lowerRightEnvelope
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) :
    Measurable (fun p : LSCMetric × ℝ =>
      lowerRightEnvelope p.1 V A B p.2) := by
  unfold lowerRightEnvelope
  apply Measurable.iSup
  intro q
  have hq : Measurable (fun p : LSCMetric × ℝ =>
      lowerPathInf p.1 V A B q) :=
    (measurable_lowerPathInf_fixed hV hA hB q).comp measurable_fst
  exact Measurable.ite
    (measurableSet_lt measurable_snd measurable_const) hq measurable_const

theorem lowerLeftEnvelope_eq_leftLim
    (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) :
    lowerLeftEnvelope d V A B s =
      Function.leftLim (lowerPathInf d V A B) s := by
  have hlim := (lowerPathInf_antitone d V A B).dual_right.leftLim_eq_sSup (x := s)
  change Function.leftLim (lowerPathInf d V A B) s =
    sInf (lowerPathInf d V A B '' Iio s) at hlim
  rw [hlim, sInf_image]
  unfold lowerLeftEnvelope
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => ?_
    obtain ⟨y, hxy, hys⟩ := exists_between (show x < s from hx)
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open
      isOpen_Ioo ⟨y, hxy, hys⟩
    have hqs : (q : ℝ) < s := hq.2
    calc
      (⨅ q : ℚ, if (q : ℝ) < s then lowerPathInf d V A B q else ∞)
          ≤ lowerPathInf d V A B q := iInf_le_of_le q (by simp [hqs])
      _ ≤ lowerPathInf d V A B x :=
        (lowerPathInf_antitone d V A B) hq.1.le
  · refine le_iInf fun q => ?_
    split_ifs with hq
    · exact iInf_le_of_le (q : ℝ) (iInf_le_of_le hq le_rfl)
    · exact le_top

theorem lowerRightEnvelope_eq_rightLim
    (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) :
    lowerRightEnvelope d V A B s =
      Function.rightLim (lowerPathInf d V A B) s := by
  have hlim := (lowerPathInf_antitone d V A B).dual_right.rightLim_eq_sInf (x := s)
  change Function.rightLim (lowerPathInf d V A B) s =
    sSup (lowerPathInf d V A B '' Ioi s) at hlim
  rw [hlim, sSup_image]
  unfold lowerRightEnvelope
  apply le_antisymm
  · refine iSup_le fun q => ?_
    split_ifs with hq
    · exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hq le_rfl)
    · exact bot_le
  · refine iSup_le fun x => iSup_le fun hx => ?_
    obtain ⟨y, hsy, hyx⟩ := exists_between (show s < x from hx)
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open
      isOpen_Ioo ⟨y, hsy, hyx⟩
    have hsq : s < (q : ℝ) := hq.1
    calc
      lowerPathInf d V A B x ≤ lowerPathInf d V A B q :=
        (lowerPathInf_antitone d V A B) hq.2.le
      _ ≤ ⨆ q : ℚ, if s < (q : ℝ) then lowerPathInf d V A B q else 0 :=
        le_iSup_of_le q (by simp [hsq])

theorem lowerEnvelope_jump_iff_not_continuousAt
    (d : LSCMetric) (V A B : Set ℂ) (s : ℝ) :
    lowerRightEnvelope d V A B s < lowerLeftEnvelope d V A B s ↔
      ¬ ContinuousAt (lowerPathInf d V A B) s := by
  rw [lowerLeftEnvelope_eq_leftLim, lowerRightEnvelope_eq_rightLim]
  let hm := (lowerPathInf_antitone d V A B).dual_right
  have hle := hm.leftLim_le_rightLim (le_refl s)
  have hiff := hm.continuousAt_iff_leftLim_eq_rightLim (x := s)
  constructor
  · intro hlt hc
    exact (ne_of_lt hlt) (hiff.mp hc).symm
  · intro hn
    exact lt_of_le_of_ne hle (fun heq => hn (hiff.mpr heq.symm))

theorem ae_height_ae_continuousAt_lowerPathInf
    (μ : Measure LSCMetric) [SFinite μ]
    {V A B : Set ℂ} (hV : IsCompact V) (hA : IsCompact A)
    (hB : IsCompact B) :
    ∀ᵐ s : ℝ ∂volume, ∀ᵐ d ∂μ,
      ContinuousAt (lowerPathInf d V A B) s := by
  have hmeas : MeasurableSet {p : LSCMetric × ℝ |
      ContinuousAt (lowerPathInf p.1 V A B) p.2} := by
    have heq : {p : LSCMetric × ℝ |
        ContinuousAt (lowerPathInf p.1 V A B) p.2} =
        {p : LSCMetric × ℝ |
          ¬ lowerRightEnvelope p.1 V A B p.2 <
            lowerLeftEnvelope p.1 V A B p.2} := by
      ext p
      simpa only [Set.mem_ofPred_eq, not_not] using
        (lowerEnvelope_jump_iff_not_continuousAt p.1 V A B p.2).not.symm
    rw [heq]
    exact (measurableSet_lt (measurable_lowerRightEnvelope hV hA hB)
      (measurable_lowerLeftEnvelope hV hA hB)).compl
  have hfirst : ∀ᵐ d ∂μ, ∀ᵐ s : ℝ ∂volume,
      ContinuousAt (lowerPathInf d V A B) s := by
    filter_upwards [] with d
    exact ae_continuousAt_lowerPathInf d V A B
  exact (Measure.ae_ae_comm hmeas).mp hfirst

end SupercriticalLQGUniqueness.B2.Median
