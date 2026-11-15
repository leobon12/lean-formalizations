import InteractingSLE.Foundations.Strip.SLE
import InteractingSLE.Spec.Sec2.RestartLaw
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# Live strip events and progressive regularization on the A.1 reference space

Continuity before the lifetime is required at every sample. The progressive version
already constructed in `Sec2.Restart` is killed again at the lifetime, so it is zero
afterwards and agrees with the original process at every earlier time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RefCD

open Sec2.Restart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ζ : Ω → ℝ≥0∞} {W V : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0}

/-- A countable closed-inequality test for strict separation on a compact prefix. -/
theorem isStripLife_iff_nnrat {w v : ℝ≥0 → ℝ} {z : ℝ≥0∞} {t : ℝ≥0}
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < z})
    (hv : ContinuousOn v {s | (s : ℝ≥0∞) < z}) :
    Strip.IsStripLife w v z t ↔ (t : ℝ≥0∞) < z ∧
      ∃ n : ℕ, ∀ q : ℚ≥0,
        1 / (n + 1 : ℝ) ≤ w (min (q : ℝ≥0) t) - v (min (q : ℝ≥0) t) := by
  constructor
  · rintro ⟨ht, hgap⟩
    have hsub : Icc (0 : ℝ≥0) t ⊆ {s | (s : ℝ≥0∞) < z} :=
      fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans_lt ht
    obtain ⟨c, hc, hb⟩ := isCompact_Icc.exists_forall_le'
      ((hw.mono hsub).sub (hv.mono hsub))
      (fun s hs => sub_pos.2 (hgap s hs.2))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
    exact ⟨ht, n, fun q => hn.le.trans (hb _ ⟨zero_le, min_le_right _ _⟩)⟩
  · rintro ⟨ht, n, hn⟩
    have hsub : ∀ s : ℝ≥0, (min s t : ℝ≥0∞) < z :=
      fun s => (ENNReal.coe_le_coe.2 (min_le_right s t)).trans_lt ht
    have hc : Continuous (fun s => w (min s t) - v (min s t)) :=
      (hw.comp_continuous (continuous_id.min continuous_const) hsub).sub
        (hv.comp_continuous (continuous_id.min continuous_const) hsub)
    have hb : ∀ s, 1 / (n + 1 : ℝ) ≤ w (min s t) - v (min s t) := by
      intro s
      exact le_on_closure (s := range ((↑) : ℚ≥0 → ℝ≥0))
        (by rintro _ ⟨q, rfl⟩; exact hn q) continuous_const.continuousOn
        hc.continuousOn (LocalExt.dense_range_coe_nnrat s)
    refine ⟨ht, fun s hs => sub_pos.1
      (lt_of_lt_of_le (show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity) ?_)⟩
    simpa only [min_eq_left hs] using hb s

/-- The survival event at a finite stopping time belongs to its stopped σ-algebra. -/
theorem measurableSet_alive (ha : AdaptedBefore 𝓕 ζ W)
    (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) :
    MeasurableSet[hτ.measurableSpace] {ω | (τ ω : ℝ≥0∞) < ζ ω} := by
  have h := (Ito.isStoppingTime_lifetime ha).measurableSet_stopping_time_le hτ
  convert h.compl using 1
  ext ω
  change (τ ω : ℝ≥0∞) < ζ ω ↔ ¬ ζ ω ≤ (τ ω : ℝ≥0∞)
  exact lt_iff_not_ge

/-- Progressive values at every stopped rational prefix are measurable at the original stop. -/
theorem measurable_progVersion_min (ha : AdaptedBefore 𝓕 ζ W)
    (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) (q : ℝ≥0) :
    Measurable[hτ.measurableSpace] fun ω => progVersion ζ W (min q (τ ω)) ω := by
  have hmin : IsStoppingTime 𝓕 fun ω => (min q (τ ω) : WithTop ℝ≥0) := by
    simpa only [WithTop.coe_min] using (isStoppingTime_const 𝓕 q).min hτ
  exact (measurable_eval_stop (isStronglyProgressive_progVersion ha) hmin).mono
    (hmin.measurableSpace_mono hτ (fun ω => WithTop.coe_le_coe.2 (min_le_right q (τ ω)))) le_rfl

/-- The exact strip live event is measurable at the stop on an everywhere regular space. -/
theorem measurableSet_isStripLife (haW : AdaptedBefore 𝓕 ζ W)
    (haV : AdaptedBefore 𝓕 ζ V)
    (hcW : ∀ ω, ContinuousOn (W · ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hcV : ∀ ω, ContinuousOn (V · ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) :
    MeasurableSet[hτ.measurableSpace]
      {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) (τ ω)} := by
  have he : {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) (τ ω)} =
      {ω | (τ ω : ℝ≥0∞) < ζ ω} ∩
      ⋃ n : ℕ, ⋂ q : ℚ≥0, {ω | 1 / (n + 1 : ℝ) ≤
        progVersion ζ W (min (q : ℝ≥0) (τ ω)) ω -
        progVersion ζ V (min (q : ℝ≥0) (τ ω)) ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
    rw [isStripLife_iff_nnrat (hcW ω) (hcV ω)]
    apply and_congr_right
    intro ht
    have hmin : ∀ q : ℚ≥0, (min (q : ℝ≥0) (τ ω) : ℝ≥0∞) < ζ ω :=
      fun q => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt ht
    simp only [progVersion_eq (hcW ω) (hmin _), progVersion_eq (hcV ω) (hmin _)]
  rw [he]
  refine (measurableSet_alive haW hτ).inter (MeasurableSet.iUnion fun n =>
    MeasurableSet.iInter fun q => ?_)
  exact measurableSet_le measurable_const
    ((measurable_progVersion_min haW hτ q).sub (measurable_progVersion_min haV hτ q))

/-- A progressive version equal to the original before the lifetime and zero afterwards. -/
def regularized (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then progVersion ζ X t ω else 0

/-- The regularization agrees at every live time of every continuous sample. -/
theorem regularized_eq {ω : Ω} (hc : ContinuousOn (W · ω) {s | (s : ℝ≥0∞) < ζ ω})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    regularized ζ W t ω = W t ω := by
  simp only [regularized, ht, ↓reduceIte, progVersion_eq hc ht]

/-- The regularized process is zero at and after its lifetime. -/
theorem regularized_eq_zero {ω : Ω} {t : ℝ≥0} (ht : ζ ω ≤ (t : ℝ≥0∞)) :
    regularized ζ W t ω = 0 := by
  simp only [regularized, not_lt.2 ht, ↓reduceIte]

/-- Killing a progressive process at a stopping lifetime preserves progressiveness. -/
theorem isStronglyProgressive_regularized (ha : AdaptedBefore 𝓕 ζ W) :
    IsStronglyProgressive 𝓕 (regularized ζ W) := by
  intro t
  have hζ := Ito.isStoppingTime_lifetime ha
  have hm : Measurable[𝓕 t] (fun ω => min (ζ ω : WithTop ℝ≥0) t) :=
    (hζ.min_const t).measurable_of_le (fun _ => min_le_right _ _)
  have hlt : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    convert (hζ.measurableSet_le t).compl using 1
    ext ω
    change (t : ℝ≥0∞) < ζ ω ↔ ¬ ζ ω ≤ (t : ℝ≥0∞)
    exact lt_iff_not_ge
  have hset : MeasurableSet[(inferInstance : MeasurableSpace (Iic t)).prod (𝓕 t)]
      {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2} := by
    have he : {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2} =
        {p | (p.1.val : WithTop ℝ≥0) < min (ζ p.2 : WithTop ℝ≥0) t} ∪
        {p | (t : ℝ≥0∞) < ζ p.2} := by
      ext p
      change (p.1.val : WithTop ℝ≥0) < ζ p.2 ↔
        (p.1.val : WithTop ℝ≥0) < min (ζ p.2 : WithTop ℝ≥0) t ∨
        (t : WithTop ℝ≥0) < ζ p.2
      constructor
      · intro h
        have hpt : p.1.val ≤ t := p.1.property
        rcases hpt.lt_or_eq with hpt | hpt
        · exact Or.inl (lt_min h (WithTop.coe_lt_coe.2 hpt))
        · exact Or.inr (by simpa only [hpt] using h)
      · rintro (h | h)
        · exact (lt_min_iff.1 h).1
        · exact (WithTop.coe_le_coe.2 p.1.property).trans_lt h
    rw [he]
    exact (measurableSet_lt (WithTop.measurable_coe.comp
      (measurable_subtype_coe.comp measurable_fst)) (hm.comp measurable_snd)).union
      (measurable_snd hlt)
  exact StronglyMeasurable.ite hset (isStronglyProgressive_progVersion ha t)
    stronglyMeasurable_const

/-- In particular every random starting position read from the regularization is measurable. -/
theorem measurable_regularized_stop (ha : AdaptedBefore 𝓕 ζ W)
    (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) :
    Measurable[hτ.measurableSpace] fun ω => regularized ζ W (τ ω) ω :=
  measurable_eval_stop (isStronglyProgressive_regularized ha) hτ

end InteractingSLE.ZhanGT4.A1RefCD
