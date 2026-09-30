import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# LR-CV: length reparametrization of an atomless, interval-positive measure

Node **LR-CV** of `handoff/E-PLAN-2.md` (E-branch blueprint `blueprint/E_BRANCH_BLUEPRINT.md`,
E-SM-inst (a): the change of variables `ℓ = ν[a, x]` used in the proof of Sheffield,
arXiv:1012.4797, Lemma 5.6 (quantum length along the zipper)).

For a measure `μ` on `ℝ` without atoms, positive on every nonempty open interval and finite on
`[a, b]`, write `L = μ[a, b]` and `xOf μ a ℓ = sup {x ≥ a | μ[a, x] ≤ ℓ}`. Then
`∫⁻_{[a,b]} g dμ = ∫⁻_{[0, L)} g (xOf μ a ℓ) dℓ` for every measurable `g ≥ 0`
(`lintegral_Icc_eq_lintegral_xOf`).

Proof (own elementary proof, the standard "distribution function pushes `μ` to Lebesgue"
argument; cost rule of `AGENT_GUIDE.md`): the distribution function
`F x = μ([a, b] ∩ (−∞, x])` is continuous (no atoms), strictly increasing on `[a, b]` (positive on
intervals), `0` below `a` and `L` above `b`; hence `F_* (μ|[a,b]) = Leb|[0,L)` (checked on the
half-lines `(−∞, c]`, via the intermediate value theorem), and `xOf μ a (F x) = x` on `[a, b]`.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace ESM

/-- `xOf μ a ℓ = sup {x ≥ a | μ[a, x] ≤ ℓ}`: the point at `μ`-length `ℓ` from `a`. -/
noncomputable def xOf (μ : Measure ℝ) (a ℓ : ℝ) : ℝ :=
  sSup {x | a ≤ x ∧ μ (Icc a x) ≤ ENNReal.ofReal ℓ}

/-- The distribution function `x ↦ μ([a,b] ∩ (−∞, x])` (real-valued). -/
noncomputable def lenFn (μ : Measure ℝ) (a b : ℝ) (x : ℝ) : ℝ :=
  (μ.restrict (Icc a b) (Iic x)).toReal

section LRCV

variable {μ : Measure ℝ} {a b : ℝ}

lemma lrcv_restrict_Iic {x : ℝ} (hx : x ≤ b) :
    μ.restrict (Icc a b) (Iic x) = μ (Icc a x) := by
  rw [Measure.restrict_apply measurableSet_Iic]
  congr 1
  ext y
  simp only [mem_inter_iff, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hx⟩

lemma lrcv_measure_lt (hpos : ∀ u v, u < v → 0 < μ (Ioo u v)) {x y : ℝ} (hx : a ≤ x)
    (hxy : x < y) (hfin : μ (Icc a x) ≠ ⊤) : μ (Icc a x) < μ (Icc a y) := by
  have hdisj : Disjoint (Icc a x) (Ioo x y) :=
    Set.disjoint_left.2 fun z h1 h2 => absurd h1.2 (not_le.2 h2.1)
  calc μ (Icc a x) < μ (Icc a x) + μ (Ioo x y) := ENNReal.lt_add_right hfin (hpos x y hxy).ne'
    _ = μ (Icc a x ∪ Ioo x y) := (measure_union hdisj measurableSet_Ioo).symm
    _ ≤ μ (Icc a y) := measure_mono (union_subset (Icc_subset_Icc_right hxy.le)
        fun z hz => ⟨hx.trans hz.1.le, hz.2.le⟩)

lemma lrcv_isFinite (hfin : μ (Icc a b) < ⊤) : IsFiniteMeasure (μ.restrict (Icc a b)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩

lemma monotone_lenFn (hfin : μ (Icc a b) < ⊤) : Monotone (lenFn μ a b) := by
  have := lrcv_isFinite hfin
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.2 hxy))

lemma lenFn_le (hfin : μ (Icc a b) < ⊤) (x : ℝ) : lenFn μ a b x ≤ (μ (Icc a b)).toReal := by
  rw [← Measure.restrict_apply_univ]
  exact ENNReal.toReal_mono (by rw [Measure.restrict_apply_univ]; exact hfin.ne)
    (measure_mono (subset_univ _))

lemma lenFn_of_ge {x : ℝ} (hx : b ≤ x) : lenFn μ a b x = (μ (Icc a b)).toReal := by
  unfold lenFn
  rw [Measure.restrict_apply measurableSet_Iic,
    Set.inter_eq_right.2 (Icc_subset_Iic_self.trans (Iic_subset_Iic.2 hx))]

lemma lenFn_of_le {x : ℝ} (hx : x ≤ b) : lenFn μ a b x = (μ (Icc a x)).toReal := by
  unfold lenFn; rw [lrcv_restrict_Iic hx]

lemma lenFn_strictMonoOn (hpos : ∀ u v, u < v → 0 < μ (Ioo u v)) (hfin : μ (Icc a b) < ⊤)
    {x y : ℝ} (hx : a ≤ x) (hxy : x < y) (hy : y ≤ b) : lenFn μ a b x < lenFn μ a b y := by
  have hyf : μ (Icc a y) ≠ ⊤ := (lt_of_le_of_lt (measure_mono (Icc_subset_Icc_right hy)) hfin).ne
  rw [lenFn_of_le (hxy.le.trans hy), lenFn_of_le hy]
  exact ENNReal.toReal_strict_mono hyf
    (lrcv_measure_lt hpos hx hxy (ne_top_of_le_ne_top hyf (measure_mono
      (Icc_subset_Icc_right hxy.le))))

lemma continuous_lenFn (hatom : ∀ x, μ {x} = 0) (hfin : μ (Icc a b) < ⊤) :
    Continuous (lenFn μ a b) := by
  set ν := μ.restrict (Icc a b) with hν
  have := lrcv_isFinite hfin
  have : NullSingletonClass ν := ⟨fun x => le_antisymm ((Measure.restrict_apply_le _ _).trans
    (hatom x).le) bot_le⟩
  rw [continuous_iff_continuousAt]
  intro z
  have hc : Tendsto (fun z' : ℝ => |z' - z|) (𝓝 z) (𝓝 0) := by
    simpa using (continuous_sub_right z).abs.tendsto z
  have ht := (tendsto_measure_Icc ν z).comp hc
  have ht' : Tendsto (fun z' => (ν (Icc (z - |z' - z|) (z + |z' - z|))).toReal) (𝓝 z) (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  have hsub : ∀ z' : ℝ, ∀ u v : ℝ, z - |z' - z| ≤ u → v ≤ z + |z' - z| →
      Iic v ⊆ Iic u ∪ Icc (z - |z' - z|) (z + |z' - z|) := by
    intro z' u v h1 h2 y hy
    by_cases hyu : y ≤ u
    · exact Or.inl hyu
    · simp only [mem_Iic] at hy hyu
      exact Or.inr ⟨by linarith, by linarith⟩
  have hb : ∀ z' : ℝ, |lenFn μ a b z' - lenFn μ a b z| ≤
      (ν (Icc (z - |z' - z|) (z + |z' - z|))).toReal := by
    intro z'
    have e1 : ν (Iic z') ≤ ν (Iic z) + ν (Icc (z - |z' - z|) (z + |z' - z|)) :=
      (measure_mono (hsub z' z z' (by linarith [abs_nonneg (z' - z)])
        (by linarith [le_abs_self (z' - z)]))).trans (measure_union_le _ _)
    have e2 : ν (Iic z) ≤ ν (Iic z') + ν (Icc (z - |z' - z|) (z + |z' - z|)) :=
      (measure_mono (hsub z' z' z (by linarith [neg_abs_le (z' - z)])
        (by linarith [abs_nonneg (z' - z)]))).trans (measure_union_le _ _)
    have r1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      measure_ne_top _ _⟩) e1
    have r2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      measure_ne_top _ _⟩) e2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at r1 r2
    unfold lenFn
    rw [abs_sub_le_iff]
    constructor <;> linarith
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun z' => by rw [Real.dist_eq]; exact hb z') ht'

lemma lenFn_left (hab : a ≤ b) (hatom : ∀ x, μ {x} = 0) : lenFn μ a b a = 0 := by
  rw [lenFn_of_le hab, Icc_self, hatom, ENNReal.toReal_zero]

/-- `F_* (μ|[a,b]) = Leb|[0, L)`. -/
lemma map_lenFn (hab : a ≤ b) (hatom : ∀ x, μ {x} = 0)
    (hpos : ∀ u v, u < v → 0 < μ (Ioo u v)) (hfin : μ (Icc a b) < ⊤) :
    (μ.restrict (Icc a b)).map (lenFn μ a b) =
      volume.restrict (Ico 0 (μ (Icc a b)).toReal) := by
  have := lrcv_isFinite hfin
  set L := (μ (Icc a b)).toReal with hL
  have hFm : Measurable (lenFn μ a b) := (monotone_lenFn hfin).measurable
  refine Measure.ext_of_Iic _ _ fun c => ?_
  rw [Measure.map_apply hFm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge c 0 with hc | hc
  · have h1 : lenFn μ a b ⁻¹' Iic c = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact hc.trans_le ENNReal.toReal_nonneg
    have h2 : Iic c ∩ Ico 0 L = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [h1, h2, measure_empty, measure_empty]
  rcases le_or_gt L c with hLc | hLc
  · have h1 : lenFn μ a b ⁻¹' Iic c = univ :=
      eq_univ_of_forall fun y => (lenFn_le hfin y).trans hLc
    have h2 : Iic c ∩ Ico 0 L = Ico 0 L :=
      Set.inter_eq_right.2 fun y hy => (hy.2.le.trans hLc : y ≤ c)
    rw [h1, h2, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero, hL,
      ENNReal.ofReal_toReal hfin.ne]
  · obtain ⟨x, hx, hFx⟩ : ∃ x ∈ Icc a b, lenFn μ a b x = c := by
      have := intermediate_value_Icc hab (continuous_lenFn hatom hfin).continuousOn
      rw [lenFn_left hab hatom, lenFn_of_ge le_rfl] at this
      exact this ⟨hc, hLc.le⟩
    have h1 : lenFn μ a b ⁻¹' Iic c = Iic x := by
      ext y
      simp only [mem_preimage, mem_Iic]
      constructor
      · intro hy
        by_contra hxy
        push Not at hxy
        rcases le_or_gt y b with hyb | hyb
        · have := lenFn_strictMonoOn hpos hfin hx.1 hxy hyb; linarith
        · rw [lenFn_of_ge hyb.le] at hy; linarith
      · intro hy; exact hFx ▸ monotone_lenFn hfin hy
    have h2 : Iic c ∩ Ico 0 L = Icc 0 c := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans_lt hLc⟩
    rw [h1, h2, Real.volume_Icc, sub_zero, ← hFx, lenFn, ENNReal.ofReal_toReal
      (measure_ne_top _ _)]

lemma xOf_lenFn (hpos : ∀ u v, u < v → 0 < μ (Ioo u v)) (hfin : μ (Icc a b) < ⊤) {x : ℝ}
    (hx : x ∈ Icc a b) : xOf μ a (lenFn μ a b x) = x := by
  have hxf : μ (Icc a x) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (Icc_subset_Icc_right hx.2)) hfin).ne
  unfold xOf
  rw [lenFn_of_le hx.2, ENNReal.ofReal_toReal hxf]
  refine IsGreatest.csSup_eq ⟨⟨hx.1, le_rfl⟩, fun y hy => ?_⟩
  by_contra hxy
  push Not at hxy
  exact absurd hy.2 (not_le.2 (lrcv_measure_lt hpos hx.1 hxy hxf))

lemma monotoneOn_xOf (hatom : ∀ x, μ {x} = 0) (hfin : μ (Icc a b) < ⊤) :
    MonotoneOn (xOf μ a) (Ico 0 (μ (Icc a b)).toReal) := by
  intro ℓ hℓ ℓ' hℓ' hle
  unfold xOf
  refine csSup_le_csSup ⟨b, fun y hy => ?_⟩ ⟨a, le_rfl, by rw [Icc_self, hatom]; exact bot_le⟩
    fun y hy => ⟨hy.1, hy.2.trans (ENNReal.ofReal_le_ofReal hle)⟩
  by_contra hyb
  push Not at hyb
  have h1 : μ (Icc a b) ≤ μ (Icc a y) := measure_mono (Icc_subset_Icc_right hyb.le)
  have h2 : ENNReal.ofReal ℓ' < μ (Icc a b) := by
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff (hℓ'.1.trans_lt hℓ'.2)).2 hℓ'.2
  exact absurd hy.2 (not_le.2 (h2.trans_le h1))

/-- **LR-CV.** For `μ` atomless, positive on nonempty open intervals and finite on `[a, b]`, and
`g ≥ 0` measurable: `∫⁻_{[a,b]} g dμ = ∫⁻_{[0, μ[a,b])} g (xOf μ a ℓ) dℓ`. -/
theorem lintegral_Icc_eq_lintegral_xOf (μ : Measure ℝ) (a b : ℝ) (hab : a ≤ b)
    (hatom : ∀ x, μ {x} = 0) (hpos : ∀ u v, u < v → 0 < μ (Ioo u v)) (hfin : μ (Icc a b) < ⊤)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in Icc a b, g x ∂μ = ∫⁻ ℓ in Ico 0 (μ (Icc a b)).toReal, g (xOf μ a ℓ) := by
  have hmap := map_lenFn hab hatom hpos hfin
  have hFm : Measurable (lenFn μ a b) := (monotone_lenFn hfin).measurable
  have hae : AEMeasurable (fun ℓ => g (xOf μ a ℓ))
      (volume.restrict (Ico 0 (μ (Icc a b)).toReal)) :=
    hg.comp_aemeasurable (aemeasurable_restrict_of_monotoneOn measurableSet_Ico
      (monotoneOn_xOf hatom hfin))
  rw [← hmap] at hae ⊢
  rw [lintegral_map' hae hFm.aemeasurable]
  exact (setLIntegral_congr_fun measurableSet_Icc fun x hx => by
    simp only [xOf_lenFn hpos hfin hx]).symm

lemma lenFn_xOf (hab : a ≤ b) (hatom : ∀ x, μ {x} = 0) (hpos : ∀ u v, u < v → 0 < μ (Ioo u v))
    (hfin : μ (Icc a b) < ⊤) {ℓ : ℝ} (hℓ : ℓ ∈ Ico 0 (μ (Icc a b)).toReal) :
    lenFn μ a b (xOf μ a ℓ) = ℓ := by
  obtain ⟨x, hx, hFx⟩ : ∃ x ∈ Icc a b, lenFn μ a b x = ℓ := by
    have := intermediate_value_Icc hab (continuous_lenFn hatom hfin).continuousOn
    rw [lenFn_left hab hatom, lenFn_of_ge le_rfl] at this
    exact this ⟨hℓ.1, hℓ.2.le⟩
  rw [← hFx, xOf_lenFn hpos hfin hx]

/-- **LR-CV** for an arbitrary (not necessarily measurable) `g ≥ 0` (lower integrals). -/
theorem lintegral_Icc_eq_lintegral_xOf' (μ : Measure ℝ) (a b : ℝ) (hab : a ≤ b)
    (hatom : ∀ x, μ {x} = 0) (hpos : ∀ u v, u < v → 0 < μ (Ioo u v)) (hfin : μ (Icc a b) < ⊤)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Icc a b, g x ∂μ = ∫⁻ ℓ in Ico 0 (μ (Icc a b)).toReal, g (xOf μ a ℓ) := by
  apply le_antisymm
  · obtain ⟨g', hg'm, hg'le, hg'eq⟩ :=
      exists_measurable_le_lintegral_eq (μ := μ.restrict (Icc a b)) g
    rw [hg'eq, lintegral_Icc_eq_lintegral_xOf μ a b hab hatom hpos hfin g' hg'm]
    exact lintegral_mono fun ℓ => hg'le _
  · obtain ⟨h', hh'm, hh'le, hh'eq⟩ :=
      exists_measurable_le_lintegral_eq (μ := volume.restrict (Ico 0 (μ (Icc a b)).toReal))
        (fun ℓ => g (xOf μ a ℓ))
    have hFm : Measurable (lenFn μ a b) := (monotone_lenFn hfin).measurable
    rw [hh'eq, ← map_lenFn hab hatom hpos hfin, lintegral_map hh'm hFm]
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun x hx => ?_))
    have : h' (lenFn μ a b x) ≤ g (xOf μ a (lenFn μ a b x)) := hh'le (lenFn μ a b x)
    rwa [xOf_lenFn hpos hfin hx] at this

end LRCV

end ESM
end QuantumZipper
