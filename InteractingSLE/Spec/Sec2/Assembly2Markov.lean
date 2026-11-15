/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# Brownian increments are independent of every event determined by the past up to null paths

Packet PROVE-SEC2-PATCH2 (Theorem 2.2, existence: strong solutions are adapted). On the space
`CPath` of continuous paths with a measure under which the coordinate process is a pre-Brownian
motion, let `G` be a measurable set of full measure. An event `A` is *saturated at time `s` on `G`*
if, for two paths of `G` that agree on `[0, s]`, either both or none lie in `A`. Then `A` is almost
surely equal to an event of the past `σ(B_r, r ≤ s)` (`ae_eq_preimage_pastC_of_saturated`), and so
it is independent of every increment `B_t − B_s`, `t ≥ s` (`indep_increment_of_le_satSpace`).

Proof (added here; it is the measurability half of the Yamada–Watanabe theorem): decompose a path
into its past `pastC s f = f(· ∧ s)` and its increments `futC s f = f(s + ·) − f s`, which are
independent (Mathlib's weak Markov property `IsPreBrownianReal.indepFun_shift`), so their joint law
is a product `π ⊗ ν`; the path is `glueC s (past, increments)`. For `A` saturated, the section
`{z | glueC s (u, z) ∈ A}` of a past `u` of a path of `G` contains, resp. misses, the full-measure
section of `G` according as the path is in `A` or not (Fubini), so `A` agrees almost surely with
`{f | ν {z | glueC s (pastC s f, z) ∈ A} = 1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

open QuantumZipper.RS

/-! ### Past, increments and gluing -/

/-- The path stopped at `s`. -/
def pastC (s : ℝ≥0) (f : CPath) : CPath :=
  ⟨fun r => f.1 (min r s), f.2.comp (continuous_id.min continuous_const)⟩

/-- The increments of the path after `s`. -/
def futC (s : ℝ≥0) (f : CPath) : CPath :=
  ⟨fun r => f.1 (s + r) - f.1 s, (f.2.comp (continuous_const.add continuous_id)).sub
    continuous_const⟩

/-- A path up to `s` followed by increments. -/
def glueC (s : ℝ≥0) (p : CPath × CPath) : CPath :=
  ⟨fun r => if r ≤ s then p.1.1 r else p.1.1 s + (p.2.1 (r - s) - p.2.1 0), by
    refine Continuous.if_le p.1.2 (continuous_const.add ((p.2.2.comp
      (continuous_id.sub continuous_const)).sub continuous_const)) continuous_id continuous_const
      fun r hr => ?_
    rw [hr, tsub_self, sub_self, add_zero]⟩

theorem glueC_apply_of_le (s : ℝ≥0) (p : CPath × CPath) {r : ℝ≥0} (hr : r ≤ s) :
    (glueC s p).1 r = p.1.1 r := ite_eq_left_iff.2 fun h => absurd hr h

theorem glueC_past_fut (s : ℝ≥0) (f : CPath) : glueC s (pastC s f, futC s f) = f := by
  refine Subtype.ext (funext fun r => ?_)
  show (if r ≤ s then f.1 (min r s) else f.1 (min s s) + ((f.1 (s + (r - s)) - f.1 s) -
    (f.1 (s + 0) - f.1 s))) = f.1 r
  split_ifs with hr
  · rw [min_eq_left hr]
  · rw [min_self, add_zero, sub_self, sub_zero, add_tsub_cancel_of_le (le_of_not_ge hr)]
    ring

/-- A glued path agrees with the past path on `[0, s]`. -/
theorem glueC_pastC_apply_of_le (s : ℝ≥0) (f z : CPath) {r : ℝ≥0} (hr : r ≤ s) :
    (glueC s (pastC s f, z)).1 r = f.1 r := by
  rw [glueC_apply_of_le s _ hr]
  show f.1 (min r s) = f.1 r
  rw [min_eq_left hr]

theorem measurable_coe_cpath : Measurable (Subtype.val : CPath → ℝ≥0 → ℝ) := measurable_subtype_coe

theorem measurable_pastC (s : ℝ≥0) : Measurable (pastC s) :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun r => measurable_canonBM (min r s))

theorem measurable_futC (s : ℝ≥0) : Measurable (futC s) :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun r =>
    (measurable_canonBM (s + r)).sub (measurable_canonBM s))

theorem measurable_glueC (s : ℝ≥0) : Measurable (glueC s) := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun r => ?_)
  by_cases hr : r ≤ s
  · simp only [hr, ↓reduceIte]
    exact (measurable_canonBM r).comp measurable_fst
  · simp only [hr, ↓reduceIte]
    exact ((measurable_canonBM s).comp measurable_fst).add
      (((measurable_canonBM (r - s)).comp measurable_snd).sub
        ((measurable_canonBM 0).comp measurable_snd))

variable {μ : Measure CPath}

/-- **Weak Markov property on `CPath`**: the increments after `s` are independent of the past. -/
theorem indepFun_futC_pastC (hB : IsPreBrownianReal canonBM μ) (s : ℝ≥0) :
    IndepFun (futC s) (pastC s) μ := by
  have h := hB.indepFun_shift s
  rw [IndepFun_iff_Indep] at h ⊢
  have e1 : MeasurableSpace.comap (futC s) (inferInstance : MeasurableSpace CPath) =
      MeasurableSpace.comap (fun f : CPath => fun t => canonBM (s + t) f - canonBM s f)
        MeasurableSpace.pi := by
    show MeasurableSpace.comap (futC s) (MeasurableSpace.comap Subtype.val MeasurableSpace.pi) = _
    rw [MeasurableSpace.comap_comp]
    rfl
  have e2 : MeasurableSpace.comap (pastC s) (inferInstance : MeasurableSpace CPath) ≤
      MeasurableSpace.comap (fun f : CPath => fun t : Set.Iic s => canonBM t f)
        MeasurableSpace.pi := by
    show MeasurableSpace.comap (pastC s) (MeasurableSpace.comap Subtype.val MeasurableSpace.pi) ≤ _
    rw [MeasurableSpace.comap_comp]
    have hψ : Measurable fun u : Set.Iic s → ℝ => fun r : ℝ≥0 => u ⟨min r s, min_le_right r s⟩ :=
      measurable_pi_iff.2 fun r => measurable_pi_apply _
    have : (Subtype.val ∘ pastC s) = (fun u : Set.Iic s → ℝ => fun r : ℝ≥0 =>
        u ⟨min r s, min_le_right r s⟩) ∘ fun f : CPath => fun t : Set.Iic s => canonBM t f := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hψ.comap_le
  rw [e1]
  exact indep_of_indep_of_le_right h e2

/-- The joint law of the past and the increments is the product of their laws. -/
theorem map_pastC_futC_eq_prod [IsProbabilityMeasure μ] (hB : IsPreBrownianReal canonBM μ)
    (s : ℝ≥0) :
    μ.map (fun f => (pastC s f, futC s f)) = (μ.map (pastC s)).prod (μ.map (futC s)) :=
  (indepFun_iff_map_prod_eq_prod_map_map (measurable_pastC s).aemeasurable
    (measurable_futC s).aemeasurable).1 (indepFun_futC_pastC hB s).symm

/-! ### Saturated events -/

/-- `A` is saturated at time `s` on `G`. -/
def IsSaturated (s : ℝ≥0) (G A : Set CPath) : Prop :=
  ∀ f ∈ G, ∀ f' ∈ G, (∀ r ≤ s, f.1 r = f'.1 r) → f ∈ A → f' ∈ A

/-- **A saturated event is almost surely an event of the past.** -/
theorem ae_eq_preimage_pastC_of_saturated [IsProbabilityMeasure μ]
    (hB : IsPreBrownianReal canonBM μ) {s : ℝ≥0} {G A : Set CPath} (hG : MeasurableSet G)
    (hGμ : μ Gᶜ = 0) (hA : MeasurableSet A) (hsat : IsSaturated s G A) :
    ∃ E, MeasurableSet E ∧ A =ᵐ[μ] pastC s ⁻¹' E := by
  set π := μ.map (pastC s) with hπ
  set ν := μ.map (futC s) with hν
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_futC s).aemeasurable).2 inferInstance
  set At := glueC s ⁻¹' A with hAt
  set Gt := glueC s ⁻¹' G with hGt
  have hAtm : MeasurableSet At := measurable_glueC s hA
  have hGtm : MeasurableSet Gt := measurable_glueC s hG
  set E := {u : CPath | ν (Prod.mk u ⁻¹' At) = 1} with hE
  have hEm : MeasurableSet E :=
    measurable_measure_prodMk_left hAtm (measurableSet_singleton 1)
  refine ⟨E, hEm, ?_⟩
  -- the sections of `G` have full measure for almost every past
  have hpf : Measurable fun f => (pastC s f, futC s f) :=
    (measurable_pastC s).prodMk (measurable_futC s)
  have hnull : (π.prod ν) Gtᶜ = 0 := by
    rw [← map_pastC_futC_eq_prod hB s, Measure.map_apply hpf hGtm.compl]
    have : (fun f => (pastC s f, futC s f)) ⁻¹' Gtᶜ = Gᶜ := by
      ext f; simp [hGt, glueC_past_fut]
    rw [this, hGμ]
  rw [Measure.prod_apply hGtm.compl, lintegral_eq_zero_iff
    (measurable_measure_prodMk_left hGtm.compl)] at hnull
  have hsec : ∀ᵐ f ∂μ, ν (Prod.mk (pastC s f) ⁻¹' Gtᶜ) = 0 := by
    have hm : MeasurableSet {u : CPath | ν (Prod.mk u ⁻¹' Gtᶜ) = 0} :=
      measurable_measure_prodMk_left hGtm.compl (measurableSet_singleton 0)
    exact (ae_map_iff (measurable_pastC s).aemeasurable hm).1 hnull
  have hGae : ∀ᵐ f ∂μ, f ∈ G := by
    rw [ae_iff]; exact hGμ
  filter_upwards [hsec, hGae] with f hf hfG
  have hfull : ν (Prod.mk (pastC s f) ⁻¹' Gt) = 1 := by
    rw [← prob_compl_eq_zero_iff (measurable_prodMk_left hGtm), ← preimage_compl]
    exact hf
  refine propext ⟨fun hfA => ?_, fun hfE => ?_⟩
  · -- `G`-section ⊆ `A`-section
    show ν (Prod.mk (pastC s f) ⁻¹' At) = 1
    refine le_antisymm prob_le_one (hfull ▸ measure_mono fun z hz => ?_)
    exact hsat f hfG _ hz (fun r hr => (glueC_pastC_apply_of_le s f z hr).symm) hfA
  · by_contra hfA
    have hsub : Prod.mk (pastC s f) ⁻¹' At ⊆ Prod.mk (pastC s f) ⁻¹' Gtᶜ := by
      intro z hz hzG
      exact hfA (hsat _ hzG f hfG (fun r hr => glueC_pastC_apply_of_le s f z hr) hz)
    have h1 : ν (Prod.mk (pastC s f) ⁻¹' At) = 1 := hfE
    have := (measure_mono hsub).trans_eq hf
    rw [h1] at this
    exact one_ne_zero (nonpos_iff_eq_zero.1 this)

/-- The σ-algebra of measurable events saturated at time `s` on `G`. -/
@[instance_reducible]
def satSpace (s : ℝ≥0) (G : Set CPath) : MeasurableSpace CPath where
  MeasurableSet' A := MeasurableSet A ∧ IsSaturated s G A
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ _ _ h => h.elim⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun f hf f' hf' hag hfA hf'A =>
    hfA (hA.2 f' hf' f hf (fun r hr => (hag r hr).symm) hf'A)⟩
  measurableSet_iUnion A hA := ⟨MeasurableSet.iUnion fun i => (hA i).1, fun f hf f' hf' hag hfA => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hfA
    exact mem_iUnion.2 ⟨i, (hA i).2 f hf f' hf' hag hi⟩⟩

theorem satSpace_le (s : ℝ≥0) (G : Set CPath) :
    satSpace s G ≤ (inferInstance : MeasurableSpace CPath) :=
  fun _ hA => hA.1

/-- **Increments after `s` are independent of the saturated events.** -/
theorem indep_increment_satSpace [IsProbabilityMeasure μ]
    (hB : IsPreBrownianReal canonBM μ) {s t : ℝ≥0} (hst : s ≤ t) {G : Set CPath}
    (hG : MeasurableSet G) (hGμ : μ Gᶜ = 0) :
    Indep (MeasurableSpace.comap (fun f : CPath => canonBM t f - canonBM s f) inferInstance)
      (satSpace s G) μ := by
  rw [Indep_iff]
  rintro C A ⟨S, hS, rfl⟩ ⟨hAm, hAs⟩
  obtain ⟨E, hEm, hAE⟩ := ae_eq_preimage_pastC_of_saturated hB hG hGμ hAm hAs
  have hC : (fun f : CPath => canonBM t f - canonBM s f) ⁻¹' S =
      futC s ⁻¹' ((fun z : CPath => z.1 (t - s)) ⁻¹' S) := by
    ext f
    simp only [mem_preimage, futC, canonBM, add_tsub_cancel_of_le hst]
  have hzm : MeasurableSet ((fun z : CPath => z.1 (t - s)) ⁻¹' S) := measurable_canonBM (t - s) hS
  rw [measure_congr (ae_eq_set_inter (EventuallyEq.refl _ _) hAE), measure_congr hAE, hC]
  exact (indepFun_futC_pastC hB s).measure_inter_preimage_eq_mul _ _ hzm hEm

/-- **Increments after `s` are independent of every σ-algebra of saturated events.** -/
theorem indep_increment_of_le_satSpace [IsProbabilityMeasure μ]
    (hB : IsPreBrownianReal canonBM μ) {s t : ℝ≥0} (hst : s ≤ t) {G : Set CPath}
    (hG : MeasurableSet G) (hGμ : μ Gᶜ = 0) {m : MeasurableSpace CPath} (hm : m ≤ satSpace s G) :
    Indep (MeasurableSpace.comap (fun f : CPath => canonBM t f - canonBM s f) inferInstance) m μ :=
  indep_of_indep_of_le_right (indep_increment_satSpace hB hst hG hGμ) hm

end Assembly2

end Sec2

end InteractingSLE
