/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartFilt2Union
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# The Markov decomposition and the history-marked avoidance criterion depend only on the joint law

Packet PROVE-WW-B18 (step B3, the field side). The history-marked avoidance criterion
(`WholeField.IsHistoryAvoidanceLocal`, Aux. lemma 18) is a statement about conditional probabilities given the field,
quantified over the Borel Markov maps `G` for which `h = G h + (h − G h)` is the Markov decomposition of Proposition 3.1
(`GFF.IsMarkovDecomposition`). Both are properties of the joint law of the field and of the random set with its marks:

* `isZBGFFExtOn_of_map_eq`, `isZeroBoundaryGFF_of_map_eq`: the Gaussian clauses transfer along equal laws;
* `measurableSet_harmonicOn`: "`T` restricted to `U` is a harmonic function" is a Borel condition on the distribution
  (Weyl's lemma through the countable generating family `distGen`: `exists_harmonic_of_distGen`, and conversely a
  harmonic function annihilates the Laplacians of test functions, `integral_mul_cmTest_of_harmonic`);
* **`isMarkovDecomposition_of_map_eq`**: a Markov decomposition transfers to any pair with the same joint law;
* **`isHistoryAvoidanceLocal_of_map_eq`**: the history-marked avoidance criterion of a set `𝔄(Y)` with marks `σ(Y)`
  restricted to a sub-σ-algebra transfers to any pair `(X', Y')` with the law of `(X, Y)`;
* `IsHistoryAvoidanceLocal.mono_marks`: fewer marks.

These let the history-marked locality of the frozen couplings (`isHistoryAvoidanceLocal_hull`) be read on the glued
space of the contact step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped ENNReal

namespace InteractingSLE.WangWu

open WholeField LocalSets GFF

/-! ### The Gaussian clauses along equal laws -/

section Gauss

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

theorem isZBGFFExtOn_of_map_eq {U D : TopologicalSpace.Opens ℂ} {X : Ω → DistOn D} {X' : Ω' → DistOn D}
    (hX : IsZBGFFExtOn U D X P) (hX' : Measurable X') (hlaw : P'.map X' = P.map X) : IsZBGFFExtOn U D X' P' := by
  obtain ⟨hm, hg, hc, hcov⟩ := hX
  refine ⟨hX', ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have h := hg.hasGaussianLaw I
    have hr : Measurable fun T : DistOn D => I.restrict fun φ => T φ :=
      measurable_pi_iff.2 fun φ => LQGMetric.measurable_distOn_apply φ.1
    refine ⟨(hr.comp hX').aemeasurable, ?_⟩
    have e1 : P'.map (fun ω => I.restrict fun φ => X' ω φ) = (P'.map X').map fun T => I.restrict fun φ => T φ :=
      (Measure.map_map hr hX').symm
    have e2 : P.map (fun ω => I.restrict fun φ => X ω φ) = (P.map X).map fun T => I.restrict fun φ => T φ :=
      (Measure.map_map hr hm).symm
    rw [e1, hlaw, ← e2]
    exact h.isGaussian_map
  · have h1 := integral_map (μ := P') hX'.aemeasurable (LQGMetric.measurable_distOn_apply φ).aestronglyMeasurable
    have h2 := integral_map (μ := P) hm.aemeasurable (LQGMetric.measurable_distOn_apply φ).aestronglyMeasurable
    rw [← hc φ]
    exact h1.symm.trans ((congrArg (fun ν => ∫ T, T φ ∂ν) hlaw).trans h2)
  · have e1 := covariance_map (μ := P') (LQGMetric.measurable_distOn_apply φ).aestronglyMeasurable
      (LQGMetric.measurable_distOn_apply ψ).aestronglyMeasurable hX'.aemeasurable
    have e2 := covariance_map (μ := P) (LQGMetric.measurable_distOn_apply φ).aestronglyMeasurable
      (LQGMetric.measurable_distOn_apply ψ).aestronglyMeasurable hm.aemeasurable
    rw [hlaw] at e1
    rw [← hcov φ ψ]
    exact e1.symm.trans e2

theorem isZeroBoundaryGFF_of_map_eq {U : TopologicalSpace.Opens ℂ} {X : Ω → DistOn U} {X' : Ω' → DistOn U}
    (hX : LQGMetric.IsZeroBoundaryGFF U X P) (hX' : Measurable X') (hlaw : P'.map X' = P.map X) :
    LQGMetric.IsZeroBoundaryGFF U X' P' := by
  have h1 := Restart.isZBGFFProcess_map (U := U) hX.measurable (X := fun φ T => T φ)
    (fun φ => LQGMetric.measurable_distOn_apply φ) hX.process
  rw [← hlaw] at h1
  refine ⟨hX', ?_⟩
  obtain ⟨-, hg, hc, hcov⟩ := h1
  refine ⟨fun φ => (LQGMetric.measurable_distOn_apply φ).comp hX', ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have h := hg.hasGaussianLaw I
    have hr : Measurable fun T : DistOn U => I.restrict fun φ => T φ :=
      measurable_pi_iff.2 fun φ => LQGMetric.measurable_distOn_apply φ.1
    refine ⟨(hr.comp hX').aemeasurable, ?_⟩
    rw [show (fun ω => I.restrict fun t => X' ω t) = (fun T : DistOn U => I.restrict fun φ => T φ) ∘ X' from rfl,
      ← Measure.map_map hr hX']
    exact h.isGaussian_map
  · rw [← hc φ, integral_map hX'.aemeasurable (LQGMetric.measurable_distOn_apply φ).aestronglyMeasurable]
  · rw [← hcov φ ψ, covariance_map (LQGMetric.measurable_distOn_apply φ).aestronglyMeasurable
      (LQGMetric.measurable_distOn_apply ψ).aestronglyMeasurable hX'.aemeasurable]
    rfl

end Gauss

/-! ### Harmonicity is a Borel condition -/

section Harmonic

/-- **"`T` is a harmonic function on `U`" is a Borel condition** on `T ∈ 𝒟'(D)`: by Weyl's lemma it is equivalent
to the vanishing of `T` on the Laplacians of the countable generating family `distGen U`. -/
theorem measurableSet_harmonicOn (U : TopologicalSpace.Opens ℂ) {D : TopologicalSpace.Opens ℂ} :
    MeasurableSet {T : DistOn D | ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictDist U T φ = ∫ x, g x * φ x} := by
  have e : {T : DistOn D | ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, restrictDist U T φ = ∫ x, g x * φ x} =
      ⋂ j : ℕ × ℕ, {T : DistOn D | restrictDist U T
        (LQGMetric.MarkovHarm.cmTestOn (LQGMetric.MarkovAsm.toZs (LQGMetric.distGen U j))) = 0} := by
    ext T
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · rintro ⟨g, hg, hT⟩ j
      set f := LQGMetric.MarkovAsm.toZs (LQGMetric.distGen U j)
      rw [hT]
      exact LQGMetric.HarmLoc.integral_mul_cmTest_of_harmonic U.isOpen hg _ f.2.2.2
    · intro hT
      exact exists_harmonic_of_distGen (restrictDist U T) hT
  rw [e]
  exact MeasurableSet.iInter fun j =>
    measurableSet_eq_fun ((LQGMetric.measurable_distOn_apply _).comp (measurable_restrictDist U))
      measurable_const

end Harmonic

/-! ### The Markov decomposition along equal joint laws -/

section MarkovLaw

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

theorem measurable_sub_distOn {D : TopologicalSpace.Opens ℂ} :
    Measurable fun p : DistOn D × DistOn D => p.1 - p.2 :=
  LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp measurable_fst).sub
      ((LQGMetric.measurable_distOn_apply φ).comp measurable_snd)

/-- **The Markov decomposition depends only on the joint law** of the field and its zero-boundary part. -/
theorem isMarkovDecomposition_of_map_eq {U D : TopologicalSpace.Opens ℂ} {h hU : Ω → DistOn D}
    {h' hU' : Ω' → DistOn D} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hd : IsMarkovDecomposition U D h hU P) (hm : Measurable h) (hUm : Measurable hU) (hm' : Measurable h')
    (hUm' : Measurable hU')
    (hlaw : P'.map (fun ω => (h' ω, hU' ω)) = P.map (fun ω => (h ω, hU ω))) :
    IsMarkovDecomposition U D h' hU' P' := by
  have hpm : Measurable fun ω => (h ω, hU ω) := hm.prodMk hUm
  have hpm' : Measurable fun ω => (h' ω, hU' ω) := hm'.prodMk hUm'
  -- laws of functions of the pair
  have hmap : ∀ {γ : Type} [MeasurableSpace γ] {F : DistOn D × DistOn D → γ}, Measurable F →
      P'.map (fun ω => F (h' ω, hU' ω)) = P.map (fun ω => F (h ω, hU ω)) := by
    intro γ _ F hF
    rw [show (fun ω => F (h' ω, hU' ω)) = F ∘ fun ω => (h' ω, hU' ω) from rfl, ← Measure.map_map hF hpm', hlaw,
      Measure.map_map hF hpm]
    rfl
  -- almost sure Borel conditions of the pair
  have hae : ∀ {S : Set (DistOn D × DistOn D)}, MeasurableSet S → (∀ᵐ ω ∂P, (h ω, hU ω) ∈ S) →
      ∀ᵐ ω ∂P', (h' ω, hU' ω) ∈ S := by
    intro S hS hP
    have h1 : ∀ᵐ x ∂(P.map fun ω => (h ω, hU ω)), x ∈ S := (ae_map_iff hpm.aemeasurable hS).2 hP
    rw [← hlaw] at h1
    exact (ae_map_iff hpm'.aemeasurable hS).1 h1
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd
  refine ⟨isZBGFFExtOn_of_map_eq h1 hUm' (hmap (F := Prod.snd) measurable_snd),
    isZeroBoundaryGFF_of_map_eq h2 ((measurable_restrictDist U).comp hUm')
      (hmap (F := fun p => restrictDist U p.2) ((measurable_restrictDist U).comp measurable_snd)), ?_, ?_, ?_⟩
  · have hS : MeasurableSet {p : DistOn D × DistOn D | restrictDist (outsideOpens U D) p.2 = 0} :=
      measurableSet_eq_fun ((measurable_restrictDist _).comp measurable_snd) measurable_const
    exact hae hS h3
  · have hsub : Measurable fun ω => h ω - hU ω := measurable_sub_distOn.comp hpm
    have hsub' : Measurable fun ω => h' ω - hU' ω := measurable_sub_distOn.comp hpm'
    rw [indepFun_iff_map_prod_eq_prod_map_map hUm'.aemeasurable hsub'.aemeasurable]
    rw [indepFun_iff_map_prod_eq_prod_map_map hUm.aemeasurable hsub.aemeasurable] at h4
    rw [hmap (F := fun p => (p.2, p.1 - p.2)) (measurable_snd.prodMk measurable_sub_distOn),
      hmap (F := Prod.snd) measurable_snd, hmap (F := fun p => p.1 - p.2) measurable_sub_distOn]
    exact h4
  · have hS := (measurableSet_harmonicOn U (D := D)).preimage (measurable_sub_distOn (D := D))
    exact hae hS h5

end MarkovLaw

/-! ### The history-marked avoidance criterion along equal joint laws -/

section Mono

variable {Ω : Type*} {ℋ ℋ' m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Fewer marks. -/
theorem IsHistoryAvoidanceLocal.mono_marks {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsHistoryAvoidanceLocal ℋ A h P) (hle : ℋ' ≤ ℋ) : IsHistoryAvoidanceLocal ℋ' A h P :=
  fun U G hUH hG hd F hF => hloc U G hUH hG hd F (hle F hF)

/-- A conditional probability lies in `[0, 1]`. -/
theorem ae_condExp_indicator_mem_Icc (hm : m ≤ mΩ) {S : Set Ω} (hS : MeasurableSet S) [IsFiniteMeasure P] :
    ∀ᵐ ω ∂P, (P⟦S | m⟧) ω ∈ Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ᵐ[P] P⟦S | m⟧ := condExp_nonneg (Eventually.of_forall fun ω => by
    simp only [Pi.zero_apply]; exact indicator_nonneg (fun _ _ => zero_le_one) ω)
  have h1 : P⟦S | m⟧ ≤ᵐ[P] P[fun _ => (1 : ℝ) | m] :=
    condExp_mono ((integrable_const (1 : ℝ)).indicator hS) (integrable_const 1)
      (Eventually.of_forall fun ω => indicator_le_self' (fun _ _ => zero_le_one) ω)
  rw [condExp_const hm] at h1
  filter_upwards [h0, h1] with ω a b using ⟨a, b⟩

end Mono

section MarkedLaw

variable {Ω Ω' β : Type*} {𝔐 : MeasurableSpace β} [mβ : MeasurableSpace β] [mΩ : MeasurableSpace Ω]
  [mΩ' : MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- **The history-marked avoidance criterion depends only on the joint law** of the field and of a decoration `Y`
from which the set (`𝔄 ∘ Y`) and the marks (`σ(Y)` restricted to a sub-σ-algebra `𝔐`) are read. -/
theorem isHistoryAvoidanceLocal_of_map_eq {X : Ω → DistOn upperHalfPlaneOpens} {Y : Ω → β}
    {X' : Ω' → DistOn upperHalfPlaneOpens} {Y' : Ω' → β} (hX : Measurable X) (hY : Measurable Y)
    (hX' : Measurable X') (hY' : Measurable Y')
    (hlaw : P'.map (fun ω => (X' ω, Y' ω)) = P.map (fun ω => (X ω, Y ω)))
    {𝔄 : β → Set ℂ} (h𝔄 : Measurable[mβ, hittingSigma] 𝔄) (h𝔐 : 𝔐 ≤ mβ)
    (hloc : IsHistoryAvoidanceLocal (𝔐.comap Y) (fun ω => 𝔄 (Y ω)) X P) :
    IsHistoryAvoidanceLocal (𝔐.comap Y') (fun ω => 𝔄 (Y' ω)) X' P' := by
  intro U G hUH hG hd' F' hF'
  obtain ⟨M, hM, rfl⟩ := hF'
  have hpm : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hpm' : Measurable fun ω => (X' ω, Y' ω) := hX'.prodMk hY'
  have hlawX : P'.map X' = P.map X := by
    have h1 := congrArg (fun ν => ν.map Prod.fst) hlaw
    simp only [Measure.map_map measurable_fst hpm', Measure.map_map measurable_fst hpm] at h1
    exact h1
  -- the Markov decomposition on `Ω`
  have hd : IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P := by
    refine isMarkovDecomposition_of_map_eq hd' hX' (hG.comp hX') hX (hG.comp hX) ?_
    have hF : Measurable fun x : DistOn upperHalfPlaneOpens => (x, G x) := measurable_id.prodMk hG
    rw [show (fun ω => (X ω, G (X ω))) = (fun x => (x, G x)) ∘ X from rfl,
      show (fun ω => (X' ω, G (X' ω))) = (fun x => (x, G x)) ∘ X' from rfl,
      ← Measure.map_map hF hX, ← Measure.map_map hF hX', hlawX]
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd (Y ⁻¹' M) ⟨M, hM, rfl⟩
  set S : Set β := {y | Disjoint (𝔄 y) (U : Set ℂ)} ∩ M with hSdef
  have hSm : MeasurableSet S := (h𝔄 (measurableSet_avoid U.isOpen hUH)).inter (h𝔐 M hM)
  change P⟦Y ⁻¹' S | MeasurableSpace.comap X inferInstance⟧ =ᵐ[P] _ at hge
  -- the clamped version of `g`
  set g' : DistOn upperHalfPlaneOpens → ℝ := fun T => max 0 (min 1 (g T)) with hg'def
  have hg'm : Measurable g' := measurable_const.max (measurable_const.min hg)
  have hmX : MeasurableSpace.comap X inferInstance ≤ mΩ := hX.comap_le
  have hge' : P⟦Y ⁻¹' S | MeasurableSpace.comap X inferInstance⟧ =ᵐ[P] fun ω => g' (markovCompl G (X ω)) := by
    filter_upwards [hge, ae_condExp_indicator_mem_Icc hmX (hY hSm)] with ω h1 h2
    rw [h1] at h2 ⊢
    simp only [hg'def, min_eq_right h2.2, max_eq_right h2.1]
  have hYm : Measurable fun x => g' (markovCompl G x) := hg'm.comp (measurable_markovCompl hG)
  have hbd : ∀ x, ‖g' (markovCompl G x)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by simp only [hg'def]; linarith [le_max_left 0 (min 1 (g (markovCompl G x)))],
      max_le zero_le_one (min_le_left _ _)⟩
  -- the identification on `Ω'`
  have hmX' : MeasurableSpace.comap X' inferInstance ≤ mΩ' := hX'.comap_le
  refine ⟨g', hg'm, ?_⟩
  change P'⟦Y' ⁻¹' S | MeasurableSpace.comap X' inferInstance⟧ =ᵐ[P'] _
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmX' ((integrable_const (1 : ℝ)).indicator (hY' hSm))
    (fun s _ _ => (Integrable.of_bound (hYm.comp hX').aestronglyMeasurable 1
      (Eventually.of_forall fun ω => hbd _)).integrableOn) (fun s hs _ => ?_)
    ((hYm.comp (comap_measurable X')).aestronglyMeasurable)).symm
  obtain ⟨B, hB, rfl⟩ := hs
  show ∫ ω in X' ⁻¹' B, g' (markovCompl G (X' ω)) ∂P' = _
  have hi' := (setIntegral_map hB hYm.aestronglyMeasurable hX'.aemeasurable (μ := P')).symm
  have hi := (setIntegral_map hB hYm.aestronglyMeasurable hX.aemeasurable (μ := P)).symm
  rw [hi', hlawX, ← hi, setIntegral_congr_ae (hX hB) (hge'.mono fun ω h _ => h.symm),
    setIntegral_condExp hmX ((integrable_const (1 : ℝ)).indicator (hY hSm)) ⟨B, hB, rfl⟩,
    integral_indicator (hY' hSm), integral_indicator (hY hSm), setIntegral_const, setIntegral_const,
    measureReal_restrict_apply (hY hSm), measureReal_restrict_apply (hY' hSm), smul_eq_mul, smul_eq_mul,
    mul_one, mul_one]
  have e1 : Y' ⁻¹' S ∩ X' ⁻¹' B = (fun ω => (X' ω, Y' ω)) ⁻¹' (B ×ˢ S) := by
    ext; simp only [mem_inter_iff, mem_preimage, mem_prod]; tauto
  have e2 : Y ⁻¹' S ∩ X ⁻¹' B = (fun ω => (X ω, Y ω)) ⁻¹' (B ×ˢ S) := by
    ext; simp only [mem_inter_iff, mem_preimage, mem_prod]; tauto
  rw [e1, e2, measureReal_def, measureReal_def, ← Measure.map_apply hpm' (hB.prod hSm),
    ← Measure.map_apply hpm (hB.prod hSm), hlaw]

end MarkedLaw

end InteractingSLE.WangWu
