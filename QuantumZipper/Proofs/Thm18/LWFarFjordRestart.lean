import QuantumZipper.Proofs.Thm18.LWFarCondMain
import QuantumZipper.Proofs.Thm18.LWFarDefs2
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.RS.TraceMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-8-R: hitting an `𝓕_σ`-measurable covered open set after a stopping time

**Result.** `lwf_restart_hit_le`: for `0 < κ < 4`, a stopping time `σ`, an `𝓕_σ`-measurable
event `A` and an `𝓕_σ`-measurable family of open sets `V ω` which (a.s. on `A`) is covered by
disks `B(cᵢ, rᵢ)` with real centres, `2 rᵢ ≤ |cᵢ|` and `Σ rᵢ/|cᵢ| ≤ δ`, the probability that the
trace of the SLE driven by the restarted motion `B_{σ+·} − B_σ` enters `V ω` is
`≤ C δ^{8/κ−1} P(A)`.

Source: G. Lawler, B. Werness, *Multi-point Green's functions for SLE and an estimate of
Beffara*, Ann. Probab. 41 (2013), the strong Markov step in the proofs of Lemma 2.10 (p. 12) and
Lemma 4.5 (p. 24): conditionally on `𝓕_σ` the restarted motion is a Brownian motion independent
of `𝓕_σ` (`StrongMarkov.isBrownianReal_smShift`, `StrongMarkov.indep_smPath`), so the
conditional probability is bounded by the unconditional covering estimate
`prob_hit_cover_le` (LW Prop 2.6 summed over the disks) at the frozen covering.

The path-space bookkeeping is an own elementary argument: the trace is read off the restarted
path by the path-measurable version `G1Pkg.traceSel` (exact for continuous paths started at
`0`), the hit is reduced to rational times by a.s. continuity of the trace (`ae_sleTrace_good`)
and openness of `V ω`, and the freezing lemma `lwc_freeze` (independence + Fubini) integrates the
frozen bound over `A`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The frozen event on `Ω × paths`: `ω ∈ A` and the path-measurable trace of `y` enters
`V ω` at some nonnegative rational time. -/
def restartS {Ω : Type} (κ : ℝ) (A : Set Ω) (V : Ω → Set ℂ) : Set (Ω × (ℝ≥0 → ℝ)) :=
  (Prod.fst ⁻¹' A) ∩ ⋃ u : {u : ℚ // 0 ≤ u},
    (fun q : Ω × (ℝ≥0 → ℝ) => (q.1, G1Pkg.traceSel κ q.2 ((u : ℚ) : ℝ))) ⁻¹'
      {q : Ω × ℂ | q.2 ∈ V q.1}

lemma measurableSet_restartS {Ω : Type} [MeasurableSpace Ω] (κ : ℝ) {A : Set Ω}
    (hA : MeasurableSet A) {V : Ω → Set ℂ} (hV : MeasurableSet {q : Ω × ℂ | q.2 ∈ V q.1}) :
    MeasurableSet (restartS κ A V) := by
  refine (hA.preimage measurable_fst).inter (MeasurableSet.iUnion fun u => ?_)
  refine hV.preimage (measurable_fst.prodMk ?_)
  exact (measurable_pi_apply (((u : {u : ℚ // 0 ≤ u}) : ℚ) : ℝ)).comp
    ((G1Pkg.measurable_traceSel κ).comp measurable_snd)

/-- **LWF-8-R** (strong Markov restart, LW Lemma 2.10 / Lemma 4.5 pattern). -/
theorem lwf_restart_hit_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ), SMSetup P B 𝓕 →
      ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0))) (A : Set Ω)
        (V : Ω → Set ℂ) (δ : ℝ), MeasurableSet[hσ.measurableSpace] A → 0 ≤ δ →
        (∀ ω, IsOpen (V ω)) →
        MeasurableSet[@Prod.instMeasurableSpace Ω ℂ hσ.measurableSpace _]
          {q : Ω × ℂ | q.2 ∈ V q.1} →
        (∀ᵐ ω ∂P, ω ∈ A → ∃ c r : ℕ → ℝ, (∀ i, 0 < r i ∧ 2 * r i ≤ |c i|) ∧
          Summable (fun i => r i / |c i|) ∧ ∑' i, r i / |c i| ≤ δ ∧
          ∀ p ∈ V ω, ∃ i, ‖p - (c i : ℂ)‖ < r i) →
        P (A ∩ {ω | ∃ u : ℝ, 0 ≤ u ∧
            sleTrace κ (StrongMarkov.smShift B σ) ω u ∈ V ω}) ≤
          ENNReal.ofReal (C * δ ^ (8 / κ - 1)) * P A := by
  obtain ⟨C, hC0, hC⟩ := prob_hit_cover_le hκ hκ4
  refine ⟨C, hC0, ?_⟩
  intro Ω mΩ P _ B 𝓕 hS σ hσ A V δ hA hδ hVo hVm hcov
  have hB := hS.brownian.toIsPreBrownianReal
  have hBc := hS.cont
  have hBm := hS.meas
  have hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (StrongMarkov.smPath B (fun _ => t))
      MeasurableSpace.pi) P := fun t =>
    StrongMarkov.indep_shift_of_le_past hB (fun t => le_of_eq (hS.natural t)) t
  have hAm : MeasurableSet A := hσ.measurableSpace_le _ hA
  have hBt : IsBrownianReal (StrongMarkov.smShift B σ) P :=
    StrongMarkov.isBrownianReal_smShift hB hBc hBm hind hσ
  set Y : Ω → (ℝ≥0 → ℝ) := StrongMarkov.smPath B σ with hYdef
  have hYm : Measurable Y := StrongMarkov.measurable_smPath hBc hBm
    (StrongMarkov.measurable_of_isStoppingTime hσ)
  have hYc : ∀ ω, Continuous (Y ω) := fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hY0 : ∀ ω, Y ω 0 = 0 := fun ω => by
    simp [hYdef, StrongMarkov.smPath, StrongMarkov.smShift]
  have hYtr : ∀ ω (t : ℝ), 0 ≤ t →
      G1Pkg.traceSel κ (Y ω) t = sleTrace κ (StrongMarkov.smShift B σ) ω t :=
    fun ω t ht => G1Pkg.traceSel_eq (hYc ω) (hY0 ω) ht
  have hξ : @Measurable Ω Ω mΩ hσ.measurableSpace id :=
    (@measurable_id Ω hσ.measurableSpace).mono hσ.measurableSpace_le le_rfl
  have hSm := @measurableSet_restartS Ω hσ.measurableSpace κ A hA V hVm
  set S := restartS κ A V with hSdef
  have hindξ : @IndepFun Ω Ω (ℝ≥0 → ℝ) mΩ hσ.measurableSpace _ id Y P := by
    refine (IndepFun_iff_Indep (mβ := hσ.measurableSpace) id Y P).2 ?_
    rw [MeasurableSpace.comap_id]
    exact StrongMarkov.indep_smPath hB hBc hBm hind hσ
  have hfr := @lwc_freeze Ω Ω (ℝ≥0 → ℝ) mΩ hσ.measurableSpace _ P _ id Y hξ hYm hindξ S hSm
  -- step 1: the event lies a.s. in the frozen event
  obtain ⟨_, _, hgood⟩ := RS.ae_sleTrace_good hBt hκ (by linarith : κ < 8)
  have hle : (A ∩ {ω | ∃ u : ℝ, 0 ≤ u ∧ sleTrace κ (StrongMarkov.smShift B σ) ω u ∈ V ω}
      : Set Ω) ≤ᵐ[P] (fun ω => (id ω, Y ω)) ⁻¹' S := by
    filter_upwards [hgood] with ω hω
    rintro ⟨hωA, u, hu, hV⟩
    set f := sleTrace κ (StrongMarkov.smShift B σ) ω with hf
    have hg : Continuous fun t : ℝ => f (max t 0) := RS.continuous_comp_max_zero hω.2.1
    have hO : IsOpen ((fun t : ℝ => f (max t 0)) ⁻¹' V ω) := (hVo ω).preimage hg
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hO ⟨u, by
      show f (max u 0) ∈ V ω
      rwa [max_eq_left hu]⟩
    refine ⟨hωA, mem_iUnion.2 ⟨⟨max q 0, le_max_right _ _⟩, ?_⟩⟩
    show G1Pkg.traceSel κ (Y ω) (((max q 0 : ℚ)) : ℝ) ∈ V ω
    have hc : (((max q 0 : ℚ)) : ℝ) = max (q : ℝ) 0 := by push_cast; rfl
    rw [hc, hYtr ω _ (le_max_right _ _)]
    exact hq
  -- step 2: freeze and bound the sections
  set K := ENNReal.ofReal (C * δ ^ (8 / κ - 1)) with hK
  have hsec : ∀ᵐ ω ∂P, P.map Y (Prod.mk (id ω) ⁻¹' S) ≤ A.indicator (fun _ => K) ω := by
    filter_upwards [hcov] with ω hω
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA]
      obtain ⟨c, r, hcr, hsum, hsδ, hVc⟩ := hω hωA
      have hsecS : Prod.mk (id ω) ⁻¹' S = ⋃ u : {u : ℚ // 0 ≤ u},
          (fun y : ℝ≥0 → ℝ => G1Pkg.traceSel κ y ((u : ℚ) : ℝ)) ⁻¹' V ω := by
        ext y
        simp [hSdef, restartS, hωA]
      have hsm : MeasurableSet (⋃ u : {u : ℚ // 0 ≤ u},
          (fun y : ℝ≥0 → ℝ => G1Pkg.traceSel κ y ((u : ℚ) : ℝ)) ⁻¹' V ω) :=
        MeasurableSet.iUnion fun u => (hVo ω).measurableSet.preimage
          ((measurable_pi_apply (((u : {u : ℚ // 0 ≤ u}) : ℚ) : ℝ)).comp
            (G1Pkg.measurable_traceSel κ))
      rw [hsecS, Measure.map_apply hYm hsm]
      have hsub : Y ⁻¹' (⋃ u : {u : ℚ // 0 ≤ u},
          (fun y : ℝ≥0 → ℝ => G1Pkg.traceSel κ y ((u : ℚ) : ℝ)) ⁻¹' V ω) ⊆
          {ω' | ∃ t : ℝ, 0 ≤ t ∧ ∃ i,
            ‖sleTrace κ (StrongMarkov.smShift B σ) ω' t - c i‖ < r i} := by
        intro ω' hω'
        obtain ⟨u, hu⟩ := mem_iUnion.1 hω'
        have hu0 : (0 : ℝ) ≤ ((u : ℚ) : ℝ) := by exact_mod_cast u.2
        have hmem : sleTrace κ (StrongMarkov.smShift B σ) ω' ((u : ℚ) : ℝ) ∈ V ω := by
          rw [← hYtr ω' _ hu0]; exact hu
        exact ⟨_, hu0, hVc _ hmem⟩
      refine (measure_mono hsub).trans ((hC P _ hBt c r hcr hsum).trans ?_)
      have hα : 0 ≤ 8 / κ - 1 := by
        rw [sub_nonneg, le_div_iff₀ hκ]; linarith
      have hs0 : 0 ≤ ∑' i, r i / |c i| :=
        tsum_nonneg fun i => div_nonneg (hcr i).1.le (abs_nonneg _)
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs0 hsδ hα) hC0)
    · rw [indicator_of_notMem hωA]
      have hempty : Prod.mk (id ω) ⁻¹' S = ∅ := by
        ext y
        simp [hSdef, restartS, hωA]
      rw [hempty, measure_empty]
  calc P (A ∩ {ω | ∃ u : ℝ, 0 ≤ u ∧ sleTrace κ (StrongMarkov.smShift B σ) ω u ∈ V ω})
      ≤ P ((fun ω => (id ω, Y ω)) ⁻¹' S) := measure_mono_ae hle
    _ = ∫⁻ ω, P.map Y (Prod.mk (id ω) ⁻¹' S) ∂P := hfr
    _ ≤ ∫⁻ ω, A.indicator (fun _ => K) ω ∂P := lintegral_mono_ae hsec
    _ = K * P A := lintegral_indicator_const hAm K

end LWFar
end Thm18Asm
end QuantumZipper
