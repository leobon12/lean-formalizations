/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.MarkovChart
import InteractingSLE.Spec.Supplement.WalkMarkedLocalKernel
import InteractingSLE.Spec.Sec6.Prop61BMarked
import InteractingSLE.Spec.Coupling.WholeField8Local

/-!
# Entrance-history locality of a path restarted in a chart (gluing at the restart)

Packet PROVE-STAGEDLOC, item (2). A staged path `α` (Theorem 1.3's angle-varying strip path, Theorem 1.4's staged
histories) is built piece by piece: after the time `t₀` the next piece is a flow line of the field read through a
conformal chart `c` fixed by the past. Lemma 6.2's hypothesis for `α` (`Sec6.IsEntranceHistoryLocal`: given
`h_{U^c}`, the history of `α` through its first entrance into a deterministic open `U ⊆ ℍ` is conditionally
independent of `h_U`) is glued here from

* **the past**: the same locality, and field determination, for the path frozen after `t₀` (`frozenPath`);
* **the continuation, under the regular conditional law `ν_{ω₀}` given the history through `t₀`**: the chart field
  `h' = h ∘ inv + m` is a zero-boundary GFF, and whenever the past avoids `U` the history of `α` through its first
  entrance into `U` is determined, up to `ν_{ω₀}`-null sets, by the Markov complement of `h'` along the chart
  pre-image `inv⁻¹ U` (`hcont`, the single-flow-line locality of the continuation read in the chart).

Proof (**`isEntranceHistoryLocal_of_restart`**), for `U`, `X = G h = h_U`, `Y = h − G h = h_{U^c}`: by
`WholeField.condIndepEv_of_factorsOn` it suffices that `X` factors out of `E[1_S e^{iX(Φ)} e^{iY(Ψ)}]` for every event
`S` of the history. Split `S` along the past avoidance event `E₀ = {α([0, t₀]) ∩ U = ∅}` (an event of the past):

* on `E₀ᶜ` the history is the frozen path's history (`histOf_frozenPath_eq`), which is almost surely a function of `Y`
  (Lemma 6.2's determination, `Sec6.measurable_entranceHist`), and `X` is independent of `Y`;
* on `E₀`, under `ν_{ω₀}` the Markov decomposition of `h` along `U` persists with the law of `X` unchanged
  (`Theorem14.WalkLaw.ae_isMarkovDecomposition_condExpKernel`, from the marked locality of the frozen path,
  `Sec6.isHistoryAvoidanceLocal_explored`), the chart transport `MarkovChart.ae_markovCompl_pushTest_eq` turns the
  Markov complement of `h'` into a function of `Y`, so the history is `ν_{ω₀}`-almost surely a function of `Y`, and
  the factorization holds under `ν_{ω₀}`; integrating over `ω₀ ∈ E₀` gives it under `P`.

Finitely many pieces follow by applying the theorem at each restart time to the path frozen after the next one
(`frozenPath_frozenPath`).

## Main results

* `frozenPath`, `histOf_frozenPath_eq`, `firstEntrance_frozenPath_eq_top_iff`: the frozen path and its entrance
  histories;
* `factorsOn_of_measurableSet_aeSigma`, `FactorsOn.union`: the factorization identity on events determined by `Y`;
* **`isEntranceHistoryLocal_of_restart`**: the gluing theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn measurable_distOn_apply)

namespace InteractingSLE

namespace Restart

namespace StagedEntrance

open Sec6 LocalSets

/-! ### The path frozen after a time -/

section Cap

/-- The path frozen after `t₀`: `γ(t ∧ t₀)`. -/
def frozenPath (γ : ℝ≥0 → ℂ) (t₀ : ℝ≥0) : ℝ≥0 → ℂ := fun t => γ (min t t₀)

variable {γ : ℝ≥0 → ℂ} {t₀ : ℝ≥0}

theorem continuous_frozenPath (hγ : Continuous γ) : Continuous (frozenPath γ t₀) :=
  hγ.comp (continuous_id.min continuous_const)

theorem frozenPath_of_le {t : ℝ≥0} (ht : t ≤ t₀) : frozenPath γ t₀ t = γ t := by
  simp only [frozenPath, min_eq_left ht]

theorem frozenPath_zero : frozenPath γ t₀ 0 = γ 0 := frozenPath_of_le zero_le

/-- Freezing twice at increasing times. -/
theorem frozenPath_frozenPath {t₁ : ℝ≥0} (h : t₀ ≤ t₁) : frozenPath (frozenPath γ t₁) t₀ = frozenPath γ t₀ := by
  funext t
  simp only [frozenPath, min_assoc, min_eq_left h]

/-- If a continuous path meets an open set by time `t₀`, it does so at a rational time `q ≤ t₀`. -/
theorem exists_rat_le_mem_of_not_disjoint {U : Set ℂ} (hU : IsOpen U) (hγ : Continuous γ)
    (h : ¬ Disjoint (γ '' Icc 0 t₀) U) : ∃ q : ℚ≥0, ((q : ℝ≥0)) ≤ t₀ ∧ γ q ∈ U := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hsU⟩ := Set.not_disjoint_iff.1 h
  obtain ⟨q, hqs, hqU⟩ := exists_rat_le_mem hU hγ hsU
  exact ⟨q, hqs.trans hs.2, hqU⟩

/-- The frozen path never enters `U` exactly when the path avoids `U` up to `t₀`. -/
theorem firstEntrance_frozenPath_eq_top_iff {U : Set ℂ} (hU : IsOpen U) (hγ : Continuous γ) :
    firstEntrance U (pathCoord (frozenPath γ t₀)) = ⊤ ↔ Disjoint (γ '' Icc 0 t₀) U := by
  constructor
  · intro htop
    by_contra hnd
    obtain ⟨q, hq, hqU⟩ := exists_rat_le_mem_of_not_disjoint hU hγ hnd
    have hle := firstEntrance_le (U := U) (c := pathCoord (frozenPath γ t₀)) (q := q)
      (show frozenPath γ t₀ q ∈ U by rw [frozenPath_of_le hq]; exact hqU)
    rw [htop] at hle
    exact ENNReal.coe_ne_top (top_le_iff.1 hle)
  · intro hd
    refine iInf₂_eq_top.2 fun q hq => absurd hq ?_
    exact Set.disjoint_left.1 hd ⟨min (q : ℝ≥0) t₀, ⟨zero_le, min_le_right _ _⟩, rfl⟩

/-- **The entrance history of a path that enters `U` by time `t₀` is the entrance history of the frozen path.** -/
theorem histOf_frozenPath_eq {U : Set ℂ} (hU : IsOpen U) (hγ : Continuous γ)
    (h : ¬ Disjoint (γ '' Icc 0 t₀) U) :
    histOf (pathCoord (frozenPath γ t₀)) (firstEntrance U (pathCoord (frozenPath γ t₀))) =
      histOf (pathCoord γ) (firstEntrance U (pathCoord γ)) := by
  obtain ⟨q₀, hq₀, hq₀U⟩ := exists_rat_le_mem_of_not_disjoint hU hγ h
  have hq₀c : frozenPath γ t₀ q₀ ∈ U := by rw [frozenPath_of_le hq₀]; exact hq₀U
  have hT₀ : firstEntrance U (pathCoord (frozenPath γ t₀)) ≤ t₀ :=
    (firstEntrance_le (c := pathCoord (frozenPath γ t₀)) hq₀c).trans (ENNReal.coe_le_coe.2 hq₀)
  have hT : firstEntrance U (pathCoord γ) ≤ t₀ :=
    (firstEntrance_le (c := pathCoord γ) hq₀U).trans (ENNReal.coe_le_coe.2 hq₀)
  have heq : firstEntrance U (pathCoord (frozenPath γ t₀)) = firstEntrance U (pathCoord γ) := by
    refine le_antisymm (le_iInf₂ fun q hq => ?_) (le_iInf₂ fun q hq => ?_)
    · by_cases hqt : (q : ℝ≥0) ≤ t₀
      · refine firstEntrance_le (c := pathCoord (frozenPath γ t₀)) ?_
        change frozenPath γ t₀ q ∈ U
        rw [frozenPath_of_le hqt]
        exact hq
      · exact hT₀.trans (ENNReal.coe_le_coe.2 (not_le.1 hqt).le)
    · by_cases hqt : (q : ℝ≥0) ≤ t₀
      · refine firstEntrance_le (c := pathCoord γ) ?_
        have hq' : frozenPath γ t₀ q ∈ U := hq
        rwa [frozenPath_of_le hqt] at hq'
      · exact hT.trans (ENNReal.coe_le_coe.2 (not_le.1 hqt).le)
  rw [heq]
  unfold histOf
  congr 1
  funext q
  unfold stopCoord
  split_ifs with hq
  · change frozenPath γ t₀ q = γ q
    exact frozenPath_of_le (ENNReal.coe_le_coe.1 (hq.trans hT))
  · rfl

end Cap

/-! ### The factorization identity on events determined by `Y` -/

section Factor

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- **The factorization identity on an event of `Y`**, for `X` independent of `Y`. -/
theorem factorsOn_preimage (hXm : Measurable X) (hYm : Measurable Y) (hind : IndepFun X Y P)
    {C : Set (DistOn upperHalfPlaneOpens)} (hC : MeasurableSet C) : WholeField.FactorsOn P X Y (Y ⁻¹' C) := by
  intro Φ Ψ
  have hYC : MeasurableSet (Y ⁻¹' C) := hYm hC
  have key := hind.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (T Φ : ℂ)))
    (g := fun T : DistOn upperHalfPlaneOpens => C.indicator (fun T => Complex.exp (Complex.I * (T Ψ : ℂ))) T)
    hXm.aemeasurable hYm.aemeasurable
    (GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)).aestronglyMeasurable
    ((GFF.measurable_exp_I_mul (measurable_distOn_apply Ψ)).indicator hC).aestronglyMeasurable
  rw [← integral_indicator hYC, ← integral_indicator hYC]
  have e1 : (Y ⁻¹' C).indicator (fun ω => Complex.exp (Complex.I * (X ω Φ : ℂ)) *
      Complex.exp (Complex.I * (Y ω Ψ : ℂ))) = fun ω => Complex.exp (Complex.I * (X ω Φ : ℂ)) *
        C.indicator (fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ))) (Y ω) := by
    funext ω
    by_cases hω : Y ω ∈ C
    · rw [indicator_of_mem (show ω ∈ Y ⁻¹' C from hω), indicator_of_mem hω]
    · rw [indicator_of_notMem (show ω ∉ Y ⁻¹' C from hω), indicator_of_notMem hω, mul_zero]
  have e2 : (Y ⁻¹' C).indicator (fun ω => Complex.exp (Complex.I * (Y ω Ψ : ℂ))) = fun ω =>
      C.indicator (fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ))) (Y ω) := by
    funext ω
    by_cases hω : Y ω ∈ C
    · rw [indicator_of_mem (show ω ∈ Y ⁻¹' C from hω), indicator_of_mem hω]
    · rw [indicator_of_notMem (show ω ∉ Y ⁻¹' C from hω), indicator_of_notMem hω]
  rw [e1, e2]
  exact key

/-- The factorization identity on a union of two disjoint events. -/
theorem FactorsOn.union (hXm : Measurable X) (hYm : Measurable Y) {m₁ m₂ : Set Ω}
    (h₁ : WholeField.FactorsOn P X Y m₁) (h₂ : WholeField.FactorsOn P X Y m₂) (hd : Disjoint m₁ m₂)
    (hm₂ : MeasurableSet m₂) : WholeField.FactorsOn P X Y (m₁ ∪ m₂) := by
  intro Φ Ψ
  have hXΦ : Measurable fun ω => X ω Φ := (measurable_distOn_apply Φ).comp hXm
  have hYΨ : Measurable fun ω => Y ω Ψ := (measurable_distOn_apply Ψ).comp hYm
  have hF := LocalSets.integrable_exp_mul_exp (P := P) hXΦ hYΨ
  have hg := GFF.integrable_exp_I_mul (P := P) hYΨ
  rw [setIntegral_union hd hm₂ hF.integrableOn hF.integrableOn, setIntegral_union hd hm₂ hg.integrableOn
    hg.integrableOn, h₁ Φ Ψ, h₂ Φ Ψ, mul_add]

omit [IsProbabilityMeasure P] in
/-- **The factorization identity on an event almost surely determined by `Y`.** -/
theorem factorsOn_of_measurableSet_aeSigma (hXm : Measurable X) (hYm : Measurable Y) (hind : IndepFun X Y P)
    {S : Set Ω} (hS : MeasurableSet[aeSigma (MeasurableSpace.comap Y inferInstance) P] S) :
    WholeField.FactorsOn P X Y S := by
  obtain ⟨S', ⟨C, hC, rfl⟩, hSS'⟩ := hS
  exact (factorsOn_preimage hXm hYm hind hC).congr_ae hSS'.symm

end Factor

/-! ### Kernel tools -/

section AeSigma

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- Events almost surely equal to events almost surely in `m` are almost surely in `m`. -/
theorem aeSigma_le_aeSigma {ν : Measure Ω} (h : m' ≤ aeSigma m ν) : aeSigma m' ν ≤ aeSigma m ν := by
  rintro s ⟨s', hs', hss'⟩
  obtain ⟨s'', hs'', hs's''⟩ := h s' hs'
  exact ⟨s'', hs'', hss'.trans hs's''⟩

end AeSigma

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Integrating over the conditional laws**: for a `𝒢`-event `E₀`, an event `S` and an integrable `F`,
`∫_{S ∩ E₀} F dP = ∫_{E₀} (∫_S F dν_{ω₀}) dP(ω₀)`, `ν = condExpKernel P 𝒢`. -/
theorem setIntegral_inter_eq_condExpKernel (h𝒢 : 𝒢 ≤ mΩ) {E₀ S : Set Ω} (hE₀ : MeasurableSet[𝒢] E₀)
    (hS : MeasurableSet S) {F : Ω → ℂ} (hF : Integrable F P) :
    ∫ ω in S ∩ E₀, F ω ∂P = ∫ ω₀ in E₀, (∫ ω in S, F ω ∂(condExpKernel P 𝒢 ω₀)) ∂P := by
  rw [inter_comm, ← setIntegral_indicator hS, ← setIntegral_condExp h𝒢 (hF.indicator hS) hE₀]
  refine setIntegral_congr_ae (h𝒢 _ hE₀) ?_
  filter_upwards [condExp_ae_eq_integral_condExpKernel h𝒢 (hF.indicator hS)] with ω₀ hω₀ _
  rw [hω₀, integral_indicator hS]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- A random distribution whose pairings are almost surely functions of `Y` is measurable for the events almost
surely determined by `Y`. -/
theorem measurable_aeSigma_of_ae_eq {ν : Measure Ω} {Y Y' : Ω → DistOn upperHalfPlaneOpens}
    (hY' : ∀ φ : TestOn upperHalfPlaneOpens, ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      (fun ω => Y' ω φ) =ᵐ[ν] fun ω => g (Y ω)) :
    Measurable[aeSigma (MeasurableSpace.comap Y inferInstance) ν] Y' := by
  refine @LQGMetric.measurable_distOn_iff _ _ (aeSigma (MeasurableSpace.comap Y inferInstance) ν) _ |>.2
    fun φ => ?_
  obtain ⟨g, hg, hgae⟩ := hY' φ
  intro B hB
  refine ⟨Y ⁻¹' (g ⁻¹' B), ⟨g ⁻¹' B, hg hB, rfl⟩, ?_⟩
  filter_upwards [hgae] with ω hω
  simp only [mem_preimage, hω]

end Kernel

/-! ### The past of a restarted path -/

section Past

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {α : Ω → ℝ≥0 → ℂ} {t₀ : ℝ≥0}

/-- **The past at the restart**: the σ-algebra of the history through `t₀` of the path frozen after `t₀` (Lemma
6.2's stopped-history σ-algebra of one path at the deterministic time `t₀`). -/
@[instance_reducible]
def pastSigma (α : Ω → ℝ≥0 → ℂ) (t₀ : ℝ≥0) : MeasurableSpace Ω :=
  stoppedHistSigma (fun _ : Fin 1 => fun ω => frozenPath (α ω) t₀) (fun _ _ => ((t₀ : ℝ≥0) : ℝ≥0∞))

theorem measurable_pastHist (hαm : ∀ t, Measurable fun ω => α ω t) :
    Measurable fun ω (_ : Fin 1) => histOf (pathCoord (frozenPath (α ω) t₀)) ((t₀ : ℝ≥0) : ℝ≥0∞) := by
  have hcm : Measurable fun ω => pathCoord (frozenPath (α ω) t₀) := Measurable.of_eval fun q => hαm _
  exact measurable_pi_iff.2 fun _ => measurable_histOf.comp (measurable_const.prodMk hcm)

theorem pastSigma_le (hαm : ∀ t, Measurable fun ω => α ω t) : pastSigma α t₀ ≤ mΩ :=
  (measurable_pastHist hαm).comap_le

omit mΩ in
/-- The explored set of the frozen path through `t₀`. -/
theorem explored_frozenPath (ω : Ω) :
    explored (fun _ : Fin 1 => fun ω => frozenPath (α ω) t₀) (fun _ _ => ((t₀ : ℝ≥0) : ℝ≥0∞)) ω =
      α ω '' Icc 0 t₀ ∩ H := by
  have e : (fun t : ℝ≥0 => frozenPath (α ω) t₀ t) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (t₀ : ℝ≥0∞)} = α ω '' Icc 0 t₀ := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ⟨zero_le, ENNReal.coe_le_coe.1 ht⟩, (frozenPath_of_le (ENNReal.coe_le_coe.1 ht)).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ENNReal.coe_le_coe.2 ht.2, frozenPath_of_le ht.2⟩
  simp only [explored, iUnion_const, e]

omit mΩ in
/-- The avoidance events of the past are events of the past. -/
theorem measurableSet_disjoint_pastSigma (hαc : ∀ ω, Continuous (α ω)) {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) :
    MeasurableSet[pastSigma α t₀] {ω | Disjoint (α ω '' Icc 0 t₀ ∩ H) V} := by
  set Ψ : Ω → Fin 1 → Hist := fun ω _ => histOf (pathCoord (frozenPath (α ω) t₀)) ((t₀ : ℝ≥0) : ℝ≥0∞)
  have hc : ∀ (i : Fin 1) ω, Continuous ((fun _ : Fin 1 => fun ω => frozenPath (α ω) t₀) i ω) :=
    fun _ ω => continuous_frozenPath (hαc ω)
  have e : {ω | Disjoint (α ω '' Icc 0 t₀ ∩ H) V}ᶜ =
      ⋃ q : ℚ≥0, {ω | (((q : ℝ≥0) : ℝ≥0∞)) ≤ (t₀ : ℝ≥0∞) ∧ (Ψ ω 0).2 q ∈ V} := by
    ext ω
    simp only [mem_compl_iff, mem_ofPred_eq, Set.not_disjoint_iff_nonempty_inter, mem_iUnion]
    rw [← explored_frozenPath, explored_inter_nonempty_iff hc hV hVH ω]
    constructor
    · rintro ⟨_, q, hq, hqV⟩
      refine ⟨q, hq, ?_⟩
      change stopCoord (pathCoord (frozenPath (α ω) t₀)) ((t₀ : ℝ≥0) : ℝ≥0∞) q ∈ V
      rw [stopCoord_of_le hq]
      exact hqV
    · rintro ⟨q, hq, hqV⟩
      refine ⟨0, q, hq, ?_⟩
      change stopCoord (pathCoord (frozenPath (α ω) t₀)) ((t₀ : ℝ≥0) : ℝ≥0∞) q ∈ V at hqV
      rwa [stopCoord_of_le hq] at hqV
  rw [← compl_compl {ω | Disjoint (α ω '' Icc 0 t₀ ∩ H) V}, e]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun q => ?_)
  by_cases hq : (((q : ℝ≥0) : ℝ≥0∞)) ≤ (t₀ : ℝ≥0∞)
  · simp only [hq, true_and]
    exact ⟨{p : Fin 1 → Hist | (p 0).2 q ∈ V},
      ((measurable_pi_apply q).comp (measurable_snd.comp (measurable_pi_apply 0))) hV.measurableSet, rfl⟩
  · simp only [hq, false_and, ofPred_false, MeasurableSet.empty]

end Past

/-! ### The gluing theorem -/

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `pushTest` depends on the conformality proof only through the chart. -/
theorem pushTest_congr {c₁ c₂ : Chart} (h₁ : c₁.IsConformal) (h₂ : c₂.IsConformal) (e : c₁ = c₂)
    (φ : TestOn upperHalfPlaneOpens) : Chart.pushTest h₁ φ = Chart.pushTest h₂ φ := by
  subst e
  rfl

/-- If the old curve carries the frontier of the chart domain in `ℍ` and avoids `U ⊆ ℍ`, then `U ∖ dom c` is open. -/
theorem isOpen_sdiff_dom {c : Chart} {K U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    (hfr : ∀ z ∈ H, z ∈ closure (c.dom : Set ℂ) → z ∉ c.dom → z ∈ K) (hKU : Disjoint K U) :
    IsOpen (U \ c.dom) := by
  have e : U \ c.dom = U ∩ (closure (c.dom : Set ℂ))ᶜ := by
    ext z
    refine ⟨fun hz => ⟨hz.1, fun hcl => Set.disjoint_left.1 hKU (hfr z (hUH hz.1) hcl hz.2) hz.1⟩,
      fun hz => ⟨hz.1, fun hd => hz.2 (subset_closure hd)⟩⟩
  rw [e]
  exact hU.inter isClosed_closure.isOpen_compl

/-- **Entrance-history locality of a path restarted in a chart** (Lemma 6.2's hypothesis, glued at the restart time
`t₀`). Let `h` be a zero-boundary GFF on `ℍ` and `α` a continuous path started at a point `x ∉ ℍ`. Suppose

* (past) the path frozen after `t₀` is field-determined and entrance-history local;
* (chart) for almost every `ω₀`, `c ω₀` is a conformal chart whose domain has its frontier in `ℍ` on the old curve
  `α(ω₀)([0, t₀])`, and under the regular conditional law `ν_{ω₀}` given the past the chart field `h' ω₀` is
  `h ∘ inv + m ω₀` (`inv` of `c ω₀`, `m ω₀` deterministic) and a zero-boundary GFF;
* (continuation) whenever the old curve avoids an open `U ⊆ ℍ`, the history of `α` through its first entrance into
  `U` is `ν_{ω₀}`-almost surely determined by the Markov complement of `h' ω₀` along the chart pre-image of `U`.

The chart data are indexed by the conditioning point `ω₀` (no measurability in `ω₀` is needed).

Then `α` is entrance-history local for `h`. -/
theorem isEntranceHistoryLocal_of_restart {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hxH : x ∉ H)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = x) (hαm : ∀ t, Measurable fun ω => α ω t) {t₀ : ℝ≥0}
    (hdet₀ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) t₀ t) =ᵐ[P] fun ω => f (h ω))
    (hloc₀ : IsEntranceHistoryLocal (fun ω => frozenPath (α ω) t₀) h P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom → z ∈ α ω '' Icc 0 t₀)
    {h' : Ω → Ω → DistOn upperHalfPlaneOpens} {m : Ω → TestOn upperHalfPlaneOpens → ℝ}
    (hh' : ∀ᵐ ω₀ ∂P, ∀ φ, ∀ᵐ ω ∂(condExpKernel P (pastSigma α t₀) ω₀),
      h' ω₀ ω φ = h ω (Chart.pushTest (hc ω₀) φ) + m ω₀ φ)
    (hZB : ∀ᵐ ω₀ ∂P,
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (h' ω₀) (condExpKernel P (pastSigma α t₀) ω₀))
    (hcont : ∀ᵐ ω₀ ∂P, ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → Disjoint (α ω₀ '' Icc 0 t₀) U →
      ∀ G' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable G' →
        GFF.IsMarkovDecomposition (MarkovChart.chartPreOpens (hc ω₀) U) upperHalfPlaneOpens (h' ω₀)
          (fun ω => G' (h' ω₀ ω)) (condExpKernel P (pastSigma α t₀) ω₀) →
        Measurable[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G' (h' ω₀ ω)) inferInstance)
          (condExpKernel P (pastSigma α t₀) ω₀)]
          (fun ω => histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω))))) :
    IsEntranceHistoryLocal α h P := by
  intro U G hUH hG hd
  classical
  have hhm : Measurable h := hh.measurable
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => G (h ω) with hXdef
  set Y : Ω → DistOn upperHalfPlaneOpens := fun ω => markovCompl G (h ω) with hYdef
  have hXm : Measurable X := hG.comp hhm
  have hYm : Measurable Y := (measurable_markovCompl hG).comp hhm
  have hind : IndepFun X Y P := hd.indepFun
  have hU' : U ≤ upperHalfPlaneOpens := hUH
  have hxU : x ∉ (U : Set ℂ) := fun hx => hxH (hUH hx)
  have h𝒢 : pastSigma α t₀ ≤ mΩ := pastSigma_le hαm
  set Hα : Ω → Hist := fun ω => histOf (pathCoord (α ω)) (firstEntrance U (pathCoord (α ω))) with hHαdef
  have hcm' : Measurable fun ω => pathCoord (α ω) := Measurable.of_eval fun q => hαm q
  have hFm := measurable_firstEntrance (U := (U : Set ℂ)) U.isOpen.measurableSet
  have hHαm : Measurable Hα := measurable_histOf.comp ((hFm.comp hcm').prodMk hcm')
  have hE : {ω | AvoidsUpTo (α ω) (firstEntrance U (pathCoord (α ω))) U} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact fun t ht => notMem_of_le_firstEntrance U.isOpen (hαc ω) (by rw [hα0]; exact hxU) ht
  rw [hE]
  have h𝓜 : markedHistSigma univ Hα ≤ MeasurableSpace.comap Hα inferInstance := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, (univ_inter _).symm⟩
  refine WholeField.condIndepEv_of_factorsOn hXm hYm (h𝓜.trans hHαm.comap_le) fun S hS => ?_
  obtain ⟨B, hB, rfl⟩ := h𝓜 S hS
  -- the past avoidance event
  set E₀ : Set Ω := {ω | Disjoint (α ω '' Icc 0 t₀ ∩ H) (U : Set ℂ)} with hE₀def
  have hE₀ : MeasurableSet[pastSigma α t₀] E₀ := measurableSet_disjoint_pastSigma hαc U.isOpen hUH
  have hE₀' : ∀ ω, ω ∈ E₀ ↔ Disjoint (α ω '' Icc 0 t₀) (U : Set ℂ) := fun ω => by
    simp only [hE₀def, mem_ofPred_eq]
    constructor
    · intro hd' 
      exact Set.disjoint_left.2 fun z hz hzU => Set.disjoint_left.1 hd' ⟨hz, hUH hzU⟩ hzU
    · exact fun hd' => hd'.mono_left inter_subset_left
  have hsplit : Hα ⁻¹' B = (Hα ⁻¹' B ∩ E₀ᶜ) ∪ (Hα ⁻¹' B ∩ E₀) := by
    rw [← inter_union_distrib_left, compl_union_self, inter_univ]
  rw [hsplit]
  refine FactorsOn.union hXm hYm ?_ ?_ (disjoint_compl_left.mono inter_subset_right inter_subset_right)
    ((hHαm hB).inter (h𝒢 _ hE₀))
  · -- off the past avoidance event: the frozen path's history, determined by `Y`
    set Hc : Ω → Hist := fun ω =>
      histOf (pathCoord (frozenPath (α ω) t₀)) (firstEntrance U (pathCoord (frozenPath (α ω) t₀))) with hHcdef
    have hHc : Measurable[aeSigma (MeasurableSpace.comap Y inferInstance) P] Hc :=
      measurable_entranceHist hhm (fun ω => continuous_frozenPath (hαc ω)) (fun t => hαm _) hdet₀ hloc₀ U G hUH
        hG hd fun ω => by rw [frozenPath_zero, hα0]; exact hxU
    have e : Hα ⁻¹' B ∩ E₀ᶜ = Hc ⁻¹' (B ∩ {p : Hist | p.1 ≠ ⊤}) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, hE₀', mem_ofPred_eq]
      rw [← firstEntrance_frozenPath_eq_top_iff U.isOpen (hαc ω)]
      constructor
      · rintro ⟨hBω, hne⟩
        refine ⟨?_, hne⟩
        rw [hHcdef]
        dsimp only
        rw [histOf_frozenPath_eq U.isOpen (hαc ω) (by rwa [← firstEntrance_frozenPath_eq_top_iff U.isOpen (hαc ω)])]
        exact hBω
      · rintro ⟨hBω, hne⟩
        refine ⟨?_, hne⟩
        have := histOf_frozenPath_eq U.isOpen (hαc ω) (t₀ := t₀)
          (by rwa [← firstEntrance_frozenPath_eq_top_iff U.isOpen (hαc ω)])
        rw [hHcdef] at hBω
        dsimp only at hBω
        rw [this] at hBω
        exact hBω
    rw [e]
    exact factorsOn_of_measurableSet_aeSigma hXm hYm hind
      (hHc (hB.inter (measurable_fst (measurableSet_singleton (⊤ : ℝ≥0∞)).compl)))
  · -- on the past avoidance event: the factorization under the regular conditional laws
    have hc1 : ∀ (i : Fin 1) ω, Continuous ((fun _ : Fin 1 => fun ω => frozenPath (α ω) t₀) i ω) :=
      fun _ ω => continuous_frozenPath (hαc ω)
    have hloc𝒢 : WholeField.IsHistoryAvoidanceLocal (pastSigma α t₀)
        (explored (fun _ : Fin 1 => fun ω => frozenPath (α ω) t₀) (fun _ _ => ((t₀ : ℝ≥0) : ℝ≥0∞))) h P :=
      isHistoryAvoidanceLocal_explored (x := fun _ => x) (S := fun _ _ _ => ((t₀ : ℝ≥0) : ℝ≥0∞)) hhm hc1
        (fun _ ω => by rw [frozenPath_zero, hα0]) (fun _ t => hαm _) (fun _ => hdet₀) (fun _ => hloc₀)
        (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
    have hA : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → MeasurableSet[pastSigma α t₀] {ω | Disjoint
        (explored (fun _ : Fin 1 => fun ω => frozenPath (α ω) t₀) (fun _ _ => ((t₀ : ℝ≥0) : ℝ≥0∞)) ω) V} :=
      fun V hV => by
        simp_rw [explored_frozenPath]
        exact measurableSet_disjoint_pastSigma hαc V.isOpen hV
    have hK := Theorem14.WalkLaw.ae_isMarkovDecomposition_condExpKernel hh h𝒢 hA hloc𝒢 hUH hG hd
    have hgood : ∀ᵐ ω₀ ∂P, ω₀ ∈ E₀ →
        WholeField.FactorsOn (condExpKernel P (pastSigma α t₀) ω₀) X Y (Hα ⁻¹' B) ∧
          ∀ Φ : TestOn upperHalfPlaneOpens,
            ∫ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂(condExpKernel P (pastSigma α t₀) ω₀) =
              ∫ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂P := by
      filter_upwards [hK, hh', hZB, hcont] with ω₀ hK₀ hhν hZB₀ hcont₀ hω₀
      have hdisj : Disjoint (α ω₀ '' Icc 0 t₀) (U : Set ℂ) := (hE₀' ω₀).1 hω₀
      rw [explored_frozenPath] at hK₀
      obtain ⟨hMD, hlaw⟩ := hK₀ hω₀
      obtain ⟨G', hG'm, hG'⟩ := LocalSets.exists_markovMap (MarkovChart.chartPreOpens (hc ω₀) U)
        (MarkovChart.chartPre_subset_H _ _)
      have hd' := hG' hZB₀
      have hHist := hcont₀ U hUH hdisj G' hG'm hd'
      have hUD := isOpen_sdiff_dom U.isOpen hUH (hfr ω₀) hdisj
      have hY' := MarkovChart.ae_markovCompl_pushTest_eq (hc ω₀) hUH hUD hMD.isZBGFFExtOn
        (ae_isHarmonicDistOn_of_isMarkovDecomposition hU' hMD) hd' (m ω₀) hhν
      have hY'm : Measurable[aeSigma (MeasurableSpace.comap Y inferInstance) (condExpKernel P (pastSigma α t₀) ω₀)]
          (fun ω => markovCompl G' (h' ω₀ ω)) := by
        refine measurable_aeSigma_of_ae_eq fun φ => ⟨fun T => T (Chart.pushTest (hc ω₀) φ) + m ω₀ φ,
          (measurable_distOn_apply _).add_const _, ?_⟩
        filter_upwards [hY' φ] with ω hω
        show (h' ω₀ ω - G' (h' ω₀ ω)) φ = (h ω - G (h ω)) (Chart.pushTest (hc ω₀) φ) + m ω₀ φ
        rw [sub_apply, sub_apply]
        exact hω
      have hS : MeasurableSet[aeSigma (MeasurableSpace.comap Y inferInstance)
          (condExpKernel P (pastSigma α t₀) ω₀)] (Hα ⁻¹' B) :=
        aeSigma_le_aeSigma hY'm.comap_le _ (hHist hB)
      refine ⟨factorsOn_of_measurableSet_aeSigma hXm hYm hMD.indepFun hS, fun Φ => ?_⟩
      have hf : Measurable fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Φ : ℂ)) :=
        GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)
      rw [← integral_map hXm.aemeasurable hf.aestronglyMeasurable, hlaw,
        integral_map hXm.aemeasurable hf.aestronglyMeasurable]
    intro Φ Ψ
    have hXΦ : Measurable fun ω => X ω Φ := (measurable_distOn_apply Φ).comp hXm
    have hYΨ : Measurable fun ω => Y ω Ψ := (measurable_distOn_apply Ψ).comp hYm
    rw [setIntegral_inter_eq_condExpKernel h𝒢 hE₀ (hHαm hB) (LocalSets.integrable_exp_mul_exp hXΦ hYΨ),
      setIntegral_inter_eq_condExpKernel h𝒢 hE₀ (hHαm hB) (GFF.integrable_exp_I_mul hYΨ),
      ← integral_const_mul]
    refine setIntegral_congr_ae (h𝒢 _ hE₀) ?_
    filter_upwards [hgood] with ω₀ hω₀ hmem
    obtain ⟨hfac, hlawΦ⟩ := hω₀ hmem
    rw [hfac Φ Ψ, hlawΦ]

/-- **The restart step for frozen paths** (finitely many pieces). If the path frozen after `t₀` is field-determined
and entrance-history local, and the path frozen after a later `t₁` satisfies the chart and continuation hypotheses
of `isEntranceHistoryLocal_of_restart` at `t₀`, then the path frozen after `t₁` is entrance-history local. Applied
at the successive restart times `t₀ ≤ t₁ ≤ ⋯ ≤ t_n` this gives the locality of every finite staged path. -/
theorem isEntranceHistoryLocal_frozenPath_of_restart {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hxH : x ∉ H)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = x) (hαm : ∀ t, Measurable fun ω => α ω t)
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    (hdet₀ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) t₀ t) =ᵐ[P] fun ω => f (h ω))
    (hloc₀ : IsEntranceHistoryLocal (fun ω => frozenPath (α ω) t₀) h P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom → z ∈ α ω '' Icc 0 t₀)
    {h' : Ω → Ω → DistOn upperHalfPlaneOpens} {m : Ω → TestOn upperHalfPlaneOpens → ℝ}
    (hh' : ∀ᵐ ω₀ ∂P, ∀ φ, ∀ᵐ ω ∂(condExpKernel P (pastSigma α t₀) ω₀),
      h' ω₀ ω φ = h ω (Chart.pushTest (hc ω₀) φ) + m ω₀ φ)
    (hZB : ∀ᵐ ω₀ ∂P,
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (h' ω₀) (condExpKernel P (pastSigma α t₀) ω₀))
    (hcont : ∀ᵐ ω₀ ∂P, ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → Disjoint (α ω₀ '' Icc 0 t₀) U →
      ∀ G' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable G' →
        GFF.IsMarkovDecomposition (MarkovChart.chartPreOpens (hc ω₀) U) upperHalfPlaneOpens (h' ω₀)
          (fun ω => G' (h' ω₀ ω)) (condExpKernel P (pastSigma α t₀) ω₀) →
        Measurable[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G' (h' ω₀ ω)) inferInstance)
          (condExpKernel P (pastSigma α t₀) ω₀)]
          (fun ω => histOf (pathCoord (frozenPath (α ω) t₁)) (firstEntrance U (pathCoord (frozenPath (α ω) t₁))))) :
    IsEntranceHistoryLocal (fun ω => frozenPath (α ω) t₁) h P := by
  have e₀ : ∀ ω, frozenPath (frozenPath (α ω) t₁) t₀ = frozenPath (α ω) t₀ := fun ω => frozenPath_frozenPath ht
  have ei : ∀ ω, frozenPath (α ω) t₁ '' Icc 0 t₀ = α ω '' Icc 0 t₀ := fun ω => by
    refine image_congr fun s hs => frozenPath_of_le (hs.2.trans ht)
  have eσ : pastSigma (fun ω => frozenPath (α ω) t₁) t₀ = pastSigma α t₀ := by
    simp only [pastSigma, e₀]
  refine isEntranceHistoryLocal_of_restart hh hxH (fun ω => continuous_frozenPath (hαc ω))
    (fun ω => by rw [frozenPath_zero, hα0]) (fun t => hαm _) (t₀ := t₀) (by simpa only [e₀] using hdet₀)
    (by simpa only [e₀] using hloc₀) hc (fun ω => by rw [ei]; exact hfr ω) (by rw [eσ]; exact hh')
    (by rw [eσ]; exact hZB) ?_
  rw [eσ]
  simpa only [ei] using hcont

end Main

end StagedEntrance

end Restart

end InteractingSLE
