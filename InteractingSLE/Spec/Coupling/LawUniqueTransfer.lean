/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.LawUniqueHistory
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec7.TwoForceMainDetermine

/-!
# Transfer of field determination along equal joint laws (ruling R33)

Packet PROVE-OHC-UNIQ. Ruling R33: field determination proved for one coupling satisfying the frozen
`IsOptionalHullCoupling` reaches every such coupling once the joint law of the field and the killed
driving history is the same in all of them. This file proves the transfer and states the uniqueness
of the joint law as a named proposition.

* `IsOptionalHullLawUnique κ xL xR ρL ρR`: any two couplings satisfying the frozen optional hull
  specification for `κ` and the force word have the same joint law of the field `h` and the killed
  driving history `killedHistory W VL VR ζ` (`LawUniqueHistory.lean`). This is the lemma of ruling R33;
  it is **not proved** here (see `LawUniqueKernel.lean` and the handoff for the exact obstruction).
* `ae_mem_of_map_eq`: any almost sure property of the joint law transfers between two couplings with
  equal joint laws.
* `isFieldDeterminedHistory_of_map_eq`: field determination of the killed driving history
  (`LP.IsFieldDeterminedHistory`, the input form of the frozen Theorem 1.2 in `LPAssembly.lean`)
  transfers along equal joint laws to a coupling whose driving process is continuous before its
  lifetime. The killed history only records dyadic times; the determining map of the second coupling
  reads the first one's along dyadic times `⌊2^n t⌋ / 2^n ↑ t` and takes the limit.
* `hasFieldDeterminedHistories_of_isOptionalHullLawUnique`: under `IsOptionalHullLawUnique`, one
  field-determined reference coupling gives `LP.HasFieldDeterminedHistories` (every coupling is field
  determined). `wwTheorem17Statement_of_isOptionalHullLawUnique` is the `κ = 4` instance (Wang–Wu's
  determination, ruling R31, reaching `LP.WWTheorem17Statement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace LawUnique

/-- **Uniqueness of the joint law of an optional hull coupling** (ruling R33; the joint-law part of
the specification's Aux. lemma 51, p. 242, and Proposition 7.3, p. 242, for every parameter): any two
couplings satisfying the frozen optional hull specification of Theorem 1.1 for `κ` and the force
word, on probability spaces in the universes `u` and `v`, have the same joint law of the field and the
killed driving history. -/
def IsOptionalHullLawUnique (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∀ {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (𝓕₁ : Filtration ℝ≥0 m₁) (W₁ : ℝ≥0 → Ω₁ → ℝ) (VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ)
    (VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (ζ₁ : Ω₁ → ℝ≥0∞)
    (h₁ : Ω₁ → LQGMetric.DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ →
    ∀ {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 m₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ)
      (VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
      (h₂ : Ω₂ → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
        P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω))

/-! ### Almost sure properties of the joint law transfer -/

section Generic

variable {Ω₁ Ω₂ α β : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  [MeasurableSpace α] [MeasurableSpace β] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}

/-- **Any almost sure property of the joint law transfers**: if `(h₁, H₁)` and `(h₂, H₂)` have the
same joint law and `(h₁, H₁) ∈ S` almost surely for a measurable `S`, then `(h₂, H₂) ∈ S` almost
surely. -/
theorem ae_mem_of_map_eq {h₁ : Ω₁ → α} {H₁ : Ω₁ → β} {h₂ : Ω₂ → α} {H₂ : Ω₂ → β}
    (hm₁ : AEMeasurable (fun ω => (h₁ ω, H₁ ω)) P₁) (hm₂ : AEMeasurable (fun ω => (h₂ ω, H₂ ω)) P₂)
    (hlaw : P₁.map (fun ω => (h₁ ω, H₁ ω)) = P₂.map (fun ω => (h₂ ω, H₂ ω)))
    {S : Set (α × β)} (hS : MeasurableSet S) (h : ∀ᵐ ω ∂P₁, (h₁ ω, H₁ ω) ∈ S) :
    ∀ᵐ ω ∂P₂, (h₂ ω, H₂ ω) ∈ S := by
  have h' : ∀ᵐ p ∂(P₁.map fun ω => (h₁ ω, H₁ ω)), p ∈ S := (ae_map_iff hm₁ hS).2 h
  rw [hlaw] at h'
  exact (ae_map_iff hm₂ hS).1 h'

end Generic

/-! ### Transfer of field determination -/

section Determination

variable {nL nR : ℕ}

/-- The killed history read off a determining map `Ψ` of the type used by `LP.IsFieldDeterminedHistory`
(lifetime, driving path, left and right force paths). -/
def historyOfPaths (x : ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) :
    HistorySpace nL nR :=
  (x.1, fun p => if (dyadicTime p : ℝ≥0∞) < x.1 then
    (x.2.1 (dyadicTime p), (fun i => x.2.2.1 i (dyadicTime p)), fun i => x.2.2.2 i (dyadicTime p))
    else 0)

theorem measurable_historyOfPaths :
    Measurable (historyOfPaths (nL := nL) (nR := nR)) := by
  refine measurable_fst.prodMk (Measurable.of_eval fun p => ?_)
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  refine ((measurable_pi_apply _).comp measurable_snd.fst).prodMk
    ((Measurable.of_eval fun i => ?_).prodMk (Measurable.of_eval fun i => ?_))
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply i).comp measurable_snd.snd.fst)
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply i).comp measurable_snd.snd.snd)

/-- The paths reconstructed from their values at the dyadic times below each time: the limit of
`x(⌊2^n t⌋ / 2^n)` as `n → ∞`. -/
def pathsOfDyadic (x : ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) :
    ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ) :=
  (x.1, (fun t => limUnder atTop fun n => x.2.1 (dyadicTime (lowerDyadic t n))),
    (fun i t => limUnder atTop fun n => x.2.2.1 i (dyadicTime (lowerDyadic t n))),
    fun i t => limUnder atTop fun n => x.2.2.2 i (dyadicTime (lowerDyadic t n)))

theorem measurable_pathsOfDyadic : Measurable (pathsOfDyadic (nL := nL) (nR := nR)) := by
  have hlim : ∀ (f : ℕ → (ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) → ℝ),
      (∀ n, Measurable (f n)) → Measurable fun x => limUnder atTop fun n => f n x :=
    fun f hf => (StronglyMeasurable.limUnder fun n => (hf n).stronglyMeasurable).measurable
  refine measurable_fst.prodMk ((Measurable.of_eval fun t => hlim _ fun n => ?_).prodMk
    ((Measurable.of_eval fun i => Measurable.of_eval fun t => hlim _ fun n => ?_).prodMk
      (Measurable.of_eval fun i => Measurable.of_eval fun t => hlim _ fun n => ?_)))
  · exact (measurable_pi_apply _).comp measurable_snd.fst
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply i).comp measurable_snd.snd.fst)
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply i).comp measurable_snd.snd.snd)

/-- A path continuous on `[0, T)` is the limit of its values at the dyadic times below `t < T`. -/
theorem tendsto_lowerDyadic_of_continuousOn {E : Type*} [TopologicalSpace E] {f : ℝ≥0 → E}
    {T : ℝ≥0∞} (hf : ContinuousOn f {s | (s : ℝ≥0∞) < T}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    Tendsto (fun n => f (dyadicTime (lowerDyadic t n))) atTop (𝓝 (f t)) := by
  have hin : ∀ n, dyadicTime (lowerDyadic t n) ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < T} := fun n =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
  exact ((hf t ht).tendsto).comp
    (tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicTime_lowerDyadic t, Eventually.of_forall hin⟩)

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}

/-- **Field determination transfers along equal joint laws.** If the joint laws of the field and the
killed driving history agree in two couplings, the first coupling's killed driving history is a Borel
function of its field, and the second coupling's driving process is almost surely continuous before
its lifetime, then the second coupling's killed driving history is a Borel function of its field. -/
theorem isFieldDeterminedHistory_of_map_eq
    {h₁ : Ω₁ → LQGMetric.DistOn upperHalfPlaneOpens} {W₁ : ℝ≥0 → Ω₁ → ℝ}
    {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (hh₁ : Measurable h₁) (hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁)
    {h₂ : Ω₂ → LQGMetric.DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ}
    {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hh₂ : Measurable h₂) (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂)
    (hlaw : P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)))
    (hcont₂ : ∀ᵐ ω ∂P₂, ContinuousOn (fun t => W₂ t ω) {t | (t : ℝ≥0∞) < ζ₂ ω} ∧
      (∀ i, ContinuousOn (fun t => VL₂ i t ω) {t | (t : ℝ≥0∞) < ζ₂ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR₂ i t ω) {t | (t : ℝ≥0∞) < ζ₂ ω})
    (hdet : LP.IsFieldDeterminedHistory P₁ h₁ W₁ VL₁ VR₁ ζ₁) :
    LP.IsFieldDeterminedHistory P₂ h₂ W₂ VL₂ VR₂ ζ₂ := by
  obtain ⟨Ψ, hΨ, hae⟩ := hdet
  -- the first coupling's killed history is `historyOfPaths ∘ Ψ` of its field
  have hK₁ : (fun ω => killedHistory W₁ VL₁ VR₁ ζ₁ ω) =ᵐ[P₁]
      fun ω => historyOfPaths (Ψ (h₁ ω)) := by
    filter_upwards [hae] with ω hω
    obtain ⟨hζ, hpath⟩ := hω
    simp only [killedHistory, historyOfPaths, hζ, Prod.mk.injEq, true_and]
    funext p
    split_ifs with hp
    · obtain ⟨e1, e2, e3⟩ := hpath _ hp
      rw [e1, funext e2, funext e3]
    · rfl
  -- it transfers to the second coupling
  have hK₂ : (fun ω => killedHistory W₂ VL₂ VR₂ ζ₂ ω) =ᵐ[P₂]
      fun ω => historyOfPaths (Ψ (h₂ ω)) :=
    Sec7.ae_eq_comp_of_map_eq (hh₁.prodMk (measurable_killedHistory hX₁)).aemeasurable
      (hh₂.prodMk (measurable_killedHistory hX₂)).aemeasurable hlaw
      (measurable_historyOfPaths.comp hΨ) hK₁
  -- the second coupling's paths are recovered from the dyadic values
  refine ⟨fun d => pathsOfDyadic (Ψ d), measurable_pathsOfDyadic.comp hΨ, ?_⟩
  filter_upwards [hK₂, hcont₂] with ω hω hc
  have hζ : (Ψ (h₂ ω)).1 = ζ₂ ω := (congrArg Prod.fst hω).symm
  have hdy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ ω → ∀ n,
      (W₂ (dyadicTime (lowerDyadic t n)) ω, (fun i => VL₂ i (dyadicTime (lowerDyadic t n)) ω),
        fun i => VR₂ i (dyadicTime (lowerDyadic t n)) ω) =
      ((Ψ (h₂ ω)).2.1 (dyadicTime (lowerDyadic t n)),
        (fun i => (Ψ (h₂ ω)).2.2.1 i (dyadicTime (lowerDyadic t n))),
        fun i => (Ψ (h₂ ω)).2.2.2 i (dyadicTime (lowerDyadic t n))) := by
    intro t ht n
    have hlt : (dyadicTime (lowerDyadic t n) : ℝ≥0∞) < ζ₂ ω :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
    have e := congrFun (congrArg Prod.snd hω) (lowerDyadic t n)
    simp only [killedHistory, historyOfPaths, hζ, hlt, ↓reduceIte] at e
    exact e
  refine ⟨hζ, fun t ht => ⟨?_, fun i => ?_, fun i => ?_⟩⟩
  · refine (Tendsto.limUnder_eq ?_)
    have := tendsto_lowerDyadic_of_continuousOn hc.1 ht
    refine this.congr fun n => ?_
    exact congrArg Prod.fst (hdy t ht n)
  · refine (Tendsto.limUnder_eq ?_)
    have := tendsto_lowerDyadic_of_continuousOn (hc.2.1 i) ht
    refine this.congr fun n => ?_
    exact congrFun (congrArg (fun x => x.2.1) (hdy t ht n)) i
  · refine (Tendsto.limUnder_eq ?_)
    have := tendsto_lowerDyadic_of_continuousOn (hc.2.2 i) ht
    refine this.congr fun n => ?_
    exact congrFun (congrArg (fun x => x.2.2) (hdy t ht n)) i

end Determination

/-! ### Consumers: every coupling is field determined once one is -/

/-- The driving process of an integrated `SLE_a(ρ)` evolution is almost surely continuous before its
lifetime (the conjuncts `continuousOn_w`, `continuousOn_vL`, `continuousOn_vR` of
`IsIntegratedSLEPath`). -/
theorem IsIntegratedSLEEvolution.ae_continuousOn_driving {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hev : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  filter_upwards [hev.2.2.2.2] with ω hp
  exact ⟨hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩

/-- **Field determination of every coupling from one reference** (ruling R33). Under
`IsOptionalHullLawUnique`, if one coupling satisfying the optional hull specification (on a
probability space in the universe `v`) has its killed driving history determined by its field, then
so has every such coupling (`LP.HasFieldDeterminedHistories`, the named input of the frozen Theorem
1.2's assembly in `LPAssembly.lean`). -/
theorem hasFieldDeterminedHistories_of_isOptionalHullLawUnique {κ : ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hU : IsOptionalHullLawUnique.{v, u} κ xL xR ρL ρR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hcoup
  obtain ⟨Ω₀, m₀, P₀, _, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup₀, hdet₀⟩ := href
  have hlaw := hU P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hcoup₀ P 𝓕 W VL VR B ζ h hcoup
  exact isFieldDeterminedHistory_of_map_eq hcoup₀.2.1 hcoup₀.2.2.2.1 hcoup.2.1 hcoup.2.2.2.1 hlaw
    (IsIntegratedSLEEvolution.ae_continuousOn_driving hcoup.1) hdet₀

/-- **The `κ = 4` instance** (rulings R31, R33): if the joint law of every optional hull coupling at
`κ = 4` is unique and, for every ordered force word, one such coupling is field determined (Wang–Wu's
Theorem 1.7 for the coupling of their Theorem 1.6, once it is shown to satisfy the frozen optional
hull specification), then the named input `LP.WWTheorem17Statement` of the frozen Theorem 1.2's
assembly holds. -/
theorem wwTheorem17Statement_of_isOptionalHullLawUnique
    (hU : ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsOrderedForceWord xL xR → IsOptionalHullLawUnique.{v, u} 4 xL xR ρL ρR)
    (href : ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
      (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
      ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
        (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧
          LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.WWTheorem17Statement.{u} := fun xL xR ρL ρR hF =>
  hasFieldDeterminedHistories_of_isOptionalHullLawUnique (hU xL xR ρL ρR hF)
    (href xL xR ρL ρR hF)

end LawUnique

end InteractingSLE
