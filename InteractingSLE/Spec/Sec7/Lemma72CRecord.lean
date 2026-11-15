/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72CChart
import InteractingSLE.Spec.Sec7.Lemma72BMain
import InteractingSLE.GFF.LocalSets.Prop39Indep

/-!
# The locality (L) conditionally on the exterior record

Packet PROVE-LEMMA72C. Specification §7.1, proofs of Lemmas 7.1–7.2 (`source/spec/p193-240.md` L600–L640,
pp. 224–227). Lemma 7.2's exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})` (`Lemma72B.pocketRecord`) consists of the two
outer curves and the field off the closed pocket. The field off `C̄` lies in the **germ** of every random set
`B ⊇ ℍ ∖ C` (a test function supported off `C̄` is supported in `B`, hence in every neighbourhood of `B`), so the
events of `Q` are events of the germ σ-algebra of `B` joined with any marks containing the outer curves and the events
`{supp φ ∩ C̄ = ∅}`. With `B = ℍ ∖ ψ⁻¹(ℍ ∖ K)` (`Lemma72CChart`), conditioning on an event of `Q` keeps the locality of
the mapped hull `K` for `h_ψ` — the locality half of `Lemma72C.PocketCondStatement` at one hull:

* `measurable_indicator_subset_germSigma`: `1{supp φ ⊆ B̄} · h(φ)` is measurable for the germ σ-algebra of `B`;
* `measurable_outField_germSigma`: for `ℍ ∖ C ⊆ B`, each coordinate of the field off `C̄` is measurable for the germs
  of `B` (of the field `h − T`, `T` deterministic) and the marks;
* `comap_pocketRecord_le`: `σ(Q) ≤ 𝒜_B ∨ ℋ`;
* **`isLocalSet_cond_pocketRecord`**: if `B = ℍ ∖ ψ⁻¹(ℍ ∖ K)` is a history-marked local set of the centred field for
  marks `ℋ` containing the outer curves and the closure events of the pocket, then `K` is a local set of
  `h_ψ = chartTransport c 1 a k h` under `P[· | G]` for every event `G` of `Q` of positive probability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open QuantumZipper (H zeroGFFTestCov)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec7.Lemma72C

open LQGMetric LocalSets WholeField

/-! ### The field on a random set is germ-measurable -/

section Germ

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- **The field on a random set is a germ variable**: `ω ↦ 1{supp φ ⊆ relClosureH (B ω)} · h ω φ` is measurable for
the germ σ-algebra of `B`. At every scale `δ`, the event `{supp φ ⊆ B̄}` is an event of `B` contained in
`{supp φ ⊆ germNbhd δ B}`, on which `h(φ)` is recorded. -/
theorem measurable_indicator_subset_germSigma (B : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) :
    Measurable[germSigma B h] ({ω | tsupport φ ⊆ relClosureH (B ω)}.indicator fun ω => h ω φ) := by
  set E : Set Ω := {ω | tsupport φ ⊆ relClosureH (B ω)} with hEdef
  intro S hS
  refine MeasurableSpace.measurableSet_iInf.2 fun n => ?_
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  set F : Set Ω := {ω | tsupport φ ⊆ germNbhd δ (B ω)} with hFdef
  have hEF : E ⊆ F := by
    intro ω hω z hz
    obtain ⟨hzH, hzc⟩ := hω hz
    exact ⟨hzH, Or.inl (thickening_subset_of_subset δ subset_union_left (closure_subset_thickening hδ _ hzc))⟩
  have hEm : MeasurableSet[germSigmaAt B h δ] E :=
    (le_sup_left : MeasurableSpace.comap B hittingSigma ≤ germSigmaAt B h δ) _
      ⟨_, measurableSet_subset_relClosureH φ.hasCompactSupport φ.tsupport_subset, rfl⟩
  have hgen : ∀ S' : Set ℝ, MeasurableSet S' → MeasurableSet[germSigmaAt B h δ] (F ∩ (fun ω => h ω φ) ⁻¹' S') :=
    fun S' hS' => (le_sup_right : MeasurableSpace.generateFrom _ ≤ germSigmaAt B h δ) _
      (MeasurableSpace.measurableSet_generateFrom ⟨φ, S', hS', rfl⟩)
  have hFm : MeasurableSet[germSigmaAt B h δ] F := by
    have := hgen univ MeasurableSet.univ
    rwa [preimage_univ, inter_univ] at this
  have e : (E.indicator fun ω => h ω φ) ⁻¹' S =
      (E ∩ (F ∩ (fun ω => h ω φ) ⁻¹' S)) ∪ (Eᶜ ∩ (fun _ : Ω => (0 : ℝ)) ⁻¹' S) := by
    ext ω
    by_cases hω : ω ∈ E
    · simp only [mem_preimage, indicator_of_mem hω, mem_union, mem_inter_iff, hω, hEF hω, true_and,
        mem_compl_iff, not_true_eq_false, false_and, or_false]
    · simp only [mem_preimage, indicator_of_notMem hω, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff,
        not_false_eq_true, true_and, false_or]
  rw [e]
  exact (hEm.inter (hgen S hS)).union (hEm.compl.inter (MeasurableSet.const _))

omit mΩ in
/-- **The field off the closed pocket is a germ variable of every `B ⊇ ℍ ∖ C`**, joined with marks recording the
events `{supp φ ∩ C̄ = ∅}`; for the field `h` and the germs of `h − T` (`T` deterministic). -/
theorem measurable_outField_germSigma {B C : Ω → Set ℂ} (hCB : ∀ ω, H \ C ω ⊆ B ω)
    {h : Ω → DistOn upperHalfPlaneOpens} (T : DistOn upperHalfPlaneOpens)
    (hS : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[ℋ] {ω | Disjoint (tsupport φ) (closure (C ω))})
    (φ : TestOn upperHalfPlaneOpens) :
    Measurable[germSigma B (fun ω => h ω - T) ⊔ ℋ] fun ω => Lemma72B.outField C h ω φ := by
  set S : Set Ω := {ω | Disjoint (tsupport φ) (closure (C ω))} with hSdef
  set E : Set Ω := {ω | tsupport φ ⊆ relClosureH (B ω)} with hEdef
  have hSE : S ⊆ E := by
    intro ω hω z hz
    have hzH : z ∈ H := φ.tsupport_subset hz
    have hzC : z ∉ C ω := fun hzC => Set.disjoint_left.1 hω hz (subset_closure hzC)
    exact ⟨hzH, subset_closure ⟨hCB ω ⟨hzH, hzC⟩, hzH⟩⟩
  have e : (fun ω => Lemma72B.outField C h ω φ) =
      S.indicator fun ω => (E.indicator fun ω => (h ω - T) φ) ω + T φ := by
    rw [Lemma72B.outField_eq_indicator]
    funext ω
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem (hSE hω), sub_apply, sub_add_cancel]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  rw [e]
  refine Measurable.indicator ?_ ((le_sup_right : ℋ ≤ germSigma B (fun ω => h ω - T) ⊔ ℋ) _ (hS φ))
  exact ((measurable_indicator_subset_germSigma B (fun ω => h ω - T) φ).add_const _).mono le_sup_left le_rfl

omit mΩ in
/-- **`σ(Q) ≤ 𝒜_B ∨ ℋ`** for the exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})`, when the outer curves and the closure
events of `C` are marks and `ℍ ∖ C ⊆ B`. -/
theorem comap_pocketRecord_le {B C : Ω → Set ℂ} (hCB : ∀ ω, H \ C ω ⊆ B ω) {β α : Ω → ℝ≥0 → ℂ}
    (hβ : ∀ t, Measurable[ℋ] fun ω => β ω t) (hα : ∀ t, Measurable[ℋ] fun ω => α ω t)
    {h : Ω → DistOn upperHalfPlaneOpens} (T : DistOn upperHalfPlaneOpens)
    (hS : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[ℋ] {ω | Disjoint (tsupport φ) (closure (C ω))}) :
    MeasurableSpace.comap (Lemma72B.pocketRecord β α C h) inferInstance ≤
      germSigma B (fun ω => h ω - T) ⊔ ℋ := by
  have hle : ℋ ≤ germSigma B (fun ω => h ω - T) ⊔ ℋ := le_sup_right
  have hβm : Measurable[ℋ] β := by
    let _ : MeasurableSpace Ω := ℋ
    exact measurable_pi_iff.2 hβ
  have hαm : Measurable[ℋ] α := by
    let _ : MeasurableSpace Ω := ℋ
    exact measurable_pi_iff.2 hα
  have hβm' := hβm.mono hle le_rfl
  have hαm' := hαm.mono hle le_rfl
  have hout := fun φ => measurable_outField_germSigma (ℋ := ℋ) (h := h) hCB T hS φ
  refine Measurable.comap_le ?_
  let _ : MeasurableSpace Ω := germSigma B (fun ω => h ω - T) ⊔ ℋ
  exact (hβm'.prodMk hαm').prodMk (measurable_pi_iff.2 hout)

end Germ

/-! ### (L) conditionally on the exterior record -/

section Cond

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The locality (L) of a mapped hull conditionally on the exterior record.** In the setting of
`isLocalSet_cond_chart_of_isHistoryAvoidanceLocal` (centred field a zero-boundary GFF, `ℋ`-measurable random chart with
harmonic lift, `ℋ`-measurable `K`, and `B = ℍ ∖ ψ⁻¹(ℍ ∖ K)` an `ℋ`-measurable history-marked local set of the centred
field for the marks `ℋ`), if the outer curves and the closure events of the pocket `C = dom c` are marks, then for every
event `G` of the exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})` of positive probability, `K` is a local set of
`h_ψ = chartTransport c 1 a k h` under `P[· | G]`. -/
theorem isLocalSet_cond_pocketRecord {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    {K : Ω → Set ℂ} (hKm : Measurable[ℋ, hittingSigma] K) (hK : ∀ ω, K ω ⊆ H ∧ IsOpen (H \ K ω))
    (hℋ : ℋ ≤ mΩ) (hBm : Measurable[ℋ, hittingSigma] fun ω => H \ (c ω).2.1 '' (H \ K ω))
    (hloc : IsHistoryAvoidanceLocal ℋ (fun ω => H \ (c ω).2.1 '' (H \ K ω)) (centredField h u₀) P)
    {β α : Ω → ℝ≥0 → ℂ} (hβ : ∀ t, Measurable[ℋ] fun ω => β ω t) (hα : ∀ t, Measurable[ℋ] fun ω => α ω t)
    (hS : ∀ φ : TestOn upperHalfPlaneOpens,
      MeasurableSet[ℋ] {ω | Disjoint (tsupport φ) (closure ((c ω).dom : Set ℂ))})
    {G : Set Ω}
    (hG : MeasurableSet[MeasurableSpace.comap
      (Lemma72B.pocketRecord β α (fun ω => ((c ω).dom : Set ℂ)) h) inferInstance] G)
    (hPG : P G ≠ 0) (a k : ℝ) :
    IsLocalSet K (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) (P[|G]) := by
  have hCB : ∀ ω, H \ ((c ω).dom : Set ℂ) ⊆ H \ (c ω).2.1 '' (H \ K ω) := fun ω =>
    sdiff_subset_sdiff_right (by rw [(hc ω).coe_dom]; exact image_mono sdiff_subset)
  have hle := comap_pocketRecord_le (ℋ := ℋ) hCB hβ hα (h := h)
    (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) hS
  exact isLocalSet_cond_chart_of_isHistoryAvoidanceLocal hhm hu₀ hh0 hc hdom hfwd hliftm hliftc hlift hKm hK hℋ
    hBm hloc (hle G hG) hPG a k

end Cond

end InteractingSLE.Sec7.Lemma72C
