/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdAStopAnnounce
import InteractingSLE.Spec.Supplement.OrdAStopTransfer
import InteractingSLE.Spec.Restart.RetLeafModel
import InteractingSLE.Spec.Restart.RetPlumbProofDriverAnnounce

/-!
# The A-stop is announced in the driving filtration enlarged by the code of `I_A`

Packet PROVE-T15-ASTOP. On a probability space carrying a killed driving process `(W, VL, VR)` with lifetime `V`, a
real code `e` and a closed set `J (e ω) ⊂ ℂ` decoded from it (in the application: the chart image `I_A` of the retained
union, read through a code of its end points), let `γ` be a globally continuous trace. If almost surely

* `γ` generates `W` through `V`, `V > 0`, `V ≤ ζ₂`,
* `γ t ∉ J (e ω)` at positive times `t < V` (no earlier new contact with `A`),
* at a finite `V`: either `V = ζ₂` (the continuation's threshold, its original terminal rule) or `γ V ∈ J (e ω)`
  (a new contact with `A`),

and `ζ₂` has an announcing sequence in the enlarged driving filtration, then **`V` has an announcing sequence in the
killed driving filtration enlarged at time `0` by `e`** (`exists_isAnnouncingSeq_aStop`). The blowup process is
`1 / dist(γ t, J (e ω))`, read through the tip of the frozen driver (`Restart.RetLeaf.frozenDrv`), so it is observable;
it is infinite at time `0` (the trace starts in `J`), which `exists_isAnnouncingSeq_of_blowup_or` allows. With
`isCondStopSeq_of_sup` these stops feed the stopped K2 (`StoppedTypeDataJ.driveStopping`);
`exists_stoppedK2_sequences_sup` turns such an announcing sequence into the two sequences of `StoppedTypeDataJ`
(`announce`, `driveStops`), as PROVE-RETPLUMB's `RetAux79.exists_stoppedK2_sequences` does for the plain filtration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdAStop

open Restart Restart.RetLeaf Sec7.Coding

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- On a good sample, `1 / dist(γ t, J)` tends to `+∞` as `t` increases to a finite lifetime at which `γ` meets the
closed set `J`, after avoiding it at positive times. -/
theorem blowup_infDist {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {J : Set ℂ} (hJ : IsClosed J) {L : ℝ≥0} (hL0 : 0 < L)
    (hoff : ∀ t : ℝ≥0, 0 < t → t < L → γ t ∉ J) (hend : γ L ∈ J) (M : ℝ) :
    ∃ s₀ : ℝ≥0, s₀ < L ∧ ∀ t : ℝ≥0, s₀ ≤ t → t < L → M < 1 / infDist (γ t) J := by
  have hne : J.Nonempty := ⟨_, hend⟩
  set ε : ℝ := 1 / (|M| + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hcont : Tendsto (fun t => infDist (γ t) J) (𝓝 L) (𝓝 0) := by
    have h := ((continuous_infDist_pt J).comp hγ).tendsto L
    rwa [Function.comp_apply, infDist_zero_of_mem hend] at h
  have hev : {t : ℝ≥0 | infDist (γ t) J < ε} ∈ 𝓝 L := by
    have h := (Metric.tendsto_nhds.1 hcont) ε hε0
    filter_upwards [h] with t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg] at ht
    exact ht
  obtain ⟨l, hlL, hsub⟩ := exists_Ioc_subset_of_mem_nhds hev ⟨0, hL0⟩
  obtain ⟨s₀, hs₀1, hs₀2⟩ := exists_between (max_lt hlL (half_lt_self hL0))
  refine ⟨s₀, hs₀2, fun t ht htL => ?_⟩
  have hlt : l < t := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hs₀1) ht
  have ht0 : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt zero_le (lt_of_le_of_lt (le_max_right _ _) hs₀1)) ht
  have hpos : 0 < infDist (γ t) J := (hJ.notMem_iff_infDist_pos hne).1 (hoff t ht0 htL)
  have habs : infDist (γ t) J < ε := hsub ⟨hlt, htL.le⟩
  have h1 : 1 / ε < 1 / infDist (γ t) J := one_div_lt_one_div_of_lt hpos habs
  rw [hε, one_div_one_div] at h1
  linarith [le_abs_self M]

/-- `1 / dist(·, J)` is continuous at the points off a closed set `J`. -/
theorem continuousOn_one_div_infDist {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {J : Set ℂ} (hJ : IsClosed J)
    {S : Set ℝ≥0} (hS : ∀ t ∈ S, γ t ∉ J) : ContinuousOn (fun t => 1 / infDist (γ t) J) S := by
  rcases J.eq_empty_or_nonempty with he | hne
  · have e : (fun t => 1 / infDist (γ t) J) = fun _ => 0 := funext fun t => by
      rw [he, infDist_empty, div_zero]
    rw [e]
    exact continuousOn_const
  · exact continuousOn_const.div ((continuous_infDist_pt J).comp hγ).continuousOn
      fun t ht => ((hJ.notMem_iff_infDist_pos hne).1 (hS t ht)).ne'

/-- **The A-stop is announced in the killed driving filtration enlarged by the code of `J`.** -/
theorem exists_isAnnouncingSeq_aStop {Q : Measure Ω} [IsProbabilityMeasure Q] {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hXP : IsMeasurableKilledDriving W VL VR V) {e : Ω → ℝ} (hem : Measurable e)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    {J : ℝ → Set ℂ} (hJc : ∀ c, IsClosed (J c)) (hJ : Measurable fun p : ℂ × ℝ => infDist p.1 (J p.2))
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω))
    {ζ₂ : Ω → ℝ≥0∞} {b : ℕ → Ω → ℝ≥0} (hb : Coupling.IsAnnouncingSeq (drivingSupCode Q hXP hem) Q ζ₂ b)
    (hgood : ∀ᵐ ω ∂Q, IsGeneratingTrace (W · ω) (V ω) (γ ω) ∧ 0 < V ω ∧ V ω ≤ ζ₂ ω ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ ω t ∉ J (e ω)) ∧
      (V ω ≠ ⊤ → V ω = ζ₂ ω ∨ γ ω (V ω).toNNReal ∈ J (e ω))) :
    ∃ T : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq (drivingSupCode Q hXP hem) Q V T := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hG : ∀ ω, ω ∉ N → IsGeneratingTrace (W · ω) (V ω) (γ ω) ∧ 0 < V ω ∧ V ω ≤ ζ₂ ω ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ ω t ∉ J (e ω)) ∧
      (V ω ≠ ⊤ → V ω = ζ₂ ω ∨ γ ω (V ω).toNNReal ∈ J (e ω)) := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  set X : ℝ≥0 → Ω → ℝ := fun t => Nᶜ.indicator fun ω => 1 / infDist (γ ω t) (J (e ω)) with hX
  set 𝓖 := drivingSupCode Q hXP hem with h𝓖
  have hsup : ∀ (t : ℝ≥0) {S : Set Ω},
      MeasurableSet[killedDrivingSigma W VL VR V t ⊔ MeasurableSpace.comap e inferInstance] S →
        MeasurableSet[𝓖 t] S :=
    fun t S hS => Ito.le_usualAugmentation _ Q t _ hS
  have hN𝓖 : ∀ (t : ℝ≥0) {S : Set Ω}, MeasurableSet S → S ⊆ N → MeasurableSet[𝓖 t] S :=
    fun t S hS hSN => Ito.measurableSet_usualAugmentation_of_null hS (measure_mono_null hSN hN0) t
  have hlive : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < V ω} := fun t =>
    hsup t (le_sup_left (a := killedDrivingSigma W VL VR V t) _ (measurableSet_live_killedDrivingSigma t))
  have hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | V ω ≤ t} := fun t => by
    have e' : {ω | V ω ≤ t} = {ω | (t : ℝ≥0∞) < V ω}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    rw [e']
    exact (hlive t).compl
  have hVm : Measurable V := by
    refine measurable_of_Iic fun t => ?_
    induction t using ENNReal.recTopCoe with
    | top => simp only [Iic_top, preimage_univ, MeasurableSet.univ]
    | coe t => exact 𝓖.le t _ (hζ t)
  have hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < V ω ∧ c < X t ω} := by
    intro t c
    obtain ⟨g, hgdef⟩ : ∃ g : Ω → ℝ, g = (fun p : ℂ × ℝ => infDist p.1 (J p.2)) ∘
        fun ω => (LP.traceAt t (frozenDrv W V t ω), e ω) := ⟨_, rfl⟩
    have hg_apply : ∀ ω, g ω = infDist (LP.traceAt t (frozenDrv W V t ω)) (J (e ω)) := fun ω => by
      rw [hgdef, Function.comp_apply]
    have hfm : MeasurableSet[𝓖 t] {ω | c < 1 / g ω} := by
      have h1 : Measurable[killedDrivingSigma W VL VR V t ⊔ MeasurableSpace.comap e inferInstance]
          fun ω => LP.traceAt t (frozenDrv W V t ω) :=
        (measurable_traceAt_frozenDrv (W := W) (VL := VL) (VR := VR) (ζ := V) t).mono le_sup_left le_rfl
      have h2 : Measurable[killedDrivingSigma W VL VR V t ⊔ MeasurableSpace.comap e inferInstance] e :=
        (comap_measurable e).mono le_sup_right le_rfl
      have hg : Measurable[killedDrivingSigma W VL VR V t ⊔ MeasurableSpace.comap e inferInstance] g := by
        rw [hgdef]
        exact hJ.comp (h1.prodMk h2)
      exact hsup t ((hg.const_div 1) measurableSet_Ioi)
    have hlm : MeasurableSet {ω | (t : ℝ≥0∞) < V ω} := measurableSet_lt measurable_const hVm
    have heq : ∀ ω, ω ∉ N → (t : ℝ≥0∞) < V ω → LP.traceAt t (frozenDrv W V t ω) = γ ω t := fun ω hω ht => by
      rw [traceAt_frozenDrv ht]
      exact LP.traceAt_eq_of_isGeneratingTrace (hG ω hω).1 (hWc ω).continuousOn (hW0 ω) ht
    have e' : {ω | (t : ℝ≥0∞) < V ω ∧ c < X t ω} =
        (({ω | (t : ℝ≥0∞) < V ω} ∩ Nᶜ) ∩ {ω | c < 1 / g ω}) ∪
          (({ω | (t : ℝ≥0∞) < V ω} ∩ N) ∩ {_ω | c < 0}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, hX]
      by_cases hωN : ω ∈ N
      · rw [indicator_of_notMem (show ω ∉ Nᶜ from fun h => h hωN)]
        exact ⟨fun h => Or.inr ⟨⟨h.1, hωN⟩, h.2⟩, fun h => h.elim (fun h => absurd hωN h.1.2)
          fun h => ⟨h.1.1, h.2⟩⟩
      · rw [indicator_of_mem (show ω ∈ Nᶜ from hωN)]
        constructor
        · rintro ⟨ht, hc⟩
          refine Or.inl ⟨⟨ht, hωN⟩, ?_⟩
          rw [hg_apply ω, heq ω hωN ht]
          exact hc
        · rintro (⟨⟨ht, -⟩, hc⟩ | ⟨⟨-, h⟩, -⟩)
          · refine ⟨ht, ?_⟩
            rwa [hg_apply ω, heq ω hωN ht] at hc
          · exact absurd h hωN
    rw [e']
    exact ((hlive t).inter (hN𝓖 t hNm subset_rfl).compl).inter hfm |>.union
      (hN𝓖 t ((hlm.inter hNm).inter (MeasurableSet.const _)) fun ω hω => hω.1.2)
  have hXc : ∀ ω, ContinuousOn (X · ω) {t | 0 < t ∧ (t : ℝ≥0∞) < V ω} := by
    intro ω
    by_cases hωN : ω ∈ N
    · have e' : (X · ω) = fun _ => 0 := funext fun t => by
        simp only [hX]
        exact indicator_of_notMem (show ω ∉ Nᶜ from fun h => h hωN) _
      rw [e']
      exact continuousOn_const
    · have e' : (X · ω) = fun t => 1 / infDist (γ ω t) (J (e ω)) := funext fun t => by
        simp only [hX]
        exact indicator_of_mem (show ω ∈ Nᶜ from hωN) _
      rw [e']
      exact continuousOn_one_div_infDist (hγc ω) (hJc _) fun t ht => (hG ω hωN).2.2.2.1 t ht.1 ht.2
  have hblow : ∀ᵐ ω ∂Q, V ω ≠ ⊤ → V ω = ζ₂ ω ∨ ∀ M : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < V ω ∧
      ∀ t : ℝ≥0, s ≤ t → (t : ℝ≥0∞) < V ω → M < X t ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hωN htop
    obtain ⟨-, hV0, -, hoff, hend⟩ := hG ω hωN
    rcases hend htop with h | h
    · exact Or.inl h
    · refine Or.inr fun M => ?_
      set L : ℝ≥0 := (V ω).toNNReal with hL
      have hLe : V ω = (L : ℝ≥0∞) := (ENNReal.coe_toNNReal htop).symm
      have hL0 : 0 < L := by
        rw [hLe] at hV0
        exact_mod_cast hV0
      obtain ⟨s₀, hs₀, hM⟩ := blowup_infDist (hγc ω) (hJc (e ω)) hL0
        (fun t ht0 htL => hoff t ht0 (by rw [hLe]; exact_mod_cast htL)) h M
      refine ⟨s₀, by rw [hLe]; exact_mod_cast hs₀, fun t ht htV => ?_⟩
      have htL : t < L := by
        rw [hLe] at htV
        exact_mod_cast htV
      simp only [hX]
      rw [indicator_of_mem (show ω ∈ Nᶜ from hωN)]
      exact hM t ht htL
  exact exists_isAnnouncingSeq_of_blowup_or (𝓖 := 𝓖) hζ hXa hXc (hgood.mono fun ω h => h.2.1) hb
    (hgood.mono fun ω h => h.2.2.1) hblow

/-! ### The two K2 sequences from one announcement in the enlarged driving filtration -/

section Seq

open Restart.RetAux79 Sec7.PocketTraversal Restart.DomainMarkov Restart.FCDet

/-- The killed driving filtration of the geometric coordinates, enlarged by an `𝓗 0`-measurable code, is contained
in the usual augmentation of `𝓗`. -/
theorem drivingSupCode_geom_le_usual {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {V : Ω → ℝ≥0∞}
    (hWa : StronglyAdapted 𝓗 W) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hxL : Measurable[𝓗 0] xL) (hxR : Measurable[𝓗 0] xR)
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) {e : Ω → ℝ} (he : Measurable[𝓗 0] e) :
    drivingSupCode P (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs) (he.mono (𝓗.le 0) le_rfl) ≤
      usualAugmentation 𝓗 P := by
  have hk := Ito.killedDrivingFiltration_le (MartChar.adaptedBefore_of_stronglyAdapted hVs hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hVs (stronglyAdapted_geomLW hWa hWc hxL i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hVs (stronglyAdapted_geomRW hWa hWc hxR j))
    (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs)
  exact Ito.usualAugmentation_mono (fun t => sup_le (hk t) (he.comap_le.trans (𝓗.mono zero_le))) P

/-- **One announcement of the lifetime in the enlarged driving filtration supplies the augmented announcement and
the monotone enlarged driving stops**, with strict inequality and convergence (`RetAux79.exists_stoppedK2_sequences`
for `drivingSupCode`). -/
theorem exists_stoppedK2_sequences_sup {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {V : Ω → ℝ≥0∞}
    (hWa : StronglyAdapted 𝓗 W) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hxL : Measurable[𝓗 0] xL) (hxR : Measurable[𝓗 0] xR)
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) {e : Ω → ℝ} (he : Measurable[𝓗 0] e)
    (hp : ∃ T : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq
      (drivingSupCode P (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs) (he.mono (𝓗.le 0) le_rfl)) P V T) :
    ∃ T : ℕ → Ω → ℝ≥0,
      Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P V T ∧
      (∀ n, IsStoppingTime
        (drivingSupCode P (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs) (he.mono (𝓗.le 0) le_rfl))
        (fun ω => (T n ω : WithTop ℝ≥0))) ∧
      (∀ ω, Monotone fun n => (T n ω : WithTop ℝ≥0)) ∧
      (∀ᵐ ω ∂P, ∀ n, (T n ω : ℝ≥0∞) < V ω) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => (T n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
  obtain ⟨T, hT⟩ := hp
  refine ⟨T, isAnnouncingSeq_of_absolutelyContinuous hT
    (drivingSupCode_geom_le_usual hWa hWc hxL hxR hVs he) Measure.AbsolutelyContinuous.rfl,
    hT.1, ?_, ae_all_iff.2 hT.2.2.1, ae_tendsto_of_isAnnouncingSeq hT⟩
  intro ω n k hnk
  exact WithTop.coe_le_coe.2 (hT.2.1 ω hnk)

end Seq

end InteractingSLE.RLC.OrdAStop
