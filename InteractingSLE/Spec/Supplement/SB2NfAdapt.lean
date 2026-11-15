/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfRead
import InteractingSLE.Spec.Supplement.SB2NfStop
import InteractingSLE.Spec.Supplement.SB2NdAdapt

/-!
# F2b′'s root: the strict time change, adapted frozen drivers, safe events

Packet PROVE-AUX61-NOJUMP (round 22, the root variant; D48, CONDFIN's `Cr.RootVersionG`).

* **`tcFiltS`**: the strict time change `D ∈ 𝓗 q ⇔ D measurable ∧ ∀ t, D ∩ {q < a t} ∈ 𝓖 t` (`Cr.RootVersionG`'s
  `timeChange`), `le_tcFiltS_zero`, `stronglyAdapted_tcFiltS_of_ae_read`;
* **`RootStop`**: the root objects, a record word measurable at B-time `0`, a countable set of types and a conull
  event on which the relative facts of the root's relative curve hold; `toG` (`StopG`, the stops);
* the frozen drivers are read on `At t = {0 < a t} ∩ Gr` (an event of the completed line filtration at `t`; the good
  event of the stops is not, since the root is not decided at B-time `0`): `exists_frozenLineReading`,
  **`stronglyAdapted_W`**, **`measurableSet_safe_stop`** (with `0 < a t`, as in `Cr.RootVersionG.safeS`);
* the record and the root event are events of `𝓗 0` (**`measurable_record_H0`**, **`measurableSet_root_H0`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Nd

/-! ### The strict time change -/

section Strict

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The σ-algebra of the strict time change at relative time `q`. -/
@[instance_reducible]
def tcSigmaS (𝓖 : Filtration ℝ≥0 mΩ) (a : ℝ≥0 → Ω → ℝ≥0∞) (ha : ∀ t, Measurable[𝓖 t] (a t)) (q : ℝ≥0) :
    MeasurableSpace Ω where
  MeasurableSet' D := MeasurableSet D ∧ ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) < a t ω})
  measurableSet_empty := ⟨MeasurableSet.empty, fun t => by
    rw [empty_inter]; exact @MeasurableSet.empty Ω (𝓖 t)⟩
  measurableSet_compl D hD := ⟨hD.1.compl, fun t => by
    have hA : MeasurableSet[𝓖 t] {ω | (q : ℝ≥0∞) < a t ω} := measurableSet_lt measurable_const (ha t)
    have e : Dᶜ ∩ {ω | (q : ℝ≥0∞) < a t ω} = {ω | (q : ℝ≥0∞) < a t ω} \ (D ∩ {ω | (q : ℝ≥0∞) < a t ω}) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]
    exact hA.diff (hD.2 t)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun t => by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion fun i => (hf i).2 t⟩

/-- **The strict time-changed filtration.** -/
def tcFiltS (𝓖 : Filtration ℝ≥0 mΩ) (a : ℝ≥0 → Ω → ℝ≥0∞) (ha : ∀ t, Measurable[𝓖 t] (a t)) :
    Filtration ℝ≥0 mΩ where
  seq := tcSigmaS 𝓖 a ha
  mono' q q' hqq' D hD := ⟨hD.1, fun t => by
    have hA : MeasurableSet[𝓖 t] {ω | (q' : ℝ≥0∞) < a t ω} := measurableSet_lt measurable_const (ha t)
    have e : D ∩ {ω | (q' : ℝ≥0∞) < a t ω} =
        (D ∩ {ω | (q : ℝ≥0∞) < a t ω}) ∩ {ω | (q' : ℝ≥0∞) < a t ω} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨⟨h.1, lt_of_le_of_lt (ENNReal.coe_le_coe.2 hqq') h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [e]
    exact (hD.2 t).inter hA⟩
  le' _ _ hD := hD.1

variable {𝓖 : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ≥0∞} {ha : ∀ t, Measurable[𝓖 t] (a t)}

theorem tcFiltS_inter (q : ℝ≥0) (D : Set Ω) (hD : MeasurableSet[tcFiltS 𝓖 a ha q] D) (t : ℝ≥0) :
    MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) < a t ω}) := hD.2 t

theorem measurableSet_tcFiltS_iff {q : ℝ≥0} {D : Set Ω} :
    MeasurableSet[tcFiltS 𝓖 a ha q] D ↔
      MeasurableSet D ∧ ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) < a t ω}) := Iff.rfl

/-- **Adaptedness to the strict time change through an almost-sure reading.** -/
theorem stronglyAdapted_tcFiltS_of_ae_read {P : Measure Ω}
    (hcl : ∀ t (s s' : Set Ω), MeasurableSet s → MeasurableSet[𝓖 t] s' → s =ᵐ[P] s' → MeasurableSet[𝓖 t] s)
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ q, Measurable (W q)) (Y : ℝ≥0 → ℝ≥0 → Ω → ℝ)
    (hY : ∀ q t, Measurable[𝓖 t] (Y q t))
    (hread : ∀ q t : ℝ≥0, ∀ᵐ ω ∂P, (q : ℝ≥0∞) < a t ω → W q ω = Y q t ω) :
    StronglyAdapted (tcFiltS 𝓖 a ha) W := by
  intro q
  refine Measurable.stronglyMeasurable fun B hB => ⟨hWm q hB, fun t => ?_⟩
  have hA : MeasurableSet[𝓖 t] {ω | (q : ℝ≥0∞) < a t ω} := measurableSet_lt measurable_const (ha t)
  have hAm : MeasurableSet {ω | (q : ℝ≥0∞) < a t ω} := 𝓖.le t _ hA
  refine hcl t _ (Y q t ⁻¹' B ∩ {ω | (q : ℝ≥0∞) < a t ω}) ((hWm q hB).inter hAm) ((hY q t hB).inter hA) ?_
  filter_upwards [hread q t] with ω hω
  apply propext
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  exact ⟨fun h => ⟨hω h.2 ▸ h.1, h.2⟩, fun h => ⟨(hω h.2).symm ▸ h.1, h.2⟩⟩

end Strict

/-- **A σ-algebra below every physical time is below the strict time change at `0`.** -/
theorem le_tcFiltS_zero {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 mΩ}
    {a : ℝ≥0 → Ω → ℝ≥0∞} {ha : ∀ t, Measurable[𝓖 t] (a t)} (h𝒢 : ∀ t, 𝒢 ≤ 𝓖 t) :
    𝒢 ≤ tcFiltS 𝓖 a ha 0 := fun D hD =>
  ⟨𝓖.le 0 _ (h𝒢 0 _ hD), fun t => (h𝒢 t _ hD).inter (measurableSet_lt measurable_const (ha t))⟩

/-! ### The root's stop inputs -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

variable (P) in
/-- **The root's stop inputs**: the root objects, a record word measurable at B-time `0`, a countable set of types,
and a conull event on which the relative facts of the root's relative curve hold. -/
structure RootStop (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) where
  hb : IsPiecewiseConstantBoundaryData b jumps
  S : RootObj P κ b jumps E u l k ℓ
  cw : Ω → BoundaryWord
  types : Set WordType
  htypes : types.Countable
  hcw : Measurable[lineC0 P κ b jumps E u l k ℓ] cw
  Gr : Set Ω
  hGr : MeasurableSet Gr
  hGrae : ∀ᵐ ω ∂P, ω ∈ Gr
  rel : ∀ ω ∈ S.Eg ∩ Gr, RelFactsAt κ (-(Real.pi / 2)) cw types (S.ρM ω) ω

namespace RootStop

variable (T : RootStop P κ b jumps E u l k ℓ)

/-- The stops of the root's relative curve. -/
def toG : StopG P κ (-(Real.pi / 2)) where
  ρ := T.S.ρM
  hd := T.S.driven_ρM
  hm := fun r hr => T.S.measurable_ρM T.hb r hr
  Eg := T.S.Eg
  hEg := T.S.measurableSet_Eg
  cw := T.cw
  types := T.types
  htypes := T.htypes
  hcw := T.hcw.mono inf_le_left le_rfl
  Gr := T.Gr
  hGr := T.hGr
  hGrae := T.hGrae
  rel := T.rel

/-- The reading event at time `t`. -/
def At (t : ℝ≥0) : Set Ω := {ω | 0 < T.S.a t ω} ∩ T.Gr

theorem At_subset_Gs (t : ℝ≥0) : T.At t ⊆ T.toG.Gs := fun _ hω => ⟨T.S.mem_Eg_of_pos hω.1, hω.2⟩

open Classical in
/-- The record read off the conull event. -/
def recG (ω : Ω) : RecData := if ω ∈ T.Gr then rec2 κ (-(Real.pi / 2)) T.cw T.types ω else recOne

theorem record_eq_recG {ω : Ω} {t : ℝ≥0} (hω : 0 < T.S.a t ω) : T.toG.record ω = T.recG ω := by
  have hE := T.S.mem_Eg_of_pos hω
  by_cases hG : ω ∈ T.Gr
  · rw [T.toG.record_of_mem ⟨hE, hG⟩]; simp only [recG, hG, ↓reduceIte]; rfl
  · rw [T.toG.record_of_notMem fun h' => hG h'.2]; simp only [recG, hG, ↓reduceIte]

variable (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
  (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
  (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
  (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
  (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
  {𝓖 : Filtration ℝ≥0 mΩ} (h𝓖 : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t)

include T hE hER hℓ hwℓ h𝓖 in
theorem lineC0_le_lineFilt (t : ℝ≥0) : lineC0 P κ b jumps E u l k ℓ ≤ lineFiltC P 𝓖 t := by
  show mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P ≤ mΩ ⊓ aeSigma (𝓖 t) P
  rw [h𝓖 t]
  exact inf_le_inf_left _ (WalkLaw.aeSigma_mono (lineSigma0_le_T (u := u) (l := l) (k := k) T.hb hE hER hℓ hwℓ t))

include hE hER hlθ hℓ hwℓ h𝓖 in
theorem measurable_a_lineFilt (t : ℝ≥0) : Measurable[lineFiltC P 𝓖 t] (T.S.a t) := by
  show Measurable[mΩ ⊓ aeSigma (𝓖 t) P] _
  rw [h𝓖 t]
  exact T.S.measurable_a_line T.hb hE hER hlθ hℓ hwℓ t

theorem measurableSet_Gr_line (t : ℝ≥0) : MeasurableSet[lineFiltC P 𝓖 t] T.Gr :=
  Vf.measurableSet_cmpl_of_conull T.hGr (ae_iff.1 T.hGrae)

include hE hER hlθ hℓ hwℓ h𝓖 in
theorem measurableSet_At (t : ℝ≥0) : MeasurableSet[lineFiltC P 𝓖 t] (T.At t) :=
  (measurableSet_lt measurable_const (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖 t)).inter
    (T.measurableSet_Gr_line t)

include hE hER hℓ hwℓ h𝓖 in
theorem measurable_recG_line (t : ℝ≥0) : Measurable[lineFiltC P 𝓖 t] T.recG := by
  classical
  unfold recG
  exact Measurable.ite (T.measurableSet_Gr_line t)
    ((measurable_rec2 κ (-(Real.pi / 2)) T.cw T.types T.hcw T.htypes).mono
      (T.lineC0_le_lineFilt hE hER hℓ hwℓ h𝓖 t) le_rfl)
    (@measurable_const _ _ _ (lineFiltC P 𝓖 t) recOne)

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The canonical driver below the clock is read from the completed line filtration on the reading event.** -/
theorem measurable_Wr_line (t r : ℝ≥0) :
    Measurable[lineFiltC P 𝓖 t] ((T.At t ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}).indicator (T.toG.Wr r)) := by
  have e : (T.At t ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}).indicator (T.toG.Wr r) =
      T.Gr.indicator ((T.S.Eg ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}).indicator fun ω => segDrv (T.S.ρM ω) r) := by
    funext ω
    by_cases hω : ω ∈ T.At t ∩ {ω | (r : ℝ≥0∞) < T.S.a t ω}
    · have hEg : ω ∈ T.S.Eg := T.S.mem_Eg_of_pos hω.1.1
      rw [indicator_of_mem hω, indicator_of_mem hω.1.2, indicator_of_mem (show ω ∈ T.S.Eg ∩
        {ω | (r : ℝ≥0∞) < T.S.a t ω} from ⟨hEg, hω.2⟩)]
      unfold StopG.Wr
      show CoordB.drivenDriver T.S.ρM r ω = _
      rw [CoordB.drivenDriver_eq (lt_of_lt_of_le hω.2 (T.S.a_le_capLife hEg t))]
      rfl
    · rw [indicator_of_notMem hω]
      by_cases hG : ω ∈ T.Gr
      · rw [indicator_of_mem hG, indicator_of_notMem fun h' => hω
          ⟨⟨lt_of_le_of_lt zero_le (show (r : ℝ≥0∞) < T.S.a t ω from h'.2), hG⟩, h'.2⟩]
      · rw [indicator_of_notMem hG]
  rw [e]
  have h1 := T.S.measurable_segDrv_line T.hb hE hER hlθ hℓ hwℓ t r
  have h2 : MeasurableSet[mΩ ⊓ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P] T.Gr :=
    Vf.measurableSet_cmpl_of_conull T.hGr (ae_iff.1 T.hGrae)
  show Measurable[mΩ ⊓ aeSigma (𝓖 t) P] _
  rw [h𝓖 t]
  exact h1.indicator h2

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The frozen drivers read below the clock** on the reading events. -/
theorem exists_frozenLineReading (m : ℕ) :
    ∃ Y : ℝ≥0 → ℝ≥0 → Ω → ℝ, (∀ q t : ℝ≥0, Measurable[lineFiltC P 𝓖 t] (Y q t)) ∧
      (∀ (q t : ℝ≥0) (ω : Ω), ω ∉ T.At t → Y q t ω = 0) ∧
      ∀ (q t : ℝ≥0) (ω : Ω), ω ∈ T.At t → (q : ℝ≥0∞) ≤ T.S.a t ω → Y q t ω = T.toG.W m q ω := by
  have hex : ∀ q t : ℝ≥0, ∃ Y : Ω → ℝ, Measurable[lineFiltC P 𝓖 t] Y ∧ (∀ ω, ω ∉ T.At t → Y ω = 0) ∧
      ∀ ω ∈ T.At t, (q : ℝ≥0∞) ≤ T.S.a t ω →
        Y ω = T.toG.Wr (min q (stopRule m (T.recG ω, fun u => T.toG.Wr u ω)).toNNReal) ω := fun q t =>
    exists_frozen_reading (T.measurableSet_At hE hER hlθ hℓ hwℓ h𝓖 t)
      (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖 t) (T.measurable_Wr_line hE hER hlθ hℓ hwℓ h𝓖 t)
      (T.measurable_recG_line hE hER hℓ hwℓ h𝓖 t)
      (measurable_stopRule m) (isPathRule_stopRule m) (U := fun ω => capLife (T.S.ρM ω))
      (fun ω _ => T.toG.continuousOn_Wr ω)
      (fun ω hω => by
        rw [← T.record_eq_recG hω.1]
        exact T.toG.Vstop_lt (T.At_subset_Gs t hω))
      (fun ω _ => T.toG.Wr_zero ω) q
  choose Y hYm hYoff hYon using hex
  refine ⟨Y, hYm, hYoff, fun q t ω hω hq => ?_⟩
  rw [hYon q t ω hω hq, T.toG.W_of_mem (T.At_subset_Gs t hω), ← T.record_eq_recG hω.1]
  rfl

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **Each frozen driver is adapted to the strict time change of the completed line filtration.** -/
theorem stronglyAdapted_W (m : ℕ) :
    StronglyAdapted (tcFiltS (lineFiltC P 𝓖) T.S.a (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖)) (T.toG.W m) := by
  obtain ⟨Y, hYm, -, hYon⟩ := T.exists_frozenLineReading hE hER hlθ hℓ hwℓ h𝓖 m
  refine stronglyAdapted_tcFiltS_of_ae_read (P := P) (fun t s s' hs hs' he => Vf.cmpl_closed hs hs' he)
    (T.toG.measurable_W m) Y hYm fun q t => ?_
  filter_upwards [T.hGrae] with ω hG hq
  exact (hYon q t ω ⟨lt_of_le_of_lt zero_le hq, hG⟩ hq.le).symm

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The safe event of a frozen driver for a closed set, where the clock is positive, is an event of the completed
line filtration.** -/
theorem measurableSet_safe_stop (m : ℕ) {K : Set ℂ} (hK : IsClosed K) (t : ℝ≥0) :
    MeasurableSet[lineFiltC P 𝓖 t] {ω | 0 < T.S.a t ω ∧ T.S.a t ω < T.toG.V m ω ∧
      Disjoint K (fwdHull (fun s : ℝ => T.toG.W m s.toNNReal ω) (T.S.a t ω).toNNReal)} := by
  classical
  obtain ⟨Y, hYm, hYoff, hYon⟩ := T.exists_frozenLineReading hE hER hlθ hℓ hwℓ h𝓖 m
  have ha := T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖 t
  have hAt := T.measurableSet_At hE hER hlθ hℓ hwℓ h𝓖 t
  have hGr := T.measurableSet_Gr_line (𝓖 := 𝓖) t
  set τ : Ω → ℝ≥0 := fun ω => (T.S.a t ω).toNNReal with hτdef
  have hτm : Measurable[lineFiltC P 𝓖 t] τ := ENNReal.measurable_toNNReal.comp ha
  set B : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ T.At t then T.toG.W m (min s (τ ω)) ω else 0 with hBdef
  have hBm : ∀ s, Measurable[lineFiltC P 𝓖 t] (B s) := fun s =>
    Vm.measurable_stopped (T.toG.continuous_W m) hτm (Y := fun v => Y v t) (fun v => hYm v t)
      (fun v ω hω hv => hYon v t ω hω (by
        by_cases htop : T.S.a t ω = ⊤
        · rw [htop]; exact le_top
        · rw [← ENNReal.coe_toNNReal htop]; exact ENNReal.coe_le_coe.2 hv))
      (fun v ω hω => hYoff v t ω hω) s
  have hBc : ∀ ω, Continuous fun s => B s ω := fun ω => by
    by_cases hω : ω ∈ T.At t
    · simp only [hBdef, hω, ↓reduceIte]
      exact (T.toG.continuous_W m ω).comp (continuous_id.min continuous_const)
    · simp only [hBdef, hω, ↓reduceIte]; exact continuous_const
  have hBpath : Measurable[lineFiltC P 𝓖 t] fun ω => fun s => B s ω :=
    @Measurable.of_eval Ω ℝ≥0 (fun _ => ℝ) (lineFiltC P 𝓖 t) _ _ hBm
  have hrec := T.measurable_recG_line hE hER hℓ hwℓ h𝓖 t
  set S₁ : Set Ω := T.At t ∩ {ω | T.S.a t ω ≠ ⊤} ∩
    {ω | ¬ stopRule m (T.recG ω, fun s => B s ω) ≤ T.S.a t ω} ∩
    {ω | Disjoint K (fwdHull (QuantumZipper.drive 1 B ω) (τ ω))} with hS₁
  set S₂ : Set Ω := (T.Grᶜ ∩ {ω | 0 < T.S.a t ω}) ∩ {ω | T.S.a t ω < (((m : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) ∧
    Disjoint K (fwdHull (QuantumZipper.drive 1 (fun _ _ => (0 : ℝ)) ω) (τ ω))} with hS₂
  have hS₁m : MeasurableSet[lineFiltC P 𝓖 t] S₁ :=
    ((hAt.inter (measurableSet_eq_fun ha measurable_const).compl).inter
      (measurableSet_le ((measurable_stopRule m).comp (hrec.prodMk hBpath)) ha).compl).inter
      (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hBc hBm (measurable_coe_nnreal_real.comp hτm)
        (fun ω => (τ ω).2) hK)
  have hS₂m : MeasurableSet[lineFiltC P 𝓖 t] S₂ :=
    (hGr.compl.inter (measurableSet_lt measurable_const ha)).inter ((measurableSet_lt ha measurable_const).inter
      (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand (B := fun _ _ => (0 : ℝ)) (fun _ => continuous_const)
        (fun _ => measurable_const) (measurable_coe_nnreal_real.comp hτm) (fun ω => (τ ω).2) hK))
  have e : {ω | 0 < T.S.a t ω ∧ T.S.a t ω < T.toG.V m ω ∧
      Disjoint K (fwdHull (fun s : ℝ => T.toG.W m s.toNNReal ω) (T.S.a t ω).toNNReal)} = S₁ ∪ S₂ := by
    ext ω
    show (0 < T.S.a t ω ∧ T.S.a t ω < T.toG.V m ω ∧ _) ↔ (ω ∈ S₁ ∨ ω ∈ S₂)
    by_cases hpos : 0 < T.S.a t ω
    · by_cases hG : ω ∈ T.Gr
      · have hω : ω ∈ T.At t := ⟨hpos, hG⟩
        have hGs := T.At_subset_Gs t hω
        have hnS₂ : ω ∉ S₂ := fun h' => h'.1.1 hG
        simp only [hnS₂, or_false, hS₁, mem_inter_iff, mem_ofPred_eq, hω, true_and, hpos]
        have hBW : ∀ s ≤ τ ω, B s ω = T.toG.W m s ω := fun s hs => by
          simp only [hBdef, hω, ↓reduceIte, min_eq_left hs]
        have hhull : fwdHull (fun s : ℝ => T.toG.W m s.toNNReal ω) (τ ω : ℝ) =
            fwdHull (QuantumZipper.drive 1 B ω) (τ ω : ℝ) := by
          rw [Vm.drive_one]
          refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ((T.toG.continuous_W m ω).comp continuous_real_toNNReal)
            ((hBc ω).comp continuous_real_toNNReal) (τ ω).2 fun r hr => (hBW _ ?_).symm
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
          exact hr.2
        have hVrec : T.toG.V m ω = stopRule m (T.recG ω, fun s => T.toG.W m s ω) := by
          show stopRule m (T.toG.record ω, fun s => T.toG.W m s ω) = _
          rw [T.record_eq_recG hpos]
        constructor
        · rintro ⟨hlt, hdisj⟩
          have htop : T.S.a t ω ≠ ⊤ := ne_top_of_lt hlt
          have hτa : (τ ω : ℝ≥0∞) = T.S.a t ω := ENNReal.coe_toNNReal htop
          refine ⟨⟨htop, ?_⟩, by rw [← hhull]; exact hdisj⟩
          rw [← hτa]
          intro hle
          have := (GW2Bh.pathRule_le_iff (isPathRule_stopRule m) (r := T.recG ω) hBW).1 hle
          rw [hτa, ← hVrec] at this
          exact absurd hlt (not_lt.2 this)
        · rintro ⟨⟨htop, hnle⟩, hdisj⟩
          have hτa : (τ ω : ℝ≥0∞) = T.S.a t ω := ENNReal.coe_toNNReal htop
          refine ⟨?_, by rw [hhull]; exact hdisj⟩
          by_contra hle
          rw [not_lt, ← hτa, hVrec] at hle
          have h2 := (GW2Bh.pathRule_le_iff (isPathRule_stopRule m) (r := T.recG ω) hBW).2 hle
          exact hnle (by rw [← hτa]; exact h2)
      · have hGs : ω ∉ T.toG.Gs := fun h' => hG h'.2
        have hnS₁ : ω ∉ S₁ := fun h' => hG h'.1.1.1.2
        simp only [hnS₁, false_or, hS₂, mem_inter_iff, mem_compl_iff, hG, not_false_eq_true, true_and,
          mem_ofPred_eq, T.toG.V_of_notMem hGs, hpos]
        have hh : fwdHull (fun s : ℝ => T.toG.W m s.toNNReal ω) (T.S.a t ω).toNNReal =
            fwdHull (QuantumZipper.drive 1 (fun _ _ => (0 : ℝ)) ω) (τ ω) := by
          rw [Vm.drive_one]; simp only [T.toG.W_of_notMem hGs]; rfl
        rw [hh]
    · have hnS₁ : ω ∉ S₁ := fun h' => hpos h'.1.1.1.1
      have hnS₂ : ω ∉ S₂ := fun h' => hpos h'.1.2
      simp only [hpos, false_and, hnS₁, hnS₂, or_self]
  rw [e]
  exact hS₁m.union hS₂m

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The record is an event of `𝓗 0`.** -/
theorem measurable_record_H0 :
    Measurable[tcFiltS (lineFiltC P 𝓖) T.S.a (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖) 0] T.toG.record := by
  intro B hB
  refine ⟨T.toG.measurable_record hB, fun t => ?_⟩
  have e : T.toG.record ⁻¹' B ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T.S.a t ω} =
      T.recG ⁻¹' B ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T.S.a t ω} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [ENNReal.coe_zero] at h2
      exact ⟨by rw [← T.record_eq_recG h2]; exact h1, by rw [ENNReal.coe_zero]; exact h2⟩
    · rintro ⟨h1, h2⟩
      rw [ENNReal.coe_zero] at h2
      exact ⟨by rw [T.record_eq_recG h2]; exact h1, by rw [ENNReal.coe_zero]; exact h2⟩
  rw [e]
  exact (T.measurable_recG_line hE hER hℓ hwℓ h𝓖 t hB).inter
    (measurableSet_lt measurable_const (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖 t))

include hE hER hlθ hℓ hwℓ h𝓖 in
/-- **The root's good event is an event of `𝓗 0`.** -/
theorem measurableSet_root_H0 :
    MeasurableSet[tcFiltS (lineFiltC P 𝓖) T.S.a (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖) 0] T.S.Eg := by
  refine ⟨T.S.measurableSet_Eg, fun t => ?_⟩
  have e : T.S.Eg ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T.S.a t ω} = {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T.S.a t ω} :=
    inter_eq_right.2 fun ω hω => T.S.mem_Eg_of_pos (by rw [ENNReal.coe_zero] at hω; exact hω)
  rw [e]
  exact measurableSet_lt measurable_const (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖 t)

end RootStop

end InteractingSLE.Theorem14.SB.Nf
