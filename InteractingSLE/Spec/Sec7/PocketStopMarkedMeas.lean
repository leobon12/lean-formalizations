/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedPath
import InteractingSLE.Spec.Sec7.PocketStopWallsFinStop
import InteractingSLE.Spec.Sec7.PocketTraversalMeasRand
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# The pocket's stop `T⁰(q)`: measurability at fixed times and at stopping times

Packet PROVE-STRIPSYS43 (PROVE-STRIPSYS41 §5.1). The measurable half of the Galmarino property of `T⁰(q)`:

* **Traces of joins at stopping times** (`measurableSet_le_inter_sup`, `measurableSet_lt_inter_sup`): an event of
  `σ(X) ∨ 𝓕_s`, restricted to `{s ≤ σ}` (or `{s < σ}`), is an event of `σ(X) ∨ 𝓕_σ` for every stopping time `σ`;
  `traceSigma`: the σ-algebra of the events whose restriction to a fixed event is measurable.
* **The adapted trace** `adTrace W ζ ω u = LP.traceAt u (killed driver)` (PROVE-LP's measurable radial-limit trace,
  which reads the driver only on `[0, u]`): `𝓕_s`-measurable for `u ≤ s` (`measurable_adTrace`), equal to the
  counterflow's Loewner trace wherever the driver is continuous with infinite lifetime (`adTrace_eq`).
* **The pocket's events on a configuration event `A`**, for any ambient σ-algebra `𝓜 ⊇ 𝓦` in which a path is
  measurable up to time `u`: visiting a wall point during `[0, u]` (`measurableSet_mem_arc_image`), a pocket visit at
  time `u` (`measurableSet_visit`), its Jordan coordinate (`measurable_visPt`), and the hitting capacity of the
  rational pocket visits up to `u` (`measurable_ratCap`).

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked

open QuantumZipper (H)

/-! ### Traces of joins at stopping times -/

section Trace

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The trace σ-algebra**: the events whose intersection with `D` is in `𝒮`. -/
@[instance_reducible] def traceSigma (𝒮 : MeasurableSpace Ω) (D : Set Ω) (hD : MeasurableSet[𝒮] D) :
    MeasurableSpace Ω where
  MeasurableSet' Q := MeasurableSet[𝒮] (D ∩ Q)
  measurableSet_empty := by
    simp only [inter_empty]
    exact @MeasurableSet.empty _ 𝒮
  measurableSet_compl Q hQ := by
    have e : D ∩ Qᶜ = D \ (D ∩ Q) := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [e]
    exact hD.diff hQ
  measurableSet_iUnion f hf := by
    rw [inter_iUnion]
    exact MeasurableSet.iUnion hf

theorem measurableSet_traceSigma_iff {𝒮 : MeasurableSpace Ω} {D : Set Ω} (hD : MeasurableSet[𝒮] D) {Q : Set Ω} :
    MeasurableSet[traceSigma 𝒮 D hD] Q ↔ MeasurableSet[𝒮] (D ∩ Q) := Iff.rfl

variable {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳}

/-- **An event of `σ(X) ∨ 𝓕_s` on `{s ≤ σ}` is an event of `σ(X) ∨ 𝓕_σ`.** -/
theorem measurableSet_le_inter_sup {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0))
    (s : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 s] E) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace] ({ω | s ≤ σ ω} ∩ E) := by
  set 𝒮 : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace with h𝒮
  have hσ𝒮 : hσ.measurableSpace ≤ 𝒮 := le_sup_right
  have hD : MeasurableSet[hσ.measurableSpace] {ω | s ≤ σ ω} := by
    have h := hσ.measurableSet_ge' s
    simpa only [WithTop.coe_le_coe] using h
  refine PocketStopWalls.measurableSet_inter_of_sup (𝒜 := 𝓕 s) (hσ𝒮 _ hD)
    (fun B hB => (hσ𝒮 _ hD).inter
      (le_sup_left (a := MeasurableSpace.comap X inferInstance) _ ⟨B, hB, rfl⟩)) (fun F hF => ?_) hE
  have hc := isStoppingTime_const 𝓕 s
  have hF' : MeasurableSet[hc.measurableSpace] F := by rwa [IsStoppingTime.measurableSpace_const]
  have h1 : MeasurableSet[hσ.measurableSpace] (F ∩ {ω | (s : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0)}) :=
    IsStoppingTime.measurableSpace_mono (hc.min hσ) hσ (fun ω => min_le_right _ _) _
      (IsStoppingTime.measurableSet_inter_le hc hσ F hF')
  have e : {ω | s ≤ σ ω} ∩ F = F ∩ {ω | (s : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e]
  exact hσ𝒮 _ h1

/-- **An event of `σ(X) ∨ 𝓕_s` on `{s < σ}` is an event of `σ(X) ∨ 𝓕_σ`.** -/
theorem measurableSet_lt_inter_sup {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0))
    (s : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 s] E) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace] ({ω | s < σ ω} ∩ E) := by
  have hD : MeasurableSet[hσ.measurableSpace] {ω | s < σ ω} := by
    have h := hσ.measurableSet_gt' s
    simpa only [WithTop.coe_lt_coe] using h
  have e : {ω | s < σ ω} ∩ E = ({ω | s ≤ σ ω} ∩ E) ∩ {ω | s < σ ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  rw [e]
  exact (measurableSet_le_inter_sup hσ s hE).inter (le_sup_right (b := hσ.measurableSpace) _ hD)

/-- An event of `σ(X) ∨ 𝓕_0` is an event of `σ(X) ∨ 𝓕_σ`. -/
theorem measurableSet_sup_of_zero {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0))
    {E : Set Ω} (hE : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 0] E) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace] E := by
  have h := measurableSet_le_inter_sup hσ 0 hE
  have e : {ω | (0 : ℝ≥0) ≤ σ ω} ∩ E = E := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, zero_le, true_and]
  rwa [e] at h

end Trace

/-! ### The adapted trace -/

section Adapted

open PocketStopWallsFin

/-- The measurable trace evaluation of a random path frozen after `u`, whose values up to `u` are measurable. -/
theorem measurable_traceAt_freezeAt {α : Type*} [MeasurableSpace α] {k : α → ℝ≥0 → ℝ} {u : ℝ≥0}
    (hk : ∀ r ≤ u, Measurable fun a => k a r) : Measurable fun a => LP.traceAt u (LP.freezeAt u (k a)) :=
  (LP.measurable_traceAt u).comp (Measurable.of_eval fun r => hk _ (min_le_right r u))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The adapted trace** of the killed driver: PROVE-LP's measurable radial-limit trace at time `u`. -/
def adTrace (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) (u : ℝ) : ℂ :=
  LP.traceAt u.toNNReal (killedPath W ζ ω)

/-- The killed driver at time `r` is `𝓕_r`-measurable for a driver adapted before its lifetime. -/
theorem measurable_killedPath_apply (hW : AdaptedBefore 𝓕 ζ W) (r : ℝ≥0) :
    Measurable[𝓕 r] fun ω => killedPath W ζ ω r := by
  intro B hB
  have hlt : MeasurableSet[𝓕 r] {ω | (r : ℝ≥0∞) < ζ ω} := by
    have := hW r univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have e : (fun ω => killedPath W ζ ω r) ⁻¹' B =
      {ω | (r : ℝ≥0∞) < ζ ω ∧ W r ω ∈ B} ∪ ({ω | (r : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
    ext ω
    simp only [killedPath, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    by_cases hω : (r : ℝ≥0∞) < ζ ω
    · simp only [hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
    · simp only [hω, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  exact (hW r B hB).union (hlt.compl.inter (MeasurableSet.const _))

/-- **The adapted trace at time `u ≤ s` is `𝓕_s`-measurable.** -/
theorem measurable_adTrace (hW : AdaptedBefore 𝓕 ζ W) {u : ℝ} {s : ℝ≥0} (hus : u ≤ s) :
    Measurable[𝓕 s] fun ω => adTrace W ζ ω u := by
  have hu : u.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hus
  have e : (fun ω => adTrace W ζ ω u) = fun ω => LP.traceAt u.toNNReal (LP.freezeAt u.toNNReal (killedPath W ζ ω)) :=
    funext fun ω => LP.traceAt_congr fun r hr => by simp only [LP.freezeAt, min_eq_left hr]
  rw [e]
  exact @measurable_traceAt_freezeAt Ω (𝓕 s) (killedPath W ζ) u.toNNReal fun r hr =>
    (measurable_killedPath_apply hW r).mono (𝓕.mono (hr.trans hu)) le_rfl

/-- **The adapted trace is the Loewner trace** where the driver is continuous with infinite lifetime. -/
theorem adTrace_eq {ω : Ω} {η : ℝ → ℂ} (hη : IsLoewnerTrace (fun s : ℝ => W s.toNNReal ω) η)
    (hc : Continuous fun s : ℝ => W s.toNNReal ω) (h0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {u : ℝ} (hu : 0 ≤ u) :
    adTrace W ζ ω u = η u := by
  have hk : killedPath W ζ ω = fun s => W s ω := funext fun s => by
    simp only [killedPath, hζ, ENNReal.coe_lt_top, ↓reduceIte]
  have hc' : Continuous fun s : ℝ≥0 => W s ω := continuous_nnreal_of_continuous_real hc
  have hlt : ((u.toNNReal : ℝ≥0) : ℝ) < u + 1 := by rw [Real.coe_toNNReal _ hu]; linarith
  rw [adTrace, hk, LP.traceAt_eq_trace hlt hc'.continuousOn h0, Real.coe_toNNReal _ hu]
  have hLT : IsLoewnerTraceLT (fun s : ℝ => W s.toNNReal ω) (u + 1) η :=
    ⟨hη.1, hη.2.1.mono fun t ht => ht.1, fun t ht _ => hη.2.2 t ht⟩
  exact hLT.trace_eq hc (by simpa using h0) hu (by linarith)

end Adapted

/-! ### Hitting capacity of a countable family -/

section Cap

variable {Ω : Type*} {𝓜 : MeasurableSpace Ω}

/-- **The hitting capacity of the range of a countable family of random points is measurable.** -/
theorem measurable_hcapHit_range {f : ℚ → Ω → ℂ} (hf : ∀ p, Measurable[𝓜] (f p)) :
    Measurable[𝓜] fun ω => WholeField.hcapHit (range fun p => f p ω) := by
  classical
  unfold WholeField.hcapHit
  refine Measurable.iInf fun n => Measurable.iInf fun s => Measurable.ite ?_ measurable_const measurable_const
  have hO : MeasurableSet (H \ WholeField.gridUnion n s) :=
    (QuantumZipper.isOpen_H.sdiff (WholeField.isClosed_gridUnion n s)).measurableSet
  have heq : {ω | Disjoint (range fun p => f p ω) (H \ WholeField.gridUnion n s)} =
      ⋂ p, (f p) ⁻¹' (H \ WholeField.gridUnion n s)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_compl_iff, Set.disjoint_left, forall_mem_range]
  rw [heq]
  exact MeasurableSet.iInter fun p => hf p hO.compl

end Cap

/-! ### The pocket's events on a configuration event, for an ambient σ-algebra -/

section Pocket

open PocketCoord PocketJordan PocketWordAssembly PocketTraversalMeasRand

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {G A : Set Ω} {e : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

/-- **Visiting a wall point during `[0, u]`** is an event on a configuration event `A`, for a path continuous on `A`
and measurable up to time `u`. -/
theorem measurableSet_mem_arc_image (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet A) (hAG : A ⊆ G)
    (he : ∀ ω ∈ A, ContinuousOn (e ω) (Ici 0)) {u : ℝ} (hu : 0 ≤ u)
    (hem : ∀ u', 0 ≤ u' → u' ≤ u → Measurable fun ω => e ω u') {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MeasurableSet {ω | ω ∈ A ∧ cfArcR (R ω) (L ω) r c ∈ e ω '' Icc 0 u} := by
  set ê : A → ℝ → ℂ := fun ω u' => e ω (min u' u) with hê
  have hêc : ∀ ω, ContinuousOn (ê ω) (Ici 0) := fun ω =>
    (he ω ω.2).comp (continuous_id.min continuous_const).continuousOn fun u' hu' => le_min hu' hu
  have hêm : ∀ u', 0 ≤ u' → Measurable fun ω : A => ê ω u' := fun u' hu' =>
    (hem _ (le_min hu' hu) (min_le_right _ _)).comp measurable_subtype_coe
  have hp := measurable_cfArcR_sub h𝓦 hRm hLm hGm hG hAG hc
  have hS := measurableSet_mem_image_Icc (α := A) hêc hêm hp hu
  have himg : ∀ ω : A, ê ω '' Icc 0 u = e ω '' Icc 0 u := fun ω =>
    image_congr fun u' hu' => by simp only [hê, min_eq_left hu'.2]
  have e1 : {ω | ω ∈ A ∧ cfArcR (R ω) (L ω) r c ∈ e ω '' Icc 0 u} =
      Subtype.val '' {ω : A | cfArcR (R ω) (L ω) r c ∈ ê ω '' Icc 0 u} := by
    ext ω
    constructor
    · rintro ⟨hω, h⟩
      exact ⟨⟨ω, hω⟩, by simp only [mem_ofPred_eq, himg]; exact h, rfl⟩
    · rintro ⟨ω', h, rfl⟩
      exact ⟨ω'.2, by simpa only [mem_ofPred_eq, himg] using h⟩
  rw [e1]
  exact MeasurableSet.subtype_image hA hS

/-- **A pocket visit at time `u`** is an event on a configuration event `A`. -/
theorem measurableSet_visit (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet A) (hAG : A ⊆ G) {u : ℝ}
    (hem : Measurable fun ω => e ω u) : MeasurableSet {ω | ω ∈ A ∧ e ω u ∈ cfPocket (R ω) (L ω) r} := by
  have hJ := measurable_cfPocket_sub h𝓦 hRm hLm hGm hG hAG
  have hf : Measurable fun ω : A => ((ω, e ω u) : A × ℂ) :=
    measurable_id.prodMk (hem.comp measurable_subtype_coe)
  have hS : MeasurableSet {ω : A | e ω u ∈ cfPocket (R ω) (L ω) r} := hf hJ
  have e1 : {ω | ω ∈ A ∧ e ω u ∈ cfPocket (R ω) (L ω) r} =
      Subtype.val '' {ω : A | e ω u ∈ cfPocket (R ω) (L ω) r} := by
    ext ω
    constructor
    · rintro ⟨hω, h⟩
      exact ⟨⟨ω, hω⟩, h, rfl⟩
    · rintro ⟨ω', h, rfl⟩
      exact ⟨ω'.2, h⟩
  rw [e1]
  exact MeasurableSet.subtype_image hA hS

open scoped Classical in
/-- **The Jordan coordinate of the pocket visit at time `u`** (`0` off the visit event). -/
def visPt (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (e : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (u : ℝ) (ω : Ω) : ℂ :=
  if ω ∈ A ∧ e ω u ∈ cfPocket (R ω) (L ω) r then ψ ω (e ω u) else 0

/-- **The Jordan coordinate of a pocket visit is measurable** for a Jordan coordinate family measurable for the walls'
σ-algebra at its measurable points. -/
theorem measurable_visPt (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet A) (hAG : A ⊆ G)
    (hψc : ∀ ω ∈ A, ContinuousOn (ψ ω) (closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {u : ℝ} (hem : Measurable fun ω => e ω u) :
    Measurable (visPt A R L r e ψ u) := by
  classical
  set A' := {ω | ω ∈ A ∧ e ω u ∈ cfPocket (R ω) (L ω) r} with hA'def
  have hA' : MeasurableSet A' := measurableSet_visit h𝓦 hRm hLm hGm hG hA hAG hem
  refine measurable_of_restrict_of_restrict_compl hA' ?_ ?_
  · have e1 : A'.domRestrict (visPt A R L r e ψ u) = fun ω : A' => ψ ω (e ω u) := funext fun ω => by
      simp only [Set.domRestrict_apply, visPt]
      exact ite_eq_left ω.2
    rw [e1]
    exact measurable_comp_of_isPointMeasurable h𝓦 hRm hLm hGm hG (A := A') (fun ω hω => hAG hω.1)
      (fun ω hω => hψc ω hω.1) hψm (p := fun ω : A' => e ω u) (hem.comp measurable_subtype_coe)
      fun ω => ⟨subset_closure ω.2.2, fun h => (hG _ (hAG ω.2.1)).cfPt_openPt_notMem (h ▸ ω.2.2)⟩
  · have e1 : A'ᶜ.domRestrict (visPt A R L r e ψ u) = fun _ => 0 := funext fun ω => by
      simp only [Set.domRestrict_apply, visPt]
      exact ite_eq_right ω.2
    rw [e1]
    exact measurable_const

open scoped Classical in
/-- **The capacity of the rational pocket visits up to `u`**, halved (the measurable form of the relative capacity
reached at ambient time `u`). -/
def ratCap (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (e : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (u : ℝ) (ω : Ω) : ℝ :=
  (WholeField.hcapHit (range fun p : ℚ =>
    if 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u then visPt A R L r e ψ p ω else 0)).toReal / 2

theorem measurable_ratCap (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet A) (hAG : A ⊆ G)
    (hψc : ∀ ω ∈ A, ContinuousOn (ψ ω) (closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {u : ℝ}
    (hem : ∀ u', 0 ≤ u' → u' ≤ u → Measurable fun ω => e ω u') : Measurable (ratCap A R L r e ψ u) := by
  classical
  refine (ENNReal.measurable_toReal.comp (measurable_hcapHit_range fun p => ?_)).div_const 2
  by_cases hp : 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u
  · simp only [hp, and_self, ↓reduceIte]
    exact measurable_visPt h𝓦 hRm hLm hGm hG hA hAG hψc hψm (hem _ hp.1 hp.2)
  · simp only [hp, ↓reduceIte]
    exact measurable_const

/-- **The distance from a wall point to the path at time `u`** is measurable on a configuration event. -/
theorem measurableSet_arc_dist_lt (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet A) (hAG : A ⊆ G) {u : ℝ}
    (hem : Measurable fun ω => e ω u) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (ε : ℝ) :
    MeasurableSet {ω | ω ∈ A ∧ dist (cfArcR (R ω) (L ω) r c) (e ω u) < ε} := by
  have hp := measurable_cfArcR_sub h𝓦 hRm hLm hGm hG hAG hc
  have hS : MeasurableSet {ω : A | dist (cfArcR (R ω) (L ω) r c) (e ω u) < ε} :=
    measurableSet_lt (hp.dist (hem.comp measurable_subtype_coe)) measurable_const
  have e1 : {ω | ω ∈ A ∧ dist (cfArcR (R ω) (L ω) r c) (e ω u) < ε} =
      Subtype.val '' {ω : A | dist (cfArcR (R ω) (L ω) r c) (e ω u) < ε} := by
    ext ω
    constructor
    · rintro ⟨hω, h⟩
      exact ⟨⟨ω, hω⟩, h, rfl⟩
    · rintro ⟨ω', h, rfl⟩
      exact ⟨ω'.2, h⟩
  rw [e1]
  exact MeasurableSet.subtype_image hA hS

end Pocket

end InteractingSLE.Sec7.PocketStopMarked
