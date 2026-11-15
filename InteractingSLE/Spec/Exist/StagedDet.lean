/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalMain

/-!
# Staged histories, step (b): Theorem 1.2 jointly measurable in the force word; the driver from the trace

Packet PROVE-STAGED (Goal 2 of PROVE-FLOWEXIST3, obstruction (b)). A staged history (`IsStagedHistory`) asks for
**one** measurable driver `E k : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞` serving the conditional laws at all `ω₀`, while the force word
of the conditional field (its marks are images of earlier marks under the earlier Loewner maps) depends on `ω₀`. The
frozen Theorem 1.2 is per force word: for each coupling it gives *some* Borel `Φ`. Nothing in its type makes the
choice measurable in the word, so the per-word statement does not give a jointly measurable version (a measurable
selection of a.e.-defined maps; Mathlib has no selection theorem, and the coupling law is not known to depend
measurably on the word). We therefore name the parametric version:

* **`Theorem12ParamStatement`** (named input): the frozen Theorem 1.2 with the determination map `Φ` jointly Borel in
  the word data `((xL, xR), (ρL, ρR))` and the field. It implies the frozen per-word statement
  (`theorem12Statement_of_param`).

The rest of this file is proved. The frozen Theorem 1.2 returns the trace; the staged history records the driver. On
the word-free Borel set `DSet` of *driver codes* (lifetime and killed dyadic driving code with a generating trace before
the lifetime) the trace code determines the driver code (`injOn_dTrace`: hulls are fillings of the trace, and hulls
determine continuous drivers), so a Borel left inverse `G` exists (Lusin–Souslin). Composed with `Φ` it gives the
jointly measurable **`detCode`**; on every coupling of the word it returns, almost surely, the lifetime and the killed
code of the driver (`ae_detCode_eq`). **`drvPath`** reads a driver code as a path frozen at the lifetime at its left
limit along `ζ − 1/(m+1)`, so that a staged driver built from it satisfies the left-limit clause of `IsStagedHistory`
at every sample (`drvPath_eq_of_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Exist

namespace Staged

open Sec2.Assembly LQGMetric

/-! ### The parametric determination input -/

/-- Force-word data with `nL` left and `nR` right marks: `((xL, xR), (ρL, ρR))` (positions, then weights). -/
abbrev WordData (nL nR : ℕ) : Type := ((Fin nL → ℝ) × (Fin nR → ℝ)) × ((Fin nL → ℝ) × (Fin nR → ℝ))

/-- **Named input: Theorem 1.2, jointly measurable in the force word.** The frozen Theorem 1.2
(`exists_measurable_lifetime_trace_eq_comp_field`, at universe `u`) with the word moved inside the determination map:
for fixed `κ > 0` and numbers of marks, one Borel `Φ` of the word data and the field returns, for every optional hull
coupling of every ordered word, almost surely the lifetime and the capacity-parametrized trace frozen after the
lifetime. -/
def Theorem12ParamStatement : Prop :=
  ∀ (κ : ℝ) (_ : 0 < κ) (nL nR : ℕ),
    ∃ Φ : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
        (_ : IsOrderedForceWord xL xR)
        {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
        {h : Ω → DistOn upperHalfPlaneOpens}
        (_ : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h),
        ∀ᵐ ω ∂P, (Φ (((xL, xR), (ρL, ρR)), h ω)).1 = ζ ω ∧
          ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
            ∀ t : ℝ≥0, (Φ (((xL, xR), (ρL, ρR)), h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal

/-- The parametric statement gives the frozen per-word Theorem 1.2. -/
theorem theorem12Statement_of_param (h : Theorem12ParamStatement.{u}) : Theorem12Statement.{u} := by
  intro κ hκ nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ hh hC
  obtain ⟨Φ, hΦm, hΦ⟩ := h κ hκ nL nR
  exact ⟨fun f => Φ (((xL, xR), (ρL, ρR)), f), hΦm.comp (measurable_const.prodMk measurable_id),
    hΦ xL xR ρL ρR hF hC⟩

/-! ### Driver codes and their trace codes -/

/-- A driver code: lifetime and killed dyadic driving code. -/
abbrev DCode : Type := ℝ≥0∞ × PCode

/-- The lifetime and the dyadic trace values (before the lifetime) of a driver code. -/
def dTrace (z : DCode) : ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  (z.1, fun n k => if (dyad n k : ℝ≥0∞) < z.1 then LP.traceAt (dyad n k) (dec z.2) else 0)

theorem measurable_dec_snd : Measurable fun z : DCode => dec z.2 :=
  measurable_pi_iff.2 fun _ => measurable_dec.comp (measurable_snd.prodMk measurable_const)

theorem measurable_dTrace : Measurable dTrace := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((LP.measurable_traceAt _).comp measurable_dec_snd) measurable_const

/-- **The good driver codes**: uniformly continuous before the lifetime, `0` at time `0` and from the lifetime on,
and with a generating trace on `[0, T]` for every dyadic `T` before the lifetime. -/
def DSet : Set DCode :=
  {z | (∀ n k, (dyad n k : ℝ≥0∞) < z.1 → UC z.2 (dyad n k)) ∧ (∀ n k, dyad n k = 0 → z.2 n k = 0) ∧
    (∀ n k, ¬ (dyad n k : ℝ≥0∞) < z.1 → z.2 n k = 0) ∧
    ∀ n k, (dyad n k : ℝ≥0∞) < z.1 → (dec z.2, ((dyad n k : ℝ≥0) : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet}

theorem measurableSet_DSet : MeasurableSet DSet := by
  have hc : ∀ n k, Measurable fun z : DCode => z.2 n k := fun n k =>
    (measurable_code n k).comp measurable_snd
  have hlt : ∀ n k, MeasurableSet {z : DCode | (dyad n k : ℝ≥0∞) < z.1} := fun n k =>
    measurableSet_lt measurable_const measurable_fst
  refine measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
  · refine Measurable.forall fun n => Measurable.forall fun k => ?_
    exact (measurableSet_setOfPred.1 (hlt n k)).imp
      (measurableSet_setOfPred.1 (measurable_snd (measurableSet_UC (dyad n k))))
  · refine Measurable.forall fun n => Measurable.forall fun k => ?_
    exact measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_eq_fun (hc n k) measurable_const))
  · refine Measurable.forall fun n => Measurable.forall fun k => ?_
    exact (measurableSet_setOfPred.1 (hlt n k)).not.imp
      (measurableSet_setOfPred.1 (measurableSet_eq_fun (hc n k) measurable_const))
  · refine Measurable.forall fun n => Measurable.forall fun k => ?_
    exact (measurableSet_setOfPred.1 (hlt n k)).imp (measurableSet_setOfPred.1
      ((measurable_dec_snd.prodMk measurable_const) Sec7.RandRestart.measurableSet_traceSet))

section DSetFacts

variable {z z' : DCode}

theorem continuousOn_of_mem_DSet (hz : z ∈ DSet) : ContinuousOn (dec z.2) {t | (t : ℝ≥0∞) < z.1} :=
  continuousOn_dec_of_UC hz.1

theorem dec_zero_of_mem_DSet (hz : z ∈ DSet) (hpos : 0 < z.1) : dec z.2 0 = 0 := by
  have h00 : ((dyad 0 0 : ℝ≥0) : ℝ≥0∞) < z.1 := by rw [dyad_zero_zero, ENNReal.coe_zero]; exact hpos
  have := (hz.1 0 0 h00).dec_dyad le_rfl
  rw [dyad_zero_zero] at this
  rw [this]
  exact hz.2.1 0 0 dyad_zero_zero

/-- On the good set, a generating trace exists on `[0, T]` for every dyadic `T` before the lifetime. -/
theorem exists_isGeneratingTrace_of_mem_DSet (hz : z ∈ DSet) {n k : ℕ} (hT : (dyad n k : ℝ≥0∞) < z.1) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (dec z.2) (dyad n k) η := by
  have hcw := continuousOn_of_mem_DSet hz
  have hc : ContinuousOn (dec z.2) {t : ℝ≥0 | (t : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞)} :=
    hcw.mono fun t ht => lt_trans ht hT
  have hlim : 0 < ((dyad n k : ℝ≥0) : ℝ≥0∞) → ((dyad n k : ℝ≥0) : ℝ≥0∞) < ⊤ →
      ∃ w₀ : ℝ, Tendsto (dec z.2) (𝓝[<] ((dyad n k : ℝ≥0) : ℝ≥0∞).toNNReal) (𝓝 w₀) := fun _ _ => by
    refine ⟨dec z.2 (dyad n k), ?_⟩
    rw [ENNReal.toNNReal_coe]
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < z.1} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((hcw (dyad n k) hT).continuousAt (hopen.mem_nhds hT)).tendsto.mono_left nhdsWithin_le_nhds
  have hpos : 0 < z.1 := lt_of_le_of_lt zero_le hT
  obtain ⟨η, hη, -⟩ :=
    (Sec7.RandRestart.mem_traceSet_iff hc (dec_zero_of_mem_DSet hz hpos) hlim).1 (hz.2.2.2 n k hT)
  exact ⟨η, hη⟩

theorem lifetime_eq_of_dTrace_eq (he : dTrace z = dTrace z') : z.1 = z'.1 :=
  congrArg (fun p : ℝ≥0∞ × (ℕ → ℕ → ℂ) => p.1) he

theorem traceAt_eq_of_dTrace_eq (he : dTrace z = dTrace z') {n k : ℕ} (hlt : (dyad n k : ℝ≥0∞) < z.1) :
    LP.traceAt (dyad n k) (dec z.2) = LP.traceAt (dyad n k) (dec z'.2) := by
  have h := congrFun (congrFun (congrArg Prod.snd he) n) k
  have hlt' : (dyad n k : ℝ≥0∞) < z'.1 := lifetime_eq_of_dTrace_eq he ▸ hlt
  simp only [dTrace, hlt, hlt', ↓reduceIte] at h
  exact h

/-- **Equal trace codes give equal hulls** before the lifetime. -/
theorem fwdHull_eq_of_dTrace_eq (hz : z ∈ DSet) (hz' : z' ∈ DSet) (he : dTrace z = dTrace z') {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < z.1) :
    QuantumZipper.fwdHull (fun s : ℝ => dec z.2 s.toNNReal) t =
      QuantumZipper.fwdHull (fun s : ℝ => dec z'.2 s.toNNReal) t := by
  have hζ := lifetime_eq_of_dTrace_eq he
  obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
  have hdζ' : (dyad n k : ℝ≥0∞) < z'.1 := hζ ▸ hdζ
  obtain ⟨η, hη⟩ := exists_isGeneratingTrace_of_mem_DSet hz hdζ
  obtain ⟨η', hη'⟩ := exists_isGeneratingTrace_of_mem_DSet hz' hdζ'
  have hc : ∀ {y : DCode}, y ∈ DSet → (dyad n k : ℝ≥0∞) < y.1 →
      ContinuousOn (dec y.2) {s : ℝ≥0 | (s : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞)} := fun hy hy' =>
    (continuousOn_of_mem_DSet hy).mono fun s hs => lt_trans hs hy'
  have h0 : ∀ {y : DCode}, y ∈ DSet → (dyad n k : ℝ≥0∞) < y.1 → dec y.2 0 = 0 := fun hy hy' =>
    dec_zero_of_mem_DSet hy (lt_of_le_of_lt zero_le hy')
  have hval : ∀ m j, dyad m j < dyad n k → η (dyad m j) = η' (dyad m j) := fun m j hmj => by
    have hmj' : ((dyad m j : ℝ≥0) : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hmj
    rw [← LP.traceAt_eq_of_isGeneratingTrace hη (hc hz hdζ) (h0 hz hdζ) hmj',
      ← LP.traceAt_eq_of_isGeneratingTrace hη' (hc hz' hdζ') (h0 hz' hdζ') hmj']
    exact traceAt_eq_of_dTrace_eq he (lt_trans hmj' hdζ)
  have heqη : ∀ s : ℝ≥0, s < dyad n k → η s = η' s := fun s hs => by
    have hu : Tendsto (fun m => dyad m (flr m s)) atTop
        (𝓝[{u : ℝ≥0 | (u : ℝ≥0∞) ≤ ((dyad n k : ℝ≥0) : ℝ≥0∞)}] s) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr s, Eventually.of_forall fun m =>
        ENNReal.coe_le_coe.2 ((dyad_flr_le m s).trans hs.le)⟩
    have hs' : s ∈ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ((dyad n k : ℝ≥0) : ℝ≥0∞)} := ENNReal.coe_le_coe.2 hs.le
    have h1 := ((hη.2.1 s hs').tendsto).comp hu
    have h2 := ((hη'.2.1 s hs').tendsto).comp hu
    refine tendsto_nhds_unique h1 (h2.congr fun m => ?_)
    exact (hval m (flr m s) ((dyad_flr_le m s).trans_lt hs)).symm
  have htT : t < dyad n k := by exact_mod_cast htd
  have himg : η '' Icc 0 t = η' '' Icc 0 t :=
    image_congr fun s hs => heqη s (lt_of_le_of_lt hs.2 htT)
  have htT' : (t : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 htT
  have hA : IsCompact (η '' Icc 0 t) := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun s hs => ENNReal.coe_le_coe.2 (hs.2.trans htT.le))
  have hF := (isFilling_iff_inter_H_eq_fillH hA.isBounded hA.isClosed).1 (hη.2.2 t htT')
  have hF' := (isFilling_iff_inter_H_eq_fillH hA.isBounded hA.isClosed).1 (himg ▸ hη'.2.2 t htT')
  calc QuantumZipper.fwdHull (fun s : ℝ => dec z.2 s.toNNReal) t
      = QuantumZipper.fwdHull (fun s : ℝ => dec z.2 s.toNNReal) t ∩ H :=
        (inter_eq_left.2 (fwdHull_subset_H t.2)).symm
    _ = QuantumZipper.fwdHull (fun s : ℝ => dec z'.2 s.toNNReal) t ∩ H := by rw [hF, hF']
    _ = _ := inter_eq_left.2 (fwdHull_subset_H t.2)

/-- **Equal trace codes give equal drivers** before the lifetime. -/
theorem dec_eq_of_dTrace_eq (hz : z ∈ DSet) (hz' : z' ∈ DSet) (he : dTrace z = dTrace z') {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < z.1) : dec z.2 t = dec z'.2 t := by
  have hζ := lifetime_eq_of_dTrace_eq he
  obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
  set T : ℝ := ((dyad n k : ℝ≥0) : ℝ) with hT
  have hT0 : 0 ≤ T := (dyad n k).2
  have hcont : ∀ {y : DCode}, y ∈ DSet → (dyad n k : ℝ≥0∞) < y.1 →
      ContinuousOn (fun s : ℝ => dec y.2 s.toNNReal) (Icc 0 T) := fun hy hy' => by
    refine (continuousOn_of_mem_DSet hy).comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hy'
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2
  have hdζ' : (dyad n k : ℝ≥0∞) < z'.1 := hζ ▸ hdζ
  set Wc := Ito.clampDrv (fun s : ℝ => dec z.2 s.toNNReal) T with hWc
  set Wc' := Ito.clampDrv (fun s : ℝ => dec z'.2 s.toNNReal) T with hWc'
  have hWcc : Continuous Wc := Ito.continuous_clampDrv hT0 (hcont hz hdζ)
  have hWcc' : Continuous Wc' := Ito.continuous_clampDrv hT0 (hcont hz' hdζ')
  have hpos : 0 < z.1 := lt_of_le_of_lt zero_le hdζ
  have hpos' : 0 < z'.1 := lt_of_le_of_lt zero_le hdζ'
  have hW0 : Wc 0 = 0 := by
    rw [hWc, Ito.clampDrv_eqOn ⟨le_rfl, hT0⟩]; simpa using dec_zero_of_mem_DSet hz hpos
  have hW0' : Wc' 0 = 0 := by
    rw [hWc', Ito.clampDrv_eqOn ⟨le_rfl, hT0⟩]; simpa using dec_zero_of_mem_DSet hz' hpos'
  have htT : (t : ℝ) < T := by exact_mod_cast htd
  have hhull : ∀ s ∈ Icc (0 : ℝ) t, QuantumZipper.fwdHull Wc s = QuantumZipper.fwdHull Wc' s := by
    intro s hs
    have hsT : s < T := lt_of_le_of_lt hs.2 htT
    rw [fwdHull_eq_of_eqOn hs.1 hsT fun r hr => Ito.clampDrv_eqOn hr,
      fwdHull_eq_of_eqOn (W := Wc') hs.1 hsT fun r hr => Ito.clampDrv_eqOn hr]
    have hsζ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < z.1 := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) ht
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    have h := fwdHull_eq_of_dTrace_eq hz hz' he hsζ
    rwa [Real.coe_toNNReal _ hs.1] at h
  have heq := Sec6.eqOn_of_fwdHull_eq hWcc hWcc' hW0 hW0' t.2 hhull ⟨t.2, le_rfl⟩
  rw [hWc, hWc', Ito.clampDrv_eqOn ⟨t.2, htT.le⟩, Ito.clampDrv_eqOn ⟨t.2, htT.le⟩] at heq
  simpa using heq

/-- **On the good set, the trace code determines the driver code.** -/
theorem injOn_dTrace : InjOn dTrace DSet := by
  intro z hz z' hz' he
  have hζ := lifetime_eq_of_dTrace_eq he
  refine Prod.ext hζ (funext fun n => funext fun k => ?_)
  by_cases hlt : (dyad n k : ℝ≥0∞) < z.1
  · have hlt' : (dyad n k : ℝ≥0∞) < z'.1 := hζ ▸ hlt
    rw [← (hz.1 n k hlt).dec_dyad le_rfl, ← (hz'.1 n k hlt').dec_dyad le_rfl]
    exact dec_eq_of_dTrace_eq hz hz' he hlt
  · have hlt' : ¬ (dyad n k : ℝ≥0∞) < z'.1 := hζ ▸ hlt
    rw [hz.2.2.1 n k hlt, hz'.2.2.1 n k hlt']

end DSetFacts

/-- A Borel left inverse of the trace code on the good driver codes. -/
theorem exists_dTrace_leftInverse :
    ∃ G : ℝ≥0∞ × (ℕ → ℕ → ℂ) → DCode, Measurable G ∧ ∀ z ∈ DSet, G (dTrace z) = z :=
  exists_measurable_leftInverse_of_injOn measurable_dTrace measurableSet_DSet injOn_dTrace

/-- The chosen Borel left inverse. -/
def dInv : ℝ≥0∞ × (ℕ → ℕ → ℂ) → DCode := exists_dTrace_leftInverse.choose

theorem measurable_dInv : Measurable dInv := exists_dTrace_leftInverse.choose_spec.1

theorem dInv_dTrace {z : DCode} (hz : z ∈ DSet) : dInv (dTrace z) = z :=
  exists_dTrace_leftInverse.choose_spec.2 z hz

/-- The killed driver code of a history code. -/
def dOf {nL nR : ℕ} (x : XCode nL nR) : DCode := (cζ x, x.2.2.1)

theorem dTrace_dOf {nL nR : ℕ} (x : XCode nL nR) : dTrace (dOf x) = traceOfCode x := rfl

theorem dOf_mem_DSet {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {x : XCode nL nR} (hx : x ∈ DetSet a xL xR ρL ρR) : dOf x ∈ DSet := by
  obtain ⟨⟨⟨⟨hg, -, -⟩, hcan⟩, -⟩, htr⟩ := hx
  refine ⟨fun n k h => (hg.2 n k h).1, fun n k h => ((hcan n k).1 h).1, fun n k h => ?_, htr⟩
  by_cases h0 : dyad n k = 0
  · exact ((hcan n k).1 h0).1
  · exact ((hcan n k).2 h0 h).1

/-! ### The driver path of a code, frozen at its left limit -/

/-- The driver path of a driver code: the decoded path before the lifetime, and from the lifetime on the `limsup`
of its values at `ζ − 1/(m+1)` (its left limit when it has one). -/
def drvPath (z : DCode) (t : ℝ≥0) : ℝ :=
  if (t : ℝ≥0∞) < z.1 then dec z.2 t
  else limsup (fun m : ℕ => dec z.2 (z.1.toNNReal - 1 / ((m : ℝ≥0) + 1))) atTop

theorem measurable_drvPath : Measurable drvPath := by
  refine measurable_pi_iff.2 fun t => ?_
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (measurable_dec.comp (measurable_snd.prodMk measurable_const)) ?_
  refine Measurable.limsup fun m => ?_
  exact measurable_dec.comp (measurable_snd.prodMk
    ((measurable_fst.ennreal_toNNReal).sub measurable_const))

theorem drvPath_of_lt {z : DCode} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < z.1) : drvPath z t = dec z.2 t := by
  simp only [drvPath, ht, ↓reduceIte]

/-- `ζ − 1/(m+1)` tends to `ζ` from below. -/
theorem tendsto_sub_inv {ζ : ℝ≥0} (hζ : 0 < ζ) :
    Tendsto (fun m : ℕ => ζ - 1 / ((m : ℝ≥0) + 1)) atTop (𝓝[<] ζ) := by
  have hinv : Tendsto (fun m : ℕ => (1 : ℝ≥0) / ((m : ℝ≥0) + 1)) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := (tendsto_const_nhds (x := ζ)).sub hinv
    simpa using this
  · obtain ⟨M, hM⟩ := (hinv.eventually (gt_mem_nhds hζ)).exists_forall_of_atTop
    refine eventually_atTop.2 ⟨M, fun m hm => ?_⟩
    have h1 : 1 / ((m : ℝ≥0) + 1) < ζ := hM m hm
    have hpos : (0 : ℝ≥0) < 1 / ((m : ℝ≥0) + 1) := by positivity
    exact tsub_lt_self (lt_trans hpos h1) hpos

/-- **The left-limit clause holds at every sample**: at a finite positive lifetime, the frozen value is the
continuous left limit whenever the path has one. -/
theorem drvPath_eq_of_tendsto {z : DCode} (hne : z.1 ≠ ⊤) (hpos : 0 < z.1) {c : ℝ}
    (hc : Tendsto (drvPath z) (𝓝[<] z.1.toNNReal) (𝓝 c)) : drvPath z z.1.toNNReal = c := by
  have hζ : (0 : ℝ≥0) < z.1.toNNReal := ENNReal.toNNReal_pos hpos.ne' hne
  have hnot : ¬ ((z.1.toNNReal : ℝ≥0) : ℝ≥0∞) < z.1 := by rw [ENNReal.coe_toNNReal hne]; exact lt_irrefl _
  simp only [drvPath, hnot, ↓reduceIte]
  have hs := tendsto_sub_inv hζ
  have h1 : Tendsto (fun m : ℕ => drvPath z (z.1.toNNReal - 1 / ((m : ℝ≥0) + 1))) atTop (𝓝 c) :=
    hc.comp hs
  have h2 : Tendsto (fun m : ℕ => dec z.2 (z.1.toNNReal - 1 / ((m : ℝ≥0) + 1))) atTop (𝓝 c) := by
    refine h1.congr' ?_
    filter_upwards [(tendsto_nhdsWithin_iff.1 hs).2] with m hm
    refine drvPath_of_lt ?_
    rw [← ENNReal.coe_toNNReal hne]
    exact ENNReal.coe_lt_coe.2 hm
  exact h2.limsup_eq

/-! ### The jointly measurable driver determination -/

/-- The trace code read off a determination output. -/
def outCode (o : ℝ≥0∞ × (ℝ≥0 → ℂ)) : ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  (o.1, fun n k => if (dyad n k : ℝ≥0∞) < o.1 then o.2 (dyad n k) else 0)

theorem measurable_outCode : Measurable outCode := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((measurable_pi_apply _).comp measurable_snd) measurable_const

theorem outCode_eq_codeΦ (Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)) (f : DistOn upperHalfPlaneOpens) :
    outCode (Φ f) = codeΦ Φ f := rfl

/-- **The driver code determined by the field**, jointly measurable in the word and the field. -/
def detCode {nL nR : ℕ} (Φ : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ))
    (p : WordData nL nR × DistOn upperHalfPlaneOpens) : DCode :=
  dInv (outCode (Φ p))

theorem measurable_detCode {nL nR : ℕ} {Φ : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)}
    (hΦ : Measurable Φ) : Measurable (detCode Φ) :=
  measurable_dInv.comp (measurable_outCode.comp hΦ)

/-- **On every coupling of the word, the determined driver code is almost surely the killed driver code**: there is a
history code `x₀` in the good set `DetSet` with lifetime `ζ` and paths `(W, V)` before `ζ`, and
`detCode Φ (w, h) = dOf x₀`. -/
theorem ae_detCode_eq {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {Φ : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h13 : Theorem13Statement.{u})
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hΦ : ∀ᵐ ω ∂P, (Φ (((xL, xR), (ρL, ρR)), h ω)).1 = ζ ω ∧
          ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
            ∀ t : ℝ≥0, (Φ (((xL, xR), (ρL, ρR)), h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal) :
    ∀ᵐ ω ∂P, ∃ x₀ : XCode nL nR, x₀ ∈ DetSet κ xL xR ρL ρR ∧ cζ x₀ = ζ ω ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw x₀ t = W t ω ∧ (∀ i, cvL x₀ i t = VL i t ω) ∧
        ∀ j, cvR x₀ j t = VR j t ω) ∧
      detCode Φ (((xL, xR), (ρL, ρR)), h ω) = dOf x₀ := by
  have hE := hC.1
  have h13' := h13 hκ hF hE
  obtain ⟨B', -, hB'c, -, -, hB'ae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  filter_upwards [hΦ, h13', ae_codeOf_mem hκ hE hB'c hB'ae] with ω hΦω h13ω hcode
  obtain ⟨-, η, hη, -⟩ := h13ω
  obtain ⟨hx₁, hdec⟩ := hcode
  set x₀ := frz (codeOf xL xR B' W VL VR ζ ω) with hx₀def
  have hζx : cζ x₀ = ζ ω := rfl
  have hcwx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw x₀ t = W t ω := fun t ht => (hdec t ht).1
  have hηx : IsGeneratingTrace (cw x₀) (ζ ω) η := Sec7.IsGeneratingTrace.congr_lt hη hcwx
  have hcrel : x₀ ∈ CRel κ xL xR ρL ρR := frz_mem_cRel hx₁
  have hmem : x₀ ∈ DetSet κ xL xR ρL ρR :=
    ⟨⟨hcrel, frozenB_frz hx₁.1.1⟩, fun n k hT => mem_traceSet_of_isGeneratingTrace hcrel hT hηx hT.le⟩
  have hcode : traceOfCode x₀ = outCode (Φ (((xL, xR), (ρL, ρR)), h ω)) := by
    refine Prod.ext hΦω.1.symm (funext fun n => funext fun k => ?_)
    simp only [traceOfCode, outCode, hζx, hΦω.1]
    by_cases hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ ω
    · simp only [hlt, ↓reduceIte]
      rw [hΦω.2 η hη, min_eq_left hlt.le, ENNReal.toNNReal_coe]
      exact LP.traceAt_eq_of_isGeneratingTrace hηx hcrel.1.1.continuousOn_w hcrel.1.2.2.1 hlt
    · simp only [hlt, ↓reduceIte]
  refine ⟨x₀, hmem, hζx, fun t ht => (hdec t ht).1.symm ▸ ⟨rfl, ?_, ?_⟩, ?_⟩
  · exact fun i => (hdec t ht).2.1 i
  · exact fun j => (hdec t ht).2.2.1 j
  · rw [detCode, ← hcode, ← dTrace_dOf]
    exact dInv_dTrace (dOf_mem_DSet hmem)

end Staged

end Exist

end InteractingSLE
