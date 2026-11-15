/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Uniq
import InteractingSLE.Spec.Sec2.AssemblyUnique
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Spec.Ito.Loewner

/-!
# The driving history is a Borel function of its trace (codes)

Packet PROVE-FLOWEXIST, step "recover `W` and `V` measurably from the trace" of `exists_isFlowLine`. The frozen
Theorem 1.2 determines only the lifetime and the trace by the field; the frozen `IsFlowLine` needs the driving
process `(W, V)` itself. This file works on the standard Borel code space `Sec2.Assembly.XCode` of the Theorem 2.2
assembly (driving code, lifetime, killed state codes):

* `traceOfCode x`: the lifetime and the trace values `LP.traceAt (k/2ⁿ) w` at the dyadic times before it (a
  measurable map, `measurable_traceOfCode`);
* `frz x`: the code whose driving path is frozen at the lifetime (`0` for lifetime `0`); `FrozenB`;
* **`DetSet a xL xR ρL ρR`**: canonical solution codes (`Sec2.Assembly.CRel`) with frozen driving path and a
  generating trace on `[0, T]` for every dyadic `T` before the lifetime (`RandRestart.traceSet`); measurable;
* **`injOn_traceOfCode`**: on `DetSet`, the trace code determines the code. The trace determines the hulls, hence
  the driver (`Sec6.eqOn_of_fwdHull_eq`); the driver determines the force points (`Exist.eqOn_of_force_eq`); the
  driving equation then determines the Brownian path before the lifetime, and freezing determines it afterwards.

Mathematical steps added (not in the specification; standard Loewner theory): the hulls `K_t` are the fillings of
`η[0, t]`, so equal traces give equal hulls, and equal hulls give equal continuous drivers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Exist

open Sec2.Assembly

variable {nL nR : ℕ}

/-! ### The trace code of a history code -/

/-- The lifetime and the trace values at the dyadic times before it. -/
def traceOfCode (x : XCode nL nR) : ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  (cζ x, fun n k => if (dyad n k : ℝ≥0∞) < cζ x then LP.traceAt (dyad n k) (cw x) else 0)

theorem measurable_cw : Measurable (cw : XCode nL nR → ℝ≥0 → ℝ) :=
  measurable_pi_iff.2 fun t => measurable_cw_at t

theorem measurable_traceOfCode : Measurable (traceOfCode (nL := nL) (nR := nR)) := by
  refine measurable_cζ.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_cζ)
    ((LP.measurable_traceAt _).comp measurable_cw) measurable_const

/-! ### Freezing the driving path at the lifetime -/

/-- The driving path frozen at the lifetime (`0` when the lifetime is `0`). -/
def frzPath (x : XCode nL nR) (t : ℝ≥0) : ℝ :=
  if cζ x = 0 then 0 else if (t : ℝ≥0∞) < cζ x then cb x t else cb x (cζ x).toNNReal

/-- The code with the driving path frozen at the lifetime. -/
def frz (x : XCode nL nR) : XCode nL nR := (enc (frzPath x), x.2)

/-- The driving code is frozen at the lifetime. -/
def FrozenB (x : XCode nL nR) : Prop :=
  ∀ n k, ¬ (dyad n k : ℝ≥0∞) < cζ x → x.1 n k = if cζ x = 0 then 0 else cb x (cζ x).toNNReal

theorem measurable_cb_lifetime : Measurable fun x : XCode nL nR => cb x (cζ x).toNNReal :=
  measurable_dec.comp (measurable_code_b.prodMk measurable_cζ.ennreal_toNNReal)

theorem measurable_frozenB : Measurable fun x : XCode nL nR => FrozenB x := by
  refine Measurable.forall fun n => Measurable.forall fun k => ?_
  refine (measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_cζ)).not.imp ?_
  refine measurable_eq_real ((measurable_code n k).comp measurable_code_b) ?_
  exact Measurable.ite (measurable_cζ (measurableSet_singleton 0)) measurable_const measurable_cb_lifetime

theorem continuous_frzPath {x : XCode nL nR} (hb : Continuous (cb x)) : Continuous (frzPath x) := by
  unfold frzPath
  by_cases h0 : cζ x = 0
  · simp only [h0, ↓reduceIte]; exact continuous_const
  · simp only [h0, ↓reduceIte]
    by_cases ht : cζ x = ⊤
    · have e : (fun t : ℝ≥0 => if (t : ℝ≥0∞) < cζ x then cb x t else cb x (cζ x).toNNReal) = cb x := by
        funext t
        have hlt : (t : ℝ≥0∞) < cζ x := by rw [ht]; exact ENNReal.coe_lt_top
        simp only [hlt, ↓reduceIte]
      rw [e]; exact hb
    · have e : (fun t : ℝ≥0 => if (t : ℝ≥0∞) < cζ x then cb x t else cb x (cζ x).toNNReal) =
          fun t => cb x (min t (cζ x).toNNReal) := by
        funext t
        by_cases hlt : (t : ℝ≥0∞) < cζ x
        · simp only [hlt, ↓reduceIte]
          rw [min_eq_left]
          rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal ht]; exact hlt.le
        · simp only [hlt, ↓reduceIte]
          rw [min_eq_right]
          rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal ht]; exact not_lt.1 hlt
      rw [e]
      exact hb.comp (continuous_id.min continuous_const)

theorem cb_frz {x : XCode nL nR} (hb : Continuous (cb x)) (t : ℝ≥0) : cb (frz x) t = frzPath x t :=
  dec_enc (continuous_frzPath hb).continuousWithinAt

theorem good_frz {x : XCode nL nR} (hx : Good x) : Good (frz x) :=
  ⟨fun _ => uc_enc (continuous_frzPath hx.continuous_b).continuousOn, hx.2⟩

theorem frozenB_frz {x : XCode nL nR} (hx : Good x) : FrozenB (frz x) := by
  intro n k hnk
  change ¬ (dyad n k : ℝ≥0∞) < cζ x at hnk
  change enc (frzPath x) n k = if cζ x = 0 then 0 else cb (frz x) (cζ x).toNNReal
  rw [cb_frz hx.continuous_b]
  unfold enc frzPath
  by_cases h0 : cζ x = 0
  · simp only [h0, ↓reduceIte]
  · have hfin : cζ x ≠ ⊤ := fun h => hnk (h ▸ ENNReal.coe_lt_top)
    have hnlt : ¬ (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) < cζ x := by
      rw [ENNReal.coe_toNNReal hfin]; exact lt_irrefl _
    simp only [h0, ↓reduceIte, hnk, hnlt]

theorem frz_mem_cRel {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {x : XCode nL nR} (hx : x ∈ CRel a xL xR ρL ρR) : frz x ∈ CRel a xL xR ρL ρR := by
  obtain ⟨⟨hg, hlim, hp⟩, hc⟩ := hx
  refine ⟨⟨good_frz hg, hlim, ?_⟩, hc⟩
  refine isIntegratedSLEPath_congr hp rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) fun t ht => ?_
  change (t : ℝ≥0∞) < cζ x at ht
  rw [cb_frz hg.continuous_b]
  unfold frzPath
  have h0 : cζ x ≠ 0 := fun h => by rw [h] at ht; exact absurd ht (not_lt.2 bot_le)
  simp only [h0, ↓reduceIte, ht]

theorem measurable_frz : Measurable (frz (nL := nL) (nR := nR)) := by
  refine (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_).prodMk measurable_snd
  change Measurable fun x : XCode nL nR => frzPath x (dyad n k)
  unfold frzPath
  refine Measurable.ite (measurable_cζ (measurableSet_singleton 0)) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_cζ) (measurable_cb_at _)
      measurable_cb_lifetime)

/-! ### The good set -/

/-- **The good set of history codes**: canonical solution codes with frozen driving path and a generating trace
on `[0, T]` for every dyadic `T` before the lifetime. -/
def DetSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Set (XCode nL nR) :=
  CRel a xL xR ρL ρR ∩ {x | FrozenB x} ∩
    {x | ∀ n k, (dyad n k : ℝ≥0∞) < cζ x → (cw x, ((dyad n k : ℝ≥0) : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet}

theorem measurableSet_detSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : MeasurableSet (DetSet a xL xR ρL ρR) := by
  refine ((measurableSet_cRel a xL xR ρL ρR).inter (measurableSet_setOfPred.2 measurable_frozenB)).inter ?_
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.forall fun k => ?_)
  refine (measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_cζ)).imp ?_
  exact measurableSet_setOfPred.1
    ((measurable_cw.prodMk measurable_const) Sec7.RandRestart.measurableSet_traceSet)

/-- On the good set, a generating trace exists on `[0, T]` for every dyadic `T` before the lifetime. -/
theorem exists_isGeneratingTrace_of_mem_detSet {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {x : XCode nL nR} (hx : x ∈ DetSet a xL xR ρL ρR) {n k : ℕ}
    (hT : (dyad n k : ℝ≥0∞) < cζ x) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (cw x) (dyad n k) η := by
  obtain ⟨⟨⟨⟨hg, -, hp⟩, -⟩, -⟩, htr⟩ := hx
  have hcw := hg.continuousOn_w
  have hc : ContinuousOn (cw x) {t : ℝ≥0 | (t : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞)} :=
    hcw.mono fun t ht => lt_trans ht hT
  have hlim : 0 < ((dyad n k : ℝ≥0) : ℝ≥0∞) → ((dyad n k : ℝ≥0) : ℝ≥0∞) < ⊤ →
      ∃ w₀ : ℝ, Tendsto (cw x) (𝓝[<] ((dyad n k : ℝ≥0) : ℝ≥0∞).toNNReal) (𝓝 w₀) := fun _ _ => by
    refine ⟨cw x (dyad n k), ?_⟩
    rw [ENNReal.toNNReal_coe]
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((hcw (dyad n k) hT).continuousAt (hopen.mem_nhds hT)).tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨η, hη, -⟩ := (Sec7.RandRestart.mem_traceSet_iff hc hp.1 hlim).1 (htr n k hT)
  exact ⟨η, hη⟩

/-! ### The trace code determines the code on the good set -/

section Inj

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

theorem fwdHull_subset_H {W : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) : QuantumZipper.fwdHull W t ⊆ H := fun _ hz =>
  ((mem_fwdHull_iff_forall ht).1 hz).1

theorem lifetime_eq_of_traceOfCode_eq {x x' : XCode nL nR} (he : traceOfCode x = traceOfCode x') :
    cζ x = cζ x' :=
  congrArg (fun p : ℝ≥0∞ × (ℕ → ℕ → ℂ) => p.1) he

theorem traceAt_eq_of_traceOfCode_eq {x x' : XCode nL nR} (he : traceOfCode x = traceOfCode x') {n k : ℕ}
    (hlt : (dyad n k : ℝ≥0∞) < cζ x) : LP.traceAt (dyad n k) (cw x) = LP.traceAt (dyad n k) (cw x') := by
  have h := congrFun (congrFun (congrArg Prod.snd he) n) k
  have hlt' : (dyad n k : ℝ≥0∞) < cζ x' := lifetime_eq_of_traceOfCode_eq he ▸ hlt
  simp only [traceOfCode, hlt, hlt', ↓reduceIte] at h
  exact h

/-- **Equal trace codes give equal hulls** before the lifetime (the hull is the filling of the trace). -/
theorem fwdHull_eq_of_traceOfCode_eq {x x' : XCode nL nR} (hx : x ∈ DetSet a xL xR ρL ρR)
    (hx' : x' ∈ DetSet a xL xR ρL ρR) (he : traceOfCode x = traceOfCode x') {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < cζ x) :
    QuantumZipper.fwdHull (fun s : ℝ => cw x s.toNNReal) t =
      QuantumZipper.fwdHull (fun s : ℝ => cw x' s.toNNReal) t := by
  have hζ := lifetime_eq_of_traceOfCode_eq he
  obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
  have hdζ' : (dyad n k : ℝ≥0∞) < cζ x' := hζ ▸ hdζ
  obtain ⟨η, hη⟩ := exists_isGeneratingTrace_of_mem_detSet hx hdζ
  obtain ⟨η', hη'⟩ := exists_isGeneratingTrace_of_mem_detSet hx' hdζ'
  have hc : ∀ {y : XCode nL nR}, y ∈ DetSet a xL xR ρL ρR → (dyad n k : ℝ≥0∞) < cζ y →
      ContinuousOn (cw y) {s : ℝ≥0 | (s : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞)} := fun hy hy' =>
    hy.1.1.1.1.continuousOn_w.mono fun s hs => lt_trans hs hy'
  have h0 : ∀ {y : XCode nL nR}, y ∈ DetSet a xL xR ρL ρR → cw y 0 = 0 := fun hy => hy.1.1.1.2.2.1
  have hval : ∀ m j, dyad m j < dyad n k → η (dyad m j) = η' (dyad m j) := fun m j hmj => by
    have hmj' : ((dyad m j : ℝ≥0) : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hmj
    rw [← LP.traceAt_eq_of_isGeneratingTrace hη (hc hx hdζ) (h0 hx) hmj',
      ← LP.traceAt_eq_of_isGeneratingTrace hη' (hc hx' hdζ') (h0 hx') hmj']
    exact traceAt_eq_of_traceOfCode_eq he (lt_trans hmj' hdζ)
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
  calc QuantumZipper.fwdHull (fun s : ℝ => cw x s.toNNReal) t
      = QuantumZipper.fwdHull (fun s : ℝ => cw x s.toNNReal) t ∩ H :=
        (inter_eq_left.2 (fwdHull_subset_H t.2)).symm
    _ = QuantumZipper.fwdHull (fun s : ℝ => cw x' s.toNNReal) t ∩ H := by rw [hF, hF']
    _ = _ := inter_eq_left.2 (fwdHull_subset_H t.2)

/-- **Equal trace codes give equal drivers** before the lifetime. -/
theorem cw_eq_of_traceOfCode_eq {x x' : XCode nL nR} (hx : x ∈ DetSet a xL xR ρL ρR)
    (hx' : x' ∈ DetSet a xL xR ρL ρR) (he : traceOfCode x = traceOfCode x') {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < cζ x) : cw x t = cw x' t := by
  have hζ := lifetime_eq_of_traceOfCode_eq he
  obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
  set T : ℝ := ((dyad n k : ℝ≥0) : ℝ) with hT
  have hT0 : 0 ≤ T := (dyad n k).2
  have hcont : ∀ {y : XCode nL nR}, y ∈ DetSet a xL xR ρL ρR → (dyad n k : ℝ≥0∞) < cζ y →
      ContinuousOn (fun s : ℝ => cw y s.toNNReal) (Icc 0 T) := fun hy hy' => by
    refine hy.1.1.1.1.continuousOn_w.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hy'
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2
  have hdζ' : (dyad n k : ℝ≥0∞) < cζ x' := hζ ▸ hdζ
  set Wc := Ito.clampDrv (fun s : ℝ => cw x s.toNNReal) T with hWc
  set Wc' := Ito.clampDrv (fun s : ℝ => cw x' s.toNNReal) T with hWc'
  have hWcc : Continuous Wc := Ito.continuous_clampDrv hT0 (hcont hx hdζ)
  have hWcc' : Continuous Wc' := Ito.continuous_clampDrv hT0 (hcont hx' hdζ')
  have h0 : ∀ {y : XCode nL nR}, y ∈ DetSet a xL xR ρL ρR → cw y 0 = 0 := fun hy => hy.1.1.1.2.2.1
  have hW0 : Wc 0 = 0 := by
    rw [hWc, Ito.clampDrv_eqOn ⟨le_rfl, hT0⟩]; simpa using h0 hx
  have hW0' : Wc' 0 = 0 := by
    rw [hWc', Ito.clampDrv_eqOn ⟨le_rfl, hT0⟩]; simpa using h0 hx'
  have htT : (t : ℝ) < T := by exact_mod_cast htd
  have hhull : ∀ s ∈ Icc (0 : ℝ) t, QuantumZipper.fwdHull Wc s = QuantumZipper.fwdHull Wc' s := by
    intro s hs
    have hsT : s < T := lt_of_le_of_lt hs.2 htT
    rw [fwdHull_eq_of_eqOn hs.1 hsT fun r hr => Ito.clampDrv_eqOn hr,
      fwdHull_eq_of_eqOn (W := Wc') hs.1 hsT fun r hr => Ito.clampDrv_eqOn hr]
    have hsζ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < cζ x := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) ht
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    have h := fwdHull_eq_of_traceOfCode_eq hx hx' he hsζ
    rwa [Real.coe_toNNReal _ hs.1] at h
  have heq := Sec6.eqOn_of_fwdHull_eq hWcc hWcc' hW0 hW0' t.2 hhull ⟨t.2, le_rfl⟩
  rw [hWc, hWc', Ito.clampDrv_eqOn ⟨t.2, htT.le⟩, Ito.clampDrv_eqOn ⟨t.2, htT.le⟩] at heq
  simpa using heq

theorem toNNReal_lt_of_mem_uIcc {ζ : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ}
    (hs : s ∈ uIcc (0 : ℝ) t) : (s.toNNReal : ℝ≥0∞) < ζ := by
  rw [uIcc_of_le t.coe_nonneg] at hs
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) ht

/-- **On the good set, the trace code determines the code** (`a > 0`). -/
theorem injOn_traceOfCode (ha : 0 < a) :
    InjOn (traceOfCode (nL := nL) (nR := nR)) (DetSet a xL xR ρL ρR) := by
  intro x hx x' hx' he
  have hζ := lifetime_eq_of_traceOfCode_eq he
  have hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → cw x t = cw x' t := fun t ht =>
    cw_eq_of_traceOfCode_eq hx hx' he ht
  obtain ⟨⟨⟨⟨hg, -, hp⟩, hc⟩, hfz⟩, -⟩ := hx
  obtain ⟨⟨⟨⟨hg', -, hp'⟩, hc'⟩, hfz'⟩, -⟩ := hx'
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -, hintL, hintR, hweq, hvLeq, hvReq, hnullL, hnullR, -, -, -⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, hvLw', hwvR', -, hintL', hintR', hweq', hvLeq', hvReq', hnullL', hnullR', -, -,
    -⟩ := hp'
  have mI := fun {t : ℝ≥0} (ht : (t : ℝ≥0∞) < cζ x) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) =>
    toNNReal_lt_of_mem_uIcc ht hs
  have mO := fun {t : ℝ≥0} (ht : (t : ℝ≥0∞) < cζ x) {s : ℝ} (hs : s ∈ uIoc (0 : ℝ) t) =>
    toNNReal_lt_of_mem_uIcc ht (uIoc_subset_uIcc hs)
  -- the force points
  have hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ j, cvR x j t = cvR x' j t := by
    intro t ht j
    refine eqOn_of_force_eq (w := cw x) (T := cζ x) (x₀ := xR j)
      (fun t ht => Or.inl ⟨hwvR t ht j, by rw [hw t ht]; exact hwvR' t (hζ ▸ ht) j⟩)
      (fun t ht => hintR t ht j)
      (fun t ht => (hintR' t (hζ ▸ ht) j).congr fun s hs => by
        rw [hw _ (mO ht hs)])
      (fun t ht => hvReq t ht j)
      (fun t ht => by
        rw [hvReq' t (hζ ▸ ht) j]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by
          rw [hw _ (mI ht hs)])
      (hnullR j) ?_ t ht
    have e : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧ cw x s.toNNReal = cvR x' j s.toNNReal} =
        {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x' ∧ cw x' s.toNNReal = cvR x' j s.toNNReal} := by
      ext s
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hζ ▸ h2, by rw [← hw _ h2]; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        have h2' : (s.toNNReal : ℝ≥0∞) < cζ x := hζ ▸ h2
        exact ⟨h1, h2', by rw [hw _ h2']; exact h3⟩
    rw [e]
    exact hnullR' j
  have hL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ i, cvL x i t = cvL x' i t := by
    intro t ht i
    refine eqOn_of_force_eq (w := cw x) (T := cζ x) (x₀ := xL i)
      (fun t ht => Or.inr ⟨hvLw t ht i, by rw [hw t ht]; exact hvLw' t (hζ ▸ ht) i⟩)
      (fun t ht => hintL t ht i)
      (fun t ht => (hintL' t (hζ ▸ ht) i).congr fun s hs => by
        rw [hw _ (mO ht hs)])
      (fun t ht => hvLeq t ht i)
      (fun t ht => by
        rw [hvLeq' t (hζ ▸ ht) i]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by
          rw [hw _ (mI ht hs)])
      (hnullL i) ?_ t ht
    have e : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧ cw x s.toNNReal = cvL x' i s.toNNReal} =
        {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x' ∧ cw x' s.toNNReal = cvL x' i s.toNNReal} := by
      ext s
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hζ ▸ h2, by rw [← hw _ h2]; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        have h2' : (s.toNNReal : ℝ≥0∞) < cζ x := hζ ▸ h2
        exact ⟨h1, h2', by rw [hw _ h2']; exact h3⟩
    rw [e]
    exact hnullL' i
  -- the driving path before the lifetime
  have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → cb x t = cb x' t := by
    intro t ht
    have e1 := hweq t ht
    have e2 := hweq' t (hζ ▸ ht)
    have hsL : ∀ i, ∫ s in (0 : ℝ)..t, ρL i / (cw x s.toNNReal - cvL x i s.toNNReal) =
        ∫ s in (0 : ℝ)..t, ρL i / (cw x' s.toNNReal - cvL x' i s.toNNReal) := fun i =>
      intervalIntegral.integral_congr fun s hs => by
        rw [hw _ (mI ht hs), hL _ (mI ht hs) i]
    have hsR : ∀ j, ∫ s in (0 : ℝ)..t, ρR j / (cw x s.toNNReal - cvR x j s.toNNReal) =
        ∫ s in (0 : ℝ)..t, ρR j / (cw x' s.toNNReal - cvR x' j s.toNNReal) := fun j =>
      intervalIntegral.integral_congr fun s hs => by
        rw [hw _ (mI ht hs), hR _ (mI ht hs) j]
    rw [hw t ht, Finset.sum_congr rfl fun i _ => hsL i, Finset.sum_congr rfl fun j _ => hsR j] at e1
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have : Real.sqrt a * cb x t = Real.sqrt a * cb x' t := by linarith
    exact mul_left_cancel₀ hsa.ne' this
  -- the driving code
  have hb1 : x.1 = x'.1 := by
    funext n k
    by_cases hlt : (dyad n k : ℝ≥0∞) < cζ x
    · have hN : dyad n k ≤ ((⌈dyad n k⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil _
      rw [← (hg.1 _).dec_dyad hN, ← (hg'.1 _).dec_dyad hN]
      exact hb _ hlt
    · rw [hfz n k hlt, hfz' n k (hζ ▸ hlt), ← hζ]
      by_cases h0 : cζ x = 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, ↓reduceIte]
        have hfin : cζ x ≠ ⊤ := fun h => hlt (h ▸ ENNReal.coe_lt_top)
        have hpos : 0 < (cζ x).toNNReal := ENNReal.toNNReal_pos h0 hfin
        have : (𝓝[<] (cζ x).toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
        have h1 := (hg.continuous_b.tendsto (cζ x).toNNReal).mono_left
          (nhdsWithin_le_nhds (s := Iio (cζ x).toNNReal))
        have h2 := (hg'.continuous_b.tendsto (cζ x).toNNReal).mono_left
          (nhdsWithin_le_nhds (s := Iio (cζ x).toNNReal))
        refine tendsto_nhds_unique h1 (h2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin] with s hs
        refine (hb s ?_).symm
        rw [← ENNReal.coe_toNNReal hfin]
        exact ENNReal.coe_lt_coe.2 hs
  exact code_eq hg hg' hc hc' hb1 hζ hw hL hR

end Inj

end Exist

end InteractingSLE
