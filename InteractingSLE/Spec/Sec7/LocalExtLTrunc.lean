/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHExt
import InteractingSLE.Spec.Sec7.LocalExtHKer

/-!
# Aux. lemma 54, (K-pre): the kernel at deterministic times read from truncated histories

Packet PROVE-LOCEXT-L. A two-seed history `y = (σ, (y_q)_{q ∈ ℚ≥0})` is **truncated** at a rational time `t` by
`truncH t y = (σ ∧ t, (y_{q ∧ t})_q)`; for the history `tsOf S X` of a state stopped at `S` this is `tsOf (S ∧ t) X`.

The two kernels of Aux. lemma 54 are read at a deterministic rational time `t` before the stop:

* **stopped coupling** (`IsStoppedSeedCoupling.setIntegral_cexp_trunc`): for every Borel set `D` of histories, on the
  event `A = {t < S, supp ψ ∩ K(truncH t Y) = ∅, truncH t Y ∈ D}` (`Y` the merged stopped history),
  `∫_A e^{i h(ψ)} dQ = ∫_A kerFun ψ (truncH t Y) dQ` — clause (e) at the stop `t ∧ S`;
* **reference** (`setIntegral_cexp_trunc_ref`): the same for a two-seed coupling with a good event, its history at the
  capped local stop `Ŝ` (`refRecHist`) and `A = {t < Ŝ, …}` — the frozen kernel at the stop `t ∧ Ŝ`.

## Main results

* `truncH`, `measurable_truncH`, `truncH_tsOf`;
* `IsStoppedSeedCoupling.setIntegral_cexp_trunc`, `setIntegral_cexp_trunc_ref`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling

/-! ### Truncated histories -/

/-- **The truncation of a two-seed history at a rational time `t`**: stop `σ ∧ t`, values `y_{q ∧ t}`. -/
def truncH (t : ℚ≥0) (y : TwoSeedHist) : TwoSeedHist :=
  (min y.1 ((t : ℝ≥0) : WithTop ℝ≥0), fun q => y.2 (min q t))

theorem measurable_truncH (t : ℚ≥0) : Measurable (truncH t) :=
  (measurable_fst.min measurable_const).prodMk
    (Measurable.of_eval fun q => (measurable_pi_apply (min q t)).comp measurable_snd)

theorem coe_min_nnrat (q t : ℚ≥0) : ((min q t : ℚ≥0) : ℝ≥0) = min (q : ℝ≥0) (t : ℝ≥0) := by
  rcases le_total q t with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]

/-- **The truncation of the history of a stopped state** is the history of the state stopped at `S ∧ t`. -/
theorem truncH_tsOf (t : ℚ≥0) (S : ℝ≥0) (X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    truncH t (tsOf S X) = tsOf (min S (t : ℝ≥0)) X := by
  refine Prod.ext ?_ (funext fun q => ?_)
  · simp only [truncH, tsOf, WithTop.coe_min]
  · simp only [truncH, tsOf]
    rw [coe_min_nnrat]
    congr 1
    rw [min_comm S, min_assoc]

/-- The truncation at `t` of the history of a state stopped beyond `t` is the history of the state stopped at `t`. -/
theorem truncH_tsOf_of_le {t : ℚ≥0} {S : ℝ≥0} (htS : (t : ℝ≥0) ≤ S)
    (X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)) : truncH t (tsOf S X) = tsOf (t : ℝ≥0) X := by
  rw [truncH_tsOf, min_eq_right htS]

/-! ### The stopped coupling at a truncated time -/

section Stopped

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- Before the stop, the truncated merged stopped history is the history of the merged state stopped at `t`. -/
theorem truncH_twoSeedProj_stoppedHistory {t : ℚ≥0} {ω : Ω} (htS : ((t : ℝ≥0) : WithTop ℝ≥0) < S ω) :
    truncH t (twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω)) =
      tsOf (t : ℝ≥0) (stState xL xR W VL VR ω) := by
  refine Prod.ext ?_ (funext fun q => ?_)
  · simp only [truncH, twoSeedProj, stoppedHistory, tsOf]
    exact min_eq_right htS.le
  · have hst : stopAt S ((min q t : ℚ≥0) : ℝ≥0) ω = min (q : ℝ≥0) (t : ℝ≥0) := by
      rw [coe_min_nnrat]
      unfold stopAt
      cases hS : S ω with
      | top => simp
      | coe s =>
        rw [hS] at htS
        have hts : (t : ℝ≥0) < s := WithTop.coe_lt_coe.1 htS
        simp only [WithTop.untopD_coe]
        exact min_eq_left ((min_le_right _ _).trans hts.le)
    simp only [truncH, twoSeedProj, stoppedHistory, tsOf, hst, drivingState, stState]

end Stopped

/-! ### Killed truncated histories (measurable at the truncation time) -/

section Killed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- The killed coordinates `1_{s < ζ} X_s`. -/
def killedAt (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := Coupling.killedVal ζ X

theorem killedAt_of_lt {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} {ω : Ω} (h : (s : ℝ≥0∞) < ζ ω) :
    killedAt ζ X s ω = X s ω := by
  simp only [killedAt, Coupling.killedVal, h, ↓reduceIte]

theorem measurable_killedAt {𝓓 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓓 ζ X) (s : ℝ≥0) : Measurable[𝓓 s] (killedAt ζ X s) :=
  Coupling.measurable_killedVal (hX s)

/-- **The killed state merged by `Φ` and stopped at `t`, as a two-seed history** (`𝓓_t`-measurable when the
coordinates are adapted before `ζ`; the history of `Φ ∘ X` stopped at `t` when `t < ζ`). -/
def killedTrunc (Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)) (ζ : Ω → ℝ≥0∞)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℚ≥0) (ω : Ω) :
    TwoSeedHist :=
  tsOf (t : ℝ≥0) fun s => Φ (killedAt ζ W s ω, fun i => killedAt ζ (VL i) s ω, fun j => killedAt ζ (VR j) s ω)

theorem measurable_killedTrunc {𝓓 : Filtration ℝ≥0 mΩ}
    {Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hΦ : Measurable Φ) {ζ : Ω → ℝ≥0∞}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hW : AdaptedBefore 𝓓 ζ W) (hVL : ∀ i, AdaptedBefore 𝓓 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓓 ζ (VR j))
    (t : ℚ≥0) : Measurable[𝓓 (t : ℝ≥0)] (killedTrunc Φ ζ W VL VR t) := by
  have hle : ∀ q : ℚ≥0, 𝓓 (min (q : ℝ≥0) (t : ℝ≥0)) ≤ 𝓓 (t : ℝ≥0) := fun q => 𝓓.mono (min_le_right _ _)
  have hWm : ∀ q : ℚ≥0, Measurable[𝓓 (t : ℝ≥0)] (killedAt ζ W (min (q : ℝ≥0) (t : ℝ≥0))) := fun q =>
    (measurable_killedAt hW _).mono (hle q) le_rfl
  have hVLm : ∀ q : ℚ≥0, ∀ i, Measurable[𝓓 (t : ℝ≥0)] (killedAt ζ (VL i) (min (q : ℝ≥0) (t : ℝ≥0))) :=
    fun q i => (measurable_killedAt (hVL i) _).mono (hle q) le_rfl
  have hVRm : ∀ q : ℚ≥0, ∀ j, Measurable[𝓓 (t : ℝ≥0)] (killedAt ζ (VR j) (min (q : ℝ≥0) (t : ℝ≥0))) :=
    fun q j => (measurable_killedAt (hVR j) _).mono (hle q) le_rfl
  let _ : MeasurableSpace Ω := 𝓓 (t : ℝ≥0)
  refine measurable_const.prodMk (measurable_pi_iff.2 fun q => ?_)
  exact hΦ.comp ((hWm q).prodMk ((measurable_pi_iff.2 fun i => hVLm q i).prodMk
    (measurable_pi_iff.2 fun j => hVRm q j)))

theorem killedTrunc_eq {Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)}
    {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {t : ℚ≥0} {ω : Ω}
    (htζ : ((t : ℝ≥0) : ℝ≥0∞) < ζ ω) :
    killedTrunc Φ ζ W VL VR t ω = tsOf (t : ℝ≥0) fun s => Φ (drivingState W VL VR s ω) := by
  refine Prod.ext rfl (funext fun q => ?_)
  have hlt : ((min (q : ℝ≥0) (t : ℝ≥0) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) htζ
  simp only [killedTrunc, tsOf, killedAt_of_lt hlt, drivingState]

/-- The merging map of an original state onto the two-seed state (`stState`). -/
def stMerge (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :
    ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (p.1, fun _ => seedVal xL p.2.1 p.1, fun _ => seedVal xR p.2.2 p.1)

theorem measurable_stMerge (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Measurable (stMerge xL xR) :=
  measurable_fst.prodMk ((measurable_pi_iff.2 fun _ =>
      (measurable_seedVal xL).comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
    (measurable_pi_iff.2 fun _ =>
      (measurable_seedVal xR).comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)))

open Classical in
/-- The normalizing map of a two-seed state (`refState`: empty seed sides read the driver). -/
def refMerge (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (p : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (p.1, fun _ => if ∃ i, xL i = 0 then p.2.1 0 else p.1, fun _ => if ∃ j, xR j = 0 then p.2.2 0 else p.1)

theorem measurable_refMerge (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Measurable (refMerge xL xR) := by
  classical
  refine measurable_fst.prodMk ((measurable_pi_iff.2 fun _ => ?_).prodMk (measurable_pi_iff.2 fun _ => ?_))
  · by_cases h : ∃ i, xL i = 0
    · simp only [h, ↓reduceIte]
      exact (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
    · simp only [h, ↓reduceIte]
      exact measurable_fst
  · by_cases h : ∃ j, xR j = 0
    · simp only [h, ↓reduceIte]
      exact (measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd)
    · simp only [h, ↓reduceIte]
      exact measurable_fst

end Killed


/-! ### Stopped σ-algebras at `t ∧ S` -/

section StopMin

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓓 : Filtration ℝ≥0 mΩ} {S : Ω → WithTop ℝ≥0}

/-- **An event of `𝓓_c` inside `{c < S}` is an event of the stopped σ-algebra at `c ∧ S`.** -/
theorem measurableSet_stopping_min_of_subset_lt {c : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[𝓓 c] A) (hAS : ∀ ω ∈ A, (c : WithTop ℝ≥0) < S ω)
    (hτ : IsStoppingTime 𝓓 fun ω => min (c : WithTop ℝ≥0) (S ω)) :
    MeasurableSet[hτ.measurableSpace] A := by
  refine ⟨le_iSup (fun t => 𝓓 t) c A hA, fun i => ?_⟩
  by_cases hci : c ≤ i
  · have he : A ∩ {ω | min (c : WithTop ℝ≥0) (S ω) ≤ i} = A := by
      refine inter_eq_left.2 fun ω _ => ?_
      exact (min_le_left _ _).trans (WithTop.coe_le_coe.2 hci)
    rw [he]
    exact 𝓓.mono hci A hA
  · have he : A ∩ {ω | min (c : WithTop ℝ≥0) (S ω) ≤ i} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hω
      rw [min_eq_left (hAS ω hω).le]
      exact WithTop.coe_lt_coe.2 (not_le.1 hci)
    rw [he]
    exact @MeasurableSet.empty Ω (𝓓 i)

theorem measurableSet_lt_stop (hS : IsStoppingTime 𝓓 S) (c : ℝ≥0) :
    MeasurableSet[𝓓 c] {ω | (c : WithTop ℝ≥0) < S ω} := by
  have e : {ω | (c : WithTop ℝ≥0) < S ω} = {ω | S ω ≤ c}ᶜ := by
    ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  rw [e]
  exact (hS c).compl

end StopMin

/-! ### The kernel of the stopped coupling at a truncated time -/

section StoppedKernel

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- The merged stopped history of a stopped coupling (raw form). -/
def stRaw (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0) (ω : Ω) : TwoSeedHist :=
  twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω)

/-- **Clause (e) at a truncated time, read from the truncated history.** For a stopped seed coupling, a rational `t`
and a Borel set `D` of histories whose hulls avoid `supp ψ`, on `A = {t < S, truncH t Y ∈ D}` (`Y` the merged stopped
history), `∫_A e^{i h(ψ)} dQ = ∫_A kerFun ψ (truncH t Y) dQ` (the kernel at the stop `t ∧ S`). -/
theorem IsStoppedSeedCoupling.setIntegral_cexp_trunc [IsProbabilityMeasure Q]
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) (t : ℚ≥0) {D : Set TwoSeedHist}
    (hD : MeasurableSet D) (ψ : TestOn upperHalfPlaneOpens)
    (hDψ : ∀ y ∈ D, Disjoint (tsupport ψ) (tsHull y)) :
    MeasurableSet {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t (stRaw xL xR W VL VR S ω) ∈ D} ∧
      ∫ ω in {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t (stRaw xL xR W VL VR S ω) ∈ D},
          Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂Q =
        ∫ ω in {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t (stRaw xL xR W VL VR S ω) ∈ D},
          kerFun κ (seedSumL xL ρL) (seedSumR xR ρR) ψ (truncH t (stRaw xL xR W VL VR S ω)) ∂Q := by
  classical
  obtain ⟨𝓓, hS, -, hb, hWa, hVLa, hVRa, hhm, -, he⟩ := hc
  set A : Set Ω := {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t (stRaw xL xR W VL VR S ω) ∈ D} with hAdef
  have hAeq : A = {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω} ∩
      killedTrunc (stMerge xL xR) (fun ω => (S ω : ℝ≥0∞)) W VL VR t ⁻¹' D := by
    ext ω
    simp only [hAdef, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    refine and_congr_right fun htS => ?_
    rw [killedTrunc_eq (show ((t : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) from htS), stRaw,
      truncH_twoSeedProj_stoppedHistory htS]
    rfl
  have hAt : MeasurableSet[𝓓 (t : ℝ≥0)] A := by
    rw [hAeq]
    exact (measurableSet_lt_stop hS _).inter (measurable_killedTrunc (measurable_stMerge xL xR) hWa hVLa hVRa t hD)
  have hτ : IsStoppingTime 𝓓 fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (S ω) := (isStoppingTime_const 𝓓 _).min hS
  have hAτ : MeasurableSet[hτ.measurableSpace] A :=
    measurableSet_stopping_min_of_subset_lt hAt (fun ω hω => hω.1) hτ
  have hAm : MeasurableSet A := hτ.measurableSpace_le A hAτ
  refine ⟨hAm, ?_⟩
  set τ : Ω → WithTop ℝ≥0 := fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (S ω) with hτdef
  have hτt : ∀ ω, ((t : ℝ≥0) : WithTop ℝ≥0) < S ω → ((τ ω).untopD 0 : ℝ≥0) = t := fun ω h => by
    simp only [hτdef, min_eq_left h.le, WithTop.untopD_coe]
  set ρ'L : Fin 1 → ℝ := fun _ => seedSumL xL ρL with hρ'L
  set ρ'R : Fin 1 → ℝ := fun _ => seedSumR xR ρR with hρ'R
  set u : Ω → ℂ → ℝ := fun ω => if ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧
      ContinuousOn (stState xL xR W VL VR ω) (Iic (t : ℝ≥0)) then
      histHarm κ ρ'L ρ'R (tsHist (tsOf (t : ℝ≥0) (stState xL xR W VL VR ω))) else
    Classical.choose (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R
      (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω)) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρ'L ρ'R (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω)) (u ω) := by
    intro ω
    by_cases hω : ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ ContinuousOn (stState xL xR W VL VR ω) (Iic (t : ℝ≥0))
    · obtain ⟨htS, hX⟩ := hω
      set γ := tsHist (tsOf (t : ℝ≥0) (stState xL xR W VL VR ω)) with hγ
      have hspec := histHarm_spec κ ρ'L ρ'R γ
      have hstop : γ.1.toNNReal = (t : ℝ≥0) := histStop_tsHist_tsOf
      have hpL : (fun i => histVL γ i - histPath γ γ.1.toNNReal) = fun _ : Fin 1 => seedPosL xL W VL τ ω := by
        funext i
        rw [hγ, histVL_tsHist_tsOf hX, ← hγ, hstop, hγ, histPath_tsHist_tsOf hX, min_self]
        simp only [stState, seedPosL]
        rw [← seedVal_sub]
        unfold cposL
        rw [hτt ω htS]
      have hpR : (fun i => histVR γ i - histPath γ γ.1.toNNReal) = fun _ : Fin 1 => seedPosR xR W VR τ ω := by
        funext i
        rw [hγ, histVR_tsHist_tsOf hX, ← hγ, hstop, hγ, histPath_tsHist_tsOf hX, min_self]
        simp only [stState, seedPosR]
        rw [← seedVal_sub]
        unfold cposR
        rw [hτt ω htS]
      rw [hpL, hpR] at hspec
      simp only [hudef, htS, hX, and_self, ↓reduceIte]
      exact hspec
    · simp only [hudef, hω, ↓reduceIte]
      exact Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R _ _)
  have he' := (he τ hτ (ae_of_all _ fun ω => min_le_right _ _)).2 u hu ψ
  have hfi : Integrable (fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ))) Q :=
    Integrable.of_bound (Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp hhm)))).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  rw [← setIntegral_condExp hτ.measurableSpace_le hfi hAτ]
  refine setIntegral_congr_ae hAm ?_
  filter_upwards [he', hb] with ω h1 hbω hωA
  obtain ⟨ζ₀, hSζ, -, hcont⟩ := hbω
  have htS : ((t : ℝ≥0) : WithTop ℝ≥0) < S ω := hωA.1
  have htζ : ((t : ℝ≥0) : ℝ≥0∞) < ζ₀ := lt_trans (show ((t : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) from htS) hSζ
  have hX : ContinuousOn (stState xL xR W VL VR ω) (Iic (t : ℝ≥0)) :=
    continuousOn_stState (hcont.mono fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) htζ)
  have hY : truncH t (stRaw xL xR W VL VR S ω) = tsOf (t : ℝ≥0) (stState xL xR W VL VR ω) :=
    truncH_twoSeedProj_stoppedHistory htS
  have hdis : Disjoint (tsupport ψ) (tsHull (tsOf (t : ℝ≥0) (stState xL xR W VL VR ω))) :=
    hDψ _ (hY ▸ hωA.2)
  have hWc : ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ₀} := continuous_fst.comp_continuousOn hcont
  have hsub := fwdHull_subset_tsHull_tsOf hX htζ hWc (fun _ _ => rfl)
  have hK : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
    rw [hτt ω htS]
    exact hdis.mono_right hsub
  rw [h1 hK, hY, kerFun_eq κ _ _ (isContHist_tsHist_tsOf hX) hdis,
    histCharFun_tsOf_eq κ _ _ hX (w := fun s => W s ω) (fun _ _ => rfl) ψ, hτt ω htS]
  have huω : u ω = histHarm κ ρ'L ρ'R (tsHist (tsOf (t : ℝ≥0) (stState xL xR W VL VR ω))) := by
    simp only [hudef, htS, hX, and_self, ↓reduceIte]
  rw [huω]

end StoppedKernel

/-! ### The kernel of the reference at a truncated time -/

section RefKernel

variable {κ rL rR r : ℝ} {nL nR : ℕ} {Ωr : Type*} {mΩr : MeasurableSpace Ωr} {Pr : Measure Ωr}
  {𝓕r : Filtration ℝ≥0 mΩr} {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ}
  {ζr : Ωr → ℝ≥0∞} {hr' : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}

theorem lt_zeta_of_lt_capStop {t : ℝ≥0} {ω : Ωr} (htS : (t : WithTop ℝ≥0) < capStop r Gr ζr Wr ω) :
    (t : ℝ≥0∞) < ζr ω :=
  lt_of_lt_of_le htS (capStop_le r ω)

/-- Before the capped local stop, the truncated reference history is the history of the normalized state stopped
at `t`. -/
theorem truncH_refRecHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {t : ℚ≥0} {ω : Ωr}
    (htS : ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω) :
    truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) = tsOf (t : ℝ≥0) (refState xL xR Wr VLr VRr ω) := by
  classical
  refine Prod.ext ?_ (funext fun q => ?_)
  · simp only [truncH, refRecHist, seedProj, stoppedHistory, tsOf]
    exact min_eq_right htS.le
  · have hst : stopAt (capStop r Gr ζr Wr) ((min q t : ℚ≥0) : ℝ≥0) ω = min (q : ℝ≥0) (t : ℝ≥0) := by
      rw [coe_min_nnrat]
      unfold stopAt
      cases hS : capStop r Gr ζr Wr ω with
      | top => simp
      | coe s =>
        rw [hS] at htS
        have hts : (t : ℝ≥0) < s := WithTop.coe_lt_coe.1 htS
        simp only [WithTop.untopD_coe]
        exact min_eq_left ((min_le_right _ _).trans hts.le)
    have hlt : ((min (q : ℝ≥0) (t : ℝ≥0) : ℝ≥0) : ℝ≥0∞) < ζr ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) (lt_zeta_of_lt_capStop htS)
    simp only [truncH, refRecHist, seedProj, stoppedHistory, tsOf, hst, completedState, hlt, ↓reduceIte,
      drivingState, refState]

/-- **The frozen kernel of a two-seed coupling at a truncated time, read from the truncated history.** On
`A = {t < Ŝ, truncH t Ŷ ∈ D}` (`Ŝ` the capped local stop, `Ŷ` the history there, empty seed sides normalized, `D` a
Borel set of histories whose hulls avoid `supp ψ`), `∫_A e^{i ĥ(ψ)} dP̂ = ∫_A kerFun ψ (truncH t Ŷ) dP̂`. -/
theorem setIntegral_cexp_trunc_ref [IsProbabilityMeasure Pr] (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (hL : -2 < rL) (hR : -2 < rR) (hr : 0 < r)
    (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω)
    (hrL : (¬ ∃ i, xL i = 0) → rL = 0) (hrR : (¬ ∃ j, xR j = 0) → rR = 0)
    (t : ℚ≥0) {D : Set TwoSeedHist} (hD : MeasurableSet D) (ψ : TestOn upperHalfPlaneOpens)
    (hDψ : ∀ y ∈ D, Disjoint (tsupport ψ) (tsHull y)) :
    MeasurableSet {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
        truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ D} ∧
      ∫ ω in {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
          truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ D}, Complex.exp (Complex.I * (hr' ω ψ : ℂ)) ∂Pr =
        ∫ ω in {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
          truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ D},
          kerFun κ rL rR ψ (truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω)) ∂Pr := by
  classical
  obtain ⟨hXr, hker⟩ := hC.2.2.2
  have hŜ := isStoppingTime_capStop hXr hGm hG0 hG r
  have hdl : killedDrivingFiltration hXr ≤ drivingFiltration Pr hXr := Ito.le_usualAugmentation _ Pr
  have hWa := Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_W hXr)
  have hVLa := fun i => Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VL hXr i)
  have hVRa := fun j => Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VR hXr j)
  set A : Set Ωr := {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
    truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ D} with hAdef
  have hAeq : A = {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω} ∩
      killedTrunc (refMerge xL xR) ζr Wr VLr VRr t ⁻¹' D := by
    ext ω
    simp only [hAdef, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    refine and_congr_right fun htS => ?_
    rw [killedTrunc_eq (lt_zeta_of_lt_capStop htS), truncH_refRecHist xL xR htS]
    rfl
  have hAt : MeasurableSet[drivingFiltration Pr hXr (t : ℝ≥0)] A := by
    rw [hAeq]
    exact (measurableSet_lt_stop hŜ _).inter
      (measurable_killedTrunc (measurable_refMerge xL xR) hWa hVLa hVRa t hD)
  have hτ : IsStoppingTime (drivingFiltration Pr hXr) fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (capStop r Gr ζr Wr ω) :=
    (isStoppingTime_const _ _).min hŜ
  have hAτ : MeasurableSet[hτ.measurableSpace] A :=
    measurableSet_stopping_min_of_subset_lt hAt (fun ω hω => hω.1) hτ
  have hAm : MeasurableSet A := hτ.measurableSpace_le A hAτ
  refine ⟨hAm, ?_⟩
  set τ : Ωr → WithTop ℝ≥0 := fun ω => min ((t : ℝ≥0) : WithTop ℝ≥0) (capStop r Gr ζr Wr ω) with hτdef
  have hτt : ∀ ω, ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω → ((τ ω).untopD 0 : ℝ≥0) = t := fun ω h => by
    simp only [hτdef, min_eq_left h.le, WithTop.untopD_coe]
  have hGP : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
  have hτζ : ∀ᵐ ω ∂Pr, ((τ ω : WithTop ℝ≥0) : ℝ≥0∞) < ζr ω := by
    filter_upwards [hGP] with ω hω
    obtain ⟨hS, hSζ'⟩ := capStop_ref hL hR hr hG hω
    refine lt_of_le_of_lt (show ((τ ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ (capStop r Gr ζr Wr ω : ℝ≥0∞) from min_le_right _ _) ?_
    rw [hS]
    exact hSζ'
  set ρ'L : Fin 1 → ℝ := fun _ => rL with hρ'L
  set ρ'R : Fin 1 → ℝ := fun _ => rR with hρ'R
  set u : Ωr → ℂ → ℝ := fun ω => if ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧ ω ∈ Gr then
      histHarm κ ρ'L ρ'R (tsHist (tsOf (t : ℝ≥0) (refState xL xR Wr VLr VRr ω))) else
    Classical.choose (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R
      (fun i => VLr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω)
      (fun i => VRr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω)) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρ'L ρ'R (fun i => VLr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω)
        (fun i => VRr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VLr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω)
        (fun i => VRr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω)) (u ω) := by
    intro ω
    by_cases hω : ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧ ω ∈ Gr
    · obtain ⟨htS, hωG⟩ := hω
      have hX := continuousOn_refState xL xR (hG ω hωG) (lt_zeta_of_lt_capStop htS)
      set γ := tsHist (tsOf (t : ℝ≥0) (refState xL xR Wr VLr VRr ω)) with hγ
      have hspec := histHarm_spec κ ρ'L ρ'R γ
      have hstop : γ.1.toNNReal = (t : ℝ≥0) := histStop_tsHist_tsOf
      have hpL : (fun i => histVL γ i - histPath γ γ.1.toNNReal) =
          fun _ : Fin 1 => if ∃ i, xL i = 0 then VLr 0 (t : ℝ≥0) ω - Wr (t : ℝ≥0) ω else 0 := by
        funext i
        rw [hγ, histVL_tsHist_tsOf hX, ← hγ, hstop, hγ, histPath_tsHist_tsOf hX, min_self]
        simp only [refState]
        split_ifs <;> first | rfl | exact sub_self _
      have hpR : (fun i => histVR γ i - histPath γ γ.1.toNNReal) =
          fun _ : Fin 1 => if ∃ j, xR j = 0 then VRr 0 (t : ℝ≥0) ω - Wr (t : ℝ≥0) ω else 0 := by
        funext i
        rw [hγ, histVR_tsHist_tsOf hX, ← hγ, hstop, hγ, histPath_tsHist_tsOf hX, min_self]
        simp only [refState]
        split_ifs <;> first | rfl | exact sub_self _
      rw [hpL, hpR] at hspec
      have h' := isBoundedHarmonicExtension_of_normalized hrL hrR hspec
      have eL : (fun i : Fin 1 => VLr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω) =
          fun _ => VLr 0 (t : ℝ≥0) ω - Wr (t : ℝ≥0) ω := by
        funext i; rw [Subsingleton.elim i 0, hτt ω htS]
      have eR : (fun i : Fin 1 => VRr i ((τ ω).untopD 0) ω - Wr ((τ ω).untopD 0) ω) =
          fun _ => VRr 0 (t : ℝ≥0) ω - Wr (t : ℝ≥0) ω := by
        funext i; rw [Subsingleton.elim i 0, hτt ω htS]
      simp only [hudef, htS, hωG, and_self, ↓reduceIte]
      rw [eL, eR]
      exact h'
    · simp only [hudef, hω, ↓reduceIte]
      exact Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρ'L ρ'R _ _)
  have hcl := (hker τ hτ hτζ).2 u hu ψ
  have hfi : Integrable (fun ω => Complex.exp (Complex.I * (hr' ω ψ : ℂ))) Pr :=
    Integrable.of_bound (Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp hC.2.1)))).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  rw [← setIntegral_condExp hτ.measurableSpace_le hfi hAτ]
  refine setIntegral_congr_ae hAm ?_
  filter_upwards [hcl, hGP] with ω h1 hω hωA
  have htS : ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω := hωA.1
  have htζ := lt_zeta_of_lt_capStop htS
  have hX := continuousOn_refState xL xR (hG ω hω) htζ
  have hY := truncH_refRecHist (VLr := VLr) (VRr := VRr) xL xR htS
  have hdis : Disjoint (tsupport ψ) (tsHull (tsOf (t : ℝ≥0) (refState xL xR Wr VLr VRr ω))) :=
    hDψ _ (hY ▸ hωA.2)
  have hsub := fwdHull_subset_tsHull_tsOf hX htζ (hG ω hω).1.2.2.2.1 (w := fun s => Wr s ω) (fun _ _ => rfl)
  have hK : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => Wr s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
    rw [hτt ω htS]
    exact hdis.mono_right hsub
  rw [h1 hK, hY, kerFun_eq κ _ _ (isContHist_tsHist_tsOf hX) hdis,
    histCharFun_tsOf_eq κ _ _ hX (w := fun s => Wr s ω) (fun _ _ => rfl) ψ, hτt ω htS]
  have huω : u ω = histHarm κ ρ'L ρ'R (tsHist (tsOf (t : ℝ≥0) (refState xL xR Wr VLr VRr ω))) := by
    simp only [hudef, htS, hω, and_self, ↓reduceIte]
  rw [huω]

end RefKernel

end LocalExt

end InteractingSLE
