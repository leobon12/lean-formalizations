/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCond
import InteractingSLE.WangWu.ReverseContactMartFilt2Glue

/-!
# The cross-conditioning law at general `κ`: marked locality of the revealed union (Astra's E.2)

Packet PROVE-GLUECOND5. Astra's follow-up note, Part E (R53; `source/external/AstraIG1/ig1_followup_a_e_audited.txt`
lines 1007–1313), at general `κ`, on the glued space of `Prop411Q.CfGlueAE`: the flow line `η` of `h` (an optional
hull coupling on `Ω`) and the counterflow `η′ = R ∘ β` of `h − π/2 χ` (a centred counterflow coupling on `Ω₂`, read
through a regular conditional law `k` of its history), conditionally independent given `h`.

E.2 (lines 1083–1124): "For each of the two lines take its own first-entry history … the conditional kernel of each
such complete stopped record, given `h`, depends only on the orthogonal complement projection … Conditional
independence of the complete two lines given `h` implies that these two own first-entry records have a product
conditional kernel … The finite-cover Gaussian-kernel proof of Proposition 3.7 … therefore applies with the complete
stopped records as marks."

* **The counterflow's own stopped record** (`isHistoryAvoidanceLocal_cfHullQ`): on `Ω₂`, the reflected counterflow
  hull `G = R(K′_t)` read from the counterflow history satisfies Aux. lemma 18's history-marked avoidance criterion for
  the centred field, with the counterflow history stopped at `t` as marks. The counterflow coupling is an optional hull
  coupling at `16/κ` of the transported field `h′` (`h₂ = R_* h′ + (a + k · lift)`), so this is the reflected frozen
  clause (`WangWu.isHistoryAvoidanceLocal_reflect_hull`) with the harmonic shift absorbed; the history without force
  coordinates is known to the frozen driving filtration of the `16/κ` word (`drivingFiltration_elim0_le`).
* **The flow line's own stopped record** (`isHistoryAvoidanceLocal_hullAt_flow`): on `Ω`, the flow hull `A = K_q`
  read from the flow history, with the flow history stopped at `q` as marks (`isHistoryAvoidanceLocal_hull`).
* **The revealed union on the glued space** (`isHistoryAvoidanceLocal_cfGlue`, Proposition 3.7 with both stopped
  records retained): `A ∪ G` satisfies the history-marked criterion for the centred field `h − 𝔥₀` and the marks
  `σ(flow history stopped at q) ∨ σ(counterflow history stopped at t)` — both directions of the cross-conditioning
  (flow line given the counterflow prefix, counterflow given the flow prefix) at once.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref GlueCond WholeField
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### The history without force coordinates is known to the driving filtration of the word -/

section Elim0

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

omit mΩ in
/-- The killed driving σ-algebra of the driver alone is coarser than that of the driver with its force points. -/
theorem killedDrivingSigma_elim0_le (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) :
    killedDrivingSigma W (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) ζ t ≤
      killedDrivingSigma W VL VR ζ t := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro E ⟨r, hr, A, hA, rfl⟩
  refine MeasurableSpace.measurableSet_generateFrom ⟨r, hr,
    (fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => (x.1, (Fin.elim0 : Fin 0 → ℝ), (Fin.elim0 : Fin 0 → ℝ))) ⁻¹' A,
    (measurable_fst.prodMk measurable_const) hA, ?_⟩
  ext ω
  simp only [mem_ofPred_eq, mem_preimage]
  have e : ∀ f : Fin 0 → ℝ, f = Fin.elim0 := fun f => Subsingleton.elim _ _
  rw [e (fun i => (Fin.elim0 i : ℝ≥0 → Ω → ℝ) r ω)]

/-- **The driving filtration of the driver alone is coarser than that of the word.** -/
theorem drivingFiltration_elim0_le (P : Measure Ω) {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) :
    drivingFiltration P (isMeasurableKilledDriving_elim0 hX) ≤ drivingFiltration P hX :=
  Ito.usualAugmentation_mono (fun t => killedDrivingSigma_elim0_le W VL VR ζ t) P

/-- The counterflow history stopped at `t` is known at time `t` of the driving filtration of the word. -/
theorem comap_cfHistory_stopSigma_le (P : Measure Ω) {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    MeasurableSpace.comap (cfHistory W ζ) (stopSigma t) ≤ drivingFiltration P hX t :=
  (comap_stopSigma_le (P := P) (isMeasurableKilledDriving_elim0 hX) t).trans
    (drivingFiltration_elim0_le P hX t)

end Elim0

/-! ### The counterflow's own stopped record (on `Ω₂`) -/

section Omega2

variable {κ : ℝ} {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- The harmonic distribution absorbed by the centring of the counterflow field: `𝔥₀ − (a + k · lift) − π/2 χ`. -/
def cfShiftDist (κ : ℝ) (u₀ : ℂ → ℝ) : DistOn upperHalfPlaneOpens :=
  smoothDist upperHalfPlaneOpens u₀ - smoothDist upperHalfPlaneOpens (retShift (-(π * chiC κ)) (chiC (16 / κ))) -
    smoothDist upperHalfPlaneOpens (fun _ => π / 2 * chiC κ)

theorem isHarmonicDistOn_cfShiftDist (κ : ℝ) {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    IsHarmonicDistOn (cfShiftDist κ u₀) H :=
  LocalSets.IsHarmonicDistOn.sub' QuantumZipper.isOpen_H
    (LocalSets.IsHarmonicDistOn.sub' QuantumZipper.isOpen_H (isHarmonicDistOn_smoothDist hu₀)
      (isHarmonicDistOn_smoothDist (harmonicOnNhd_retShift _ _)))
    (isHarmonicDistOn_smoothDist fun _ _ => InnerProductSpace.harmonicAt_const _)

/-- The centred counterflow field is the reflected `16/κ` field minus `cfShiftDist`. -/
theorem cenT_eq_reflectField_sub (κ : ℝ) (u₀ : ℂ → ℝ) {f f' : DistOn upperHalfPlaneOpens}
    (htr : IsChartTransport infinitySourceChart (-1) (-(π * chiC κ)) (chiC (16 / κ)) f f') :
    cenT κ u₀ f = reflectField f' - cfShiftDist κ u₀ := by
  rw [cenT_eq_add_sub, Theorem14.GW2Cone.eq_returnField_of_isChartTransport htr, returnField_eq_reflectField_add,
    cfShiftDist]
  abel

/-- **E.2, the counterflow's own stopped record** (Aux. lemmas 18–19 for the counterflow, chart `Q`). For a centred
counterflow coupling (`κ > 0`) of almost surely infinite lifetime with a continuous driver from `0`, the reflected
counterflow hull `R(K′_t)` read from the counterflow history satisfies the history-marked avoidance criterion for the
centred field `cenT κ u₀ h₂` (any `u₀` harmonic on `ℍ`) and the marks `σ(counterflow history stopped at t)`. -/
theorem isHistoryAvoidanceLocal_cfHullQ (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hκ : 0 < κ)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (t : ℝ≥0) :
    IsHistoryAvoidanceLocal (MeasurableSpace.comap (cfHistory W₂ ζ₂) (stopSigma t))
      (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) (fun ω => cenT κ u₀ (h₂ ω)) P₂ := by
  have hX₀ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  obtain ⟨b', J', h', -, htr, hfl⟩ := hcf
  obtain ⟨h'', 𝓕, VL, VR, B, htac, hC⟩ := hfl
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  have hX := hC.2.2.2.1
  have hτ := isStoppingTime_const (drivingFiltration P₂ hX) t
  have hτζ : ∀ᵐ ω ∂P₂, (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by
    filter_upwards [hreg₂] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hloc := isHistoryAvoidanceLocal_reflect_hull hC (by positivity) (isHarmonicDistOn_cfShiftDist κ hu₀) hX hτ
    hτζ (A := fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) ((measurable_cfHullQ t).comp (measurable_cfHistory hX₀))
    (by
      filter_upwards [hreg₂] with ω hω
      rw [cfHullQ, hullAt_cfHistory hω.1 hω.2.1 hω.2.2, WithTop.untopD_coe])
  have hf : (fun ω => cenT κ u₀ (h₂ ω)) = fun ω => reflectField (h'' ω) - cfShiftDist κ u₀ :=
    funext fun ω => cenT_eq_reflectField_sub κ u₀ (htr ω)
  rw [hf]
  exact IsHistoryAvoidanceLocal.mono_marks hloc ((comap_cfHistory_stopSigma_le P₂ hX t).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)

end Omega2

/-! ### The flow line's own stopped record (on `Ω`) -/

section Omega

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- **E.2, the flow line's own stopped record**: for an optional hull coupling (`κ > 0`) of almost surely infinite
lifetime, the flow hull `K_q` read from the flow history satisfies the history-marked avoidance criterion for the
centred field `h − 𝔥₀ = cenT κ u₀ (h − π/2 χ)` and the marks `σ(flow history stopped at q)`. -/
theorem isHistoryAvoidanceLocal_hullAt_flow (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q : ℝ≥0) :
    IsHistoryAvoidanceLocal (MeasurableSpace.comap (killedHistory W VL VR ζ) (stopSigma q))
      (fun ω => hullAt q (killedHistory W VL VR ζ ω)) (fun ω => cenT κ u₀ (cfField κ (h ω))) P := by
  have hX := hC.2.2.2.1
  have hτ := isStoppingTime_const (drivingFiltration P hX) q
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hτ hτζ
    (A := fun ω => hullAt q (killedHistory W VL VR ζ ω)) ((measurable_hullAt q).comp (measurable_killedHistory hX))
    (by
      filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
      rw [WithTop.untopD_coe]
      exact Aux50Hit.regHull_stopHistory_cstop hg q)
  have hf : centredField h u₀ = fun ω => cenT κ u₀ (cfField κ (h ω)) :=
    funext fun ω => (cenT_cfField κ u₀ (h ω)).symm
  rw [hf] at hloc
  exact IsHistoryAvoidanceLocal.mono_marks hloc ((comap_stopSigma_le (P := P) hX q).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)

end Omega

/-! ### The revealed union on the glued space (Proposition 3.7 with both stopped records) -/

section Glue

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- **The marks of the glued space**: the flow history stopped at `q` and the counterflow history stopped at `t`. -/
@[instance_reducible]
def cfGlueMarks (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (q t : ℝ≥0) : MeasurableSpace (Ω × HistorySpace 0 0) :=
  MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1) (stopSigma q) ⊔
    MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => p.2) (stopSigma t)

omit [IsProbabilityMeasure P] in
theorem cfGlueMarks_le (q t : ℝ≥0) (hX : IsMeasurableKilledDriving W VL VR ζ) :
    cfGlueMarks W VL VR ζ q t ≤ (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) := by
  refine sup_le ?_ ?_
  · rw [show (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1) =
      killedHistory W VL VR ζ ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact (MeasurableSpace.comap_mono ((MeasurableSpace.comap_mono (stopSigma_le _)).trans
      (measurable_killedHistory hX).comap_le)).trans measurable_fst.comap_le
  · exact (MeasurableSpace.comap_mono (stopSigma_le _)).trans measurable_snd.comap_le

omit [IsProbabilityMeasure P] in
/-- The centring does not change the σ-algebra of the field on the glued space. -/
theorem comap_cenT_glue (κ : ℝ) (u₀ : ℂ → ℝ) (X : Ω → DistOn upperHalfPlaneOpens) :
    MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (X p.1)) inferInstance =
      MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => X p.1) inferInstance := by
  refine le_antisymm ?_ ?_
  · change MeasurableSpace.comap (cenT κ u₀ ∘ fun p : Ω × HistorySpace 0 0 => X p.1) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_cenT κ u₀).comap_le
  · calc MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => X p.1) inferInstance
        = MeasurableSpace.comap (cenT' κ u₀ ∘ fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (X p.1))
            inferInstance := by
          congr 1
          funext p
          exact (cenT'_cenT κ u₀ (X p.1)).symm
      _ ≤ _ := by
          rw [← MeasurableSpace.comap_comp]
          exact MeasurableSpace.comap_mono (measurable_cenT' κ u₀).comap_le

/-- **E.2 on the glued space: the revealed union with both own stopped records retained** (Proposition 3.7 with Aux.
lemma 18's marks; Astra's (E.3)). On the glued space `P ⊗ k(h − π/2 χ)` of an optional hull coupling `(h, W, …)` of
infinite lifetime (`κ > 0`) and a centred counterflow coupling `(h₂, W₂)` of `h − π/2 χ` with a continuous driver
from `0` and infinite lifetime, conditionally independent given `h`: for all times `q, t ≥ 0`, the union of the flow
hull `K_q` and the reflected counterflow hull `R(K′_t)` (both read from the histories) satisfies the history-marked
avoidance criterion for the centred field `h − 𝔥₀` and the marks `σ(flow history stopped at q) ∨ σ(counterflow history
stopped at t)`. This is the field side of both cross-conditionings (the counterflow given the flow prefix, Lemma 4.7;
the flow line given the counterflow prefix, Proposition 4.9). -/
theorem isHistoryAvoidanceLocal_cfGlue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0) :
    IsHistoryAvoidanceLocal (cfGlueMarks W VL VR ζ q t)
      (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  have hX := hC.2.2.2.1
  have hX₀ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hh₂m := CfRegQ.measurable_of_isCenteredCounterflowDriver hcf
  have hXm₀ : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hXm : Measurable fun ω => cenT κ u₀ (cfField κ (h ω)) := (measurable_cenT κ u₀).comp hXm₀
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hY₂m : Measurable (cfHistory W₂ ζ₂) := measurable_cfHistory hX₀
  have hX₂m : Measurable fun ω => cenT κ u₀ (h₂ ω) := (measurable_cenT κ u₀).comp hh₂m
  -- the flow line's record, transported along `fst`
  have hlaw₁ : μ.map (fun p : Ω × HistorySpace 0 0 =>
      (cenT κ u₀ (cfField κ (h p.1)), killedHistory W VL VR ζ p.1)) =
      P.map (fun ω => (cenT κ u₀ (cfField κ (h ω)), killedHistory W VL VR ζ ω)) := by
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenT κ u₀ (cfField κ (h p.1)), killedHistory W VL VR ζ p.1)) =
        (fun ω => (cenT κ u₀ (cfField κ (h ω)), killedHistory W VL VR ζ ω)) ∘ Prod.fst from rfl,
      ← Measure.map_map (hXm.prodMk hYm) measurable_fst, hμ, glueMeasure_fst k hXm₀]
  have hA₁ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma q) hXm hYm (hXm.comp measurable_fst)
    (hYm.comp measurable_fst) hlaw₁ (measurable_hullAt q) (stopSigma_le _)
    (isHistoryAvoidanceLocal_hullAt_flow hC hκ hζ hu₀ q)
  -- the counterflow's record, transported along the law of `(h − π/2 χ, history)`
  have hlaw₂ : μ.map (fun p : Ω × HistorySpace 0 0 => (cenT κ u₀ (cfField κ (h p.1)), p.2)) =
      P₂.map (fun ω => (cenT κ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) := by
    have hT : Measurable fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenT κ u₀ r.1, r.2) :=
      ((measurable_cenT κ u₀).comp measurable_fst).prodMk measurable_snd
    have hpair : Measurable fun p : Ω × HistorySpace 0 0 => (cfField κ (h p.1), p.2) :=
      (hXm₀.comp measurable_fst).prodMk measurable_snd
    have hpair₂ : Measurable fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) := hh₂m.prodMk hY₂m
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenT κ u₀ (cfField κ (h p.1)), p.2)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenT κ u₀ r.1, r.2)) ∘
          fun p => (cfField κ (h p.1), p.2) from rfl,
      show (fun ω => (cenT κ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenT κ u₀ r.1, r.2)) ∘
          fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) from rfl,
      ← Measure.map_map hT hpair, ← Measure.map_map hT hpair₂, hμ, glueMeasure_map_pair hXm₀ k, hlaw, hk]
  have hA₂ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma t) hX₂m hY₂m (hXm.comp measurable_fst)
    measurable_snd hlaw₂ (measurable_cfHullQ t) (stopSigma_le _)
    (isHistoryAvoidanceLocal_cfHullQ hcf hκ hreg₂ hu₀.1 t)
  -- the union
  have hci := condIndepEv_glue_fst (μ := P) k hXm₀
  rw [← comap_cenT_glue κ u₀ (fun ω => cfField κ (h ω))] at hci
  have hℋ₁ : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1)
      (stopSigma q) ≤ MeasurableSpace.comap Prod.fst mΩ := by
    rw [show (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1) =
      killedHistory W VL VR ζ ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((MeasurableSpace.comap_mono (stopSigma_le _)).trans hYm.comap_le)
  have hℋ₂ : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => p.2) (stopSigma t) ≤
      MeasurableSpace.comap Prod.snd inferInstance :=
    MeasurableSpace.comap_mono (stopSigma_le _)
  exact isHistoryAvoidanceLocal_union measurable_fst.comap_le measurable_snd.comap_le hℋ₁ hℋ₂
    (((measurable_hullAt q).comp hYm).comp (comap_measurable Prod.fst))
    ((measurable_cfHullQ t).comp (comap_measurable Prod.snd)) hci hA₁ hA₂

end Glue

/-! ### The revealed union for arbitrary own records (the general statement) -/

section GlueRecords

variable {κ : ℝ} {Ω : Type u} {ℋ₁ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {γ : Type*} [mγ : MeasurableSpace γ]

/-- **E.2 on the glued space, for arbitrary own records of the two curves** (the general cross-conditioning
locality: the revealed set is the union of one own record of each curve). Let `A` be a hitting-measurable random set
on `Ω` satisfying the history-marked avoidance criterion for the centred field `cenT κ u₀ (h − π/2 χ)` with marks
`ℋ₁ ≤ mΩ` (e.g. the flow hull at a stopping time of its driving filtration, with the stopped σ-algebra), and
`𝔊 ∘ cfHistory` a random set on `Ω₂` read from the counterflow history, satisfying the criterion for `cenT κ u₀ h₂`
with marks `σ(f ∘ cfHistory)` for a measurable record `f` of the history (e.g. the history stopped at a stopping rule).
Then on the glued space `A ∪ 𝔊` satisfies the criterion for the centred glued field with the marks
`σ(fst)|_{ℋ₁} ∨ σ(f ∘ snd)`. -/
theorem isHistoryAvoidanceLocal_cfGlue_of_records (hhm : Measurable h)
    (hX₀ : IsMeasurableKilledDriving W₂ (Fin.elim0 : Fin 0 → ℝ≥0 → Ω₂ → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω₂ → ℝ) ζ₂)
    (hh₂m : Measurable h₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hℋ₁ : ℋ₁ ≤ mΩ) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc₁ : IsHistoryAvoidanceLocal ℋ₁ A (fun ω => cenT κ u₀ (cfField κ (h ω))) P)
    {f : HistorySpace 0 0 → γ} (hf : Measurable f)
    {𝔊 : HistorySpace 0 0 → Set ℂ} (h𝔊 : Measurable[_, hittingSigma] 𝔊)
    (hloc₂ : IsHistoryAvoidanceLocal (mγ.comap fun ω => f (cfHistory W₂ ζ₂ ω)) (fun ω => 𝔊 (cfHistory W₂ ζ₂ ω))
      (fun ω => cenT κ u₀ (h₂ ω)) P₂) :
    IsHistoryAvoidanceLocal (ℋ₁.comap (Prod.fst : Ω × HistorySpace 0 0 → Ω) ⊔
        mγ.comap (fun p : Ω × HistorySpace 0 0 => f p.2))
      (fun p : Ω × HistorySpace 0 0 => A p.1 ∪ 𝔊 p.2) (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hhm)) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hhm) with hμ
  have hXm₀ : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hhm
  have hXm : Measurable fun ω => cenT κ u₀ (cfField κ (h ω)) := (measurable_cenT κ u₀).comp hXm₀
  have hY₂m : Measurable (cfHistory W₂ ζ₂) := measurable_cfHistory hX₀
  have hX₂m : Measurable fun ω => cenT κ u₀ (h₂ ω) := (measurable_cenT κ u₀).comp hh₂m
  -- the first record, transported along `fst` (marks: the identity of `Ω` read through `ℋ₁`)
  have hpm : Measurable fun ω => (cenT κ u₀ (cfField κ (h ω)), ω) := hXm.prodMk measurable_id
  have hlaw₁ : μ.map (fun p : Ω × HistorySpace 0 0 => (cenT κ u₀ (cfField κ (h p.1)), p.1)) =
      P.map (fun ω => (cenT κ u₀ (cfField κ (h ω)), ω)) := by
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenT κ u₀ (cfField κ (h p.1)), p.1)) =
        (fun ω => (cenT κ u₀ (cfField κ (h ω)), ω)) ∘ Prod.fst from rfl,
      ← Measure.map_map hpm measurable_fst, hμ, glueMeasure_fst k hXm₀]
  have h₁' : IsHistoryAvoidanceLocal (ℋ₁.comap id) (fun ω => A (id ω)) (fun ω => cenT κ u₀ (cfField κ (h ω))) P := by
    rw [MeasurableSpace.comap_id]
    exact hloc₁
  have hA₁ := isHistoryAvoidanceLocal_of_map_eq (mβ := mΩ) (𝔐 := ℋ₁) hXm measurable_id (hXm.comp measurable_fst)
    measurable_fst hlaw₁ hA hℋ₁ h₁'
  -- the second record, transported along the law of `(h − π/2 χ, history)`
  have hlaw₂ : μ.map (fun p : Ω × HistorySpace 0 0 => (cenT κ u₀ (cfField κ (h p.1)), p.2)) =
      P₂.map (fun ω => (cenT κ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) := by
    have hT : Measurable fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenT κ u₀ r.1, r.2) :=
      ((measurable_cenT κ u₀).comp measurable_fst).prodMk measurable_snd
    have hpair : Measurable fun p : Ω × HistorySpace 0 0 => (cfField κ (h p.1), p.2) :=
      (hXm₀.comp measurable_fst).prodMk measurable_snd
    have hpair₂ : Measurable fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) := hh₂m.prodMk hY₂m
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenT κ u₀ (cfField κ (h p.1)), p.2)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenT κ u₀ r.1, r.2)) ∘
          fun p => (cfField κ (h p.1), p.2) from rfl,
      show (fun ω => (cenT κ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenT κ u₀ r.1, r.2)) ∘
          fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) from rfl,
      ← Measure.map_map hT hpair, ← Measure.map_map hT hpair₂, hμ, glueMeasure_map_pair hXm₀ k, hlaw, hk]
  have h₂' : IsHistoryAvoidanceLocal ((mγ.comap f).comap (cfHistory W₂ ζ₂)) (fun ω => 𝔊 (cfHistory W₂ ζ₂ ω))
      (fun ω => cenT κ u₀ (h₂ ω)) P₂ := by
    rw [MeasurableSpace.comap_comp]
    exact hloc₂
  have hA₂ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := mγ.comap f) hX₂m hY₂m (hXm.comp measurable_fst)
    measurable_snd hlaw₂ h𝔊 hf.comap_le h₂'
  have e₂ : (mγ.comap f).comap (Prod.snd : Ω × HistorySpace 0 0 → HistorySpace 0 0) =
      mγ.comap (fun p : Ω × HistorySpace 0 0 => f p.2) := MeasurableSpace.comap_comp
  rw [e₂] at hA₂
  -- the union
  have hci := condIndepEv_glue_fst (μ := P) k hXm₀
  rw [← comap_cenT_glue κ u₀ (fun ω => cfField κ (h ω))] at hci
  have hℋ₁' : ℋ₁.comap (Prod.fst : Ω × HistorySpace 0 0 → Ω) ≤ MeasurableSpace.comap Prod.fst mΩ :=
    MeasurableSpace.comap_mono hℋ₁
  have hℋ₂ : mγ.comap (fun p : Ω × HistorySpace 0 0 => f p.2) ≤ MeasurableSpace.comap Prod.snd inferInstance := by
    rw [← e₂]
    exact MeasurableSpace.comap_mono hf.comap_le
  exact isHistoryAvoidanceLocal_union measurable_fst.comap_le measurable_snd.comap_le hℋ₁' hℋ₂
    (hA.comp (comap_measurable Prod.fst)) (h𝔊.comp (comap_measurable Prod.snd)) hci hA₁ hA₂

end GlueRecords

end InteractingSLE.Sec5.CrossCond
