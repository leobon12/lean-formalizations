/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtILoc
import InteractingSLE.Spec.Sec7.LocalExtGLocal

/-!
# Aux. lemma 53 conditionally on an event `D ∈ 𝓓_T` (no almost-sure bound `T < ζ`)

Packet PROVE-LOCEXT-I. PROVE-LOCEXT-G's `isCouplingCharFun_restart` (and PROVE-SEC5-D's `restart_condExp` under it) need
the restarted stopping times below the restarted lifetime `ζ − T` **almost surely**, which is empty when `P(T ≥ ζ) > 0`.
Theorem 1.2's restart input (`RestartSeedCouplingStatement`) only has `T < ζ` on the cell event `D`. Here:

* **`IsOptionalHullCoupling.restart_condExp_of_lt`**: the restart clause in the original domain of the chart at **every**
  restarted stopping time `τ'`, almost surely on `{τ' < ζ − T}` (localized frozen clause of `LocalExtILoc`, at
  `T + (τ' ∧ N)`, and `E[· | 𝓖'_{τ'∧N}] = E[· | 𝓖'_{τ'}]` on `{τ' ≤ N}`);
* **`isCouplingCharFun_restart_cond`**: for `D ∈ 𝓓_T` with `P D ≠ 0` and `T < ζ` on `D`, and a `𝓓_T`-measurable `K`
  equal to `𝒳_T` almost surely on `D`, the restarted field `h' = restartField κ (h, K)` satisfies the coupling clause of
  the restarted processes **under `P[·|D]`** for the restarted filtration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE

namespace LocalExt

open Coupling Sec5.Markov Sec2.Restart

section RestartLocalized

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The kernel of the restart clause read in the original domain of the chart `c`:
`exp(i ∫ (𝔥'_t ∘ fwd − χ lift) φ − ½ ‖φ‖²_{H⁻¹(inv(ℍ ∖ K'_t))})`. -/
def restartKernel (κ : ℝ) (W' : ℝ≥0 → Ω → ℝ) (c : Ω → Chart) (u : ℂ → ℝ)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (t : ℝ≥0) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => W' s.toNNReal ω) (t : ℝ≥0) u ((c ω).1 z) - 0 -
      chiC κ * (c ω).2.2 z) * φ z : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) (t : ℝ≥0))) φ φ : ℝ) : ℂ))

/-- The restart clause at a **finite** restarted stopping time, almost surely on `{τ' < ζ − T}`. -/
theorem restart_condExp_of_lt_of_ne_top [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ)
    (hτfin : ∀ ω, τ ω ≠ ⊤) (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (forceJumpSet
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (u ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < restartLife ζ T ω →
      tsupport φ ⊆ (restartChart W T ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        restartKernel κ (restartDrv W T) (restartChart W T) (u ω) φ ((τ ω).untopD 0) ω := by
  classical
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t, MeasurableSet[drivingFiltration P hX t] s :=
    fun s hs h0 t => Ito.measurableSet_usualAugmentation_of_null hs h0 t
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hτfin' : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := ae_of_all _ hτfin
  set σ := restartTime T τ with hσdef
  have hσ : IsStoppingTime (drivingFiltration P hX) σ := isStoppingTime_restartTime hT hnull hτ hτfin'
  have hσval : ∀ ω, (σ ω).untopD 0 = T ω + (τ ω).untopD 0 := fun ω => restartTime_untopD T τ ω
  have hu' : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω)
        (fun i => VR i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω)
        (fun i => VR i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω)) (u ω) := by
    intro ω
    have e1 : (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω) =
        fun i => VL i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω := funext fun i => by
      rw [restartMark_sub_restartDrv, hσval]
    have e2 : (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω) =
        fun i => VR i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω := funext fun i => by
      rw [restartMark_sub_restartDrv, hσval]
    rw [← e1, ← e2]
    exact hu ω
  have hmain := hC.ae_condExp_cexp_eq_of_lt hκ hX hσ u hu' φ
  rw [measurableSpace_restartTime_eq hT hnull hτ hτfin']
  filter_upwards [hmain, hC.1.2.2.2.2] with ω hω hp hlt hsupp
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (hτfin ω)
  have hτr : (τ ω).untopD 0 = r := by rw [← hr, WithTop.untopD_coe]
  have hσr : (σ ω).untopD 0 = T ω + r := by rw [hσval, hτr]
  have hσeq : σ ω = ((T ω + r : ℝ≥0) : WithTop ℝ≥0) := by simp only [hσdef, restartTime, hτr]
  have hTr : ((T ω + r : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    have h1 : (r : ℝ≥0∞) < ζ ω - T ω := by
      rw [← hr] at hlt
      exact_mod_cast hlt
    have h2 : (T ω : ℝ≥0∞) + (r : ℝ≥0∞) < ζ ω := lt_tsub_iff_left.1 h1
    exact_mod_cast h2
  have hσζ : (σ ω : ℝ≥0∞) < ζ ω := by rw [hσeq]; exact_mod_cast hTr
  obtain ⟨himg, hint⟩ := restart_path (w := fun t => W t ω) hp.2.2.2.1 hp.1 hTr κ (u ω)
  simp only [hτr] at hsupp ⊢
  have himg' : (restartChart W T ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) (r : ℝ)) =
        H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((T ω + r : ℝ≥0) : ℝ) := himg
  rw [himg'] at hsupp
  have hdisj : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((T ω + r : ℝ≥0) : ℝ)) :=
    Set.disjoint_left.2 fun z hz hzK => (hsupp hz).2 hzK
  have hω' := hω hσζ (by rw [hσr]; exact hdisj)
  rw [hω', hσr, clauseKernel, restartKernel, himg',
    WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω) hp.2.2.2.1 hp.1 hTr φ hdisj]
  congr 4
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport φ
  · have hz' : z ∈ (restartChart W T ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) (r : ℝ)) := by
      rw [himg']; exact hsupp hz
    exact congrArg (· * φ z) (hint z hz').symm
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- **Aux. lemma 53 in the original domain, at every restarted stopping time, on `{τ' < ζ − T}`** (no almost-sure bound
by the restarted lifetime): almost surely, if `τ' < ζ − T` and `φ` is supported in `F_T(ℍ ∖ K'_{τ'})`, then
`E[e^{i(h, φ)} | 𝓖'_{τ'}]` is the restart kernel. -/
theorem restart_condExp_of_lt [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ)
    (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (forceJumpSet
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (u ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < restartLife ζ T ω →
      tsupport φ ⊆ (restartChart W T ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        restartKernel κ (restartDrv W T) (restartChart W T) (u ω) φ ((τ ω).untopD 0) ω := by
  classical
  have hN : ∀ N : ℕ, ∀ᵐ ω ∂P, τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0) → (τ ω : ℝ≥0∞) < restartLife ζ T ω →
      tsupport φ ⊆ (restartChart W T ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        restartKernel κ (restartDrv W T) (restartChart W T) (u ω) φ ((τ ω).untopD 0) ω := by
    intro N
    set τN : Ω → WithTop ℝ≥0 := fun ω => min (τ ω) ((N : ℝ≥0) : WithTop ℝ≥0) with hτNdef
    have hτN : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τN := hτ.min_const (N : ℝ≥0)
    have hfin : ∀ ω, τN ω ≠ ⊤ := fun ω =>
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right (τ ω) ((N : ℝ≥0) : WithTop ℝ≥0))
    set uN : Ω → ℂ → ℝ := fun ω => if τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0) then u ω else
      bheAt κ ρL ρR
        (fun i => restartMark (VL i) W T ((τN ω).untopD 0) ω - restartDrv W T ((τN ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τN ω).untopD 0) ω - restartDrv W T ((τN ω).untopD 0) ω) with huNdef
    have huN : ∀ ω, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR
          (fun i => restartMark (VL i) W T ((τN ω).untopD 0) ω - restartDrv W T ((τN ω).untopD 0) ω)
          (fun i => restartMark (VR i) W T ((τN ω).untopD 0) ω - restartDrv W T ((τN ω).untopD 0) ω))
        (forceJumpSet
          (fun i => restartMark (VL i) W T ((τN ω).untopD 0) ω - restartDrv W T ((τN ω).untopD 0) ω)
          (fun i => restartMark (VR i) W T ((τN ω).untopD 0) ω - restartDrv W T ((τN ω).untopD 0) ω))
        (uN ω) := by
      intro ω
      by_cases hle : τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)
      · have e : τN ω = τ ω := min_eq_left hle
        simp only [huNdef, hle, ↓reduceIte, e]
        exact hu ω
      · simp only [huNdef, hle, ↓reduceIte]
        exact isBoundedHarmonicExtension_bheAt κ ρL ρR _ _
    have hmain := restart_condExp_of_lt_of_ne_top hC hκ hX hT τN hτN hfin uN huN φ
    have hce := condExp_min_stopping_time_ae_eq_restrict_le_const (μ := P)
      (f := fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) hτ (N : ℝ≥0)
    rw [EventuallyEq, ae_restrict_iff' (hτ.measurableSpace_le _ (hτ.measurableSet_le' (N : ℝ≥0)))] at hce
    filter_upwards [hmain, hce] with ω h1 h2 hle hlt hsupp
    have e : τN ω = τ ω := min_eq_left hle
    rw [← h2 hle]
    have h1' := h1 (by rw [e]; exact hlt) (by rw [e]; exact hsupp)
    simp only [e, huNdef, hle, ↓reduceIte] at h1'
    exact h1'
  filter_upwards [ae_all_iff.2 hN] with ω hall hlt hsupp
  have hfin : τ ω ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact not_top_lt hlt
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hfin
  obtain ⟨N, hN'⟩ := exists_nat_ge (t : ℝ)
  refine hall N ?_ hlt hsupp
  rw [← ht]
  exact WithTop.coe_le_coe.2 (by exact_mod_cast hN')

end RestartLocalized


section RestartCond

open Sec7

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- `D ∈ 𝓓_T` is measurable at every stopping time of the restarted filtration. -/
theorem measurableSet_restart_stop {𝓓 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓓 fun ω => (T ω : WithTop ℝ≥0)) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (restartFiltration 𝓓 T hT) τ) {D : Set Ω} (hD : MeasurableSet[hT.measurableSpace] D) :
    MeasurableSet[hτ.measurableSpace] D := by
  have h0 : restartFiltration 𝓓 T hT 0 ≤ hτ.measurableSpace :=
    hτ.le_measurableSpace_of_const_le fun _ => bot_le
  rw [restartFiltration_zero hT] at h0
  exact h0 _ hD

/-- **Aux. lemma 53, the Gaussian clause in the half-plane, conditionally on a cell event** (no almost-sure bound
`T < ζ`). For a frozen optional hull coupling with `κ > 0`, a finite stopping time `T` of its driving filtration, an
event `D ∈ 𝓓_T` of positive probability and a `𝓓_T`-measurable `K` equal to the recorded history `𝒳_T` almost surely
on `D ∩ {T < ζ}`, the restarted field `h' = restartField κ (h, K)` satisfies the coupling clause of the restarted
processes `W_{T+·} − W_T`, `V_{T+·} − W_T`, `ζ − T` in the restarted filtration `𝓖'_s = 𝓓_{T+s}`, **under `P[·|D]`**. -/
theorem isCouplingCharFun_restart_cond [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {D : Set Ω} (hD : MeasurableSet[hT.measurableSpace] D) (hPD : P D ≠ 0)
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, ω ∈ D → (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) :
    Coupling.MartMeans.IsCouplingCharFun κ ρL ρR (P[|D]) (restartFiltration (drivingFiltration P hX) T hT)
      (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T) (restartLife ζ T)
      (fun ω => restartField κ (h ω, K ω)) := by
  have hDm : MeasurableSet D := hT.measurableSpace_le _ hD
  have hprob : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hac : P[|D] ≪ P := cond_absolutelyContinuous
  have hpath := hC.1.2.2.2.2
  have h0 := restartFiltration_zero (𝓕 := drivingFiltration P hX) hT
  have hKm' : Measurable[restartFiltration (drivingFiltration P hX) T hT 0] K := by rw [h0]; exact hKm
  refine Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport (c := fun ω => histChart (K ω))
    (fun ω => isConformal_histChart (K ω)) (fun z => hKm' (measurableSet_mem_dom_histChart z))
    (fun z => ?_) (fun z => ?_) (fun ω => continuousOn_lift_histChart (K ω)) hC.2.1 ?_ ?_
    (fun ω => isChartTransport_restartField κ (h ω, K ω))
  · have hm := (measurable_indicator_fwd_histChart (nL := nL) (nR := nR) z).comp hKm'
    have e : ({ω | z ∈ (histChart (K ω)).dom}.indicator fun ω => (histChart (K ω)).1 z) =
        ({y | z ∈ (histChart y).dom}.indicator fun y => (histChart y).1 z) ∘ K := by
      funext ω
      by_cases hz : z ∈ (histChart (K ω)).dom
      · simp only [Function.comp_apply, indicator_of_mem (show K ω ∈ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_mem (show ω ∈ {ω | z ∈ (histChart (K ω)).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show K ω ∉ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_notMem (show ω ∉ {ω | z ∈ (histChart (K ω)).dom} from hz)]
    rw [e]
    exact hm
  · have hm := (measurable_indicator_lift_histChart (nL := nL) (nR := nR) z).comp hKm'
    have e : ({ω | z ∈ (histChart (K ω)).dom}.indicator fun ω => (histChart (K ω)).2.2 z) =
        ({y | z ∈ (histChart y).dom}.indicator fun y => (histChart y).2.2 z) ∘ K := by
      funext ω
      by_cases hz : z ∈ (histChart (K ω)).dom
      · simp only [Function.comp_apply, indicator_of_mem (show K ω ∈ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_mem (show ω ∈ {ω | z ∈ (histChart (K ω)).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show K ω ∉ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_notMem (show ω ∉ {ω | z ∈ (histChart (K ω)).dom} from hz)]
    rw [e]
    exact hm
  · -- the restarted driver starts at `0` and is continuous before the restarted lifetime
    filter_upwards [hac.ae_le hpath] with ω hp
    refine ⟨by simp [restartDrv], ?_⟩
    by_cases hTζ : (T ω : ℝ≥0∞) < ζ ω
    · exact (hp.restart hTζ).2.2.2.1
    · have he : {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} = ∅ := by
        ext t
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, restartLife]
        rw [tsub_eq_zero_of_le (not_lt.1 hTζ)]
        exact zero_le
      rw [he]
      exact continuousOn_empty _
  · -- the clause in the original domain of the chart, under `P[·|D]`
    intro τ hτ hτζ u hu φ
    have hmain := restart_condExp_of_lt hC hκ hX hT τ hτ u hu φ
    have hDτ : MeasurableSet[hτ.measurableSpace] D := measurableSet_restart_stop hT hτ hD
    have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hC.2.1)
    have hcond := condExp_cond_ae_eq (𝒢 := hτ.measurableSpace) (𝒢' := hτ.measurableSpace) le_rfl
      hτ.measurableSpace_le hDτ hPD hXi stronglyMeasurable_condExp integrable_condExp EventuallyEq.rfl
    filter_upwards [hcond, hac.ae_le hmain, hac.ae_le hK, hac.ae_le hpath, hτζ, ae_cond_mem hDm]
      with ω h1 h2 h3 hp h4 hωD hsupp
    have hTζ : (T ω : ℝ≥0∞) < ζ ω := by
      have h5 : 0 < restartLife ζ T ω := lt_of_le_of_lt zero_le h4
      exact tsub_pos_iff_lt.1 h5
    have hc : histChart (K ω) = restartChart W T ω := by
      rw [h3 hωD hTζ]
      exact (restartChart_eq_histChart hp.2.2.2.1 hp.1 hTζ).symm
    simp only [hc] at hsupp ⊢
    rw [h1]
    exact h2 h4 hsupp

end RestartCond

end LocalExt

end InteractingSLE
