/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Record
import InteractingSLE.Spec.Coupling.SafeEnergy

/-!
# Aux. lemma 54 for general words, part 2: the kernel at the stop

Packet PROVE-AUX54. The record law of Aux. lemma 54 ("its conditional second marginal is the specified Gaussian
kernel") needs, on both sides, the conditional characteristic functional of the field at the stop, at every test
function avoiding the recorded hull, as a Borel functional of the recorded history:

* `kerG`, `recG`: Sec4's Borel version of the frozen right-hand side (`hasMeasurableHistCharFun`) read on the stopped
  history `recH`, and `1` on histories with no future;
* `recG_eq`: on the killed history of a state continuous on `[0, T]`, `recG` is the frozen right-hand side at `T`
  along the driver, with the bounded harmonic extension `histHarm` of the recorded data;
* `measurable_killedHistory_stopped`: the killed history is measurable for the stopped σ-algebra at its lifetime;
* **`hasSetKernel_of_clause`**: the set-integral kernel (`HasSetKernel`) for any killed history whose clause holds
  at the stops `V ∧ N`, under the regularity at the stop (the driver continuous a little beyond a stop that is not a
  threshold state).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4

variable {nL nR : ℕ}

/-! ### The kernel functional -/

/-- **The Borel kernel functional** (Sec4's `hasMeasurableHistCharFun`) read on the stopped history. -/
def kerG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR) : ℂ :=
  (hasMeasurableHistCharFun κ ρL ρR).choose φ (recH xL xR γ)

theorem measurable_kerG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) : Measurable (kerG κ ρL ρR xL xR φ) :=
  ((hasMeasurableHistCharFun κ ρL ρR).choose_spec.1 φ).comp (measurable_recH xL xR)

theorem kerG_eq (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    {φ : TestOn upperHalfPlaneOpens} {γ : HistorySpace nL nR} (hc : IsContHist (recH xL xR γ))
    (hd : Disjoint (tsupport φ) (regHull (recH xL xR γ))) :
    kerG κ ρL ρR xL xR φ γ = histCharFun κ ρL ρR φ (recH xL xR γ) :=
  (hasMeasurableHistCharFun κ ρL ρR).choose_spec.2 φ _ hc (by rwa [← hc.regHull_eq])

open Classical in
/-- **The record kernel**: `1` on histories with no future, the kernel functional otherwise. -/
def recG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR) : ℂ :=
  if recMask ρL ρR xL xR γ then 1 else kerG κ ρL ρR xL xR φ γ

theorem measurable_recG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) : Measurable (recG κ ρL ρR xL xR φ) := by
  classical
  exact Measurable.ite (measurableSet_recMask ρL ρR xL xR) measurable_const (measurable_kerG κ ρL ρR xL xR φ)

open Classical in
/-- **The bounded record kernel**: `recG` where it has modulus at most `1`, `0` elsewhere (it has modulus at most `1`
on every continuous history whose hull avoids the support, `norm_histCharFun_le_one`). -/
def recK (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR) : ℂ :=
  if ‖recG κ ρL ρR xL xR φ γ‖ ≤ 1 then recG κ ρL ρR xL xR φ γ else 0

theorem measurable_recK (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) : Measurable (recK κ ρL ρR xL xR φ) := by
  classical
  have hg := measurable_recG κ ρL ρR xL xR φ
  exact Measurable.ite (measurableSet_le hg.norm measurable_const) hg measurable_const

theorem norm_recK_le (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR) : ‖recK κ ρL ρR xL xR φ γ‖ ≤ 1 := by
  classical
  unfold recK
  split_ifs with h
  · exact h
  · simp

/-- **The conditional characteristic functional of a continuous history has modulus at most `1`** when the hull avoids
the support (the energy is nonnegative, `Coupling.loewnerGreenEnergy_nonneg`). -/
theorem norm_histCharFun_le_one (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {φ : TestOn upperHalfPlaneOpens}
    {γ : HistorySpace nL nR} (hc : IsContHist γ) (h0 : histPath γ 0 = 0)
    (hd : Disjoint (tsupport φ) (regHull γ)) : ‖histCharFun κ ρL ρR φ γ‖ ≤ 1 := by
  have hdc : Continuous (histDrive γ) := hc.continuous_histPath.comp continuous_real_toNNReal
  have hd0 : histDrive γ 0 = 0 := by
    show histPath γ (0 : ℝ).toNNReal = 0
    rw [Real.toNNReal_zero, h0]
  have hdis : Disjoint (tsupport φ) (fwdHull (histDrive γ) (γ.1.toNNReal : ℝ)) := by
    rw [hc.regHull_eq] at hd
    refine hd.mono_right fun z hz => (show z ∈ closure (fwdHull (histDrive γ) (γ.1.toNNReal : ℝ)) ∩
      (upperHalfPlaneOpens : Set ℂ) from ⟨subset_closure hz, hz.1⟩)
  have hE := Coupling.loewnerGreenEnergy_nonneg hdc hd0 (NNReal.coe_nonneg _) φ hdis
  unfold histCharFun
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, zero_sub]
  linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hE]

/-- A test function whose support avoids everything is `0`, and its pairing with any distribution is `0`. -/
theorem apply_eq_zero_of_disjoint_univ {φ : TestOn upperHalfPlaneOpens} (hφ : Disjoint (tsupport φ) (univ : Set ℂ))
    (x : DistOn upperHalfPlaneOpens) : x φ = 0 := by
  have h0 : φ = 0 := by
    ext z
    have hz : z ∉ tsupport φ := fun hz => Set.disjoint_left.1 hφ hz (mem_univ z)
    simpa using image_eq_zero_of_notMem_tsupport hz
  rw [h0, map_zero]

section Killed

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {ω : Ω} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **The frozen right-hand side at the stop along the driver is `histCharFun` of the stopped history** (with the
bounded harmonic extension `histHarm` of the recorded data). -/
theorem histCharFun_recH_killedHistory (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = e ω) (hc : ContinuousOn (dState W VL VR ω) (Iic T))
    (h0 : dState W VL VR ω 0 = initVal xL xR) (φ : TestOn upperHalfPlaneOpens) :
    histCharFun κ ρL ρR φ (recH xL xR (killedHistory W VL VR e ω)) =
      Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) T
          (histHarm κ ρL ρR (recH xL xR (killedHistory W VL VR e ω))) z * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) T φ : ℝ) : ℂ)) := by
  obtain ⟨-, hpath, -, -⟩ := recH_killedHistory_read hT hc h0
  have hstop : (recH xL xR (killedHistory W VL VR e ω)).1.toNNReal = T := by
    simp only [recH, killedHistory, ← hT, ENNReal.toNNReal_coe]
  have heq : EqOn (fun s : ℝ => W s.toNNReal ω) (histDrive (recH xL xR (killedHistory W VL VR e ω)))
      (Icc 0 (T : ℝ)) := by
    intro s hs
    show W s.toNNReal ω = histPath _ s.toNNReal
    rw [hpath, min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have h1 : (∫ z, couplingMean κ (histDrive (recH xL xR (killedHistory W VL VR e ω))) (T : ℝ)
      (histHarm κ ρL ρR (recH xL xR (killedHistory W VL VR e ω))) z * φ z) =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (T : ℝ)
        (histHarm κ ρL ρR (recH xL xR (killedHistory W VL VR e ω))) z * φ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [couplingMean]
    rw [Ito.fwdMap_congr_of_eqOn heq.symm, Ito.logDerivFwd_congr_of_eqOn heq.symm (NNReal.coe_nonneg _) le_rfl]
  have h2 : loewnerGreenEnergy (histDrive (recH xL xR (killedHistory W VL VR e ω))) (T : ℝ) φ =
      loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (T : ℝ) φ := by
    unfold loewnerGreenEnergy
    simp_rw [Ito.fwdMap_congr_of_eqOn heq.symm]
  unfold histCharFun
  rw [hstop, h1, h2]

/-- The data recorded at the stop of the stopped history are the centred positions at `T`. -/
theorem histData_recH_killedHistory {T : ℝ≥0} (hT : (T : ℝ≥0∞) = e ω)
    (hc : ContinuousOn (dState W VL VR ω) (Iic T)) (h0 : dState W VL VR ω 0 = initVal xL xR) :
    (fun i => histVL (recH xL xR (killedHistory W VL VR e ω)) i -
        histPath (recH xL xR (killedHistory W VL VR e ω)) (recH xL xR (killedHistory W VL VR e ω)).1.toNNReal) =
      (fun i => VL i T ω - W T ω) ∧
    (fun i => histVR (recH xL xR (killedHistory W VL VR e ω)) i -
        histPath (recH xL xR (killedHistory W VL VR e ω)) (recH xL xR (killedHistory W VL VR e ω)).1.toNNReal) =
      (fun i => VR i T ω - W T ω) := by
  obtain ⟨-, hpath, hL, hR⟩ := recH_killedHistory_read hT hc h0
  have hstop : (recH xL xR (killedHistory W VL VR e ω)).1.toNNReal = T := by
    simp only [recH, killedHistory, ← hT, ENNReal.toNNReal_coe]
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · rw [hL, hstop, hpath, min_self]
  · rw [hR, hstop, hpath, min_self]

end Killed

/-! ### The killed history at its lifetime -/

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- The lifetime of a measurable killed driving process is a stopping time of its driving filtration. -/
theorem isStoppingTime_lifetime_driving {P : Measure Ω} (hX : IsMeasurableKilledDriving W VL VR V) :
    IsStoppingTime (drivingFiltration P hX) fun ω => (V ω : WithTop ℝ≥0) :=
  Ito.isStoppingTime_lifetime (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hX))

/-- A killed sample is measurable for the stopped σ-algebra at the lifetime, in any filtration in which the lifetime
is a stopping time and the killed samples are adapted. -/
theorem measurableSet_killedSample_stopped' {𝓖 : Filtration ℝ≥0 mΩ}
    (hV : IsStoppingTime 𝓖 fun ω => (V ω : WithTop ℝ≥0))
    (hs : ∀ (p : ℕ × ℕ) (S : Set (DrivingValue nL nR)), MeasurableSet S →
      MeasurableSet[𝓖 (dyadicTime p)] ((fun ω => (killedHistory W VL VR V ω).2 p) ⁻¹' S)) (p : ℕ × ℕ)
    {S : Set (DrivingValue nL nR)} (hS : MeasurableSet S) :
    MeasurableSet[hV.measurableSpace] ((fun ω => (killedHistory W VL VR V ω).2 p) ⁻¹' S) := by
  have hsample := hs p S hS
  have e : (fun ω => (killedHistory W VL VR V ω).2 p) ⁻¹' S =
      ({ω | ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0) ≤ (V ω : WithTop ℝ≥0)} ∩
          (fun ω => (killedHistory W VL VR V ω).2 p) ⁻¹' S) ∪
        ({ω | (V ω : WithTop ℝ≥0) < (dyadicTime p : ℝ≥0)} ∩ {_ω | (0 : DrivingValue nL nR) ∈ S}) := by
    ext ω
    simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq]
    by_cases h : ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0) ≤ (V ω : WithTop ℝ≥0)
    · have h' : ¬ (V ω : WithTop ℝ≥0) < (dyadicTime p : ℝ≥0) := not_lt.2 h
      simp only [h, h', true_and, false_and, or_false]
    · have h' : (V ω : WithTop ℝ≥0) < (dyadicTime p : ℝ≥0) := not_le.1 h
      have hk : (killedHistory W VL VR V ω).2 p = 0 := by
        have : ¬ ((dyadicTime p : ℝ≥0∞) < V ω) := fun hlt => h hlt.le
        simp only [killedHistory, this, ↓reduceIte]
      simp only [h, h', false_and, true_and, false_or, hk]
  rw [e]
  exact (measurableSet_stopped_le_inter hV hsample).union
    ((hV.measurableSet_lt' (dyadicTime p)).inter (MeasurableSet.const _))

/-- **The killed history is measurable for the stopped σ-algebra at its lifetime**, in any filtration in which the
lifetime is a stopping time and the killed samples are adapted. -/
theorem measurable_killedHistory_stopped' {𝓖 : Filtration ℝ≥0 mΩ}
    (hV : IsStoppingTime 𝓖 fun ω => (V ω : WithTop ℝ≥0))
    (hs : ∀ (p : ℕ × ℕ) (S : Set (DrivingValue nL nR)), MeasurableSet S →
      MeasurableSet[𝓖 (dyadicTime p)] ((fun ω => (killedHistory W VL VR V ω).2 p) ⁻¹' S)) :
    Measurable[hV.measurableSpace] (killedHistory W VL VR V) := by
  have hVm : Measurable[hV.measurableSpace] V := by
    refine measurable_of_Iic fun a => ?_
    induction a using ENNReal.recTopCoe with
    | top => simp only [Iic_top, preimage_univ]; exact @MeasurableSet.univ _ hV.measurableSpace
    | coe r => exact hV.measurableSet_le' r
  have hsm : ∀ p : ℕ × ℕ, Measurable[hV.measurableSpace] fun ω => (killedHistory W VL VR V ω).2 p :=
    fun p S hS => measurableSet_killedSample_stopped' hV hs p hS
  exact Measurable.prodMk (m := hV.measurableSpace) hVm (@measurable_pi_iff Ω (ℕ × ℕ) _ hV.measurableSpace _ _ |>.2 hsm)

/-- **The killed history is measurable for the stopped σ-algebra at its lifetime** (its own driving filtration). -/
theorem measurable_killedHistory_stopped {P : Measure Ω} (hX : IsMeasurableKilledDriving W VL VR V)
    (hV : IsStoppingTime (drivingFiltration P hX) fun ω => (V ω : WithTop ℝ≥0)) :
    Measurable[hV.measurableSpace] (killedHistory W VL VR V) :=
  measurable_killedHistory_stopped' hV fun p _ hS =>
    Ito.le_usualAugmentation (killedDrivingFiltration hX) P (dyadicTime p) _ (measurable_killedSample hX p hS)

end Stopped

/-! ### The kernel at the stop from the frozen clause at `V ∧ σₙ` -/

section Clause

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **Regularity at the stop**: almost surely, if the state at a finite stop is not a threshold state, the driver is
continuous on `[0, T']` for some `T'` beyond the stop. (For a stopped coupling `(h, W_{·∧S}, V_{·∧S})` of the source,
whose driver is the stopped process, this holds with any `T'`.) -/
def IsRegularStop (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
    ¬ ForceWord.ThresholdCondition ρL ρR (W T ω) (fun i => VL i T ω) (fun j => VR j T ω) →
    ∃ T' : ℝ≥0, T < T' ∧ ContinuousOn (fun t => W t ω) (Iic T')

/-- **The frozen conditional-law clause at a stop `τ`**, for a σ-algebra `m` (the second conjunct of the clause of
`IsOptionalHullCoupling` and of `StoppedExtend.IsStoppedHullCoupling`). -/
def ClauseAt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (h : Ω → DistOn upperHalfPlaneOpens)
    (τ : Ω → WithTop ℝ≥0) (m : MeasurableSpace Ω) : Prop :=
  ∀ u : Ω → ℂ → ℝ,
    (∀ ω, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
        (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
        (u ω)) →
    ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
        condExp m P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
          Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))

/-- **The kernel at the stop** (set-integral form) from the frozen clause at the stops `V ∧ σₙ`: the killed history at
`V` (measurable for the stopped σ-algebra at `V`), its state continuous on `[0, V]` and started at the initial state,
regular at the stop, and stopping times `σₙ`, nondecreasing, with `V ≤ σₙ` for some `n` on every history with a
future. -/
theorem hasSetKernel_of_stops (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {𝓖 : Filtration ℝ≥0 mΩ} (hV : IsStoppingTime 𝓖 fun ω => (V ω : WithTop ℝ≥0))
    (hXm : Measurable[hV.measurableSpace] (killedHistory W VL VR V))
    (hcont : ∀ᵐ ω ∂P, ¬ recMask ρL ρR xL xR (killedHistory W VL VR V ω) → ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
      ContinuousOn (dState W VL VR ω) (Iic T))
    (h0 : ∀ᵐ ω ∂P, dState W VL VR ω 0 = initVal xL xR)
    (hreg : ∀ᵐ ω ∂P, ¬ recMask ρL ρR xL xR (killedHistory W VL VR V ω) → ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
      ∃ T' : ℝ≥0, T < T' ∧ ContinuousOn (fun t => W t ω) (Iic T'))
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓖 (σ n)) (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hcover : ∀ᵐ ω ∂P, ¬ recMask ρL ρR xL xR (killedHistory W VL VR V ω) →
      ∃ n, (V ω : WithTop ℝ≥0) ≤ σ n ω)
    (hcl : ∀ n, ClauseAt κ ρL ρR P W VL VR h (fun ω => min (V ω : WithTop ℝ≥0) (σ n ω))
      (hV.min (hσ n)).measurableSpace) :
    HasSetKernel P (killedHistory W VL VR V) (recHull ρL ρR xL xR) h (recK κ ρL ρR xL xR) := by
  classical
  intro φ B hB hBd
  set X : Ω → HistorySpace nL nR := killedHistory W VL VR V with hXdef
  have hXm' : Measurable X := hXm.mono hV.measurableSpace_le le_rfl
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hfdef
  have hfm : Measurable f := Complex.continuous_exp.measurable.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp ((measurable_distOn_apply φ).comp hh)))
  have hfi : Integrable f P := LocalExt.integrable_cexp_field hh φ
  have hgm : Measurable fun ω => recK κ ρL ρR xL xR φ (X ω) := (measurable_recK κ ρL ρR xL xR φ).comp hXm'
  set M : Set (HistorySpace nL nR) := {γ | recMask ρL ρR xL xR γ} with hMdef
  have hMm : MeasurableSet M := measurableSet_recMask ρL ρR xL xR
  -- the masked part: `φ = 0`
  have hmask : ∫ ω in X ⁻¹' (B ∩ M), f ω ∂P = ∫ ω in X ⁻¹' (B ∩ M), recK κ ρL ρR xL xR φ (X ω) ∂P := by
    refine setIntegral_congr_fun (hXm' (hB.inter hMm)) fun ω hω => ?_
    have hdis := hBd _ hω.1
    have hm : recMask ρL ρR xL xR (X ω) := hω.2
    simp only [recHull, hm, ↓reduceIte] at hdis
    simp only [hfdef, recK, recG, hm, ↓reduceIte, apply_eq_zero_of_disjoint_univ hdis, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, norm_one, le_refl]
  -- the unmasked part, piece by piece
  set B' : Set (HistorySpace nL nR) := B ∩ Mᶜ with hB'def
  have hB'm : MeasurableSet B' := hB.inter hMm.compl
  set A : ℕ → Set Ω := fun n => X ⁻¹' B' ∩ {ω | (V ω : WithTop ℝ≥0) ≤ σ n ω} with hAdef
  have hAm : ∀ n, MeasurableSet[(hV.min (hσ n)).measurableSpace] (A n) := fun n =>
    IsStoppingTime.measurableSet_inter_le hV (hσ n) _ (hXm hB'm)
  have hAm' : ∀ n, MeasurableSet (A n) := fun n => (hV.min (hσ n)).measurableSpace_le _ (hAm n)
  have hAmono : Monotone A := fun n k hnk ω hω => ⟨hω.1, hω.2.trans (hσm ω hnk)⟩
  have hAU : (⋃ n, A n) =ᵐ[P] X ⁻¹' B' := by
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · have : (⋃ n, A n) \ X ⁻¹' B' = ∅ := by
        rw [Set.sdiff_eq_empty]
        exact iUnion_subset fun n => inter_subset_left
      rw [this, measure_empty]
    · rw [← nonpos_iff_eq_zero, ← ae_iff.mp (show ∀ᵐ ω ∂P, ω ∈ X ⁻¹' B' → ω ∈ ⋃ n, A n from by
        filter_upwards [hcover] with ω hω hωB
        obtain ⟨n, hn⟩ := hω hωB.2
        exact mem_iUnion.2 ⟨n, hωB, hn⟩)]
      refine measure_mono fun ω hω => ?_
      simp only [Set.mem_sdiff, mem_ofPred_eq, not_imp] at hω ⊢
      exact hω
  -- the identity on each piece
  have hpiece : ∀ n, ∫ ω in A n, f ω ∂P = ∫ ω in A n, recK κ ρL ρR xL xR φ (X ω) ∂P := by
    intro n
    set τ : Ω → WithTop ℝ≥0 := fun ω => min (V ω : WithTop ℝ≥0) (σ n ω) with hτdef
    set good : Ω → Prop := fun ω => ∃ T : ℝ≥0, (T : ℝ≥0∞) = V ω ∧ (V ω : WithTop ℝ≥0) ≤ σ n ω ∧
      ContinuousOn (dState W VL VR ω) (Iic T) ∧ dState W VL VR ω 0 = initVal xL xR with hgood
    set u : Ω → ℂ → ℝ := fun ω => if hω : good ω then histHarm κ ρL ρR (recH xL xR (X ω)) else
      Classical.choose (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
        (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) with hudef
    have hτT : ∀ ω, (hω : good ω) → (τ ω).untopD 0 = hω.choose := by
      intro ω hω
      obtain ⟨hT, hle, -, -⟩ := hω.choose_spec
      have : τ ω = ((hω.choose : ℝ≥0) : WithTop ℝ≥0) := (min_eq_left hle).trans hT.symm
      rw [this, WithTop.untopD_coe]
    have hu : ∀ ω, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
        (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω) := by
      intro ω
      by_cases hω : good ω
      · obtain ⟨hT, -, hc, h0ω⟩ := hω.choose_spec
        have hspec := histHarm_spec κ ρL ρR (recH xL xR (X ω))
        obtain ⟨hdL, hdR⟩ := histData_recH_killedHistory (W := W) (VL := VL) (VR := VR) (xL := xL) (xR := xR)
          hT hc h0ω
        rw [hdL, hdR] at hspec
        simp only [hudef, hω, ↓reduceDIte, hτT ω hω]
        exact hspec
      · simp only [hudef, hω, ↓reduceDIte]
        exact Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR _ _)
    have hker := hcl n u hu φ
    rw [← setIntegral_condExp (hV.min (hσ n)).measurableSpace_le hfi (hAm n)]
    refine setIntegral_congr_ae (hAm' n) ?_
    filter_upwards [hker, hcont, h0, hreg] with ω h1 hc0 h00 hrg hωA
    obtain ⟨hωB, hωle⟩ := hωA
    have hnm : ¬ recMask ρL ρR xL xR (X ω) := hωB.2
    have hVtop : V ω ≠ ⊤ := fun htop => hnm (Or.inl (by simp only [hXdef, killedHistory, htop]))
    set T : ℝ≥0 := (V ω).toNNReal with hTdef
    have hT : (T : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal hVtop
    have hc := hc0 hnm T hT
    have hgω : good ω := ⟨T, hT, hωle, hc, h00⟩
    have hTeq : hgω.choose = T := ENNReal.coe_injective (hgω.choose_spec.1.trans hT.symm)
    obtain ⟨T', hTT', hW'⟩ := hrg hnm T hT
    have hreg' := regHull_recH_killedHistory (xL := xL) (xR := xR) hT hc h00 hTT' hW'
    have hdis : Disjoint (tsupport φ) (regHull (recH xL xR (X ω))) := by
      have := hBd _ hωB.1
      rwa [recHull_of_not_mask hnm] at this
    have hdisK : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
      rw [hτT ω hgω, hTeq]
      refine hdis.mono_right fun z hz => ?_
      rw [hreg']
      exact ⟨subset_closure hz, hz.1⟩
    have hC := (recH_killedHistory_read (xL := xL) (xR := xR) hT hc h00).1
    have hp0 : histPath (recH xL xR (X ω)) 0 = 0 := by
      rw [(recH_killedHistory_read (xL := xL) (xR := xR) hT hc h00).2.1, zero_min]
      exact congrArg Prod.fst h00
    have hnorm := norm_histCharFun_le_one κ ρL ρR hC hp0 hdis
    have hG : recG κ ρL ρR xL xR φ (X ω) = histCharFun κ ρL ρR φ (recH xL xR (X ω)) := by
      simp only [recG, hnm, ↓reduceIte]
      exact kerG_eq κ ρL ρR xL xR hC hdis
    have hK : recK κ ρL ρR xL xR φ (X ω) = histCharFun κ ρL ρR φ (recH xL xR (X ω)) := by
      unfold recK
      rw [hG]
      exact ite_eq_left_iff.2 fun hn => absurd hnorm hn
    rw [h1 hdisK, hK, histCharFun_recH_killedHistory κ ρL ρR hT hc h00 φ, hτT ω hgω, hTeq]
    first
      | rfl
      | (simp only [hudef, hgω, ↓reduceDIte]; rfl)
  -- the limit
  have hL1 := tendsto_setIntegral_of_monotone (μ := P) (f := f) hAm' hAmono hfi.integrableOn
  have hgi : Integrable (fun ω => recK κ ρL ρR xL xR φ (X ω)) P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => norm_recK_le κ ρL ρR xL xR φ _)
  have hL2 := tendsto_setIntegral_of_monotone (μ := P) hAm' hAmono hgi.integrableOn
  simp_rw [hpiece] at hL1
  have hunm : ∫ ω in X ⁻¹' B', f ω ∂P = ∫ ω in X ⁻¹' B', recK κ ρL ρR xL xR φ (X ω) ∂P := by
    rw [← setIntegral_congr_set hAU, ← setIntegral_congr_set hAU]
    exact tendsto_nhds_unique hL1 hL2
  have hsplit : X ⁻¹' B = X ⁻¹' (B ∩ M) ∪ X ⁻¹' B' := by
    ext ω
    simp only [mem_preimage, mem_union, mem_inter_iff, hB'def, mem_compl_iff]
    tauto
  have hdisj : Disjoint (X ⁻¹' (B ∩ M)) (X ⁻¹' B') :=
    Set.disjoint_left.2 fun ω h1 h2 => h2.2 h1.2
  rw [hsplit, setIntegral_union hdisj (hXm' hB'm) hfi.integrableOn hfi.integrableOn,
    setIntegral_union hdisj (hXm' hB'm) hgi.integrableOn hgi.integrableOn, hmask, hunm]

/-- **The kernel at the stop of a coupling through a stop** (the clause of `StoppedExtend.IsStoppedHullCoupling` at
`V ∧ N`), under the regularity at the stop. -/
theorem hasSetKernel_stoppedCoupling {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hreg : IsRegularStop ρL ρR P W VL VR V) :
    HasSetKernel P (killedHistory W VL VR V) (recHull ρL ρR xL xR) h (recK κ ρL ρR xL xR) := by
  obtain ⟨hEv, hcont, hh, -, hX, hcl⟩ := hSC
  have hV := isStoppingTime_lifetime_driving (P := P) hX
  have h0 : ∀ᵐ ω ∂P, dState W VL VR ω 0 = initVal xL xR := by
    filter_upwards [hEv.ae_path] with ω hp
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  refine hasSetKernel_of_stops κ ρL ρR xL xR hh hV (measurable_killedHistory_stopped hX hV) ?_ h0 ?_
    (σ := fun n _ => ((n : ℝ≥0) : WithTop ℝ≥0)) (fun n => isStoppingTime_const _ _)
    (fun ω n k hnk => by
      show ((n : ℝ≥0) : WithTop ℝ≥0) ≤ ((k : ℝ≥0) : WithTop ℝ≥0)
      exact_mod_cast hnk) ?_ fun n => ?_
  · filter_upwards [hcont] with ω hω _ T hT
    exact hω T hT
  · filter_upwards [hreg, hcont, h0] with ω hr hc h00 hnm T hT
    refine hr T hT fun hth => hnm (Or.inr ?_)
    rw [stopVal_killedHistory (xL := xL) (xR := xR) hT (hc T hT) h00]
    exact hth
  · refine Eventually.of_forall fun ω hω => ?_
    have hVtop : V ω ≠ ⊤ := fun htop => hω (Or.inl (by simp only [killedHistory, htop]))
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hVtop
    exact ⟨n, by exact_mod_cast hn.le⟩
  · refine (hcl _ (hV.min (isStoppingTime_const _ _)) (Eventually.of_forall fun ω => ⟨min_le_left _ _, ?_⟩)).2
    exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)

end Clause

end Aux54

end Restart

end InteractingSLE
