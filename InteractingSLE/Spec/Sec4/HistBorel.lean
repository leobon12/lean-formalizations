/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Special4Coupling
import InteractingSLE.Spec.Coupling.Assembly11Meas
import InteractingSLE.Spec.Coupling.SafeCompact
import QuantumZipper.Proofs.Thm18.G1PkgPath
import InteractingSLE.Spec.Sec2.Assembly3Entr

/-!
# Aux. lemma 23: the two Borel facts about a recorded history

Packet PROVE-SEC4-B4. `planning/handoffs/PROVE-SEC4-A4.md` reduced Aux. lemma 23 at coupling level
(`Sec4.aux23_of_historyMeasurable`) to two deterministic measurability inputs about Loewner functionals of a recorded
driving history: `HasMeasurableHistHull nL nR` (input (c)) and `HasMeasurableHistCharFun κ ρL ρR` (input (b)). Both
are proved here.

## Method

* **The regularized driver** `regPath γ`: QuantumZipper's path regularization `G1Pkg.pathReg` applied to the driver
  `histPath γ` read from the history. It is continuous for every history, measurable in the history at each time, and
  equal to `histPath γ` on every continuous history (`IsContHist`).
* **The canonical space.** The history space itself, with the constant filtration, the driver `regPath`, the lifetime
  `⊤`, and the recorded stop `histStop γ = γ.1.toNNReal` (a stopping time). The landed machinery of the safe stops
  (`Coupling.IsSafeAt`, `safeExitTime`, `measurable_stoppedPair`) applies verbatim.
* **Safe events at the recorded stop** (`safeHist K δ n`): `K` is safe at time `0` and the safe exit time is not
  before the stop. They are measurable (the exit time is read on a dense countable set of times, the safe condition on
  a dense countable subset of `K`), imply the safe condition at the stop, and cover the event "`K` is alive at the
  stop" (`exists_mem_safeHist`).
* **Input (c)**: `regHull γ = cl(K_S(regPath γ)) ∩ ℍ`; a compact `K` misses it iff each slice
  `K ∩ {Im ≥ 1/(j+1)}` is alive at the stop, a countable condition on safe events.
* **Input (b)**: on each safe event the tested mean and the energy at the stop are measurable
  (`Coupling.measurable_stoppedPair`); the bounded harmonic extension is the explicit `Impl.forceExt` (unique on `ℍ`),
  which is the explicit `meanHarmonic` at the clamped positions.

## Main results

* **`hasMeasurableHistHull`**: `HasMeasurableHistHull nL nR`;
* **`hasMeasurableHistCharFun`**: `HasMeasurableHistCharFun κ ρL ρR`;
* `killedStateLawUnique_of_isOrderedForceWord`: Theorem 2.2's uniqueness in law (PROVE-SEC2-PATCH4) in the form
  `KilledStateLawUnique`;
* **`map_stopHistory_prod_eq_of_thinTrace`**: Aux. lemma 23 at coupling level, with no named input;
* **`ae_stopHistory_eq_comp_of_thinTrace`**: its "Consequently" clause — a field-determining function of the stopped
  history in one coupling is one in every coupling with the optional hull specification.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Sec4

open LawUnique LQGMetric

variable {nL nR : ℕ}

/-! ### Reading a history measurably -/

/-- The recorded stop of a history. -/
def histStop (γ : HistorySpace nL nR) : ℝ≥0 := γ.1.toNNReal

theorem measurable_histStop : Measurable (histStop (nL := nL) (nR := nR)) :=
  ENNReal.measurable_toNNReal.comp measurable_fst

/-- Evaluation of the recorded samples at a measurable index. -/
theorem measurable_sample_comp {f : HistorySpace nL nR → ℕ × ℕ} (hf : Measurable f) :
    Measurable fun γ : HistorySpace nL nR => γ.2 (f γ) := by
  have h : Measurable fun q : HistorySpace nL nR × (ℕ × ℕ) => q.1.2 q.2 :=
    measurable_from_prod_countable_left fun p => (measurable_pi_apply p).comp measurable_snd
  exact h.comp (measurable_id.prodMk hf)

theorem measurable_lowerDyadic_comp {r : HistorySpace nL nR → ℝ≥0} (hr : Measurable r) (n : ℕ) :
    Measurable fun γ => lowerDyadic (r γ) n := by
  refine measurable_const.prodMk ?_
  exact Nat.measurable_floor.comp (measurable_const.mul hr)

theorem measurable_histPath_apply (t : ℝ≥0) :
    Measurable fun γ : HistorySpace nL nR => histPath γ t := by
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine (measurable_fst.comp (measurable_sample_comp ?_)).stronglyMeasurable
  exact measurable_lowerDyadic_comp (measurable_const.min measurable_histStop) n

theorem measurable_histPath : Measurable fun γ : HistorySpace nL nR => histPath γ :=
  measurable_pi_iff.2 measurable_histPath_apply

theorem measurable_histVL (i : Fin nL) : Measurable fun γ : HistorySpace nL nR => histVL γ i := by
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).comp
    (measurable_sample_comp ?_)).stronglyMeasurable
  exact measurable_lowerDyadic_comp measurable_histStop n

theorem measurable_histVR (i : Fin nR) : Measurable fun γ : HistorySpace nL nR => histVR γ i := by
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine (((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).comp
    (measurable_sample_comp ?_)).stronglyMeasurable
  exact measurable_lowerDyadic_comp measurable_histStop n

/-! ### The regularized driver -/

/-- **The regularized driver of a history**: QuantumZipper's regularization of `histPath γ`. -/
def regPath (γ : HistorySpace nL nR) : ℝ≥0 → ℝ := Thm18Asm.G1Pkg.pathReg (histPath γ)

theorem continuous_regPath (γ : HistorySpace nL nR) : Continuous (regPath γ) :=
  Thm18Asm.G1Pkg.pathReg_spec.2.1 _

theorem measurable_regPath_apply (t : ℝ≥0) : Measurable fun γ : HistorySpace nL nR => regPath γ t :=
  (measurable_pi_apply t).comp (Thm18Asm.G1Pkg.pathReg_spec.1.comp measurable_histPath)

theorem measurable_regPath_uncurry :
    Measurable fun p : ℝ≥0 × HistorySpace nL nR => regPath p.2 p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun t (γ : HistorySpace nL nR) => regPath γ t)
    (fun γ => continuous_regPath γ) measurable_regPath_apply

/-- The regularized driver at the recorded stop is measurable. -/
theorem measurable_regPath_histStop :
    Measurable fun γ : HistorySpace nL nR => regPath γ (histStop γ) := by
  have h := measurable_regPath_uncurry.comp (f := fun γ : HistorySpace nL nR => (histStop γ, γ))
    (g := fun p : ℝ≥0 × HistorySpace nL nR => regPath p.2 p.1) (measurable_histStop.prodMk measurable_id)
  exact h

/-- On a continuous history the recorded driver and the force coordinates are read from the continuous state. -/
theorem IsContHist.exists_eq {γ : HistorySpace nL nR} (h : IsContHist γ) :
    ∃ f : ℝ≥0 → DrivingValue nL nR, Continuous f ∧ (∀ t, histPath γ t = (f (min t (histStop γ))).1) ∧
      (∀ i, histVL γ i = (f (histStop γ)).2.1 i) ∧ ∀ i, histVR γ i = (f (histStop γ)).2.2 i := by
  obtain ⟨-, f, hf, hγ⟩ := h
  have key : ∀ r : ℝ≥0, r ≤ histStop γ → Tendsto (fun n => γ.2 (lowerDyadic r n)) atTop (𝓝 (f r)) := by
    intro r hr
    have h1 : Tendsto (fun n => f (dyadicTime (lowerDyadic r n))) atTop (𝓝 (f r)) :=
      (hf.tendsto r).comp (tendsto_dyadicTime_lowerDyadic r)
    refine h1.congr fun n => (hγ _ ?_).symm
    exact (dyadicTime_lowerDyadic_le r n).trans hr
  refine ⟨f, hf, fun t => ?_, fun i => ?_, fun i => ?_⟩
  · show limUnder atTop (fun n => (γ.2 (lowerDyadic (min t (histStop γ)) n)).1) = _
    exact Tendsto.limUnder_eq ((continuous_fst.tendsto _).comp (key _ (min_le_right _ _)))
  · show limUnder atTop (fun n => (γ.2 (lowerDyadic (histStop γ) n)).2.1 i) = _
    exact Tendsto.limUnder_eq ((((continuous_apply i).comp continuous_fst).tendsto _).comp
      ((continuous_snd.tendsto _).comp (key _ le_rfl)))
  · show limUnder atTop (fun n => (γ.2 (lowerDyadic (histStop γ) n)).2.2 i) = _
    exact Tendsto.limUnder_eq ((((continuous_apply i).comp continuous_snd).tendsto _).comp
      ((continuous_snd.tendsto _).comp (key _ le_rfl)))

theorem IsContHist.continuous_histPath {γ : HistorySpace nL nR} (h : IsContHist γ) :
    Continuous (histPath γ) := by
  obtain ⟨f, hf, hp, -⟩ := h.exists_eq
  have : histPath γ = fun t => (f (min t (histStop γ))).1 := funext hp
  rw [this]
  exact continuous_fst.comp (hf.comp (continuous_id.min continuous_const))

/-- **On a continuous history the regularized driver is the recorded driver.** -/
theorem IsContHist.regPath_eq {γ : HistorySpace nL nR} (h : IsContHist γ) : regPath γ = histPath γ :=
  Thm18Asm.G1Pkg.pathReg_spec.2.2 _ h.continuous_histPath

theorem IsContHist.rpath_regPath {γ : HistorySpace nL nR} (h : IsContHist γ) :
    Ito.rpath (regPath γ) = histDrive γ := by
  rw [h.regPath_eq]
  rfl

/-! ### The canonical space: the history space with the constant filtration -/

/-- The constant filtration of the history space. -/
def histFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (HistorySpace nL nR)) :=
  Filtration.const ℝ≥0 _ le_rfl

theorem histFiltration_apply (t : ℝ≥0) :
    (histFiltration (nL := nL) (nR := nR)) t = (inferInstance : MeasurableSpace (HistorySpace nL nR)) :=
  rfl

/-- The regularized driver as a process on the history space. -/
def regProc : ℝ≥0 → HistorySpace nL nR → ℝ := fun t γ => regPath γ t

theorem adaptedBefore_regProc :
    AdaptedBefore histFiltration (fun _ => ⊤) (regProc (nL := nL) (nR := nR)) := by
  intro t A hA
  have e : {γ : HistorySpace nL nR | (t : ℝ≥0∞) < ⊤ ∧ regProc t γ ∈ A} = (fun γ => regPath γ t) ⁻¹' A := by
    ext γ
    simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, mem_preimage, regProc]
  rw [e]
  exact measurable_regPath_apply t hA

theorem continuousOn_regProc (γ : HistorySpace nL nR) :
    ContinuousOn (fun t => regProc t γ) {t | (t : ℝ≥0∞) < ⊤} :=
  (continuous_regPath γ).continuousOn

theorem isStoppingTime_histStop :
    IsStoppingTime histFiltration fun γ : HistorySpace nL nR => (histStop γ : WithTop ℝ≥0) := by
  intro i
  simp only [WithTop.coe_le_coe]
  exact measurableSet_le measurable_histStop measurable_const

/-! ### Safe events at the recorded stop -/

/-- **The safe event of `K` at the recorded stop**, at level `δ` and horizon `n`: `K` is safe at time `0` along the
regularized driver, and the safe exit time is not before the stop. -/
def safeHist (K : Set ℂ) (δ : ℝ) (n : ℕ) : Set (HistorySpace nL nR) :=
  {γ | Coupling.IsSafeAt K δ n n ⊤ (regPath γ) 0 ∧
    ¬ Coupling.safeExitTime K δ n n ⊤ (regPath γ) < histStop γ}

/-- The safe condition of `K ⊆ ℍ` at a fixed time is a measurable event of the history. -/
theorem measurableSet_isSafeAt_regPath {K : Set ℂ} (hKH : K ⊆ H) {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (d : ℝ≥0) :
    MeasurableSet {γ : HistorySpace nL nR | Coupling.IsSafeAt K δ n n ⊤ (regPath γ) d} := by
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hst : IsStoppingTime (histFiltration (nL := nL) (nR := nR))
      fun _ => ((n : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have h := Coupling.measurableSet_isSafeAt (𝓖 := histFiltration (nL := nL) (nR := nR))
    (ζ := fun _ => ⊤) (W := regProc) (G := univ) adaptedBefore_regProc
    (fun γ _ => continuousOn_regProc γ) MeasurableSet.univ hDc (hDK.trans hKH)
    (σ₀ := fun _ => (n : ℝ≥0)) hst δ n d
  rw [histFiltration_apply] at h
  convert h using 1
  ext γ
  simp only [mem_ofPred_eq, mem_univ, true_and]
  constructor
  · intro h'
    exact h'.subset hDK
  · intro h'
    exact h'.of_dense (continuousOn_regProc γ) hKH hKD hDK hδ

theorem dense_range_dyadicTime : Dense (range dyadicTime) := fun t =>
  mem_closure_of_tendsto (tendsto_dyadicTime_lowerDyadic t) (Eventually.of_forall fun _ => mem_range_self _)

theorem measurableSet_safeHist {K : Set ℂ} (hKH : K ⊆ H) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    MeasurableSet (safeHist (nL := nL) (nR := nR) K δ n) := by
  have e : safeHist (nL := nL) (nR := nR) K δ n =
      {γ | Coupling.IsSafeAt K δ n n ⊤ (regPath γ) 0} ∩
        (⋃ p : ℕ × ℕ, {γ : HistorySpace nL nR | dyadicTime p < histStop γ} ∩
          {γ | Coupling.IsSafeAt K δ n n ⊤ (regPath γ) (dyadicTime p)}ᶜ)ᶜ := by
    ext γ
    have hiff := Coupling.safeExitTime_lt_iff (K := K) (δ := δ) (N := n) (σ₀ := n) (ζ := ⊤)
      (w := regPath γ) (continuous_regPath γ).continuousOn hKH dense_range_dyadicTime (t := histStop γ)
    simp only [safeHist, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_iUnion, hiff,
      exists_range_iff]
  rw [e]
  refine (measurableSet_isSafeAt_regPath hKH hδ n 0).inter (MeasurableSet.iUnion fun p => ?_).compl
  exact (measurableSet_lt measurable_const measurable_histStop).inter
    (measurableSet_isSafeAt_regPath hKH hδ n _).compl

/-- On the safe event, `K` is safe at the recorded stop. -/
theorem isSafeAt_of_mem_safeHist {K : Set ℂ} (hKH : K ⊆ H) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    {γ : HistorySpace nL nR} (h : γ ∈ safeHist K δ n) :
    Coupling.IsSafeAt K δ n n ⊤ (regPath γ) (histStop γ) := by
  have hw : ContinuousOn (regPath γ) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := (continuous_regPath γ).continuousOn
  have hτ := Coupling.isSafeAt_safeExitTime hw hKH hδ ENNReal.coe_lt_top h.1
  exact hτ.anti hw hKH (not_lt.1 h.2)

/-- A compact subset of `ℍ` has a positive lower bound on its imaginary parts. -/
theorem exists_pos_le_im {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ z.im := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, by simp [hKe]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne Complex.continuous_im.continuousOn
    exact ⟨x₀.im, hKH hx₀, fun z hz => isMinOn_iff.1 hmin z hz⟩

/-- **The safe events cover the event "`K` is alive at the recorded stop"**: if every point of the compact
`K ⊆ ℍ` is alive at the stop, then the history lies in the safe events of all large levels. -/
theorem eventually_mem_safeHist {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    {γ : HistorySpace nL nR}
    (halive : ∀ z ∈ K, ∃ u, IsForwardSol (Ito.rpath (regPath γ)) z (histStop γ) u) :
    ∀ᶠ n : ℕ in atTop, γ ∈ safeHist K (1 / ((n : ℝ) + 1)) n := by
  have hw : ContinuousOn (regPath γ) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := (continuous_regPath γ).continuousOn
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (histStop γ)
  have h1 := Coupling.eventually_le_safeExitTime hw hK hKH 1 (σ₀ := (N₀ : ℝ≥0)) hN₀
    ENNReal.coe_lt_top halive
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_im hK hKH
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hc
  have h2 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ c := by
    refine eventually_atTop.2 ⟨N, fun n hn => le_trans ?_ hN.le⟩
    gcongr
  filter_upwards [h1, h2, eventually_ge_atTop N₀] with n hn hnc hnN
  refine ⟨⟨ENNReal.coe_lt_top, zero_le, by simp, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · simpa using Ito.exists_isForwardSol_zero (Ito.rpath (regPath γ)) (hKH hz)
  · rw [NNReal.coe_zero, Ito.fwdMap_zero_eq_sub _ (hKH hz)]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact hnc.trans (hcK z hz)
  · exact not_lt.2 (hn.trans (Coupling.safeExitTime_mono le_rfl le_rfl (by exact_mod_cast hnN)))

/-! ### Input (c): the hull at the recorded stop -/

theorem continuous_rpath_regPath (γ : HistorySpace nL nR) : Continuous (Ito.rpath (regPath γ)) :=
  (continuous_regPath γ).comp continuous_real_toNNReal

/-- The hull at the recorded stop along the regularized driver, closed in `ℍ`. -/
def regHull (γ : HistorySpace nL nR) : Set ℂ :=
  closure (fwdHull (Ito.rpath (regPath γ)) (histStop γ)) ∩ (upperHalfPlaneOpens : Set ℂ)

/-- The part of `K` at height at least `1/(j+1)`. -/
def heightSlice (K : Set ℂ) (j : ℕ) : Set ℂ := K ∩ {z | 1 / ((j : ℝ) + 1) ≤ z.im}

theorem isCompact_heightSlice {K : Set ℂ} (hK : IsCompact K) (j : ℕ) : IsCompact (heightSlice K j) :=
  hK.inter_right (isClosed_le continuous_const Complex.continuous_im)

theorem heightSlice_subset_H (K : Set ℂ) (j : ℕ) : heightSlice K j ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le (by positivity) hz.2

/-- **A compact set misses the hull at the stop iff each of its height slices lies in a safe event.** -/
theorem disjoint_regHull_iff {K : Set ℂ} (hK : IsCompact K) (γ : HistorySpace nL nR) :
    Disjoint K (regHull γ) ↔
      ∀ j : ℕ, ∃ n : ℕ, γ ∈ safeHist (heightSlice K j) (1 / ((n : ℝ) + 1)) n := by
  have hW := continuous_rpath_regPath γ
  have hS : (0 : ℝ) ≤ histStop γ := (histStop γ).coe_nonneg
  constructor
  · intro hdis j
    have halive : ∀ z ∈ heightSlice K j,
        ∃ u, IsForwardSol (Ito.rpath (regPath γ)) z (histStop γ) u := by
      intro z hz
      have hzH : z ∈ H := heightSlice_subset_H K j hz
      exact exists_isForwardSol_of_not_mem_fwdHull hS hzH fun hzK =>
        Set.disjoint_left.1 hdis hz.1 ⟨subset_closure hzK, hzH⟩
    exact (eventually_mem_safeHist (isCompact_heightSlice hK j) (heightSlice_subset_H K j)
      halive).exists
  · intro h
    refine Set.disjoint_left.2 fun z hzK hzA => ?_
    have hzH : 0 < z.im := hzA.2
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hzH
    obtain ⟨n, hn⟩ := h j
    have hsafe := isSafeAt_of_mem_safeHist (heightSlice_subset_H K j) (by positivity) hn
    obtain ⟨u, hu⟩ := (hsafe.2.2.2 z ⟨hzK, hj.le⟩).1
    have hzc : z ∈ H \ fwdHull (Ito.rpath (regPath γ)) (histStop γ) :=
      ⟨hzH, Ito.notMem_fwdHull_of_isForwardSol hW hzH hS hu⟩
    obtain ⟨y, hy1, hy2⟩ :=
      mem_closure_iff.1 hzA.1 _ (FwdHolo.isOpen_compl_fwdHull hW hS) hzc
    exact hy1.2 hy2

theorem measurableSet_disjoint_regHull {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {γ : HistorySpace nL nR | Disjoint K (regHull γ)} := by
  have e : {γ : HistorySpace nL nR | Disjoint K (regHull γ)} =
      ⋂ j : ℕ, ⋃ n : ℕ, safeHist (heightSlice K j) (1 / ((n : ℝ) + 1)) n := by
    ext γ
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    exact disjoint_regHull_iff hK γ
  rw [e]
  exact MeasurableSet.iInter fun j => MeasurableSet.iUnion fun n =>
    measurableSet_safeHist (heightSlice_subset_H K j) (by positivity) n

/-- **Input (c) of Aux. lemma 23** (`HasMeasurableHistHull`): the hull at the recorded stop along the regularized
driver is relatively closed in `ℍ`, has measurable avoidance events of compact sets, and is `histHull` on every
continuous history. -/
theorem hasMeasurableHistHull : HasMeasurableHistHull nL nR := by
  refine ⟨regHull, fun K hK => measurableSet_disjoint_regHull hK, fun γ z hz => ⟨?_, hz.2⟩,
    fun γ h => ?_⟩
  · exact (closure_minimal inter_subset_left isClosed_closure) hz.1
  · simp only [regHull, histHull, h.rpath_regPath]
    rfl

/-! ### Input (b): the conditional characteristic functional at the recorded stop -/

/-- The explicit bounded harmonic extension: on `ℍ`, every bounded harmonic extension of the force boundary data at
arbitrary positions is `meanHarmonic` at the clamped positions `min 0 vL`, `max 0 vR`. -/
theorem eq_meanHarmonic_of_isBoundedHarmonicExtension (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u)
    {a : ℂ} (ha : a ∈ H) :
    u a = Ito.meanHarmonic κ ρL ρR (fun i => min 0 (vL i)) (fun i => max 0 (vR i)) a := by
  have hF := Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) vL vR
  have huF : Impl.IsBoundedHarmonicExtension
      (Impl.forceBoundaryData κ (Ito.weightWord ρL ρR) vL vR)
      (Impl.forceJumpSet (Ito.weightWord ρL ρR) vL vR) u := hu
  have h1 := Impl.eqOn_of_isBoundedHarmonicExtension
    (Impl.forceJumpSet_finite (Ito.weightWord ρL ρR) vL vR) hF huF ha
  rw [h1, ← Ito.forceExt_eq_meanHarmonic κ ρL ρR (fun i => min_le_left 0 (vL i))
    (fun i => le_max_left 0 (vR i)) a]
  simp only [Impl.forceExt, min_eq_right (min_le_left (0 : ℝ) _), max_eq_right (le_max_left (0 : ℝ) _)]

/-- A process on the history space measurable at each time is adapted to the constant filtration. -/
theorem adaptedBefore_of_measurable {X : ℝ≥0 → HistorySpace nL nR → ℝ} (hX : ∀ t, Measurable (X t)) :
    AdaptedBefore histFiltration (fun _ => ⊤) X := by
  intro t A hA
  have e : {γ : HistorySpace nL nR | (t : ℝ≥0∞) < ⊤ ∧ X t γ ∈ A} = X t ⁻¹' A := by
    ext γ
    simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, mem_preimage]
  rw [e]
  exact hX t hA

/-- The left force coordinates as processes on the history space: the regularized driver plus the clamped centred
position at the stop. -/
def posLProc (i : Fin nL) : ℝ≥0 → HistorySpace nL nR → ℝ :=
  fun t γ => regPath γ t + min 0 (histVL γ i - regPath γ (histStop γ))

/-- The right force coordinates as processes on the history space. -/
def posRProc (i : Fin nR) : ℝ≥0 → HistorySpace nL nR → ℝ :=
  fun t γ => regPath γ t + max 0 (histVR γ i - regPath γ (histStop γ))

theorem measurable_posLProc (i : Fin nL) (t : ℝ≥0) : Measurable (posLProc (nR := nR) i t) :=
  (measurable_regPath_apply t).add
    (measurable_const.min ((measurable_histVL i).sub measurable_regPath_histStop))

theorem measurable_posRProc (i : Fin nR) (t : ℝ≥0) : Measurable (posRProc (nL := nL) i t) :=
  (measurable_regPath_apply t).add
    (measurable_const.max ((measurable_histVR i).sub measurable_regPath_histStop))

theorem continuous_posLProc (i : Fin nL) (γ : HistorySpace nL nR) :
    Continuous fun t => posLProc i t γ :=
  (continuous_regPath γ).add continuous_const

theorem continuous_posRProc (i : Fin nR) (γ : HistorySpace nL nR) :
    Continuous fun t => posRProc i t γ :=
  (continuous_regPath γ).add continuous_const

/-- The tested mean and the energy at the recorded stop along the regularized driver. -/
def regPair (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (φ : ℂ → ℝ) (γ : HistorySpace nL nR) : ℝ × ℝ :=
  ((∫ z, Coupling.meanCan κ ρL ρR (regPath γ) (fun i t => posLProc i t γ)
      (fun i t => posRProc i t γ) (histStop γ) z * φ z),
    loewnerGreenEnergy (Ito.rpath (regPath γ)) (histStop γ) φ)

/-- The pair on the `n`-th safe event of `supp φ`, `(0, 0)` off it. -/
def safePair (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (φ : ℂ → ℝ) (n : ℕ)
    (γ : HistorySpace nL nR) : ℝ × ℝ :=
  if γ ∈ safeHist (tsupport φ) (1 / ((n : ℝ) + 1)) n then regPair κ ρL ρR φ γ else (0, 0)

/-- **On each safe event the tested mean and the energy at the stop are measurable** (`measurable_stoppedPair` on the
canonical space). -/
theorem measurable_safePair (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {φ : ℂ → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφH : tsupport φ ⊆ H) (n : ℕ) :
    Measurable (safePair (nL := nL) (nR := nR) κ ρL ρR φ n) := by
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h := Coupling.measurable_stoppedPair (κ := κ) (ρL := ρL) (ρR := ρR)
    (𝓖 := histFiltration (nL := nL) (nR := nR)) (ζ := fun _ => ⊤) (W := regProc)
    (VL := posLProc) (VR := posRProc) (G := safeHist (tsupport φ) (1 / ((n : ℝ) + 1)) n)
    adaptedBefore_regProc (fun i => adaptedBefore_of_measurable (measurable_posLProc i))
    (fun i => adaptedBefore_of_measurable (measurable_posRProc i))
    (fun γ _ => continuousOn_regProc γ)
    (fun γ _ => ⟨fun i => (continuous_posLProc i γ).continuousOn,
      fun i => (continuous_posRProc i γ).continuousOn⟩)
    (measurableSet_safeHist hφH hδ n) hφc hφs hφH hδ (ρ := histStop) isStoppingTime_histStop
    (N := n) (σ₀ := fun _ => (n : ℝ≥0)) (fun γ hγ => isSafeAt_of_mem_safeHist hφH hδ hγ)
  exact h.mono (isStoppingTime_histStop.measurableSpace_le) le_rfl

/-- The safe events of `supp φ`. -/
def safeUnion (φ : ℂ → ℝ) : Set (HistorySpace nL nR) :=
  ⋃ n : ℕ, safeHist (tsupport φ) (1 / ((n : ℝ) + 1)) n

theorem exists_safeIdx (φ : ℂ → ℝ) (γ : HistorySpace nL nR) :
    ∃ n : ℕ, γ ∈ safeHist (tsupport φ) (1 / ((n : ℝ) + 1)) n ∨ γ ∉ safeUnion φ := by
  by_cases h : γ ∈ safeUnion φ
  · obtain ⟨n, hn⟩ := mem_iUnion.1 h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr h⟩

/-- The index of the first safe event of `supp φ` containing the history (`0` if there is none). -/
def safeIdx (φ : ℂ → ℝ) (γ : HistorySpace nL nR) : ℕ := Nat.find (exists_safeIdx φ γ)

theorem measurable_safeIdx {φ : ℂ → ℝ} (hφH : tsupport φ ⊆ H) :
    Measurable (safeIdx (nL := nL) (nR := nR) φ) := by
  classical
  refine measurable_find (exists_safeIdx φ) fun k => ?_
  have hU : MeasurableSet (safeUnion (nL := nL) (nR := nR) φ) :=
    MeasurableSet.iUnion fun n => measurableSet_safeHist hφH (by positivity) n
  exact (measurableSet_safeHist hφH (by positivity) k).union hU.compl

theorem mem_safeHist_safeIdx {φ : ℂ → ℝ} {γ : HistorySpace nL nR} (h : γ ∈ safeUnion φ) :
    γ ∈ safeHist (tsupport φ) (1 / ((safeIdx φ γ : ℝ) + 1)) (safeIdx φ γ) := by
  classical
  have hs := Nat.find_spec (exists_safeIdx φ γ)
  rcases hs with hs | hs
  · exact hs
  · exact absurd h hs

/-- `exp(i X − E/2)` of a pair `(X, E)`. -/
def cexpPair (p : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * (p.1 : ℂ) - (((1 / 2 : ℝ) * p.2 : ℝ) : ℂ))

theorem measurable_cexpPair : Measurable cexpPair := by
  unfold cexpPair
  fun_prop

/-- **The Borel version of the conditional characteristic functional**: `exp(i X − E/2)` of the tested mean and the
energy at the stop along the regularized driver, read on the first safe event of `supp φ`. -/
def regCharFun (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (φ : TestOn upperHalfPlaneOpens)
    (γ : HistorySpace nL nR) : ℂ :=
  cexpPair (safePair κ ρL ρR φ (safeIdx φ γ) γ)

theorem measurable_regCharFun (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (φ : TestOn upperHalfPlaneOpens) : Measurable (regCharFun (nL := nL) (nR := nR) κ ρL ρR φ) := by
  have hφH : tsupport φ ⊆ H := φ.tsupport_subset
  have hF : Measurable fun q : HistorySpace nL nR × ℕ => safePair κ ρL ρR φ q.2 q.1 :=
    measurable_from_prod_countable_left fun n =>
      measurable_safePair κ ρL ρR φ.continuous φ.hasCompactSupport hφH n
  have hG : Measurable fun γ : HistorySpace nL nR => (γ, safeIdx (⇑φ) γ) :=
    measurable_id.prodMk (measurable_safeIdx hφH)
  have h2 := hF.comp (g := fun q : HistorySpace nL nR × ℕ => safePair κ ρL ρR φ q.2 q.1)
    (f := fun γ : HistorySpace nL nR => (γ, safeIdx (⇑φ) γ)) hG
  exact measurable_cexpPair.comp (g := cexpPair)
    (f := fun γ : HistorySpace nL nR => safePair κ ρL ρR φ (safeIdx φ γ) γ) h2

/-- On a continuous history the hull along the regularized driver is `histHull`. -/
theorem IsContHist.regHull_eq {γ : HistorySpace nL nR} (h : IsContHist γ) : regHull γ = histHull γ := by
  simp only [regHull, histHull, h.rpath_regPath]
  rfl

/-- **On a continuous history the pair at the stop is the tested coupling mean and the energy** along the history's
driver, with the bounded harmonic extension `histHarm`, whenever `f_S(supp φ) ⊆ ℍ`. -/
theorem IsContHist.regPair_eq (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {φ : ℂ → ℝ}
    {γ : HistorySpace nL nR} (h : IsContHist γ)
    (hpos : ∀ z ∈ tsupport φ, 0 < (fwdMap (histDrive γ) (histStop γ) z).im) :
    regPair κ ρL ρR φ γ =
      ((∫ z, couplingMean κ (histDrive γ) (histStop γ) (histHarm κ ρL ρR γ) z * φ z),
        loewnerGreenEnergy (histDrive γ) (histStop γ) φ) := by
  have hr := h.rpath_regPath
  have hS : regPath γ (histStop γ) = histPath γ (histStop γ) := by rw [h.regPath_eq]
  refine Prod.ext ?_ (by simp only [regPair, hr])
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport φ
  · simp only [Coupling.meanCan, couplingMean, hr]
    congr 2
    rw [eq_meanHarmonic_of_isBoundedHarmonicExtension κ ρL ρR (histHarm_spec κ ρL ρR γ) (hpos z hz)]
    congr 1
    · funext i
      simp only [posLProc, add_sub_cancel_left, hS]
      rfl
    · funext i
      simp only [posRProc, add_sub_cancel_left, hS]
      rfl
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- **Input (b) of Aux. lemma 23** (`HasMeasurableHistCharFun`): `regCharFun` is a Borel functional of the history
that equals the conditional characteristic functional `histCharFun` on every continuous history whose hull misses
`supp φ`. -/
theorem hasMeasurableHistCharFun (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    HasMeasurableHistCharFun κ ρL ρR := by
  refine ⟨regCharFun κ ρL ρR, measurable_regCharFun κ ρL ρR, fun φ γ hγ hdis => ?_⟩
  have hφH : tsupport φ ⊆ H := φ.tsupport_subset
  have hφK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hdis' : Disjoint (tsupport φ) (regHull γ) := by rwa [hγ.regHull_eq]
  have hS : (0 : ℝ) ≤ histStop γ := (histStop γ).coe_nonneg
  have halive : ∀ z ∈ tsupport φ,
      ∃ u, IsForwardSol (Ito.rpath (regPath γ)) z (histStop γ) u := fun z hz =>
    exists_isForwardSol_of_not_mem_fwdHull hS (hφH hz) fun hzK =>
      Set.disjoint_left.1 hdis' hz ⟨subset_closure hzK, hφH hz⟩
  have hU : γ ∈ safeUnion (⇑φ) := mem_iUnion.2 (eventually_mem_safeHist hφK hφH halive).exists
  have hmem := mem_safeHist_safeIdx hU
  have hsafe := isSafeAt_of_mem_safeHist hφH (by positivity) hmem
  have hpos : ∀ z ∈ tsupport φ, 0 < (fwdMap (histDrive γ) (histStop γ) z).im := fun z hz => by
    have h1 := (hsafe.2.2.2 z hz).2
    rw [hγ.rpath_regPath] at h1
    exact lt_of_lt_of_le (by positivity) h1
  simp only [regCharFun, safePair, hmem, ↓reduceIte]
  rw [hγ.regPair_eq κ ρL ρR hpos]
  rfl

/-! ### Aux. lemma 23 at coupling level, with no named input -/

universe u v

/-- **Theorem 2.2's uniqueness in law for an ordered word** (PROVE-SEC2-PATCH4's
`IsIntegratedSLEEvolution.measure_killedState_eq_assembled`), in the form `KilledStateLawUnique` used by the history
arguments. -/
theorem killedStateLawUnique_of_isOrderedForceWord {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    KilledStateLawUnique.{u, v} a xL xR ρL ρR :=
  fun h₁ _ _ _ _ _ _ _ _ _ _ h₂ _ _ _ hA =>
    IsIntegratedSLEEvolution.measure_killedState_eq_assembled ha hF h₁ h₂ hA

/-- **Aux. lemma 23 at coupling level** (Original-hull uniqueness when the finite hull is thin; specification p. 122).
Fix `κ > 0` and an ordered force word. Let `s` be a measurable stopping rule of the killed driving history that gives,
in each coupling, a stopping time `S < ζ` of its driving filtration, and suppose that in the first coupling the
driving trace is almost surely simple on `[0, S]` with `η((0, S]) ⊂ ℍ` and `dim_H(η([0, S]) ∩ ℍ) ≤ d < 2` (the
strict interior dimension bound of Aux. lemma 15). Then any two couplings with the frozen optional hull specification
have the same joint law of the driving history through `S` and the entire field. (`aux23_of_historyMeasurable` with
its three named inputs proved: Theorem 2.2's uniqueness, `hasMeasurableHistCharFun`, `hasMeasurableHistHull`.) -/
theorem map_stopHistory_prod_eq_of_thinTrace {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    {s : HistorySpace nL nR → ℝ≥0} (hs : Measurable s) {d : ℝ} (hd : d < 2)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hS₁ : ∀ hX : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁,
      IsStoppingTime (drivingFiltration P₁ hX) (ruleTime s W₁ VL₁ VR₁ ζ₁))
    (hSζ₁ : ∀ᵐ ω ∂P₁, (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω) : ℝ≥0∞) < ζ₁ ω)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η ∧
      InjOn η (Icc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) ∧
      (∀ t ∈ Ioc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)), η t ∈ H) ∧
      dimH (η '' Icc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) ∩ H) ≤ ENNReal.ofReal d)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (hS₂ : ∀ hX : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂,
      IsStoppingTime (drivingFiltration P₂ hX) (ruleTime s W₂ VL₂ VR₂ ζ₂))
    (hSζ₂ : ∀ᵐ ω ∂P₂, (s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) : ℝ≥0∞) < ζ₂ ω) :
    P₁.map (fun ω => (stopHistory s (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω)) =
      P₂.map (fun ω => (stopHistory s (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω)) :=
  aux23_of_historyMeasurable (killedStateLawUnique_of_isOrderedForceWord hκ ρL ρR hF)
    (hasMeasurableHistCharFun κ ρL ρR) hasMeasurableHistHull hs hd hC₁ hS₁ hSζ₁ htr₁ hC₂ hS₂ hSζ₂

/-- **Aux. lemma 23, "Consequently" (the field-determining function transfers)**. Under the hypotheses of
`map_stopHistory_prod_eq_of_thinTrace`, if in the first (reference) coupling the driving history through `S` is a
Borel function `Φ` of the field, then in every coupling with the optional hull specification the driving history
through `S` is almost surely the same function `Φ` of its field. -/
theorem ae_stopHistory_eq_comp_of_thinTrace {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    {s : HistorySpace nL nR → ℝ≥0} (hs : Measurable s) {d : ℝ} (hd : d < 2)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hS₁ : ∀ hX : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁,
      IsStoppingTime (drivingFiltration P₁ hX) (ruleTime s W₁ VL₁ VR₁ ζ₁))
    (hSζ₁ : ∀ᵐ ω ∂P₁, (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω) : ℝ≥0∞) < ζ₁ ω)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η ∧
      InjOn η (Icc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) ∧
      (∀ t ∈ Ioc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)), η t ∈ H) ∧
      dimH (η '' Icc 0 (s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) ∩ H) ≤ ENNReal.ofReal d)
    {Φ : DistOn upperHalfPlaneOpens → HistorySpace nL nR} (hΦ : Measurable Φ)
    (hdet : ∀ᵐ ω ∂P₁, stopHistory s (killedHistory W₁ VL₁ VR₁ ζ₁ ω) = Φ (h₁ ω))
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (hS₂ : ∀ hX : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂,
      IsStoppingTime (drivingFiltration P₂ hX) (ruleTime s W₂ VL₂ VR₂ ζ₂))
    (hSζ₂ : ∀ᵐ ω ∂P₂, (s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) : ℝ≥0∞) < ζ₂ ω) :
    ∀ᵐ ω ∂P₂, stopHistory s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) = Φ (h₂ ω) := by
  have hlaw := map_stopHistory_prod_eq_of_thinTrace hκ hF hs hd hC₁ hS₁ hSζ₁ htr₁ hC₂ hS₂ hSζ₂
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hm₁ : Measurable fun ω => (stopHistory s (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω) :=
    ((measurable_stopHistory hs).comp (measurable_killedHistory hX₁)).prodMk hC₁.2.1
  have hm₂ : Measurable fun ω => (stopHistory s (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω) :=
    ((measurable_stopHistory hs).comp (measurable_killedHistory hX₂)).prodMk hC₂.2.1
  have hE : MeasurableSet {p : HistorySpace nL nR × DistOn upperHalfPlaneOpens | p.1 = Φ p.2} :=
    measurableSet_eq_fun measurable_fst (hΦ.comp measurable_snd)
  have h1 : ∀ᵐ p ∂(P₁.map fun ω => (stopHistory s (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω)),
      p.1 = Φ p.2 := (ae_map_iff hm₁.aemeasurable hE).2 hdet
  rw [hlaw] at h1
  exact (ae_map_iff hm₂.aemeasurable hE).1 h1

end Sec4

end InteractingSLE
