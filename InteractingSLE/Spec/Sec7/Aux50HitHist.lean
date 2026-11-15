/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Kernel
import InteractingSLE.Spec.Coupling.WholeField9Kernel
import InteractingSLE.Spec.Sec4.HistBorel
import InteractingSLE.WangWu.CouplingVersion
import QuantumZipper.Proofs.GFF.K3.C5KernelMeas

/-!
# Aux. lemma 50 for every `κ < 8`: Borel functionals of the recorded history

Packet PROVE-AUX50B. Specification Aux. lemma 50 (`source/spec/p193-240.md` L816ff., pp. 236–242), last paragraph:
"Before comparing two couplings, fix common measurable versions of (HGV1) under their one common driving marginal […]
This defines Borel path functions once under the common law, and the same functions apply in every coupling with that
marginal. All component Green kernels are likewise measurable functions of the stopped trace."

This file builds these Borel functions of a recorded driving history `γ` (`LawUnique.HistorySpace`), read along the
regularized driver `Sec4.regPath γ` (continuous for every history), at the fixed capacity time `N ∈ ℕ`:

* **label events** (`histLab`): "the compact `C ⊆ ℍ` lies in one complementary component at `N`" (active, or a pocket
  swallowed at one time), through hulls at the rational times (`WholeField.isPocketLabel_iff`); they are Borel
  (`measurableSet_histLab`), from the landed hull-avoidance events `Sec4.measurableSet_disjoint_regHull`;
* the **random set off the labelled rational balls** (`labA`), relatively closed in `ℍ`, with Borel avoidance events
  of every compact set (`measurableSet_disjoint_labA`);
* the **tested mean read from a characteristic functional** (`charMean`): `lim sup_j (j+1) Im G((j+1)⁻¹ φ)(γ)`, the
  derivative at `0` of `c ↦ G(cφ)`; for `G = exp(i c m − c² v/2)` it is `m`;
* the **safe exit rules** of a compact set (`safeRule`), Borel; along a coupling they are stopping times announcing the
  set's swallowing time (`Aux50HitBirth`);
* the **pocket mean** (`pocketMean`): the limit of the tested means at the safe exit rules ("the harmonic limit of
  `m_s` as `s` increases to that pocket's first disconnection time", follow-up note (WF2), C.3);
* the **retained Green energy** `Q_{U_N}(φ)` of the history (`histQ`), Borel (`measurable_histQ`): `V_N(a, b)` is the
  infimum of `G_ℍ(f_q a, f_q b)` over the admissible times `q ∈ ℚ ∪ {N}` (QuantumZipper's `VTe_eq_iInf_countable`),
  and the flow is jointly measurable in the point and the path (`WangWu.measurable_fwdMap_alivePath`);
* the **kernel value** (`kerFun`): `exp(i M − Q/2)` with `M` the limit of the sums of the label means over the pieces
  of a fine partition of unity (`totMean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Aux50Hit

open LawUnique Sec4 QuantumZipper LQGMetric WholeField

variable {nL nR : ℕ}

/-! ### Stopping a history at a constant time -/

section Stop

/-- The constant stopping rule `s`. -/
def cstop (s : ℝ≥0) : HistorySpace nL nR → ℝ≥0 := fun _ => s

theorem measurable_cstop (s : ℝ≥0) : Measurable (cstop (nL := nL) (nR := nR) s) := measurable_const

/-- Stopping at `s ≤ N` after stopping at `N` is stopping at `s`. -/
theorem stopHistory_cstop_natStop {s : ℝ≥0} {N : ℕ} (hs : s ≤ N) (γ : HistorySpace nL nR) :
    stopHistory (cstop s) (stopHistory (natStop N) γ) = stopHistory (cstop s) γ := by
  refine Prod.ext rfl (funext fun p => ?_)
  simp only [stopHistory, cstop, natStop]
  by_cases hp : dyadicTime p ≤ s
  · simp only [hp, ↓reduceIte, hp.trans hs]
  · simp only [hp, ↓reduceIte]

/-- Stopping at a rule `s ≤ N` after stopping at `N` is stopping at the composed rule. -/
theorem stopHistory_stopHistory_natStop {s : HistorySpace nL nR → ℝ≥0} {N : ℕ} (γ : HistorySpace nL nR)
    (hs : s (stopHistory (natStop N) γ) ≤ N) :
    stopHistory s (stopHistory (natStop N) γ) = stopHistory (fun γ' => s (stopHistory (natStop N) γ')) γ := by
  refine Prod.ext rfl (funext fun p => ?_)
  show (if dyadicTime p ≤ s (stopHistory (natStop N) γ) then (stopHistory (natStop N) γ).2 p else 0) =
    (if dyadicTime p ≤ s (stopHistory (natStop N) γ) then γ.2 p else 0)
  split_ifs with hp
  · exact stopHistory_snd_of_le (s := natStop N) (hp.trans hs)
  · rfl

end Stop

/-! ### Label events of a history -/

section Label

/-- **`C` lies in the hull at the recorded stop** is a Borel event of the history, for compact `C ⊆ ℍ` (the hull is
relatively closed in `ℍ`, so it is checked on a countable dense subset). -/
theorem measurableSet_subset_regHull {C : Set ℂ} (hCH : C ⊆ H) :
    MeasurableSet {γ : HistorySpace nL nR | C ⊆ regHull γ} := by
  obtain ⟨D, hDC, hDc, hCD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace C).exists_countable_dense_subset
  have e : {γ : HistorySpace nL nR | C ⊆ regHull γ} =
      ⋂ z ∈ D, {γ : HistorySpace nL nR | Disjoint {z} (regHull γ)}ᶜ := by
    ext γ
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, Set.disjoint_singleton_left, not_not]
    constructor
    · intro h z hz
      exact h (hDC hz)
    · intro h z hz
      have hzc : z ∈ closure (regHull γ) := closure_mono (fun y hy => h y hy) (hCD hz)
      have hcl : closure (regHull γ) ∩ (upperHalfPlaneOpens : Set ℂ) ⊆ regHull γ := fun y hy =>
        ⟨(closure_minimal inter_subset_left isClosed_closure) hy.1, hy.2⟩
      exact hcl ⟨hzc, hCH hz⟩
  rw [e]
  exact MeasurableSet.biInter hDc fun z _ => (measurableSet_disjoint_regHull isCompact_singleton).compl

/-- The rational intermediate times `min q N` of the label events. -/
def ratTime (N : ℕ) (q : ℚ) : ℝ≥0 := min (q : ℝ).toNNReal (N : ℝ≥0)

theorem ratTime_le (N : ℕ) (q : ℚ) : ratTime N q ≤ N := min_le_right _ _

/-- **The label event of a history** at the integer time `N`: `C` misses the hull at `N` (active), or `C` lies in
the hull at `N` and, at every rational time `q ∧ N`, lies inside or outside the hull (a pocket swallowed at one time,
`WholeField.isPocketLabel_iff`). Hulls are read along the regularized driver of the history stopped at that time. -/
def histLab (N : ℕ) (C : Set ℂ) (γ : HistorySpace nL nR) : Prop :=
  Disjoint C (regHull (stopHistory (cstop N) γ)) ∨
    (C ⊆ regHull (stopHistory (cstop N) γ) ∧
      ∀ q : ℚ, C ⊆ regHull (stopHistory (cstop (ratTime N q)) γ) ∨
        Disjoint C (regHull (stopHistory (cstop (ratTime N q)) γ)))

theorem measurableSet_histLab (N : ℕ) {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    MeasurableSet {γ : HistorySpace nL nR | histLab N C γ} := by
  have hst : ∀ s : ℝ≥0, Measurable (stopHistory (nL := nL) (nR := nR) (cstop s)) := fun s =>
    measurable_stopHistory (measurable_cstop s)
  have hdis : ∀ s : ℝ≥0, MeasurableSet {γ : HistorySpace nL nR | Disjoint C (regHull (stopHistory (cstop s) γ))} :=
    fun s => (hst s) (measurableSet_disjoint_regHull hC)
  have hsub : ∀ s : ℝ≥0, MeasurableSet {γ : HistorySpace nL nR | C ⊆ regHull (stopHistory (cstop s) γ)} :=
    fun s => (hst s) (measurableSet_subset_regHull hCH)
  have e : {γ : HistorySpace nL nR | histLab N C γ} =
      {γ | Disjoint C (regHull (stopHistory (cstop N) γ))} ∪
        ({γ | C ⊆ regHull (stopHistory (cstop N) γ)} ∩
          ⋂ q : ℚ, ({γ | C ⊆ regHull (stopHistory (cstop (ratTime N q)) γ)} ∪
            {γ | Disjoint C (regHull (stopHistory (cstop (ratTime N q)) γ))})) := by
    ext γ
    simp only [histLab, mem_ofPred_eq, mem_union, mem_inter_iff, mem_iInter]
  rw [e]
  exact (hdis _).union ((hsub _).inter (MeasurableSet.iInter fun q => (hsub _).union (hdis _)))

/-- The label event of the rational ball `q` (empty unless the ball is good). -/
def ballLab (N : ℕ) (q : ℚ × ℚ × ℚ) : Set (HistorySpace nL nR) :=
  {γ | IsGoodBall q ∧ histLab N (closedBall (qCentre q) (qRad q)) γ}

theorem measurableSet_ballLab (N : ℕ) (q : ℚ × ℚ × ℚ) : MeasurableSet (ballLab (nL := nL) (nR := nR) N q) := by
  by_cases hq : IsGoodBall q
  · have e : ballLab (nL := nL) (nR := nR) N q = {γ | histLab N (closedBall (qCentre q) (qRad q)) γ} := by
      ext γ; simp only [ballLab, mem_ofPred_eq, hq, true_and]
    rw [e]
    exact measurableSet_histLab N (isCompact_closedBall _ _) hq.2
  · have e : ballLab (nL := nL) (nR := nR) N q = ∅ := by
      ext γ; simp only [ballLab, mem_ofPred_eq, hq, false_and, mem_empty_iff_false]
    rw [e]
    exact MeasurableSet.empty

/-- **The set off the labelled rational balls** of a history at `N`: `ℍ` minus the union of the open rational balls
whose closures are labels. Along a coupling with a continuous trace it lies in the trace (`offLabels_subset_image`). -/
def labA (N : ℕ) (γ : HistorySpace nL nR) : Set ℂ := offLabels (ballLab N) γ

theorem labA_subset_H (N : ℕ) (γ : HistorySpace nL nR) : labA N γ ⊆ H := fun _ hz => hz.1

/-- `labA` is relatively closed in `ℍ`. -/
theorem closure_labA_inter_subset (N : ℕ) (γ : HistorySpace nL nR) :
    closure (labA N γ) ∩ (upperHalfPlaneOpens : Set ℂ) ⊆ labA N γ := by
  intro z ⟨hzc, hzH⟩
  refine ⟨hzH, fun hzU => ?_⟩
  have hU : IsOpen (⋃ q ∈ {q | γ ∈ ballLab (nL := nL) (nR := nR) N q}, ball (qCentre q) (qRad q)) :=
    isOpen_biUnion fun _ _ => isOpen_ball
  obtain ⟨y, hyU, hyA⟩ := mem_closure_iff.1 hzc _ hU hzU
  exact hyA.2 hyU

/-- **Avoidance events of `labA` are Borel**, for every compact set (not only those inside `ℍ`: `labA ⊆ ℍ`, so it is
enough to avoid each height slice). -/
theorem measurableSet_disjoint_labA (N : ℕ) {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {γ : HistorySpace nL nR | Disjoint K (labA N γ)} := by
  have e : {γ : HistorySpace nL nR | Disjoint K (labA N γ)} =
      ⋂ j : ℕ, {γ : HistorySpace nL nR | Disjoint (heightSlice K j) (labA N γ)} := by
    ext γ
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h j
      exact h.mono_left inter_subset_left
    · intro h
      refine Set.disjoint_left.2 fun z hzK hzA => ?_
      have hzH : 0 < z.im := labA_subset_H N γ hzA
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hzH
      exact Set.disjoint_left.1 (h j) ⟨hzK, hj.le⟩ hzA
  rw [e]
  exact MeasurableSet.iInter fun j => measurableSet_disjoint_offLabels (measurableSet_ballLab N)
    (isCompact_heightSlice hK j) (heightSlice_subset_H K j)

end Label

/-! ### The tested mean read from a characteristic functional -/

section Mean

/-- **The tested mean read from a characteristic functional** `G`: `lim sup_j (j+1) Im G((j+1)⁻¹ φ)`. For
`G(cφ) = exp(i c m − c² v/2)` this is `m` (`charMean_eq`). -/
def charMean (G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ) (φ : TestOn upperHalfPlaneOpens)
    (γ : HistorySpace nL nR) : ℝ :=
  limsup (fun j : ℕ => ((j : ℝ) + 1) * (G ((1 / ((j : ℝ) + 1)) • φ) γ).im) atTop

theorem measurable_charMean {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ}
    (hG : ∀ φ, Measurable (G φ)) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (charMean G φ) :=
  Measurable.limsup fun _ => measurable_const.mul (Complex.measurable_im.comp (hG _))

/-- The imaginary part of a Gaussian characteristic value. -/
theorem im_gaussCF (a q : ℝ) : (WangWu.gaussCF a q).im = Real.exp (-((1 / 2) * q)) * Real.sin a := by
  unfold WangWu.gaussCF
  rw [show Complex.I * (a : ℂ) - (((1 / 2 : ℝ) * q : ℝ) : ℂ) =
      ((-((1 / 2) * q) : ℝ) : ℂ) + (a : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- `(j+1) e^{−v/(2(j+1)²)} sin(m/(j+1)) → m`. -/
theorem tendsto_succ_mul_im_gaussCF (m v : ℝ) :
    Tendsto (fun j : ℕ => ((j : ℝ) + 1) *
      (WangWu.gaussCF ((1 / ((j : ℝ) + 1)) * m) ((1 / ((j : ℝ) + 1)) ^ 2 * v)).im) atTop (𝓝 m) := by
  have hc : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hexp : Tendsto (fun j : ℕ => Real.exp (-((1 / 2) * ((1 / ((j : ℝ) + 1)) ^ 2 * v)))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun j : ℕ => -((1 / 2) * ((1 / ((j : ℝ) + 1)) ^ 2 * v))) atTop (𝓝 0) := by
      have := ((hc.pow 2).mul_const v).const_mul (1 / 2 : ℝ)
      simpa using this.neg
    have h1 := (Real.continuous_exp.tendsto 0).comp h0
    rw [Real.exp_zero] at h1
    exact h1
  have hsin : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * Real.sin ((1 / ((j : ℝ) + 1)) * m)) atTop (𝓝 m) := by
    refine (Coupling.MartMeans.tendsto_inv_mul_sin m).congr fun j => ?_
    rw [one_div, inv_inv]
  have hmul := hexp.mul hsin
  rw [one_mul] at hmul
  refine hmul.congr fun j => ?_
  rw [im_gaussCF]
  ring

/-- **The tested mean from Gaussian characteristic values**: if `G((j+1)⁻¹ φ)(γ) = exp(i m/(j+1) − v/(2(j+1)²))` for
every `j`, then `charMean G φ γ = m`. -/
theorem charMean_eq {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ} {φ : TestOn upperHalfPlaneOpens}
    {γ : HistorySpace nL nR} {m v : ℝ}
    (h : ∀ j : ℕ, G ((1 / ((j : ℝ) + 1)) • φ) γ =
      WangWu.gaussCF ((1 / ((j : ℝ) + 1)) * m) ((1 / ((j : ℝ) + 1)) ^ 2 * v)) :
    charMean G φ γ = m := by
  unfold charMean
  simp only [h]
  exact (tendsto_succ_mul_im_gaussCF m v).limsup_eq

end Mean


/-! ### The safe exit rules of a compact set -/

section Safe

/-- The safe condition along the regularized driver at a fixed time is a Borel event of the history (any bounds;
`Sec4.measurableSet_isSafeAt_regPath` with general `N` and `σ₀`). -/
theorem measurableSet_isSafeAt_regPath' {K : Set ℂ} (hKH : K ⊆ H) {δ : ℝ} (hδ : 0 < δ) (Nb : ℝ) (σ₀ : ℝ≥0)
    (d : ℝ≥0) :
    MeasurableSet {γ : HistorySpace nL nR | Coupling.IsSafeAt K δ Nb σ₀ ⊤ (regPath γ) d} := by
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hst : IsStoppingTime (histFiltration (nL := nL) (nR := nR))
      fun _ => ((σ₀ : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have h := Coupling.measurableSet_isSafeAt (𝓖 := histFiltration (nL := nL) (nR := nR))
    (ζ := fun _ => ⊤) (W := regProc) (G := univ) adaptedBefore_regProc
    (fun γ _ => continuousOn_regProc γ) MeasurableSet.univ hDc (hDK.trans hKH)
    (σ₀ := fun _ => σ₀) hst δ Nb d
  rw [histFiltration_apply] at h
  convert h using 1
  ext γ
  simp only [mem_ofPred_eq, mem_univ, true_and]
  constructor
  · intro h'
    exact h'.subset hDK
  · intro h'
    exact h'.of_dense (continuousOn_regProc γ) hKH hKD hDK hδ

/-- **The safe exit rule** of a compact `K ⊆ ℍ` at level `k` and horizon `N` (lower height bound `m`): the safe exit
time `inf{t : K is not alive at height ≥ m/(k+1), or t > N}` along the regularized driver. -/
def safeRule (K : Set ℂ) (m : ℝ) (N k : ℕ) (γ : HistorySpace nL nR) : ℝ≥0 :=
  Coupling.safeExitTime K (m / ((k : ℝ) + 1)) k N ⊤ (regPath γ)

theorem measurable_safeRule {K : Set ℂ} (hKH : K ⊆ H) {m : ℝ} (hm : 0 < m) (N k : ℕ) :
    Measurable (safeRule (nL := nL) (nR := nR) K m N k) := by
  refine measurable_of_Iio fun t => ?_
  have e : safeRule (nL := nL) (nR := nR) K m N k ⁻¹' Iio t =
      ⋃ p : ℕ × ℕ, {_γ : HistorySpace nL nR | dyadicTime p < t} ∩
        {γ | Coupling.IsSafeAt K (m / ((k : ℝ) + 1)) k N ⊤ (regPath γ) (dyadicTime p)}ᶜ := by
    ext γ
    have hiff := Coupling.safeExitTime_lt_iff (K := K) (δ := m / ((k : ℝ) + 1)) (N := k) (σ₀ := N) (ζ := ⊤)
      (w := regPath γ) (continuous_regPath γ).continuousOn hKH dense_range_dyadicTime (t := t)
    simp only [safeRule, mem_preimage, mem_Iio, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_compl_iff,
      hiff, exists_range_iff]
  rw [e]
  exact MeasurableSet.iUnion fun p => (MeasurableSet.const _).inter
    (measurableSet_isSafeAt_regPath' hKH (by positivity) _ _ _).compl

theorem safeRule_le (K : Set ℂ) (m : ℝ) (N k : ℕ) (γ : HistorySpace nL nR) : safeRule K m N k γ ≤ N :=
  Coupling.safeExitTime_le_sigma

/-- **The pocket mean of a history**: the limit (as `lim sup`) of the tested means read from `G` along the history
stopped at the safe exit rules of `K`. -/
def pocketMean (G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ) (K : Set ℂ) (m : ℝ) (N : ℕ)
    (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR) : ℝ :=
  limsup (fun k : ℕ => charMean G φ (stopHistory (safeRule K m N k) γ)) atTop

theorem measurable_pocketMean {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ}
    (hG : ∀ φ, Measurable (G φ)) {K : Set ℂ} (hKH : K ⊆ H) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (φ : TestOn upperHalfPlaneOpens) : Measurable (pocketMean G K m N φ) :=
  Measurable.limsup fun k => (measurable_charMean hG φ).comp
    (measurable_stopHistory (measurable_safeRule hKH hm N k))

end Safe

/-! ### The retained Green energy of a history -/

section Green

/-- The path of a history on `[0, s]`, as a continuous map (QuantumZipper's path space). -/
def histCPath (s : ℝ≥0) : HistorySpace nL nR → C(Icc (0 : ℝ) s, ℝ) :=
  Ito.drvPathMap regProc (fun _ => ⊤) univ (fun γ _ => continuousOn_regProc γ) s

theorem measurable_histCPath (s : ℝ≥0) :
    @Measurable (HistorySpace nL nR) C(Icc (0 : ℝ) s, ℝ) _ (borel _) (histCPath s) := by
  have h := Ito.measurable_drvPathMap (𝓖 := histFiltration (nL := nL) (nR := nR)) (ζ := fun _ => ⊤)
    (W := regProc) (G := univ) adaptedBefore_regProc (fun γ _ => continuousOn_regProc γ) MeasurableSet.univ s
  rwa [histFiltration_apply] at h

theorem eqOn_histCPath (s : ℝ≥0) (γ : HistorySpace nL nR) :
    EqOn (extIccPath s.coe_nonneg (histCPath s γ)) (Ito.rpath (regPath γ)) (Icc 0 (s : ℝ)) :=
  Ito.extIccPath_drvPathMap_eqOn (fun γ _ => continuousOn_regProc γ) ⟨mem_univ γ, ENNReal.coe_lt_top⟩

theorem fwdHull_histCPath (s : ℝ≥0) (γ : HistorySpace nL nR) :
    fwdHull (extIccPath s.coe_nonneg (histCPath s γ)) s = fwdHull (Ito.rpath (regPath γ)) s :=
  YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_extIccPath _ _) (continuous_rpath_regPath γ)
    s.coe_nonneg fun _ hr => eqOn_histCPath s γ hr

/-- The pairs (history, point) alive at time `s` along the regularized driver. -/
def aliveH (s : ℝ≥0) : Set (HistorySpace nL nR × ℂ) := {p | p.2 ∈ H \ fwdHull (Ito.rpath (regPath p.1)) s}

theorem measurableSet_aliveH (s : ℝ≥0) : MeasurableSet (aliveH (nL := nL) (nR := nR) s) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) s, ℝ) := borel _
  have _ : BorelSpace C(Icc (0 : ℝ) s, ℝ) := ⟨rfl⟩
  have e : aliveH (nL := nL) (nR := nR) s =
      (fun p : HistorySpace nL nR × ℂ => (p.2, histCPath s p.1)) ⁻¹' WangWu.alivePath s.coe_nonneg := by
    ext p
    simp only [aliveH, WangWu.alivePath, mem_ofPred_eq, mem_preimage, fwdHull_histCPath]
  rw [e]
  exact (measurable_snd.prodMk ((measurable_histCPath s).comp measurable_fst))
    (WangWu.measurableSet_alivePath s.coe_nonneg)

/-- The forward map at time `s` along the regularized driver, on the alive pairs, is jointly Borel. -/
theorem measurable_fwdMap_aliveH (s : ℝ≥0) :
    Measurable ((aliveH (nL := nL) (nR := nR) s).indicator
      fun p => fwdMap (Ito.rpath (regPath p.1)) s p.2) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) s, ℝ) := borel _
  have _ : BorelSpace C(Icc (0 : ℝ) s, ℝ) := ⟨rfl⟩
  have hm := (WangWu.measurable_fwdMap_alivePath (s := (s : ℝ)) s.coe_nonneg).comp
    (measurable_snd.prodMk ((measurable_histCPath s).comp measurable_fst) :
      Measurable fun p : HistorySpace nL nR × ℂ => (p.2, histCPath s p.1))
  convert hm using 1
  funext p
  by_cases hp : p ∈ aliveH (nL := nL) (nR := nR) s
  · have hp' : (p.2, histCPath s p.1) ∈ WangWu.alivePath s.coe_nonneg := by
      show p.2 ∈ H \ fwdHull _ s
      rw [fwdHull_histCPath]; exact hp
    simp only [Function.comp_apply, indicator_of_mem hp', indicator_of_mem hp]
    exact Ito.fwdMap_congr_of_eqOn (eqOn_histCPath s p.1) |>.symm
  · have hp' : (p.2, histCPath s p.1) ∉ WangWu.alivePath s.coe_nonneg := by
      show p.2 ∉ H \ fwdHull _ s
      rw [fwdHull_histCPath]; exact hp
    simp only [Function.comp_apply, indicator_of_notMem hp', indicator_of_notMem hp]

/-- The fixed-time Green kernel `G_ℍ(f_q a, f_q b)` on the admissible triples, `⊤` elsewhere. -/
def vtKerH (T q : ℝ) (x : HistorySpace nL nR × ℂ × ℂ) : ℝ≥0∞ :=
  if 0 ≤ q ∧ q ≤ T ∧ (x.1, x.2.1) ∈ aliveH (nL := nL) (nR := nR) q.toNNReal ∧
      (x.1, x.2.2) ∈ aliveH (nL := nL) (nR := nR) q.toNNReal then
    ENNReal.ofReal (greenH (fwdMap (Ito.rpath (regPath x.1)) (q.toNNReal : ℝ) x.2.1)
      (fwdMap (Ito.rpath (regPath x.1)) (q.toNNReal : ℝ) x.2.2))
  else ⊤

theorem measurable_vtKerH (T q : ℝ) : Measurable (vtKerH (nL := nL) (nR := nR) T q) := by
  set s : ℝ≥0 := q.toNNReal
  set S : Set (HistorySpace nL nR × ℂ × ℂ) := {_x | 0 ≤ q ∧ q ≤ T} ∩
    ((fun x : HistorySpace nL nR × ℂ × ℂ => (x.1, x.2.1)) ⁻¹' aliveH s ∩
      (fun x : HistorySpace nL nR × ℂ × ℂ => (x.1, x.2.2)) ⁻¹' aliveH s) with hSdef
  have hm1 : Measurable fun x : HistorySpace nL nR × ℂ × ℂ => (x.1, x.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm2 : Measurable fun x : HistorySpace nL nR × ℂ × ℂ => (x.1, x.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hS : MeasurableSet S := (MeasurableSet.const _).inter
    ((hm1 (measurableSet_aliveH s)).inter (hm2 (measurableSet_aliveH s)))
  set F : HistorySpace nL nR × ℂ → ℂ := (aliveH (nL := nL) (nR := nR) s).indicator
    fun p => fwdMap (Ito.rpath (regPath p.1)) s p.2 with hFdef
  have hF : Measurable F := measurable_fwdMap_aliveH s
  have e : vtKerH (nL := nL) (nR := nR) T q = S.piecewise
      (fun x => ENNReal.ofReal (greenH (F (x.1, x.2.1)) (F (x.1, x.2.2)))) fun _ => ⊤ := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      obtain ⟨⟨hq0, hqT⟩, h1, h2⟩ := hx
      have h1' : (x.1, x.2.1) ∈ aliveH (nL := nL) (nR := nR) s := h1
      have h2' : (x.1, x.2.2) ∈ aliveH (nL := nL) (nR := nR) s := h2
      simp only [vtKerH, hFdef]
      rw [ite_eq_left ⟨hq0, hqT, h1', h2'⟩, indicator_of_mem h1', indicator_of_mem h2']
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      simp only [vtKerH]
      rw [ite_eq_right fun h => hx ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩]
  rw [e]
  exact Measurable.piecewise hS (ENNReal.measurable_ofReal.comp
    (measurable_greenH.comp ((hF.comp hm1).prodMk (hF.comp hm2)))) measurable_const

/-- `V_T` along the regularized driver as an infimum of the fixed-time kernels over `ℚ ∪ {T}`. -/
theorem VTe_eq_iInf_vtKerH (T : ℝ) (γ : HistorySpace nL nR) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) :
    K3.VTe (Ito.rpath (regPath γ)) T a b = ⨅ q ∈ K3.vtQ T, vtKerH T q (γ, a, b) := by
  rw [K3.VTe_eq_iInf_countable (continuous_rpath_regPath γ) ha hb]
  refine le_antisymm (le_iInf₂ fun q hq => ?_) (le_iInf₂ fun q hq => ?_)
  · unfold vtKerH
    split_ifs with h
    · obtain ⟨hq0, hqT, h1, h2⟩ := h
      have hqq : ((q.toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal q hq0
      have hmem : q ∈ K3.vtQ T ∩ K3.vtIdx (Ito.rpath (regPath γ)) T a b := by
        refine ⟨hq, hq0, hqT, ?_, ?_⟩
        · exact not_le.1 fun hle => h1.2 ⟨ha, by rw [hqq]; exact hle⟩
        · exact not_le.1 fun hle => h2.2 ⟨hb, by rw [hqq]; exact hle⟩
      refine (iInf₂_le q hmem).trans (le_of_eq ?_)
      simp only [K3.vtKer, hqq]
    · exact le_top
  · obtain ⟨hqQ, hq0, hqT, ha', hb'⟩ := hq
    have hqq : ((q.toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal q hq0
    refine (iInf₂_le q hqQ).trans (le_of_eq ?_)
    have h1 : (γ, a) ∈ aliveH (nL := nL) (nR := nR) q.toNNReal :=
      ⟨ha, fun h => (not_le.2 ha') (by have := h.2; rwa [hqq] at this)⟩
    have h2 : (γ, b) ∈ aliveH (nL := nL) (nR := nR) q.toNNReal :=
      ⟨hb, fun h => (not_le.2 hb') (by have := h.2; rwa [hqq] at this)⟩
    simp only [vtKerH]
    rw [ite_eq_left ⟨hq0, hqT, h1, h2⟩, hqq]
    rfl

/-- **`V_T` along the regularized driver is jointly Borel** in the history and the two points (on `ℍ × ℍ`). -/
theorem measurable_VTeH (T : ℝ) :
    Measurable fun x : HistorySpace nL nR × ℂ × ℂ =>
      ({x : HistorySpace nL nR × ℂ × ℂ | x.2.1 ∈ H ∧ x.2.2 ∈ H}).indicator
        (fun x => K3.VTe (Ito.rpath (regPath x.1)) T x.2.1 x.2.2) x := by
  have hset : MeasurableSet {x : HistorySpace nL nR × ℂ × ℂ | x.2.1 ∈ H ∧ x.2.2 ∈ H} :=
    ((measurable_fst.comp measurable_snd) isOpen_H.measurableSet).inter
      ((measurable_snd.comp measurable_snd) isOpen_H.measurableSet)
  have e : ({x : HistorySpace nL nR × ℂ × ℂ | x.2.1 ∈ H ∧ x.2.2 ∈ H}).indicator
      (fun x => K3.VTe (Ito.rpath (regPath x.1)) T x.2.1 x.2.2) =
      ({x : HistorySpace nL nR × ℂ × ℂ | x.2.1 ∈ H ∧ x.2.2 ∈ H}).indicator
        (fun x => ⨅ q ∈ K3.vtQ T, vtKerH T q x) :=
    indicator_congr fun x hx => VTe_eq_iInf_vtKerH T x.1 hx.1 hx.2
  rw [e]
  exact (Measurable.biInf _ (K3.countable_vtQ T) fun q _ => measurable_vtKerH T q).indicator hset

/-- **The retained Green energy of a history at `N`**: `Q_{U_N}(φ)` along the regularized driver. -/
def histQ (N : ℕ) (φ : ℂ → ℝ) (γ : HistorySpace nL nR) : ℝ := WangWu.retainedGreenEnergy (regPath γ) N φ

theorem measurable_histQ (N : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (histQ (nL := nL) (nR := nR) N φ) := by
  set g : (HistorySpace nL nR × ℂ) × ℂ → ℝ := fun x => φ x.1.2 *
    (({x : HistorySpace nL nR × ℂ × ℂ | x.2.1 ∈ H ∧ x.2.2 ∈ H}).indicator
      (fun x => K3.VTe (Ito.rpath (regPath x.1)) ((N : ℝ≥0) : ℝ) x.2.1 x.2.2)
        (x.1.1, x.1.2, x.2)).toReal * φ x.2 with hgdef
  have hg : Measurable g := by
    have hφ : Measurable (φ : ℂ → ℝ) := φ.continuous.measurable
    have hm : Measurable fun x : (HistorySpace nL nR × ℂ) × ℂ => (x.1.1, x.1.2, x.2) :=
      (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact ((hφ.comp (measurable_snd.comp measurable_fst)).mul
      (ENNReal.measurable_toReal.comp ((measurable_VTeH _).comp hm))).mul (hφ.comp measurable_snd)
  have e : histQ (nL := nL) (nR := nR) N φ = fun γ => ∫ a, ∫ b, g ((γ, a), b) := by
    funext γ
    unfold histQ WangWu.retainedGreenEnergy
    refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae
      (Eventually.of_forall fun b => ?_))
    show φ a * WangWu.retainedGreen (regPath γ) N a b * φ b = g ((γ, a), b)
    by_cases hab : a ∈ H ∧ b ∈ H
    · simp only [hgdef, indicator_of_mem (show ((γ, a, b) : HistorySpace nL nR × ℂ × ℂ) ∈
        {x : HistorySpace nL nR × ℂ × ℂ | x.2.1 ∈ H ∧ x.2.2 ∈ H} from hab)]
      rfl
    · rcases not_and_or.1 hab with ha | hb
      · simp [hgdef, testOn_eq_zero_of_notMem_H φ ha]
      · simp [hgdef, testOn_eq_zero_of_notMem_H φ hb]
  rw [e]
  exact (hg.stronglyMeasurable.integral_prod_right'.integral_prod_right').measurable

end Green

/-! ### The kernel value of a history -/

section Kernel

/-- A positive lower bound for the heights of the support of a test function. -/
def testLow (ψ : TestOn upperHalfPlaneOpens) : ℝ :=
  Classical.choose (exists_pos_le_im_of_isCompact' ψ.hasCompactSupport.isCompact ψ.tsupport_subset)

theorem testLow_pos (ψ : TestOn upperHalfPlaneOpens) : 0 < testLow ψ :=
  (Classical.choose_spec (exists_pos_le_im_of_isCompact' ψ.hasCompactSupport.isCompact ψ.tsupport_subset)).1

theorem testLow_le (ψ : TestOn upperHalfPlaneOpens) {z : ℂ} (hz : z ∈ tsupport ψ) : testLow ψ ≤ z.im :=
  (Classical.choose_spec (exists_pos_le_im_of_isCompact' ψ.hasCompactSupport.isCompact ψ.tsupport_subset)).2 z hz

/-- A radius of a closed ball around `0` containing the support of a test function. -/
def testRad (φ : TestOn upperHalfPlaneOpens) : ℝ :=
  Classical.choose (φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0)

theorem tsupport_subset_testRad (φ : TestOn upperHalfPlaneOpens) : tsupport φ ⊆ closedBall 0 (testRad φ) :=
  Classical.choose_spec (φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0)

/-- **The label mean of a history at `N`**: the active mean if the support misses the hull at `N`, the pocket mean
otherwise. -/
def labelMean (G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ) (N : ℕ) (ψ : TestOn upperHalfPlaneOpens)
    (γ : HistorySpace nL nR) : ℝ :=
  if Disjoint (tsupport ψ) (regHull (stopHistory (cstop N) γ)) then charMean G ψ (stopHistory (cstop N) γ)
  else pocketMean G (tsupport ψ) (testLow ψ) N ψ γ

theorem measurable_labelMean {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ}
    (hG : ∀ φ, Measurable (G φ)) (N : ℕ) (ψ : TestOn upperHalfPlaneOpens) :
    Measurable (labelMean G N ψ) :=
  Measurable.ite ((measurable_stopHistory (measurable_cstop _)) (measurableSet_disjoint_regHull
      ψ.hasCompactSupport.isCompact))
    ((measurable_charMean hG ψ).comp (measurable_stopHistory (measurable_cstop _)))
    (measurable_pocketMean hG ψ.tsupport_subset (testLow_pos ψ) N ψ)

/-- **The total mean of a history at `N`**: the limit of the sums of the label means over the pieces of the partition
of unity of `φ` at scale `2^{-n}`. -/
def totMean (G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ) (N : ℕ) (φ : TestOn upperHalfPlaneOpens)
    (γ : HistorySpace nL nR) : ℝ :=
  limsup (fun n : ℕ => ∑ k ∈ WangWu.pouIdx (WangWu.scaleIdx (testRad φ) n),
    labelMean G N (WangWu.pouTest φ n k) γ) atTop

theorem measurable_totMean {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ}
    (hG : ∀ φ, Measurable (G φ)) (N : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (totMean G N φ) :=
  Measurable.limsup fun _ => Finset.measurable_sum _ fun _ _ => measurable_labelMean hG N _

/-- **The kernel value of a history at `N`**: `exp(i M − Q/2)` with the total mean `M` and the retained Green energy
`Q` of the history stopped at `N`. -/
def kerFun (G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ) (N : ℕ) (φ : TestOn upperHalfPlaneOpens)
    (γ : HistorySpace nL nR) : ℂ :=
  WangWu.gaussCF (totMean G N φ γ) (histQ N φ (stopHistory (cstop N) γ))

theorem measurable_kerFun {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ}
    (hG : ∀ φ, Measurable (G φ)) (N : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (kerFun G N φ) :=
  WangWu.continuous_gaussCF.measurable.comp ((measurable_totMean hG N φ).prodMk
    ((measurable_histQ N φ).comp (measurable_stopHistory (measurable_cstop _))))

end Kernel

end Aux50Hit

end InteractingSLE
