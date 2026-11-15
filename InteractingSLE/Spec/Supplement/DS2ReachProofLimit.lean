/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofFun

/-!
# DS2 in reach form, VIII: identification of subsequential limits

Packet PROVE-T14-DS (proof of DS2, spec p. 553). Let the joint laws `πₖ` of the stopped state paths and the Brownian
paths of a sequence of evolutions of DS1 words, whose weights and initial positions converge, converge weakly to `π`.
Then `π`-almost surely the limit path satisfies (`LimitProps`):

* it starts at the limiting initial state and is ordered at every time;
* at every time `q` of a fixed countable dense set (`qSet`) up to which it stays in the outer open buffer:
  the linear driver identity with the limiting weights, and for every label the lintegral identity
  `∫₀^q Ginv(gap) = |v(q) − v(0)|/2` (so the reciprocal gap is integrable and the gap vanishes on a null set).

The proof uses only Portmanteau for open sets: the violation sets are open, and their `πₖ`-probabilities vanish or
are bounded through DS1 (Markov's inequality for the occupation integrals) uniformly in `k`; the reciprocal cutoff is
then sent to zero by monotone convergence ("no hidden sticky part").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2
open scoped PathMeas

/-- A fixed countable dense set of times. -/
def qSet : Set ℝ≥0 := (TopologicalSpace.exists_countable_dense ℝ≥0).choose

theorem qSet_countable : qSet.Countable := (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.1

theorem qSet_dense : Dense qSet := (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.2

section Props

variable {nL nR : ℕ}

/-- **The properties of a subsequential limit** `(f, β)` of stopped state paths and Brownian paths. -/
def LimitProps (κ : ℝ) (mL mR : ℕ) (R g : ℝ) (T : ℝ≥0) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR))
    (β : C(Set.Icc (0 : ℝ≥0) T, ℝ)) : Prop :=
  pathAt f 0 = ((0 : ℝ), xL, xR) ∧ (∀ x, IsOrderedState (f x)) ∧
    ∀ q ∈ qSet, q ≤ T → f ∈ upSet mL mR R g q →
      (pathAt f q).1 = Real.sqrt κ * pathAt β q - (∑ i, ρL i / 2 * ((pathAt f q).2.1 i - (pathAt f 0).2.1 i)) -
          ∑ j, ρR j / 2 * ((pathAt f q).2.2 j - (pathAt f 0).2.2 j) ∧
        (∀ j, 0 ≤ (pathAt f q).2.2 j - (pathAt f 0).2.2 j ∧
          ∫⁻ s in Ioc (0 : ℝ) q, Ginv (gapR j (pathAt f s.toNNReal)) =
            ENNReal.ofReal (((pathAt f q).2.2 j - (pathAt f 0).2.2 j) / 2)) ∧
        ∀ i, 0 ≤ (pathAt f 0).2.1 i - (pathAt f q).2.1 i ∧
          ∫⁻ s in Ioc (0 : ℝ) q, Ginv (gapL i (pathAt f s.toNNReal)) =
            ENNReal.ofReal (((pathAt f 0).2.1 i - (pathAt f q).2.1 i) / 2)

end Props

/-! ### The monotone limit of the cutoff integrals -/

section MonoLimit

variable {nL nR : ℕ} {T : ℝ≥0}

/-- If the cutoff integrals `2 ∫₀^q hcut δₙ (gp ∘ f)` (with `δₙ ↓ 0`) are at most `A` and come within any `η > 0` of
`A`, then `∫₀^q Ginv (gp ∘ f) = A/2`. -/
theorem lintegral_Ginv_eq {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hanti : Antitone δ) (hlim : Tendsto δ atTop (𝓝 0))
    {gp : SState nL nR → ℝ} (hgp : Continuous gp) {q : ℝ≥0} {f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)}
    {A : ℝ} (hle : ∀ n, 2 * intH (δ n) gp q f ≤ A)
    (hclose : ∀ k : ℕ, ∃ n, A - 2 * intH (δ n) gp q f ≤ 1 / ((k : ℝ) + 1)) :
    ∫⁻ s in Ioc (0 : ℝ) q, Ginv (gp (pathAt f s.toNNReal)) = ENNReal.ofReal (A / 2) := by
  have hcont : ∀ n, Continuous fun s : ℝ => hcut (δ n) (gp (pathAt f s.toNNReal)) := fun n =>
    (continuous_hcut (hδ n)).comp (hgp.comp ((continuous_pathAt f).comp continuous_real_toNNReal))
  -- the cutoff integrals as lintegrals
  have hlin : ∀ n, ENNReal.ofReal (intH (δ n) gp q f) =
      ∫⁻ s in Ioc (0 : ℝ) q, ENNReal.ofReal (hcut (δ n) (gp (pathAt f s.toNNReal))) := by
    intro n
    unfold intH
    rw [intervalIntegral.integral_of_le q.coe_nonneg, ofReal_integral_eq_lintegral_ofReal]
    · exact (hcont n).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact ae_of_all _ fun s => hcut_nonneg (hδ n) _
  -- monotone convergence
  have hmono : Monotone fun n => fun s : ℝ => ENNReal.ofReal (hcut (δ n) (gp (pathAt f s.toNNReal))) :=
    fun n m hnm s => ENNReal.ofReal_le_ofReal (hcut_anti (hδ m) (hanti hnm) _)
  have hMCT : Tendsto (fun n => ∫⁻ s in Ioc (0 : ℝ) q, ENNReal.ofReal (hcut (δ n) (gp (pathAt f s.toNNReal))))
      atTop (𝓝 (∫⁻ s in Ioc (0 : ℝ) q, Ginv (gp (pathAt f s.toNNReal)))) := by
    have h := lintegral_tendsto_of_tendsto_of_monotone (μ := volume.restrict (Ioc (0 : ℝ) q))
      (f := fun n s => ENNReal.ofReal (hcut (δ n) (gp (pathAt f s.toNNReal))))
      (F := fun s => Ginv (gp (pathAt f s.toNNReal)))
      (fun n => (ENNReal.measurable_ofReal.comp (hcont n).measurable).aemeasurable)
      (ae_of_all _ fun s n m hnm => hmono hnm s)
      (ae_of_all _ fun s => tendsto_ofReal_hcut hδ hlim _)
    exact h
  -- the cutoff integrals converge to `A/2`
  have hA : Tendsto (fun n => intH (δ n) gp q f) atTop (𝓝 (A / 2)) := by
    have hmonoI : Monotone fun n => intH (δ n) gp q f := by
      intro n m hnm
      unfold intH
      refine intervalIntegral.integral_mono_on q.coe_nonneg ((hcont n).intervalIntegrable _ _)
        ((hcont m).intervalIntegrable _ _) fun s _ => hcut_anti (hδ m) (hanti hnm) _
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hη)
    obtain ⟨n, hn⟩ := hclose k
    refine ⟨n, fun m hm => ?_⟩
    have h1 := hmonoI hm
    have h2 := hle m
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp hA
  simp only [Function.comp_def, hlin] at h2
  exact tendsto_nhds_unique hMCT h2

end MonoLimit

/-! ### Violation functionals -/

section Viol

variable {nL nR : ℕ} {T : ℝ≥0}

/-- `(v_j(q) − v_j(0)) − 2 ∫₀^q hcut δ (v_j − w)` (right labels). -/
def psiR (δ : ℝ) (j : Fin nR) (q : ℝ≥0) (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) : ℝ :=
  ((pathAt f q).2.2 j - (pathAt f 0).2.2 j) - 2 * intH δ (gapR j) q f

/-- `(v_i(0) − v_i(q)) − 2 ∫₀^q hcut δ (w − v_i)` (left labels). -/
def psiL (δ : ℝ) (i : Fin nL) (q : ℝ≥0) (f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)) : ℝ :=
  ((pathAt f 0).2.1 i - (pathAt f q).2.1 i) - 2 * intH δ (gapL i) q f

/-- The defect of the linear driver identity at time `q` with weights `(ρL, ρR)`. -/
def phiLin (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (q : ℝ≥0)
    (p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ)) : ℝ :=
  (pathAt p.1 q).1 - (Real.sqrt κ * pathAt p.2 q - (∑ i, ρL i / 2 * ((pathAt p.1 q).2.1 i - (pathAt p.1 0).2.1 i)) -
    ∑ j, ρR j / 2 * ((pathAt p.1 q).2.2 j - (pathAt p.1 0).2.2 j))

theorem continuous_psiR {δ : ℝ} (hδ : 0 < δ) (j : Fin nR) (q : ℝ≥0) :
    Continuous (psiR (T := T) (nL := nL) δ j q) :=
  ((((continuous_apply j).comp (continuous_snd.comp continuous_snd)).comp (continuous_pathAt_const q)).sub
    (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).comp (continuous_pathAt_const 0))).sub
    (continuous_const.mul (continuous_intH hδ (continuous_gapR j) q))

theorem continuous_psiL {δ : ℝ} (hδ : 0 < δ) (i : Fin nL) (q : ℝ≥0) :
    Continuous (psiL (T := T) (nR := nR) δ i q) :=
  ((((continuous_apply i).comp (continuous_fst.comp continuous_snd)).comp (continuous_pathAt_const 0)).sub
    (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).comp (continuous_pathAt_const q))).sub
    (continuous_const.mul (continuous_intH hδ (continuous_gapL i) q))

theorem continuous_phiLin (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (q : ℝ≥0) :
    Continuous (phiLin (T := T) κ ρL ρR q) := by
  have cq : Continuous fun p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) =>
      pathAt p.1 q := (continuous_pathAt_const q).comp continuous_fst
  have c0 : Continuous fun p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) =>
      pathAt p.1 0 := (continuous_pathAt_const 0).comp continuous_fst
  have cb : Continuous fun p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) =>
      pathAt p.2 q := (continuous_pathAt_const q).comp continuous_snd
  unfold phiLin
  refine (continuous_fst.comp cq).sub (((continuous_const.mul cb).sub ?_).sub ?_)
  · exact continuous_finsetSum _ fun i _ => continuous_const.mul
      (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).comp cq |>.sub
        (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).comp c0))
  · exact continuous_finsetSum _ fun j _ => continuous_const.mul
      (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).comp cq |>.sub
        (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).comp c0))

end Viol


/-! ### Estimates for the law of one evolution -/

theorem isOpen_setOf_not_ordered {nL nR : ℕ} {T : ℝ≥0} :
    IsOpen {p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) |
      ¬ ∀ x, IsOrderedState (p.1 x)} := by
  have : {p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) |
      ¬ ∀ x, IsOrderedState (p.1 x)} =
      (⋂ x, (fun p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) => p.1 x) ⁻¹'
        {s | IsOrderedState s})ᶜ := by
    ext p
    simp only [mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact (isClosed_iInter fun x => isClosed_setOf_isOrderedState.preimage
    ((continuous_eval_const x).comp continuous_fst)).isOpen_compl

namespace EvolData

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε R g : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  (D : EvolData κ mL mR Rw ε R g xL xR ρL ρR P W VL VR ζ)

/-- The joint law as a probability measure. -/
def lawP [IsProbabilityMeasure P] (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    ProbabilityMeasure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ)) :=
  ⟨D.law T, D.isProbabilityMeasure_law hε hg T⟩

theorem coe_lawP [IsProbabilityMeasure P] (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    ((D.lawP hε hg T : ProbabilityMeasure _) :
      Measure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))) = D.law T := rfl

theorem law_apply (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0)
    {S : Set (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))} (hS : MeasurableSet S) :
    D.law T S = P ((fun ω => (fR mL mR R g T W VL VR ζ ω, D.bP T ω)) ⁻¹' S) :=
  Measure.map_apply_of_aemeasurable (D.aemeasurable_pair hε hg T) hS

/-- A set of pairs avoided on the good set is null for the law. -/
theorem law_eq_zero_of_good (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0)
    {S : Set (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))} (hS : MeasurableSet S)
    (h : ∀ ω ∈ D.G, (fR mL mR R g T W VL VR ζ ω, D.bP T ω) ∉ S) : D.law T S = 0 := by
  rw [D.law_apply hε hg T hS]
  exact measure_mono_null (fun ω hω hG => h ω hG hω) D.null_G

theorem law_psiR_neg (hε : 0 < ε) (hg : 0 < g) (hnR : 0 < nR) {T q : ℝ≥0} (hqT : q ≤ T) (j : Fin nR)
    {δ : ℝ} (hδ : 0 < δ) :
    D.law T ((upSet mL mR R g q ×ˢ univ) ∩ {p | psiR δ j q p.1 < 0}) = 0 := by
  refine D.law_eq_zero_of_good hε hg T ((((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
    (isOpen_lt ((continuous_psiR hδ j q).comp continuous_fst) continuous_const)).measurableSet) ?_
  rintro ω hG ⟨⟨hf, -⟩, hneg⟩
  have := (D.intH_bounds_R hε hg hnR hqT hG hf j hδ).1
  simp only [mem_ofPred_eq, psiR] at hneg
  linarith

theorem law_psiL_neg (hε : 0 < ε) (hg : 0 < g) (hnL : 0 < nL) {T q : ℝ≥0} (hqT : q ≤ T) (i : Fin nL)
    {δ : ℝ} (hδ : 0 < δ) :
    D.law T ((upSet mL mR R g q ×ˢ univ) ∩ {p | psiL δ i q p.1 < 0}) = 0 := by
  refine D.law_eq_zero_of_good hε hg T ((((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
    (isOpen_lt ((continuous_psiL hδ i q).comp continuous_fst) continuous_const)).measurableSet) ?_
  rintro ω hG ⟨⟨hf, -⟩, hneg⟩
  have := (D.intH_bounds_L hε hg hnL hqT hG hf i hδ).1
  simp only [mem_ofPred_eq, psiL] at hneg
  linarith

/-- **The DS1 bound in the limit identification** (right labels). -/
theorem law_psiR_gt (hε : 0 < ε) (hg : 0 < g) (hnR : 0 < nR) {T q : ℝ≥0} (hqT : q ≤ T) (j : Fin nR)
    {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) {c : ℝ≥0∞}
    (hZ : ∫⁻ ω, occ mL mR R g T W VL VR ζ (fun x => ENNReal.ofReal (invCut δ x)) (gpR hnR) ω ∂P ≤ c) :
    D.law T ((upSet mL mR R g q ×ˢ univ) ∩ {p | η < psiR δ j q p.1}) ≤ c / ENNReal.ofReal (η / 2) := by
  have hmeas : MeasurableSet ((upSet mL mR R g q ×ˢ univ) ∩
      {p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) | η < psiR δ j q p.1}) :=
    (((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
      (isOpen_lt continuous_const ((continuous_psiR hδ j q).comp continuous_fst))).measurableSet
  rw [D.law_apply hε hg T hmeas]
  have hsub : (fun ω => (fR mL mR R g T W VL VR ζ ω, D.bP T ω)) ⁻¹'
      ((upSet mL mR R g q ×ˢ univ) ∩ {p | η < psiR δ j q p.1}) ⊆
      D.Gᶜ ∪ {ω | ENNReal.ofReal (η / 2) ≤
        occ mL mR R g T W VL VR ζ (fun x => ENNReal.ofReal (invCut δ x)) (gpR hnR) ω} := by
    rintro ω ⟨⟨hf, -⟩, hgt⟩
    by_cases hG : ω ∈ D.G
    · right
      have h2 := (D.intH_bounds_R hε hg hnR hqT hG hf j hδ).2
      simp only [mem_ofPred_eq, psiR] at hgt
      have h3 : η / 2 ≤ (D.good ω hG).iR hnR T δ := by linarith
      exact (ENNReal.ofReal_le_ofReal h3).trans (D.ofReal_iR_le_occ hε hg hnR T δ hG)
    · left; exact hG
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [D.null_G, zero_add]
  refine (meas_ge_le_lintegral_div (D.aemeasurable_occ hε hg T (ENNReal.measurable_ofReal.comp
    (measurable_invCut δ)) (continuous_gpR hnR)) (ENNReal.ofReal_pos.2 (half_pos hη)).ne'
    ENNReal.ofReal_ne_top).trans ?_
  exact ENNReal.div_le_div_right hZ _

/-- **The DS1 bound in the limit identification** (left labels). -/
theorem law_psiL_gt (hε : 0 < ε) (hg : 0 < g) (hnL : 0 < nL) {T q : ℝ≥0} (hqT : q ≤ T) (i : Fin nL)
    {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) {c : ℝ≥0∞}
    (hZ : ∫⁻ ω, occ mL mR R g T W VL VR ζ (fun x => ENNReal.ofReal (invCut δ x)) (gpL hnL) ω ∂P ≤ c) :
    D.law T ((upSet mL mR R g q ×ˢ univ) ∩ {p | η < psiL δ i q p.1}) ≤ c / ENNReal.ofReal (η / 2) := by
  have hmeas : MeasurableSet ((upSet mL mR R g q ×ˢ univ) ∩
      {p : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ) | η < psiL δ i q p.1}) :=
    (((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
      (isOpen_lt continuous_const ((continuous_psiL hδ i q).comp continuous_fst))).measurableSet
  rw [D.law_apply hε hg T hmeas]
  have hsub : (fun ω => (fR mL mR R g T W VL VR ζ ω, D.bP T ω)) ⁻¹'
      ((upSet mL mR R g q ×ˢ univ) ∩ {p | η < psiL δ i q p.1}) ⊆
      D.Gᶜ ∪ {ω | ENNReal.ofReal (η / 2) ≤
        occ mL mR R g T W VL VR ζ (fun x => ENNReal.ofReal (invCut δ x)) (gpL hnL) ω} := by
    rintro ω ⟨⟨hf, -⟩, hgt⟩
    by_cases hG : ω ∈ D.G
    · right
      have h2 := (D.intH_bounds_L hε hg hnL hqT hG hf i hδ).2
      simp only [mem_ofPred_eq, psiL] at hgt
      have h3 : η / 2 ≤ (D.good ω hG).iL hnL T δ := by linarith
      exact (ENNReal.ofReal_le_ofReal h3).trans (D.ofReal_iL_le_occ hε hg hnL T δ hG)
    · left; exact hG
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [D.null_G, zero_add]
  refine (meas_ge_le_lintegral_div (D.aemeasurable_occ hε hg T (ENNReal.measurable_ofReal.comp
    (measurable_invCut δ)) (continuous_gpL hnL)) (ENNReal.ofReal_pos.2 (half_pos hη)).ne'
    ENNReal.ofReal_ne_top).trans ?_
  exact ENNReal.div_le_div_right hZ _

theorem law_not_ordered (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    D.law T {p | ¬ ∀ x, IsOrderedState (p.1 x)} = 0 :=
  D.law_eq_zero_of_good hε hg T isOpen_setOf_not_ordered.measurableSet fun ω hG h =>
    h ((D.good ω hG).isOrderedState_stopped hε hg)

theorem law_init (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) {s₀ : SState nL nR} {η : ℝ}
    (h : dist (((0 : ℝ), xL, xR) : SState nL nR) s₀ ≤ η) :
    D.law T {p | η < dist (pathAt p.1 0) s₀} = 0 := by
  refine D.law_eq_zero_of_good hε hg T (isOpen_lt continuous_const
    (((continuous_pathAt_const 0).comp continuous_fst).dist continuous_const)).measurableSet fun ω hG hω => ?_
  simp only [mem_ofPred_eq] at hω
  have h0 : pathAt (fR mL mR R g T W VL VR ζ ω) 0 = ((0 : ℝ), xL, xR) := by
    rw [pathAt_of_le _ (zero_le : (0 : ℝ≥0) ≤ T)]
    exact (D.good ω hG).stopped_zero hε hg
  rw [h0] at hω
  linarith

/-- **The linear identity with the limiting weights holds up to the weight difference.** -/
theorem law_phiLin (hε : 0 < ε) (hg : 0 < g) {T q : ℝ≥0} (hqT : q ≤ T) {ρL₀ : Fin nL → ℝ}
    {ρR₀ : Fin nR → ℝ} {η : ℝ}
    (hsmall : ((∑ i, |ρL₀ i - ρL i|) + ∑ j, |ρR₀ j - ρR j|) * (R + 1) < η) :
    D.law T ((upSet mL mR R g q ×ˢ univ) ∩ {p | η < |phiLin κ ρL₀ ρR₀ q p|}) = 0 := by
  refine D.law_eq_zero_of_good hε hg T ((((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
    (isOpen_lt continuous_const (continuous_phiLin κ ρL₀ ρR₀ q).abs)).measurableSet) ?_
  rintro ω hG ⟨⟨hf, -⟩, hgt⟩
  simp only [mem_ofPred_eq] at hgt
  set f := fR mL mR R g T W VL VR ζ ω
  have hlin := D.linear_at hε hg hqT hG hf
  have hbuf : ∀ s : ℝ≥0, s ≤ T → pathAt f s ∈ cBuf mL mR R g := fun s hs => by
    rw [pathAt_of_le _ hs]
    exact (D.good ω hG).stopped_mem_cBuf hε hg _
  have hq := hbuf q hqT
  have h0 := hbuf 0 zero_le
  have e : phiLin κ ρL₀ ρR₀ q (f, D.bP T ω) =
      (∑ i, (ρL₀ i - ρL i) / 2 * ((pathAt f q).2.1 i - (pathAt f 0).2.1 i)) +
        ∑ j, (ρR₀ j - ρR j) / 2 * ((pathAt f q).2.2 j - (pathAt f 0).2.2 j) := by
    unfold phiLin
    simp only
    rw [hlin]
    simp only [sub_div, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [e] at hgt
  have bL : ∀ i, |(ρL₀ i - ρL i) / 2 * ((pathAt f q).2.1 i - (pathAt f 0).2.1 i)| ≤ |ρL₀ i - ρL i| * (R + 1) := by
    intro i
    rw [abs_mul, abs_div, abs_two]
    have h1 : |(pathAt f q).2.1 i - (pathAt f 0).2.1 i| ≤ 2 * (R + 1) := by
      have a1 := hq.1.2.1 i
      have a2 := h0.1.2.1 i
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith
    have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (ρL₀ i - ρL i))
    nlinarith [abs_nonneg (ρL₀ i - ρL i)]
  have bR : ∀ j, |(ρR₀ j - ρR j) / 2 * ((pathAt f q).2.2 j - (pathAt f 0).2.2 j)| ≤ |ρR₀ j - ρR j| * (R + 1) := by
    intro j
    rw [abs_mul, abs_div, abs_two]
    have h1 : |(pathAt f q).2.2 j - (pathAt f 0).2.2 j| ≤ 2 * (R + 1) := by
      have a1 := hq.1.2.2 j
      have a2 := h0.1.2.2 j
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith
    have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (ρR₀ j - ρR j))
    nlinarith [abs_nonneg (ρR₀ j - ρR j)]
  have hL := (Finset.abs_sum_le_sum_abs (fun i => (ρL₀ i - ρL i) / 2 * ((pathAt f q).2.1 i - (pathAt f 0).2.1 i))
    Finset.univ).trans (Finset.sum_le_sum fun i _ => bL i)
  have hR := (Finset.abs_sum_le_sum_abs (fun j => (ρR₀ j - ρR j) / 2 * ((pathAt f q).2.2 j - (pathAt f 0).2.2 j))
    Finset.univ).trans (Finset.sum_le_sum fun j _ => bR j)
  have hsum := (abs_add_le _ _).trans (add_le_add hL hR)
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul] at hsum
  linarith

end EvolData


/-! ### Identification of the limit -/

section Identify

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε a R g : ℝ}

/-- A bound `μ G ≤ cₙ` for every `n` with `cₙ → 0` gives `μ G = 0`. -/
theorem measure_eq_zero_of_le_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α} {G : Set α}
    {c : ℕ → ℝ≥0∞} (hle : ∀ n, μ G ≤ c n) (hc : Tendsto c atTop (𝓝 0)) : μ G = 0 :=
  le_antisymm (ge_of_tendsto' hc hle) bot_le

/-- `ofReal (C δₙ^q) / ofReal c → 0` along `δₙ → 0⁺`, for `q > 0` and `c > 0`. -/
theorem tendsto_ofReal_rpow_div {C q c : ℝ} (hq : 0 < q) (hc : 0 < c) {δ : ℕ → ℝ}
    (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ENNReal.ofReal (C * δ n ^ q) / ENNReal.ofReal c) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => δ n ^ q) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto.comp hlim
    rwa [Real.zero_rpow hq.ne'] at this
  have h2 : Tendsto (fun n => ENNReal.ofReal (C * δ n ^ q)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto _).comp (h1.const_mul C)
    simpa [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using this
  have h3 := ENNReal.Tendsto.div_const h2 (Or.inr (ENNReal.ofReal_pos.2 hc).ne')
  simpa [ENNReal.zero_div] using h3

/-- **Identification of subsequential limits** (proof of DS2): if the joint laws of a sequence of evolutions of DS1
words with converging weights and initial positions converge weakly to `π`, then `π`-almost surely the limit
satisfies `LimitProps` with the limiting word. -/
theorem ae_limitProps (hκ : 0 < κ) (hnL : 0 < nL) (hnR : 0 < nR) (hε : 0 < ε) (ha : 0 < a) (hg : 0 < g)
    (hRw : 0 ≤ Rw) (T : ℝ≥0) {Ω : ℕ → Type u} [mΩ : ∀ k, MeasurableSpace (Ω k)] {P : ∀ k, Measure (Ω k)}
    [hP : ∀ k, IsProbabilityMeasure (P k)] {𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k)}
    {xL : ℕ → Fin nL → ℝ} {xR : ℕ → Fin nR → ℝ} {ρL : ℕ → Fin nL → ℝ} {ρR : ℕ → Fin nR → ℝ}
    {W : ∀ k, ℝ≥0 → Ω k → ℝ} {VL : ∀ k, Fin nL → ℝ≥0 → Ω k → ℝ} {VR : ∀ k, Fin nR → ℝ≥0 → Ω k → ℝ}
    {B : ∀ k, ℝ≥0 → Ω k → ℝ} {ζ : ∀ k, Ω k → ℝ≥0∞}
    (hE : ∀ k, IsIntegratedSLEEvolution κ (xL k) (xR k) (ρL k) (ρR k) (P k) (𝓕 k) (W k) (VL k) (VR k) (B k)
      (ζ k))
    (hw : ∀ k, IsDS1Word mL mR Rw ε (xL k) (xR k) (ρL k) (ρR k))
    (hcr : ∀ k, a ≤ xR k ⟨0, hnR⟩ - xL k ⟨0, hnL⟩)
    (D : ∀ k, EvolData κ mL mR Rw ε R g (xL k) (xR k) (ρL k) (ρR k) (P k) (W k) (VL k) (VR k) (ζ k))
    {xL₀ : Fin nL → ℝ} {xR₀ : Fin nR → ℝ} {ρL₀ : Fin nL → ℝ} {ρR₀ : Fin nR → ℝ}
    (hxL : Tendsto xL atTop (𝓝 xL₀)) (hxR : Tendsto xR atTop (𝓝 xR₀)) (hρL : Tendsto ρL atTop (𝓝 ρL₀))
    (hρR : Tendsto ρR atTop (𝓝 ρR₀))
    {π : ProbabilityMeasure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))}
    (hlim : Tendsto (fun k => (D k).lawP hε hg T) atTop (𝓝 π)) :
    ∀ᵐ p ∂(π : Measure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))),
      LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ p.1 p.2 := by
  set μ := (π : Measure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ)))
  have hz : ∀ {G : Set (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))}, IsOpen G →
      (∀ᶠ k in atTop, (D k).law T G = 0) → μ G = 0 := fun hG h =>
    measure_eq_zero_of_tendsto_of_isOpen hlim hG h
  have hb : ∀ {G : Set (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))} {c : ℝ≥0∞},
      IsOpen G → (∀ k, (D k).law T G ≤ c) → μ G ≤ c := fun hG h =>
    measure_le_of_tendsto_of_isOpen hlim hG (Eventually.of_forall h)
  -- (L1) the initial state
  have hL1 : ∀ᵐ p ∂μ, pathAt p.1 0 = ((0 : ℝ), xL₀, xR₀) := by
    have hs : Tendsto (fun k => (((0 : ℝ), xL k, xR k) : SState nL nR)) atTop (𝓝 ((0 : ℝ), xL₀, xR₀)) :=
      tendsto_const_nhds.prodMk_nhds (hxL.prodMk_nhds hxR)
    have hn : ∀ n : ℕ, ∀ᵐ p ∂μ, dist (pathAt p.1 0) ((0 : ℝ), xL₀, xR₀) ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h0 := hz (isOpen_lt continuous_const
        (((continuous_pathAt_const 0).comp continuous_fst).dist continuous_const))
        ((Metric.tendsto_nhds.1 hs _ hpos).mono fun k hk => (D k).law_init hε hg T hk.le)
      refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp => ?_
      simpa only [mem_ofPred_eq, not_lt, Function.comp_apply] using hp
    filter_upwards [ae_all_iff.2 hn] with p hp
    refine dist_le_zero.1 (le_of_forall_pos_le_add fun η hη => ?_)
    obtain ⟨n, hnη⟩ := exists_nat_one_div_lt hη
    rw [zero_add]
    exact (hp n).trans hnη.le
  -- (L2) the ordering
  have hL2 : ∀ᵐ p ∂μ, ∀ x, IsOrderedState (p.1 x) := by
    have h0 := hz isOpen_setOf_not_ordered (Eventually.of_forall fun k => (D k).law_not_ordered hε hg T)
    exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp => by simpa only [mem_ofPred_eq, not_not] using hp
  -- the DS1 constants and the cutoffs
  obtain ⟨r, hr, p, hp0, hp1, C, hds1⟩ := DS1.ds1.{u} κ hκ nL nR hnR T hRw hε ha (half_pos hg)
  obtain ⟨rL, hrL, pL, hpL0, hpL1, CL, hds1L⟩ := DS1.ds1_left.{u} κ hκ nL nR hnL T hRw hε ha (half_pos hg)
  set r₀ := min r rL with hr₀
  have hr₀pos : 0 < r₀ := lt_min hr hrL
  set δs : ℕ → ℝ := fun n => r₀ / ((n : ℝ) + 2) with hδsdef
  have hδs_pos : ∀ n, 0 < δs n := fun n => by simp only [hδsdef]; positivity
  have hδs_lt : ∀ n, δs n < r₀ := fun n => by
    simp only [hδsdef]
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) < (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
    nlinarith
  have hδs_anti : Antitone δs := fun n m hnm => by
    simp only [hδsdef]
    exact div_le_div_of_nonneg_left hr₀pos.le (by positivity) (by have h : (n : ℝ) ≤ m := (by exact_mod_cast hnm); linarith)
  have hδs_lim : Tendsto δs atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := r₀)).div_atTop h1
  have hxL0 : ∀ k, ∀ i : Fin nL, xL k i ≤ xL k ⟨0, hnL⟩ := fun k i => (hw k).1.1 (Fin.le_def.2 (Nat.zero_le _))
  have hxR0 : ∀ k, ∀ j : Fin nR, xR k ⟨0, hnR⟩ ≤ xR k j := fun k j => (hw k).1.2.2.1 (Fin.le_def.2 (Nat.zero_le _))
  have hZR : ∀ k n, ∫⁻ ω, occ mL mR R g T (W k) (VL k) (VR k) (ζ k) (fun x => ENNReal.ofReal (invCut (δs n) x))
      (EvolData.gpR hnR) ω ∂P k ≤ ENNReal.ofReal (C * δs n ^ (1 - p)) := by
    intro k n
    have hds := hds1 mL mR (hE k) (hw k).2.1 (hw k).2.2.1 (hw k).2.2.2.2
      (fun i => by linarith [hcr k, hxL0 k i])
    refine (lintegral_mono_ae ?_).trans (hds.1 (δs n) (hδs_pos n) ((hδs_lt n).trans_le (min_le_left _ _)))
    filter_upwards [(D k).ae_mem_G] with ω hω
    exact (D k).occ_gpR_le hε hg hnR T _ hω
  have hZL : ∀ k n, ∫⁻ ω, occ mL mR R g T (W k) (VL k) (VR k) (ζ k) (fun x => ENNReal.ofReal (invCut (δs n) x))
      (EvolData.gpL hnL) ω ∂P k ≤ ENNReal.ofReal (CL * δs n ^ (1 - pL)) := by
    intro k n
    have hds := hds1L mL mR (hE k) (hw k).2.1 (hw k).2.2.1 (hw k).2.2.2.1
      (fun j => by linarith [hcr k, hxR0 k j])
    refine (lintegral_mono_ae ?_).trans (hds.1 (δs n) (hδs_pos n) ((hδs_lt n).trans_le (min_le_right _ _)))
    filter_upwards [(D k).ae_mem_G] with ω hω
    exact (D k).occ_gpL_le hε hg hnL T _ hω
  -- (L3a) the linear identity
  have hLa : ∀ q, q ≤ T → ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q → phiLin κ ρL₀ ρR₀ q p = 0 := by
    intro q hqT
    have ht : Tendsto (fun k => ((∑ i, |ρL₀ i - ρL k i|) + ∑ j, |ρR₀ j - ρR k j|) * (R + 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => ∑ i, |ρL₀ i - ρL k i|) atTop (𝓝 0) := by
        have := tendsto_finsetSum (Finset.univ : Finset (Fin nL)) fun i _ =>
          (tendsto_const_nhds (x := ρL₀ i)).sub (tendsto_pi_nhds.1 hρL i) |>.abs
        simpa using this
      have h2 : Tendsto (fun k => ∑ j, |ρR₀ j - ρR k j|) atTop (𝓝 0) := by
        have := tendsto_finsetSum (Finset.univ : Finset (Fin nR)) fun j _ =>
          (tendsto_const_nhds (x := ρR₀ j)).sub (tendsto_pi_nhds.1 hρR j) |>.abs
        simpa using this
      simpa using (h1.add h2).mul_const (R + 1)
    have hn : ∀ n : ℕ, ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q → |phiLin κ ρL₀ ρR₀ q p| ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h0 := hz (((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
        (isOpen_lt continuous_const (continuous_phiLin κ ρL₀ ρR₀ q).abs))
        ((ht.eventually (gt_mem_nhds hpos)).mono fun k hk => (D k).law_phiLin hε hg hqT hk)
      refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp hup => ?_
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, mem_ofPred_eq, not_and,
        not_lt] at hp
      exact hp hup
    filter_upwards [ae_all_iff.2 hn] with p hp hup
    refine abs_nonpos_iff.1 (le_of_forall_pos_le_add fun η hη => ?_)
    obtain ⟨n, hnη⟩ := exists_nat_one_div_lt hη
    rw [zero_add]
    exact (hp n hup).trans hnη.le
  -- (L3b) the right labels
  have hLb : ∀ q, q ≤ T → ∀ j : Fin nR, ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q →
      0 ≤ (pathAt p.1 q).2.2 j - (pathAt p.1 0).2.2 j ∧
      ∫⁻ s in Ioc (0 : ℝ) q, Ginv (gapR j (pathAt p.1 s.toNNReal)) =
        ENNReal.ofReal (((pathAt p.1 q).2.2 j - (pathAt p.1 0).2.2 j) / 2) := by
    intro q hqT j
    have hneg : ∀ n, ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q → 0 ≤ psiR (δs n) j q p.1 := by
      intro n
      have h0 := hz (((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
        (isOpen_lt ((continuous_psiR (hδs_pos n) j q).comp continuous_fst) continuous_const))
        (Eventually.of_forall fun k => (D k).law_psiR_neg hε hg hnR hqT j (hδs_pos n))
      refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp hup => ?_
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, mem_ofPred_eq, not_and,
        not_lt] at hp
      exact hp hup
    have hclose : ∀ m : ℕ, ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q →
        ∃ n, psiR (δs n) j q p.1 ≤ 1 / ((m : ℝ) + 1) := by
      intro m
      have hη : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      have hle : ∀ n, μ ((upSet mL mR R g q ×ˢ univ) ∩
          ⋂ n', {p | 1 / ((m : ℝ) + 1) < psiR (δs n') j q p.1}) ≤
          ENNReal.ofReal (C * δs n ^ (1 - p)) / ENNReal.ofReal (1 / ((m : ℝ) + 1) / 2) := by
        intro n
        refine (measure_mono (Set.inter_subset_inter_right _ (Set.iInter_subset _ n))).trans ?_
        exact hb (((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
          (isOpen_lt continuous_const ((continuous_psiR (hδs_pos n) j q).comp continuous_fst)))
          fun k => (D k).law_psiR_gt hε hg hnR hqT j (hδs_pos n) hη (hZR k n)
      have h0 := measure_eq_zero_of_le_tendsto hle
        (tendsto_ofReal_rpow_div (sub_pos.2 hp1) (half_pos hη) hδs_lim)
      refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp hup => ?_
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_iInter, mem_ofPred_eq,
        not_and, not_forall, not_lt] at hp
      exact hp hup
    filter_upwards [ae_all_iff.2 hneg, ae_all_iff.2 hclose] with p h1 h2 hup
    refine ⟨?_, lintegral_Ginv_eq hδs_pos hδs_anti hδs_lim (continuous_gapR j) (fun n => ?_) (fun m => ?_)⟩
    · have := h1 0 hup
      have h0 : 0 ≤ intH (δs 0) (gapR j) q p.1 :=
        intervalIntegral.integral_nonneg q.coe_nonneg fun _ _ => hcut_nonneg (hδs_pos 0) _
      unfold psiR at this
      linarith
    · have := h1 n hup
      unfold psiR at this
      linarith
    · obtain ⟨n, hn⟩ := h2 m hup
      exact ⟨n, by unfold psiR at hn; linarith⟩
  -- (L3c) the left labels
  have hLc : ∀ q, q ≤ T → ∀ i : Fin nL, ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q →
      0 ≤ (pathAt p.1 0).2.1 i - (pathAt p.1 q).2.1 i ∧
      ∫⁻ s in Ioc (0 : ℝ) q, Ginv (gapL i (pathAt p.1 s.toNNReal)) =
        ENNReal.ofReal (((pathAt p.1 0).2.1 i - (pathAt p.1 q).2.1 i) / 2) := by
    intro q hqT i
    have hneg : ∀ n, ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q → 0 ≤ psiL (δs n) i q p.1 := by
      intro n
      have h0 := hz (((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
        (isOpen_lt ((continuous_psiL (hδs_pos n) i q).comp continuous_fst) continuous_const))
        (Eventually.of_forall fun k => (D k).law_psiL_neg hε hg hnL hqT i (hδs_pos n))
      refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp hup => ?_
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, mem_ofPred_eq, not_and,
        not_lt] at hp
      exact hp hup
    have hclose : ∀ m : ℕ, ∀ᵐ p ∂μ, p.1 ∈ upSet mL mR R g q →
        ∃ n, psiL (δs n) i q p.1 ≤ 1 / ((m : ℝ) + 1) := by
      intro m
      have hη : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      have hle : ∀ n, μ ((upSet mL mR R g q ×ˢ univ) ∩
          ⋂ n', {p | 1 / ((m : ℝ) + 1) < psiL (δs n') i q p.1}) ≤
          ENNReal.ofReal (CL * δs n ^ (1 - pL)) / ENNReal.ofReal (1 / ((m : ℝ) + 1) / 2) := by
        intro n
        refine (measure_mono (Set.inter_subset_inter_right _ (Set.iInter_subset _ n))).trans ?_
        exact hb (((isOpen_upSet mL mR R g q).prod isOpen_univ).inter
          (isOpen_lt continuous_const ((continuous_psiL (hδs_pos n) i q).comp continuous_fst)))
          fun k => (D k).law_psiL_gt hε hg hnL hqT i (hδs_pos n) hη (hZL k n)
      have h0 := measure_eq_zero_of_le_tendsto hle
        (tendsto_ofReal_rpow_div (sub_pos.2 hpL1) (half_pos hη) hδs_lim)
      refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp hup => ?_
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_iInter, mem_ofPred_eq,
        not_and, not_forall, not_lt] at hp
      exact hp hup
    filter_upwards [ae_all_iff.2 hneg, ae_all_iff.2 hclose] with p h1 h2 hup
    refine ⟨?_, lintegral_Ginv_eq hδs_pos hδs_anti hδs_lim (continuous_gapL i) (fun n => ?_) (fun m => ?_)⟩
    · have := h1 0 hup
      have h0 : 0 ≤ intH (δs 0) (gapL i) q p.1 :=
        intervalIntegral.integral_nonneg q.coe_nonneg fun _ _ => hcut_nonneg (hδs_pos 0) _
      unfold psiL at this
      linarith
    · have := h1 n hup
      unfold psiL at this
      linarith
    · obtain ⟨n, hn⟩ := h2 m hup
      exact ⟨n, by unfold psiL at hn; linarith⟩
  -- assemble
  have hL3 : ∀ q ∈ qSet, ∀ᵐ p ∂μ, q ≤ T → p.1 ∈ upSet mL mR R g q →
      (pathAt p.1 q).1 = Real.sqrt κ * pathAt p.2 q -
          (∑ i, ρL₀ i / 2 * ((pathAt p.1 q).2.1 i - (pathAt p.1 0).2.1 i)) -
          ∑ j, ρR₀ j / 2 * ((pathAt p.1 q).2.2 j - (pathAt p.1 0).2.2 j) ∧
        (∀ j, 0 ≤ (pathAt p.1 q).2.2 j - (pathAt p.1 0).2.2 j ∧
          ∫⁻ s in Ioc (0 : ℝ) q, Ginv (gapR j (pathAt p.1 s.toNNReal)) =
            ENNReal.ofReal (((pathAt p.1 q).2.2 j - (pathAt p.1 0).2.2 j) / 2)) ∧
        ∀ i, 0 ≤ (pathAt p.1 0).2.1 i - (pathAt p.1 q).2.1 i ∧
          ∫⁻ s in Ioc (0 : ℝ) q, Ginv (gapL i (pathAt p.1 s.toNNReal)) =
            ENNReal.ofReal (((pathAt p.1 0).2.1 i - (pathAt p.1 q).2.1 i) / 2) := by
    intro q _
    by_cases hqT : q ≤ T
    · filter_upwards [hLa q hqT, ae_all_iff.2 (hLb q hqT), ae_all_iff.2 (hLc q hqT)] with p ha hbj hci _ hup
      refine ⟨?_, fun j => hbj j hup, fun i => hci i hup⟩
      have := ha hup
      unfold phiLin at this
      linarith
    · exact ae_of_all _ fun p h => absurd h hqT
  filter_upwards [hL1, hL2, (ae_ball_iff qSet_countable).2 hL3] with p h1 h2 h3
  exact ⟨h1, h2, fun q hq hqT hup => h3 q hq hqT hup⟩

end Identify


end DSReach

end Supp12

end InteractingSLE
