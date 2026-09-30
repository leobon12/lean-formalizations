import QuantumZipper.Proofs.LQG.Measurability
import QuantumZipper.Proofs.LQG.BoundaryVague

/-!
# M4 (TR-MEAS): a measurable certificate for the global boundary limit, and Giry measurability

`handoff/E1-TR.md` (M4). For a field sample `x`, `BCert γ x` is the countable certificate

* every approximation `bdryApprox γ x k` is finite on every `[-N, N]`;
* `∫ g d(bdryApprox γ x k)` converges for every `g` of the countable test family
  `BdryVague.testFam N m`, `BdryVague.bump N`.

Results: `measurableSet_bCert`; `exists_isVagueLimitR_of_bCert` (Riesz–Markov, via
`BdryVague.exists_isVagueLimitR_of_testFam`); `bCert_of_isVagueLimitR` (converse, given the
finiteness); `measurable_qBoundaryMeasure_bCert`: `x ↦ qBoundaryMeasure γ x` (junk `0` off the
certificate) is measurable into `Measure ℝ` with the Giry `σ`-algebra.

The argument is that of `LQGMeas.measurable_qBoundaryMeasure_good` (M4-R5), with the good-sample
hypothesis replaced by the mere existence of the vague limit. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace E1
namespace M4

open LQGMeas BdryVague

/-- The countable certificate for the existence of the global boundary limit. -/
def BCert (γ : ℝ) (x : FieldSample) : Prop :=
  (∀ k N : ℕ, bdryApprox γ x k (Icc (-(N : ℝ)) N) < ⊤) ∧
    (∀ N m : ℕ, ∃ l, Tendsto (fun k => ∫ s, testFam N m s ∂bdryApprox γ x k) atTop (𝓝 l)) ∧
    ∀ N : ℕ, ∃ l, Tendsto (fun k => ∫ s, bump N s ∂bdryApprox γ x k) atTop (𝓝 l)

theorem measurableSet_exists_tendsto_bdry (γ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet {x : FieldSample | ∃ l, Tendsto (fun k => ∫ s, g s ∂bdryApprox γ x k)
      atTop (𝓝 l)} :=
  StronglyMeasurable.measurableSet_exists_tendsto
    (f := fun k (x : FieldSample) => ∫ s, g s ∂bdryApprox γ x k)
    fun k => (meas_integral_bdryApprox γ k hg).stronglyMeasurable

theorem measurableSet_bCert (γ : ℝ) : MeasurableSet {x | BCert γ x} := by
  have e : {x | BCert γ x} = (⋂ k : ℕ, ⋂ N : ℕ,
      {x : FieldSample | bdryApprox γ x k (Icc (-(N : ℝ)) N) < ⊤}) ∩
      ((⋂ N : ℕ, ⋂ m : ℕ, {x : FieldSample | ∃ l, Tendsto
        (fun k => ∫ s, testFam N m s ∂bdryApprox γ x k) atTop (𝓝 l)}) ∩
      ⋂ N : ℕ, {x : FieldSample | ∃ l, Tendsto
        (fun k => ∫ s, bump N s ∂bdryApprox γ x k) atTop (𝓝 l)}) := by
    ext x; simp [BCert]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun N => ?_)
    (MeasurableSet.inter (MeasurableSet.iInter fun N => MeasurableSet.iInter fun m => ?_)
      (MeasurableSet.iInter fun N => ?_))
  · exact measurableSet_lt ((Measure.measurable_coe measurableSet_Icc).comp
      (measurable_bdryApprox γ k)) measurable_const
  · exact measurableSet_exists_tendsto_bdry γ (continuous_testFam N m).measurable
  · exact measurableSet_exists_tendsto_bdry γ (continuous_bump N).measurable

theorem exists_isVagueLimitR_of_bCert {γ : ℝ} {x : FieldSample} (h : BCert γ x) :
    ∃ ν, IsVagueLimitR (bdryApprox γ x) ν :=
  exists_isVagueLimitR_of_testFam (fun k => isFiniteMeasureOnCompacts_of_Icc (h.1 k)) h.2.1 h.2.2

theorem bCert_of_isVagueLimitR {γ : ℝ} {x : FieldSample} {ν : Measure ℝ}
    (hfin : ∀ k N : ℕ, bdryApprox γ x k (Icc (-(N : ℝ)) N) < ⊤)
    (h : IsVagueLimitR (bdryApprox γ x) ν) : BCert γ x :=
  ⟨hfin, fun N m => ⟨_, h.2 _ (continuous_testFam N m) (hasCompactSupport_testFam N m)⟩,
    fun N => ⟨_, h.2 _ (continuous_bump N) (hasCompactSupport_bump N)⟩⟩

/-- The chosen boundary measure is a vague limit whenever one exists. -/
theorem isVagueLimitR_qBoundaryMeasure {γ : ℝ} {x : FieldSample}
    (h : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν) :
    IsVagueLimitR (bdryApprox γ x) (qBoundaryMeasure γ x) := by
  rw [qBoundaryMeasure, dif_pos h]
  exact h.choose_spec

theorem bdryFun_eq_of_exists {γ : ℝ} {x : FieldSample}
    (h : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν) {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : bdryFun γ f x = ∫ t, f t ∂qBoundaryMeasure γ x :=
  ((isVagueLimitR_qBoundaryMeasure h).2 f hf hfc).liminf_eq

theorem measurable_qBoundaryMeasure_bCert_open (γ : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Uᶜ.Nonempty) :
    Measurable fun x : {x // BCert γ x} => qBoundaryMeasure γ x.1 U := by
  have key : ∀ x : {x // BCert γ x}, qBoundaryMeasure γ x.1 U =
      ⨆ n : ℕ, ENNReal.ofReal (bdryFun γ (openBump U n) x.1) := by
    intro x
    have hx := exists_isVagueLimitR_of_bCert x.2
    have := (isVagueLimitR_qBoundaryMeasure hx).1
    rw [measure_open_eq_iSup _ hU hUc]
    congr 1
    funext n
    rw [bdryFun_eq_of_exists hx (continuous_openBump U n) (hasCompactSupport_openBump hUb n),
      ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun z => openBump_nonneg U n z)]
    exact (continuous_openBump U n).integrable_of_hasCompactSupport
      (hasCompactSupport_openBump hUb n)
  simp_rw [key]
  exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    ((measurable_bdryFun γ (continuous_openBump U n).measurable).comp measurable_subtype_coe)

theorem measurable_qBoundaryMeasure_bCert_sub (γ : ℝ) :
    Measurable fun x : {x // BCert γ x} => qBoundaryMeasure γ x.1 := by
  refine measurable_measure_of_open _ (fun N => Ioo (-(N : ℝ)) N) (fun N => measurableSet_Ioo)
    (fun m n hmn => Ioo_subset_Ioo (by simpa using hmn) (by exact_mod_cast hmn))
    (fun x => ?_) (fun x N => ?_) (fun U N hU => ?_)
  · have : (⋃ N : ℕ, Ioo (-(N : ℝ)) N) = univ := by
      refine eq_univ_of_forall fun t => mem_iUnion.2 ?_
      obtain ⟨N, hN⟩ := exists_nat_gt |t|
      exact ⟨N, abs_lt.1 hN⟩
    rw [this, compl_univ, measure_empty]
  · have := (isVagueLimitR_qBoundaryMeasure (exists_isVagueLimitR_of_bCert x.2)).1
    exact measure_Ioo_lt_top.ne
  · refine measurable_qBoundaryMeasure_bCert_open γ (hU.inter isOpen_Ioo)
      (Metric.isBounded_Ioo _ _ |>.subset inter_subset_right) ⟨N, fun h => ?_⟩
    exact lt_irrefl _ h.2.2

open Classical in
/-- **Giry measurability** of the boundary measure on the certificate (junk `0` off it). -/
theorem measurable_qBoundaryMeasure_bCert (γ : ℝ) :
    Measurable fun x => if BCert γ x then qBoundaryMeasure γ x else 0 := by
  convert Measurable.dite (s := {x : FieldSample | BCert γ x})
    (f := fun x => qBoundaryMeasure γ x.1) (measurable_qBoundaryMeasure_bCert_sub γ)
    (g := fun _ => (0 : Measure ℝ)) measurable_const (measurableSet_bCert γ) using 1
  funext x
  by_cases h : BCert γ x <;> simp [h]

end M4
end E1
end QuantumZipper
