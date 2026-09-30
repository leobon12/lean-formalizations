import QuantumZipper.Proofs.Zipper.D3PlusN2HeartRad
import QuantumZipper.Proofs.Zipper.D3PlusN2Bridge
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# N2-HEART: law identities for the window data

Task N2-HEART.
* `map_eq_of_coord_ae_eq`: two a.e.-measurable processes indexed by an arbitrary set, a.e. equal
  coordinatewise, have the same law for the product σ-algebra (measurable cylinders form a
  generating π-system; standard, cf. Kallenberg, *Foundations of Modern Probability*, 2nd ed.,
  Prop. 3.2).
* `tvDist_map_le_of_coord`: coordinatewise a.e. agreement on an event `G` bounds the TV distance
  of the laws by `P Gᶜ` (own elementary argument).
* `aemeasurable_resField_n2Emb`: the embedded model's window data are a.e.-measurable (the
  measurability half of `N2ZHeartStmt`).
* `ae_resField_wedgeV_eq`: a.s. the wedge's window data are `heartW (lateral window, truncated
  radial path)` (pathwise, from continuity of the wedge radial process).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

section General
variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem map_eq_of_coord_ae_eq [IsFiniteMeasure P] {W F : Ω → ι → ℝ} (hW : AEMeasurable W P)
    (hF : AEMeasurable F P) (h : ∀ i, ∀ᵐ ω ∂P, W ω i = F ω i) : P.map W = P.map F := by
  haveI : IsFiniteMeasure (P.map W) := inferInstance
  refine ext_of_generate_finite (measurableCylinders fun _ : ι => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro t ht
    obtain ⟨s, S, -, hts⟩ := (mem_measurableCylinders t).1 ht
    have hc : MeasurableSet t := MeasurableSet.of_mem_measurableCylinders ht
    rw [Measure.map_apply_of_aemeasurable hW hc, Measure.map_apply_of_aemeasurable hF hc]
    refine measure_congr ?_
    have hall : ∀ᵐ ω ∂P, ∀ i : s, W ω i = F ω i := ae_all_iff.2 fun i => h i
    filter_upwards [hall] with ω hω
    have e : s.restrict (W ω) = s.restrict (F ω) := funext fun i => hω i
    change (W ω ∈ t) = (F ω ∈ t)
    rw [hts]
    change (s.restrict (W ω) ∈ S) = (s.restrict (F ω) ∈ S)
    rw [e]
  · rw [Measure.map_apply_of_aemeasurable hW MeasurableSet.univ,
      Measure.map_apply_of_aemeasurable hF MeasurableSet.univ]
    rfl

theorem tvDist_map_le_of_coord [IsFiniteMeasure P] {W F : Ω → ι → ℝ} (hW : AEMeasurable W P)
    (hF : AEMeasurable F P) (G : Set Ω) (h : ∀ i, ∀ᵐ ω ∂P, ω ∈ G → W ω i = F ω i) :
    TV.tvDist (P.map W) (P.map F) ≤ P Gᶜ := by
  classical
  set M := toMeasurable P Gᶜ with hMdef
  have hM : MeasurableSet M := measurableSet_toMeasurable P Gᶜ
  have hGM : Gᶜ ⊆ M := subset_toMeasurable P Gᶜ
  set W' : Ω → ι → ℝ := M.piecewise hF.mk hW.mk with hW'
  have hW'm : Measurable W' := hF.measurable_mk.piecewise hM hW.measurable_mk
  have e : P.map W' = P.map F := by
    refine map_eq_of_coord_ae_eq hW'm.aemeasurable hF fun i => ?_
    filter_upwards [hW.ae_eq_mk, hF.ae_eq_mk, h i] with ω h1 h2 h3
    by_cases hω : ω ∈ M
    · simp only [hW', Set.piecewise_eq_of_mem _ _ _ hω, ← h2]
    · have hG : ω ∈ G := by
        by_contra hG; exact hω (hGM hG)
      simp only [hW', Set.piecewise_eq_of_notMem _ _ _ hω, ← h1]
      exact h3 hG
  rw [← e]
  refine (tvDist_map_le_of_ae_eq_off hW hW'm.aemeasurable M ?_).trans (measure_toMeasurable _).le
  filter_upwards [hW.ae_eq_mk] with ω h1 hω
  simp only [hW', Set.piecewise_eq_of_notMem _ _ _ hω, h1]

end General

/-! ## Measurability of the model's window data -/

theorem rescale_apply_eq (x : FieldSample) (Q a : ℝ) (μ : Measure ℂ) :
    rescale x Q a μ = evalReg x (μ.map fun z => (a : ℂ) * z) +
      Q * ((μ Set.univ).toReal * Real.log ‖(a : ℂ)‖) := by
  have hd : ∀ z : ℂ, deriv (fun z : ℂ => (a : ℂ) * z) z = a := fun z => by simp
  simp only [rescale, coordChange, hd, integral_const, smul_eq_mul, Measure.real]

theorem measurable_resField_rescale (K : ℕ) (Q : ℝ) :
    Measurable fun p : FieldSample × ℝ => resField K (rescale p.1 Q p.2) := by
  refine Measurable.of_eval fun μ => ?_
  have : IsFiniteMeasure μ.1 := μ.2.1.1
  have e : (fun p : FieldSample × ℝ => resField K (rescale p.1 Q p.2) μ) = fun p =>
      evalReg p.1 (μ.1.map fun z => (p.2 : ℂ) * z) +
        Q * ((μ.1 Set.univ).toReal * Real.log ‖(p.2 : ℂ)‖) := by
    funext p; exact rescale_apply_eq p.1 Q p.2 μ.1
  have hm : Measurable fun p : FieldSample × ℝ =>
      evalReg p.1 (μ.1.map fun z => (p.2 : ℂ) * z) +
        Q * ((μ.1 Set.univ).toReal * Real.log ‖(p.2 : ℂ)‖) :=
    (measurable_evalReg_map_mul μ.1).add (measurable_const.mul (measurable_const.mul
      (Real.measurable_log.comp (measurable_norm.comp (Complex.measurable_ofReal.comp
        measurable_snd)))))
  exact (congrArg Measurable e).mpr hm

theorem aemeasurable_resField_n2Emb {γ α L r : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} (hα : α < Qc γ) (hr : 0 < r)
    (hX : IsFreeGFFModConstH X P) (K : ℕ) :
    AEMeasurable (fun ω => resField K (n2Emb γ α L r X ω)) P := by
  have hM : Measurable (n2Model γ α L r X) :=
    (measurable_locModel γ L r).comp ((measurable_localZ hX hr).prodMk measurable_const)
  have hT := aemeasurable_Tc (c := n2Lev γ α L r) (isBrownianReal_zRadB hX hr) hα
  have hS' : AEMeasurable (fun ω => r * Real.exp
      (-ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω)) P :=
    aemeasurable_const.mul (Real.measurable_exp.comp_aemeasurable hT.neg)
  have hS : AEMeasurable (n2EmbScale γ α L r X) P := hS'
  have h := (measurable_resField_rescale K (Qc γ)).comp_aemeasurable (hM.aemeasurable.prodMk hS)
  exact h

/-! ## The wedge side -/

theorem neg_log_le_of_norm_le {K : ℕ} (hK : 0 < K) {z : ℂ} (hz : ‖z‖ ≤ K) :
    -Real.log K ≤ -Real.log ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | h0
  · simp only [norm_zero, Real.log_zero, neg_zero, neg_nonpos]
    exact Real.log_nonneg (by exact_mod_cast hK)
  · exact neg_le_neg (Real.log_le_log (norm_pos_iff.2 h0) hz)

theorem ae_resField_wedgeV_eq {γ α : ℝ} {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''}
    {X'' : Ω'' → FieldSample} {A : ℝ → Ω'' → ℝ} (hA : IsWedgeProcess α (Qc γ) A P'') {K : ℕ}
    (hK : 0 < K) :
    ∀ᵐ ω ∂P'', resField K (wedgeV γ X'' A ω) = heartW γ K (latY'' K X'' ω, radR'' K A ω) := by
  filter_upwards [WedgeCan4.ae_continuous_wedgeProcess hA] with ω hc
  have hc' : Continuous (radR'' K A ω) :=
    hc.comp (continuous_id.max continuous_const)
  funext μ
  simp only [resField, wedgeV, wedgeField, heartW, heartPsi, latY'', Pi.add_apply,
    WedgeLaw.extP_of_continuous hc']
  congr 1
  refine integral_congr_ae ?_
  obtain ⟨r', hr', h0⟩ := μ.2.2
  have hae : ∀ᵐ z ∂μ.1, z ∈ Metric.closedBall (((0 : ℝ) : ℂ)) r' := by
    rw [ae_iff]; simpa only [compl_def] using h0
  filter_upwards [hae] with z hz
  have hz' : ‖z‖ ≤ K := by
    rw [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right] at hz; linarith
  simp only [radR'', max_eq_left (neg_log_le_of_norm_le hK hz')]

end D3Plus
end QuantumZipper
