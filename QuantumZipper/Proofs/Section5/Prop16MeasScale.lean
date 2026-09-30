import QuantumZipper.Proofs.Section5.Prop16MeasArea

/-!
# Proposition 1.6, node D4-MEAS (part 4): measurability of the local scale parameter

In the setting of `Prop16MeasArea` (a measurable family of samples `x p` on random domains `U p`
with a measurable cut-off family), `scaleParamOn γ (x p) (U p)` is a.e.-measurable as soon as the
event `goodSet` (the local area measure is a genuine vague limit) is null-measurable:

* `measure_eq_M`: on good samples `qAreaMeasureOn γ (x p) (U p) (B_a(0) ∩ ℍ)` is the supremum over
  `n` of the limits of the pre-limit integrals of `openBump (B_a ∩ ℍ) n · φ n p`;
* `aemeasurable_scaleParamOn`: `sInf` of an up-closed set tested at rationals
  (`LQGMeas.measurable_sInf_upClosed`), on a measurable subset of `goodSet` of full measure in
  it; off `goodSet` the measure is the junk `0` and `scaleParamOn = sInf ∅ = 0`.

Own elementary proof (AGENT_GUIDE cost rule), following `LQGMeas.measurable_scaleParam_good`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace Meas

open LQGMeas

variable {α : Type*} [MeasurableSpace α]
variable {γ : ℝ} {x : α → FieldSample} {U : α → Set ℂ} {φ : ℕ → α → ℂ → ℝ}

/-- The half-ball `B_a(0) ∩ ℍ`. -/
abbrev hb (a : ℝ) : Set ℂ := Metric.ball (0 : ℂ) a ∩ H

theorem isOpen_hb (a : ℝ) : IsOpen (hb a) := Metric.isOpen_ball.inter isOpen_H

theorem openBump_eventually_one {W : Set ℂ} (hW : IsOpen W) (hWc : Wᶜ.Nonempty) {z : ℂ}
    (hz : z ∈ W) : ∀ᶠ n in atTop, openBump W n z = 1 := by
  have hd : 0 < Metric.infDist z Wᶜ :=
    (hW.isClosed_compl.notMem_iff_infDist_pos hWc).1 (fun h => h hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / Metric.infDist z Wᶜ)
  filter_upwards [eventually_ge_atTop n] with k hk
  have h2 : 2 ≤ (k : ℝ) * Metric.infDist z Wᶜ := by
    rw [div_lt_iff₀ hd] at hn
    have : (n : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [openBump, max_eq_right (by linarith), min_eq_left (by linarith)]

/-- The measurable proxy for `qAreaMeasureOn γ (x p) (U p) (B_a ∩ ℍ)`. -/
def M (γ : ℝ) (x : α → FieldSample) (φ : ℕ → α → ℂ → ℝ) (p : α) (a : ℝ) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (Psi γ x (fun p z => openBump (hb a) n z * φ n p z) p)

theorem measurable_M (hx : Measurable x) (hφ : IsBumpFamily U φ) (a : ℝ) :
    Measurable fun p => M γ x φ p a :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp (measurable_Psi γ hx
    (((continuous_openBump _ n).measurable.comp measurable_snd).mul (hφ.meas n)))

theorem measure_eq_M (hφ : IsBumpFamily U φ) {p : α} (hp : p ∈ goodSet γ x U) (a : ℝ) :
    qAreaMeasureOn γ (x p) (U p) (hb a) = M γ x φ p a := by
  set m := qAreaMeasureOn γ (x p) (U p) with hmdef
  have hm : IsVagueLimitOn (U p) (areaApprox γ (x p)) m := isVagueLimitOn_qAreaMeasureOn hp
  have hWc : (hb a)ᶜ.Nonempty := ⟨0, fun h => by simpa [H] using h.2⟩
  have hbd : Bornology.IsBounded (hb a) := Metric.isBounded_ball.subset inter_subset_left
  have hcont : ∀ n, Continuous fun z => openBump (hb a) n z * φ n p z := fun n =>
    (continuous_openBump _ n).mul (hφ.cont n p)
  have h0 : ∀ n z, 0 ≤ openBump (hb a) n z * φ n p z := fun n z =>
    mul_nonneg (openBump_nonneg _ n z) (hφ.nonneg n p z)
  have e1 : ∀ n, ENNReal.ofReal (Psi γ x (fun p z => openBump (hb a) n z * φ n p z) p) =
      ∫⁻ z, ENNReal.ofReal (openBump (hb a) n z * φ n p z) ∂m := fun n => by
    rw [← integral_eq_Psi (g := fun p z => openBump (hb a) n z * φ n p z) hp (hcont n)
      ((hasCompactSupport_openBump hbd n).mul_right)
      ((tsupport_mul_subset_right).trans (hφ.tsupp n p))]
    exact ofReal_integral_eq_lintegral_ofReal
      (GoodSample.integrable_of_tsupport hm.2.1 (hcont n)
        ((hasCompactSupport_openBump hbd n).mul_right)
        ((tsupport_mul_subset_right).trans (hφ.tsupp n p))) (ae_of_all _ (h0 n))
  unfold M
  simp_rw [e1]
  rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (openBump (hb a) n z * φ n p z))
      (fun n => ENNReal.measurable_ofReal.comp (hcont n).measurable)
      (fun i j hij z => ENNReal.ofReal_le_ofReal (mul_le_mul (openBump_mono _ z hij)
        (hφ.mono p z hij) (hφ.nonneg i p z) (openBump_nonneg _ j z))),
    ← lintegral_indicator_one (isOpen_hb a).measurableSet]
  have hae : ∀ᵐ z ∂m, z ∈ U p := ae_iff.2 hm.1
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with z hz
  by_cases hzW : z ∈ hb a
  · rw [indicator_of_mem hzW, Pi.one_apply]
    refine le_antisymm ?_ (iSup_le fun n => ENNReal.ofReal_le_one.2
      (mul_le_one₀ (openBump_le_one _ n z) (hφ.nonneg n p z) (hφ.le_one n p z)))
    obtain ⟨n, hn1, hn2⟩ := ((openBump_eventually_one (isOpen_hb a) hWc hzW).and
      (bump_eventually_one hφ hz)).exists
    exact le_iSup_of_le n (by rw [hn1, hn2, mul_one, ENNReal.ofReal_one])
  · rw [indicator_of_notMem hzW]
    refine le_antisymm zero_le (iSup_le fun n => ?_)
    have : openBump (hb a) n z = 0 := by
      by_contra h
      exact hzW (tsupport_openBump_subset _ n (subset_tsupport _ h))
    rw [this, zero_mul, ENNReal.ofReal_zero]

omit [MeasurableSpace α] in
theorem scaleParamOn_of_not {p : α} (hp : p ∉ goodSet γ x U) :
    scaleParamOn γ (x p) (U p) = 0 := by
  have : {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasureOn γ (x p) (U p) (Metric.ball 0 a ∩ H)} = ∅ := by
    ext a
    simp [qAreaMeasureOn_of_not hp]
  simp only [scaleParamOn, this, Real.sInf_empty]

/-- **Scale parameter, generic form.** -/
theorem aemeasurable_scaleParamOn {μ : Measure α} (hx : Measurable x) (hφ : IsBumpFamily U φ)
    (hG : NullMeasurableSet (goodSet γ x U) μ) :
    AEMeasurable (fun p => scaleParamOn γ (x p) (U p)) μ := by
  classical
  obtain ⟨G', hG'G, hG'm, hG'ae⟩ := hG.exists_measurable_subset_ae_eq
  set F : α → ℝ := fun p => scaleParamOn γ (x p) (U p) with hF
  have e1 : F = (goodSet γ x U).indicator F := by
    funext p
    by_cases hp : p ∈ goodSet γ x U
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp]; exact scaleParamOn_of_not hp
  have hmeasG' : Measurable (G'.indicator F) := by
    refine measurable_of_restrict_of_restrict_compl hG'm ?_ ?_
    · have e : G'.domRestrict (G'.indicator F) = fun p : G' => F p :=
        funext fun p => by show G'.indicator F p = F p; exact indicator_of_mem p.2 F
      rw [e]
      have hS : ∀ q : ℚ, MeasurableSet {p : G' | (q : ℝ) ∈
          {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasureOn γ (x p) (U p) (Metric.ball 0 a ∩ H)}} := by
        intro q
        have e2 : {p : G' | (q : ℝ) ∈
            {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasureOn γ (x p) (U p) (Metric.ball 0 a ∩ H)}} =
            {p : G' | 0 < (q : ℝ) ∧ 1 ≤ M γ x φ p q} := by
          ext p
          simp only [mem_setOf_eq]
          rw [← measure_eq_M hφ (hG'G p.2) q]
        rw [e2]
        exact (MeasurableSet.const _).inter (measurableSet_le measurable_const
          ((measurable_M hx hφ q).comp measurable_subtype_coe))
      exact measurable_sInf_upClosed
        (fun p : G' => {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasureOn γ (x p) (U p) (Metric.ball 0 a ∩ H)})
        hS (fun p a b ha hab => ⟨ha.1.trans_le hab, ha.2.trans (measure_mono
          (inter_subset_inter_left _ (Metric.ball_subset_ball hab)))⟩) (fun p a ha => ha.1)
    · have e : G'ᶜ.domRestrict (G'.indicator F) = fun _ => 0 :=
        funext fun p => by show G'.indicator F p = 0; exact indicator_of_notMem p.2 F
      rw [e]
      exact measurable_const
  refine ⟨G'.indicator F, hmeasG', ?_⟩
  have h1 : F =ᵐ[μ] (goodSet γ x U).indicator F := Eventually.of_forall fun p => congrFun e1 p
  exact h1.trans (indicator_ae_eq_of_ae_eq_set hG'ae.symm)

end Meas

end Prop16Area

end QuantumZipper
