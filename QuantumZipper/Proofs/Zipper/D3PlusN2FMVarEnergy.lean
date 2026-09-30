import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPotDef
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarAdm
import QuantumZipper.Proofs.GFF.K3.MixedM6Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, part E (2): energies from the Lipschitz potential

Task N2Z-FMVAR. `n2ZFMEnergy_of_potLip : FMPotLipStmt → N2ZFMEnergyStmt`.

The Neumann energy of a balanced admissible pair `(A, B)` is `∫ Φ dA − ∫ Φ dB` with
`Φ = ∫ neumannH(·, y) d(A − B)(y)` (`kernelCov2_self_eq_pot`). The first-mode measures are images
of the fixed measure `fmBase ⊗ (uniform angle)` under `(θ, φ) ↦ foldH(w + v e^{iθ} + s e^{iφ})`,
so for an `L`-Lipschitz `F` on `Hbar` the integrals against two of them differ by at most
`fmBase(ℂ) L (‖Δw‖ + ‖Δv‖ + |Δs|)` (`abs_integral_fmMeas_sub_le`; synchronous coupling,
`foldH` is 1-Lipschitz). With the potential Lipschitz bound `2π/τ` of `FMPotLipStmt` this gives
`≤ 4π fmBase(ℂ)` for a pair and `≤ 12π fmBase(ℂ) (‖Δw‖ + |Δτ| + |Δs|)/τ` for increments.
Own elementary argument (the standard "energy = potential integral + Lipschitz coupling" bound).
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace QuantumZipper
namespace D3Plus

/-! ## Lipschitz functions and folded circles -/

section Coupling

variable {F : ℂ → ℝ} {L : ℝ}

theorem continuousOn_of_lipHbar (hL : 0 ≤ L)
    (hF : ∀ x ∈ Hbar, ∀ x' ∈ Hbar, |F x - F x'| ≤ L * ‖x - x'‖) : ContinuousOn F Hbar := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (L + 1), by positivity, fun {y} hy hyx => ?_⟩
  rw [Real.dist_eq]
  rw [dist_eq_norm] at hyx
  have h1 := hF y hy x hx
  have h2 : L * ‖y - x‖ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hyx.le hL
  have h3 : L * (ε / (L + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  linarith

theorem abs_integral_fc_sub_le (hFm : Measurable F) (hL : 0 ≤ L)
    (hF : ∀ x ∈ Hbar, ∀ x' ∈ Hbar, |F x - F x'| ≤ L * ‖x - x'‖) (z z' : ℂ) (s s' : ℝ) :
    |∫ x, F x ∂foldedCircle z s - ∫ x, F x ∂foldedCircle z' s'| ≤ L * (‖z - z'‖ + |s - s'|) := by
  rw [TwoPoint.integral_foldedCircle_eq hFm, TwoPoint.integral_foldedCircle_eq hFm, ← mul_sub]
  have hc : ∀ (z : ℂ) (s : ℝ), Continuous fun θ => F (foldH (circleMap z s θ)) := fun z s =>
    (continuousOn_of_lipHbar hL hF).comp_continuous
      (CircleFubini.continuous_foldH'.comp (continuous_circleMap z s))
      (fun θ => CircleFubini.foldH_mem_Hbar' _)
  rw [← integral_sub ((hc z s).integrableOn_Icc.mono_set Ico_subset_Icc_self)
    ((hc z' s').integrableOn_Icc.mono_set Ico_subset_Icc_self)]
  have hb : ∀ θ ∈ Ico (0 : ℝ) (2 * π),
      ‖F (foldH (circleMap z s θ)) - F (foldH (circleMap z' s' θ))‖ ≤ L * (‖z - z'‖ + |s - s'|) := by
    intro θ _
    rw [Real.norm_eq_abs]
    refine (hF _ (CircleFubini.foldH_mem_Hbar' _) _ (CircleFubini.foldH_mem_Hbar' _)).trans ?_
    refine mul_le_mul_of_nonneg_left ((RegSample.norm_foldH_sub_le _ _).trans ?_) hL
    simp only [circleMap]
    calc ‖z + (s : ℂ) * Complex.exp (θ * Complex.I) - (z' + (s' : ℂ) * Complex.exp (θ * Complex.I))‖
        = ‖(z - z') + ((s - s' : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
          congr 1; push_cast; ring
      _ ≤ ‖z - z'‖ + ‖((s - s' : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := norm_add_le _ _
      _ = ‖z - z'‖ + |s - s'| := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs]
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ico_lt_top hb
  rw [Real.volume_real_Ico_of_le (by positivity), Real.norm_eq_abs] at hI
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  calc (2 * π)⁻¹ * |∫ θ in Ico 0 (2 * π), _| ≤ (2 * π)⁻¹ * (L * (‖z - z'‖ + |s - s'|) * (2 * π - 0)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = L * (‖z - z'‖ + |s - s'|) := by field_simp; ring

theorem integrable_fmMeas_of_lip (hFm : Measurable F)
    (hF : ∀ x ∈ Hbar, ∀ x' ∈ Hbar, |F x - F x'| ≤ L * ‖x - x'‖) (w v : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable F (fmMeas w v s) := by
  have : IsFiniteMeasure (fmMeas w v s) := CircleFubini.isFiniteMeasure_bind_circle _
  refine Integrable.of_bound hFm.aestronglyMeasurable (|F 0| + |L| * (‖w‖ + ‖v‖ + s)) ?_
  have h1 : ∀ᵐ x ∂fmMeas w v s, ‖x‖ ≤ ‖w‖ + ‖v‖ + s :=
    RegCont.ae_norm_bindFc_le hs (ae_norm_fmArc_le w v)
  have h2 : ∀ᵐ x ∂fmMeas w v s, x ∈ Hbar := RegCont.ae_mem_Hbar_bindFc _ _
  filter_upwards [h1, h2] with x hx hxH
  rw [Real.norm_eq_abs]
  have := hF x hxH 0 (by simp [Hbar])
  rw [sub_zero] at this
  have h3 : L * ‖x‖ ≤ |L| * (‖w‖ + ‖v‖ + s) :=
    (le_abs_self L |> fun h => mul_le_mul_of_nonneg_right h (norm_nonneg x)).trans
      (mul_le_mul_of_nonneg_left hx (abs_nonneg L))
  have := abs_sub_abs_le_abs_sub (F x) (F 0)
  linarith

/-- **Synchronous coupling bound** for the first-mode measures. -/
theorem abs_integral_fmMeas_sub_le (hFm : Measurable F) (hL : 0 ≤ L)
    (hF : ∀ x ∈ Hbar, ∀ x' ∈ Hbar, |F x - F x'| ≤ L * ‖x - x'‖) (w v w' v' : ℂ) {s s' : ℝ}
    (hs : 0 ≤ s) (hs' : 0 ≤ s') :
    |∫ x, F x ∂fmMeas w v s - ∫ x, F x ∂fmMeas w' v' s'| ≤
      fmBase.real univ * (L * (‖w - w'‖ + ‖v - v'‖ + |s - s'|)) := by
  obtain ⟨hi1, e1⟩ := CircleFubini.integral_bind_circle (r := s) (fmArc w v)
    (integrable_fmMeas_of_lip hFm hF w v hs)
  obtain ⟨hi2, e2⟩ := CircleFubini.integral_bind_circle (r := s') (fmArc w' v')
    (integrable_fmMeas_of_lip hFm hF w' v' hs')
  unfold fmMeas
  rw [e1, e2]
  unfold fmArc at hi1 hi2 ⊢
  have j1 : Integrable (fun θ : ℝ => ∫ x, F x ∂foldedCircle
      (w + v * Complex.exp ((θ : ℂ) * Complex.I)) s) fmBase :=
    (integrable_map_measure hi1.aestronglyMeasurable (measurable_fmArcMap w v).aemeasurable).1 hi1
  have j2 : Integrable (fun θ : ℝ => ∫ x, F x ∂foldedCircle
      (w' + v' * Complex.exp ((θ : ℂ) * Complex.I)) s') fmBase :=
    (integrable_map_measure hi2.aestronglyMeasurable
      (measurable_fmArcMap w' v').aemeasurable).1 hi2
  rw [integral_map (measurable_fmArcMap w v).aemeasurable hi1.aestronglyMeasurable,
    integral_map (measurable_fmArcMap w' v').aemeasurable hi2.aestronglyMeasurable,
    ← integral_sub j1 j2, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun θ => ?_)).trans
    (le_of_eq (mul_comm _ _))
  rw [Real.norm_eq_abs]
  refine (abs_integral_fc_sub_le hFm hL hF _ _ s s').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hL
  have : w + v * Complex.exp ((θ : ℂ) * Complex.I) - (w' + v' * Complex.exp ((θ : ℂ) * Complex.I)) =
      (w - w') + (v - v') * Complex.exp ((θ : ℂ) * Complex.I) := by ring
  rw [this]
  have h := norm_add_le (w - w') ((v - v') * Complex.exp ((θ : ℂ) * Complex.I))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at h
  linarith

end Coupling

/-! ## Energy as a potential integral -/

theorem integrable_neumannH_right_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℂ) :
    Integrable (fun y => neumannH x y) ν := by
  exact (K3.integrable_neumannH_right_K3 hν x).congr
    (Filter.Eventually.of_forall fun y => neumannH_symm y x)

theorem measurable_pot (μ : Measure ℂ) [SFinite μ] :
    Measurable fun x => ∫ y, neumannH x y ∂μ :=
  (TwoPoint.measurable_neumannH_uncurry.stronglyMeasurable.integral_prod_right'
    (ν := μ)).measurable

theorem kernelCov2_self_eq_pot {A B : Measure ℂ} (hA : IsAdmissibleH A) (hB : IsAdmissibleH B) :
    kernelCov2 neumannH (A, B) (A, B) =
      (∫ x, ((∫ y, neumannH x y ∂A) - ∫ y, neumannH x y ∂B) ∂A) -
        ∫ x, ((∫ y, neumannH x y ∂A) - ∫ y, neumannH x y ∂B) ∂B := by
  have := hA.1
  have := hB.1
  unfold kernelCov2 kernelCov
  have iAA := (integrable_neumannH_prod hA hA).integral_prod_left
  have iAB := (integrable_neumannH_prod hA hB).integral_prod_left
  have iBA := (integrable_neumannH_prod hB hA).integral_prod_left
  have iBB := (integrable_neumannH_prod hB hB).integral_prod_left
  simp only at iAA iAB iBA iBB ⊢
  rw [integral_sub iAA iAB, integral_sub iBA iBB]
  ring

/-! ## The energy node -/

theorem norm_ofReal_mul_unit {u : ℂ} (hu : ‖u‖ = 1) (a : ℝ) : ‖(a : ℂ) * u‖ = |a| := by
  rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem measurable_fmPot (w v : ℂ) (s : ℝ) : Measurable (fmPot w v s) := by
  have : IsFiniteMeasure (fmMeas w v s) := CircleFubini.isFiniteMeasure_bind_circle _
  have : IsFiniteMeasure (fmMeas w (-v) s) := CircleFubini.isFiniteMeasure_bind_circle _
  exact (measurable_pot _).sub (measurable_pot _)

/-- **Part E from the potential bound.** -/
theorem n2ZFMEnergy_of_potLip (hP : FMPotLipStmt) : N2ZFMEnergyStmt := by
  intro m
  set B : ℝ := fmBase.real univ with hBdef
  have hB : 0 ≤ B := measureReal_nonneg
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine ⟨24 * π * B, by positivity, 1 / (8 * ((m : ℝ) + 1)), by positivity, ?_⟩
  intro u hu w w' _ _ hw hw' τ τ' hτ hτ₀ hττ' hτ'τ s s' hs0 hsτ hs0' hs'τ'
  have hτ' : 0 < τ' := by linarith
  have e8 : 1 / (8 * ((m : ℝ) + 1)) = (1 / ((m : ℝ) + 1)) / 8 := by field_simp
  have hi0 : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have h3 : 3 * τ ≤ w.im := by rw [e8] at hτ₀; linarith
  have h3' : 3 * τ' ≤ w'.im := by rw [e8] at hτ₀; linarith
  have hnu : ‖(τ : ℂ) * u‖ = τ := by rw [norm_ofReal_mul_unit hu, abs_of_pos hτ]
  have hnu' : ‖(τ' : ℂ) * u‖ = τ' := by rw [norm_ofReal_mul_unit hu, abs_of_pos hτ']
  have hadm : ∀ (w₀ v₀ : ℂ) (t σ : ℝ), 0 < t → 0 ≤ σ → σ ≤ t → 3 * t ≤ w₀.im → ‖v₀‖ = t →
      IsAdmissibleH (fmMeas w₀ v₀ σ) := fun w₀ v₀ t σ ht hσ hσt h3t hv =>
    fmAdmStmt_holds w₀ v₀ σ hσ (by rw [hv]; exact ht) (by rw [hv]; linarith)
  have aP := hadm w _ τ s hτ hs0 hsτ h3 hnu
  have aN := hadm w (-((τ : ℂ) * u)) τ s hτ hs0 hsτ h3 (by rw [norm_neg, hnu])
  have aP' := hadm w' _ τ' s' hτ' hs0' hs'τ' h3' hnu'
  have aN' := hadm w' (-((τ' : ℂ) * u)) τ' s' hτ' hs0' hs'τ' h3' (by rw [norm_neg, hnu'])
  have hL := hP u w τ s hu hτ hs0 hsτ h3
  have hL' := hP u w' τ' s' hu hτ' hs0' hs'τ' h3'
  have hLpos : 0 ≤ 2 * π / τ := by positivity
  constructor
  · rw [kernelCov2_self_eq_pot aP aN]
    have hc := abs_integral_fmMeas_sub_le (measurable_fmPot w ((τ : ℂ) * u) s) hLpos hL
      w ((τ : ℂ) * u) w (-((τ : ℂ) * u)) hs0 hs0
    have e2 : ‖(τ : ℂ) * u - -((τ : ℂ) * u)‖ = 2 * τ := by
      rw [sub_neg_eq_add, ← two_mul, norm_mul, hnu]; norm_num
    rw [sub_self, norm_zero, sub_self, abs_zero, e2] at hc
    have e3 : B * (2 * π / τ * (0 + 2 * τ + 0)) = 4 * π * B := by field_simp; ring
    rw [e3] at hc
    have : 4 * π * B ≤ 24 * π * B := by nlinarith [Real.pi_pos]
    exact (le_abs_self _).trans (hc.trans this)
  · set P := fmMeas w ((τ : ℂ) * u) s
    set N := fmMeas w (-((τ : ℂ) * u)) s
    set P' := fmMeas w' ((τ' : ℂ) * u) s'
    set N' := fmMeas w' (-((τ' : ℂ) * u)) s'
    set Φ : ℂ → ℝ := fun x => fmPot w ((τ : ℂ) * u) s x - fmPot w' ((τ' : ℂ) * u) s' x with hΦ
    set L : ℝ := 2 * π / τ + 2 * π / τ' with hLdef
    have hL0 : 0 ≤ L := by positivity
    have hΦL : ∀ x ∈ Hbar, ∀ x' ∈ Hbar, |Φ x - Φ x'| ≤ L * ‖x - x'‖ := by
      intro x hx x' hx'
      have a1 := hL x hx x' hx'
      have a2 := hL' x hx x' hx'
      have : Φ x - Φ x' = (fmPot w ((τ : ℂ) * u) s x - fmPot w ((τ : ℂ) * u) s x') -
          (fmPot w' ((τ' : ℂ) * u) s' x - fmPot w' ((τ' : ℂ) * u) s' x') := by
        simp only [hΦ]; ring
      rw [this, hLdef, add_mul]
      exact (abs_sub _ _).trans (add_le_add a1 a2)
    have hΦm : Measurable Φ := (measurable_fmPot _ _ _).sub (measurable_fmPot _ _ _)
    have hpot : (fun x => (∫ y, neumannH x y ∂(P + N')) - ∫ y, neumannH x y ∂(N + P')) = Φ := by
      funext x
      rw [integral_add_measure (integrable_neumannH_right_adm aP x)
          (integrable_neumannH_right_adm aN' x),
        integral_add_measure (integrable_neumannH_right_adm aN x)
          (integrable_neumannH_right_adm aP' x)]
      simp only [hΦ, fmPot, P, N, P', N']
      ring
    rw [kernelCov2_self_eq_pot (isAdmissibleH_add aP aN') (isAdmissibleH_add aN aP'), hpot]
    have iP := integrable_fmMeas_of_lip hΦm hΦL w ((τ : ℂ) * u) hs0
    have iN := integrable_fmMeas_of_lip hΦm hΦL w (-((τ : ℂ) * u)) hs0
    have iP' := integrable_fmMeas_of_lip hΦm hΦL w' ((τ' : ℂ) * u) hs0'
    have iN' := integrable_fmMeas_of_lip hΦm hΦL w' (-((τ' : ℂ) * u)) hs0'
    rw [integral_add_measure iP iN', integral_add_measure iN iP']
    have c1 := abs_integral_fmMeas_sub_le hΦm hL0 hΦL w ((τ : ℂ) * u) w' ((τ' : ℂ) * u) hs0 hs0'
    have c2 := abs_integral_fmMeas_sub_le hΦm hL0 hΦL w (-((τ : ℂ) * u)) w'
      (-((τ' : ℂ) * u)) hs0 hs0'
    have ev : (τ : ℂ) * u - (τ' : ℂ) * u = ((τ - τ' : ℝ) : ℂ) * u := by push_cast; ring
    have ev' : -((τ : ℂ) * u) - -((τ' : ℂ) * u) = ((τ' - τ : ℝ) : ℂ) * u := by push_cast; ring
    rw [ev, norm_ofReal_mul_unit hu] at c1
    rw [ev', norm_ofReal_mul_unit hu, abs_sub_comm τ' τ] at c2
    set δ := ‖w - w'‖ + |τ - τ'| + |s - s'| with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hLτ : L ≤ 6 * π / τ := by
      rw [hLdef]
      have : 2 * π / τ' ≤ 4 * π / τ := by
        rw [div_le_div_iff₀ hτ' hτ]; nlinarith [Real.pi_pos]
      have e : 6 * π / τ = 2 * π / τ + 4 * π / τ := by ring
      linarith
    have key : |(∫ x, Φ x ∂P + ∫ x, Φ x ∂N') - (∫ x, Φ x ∂N + ∫ x, Φ x ∂P')| ≤
        2 * (B * (L * δ)) := by
      have : (∫ x, Φ x ∂P + ∫ x, Φ x ∂N') - (∫ x, Φ x ∂N + ∫ x, Φ x ∂P') =
          (∫ x, Φ x ∂P - ∫ x, Φ x ∂P') - (∫ x, Φ x ∂N - ∫ x, Φ x ∂N') := by ring
      rw [this]
      exact (abs_sub _ _).trans (by linarith)
    have hfin : 2 * (B * (L * δ)) ≤ 24 * π * B * δ / τ := by
      rw [le_div_iff₀ hτ]
      have h1 : L * τ ≤ 6 * π := by
        have := mul_le_mul_of_nonneg_right hLτ hτ.le
        rwa [div_mul_cancel₀ _ hτ.ne'] at this
      have h2 : 0 ≤ B * δ := mul_nonneg hB hδ0
      nlinarith [mul_le_mul_of_nonneg_left h1 h2, Real.pi_pos]
    exact (le_abs_self _).trans (key.trans hfin)

end D3Plus
end QuantumZipper
