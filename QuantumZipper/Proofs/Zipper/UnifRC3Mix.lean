import QuantumZipper.Proofs.Zipper.RegContEnergy
import QuantumZipper.Proofs.GFF.Existence
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.LQG.CoordChangeKernel

/-!
# UNIF-RC3-MIX (decision D33): the Neumann energy of a mixture of differences

For a probability measure `A`, a measurable map `ψ` and two radii `ρ, ρ'`, the circle-smoothed
pushed measures are mixtures

`M = (A ⋆ fc(·, ρ))_* ψ = ∫ L_z dA(z)`, `L_z = ψ_* fc(z, ρ)`, and likewise `M'`, `L'_z` for `ρ'`.

**Main result** `abs_kernelCov2_mix_le`: if every `L_z, L'_z` is a `α`-Frostman probability
measure supported in `closedBall 0 B ∩ Hbar` (`GoodM`), and the Neumann energy of `L_z − L'_z`
is `≤ K` for `A`-a.e. `z`, then the Neumann energy of `M − M'` is `≤ K`.

This is the `sup` form of `E(∫ (L_z − L'_z) dA) ≤ (∫ √E_z dA)²`, which is what E1/E2 use.
Proof: the Neumann kernel is a positive semidefinite form on balanced admissible pairs — the
Hilbert-space embedding `GFFExist.freeVec` with `⟪freeVec μ − freeVec ν, freeVec μ' − freeVec ν'⟫ =
kernelCov2 neumannH (μ, ν) (μ', ν')` (`GFFExist.freeVec_inner`) — so Cauchy–Schwarz gives
`|kernelCov2 (L_z − L'_z, L_w − L'_w)| ≤ K`; the bilinear form of the mixtures is the double
`A`-average of these (Fubini for circle mixtures, `CircleFubini.integral_bind_circle`, with the
Neumann potentials bounded by `TwoPoint.abs_neuPot_le`).

Also: `kernelCov2_self_nonneg` and the triangle inequality `kernelCov2_self_triangle` for
the energy (the free-boundary analogue of `ZeroRegBoundaryNA.kernelCov2_triangle`, but
deterministic).

Sources: Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab. 38 (2010),
Prop. 2.1 (energies of circle-average differences, via the variance of the field);
the Cauchy–Schwarz/Fubini bookkeeping is an own elementary argument.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint GFFExist

/-! ## The Neumann energy is a semi-inner product -/

section Inner

variable {p₁ p₂ q₁ q₂ : Measure ℂ}

theorem kernelCov2_eq_inner_freeVec (hp₁ : IsAdmissibleH p₁) (hp₂ : IsAdmissibleH p₂)
    (hq₁ : IsAdmissibleH q₁) (hq₂ : IsAdmissibleH q₂) (hp : p₁ univ = p₂ univ)
    (hq : q₁ univ = q₂ univ) :
    kernelCov2 neumannH (p₁, p₂) (q₁, q₂) =
      ⟪freeVec ⟨p₁, hp₁⟩ - freeVec ⟨p₂, hp₂⟩, freeVec ⟨q₁, hq₁⟩ - freeVec ⟨q₂, hq₂⟩⟫ :=
  (freeVec_inner ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ hp hq).symm

theorem kernelCov2_self_eq_norm_sq (hp₁ : IsAdmissibleH p₁) (hp₂ : IsAdmissibleH p₂)
    (hp : p₁ univ = p₂ univ) :
    kernelCov2 neumannH (p₁, p₂) (p₁, p₂) = ‖freeVec ⟨p₁, hp₁⟩ - freeVec ⟨p₂, hp₂⟩‖ ^ 2 := by
  rw [kernelCov2_eq_inner_freeVec hp₁ hp₂ hp₁ hp₂ hp hp, real_inner_self_eq_norm_sq]

/-- The Neumann energy of a balanced admissible pair is nonnegative. -/
theorem kernelCov2_self_nonneg (hp₁ : IsAdmissibleH p₁) (hp₂ : IsAdmissibleH p₂)
    (hp : p₁ univ = p₂ univ) : 0 ≤ kernelCov2 neumannH (p₁, p₂) (p₁, p₂) := by
  rw [kernelCov2_self_eq_norm_sq hp₁ hp₂ hp]; positivity

/-- **Cauchy–Schwarz for the Neumann energy**, in the form used below. -/
theorem abs_kernelCov2_le_of_energy (hp₁ : IsAdmissibleH p₁) (hp₂ : IsAdmissibleH p₂)
    (hq₁ : IsAdmissibleH q₁) (hq₂ : IsAdmissibleH q₂) (hp : p₁ univ = p₂ univ)
    (hq : q₁ univ = q₂ univ) {K : ℝ} (hEp : kernelCov2 neumannH (p₁, p₂) (p₁, p₂) ≤ K)
    (hEq : kernelCov2 neumannH (q₁, q₂) (q₁, q₂) ≤ K) :
    |kernelCov2 neumannH (p₁, p₂) (q₁, q₂)| ≤ K := by
  rw [kernelCov2_self_eq_norm_sq hp₁ hp₂ hp] at hEp
  rw [kernelCov2_self_eq_norm_sq hq₁ hq₂ hq] at hEq
  rw [kernelCov2_eq_inner_freeVec hp₁ hp₂ hq₁ hq₂ hp hq]
  set a := freeVec ⟨p₁, hp₁⟩ - freeVec ⟨p₂, hp₂⟩
  set b := freeVec ⟨q₁, hq₁⟩ - freeVec ⟨q₂, hq₂⟩
  refine (abs_real_inner_le_norm a b).trans ?_
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- **Triangle inequality for the Neumann energy.** -/
theorem kernelCov2_self_triangle {a b c : Measure ℂ} (ha : IsAdmissibleH a)
    (hb : IsAdmissibleH b) (hc : IsAdmissibleH c) (hab : a univ = b univ)
    (hbc : b univ = c univ) :
    kernelCov2 neumannH (a, c) (a, c) ≤
      2 * kernelCov2 neumannH (a, b) (a, b) + 2 * kernelCov2 neumannH (b, c) (b, c) := by
  rw [kernelCov2_self_eq_norm_sq ha hc (hab.trans hbc), kernelCov2_self_eq_norm_sq ha hb hab,
    kernelCov2_self_eq_norm_sq hb hc hbc]
  set u := freeVec ⟨a, ha⟩ - freeVec ⟨b, hb⟩
  set v := freeVec ⟨b, hb⟩ - freeVec ⟨c, hc⟩
  have e : freeVec ⟨a, ha⟩ - freeVec ⟨c, hc⟩ = u + v := by simp [u, v]
  rw [e]
  nlinarith [norm_add_le u v, norm_nonneg (u + v), norm_nonneg u, norm_nonneg v,
    sq_nonneg (‖u‖ - ‖v‖)]

/-- Symmetry of the Neumann bilinear form on admissible measures. -/
theorem kernelCov2_comm (hp₁ : IsAdmissibleH p₁) (hp₂ : IsAdmissibleH p₂)
    (hq₁ : IsAdmissibleH q₁) (hq₂ : IsAdmissibleH q₂) :
    kernelCov2 neumannH (p₁, p₂) (q₁, q₂) = kernelCov2 neumannH (q₁, q₂) (p₁, p₂) := by
  simp only [kernelCov2]
  rw [CoordChange.kernelCov_comm_of_admissible hp₁ hq₁,
    CoordChange.kernelCov_comm_of_admissible hp₁ hq₂,
    CoordChange.kernelCov_comm_of_admissible hp₂ hq₁,
    CoordChange.kernelCov_comm_of_admissible hp₂ hq₂]
  ring

end Inner

/-! ## Good measures and circle mixtures -/

/-- A probability measure that is `α`-Frostman with constant `C` and supported in
`closedBall 0 B ∩ Hbar`. -/
structure GoodM (κ : Measure ℂ) (α C B : ℝ) : Prop where
  prob : IsProbabilityMeasure κ
  frost : TwoPoint.IsFrostman κ α C
  supp : κ (closedBall 0 B ∩ Hbar)ᶜ = 0

theorem GoodM.admissible {κ : Measure ℂ} {α C B : ℝ} (h : GoodM κ α C B) (hα : 0 < α) :
    IsAdmissibleH κ :=
  have := h.prob
  FrostmanReg.isAdmissibleH_of_frostman h.supp (fun w r hr => h.frost w r hr) hα

theorem GoodM.univ_eq {κ κ' : Measure ℂ} {α C B α' C' B' : ℝ} (h : GoodM κ α C B)
    (h' : GoodM κ' α' C' B') : κ univ = κ' univ := by
  rw [h.prob.measure_univ, h'.prob.measure_univ]

/-- The common bound of the Neumann potentials of good measures on `closedBall 0 B`. -/
def potB (α C B : ℝ) : ℝ := 2 * (C / α) + 2 * Real.log (B + B + 1)

theorem measurableSet_closedBall_inter_Hbar (B : ℝ) :
    MeasurableSet (closedBall (0 : ℂ) B ∩ Hbar) :=
  measurableSet_closedBall.inter isClosed_Hbar.measurableSet

theorem ae_abs_neuPot_le {κ ν : Measure ℂ} {α C B : ℝ} (hκ : GoodM κ α C B) (hα : 0 < α)
    (hC : 0 ≤ C) (hB : 0 ≤ B) {ψ : ℂ → ℂ} (hψ : Measurable ψ)
    (hν : (ν.map ψ) (closedBall 0 B ∩ Hbar)ᶜ = 0) :
    ∀ᵐ y ∂ν, |neuPot κ (ψ y)| ≤ potB α C B := by
  have := hκ.prob
  have hsκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B :=
    (show ∀ᵐ y ∂κ, y ∈ closedBall 0 B ∩ Hbar from mem_ae_iff.2 hκ.supp).mono fun y hy => mem_closedBall_zero_iff.1 hy.1
  have hae : ∀ᵐ y ∂ν, ψ y ∈ closedBall 0 B ∩ Hbar :=
    ae_of_ae_map hψ.aemeasurable (mem_ae_iff.2 hν)
  filter_upwards [hae] with y hy
  have := abs_neuPot_le hκ.frost hα hC hB hsκ (X := B) (mem_closedBall_zero_iff.1 hy.1)
  rwa [probReal_univ, mul_one] at this

theorem map_bindFc_apply {A : Measure ℂ} [IsFiniteMeasure A] {ψ : ℂ → ℂ} (hψ : Measurable ψ) (ρ : ℝ) {S : Set ℂ}
    (hS : MeasurableSet S) :
    ((bindFc A ρ).map ψ) S = ∫⁻ z, ((foldedCircle z ρ).map ψ) S ∂A := by
  rw [Measure.map_apply hψ hS, CircleFubini.bind_circle_apply A (hψ hS)]
  exact lintegral_congr fun z => (Measure.map_apply hψ hS).symm

/-- A mixture of good measures is good. -/
theorem goodM_map_bindFc {A : Measure ℂ} [IsProbabilityMeasure A] {ψ : ℂ → ℂ}
    (hψ : Measurable ψ) {ρ α C B : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ z ∂A, GoodM ((foldedCircle z ρ).map ψ) α C B) :
    GoodM ((bindFc A ρ).map ψ) α C B := by
  refine ⟨⟨?_⟩, fun w r hr => ?_, ?_⟩
  · rw [map_bindFc_apply hψ ρ MeasurableSet.univ,
      lintegral_congr_ae (h.mono fun z hz => hz.prob.measure_univ)]
    simp
  · have hcr : 0 ≤ C * r ^ α := mul_nonneg hC (Real.rpow_nonneg hr.le _)
    refine ENNReal.toReal_le_of_le_ofReal hcr ?_
    rw [map_bindFc_apply hψ ρ measurableSet_closedBall]
    calc ∫⁻ z, ((foldedCircle z ρ).map ψ) (closedBall w r) ∂A
        ≤ ∫⁻ _z, ENNReal.ofReal (C * r ^ α) ∂A := by
          refine lintegral_mono_ae (h.mono fun z hz => ?_)
          have := hz.prob
          exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hcr).2 (hz.frost w r hr)
      _ = ENNReal.ofReal (C * r ^ α) := by simp
  · rw [map_bindFc_apply hψ ρ (measurableSet_closedBall_inter_Hbar B).compl,
      lintegral_congr_ae (h.mono fun z hz => hz.supp)]
    simp

/-- **Fubini for circle mixtures** (first argument). -/
theorem kernelCov_map_bindFc_left {A : Measure ℂ} [IsProbabilityMeasure A] {ψ : ℂ → ℂ}
    (hψ : Measurable ψ) {ρ : ℝ} {κ : Measure ℂ} [IsFiniteMeasure κ] {P : ℝ}
    (hb : ∀ᵐ y ∂bindFc A ρ, |neuPot κ (ψ y)| ≤ P) :
    Integrable (fun z => kernelCov neumannH ((foldedCircle z ρ).map ψ) κ) A ∧
      kernelCov neumannH ((bindFc A ρ).map ψ) κ =
        ∫ z, kernelCov neumannH ((foldedCircle z ρ).map ψ) κ ∂A := by
  have e : ∀ μ : Measure ℂ, kernelCov neumannH (μ.map ψ) κ = ∫ y, neuPot κ (ψ y) ∂μ :=
    fun μ => integral_map hψ.aemeasurable (measurable_neuPot κ).aestronglyMeasurable
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) A
  have hi : Integrable (fun y => neuPot κ (ψ y)) (bindFc A ρ) :=
    Integrable.of_bound ((measurable_neuPot κ).comp hψ).aestronglyMeasurable P
      (hb.mono fun y hy => by rwa [Real.norm_eq_abs])
  obtain ⟨i, e2⟩ := CircleFubini.integral_bind_circle A hi
  simp only [e]
  exact ⟨i, e2⟩

/-- **Fubini for circle mixtures**, for the bilinear form of pairs. -/
theorem kernelCov2_map_bindFc_left {A : Measure ℂ} [IsProbabilityMeasure A] {ψ : ℂ → ℂ}
    (hψ : Measurable ψ) {ρ ρ' : ℝ} {q₁ q₂ : Measure ℂ} [IsFiniteMeasure q₁]
    [IsFiniteMeasure q₂] {P : ℝ}
    (h₁ : ∀ᵐ y ∂bindFc A ρ, |neuPot q₁ (ψ y)| ≤ P) (h₂ : ∀ᵐ y ∂bindFc A ρ, |neuPot q₂ (ψ y)| ≤ P)
    (h₁' : ∀ᵐ y ∂bindFc A ρ', |neuPot q₁ (ψ y)| ≤ P)
    (h₂' : ∀ᵐ y ∂bindFc A ρ', |neuPot q₂ (ψ y)| ≤ P) :
    kernelCov2 neumannH ((bindFc A ρ).map ψ, (bindFc A ρ').map ψ) (q₁, q₂) =
      ∫ z, kernelCov2 neumannH ((foldedCircle z ρ).map ψ, (foldedCircle z ρ').map ψ) (q₁, q₂) ∂A := by
  obtain ⟨i1, e1⟩ := kernelCov_map_bindFc_left hψ h₁
  obtain ⟨i2, e2⟩ := kernelCov_map_bindFc_left hψ h₂
  obtain ⟨i3, e3⟩ := kernelCov_map_bindFc_left hψ h₁'
  obtain ⟨i4, e4⟩ := kernelCov_map_bindFc_left hψ h₂'
  simp only [kernelCov2]
  set k₁ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle z ρ).map ψ) q₁
  set k₂ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle z ρ).map ψ) q₂
  set k₃ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle z ρ').map ψ) q₁
  set k₄ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle z ρ').map ψ) q₂
  have a1 : ∫ z, (k₁ z - k₂ z) ∂A = ∫ z, k₁ z ∂A - ∫ z, k₂ z ∂A := integral_sub i1 i2
  have a2 : ∫ z, (k₁ z - k₂ z - k₃ z) ∂A = ∫ z, (k₁ z - k₂ z) ∂A - ∫ z, k₃ z ∂A :=
    integral_sub (i1.sub i2) i3
  have a3 : ∫ z, (k₁ z - k₂ z - k₃ z + k₄ z) ∂A =
      ∫ z, (k₁ z - k₂ z - k₃ z) ∂A + ∫ z, k₄ z ∂A := integral_add ((i1.sub i2).sub i3) i4
  change _ = ∫ z, (k₁ z - k₂ z - k₃ z + k₄ z) ∂A
  rw [a3, a2, a1, e1, e2, e3, e4]

/-! ## The mixture bound -/

/-- **UNIF-RC3-MIX.** If `L_z = ψ_* fc(z, ρ)` and `L'_z = ψ_* fc(z, ρ')` are good for `A`-a.e.
`z` and the energy of `L_z − L'_z` is `≤ K` for `A`-a.e. `z`, then the energy of the mixture
difference `(A ⋆ fc(·,ρ))_* ψ − (A ⋆ fc(·,ρ'))_* ψ` is `≤ K`. -/
theorem abs_kernelCov2_mix_le {A : Measure ℂ} [IsProbabilityMeasure A] {ψ : ℂ → ℂ}
    (hψ : Measurable ψ) {ρ ρ' α C B K : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hL : ∀ᵐ z ∂A, GoodM ((foldedCircle z ρ).map ψ) α C B ∧
      GoodM ((foldedCircle z ρ').map ψ) α C B)
    (hE : ∀ᵐ z ∂A, kernelCov2 neumannH ((foldedCircle z ρ).map ψ, (foldedCircle z ρ').map ψ)
      ((foldedCircle z ρ).map ψ, (foldedCircle z ρ').map ψ) ≤ K) :
    |kernelCov2 neumannH ((bindFc A ρ).map ψ, (bindFc A ρ').map ψ)
      ((bindFc A ρ).map ψ, (bindFc A ρ').map ψ)| ≤ K := by
  set L : ℂ → Measure ℂ := fun z => (foldedCircle z ρ).map ψ with hLdef
  set L' : ℂ → Measure ℂ := fun z => (foldedCircle z ρ').map ψ with hL'def
  set M := (bindFc A ρ).map ψ with hMdef
  set M' := (bindFc A ρ').map ψ with hM'def
  have hM : GoodM M α C B := goodM_map_bindFc hψ hC (hL.mono fun z hz => hz.1)
  have hM' : GoodM M' α C B := goodM_map_bindFc hψ hC (hL.mono fun z hz => hz.2)
  have fub : ∀ q₁ q₂ : Measure ℂ, GoodM q₁ α C B → GoodM q₂ α C B →
      kernelCov2 neumannH (M, M') (q₁, q₂) = ∫ z, kernelCov2 neumannH (L z, L' z) (q₁, q₂) ∂A :=
    fun q₁ q₂ h₁ h₂ => by
      have := h₁.prob; have := h₂.prob
      exact kernelCov2_map_bindFc_left hψ (ae_abs_neuPot_le h₁ hα hC hB hψ hM.supp)
        (ae_abs_neuPot_le h₂ hα hC hB hψ hM.supp) (ae_abs_neuPot_le h₁ hα hC hB hψ hM'.supp)
        (ae_abs_neuPot_le h₂ hα hC hB hψ hM'.supp)
  have hA1 : A.real univ = 1 := probReal_univ
  -- the pair `(L_w, L'_w)` against the mixture
  have hw : ∀ᵐ w ∂A, |kernelCov2 neumannH (M, M') (L w, L' w)| ≤ K := by
    filter_upwards [hL, hE] with w hw hEw
    rw [fub _ _ hw.1 hw.2]
    have h := norm_integral_le_of_norm_le_const (μ := A) (C := K)
      (f := fun z => kernelCov2 neumannH (L z, L' z) (L w, L' w)) ?_
    · rwa [Real.norm_eq_abs, hA1, mul_one] at h
    filter_upwards [hL, hE] with z hz hEz
    rw [Real.norm_eq_abs]
    exact abs_kernelCov2_le_of_energy (hz.1.admissible hα) (hz.2.admissible hα)
      (hw.1.admissible hα) (hw.2.admissible hα) (hz.1.univ_eq hz.2) (hw.1.univ_eq hw.2) hEz hEw
  -- the mixture against itself
  rw [fub _ _ hM hM']
  have h := norm_integral_le_of_norm_le_const (μ := A) (C := K)
    (f := fun w => kernelCov2 neumannH (L w, L' w) (M, M')) ?_
  · rwa [Real.norm_eq_abs, hA1, mul_one] at h
  filter_upwards [hL, hw] with w hwL hwK
  rw [Real.norm_eq_abs, kernelCov2_comm (hwL.1.admissible hα) (hwL.2.admissible hα)
    (hM.admissible hα) (hM'.admissible hα)]
  exact hwK

end RegUnif
end QuantumZipper
