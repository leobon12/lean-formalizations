import QuantumZipper.Proofs.Thm18.ASepModJ
import QuantumZipper.Proofs.Zipper.SWCoreVAPsi
import QuantumZipper.Proofs.Zipper.UnifRC3Mix
import QuantumZipper.Proofs.LQG.WedgeToolkit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 1): the scale parameter in the GENERIC-UC family

`G4SepScale0Stmt` asks the `τ' = 0` conclusion for `rescale (ofFun g + X ω) Q s` for **all**
scales `s > 0` at once. The regularization of the rescaled field reads `X` at the dilated
measures `(μ p ρ).map (s ·)`, so the engine (`GenUC`, Kolmogorov–Čentsov) has to be run with the
scale as an extra parameter. This file proves the energy input of that run, generically:

* `abs_kernelCov2_map_map_leα`: energy modulus for two maps of one `α`-Frostman probability
  measure (copy of `SWCore.swcVA_kernelCov2_map_map_le` with exponent `α ∈ (0,1]`);
* `isFrostman_map_mul_of`: dilations keep the Frostman bound;
* **`genFam_dil`**: a `GenFam` of probability measures with uniform Frostman and support bounds on
  a bounded parameter set stays a `GenFam` after adding the scale `s ∈ [s₀, s₁]` as a last
  parameter, `μ' (p, s) ρ = (μ p ρ).map (s ·)` (dilation invariance of the Neumann kernel
  `WedgeTK.kernelCov2_map_mul`, triangle inequality `RegUnif.kernelCov2_self_triangle`).

Own elementary bookkeeping (the moduli are those of Duplantier–Sheffield, Invent. Math. 185
(2011), Prop. 3.1, through the existing `GenUC` engine).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open TwoPoint

/-- Hölder constant of the Neumann potential of an `α`-Frostman probability measure. -/
def potKα (α C B : ℝ) : ℝ :=
  2 * (1 + 4 * C / α) + 2 * (2 * (C / α) + 2 * (Real.log (B + B + 1) * 1))

theorem potKα_nonneg {α C B : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hB : 0 ≤ B) : 0 ≤ potKα α C B := by
  unfold potKα
  have : 0 ≤ Real.log (B + B + 1) := Real.log_nonneg (by linarith)
  positivity

/-- **Energy modulus in the map, exponent `α`** (copy of `SWCore.swcVA_kernelCov2_map_map_le`). -/
theorem abs_kernelCov2_map_map_leα {σ : Measure ℂ} [IsProbabilityMeasure σ] {f g : ℂ → ℂ}
    (hf : Measurable f) (hg : Measurable g) {α C B ε : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hFf : TwoPoint.IsFrostman (σ.map f) α C) (hFg : TwoPoint.IsFrostman (σ.map g) α C)
    (hfB : ∀ᵐ x ∂σ, ‖f x‖ ≤ B) (hgB : ∀ᵐ x ∂σ, ‖g x‖ ≤ B)
    (hfg : ∀ᵐ x ∂σ, ‖f x - g x‖ ≤ ε) :
    |kernelCov2 neumannH (σ.map f, σ.map g) (σ.map f, σ.map g)| ≤
      2 * (potKα α C B * ε ^ (α / 2)) := by
  have : IsProbabilityMeasure (σ.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (σ.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hsuppf : ∀ᵐ y ∂σ.map f, ‖y‖ ≤ B :=
    (ae_map_iff hf.aemeasurable (measurableSet_le measurable_norm measurable_const)).2 hfB
  have hsuppg : ∀ᵐ y ∂σ.map g, ‖y‖ ≤ B :=
    (ae_map_iff hg.aemeasurable (measurableSet_le measurable_norm measurable_const)).2 hgB
  have hmass : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], κ.real univ = 1 := fun κ _ => by
    simp
  have hK0 : 0 ≤ potKα α C B := potKα_nonneg hα hC hB
  have hpot : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], TwoPoint.IsFrostman κ α C →
      (∀ᵐ y ∂κ, ‖y‖ ≤ B) →
      (∀ x : ℂ, ‖x‖ ≤ B → |neuPot κ x| ≤ 2 * (C / α) + 2 * (Real.log (B + B + 1) * 1)) ∧
      ∀ x x' : ℂ, ‖x‖ ≤ B → ‖x'‖ ≤ B →
        |neuPot κ x - neuPot κ x'| ≤ potKα α C B * ‖x - x'‖ ^ (α / 2) := by
    intro κ _ hF hsupp
    refine ⟨fun x hx => ?_, fun x x' hx hx' => ?_⟩
    · have := abs_neuPot_le hF hα hC hB hsupp hx
      rwa [hmass κ] at this
    · have := abs_neuPot_sub_le hF hα hα1 hC hB hsupp hx hx'
      rw [hmass κ] at this
      simpa [potKα] using this
  have hkc : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ] (h : ℂ → ℂ), Measurable h →
      kernelCov neumannH (σ.map h) κ = ∫ x, neuPot κ (h x) ∂σ := by
    intro κ _ h hh
    show ∫ y, neuPot κ y ∂σ.map h = _
    rw [integral_map hh.aemeasurable (measurable_neuPot κ).aestronglyMeasurable]
  have hint : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], TwoPoint.IsFrostman κ α C →
      (∀ᵐ y ∂κ, ‖y‖ ≤ B) → ∀ h : ℂ → ℂ, Measurable h → (∀ᵐ x ∂σ, ‖h x‖ ≤ B) →
      Integrable (fun x => neuPot κ (h x)) σ := by
    intro κ _ hF hsupp h hh hhB
    refine Integrable.of_bound ((measurable_neuPot κ).comp hh).aestronglyMeasurable
      (2 * (C / α) + 2 * (Real.log (B + B + 1) * 1)) ?_
    filter_upwards [hhB] with x hx
    rw [Real.norm_eq_abs]
    exact (hpot κ hF hsupp).1 _ hx
  have hdiff : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], TwoPoint.IsFrostman κ α C →
      (∀ᵐ y ∂κ, ‖y‖ ≤ B) →
      |∫ x, neuPot κ (f x) ∂σ - ∫ x, neuPot κ (g x) ∂σ| ≤ potKα α C B * ε ^ (α / 2) := by
    intro κ _ hF hsupp
    rw [← integral_sub (hint κ hF hsupp f hf hfB) (hint κ hF hsupp g hg hgB),
      ← Real.norm_eq_abs]
    calc ‖∫ x, (neuPot κ (f x) - neuPot κ (g x)) ∂σ‖
        ≤ potKα α C B * ε ^ (α / 2) * σ.real univ :=
          norm_integral_le_of_norm_le_const (by
            filter_upwards [hfB, hgB, hfg] with x h1 h2 h3
            rw [Real.norm_eq_abs]
            refine ((hpot κ hF hsupp).2 _ _ h1 h2).trans ?_
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg _) h3 (by linarith)) hK0)
      _ = potKα α C B * ε ^ (α / 2) := by simp
  have e : kernelCov2 neumannH (σ.map f, σ.map g) (σ.map f, σ.map g) =
      (∫ x, neuPot (σ.map f) (f x) ∂σ - ∫ x, neuPot (σ.map f) (g x) ∂σ) -
        (∫ x, neuPot (σ.map g) (f x) ∂σ - ∫ x, neuPot (σ.map g) (g x) ∂σ) := by
    simp only [kernelCov2]
    rw [hkc (σ.map f) f hf, hkc (σ.map g) f hf, hkc (σ.map f) g hg, hkc (σ.map g) g hg]
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have h1 := hdiff (σ.map f) hFf hsuppf
  have h2 := hdiff (σ.map g) hFg hsuppg
  linarith

/-- **Dilations keep the Frostman bound.** -/
theorem isFrostman_map_mul_of {σ : Measure ℂ} {α C s₀ s : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hF : TwoPoint.IsFrostman σ α C) :
    TwoPoint.IsFrostman (σ.map fun z => (s : ℂ) * z) α (C * s₀⁻¹ ^ α) := by
  intro w r hr
  have hsp : 0 < s := hs₀.trans_le hs
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  rw [Measure.map_apply (measurable_const_mul _) measurableSet_closedBall]
  have e : (fun z => (s : ℂ) * z) ⁻¹' closedBall w r = closedBall (w / s) (r / s) := by
    ext z
    simp only [mem_preimage, mem_closedBall, dist_eq_norm]
    have : (s : ℂ) * z - w = (s : ℂ) * (z - w / s) := by field_simp
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsp.le, le_div_iff₀ hsp, mul_comm]
  rw [e]
  refine (hF _ _ (div_pos hr hsp)).trans ?_
  rw [div_eq_mul_inv, Real.mul_rpow hr.le (inv_nonneg.2 hsp.le), mul_comm (r ^ α), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (by positivity)
  exact Real.rpow_le_rpow (inv_nonneg.2 hsp.le) ((inv_le_inv₀ hsp hs₀).2 hs) hα.le

/-- Lowering a Hölder exponent on a bounded range. -/
theorem rpow_le_split {t x E e c' : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) (hxE : x ≤ E) (hc' : 0 < c')
    (hce : c' ≤ e) : t ^ e ≤ E ^ (e - c') * x ^ c' := by
  have hx : 0 ≤ x := ht.trans htx
  have he : 0 < e := hc'.trans_le hce
  calc t ^ e ≤ x ^ e := Real.rpow_le_rpow ht htx he.le
    _ = x ^ c' * x ^ (e - c') := by
        rw [← Real.rpow_add' hx (by linarith)]; congr 1; ring
    _ ≤ x ^ c' * E ^ (e - c') :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxE (by linarith)) (by positivity)
    _ = E ^ (e - c') * x ^ c' := mul_comm _ _

/-- The dilated family: the last coordinate of the parameter is the scale. -/
def dilFam {n : ℕ} (μ : (Fin n → ℝ) → ℝ → Measure ℂ) : (Fin (n + 1) → ℝ) → ℝ → Measure ℂ :=
  fun q ρ => (μ (Fin.init q) ρ).map fun z => ((q (Fin.last n) : ℝ) : ℂ) * z

/-- The dilated parameter set. -/
def dilSet {n : ℕ} (S : Set (Fin n → ℝ)) (s₀ s₁ : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {q | Fin.init q ∈ S ∧ q (Fin.last n) ∈ Icc s₀ s₁}

theorem dist_init_le {n : ℕ} (q q' : Fin (n + 1) → ℝ) : dist (Fin.init q) (Fin.init q') ≤ dist q q' :=
  (dist_pi_le_iff dist_nonneg).2 fun j => dist_le_pi_dist q q' j.castSucc

/-- **`GenFam` with the scale as an extra parameter.** -/
theorem genFam_dil {n : ℕ} {S : Set (Fin n → ℝ)} {μ : (Fin n → ℝ) → ℝ → Measure ℂ} {K c : ℝ}
    (hF : GenUC.GenFam S μ 1 K c) {s₀ s₁ α C B D : ℝ} (hs₀ : 0 < s₀) (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hFr : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, TwoPoint.IsFrostman (μ p ρ) α C)
    (hsupp : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ᵐ z ∂μ p ρ, ‖z‖ ≤ B)
    (hdiam : ∀ p ∈ S, ∀ p' ∈ S, dist p p' ≤ D) :
    ∃ K' c' : ℝ, GenUC.GenFam (dilSet S s₀ s₁) (dilFam μ) 1 K' c' := by
  set c' : ℝ := min c (α / 2) with hc'def
  have hc0 : 0 < c := hF.c_pos
  have hc' : 0 < c' := lt_min hc0 (by linarith)
  set E : ℝ := D + |s₁ - s₀| + 1 with hEdef
  have hE0 : 0 ≤ E := by positivity
  set P : ℝ := potKα α (C * s₀⁻¹ ^ α) (|s₁| * B) with hPdef
  set K' : ℝ := 2 * K * E ^ (c - c') + 4 * P * B ^ (α / 2) * E ^ (α / 2 - c') with hK'def
  have hK0 := hF.K_nonneg
  have hC' : 0 ≤ C * s₀⁻¹ ^ α := by positivity
  refine ⟨K', c', ?_⟩
  have hspos : ∀ q ∈ dilSet S s₀ s₁, 0 < q (Fin.last n) := fun q hq => hs₀.trans_le hq.2.1
  have hs₁ : ∀ q ∈ dilSet S s₀ s₁, 0 ≤ s₁ := fun q hq => (hspos q hq).le.trans hq.2.2
  have hmass1 : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, IsProbabilityMeasure (μ p ρ) := fun p hp ρ hρ =>
    ⟨hF.mass p hp ρ hρ⟩
  have hmap_univ : ∀ (ν : Measure ℂ) (b : ℝ), (ν.map fun z => (b : ℂ) * z) univ = ν univ :=
    fun ν b => by rw [Measure.map_apply (measurable_const_mul _) MeasurableSet.univ, preimage_univ]
  refine ⟨fun q hq ρ hρ => ?_, fun q hq ρ hρ => ?_, ?_, hc', ?_⟩
  · exact WedgeTK.isAdmissibleH_map_mul (hspos q hq) (hF.adm _ hq.1 ρ hρ)
  · show (dilFam μ q ρ) univ = 1
    unfold dilFam; rw [hmap_univ]; exact hF.mass _ hq.1 ρ hρ
  · have := potKα_nonneg (α := α) hα hC' (mul_nonneg (abs_nonneg s₁) hB)
    positivity
  intro q hq q' hq' ρ hρ ρ' hρ'
  set p := Fin.init q
  set p' := Fin.init q'
  set s := q (Fin.last n) with hsdef
  set s' := q' (Fin.last n) with hs'def
  have hs : 0 < s := hspos q hq
  have hs' : 0 < s' := hspos q' hq'
  set A := μ p ρ
  set A' := μ p' ρ'
  have : IsProbabilityMeasure A' := hmass1 p' hq'.1 ρ' hρ'
  have hA := hF.adm p hq.1 ρ hρ
  have hA' := hF.adm p' hq'.1 ρ' hρ'
  have hAA' : A univ = A' univ := (hF.mass p hq.1 ρ hρ).trans (hF.mass p' hq'.1 ρ' hρ').symm
  have ha := WedgeTK.isAdmissibleH_map_mul hs hA
  have hb := WedgeTK.isAdmissibleH_map_mul hs hA'
  have hc := WedgeTK.isAdmissibleH_map_mul hs' hA'
  have hab : (A.map fun z => (s : ℂ) * z) univ = (A'.map fun z => (s : ℂ) * z) univ := by
    rw [hmap_univ, hmap_univ, hAA']
  have hbc : (A'.map fun z => (s : ℂ) * z) univ = (A'.map fun z => (s' : ℂ) * z) univ := by
    rw [hmap_univ, hmap_univ]
  show |kernelCov2 neumannH (A.map fun z => (s : ℂ) * z, A'.map fun z => (s' : ℂ) * z)
      (A.map fun z => (s : ℂ) * z, A'.map fun z => (s' : ℂ) * z)| ≤ K' * (dist q q' + |ρ - ρ'|) ^ c'
  have htri := RegUnif.kernelCov2_self_triangle ha hb hc hab hbc
  have hnn : 0 ≤ kernelCov2 neumannH (A.map fun z => (s : ℂ) * z, A'.map fun z => (s' : ℂ) * z)
      (A.map fun z => (s : ℂ) * z, A'.map fun z => (s' : ℂ) * z) := by
    rw [RegUnif.kernelCov2_self_eq_norm_sq ha hc (hab.trans hbc)]; positivity
  -- first piece: dilation invariance
  have e1 : kernelCov2 neumannH (A.map fun z => (s : ℂ) * z, A'.map fun z => (s : ℂ) * z)
      (A.map fun z => (s : ℂ) * z, A'.map fun z => (s : ℂ) * z) =
      kernelCov2 neumannH (A, A') (A, A') :=
    WedgeTK.kernelCov2_map_mul hs ⟨(A, A'), hA, hA', hAA'⟩ ⟨(A, A'), hA, hA', hAA'⟩
  have h1 : kernelCov2 neumannH (A.map fun z => (s : ℂ) * z, A'.map fun z => (s : ℂ) * z)
      (A.map fun z => (s : ℂ) * z, A'.map fun z => (s : ℂ) * z) ≤
      K * (dist p p' + |ρ - ρ'|) ^ c := by
    rw [e1]; exact (le_abs_self _).trans (hF.energy p hq.1 p' hq'.1 ρ hρ ρ' hρ')
  -- second piece: nearby maps
  have hsB : ∀ t : ℝ, 0 < t → t ≤ s₁ → ∀ᵐ x ∂A', ‖(t : ℂ) * x‖ ≤ |s₁| * B := fun t ht hts => by
    filter_upwards [hsupp p' hq'.1 ρ' hρ'] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact mul_le_mul (hts.trans (le_abs_self _)) hx (norm_nonneg _) (abs_nonneg _)
  have h2 := abs_kernelCov2_map_map_leα (σ := A') (measurable_const_mul (s : ℂ))
    (measurable_const_mul (s' : ℂ)) (ε := |s - s'| * B) hα hα1 hC'
    (mul_nonneg (abs_nonneg s₁) hB)
    (isFrostman_map_mul_of hα hC hs₀ hq.2.1 (hFr p' hq'.1 ρ' hρ'))
    (isFrostman_map_mul_of hα hC hs₀ hq'.2.1 (hFr p' hq'.1 ρ' hρ'))
    (hsB s hs hq.2.2) (hsB s' hs' hq'.2.2) (by
      filter_upwards [hsupp p' hq'.1 ρ' hρ'] with x hx
      rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg _))
  -- exponents
  have hdq : dist q q' ≤ D + |s₁ - s₀| := by
    refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
    induction i using Fin.lastCases with
    | last =>
      have hq2 : s ∈ Icc s₀ s₁ := hq.2
      have hq2' : s' ∈ Icc s₀ s₁ := hq'.2
      have h3 : |s - s'| ≤ s₁ - s₀ :=
        abs_sub_le_iff.2 ⟨by linarith [hq2.1, hq2.2, hq2'.1, hq2'.2], by linarith [hq2.1, hq2.2, hq2'.1, hq2'.2]⟩
      show dist s s' ≤ _
      rw [Real.dist_eq]
      linarith [le_abs_self (s₁ - s₀)]
    | cast j =>
      have := (dist_le_pi_dist p p' j).trans (hdiam p hq.1 p' hq'.1)
      have e : dist (p j) (p' j) = dist (q j.castSucc) (q' j.castSucc) := rfl
      rw [e] at this
      linarith [abs_nonneg (s₁ - s₀)]
  have hρρ : |ρ - ρ'| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2, hρ'.1, hρ'.2]
  set x := dist q q' + |ρ - ρ'| with hxdef
  have hxE : x ≤ E := by rw [hxdef, hEdef]; linarith
  have hy : dist p p' + |ρ - ρ'| ≤ x := by rw [hxdef]; linarith [dist_init_le q q']
  have hss : |s - s'| ≤ x := by
    have := dist_le_pi_dist q q' (Fin.last n)
    rw [Real.dist_eq] at this
    rw [hxdef]; linarith [abs_nonneg (ρ - ρ')]
  have i1 := rpow_le_split (by positivity) hy hxE hc' (min_le_left _ _)
  have i2 := rpow_le_split (abs_nonneg _) hss hxE hc' (min_le_right _ _)
  have eB : (|s - s'| * B) ^ (α / 2) = |s - s'| ^ (α / 2) * B ^ (α / 2) :=
    Real.mul_rpow (abs_nonneg _) hB
  rw [eB] at h2
  have hP0 : 0 ≤ P := potKα_nonneg hα hC' (mul_nonneg (abs_nonneg s₁) hB)
  have hBa : 0 ≤ B ^ (α / 2) := by positivity
  rw [abs_of_nonneg hnn]
  have h2' := (le_abs_self _).trans h2
  calc _ ≤ 2 * (K * (dist p p' + |ρ - ρ'|) ^ c) + 2 * (2 * (P * (|s - s'| ^ (α / 2) *
          B ^ (α / 2)))) := by linarith
    _ ≤ 2 * (K * (E ^ (c - c') * x ^ c')) + 2 * (2 * (P * ((E ^ (α / 2 - c') * x ^ c') *
          B ^ (α / 2)))) := by gcongr
    _ = K' * x ^ c' := by rw [hK'def]; ring

end ASep
end QuantumZipper
