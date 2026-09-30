import QuantumZipper.Proofs.Zipper.Cor15MeasVerMain
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.GFF.K3.MixedM5Pot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-MARKOV (2): reconstruction of a free field from its dyadic circle values

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5; decision D35.
The remaining input of the unzip version `Cor15UnzipVersionStmt` (hence of the Markov core
`Cor15MarkovStmt`) is the reconstruction statement `FreeCircleReconStmt` (`Cor15UnzipVerMain`):
a fixed measurable functional of the dyadic folded-circle values of a free field modulo constants
recovers, a.s., its value at every admissible measure.

**`freeCircleRecon_of_energy`** proves the body of `FreeCircleReconStmt` from one deterministic
potential-theory input, **`BindFcEnergyTendstoStmt`**: for every admissible `μ` (finite, compact
support in `ℍ̄`, bounded logarithmic potential), the Neumann energy of `μ_k − μ` tends to `0`,
where `μ_k = ∫ foldedCircle(w, 2^{-k}) dμ(w)` is the circle-average smoothing of `μ`.
(True: the folded-circle averages of `−log|x − ·|` are dominated by the logarithmic potential,
which is `μ ⊗ μ`-integrable, and converge off the diagonal, which `μ ⊗ μ` does not charge since
`μ` has no atoms; dominated convergence. This is the circle-average approximation of
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), §3.1 and
Prop. 3.1 (`literature/0808.1560.pdf`); for Frostman measures the repository proves it with a
rate, `FrostmanReg.integral_sq_frostman_le`.)

Construction (own bookkeeping, following `FrostmanReg.ae_tendsto_bind_frostman` and
`Regularization.ae_evalReg_eq_of_good`): at a dyadic folded circle `R c` reads the coordinate
(`E1.fromC`); at any other admissible `μ` it is the limit of `∫ avgReg (fromC c) n_j dμ` along
a deterministic subsequence `n_j = reconIdx μ j` on which the energy is `≤ 4^{-j}`. For a free
field, `∫ avgReg X k dμ = X μ_k` a.s. (`ae_integral_avgReg_eq`), `E (X μ_{n_j} − X μ)² ≤ 4^{-j}`,
and Borel–Cantelli gives a.s. convergence to `X μ`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Cor15Group

open CoordsFull

/-- The folded-circle smoothing of `μ` at radius `2^{-k}`. -/
abbrev fcSmooth (μ : Measure ℂ) (k : ℕ) : Measure ℂ :=
  μ.bind fun w => foldedCircle w (radius k)

/-- The Neumann energy of `μ_k − μ`. -/
def fcSmoothEnergy (μ : Measure ℂ) (k : ℕ) : ℝ :=
  kernelCov2 neumannH (fcSmooth μ k, μ) (fcSmooth μ k, μ)

/-- **Input (potential theory).** For every admissible `μ`, the Neumann energy of the
circle-average smoothing error `μ_k − μ` tends to `0`. -/
def BindFcEnergyTendstoStmt : Prop :=
  ∀ μ : Measure ℂ, IsAdmissibleH μ → Tendsto (fcSmoothEnergy μ) atTop (𝓝 0)

open Classical in
/-- A deterministic index at which the smoothing energy is at most `4^{-j}`. -/
def reconIdx (μ : Measure ℂ) (j : ℕ) : ℕ :=
  if h : ∃ N, ∀ k ≥ N, fcSmoothEnergy μ k ≤ (4⁻¹ : ℝ) ^ j then Nat.find h else 0

theorem reconIdx_spec {μ : Measure ℂ} (hμ : Tendsto (fcSmoothEnergy μ) atTop (𝓝 0)) (j : ℕ) :
    fcSmoothEnergy μ (reconIdx μ j) ≤ (4⁻¹ : ℝ) ^ j := by
  classical
  have h : ∃ N, ∀ k ≥ N, fcSmoothEnergy μ k ≤ (4⁻¹ : ℝ) ^ j :=
    eventually_atTop.1 (hμ.eventually (Iic_mem_nhds (pow_pos (by norm_num) j)))
  unfold reconIdx
  rw [dif_pos h]
  exact Nat.find_spec h _ le_rfl

open Classical in
/-- The reconstruction functional. -/
def reconR (c : ℕ → ℝ) (μ : Measure ℂ) : ℝ :=
  if ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ then E1.fromC c μ
  else if IsAdmissibleH μ then
    limUnder atTop fun j => ∫ z, avgReg (E1.fromC c) (reconIdx μ j) z ∂μ
  else 0

theorem measurable_fromC_apply' (μ : Measure ℂ) : Measurable fun c : ℕ → ℝ => E1.fromC c μ := by
  classical
  unfold E1.fromC
  by_cases h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · simp only [h, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]
    exact measurable_const

theorem measurable_fromC' : Measurable E1.fromC :=
  measurable_pi_iff.2 measurable_fromC_apply'

theorem measurable_reconR (μ : Measure ℂ) : Measurable fun c => reconR c μ := by
  classical
  unfold reconR
  by_cases h1 : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · simp only [h1, ↓reduceIte]
    exact measurable_fromC_apply' μ
  · by_cases h2 : IsAdmissibleH μ
    · simp only [h1, h2, ↓reduceIte]
      haveI := h2.1
      have hf : ∀ j : ℕ, StronglyMeasurable fun c : ℕ → ℝ =>
          ∫ z, avgReg (E1.fromC c) (reconIdx μ j) z ∂μ := fun j =>
        ((StronglyMeasurable.integral_prod_right'
          (measurable_avgReg (reconIdx μ j)).stronglyMeasurable).measurable.comp
            measurable_fromC').stronglyMeasurable
      exact (StronglyMeasurable.limUnder hf).measurable
    · simp only [h1, h2, ↓reduceIte]
      exact measurable_const

/-- At a dyadic folded circle, `reconR` reads the coordinate. -/
theorem reconR_coordsFull_of_fc (x : FieldSample) {μ : Measure ℂ}
    (h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ) :
    reconR (coordsFull x) μ = x μ := by
  classical
  obtain ⟨i, rfl⟩ := h
  unfold reconR
  rw [if_pos ⟨i, rfl⟩]
  exact congrFun (E1.coordsFull_fromC x) i

/-- **`FreeCircleReconStmt` (body) from the energy input.** -/
theorem freeCircleRecon_of_energy (hE : BindFcEnergyTendstoStmt) :
    ∃ R : (ℕ → ℝ) → FieldSample, (∀ μ : Measure ℂ, Measurable fun c => R c μ) ∧
      (∀ (x : FieldSample) (i : ℕ), R (coordsFull x) (foldedCircle (fullIndex i).1
        (fullIndex i).2) = x (foldedCircle (fullIndex i).1 (fullIndex i).2)) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ μ : Measure ℂ, IsAdmissibleH μ →
        (fun ω => R (coordsFull (X ω)) μ) =ᵐ[P] fun ω => X ω μ := by
  classical
  refine ⟨reconR, measurable_reconR, fun x i => reconR_coordsFull_of_fc x ⟨i, rfl⟩, ?_⟩
  intro Ω _ P _ X hX μ hμ
  by_cases h1 : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · exact ae_of_all _ fun ω => reconR_coordsFull_of_fc (X ω) h1
  haveI := hμ.1
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.2.1
  have hA : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (X ω) k z ∂μ = X ω (fcSmooth μ k) :=
    ae_all_iff.2 fun k => Regularization.ae_integral_avgReg_eq hX k μ hK hKH hμK
  set sd : ℕ → Ω → ℝ := fun j ω => X ω (fcSmooth μ (reconIdx μ j)) - X ω μ with hsd
  have hkA : ∀ k, IsAdmissibleH (fcSmooth μ k) := fun k => K3.isAdmissibleH_bind hμ (radius_pos k)
  have mA : ∀ k, (fcSmooth μ k) Set.univ = μ Set.univ := fun k => SmoothConv.bind_fc_univ μ _
  have hmeas : ∀ j, Measurable (sd j) := fun j =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hint : ∀ j, Integrable (fun ω => sd j ω ^ 2) P := fun j =>
    (SmoothConv.memLp_pair_sc hX (hkA _) hμ (mA _)).integrable_sq
  have hb : ∀ j, ∫ ω, sd j ω ^ 2 ∂P ≤ 1 * (4⁻¹ : ℝ) ^ j := by
    intro j
    set k := reconIdx μ j
    have c1 := hX.covariance_eq (fcSmooth μ k, μ) (fcSmooth μ k, μ) (hkA k) hμ (mA k)
      (hkA k) hμ (mA k)
    dsimp only at c1
    have hm := hX.centered _ _ (hkA k) hμ (mA k)
    have key : ∫ ω, sd j ω ^ 2 ∂P =
        cov[fun ω => X ω (fcSmooth μ k) - X ω μ, fun ω => X ω (fcSmooth μ k) - X ω μ; P] := by
      unfold covariance
      rw [hm]
      simp only [hsd, sub_zero, sq]
      rfl
    rw [key, c1, one_mul]
    exact reconIdx_spec (hE μ hμ) j
  filter_upwards [hA, FrostmanReg.ae_tendsto_zero_of_sq_geom_frostman hmeas hint zero_le_one
    (by norm_num) (by norm_num) hb] with ω hA hω
  have e : (fun j => ∫ z, avgReg (E1.fromC (coordsFull (X ω))) (reconIdx μ j) z ∂μ) =
      fun j => sd j ω + X ω μ := by
    funext j
    rw [avgReg_congr_full (E1.coordsFull_fromC (X ω)), hA, hsd, sub_add_cancel]
  have hlim : Tendsto (fun j => sd j ω + X ω μ) atTop (𝓝 (X ω μ)) := by
    simpa only [zero_add] using hω.add_const (X ω μ)
  show reconR (coordsFull (X ω)) μ = X ω μ
  unfold reconR
  rw [if_neg h1, if_pos hμ, e]
  exact hlim.limUnder_eq

end Cor15Group
end QuantumZipper
