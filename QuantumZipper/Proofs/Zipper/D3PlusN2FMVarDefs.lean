import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeVar
import QuantumZipper.Proofs.Zipper.RegContMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, definitions: the first-mode measures and the two remaining nodes

Task N2Z-FMVAR. The real (`k = 0`) and imaginary (`k = 1`) parts of the first circle mode
`∫_0^{2π} g(w + τ e^{iθ}, s) e^{iθ} dθ` equal `∫_0^{2π} g(w + τ u_k e^{iφ}, s) cos φ dφ` with
`u_0 = 1`, `u_1 = i` (shift `θ = φ + π/2`), and splitting `cos = cos⁺ − cos⁻` with
`cos⁻(φ) = cos⁺(φ + π)` this is the difference of the pairings of `g(·, s)` with the two
equal-mass arc measures `fmArc w (± τ u_k)` (`fmBase = cos⁺ φ dφ` on `(0, 2π]` pushed by
`φ ↦ w ± τ u_k e^{iφ}`). Smoothed by folded circles of radius `s` they are `fmMeas`.

Nodes stated here:

* `FMReprStmt` (part F): a.s. the first-mode part of a regular version equals
  `X(fmMeas w (τ u_k) s) − X(fmMeas w (−τ u_k) s)` (stochastic Fubini, `WedgeTK.ae_integral_G_eq`);
* `FMAdmStmt`: the first-mode measures are admissible;
* `N2ZFMEnergyStmt` (part E): the Neumann energies of the first-mode pairs are `≤ c` and those of
  their increments are `≤ c (‖Δw‖ + |Δτ| + |Δs|) / τ` (same scale `τ ≍ τ'`, `s ≤ τ`).

`fmPos`/`fmNeg`: the pairs in the rescaled, clamped block coordinates `q ∈ ℝ⁴` used by the
Kolmogorov step (part K).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace D3Plus

/-- `cos⁺ φ dφ` on `(0, 2π]`. -/
def fmBase : Measure ℝ :=
  (volume.restrict (Ioc 0 (2 * π))).withDensity fun φ => ENNReal.ofReal (Real.cos φ)

instance isFiniteMeasure_fmBase : IsFiniteMeasure fmBase := by
  unfold fmBase
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact (Real.continuous_cos.integrableOn_Icc (a := 0) (b := 2 * π)).mono_set
    Ioc_subset_Icc_self |>.hasFiniteIntegral

/-- The arc measure `fmBase` pushed by `φ ↦ w + v e^{iφ}`. -/
def fmArc (w v : ℂ) : Measure ℂ :=
  fmBase.map fun φ : ℝ => w + v * Complex.exp ((φ : ℂ) * Complex.I)

/-- The arc measure smoothed by folded circles of radius `s`. -/
def fmMeas (w v : ℂ) (s : ℝ) : Measure ℂ := (fmArc w v).bind fun z => foldedCircle z s

/-- Direction `u_k`: `1` for the real part, `i` for the imaginary part. -/
def fmDir (k : Fin 2) : ℂ := if k = 0 then 1 else Complex.I

theorem norm_fmDir (k : Fin 2) : ‖fmDir k‖ = 1 := by
  unfold fmDir; split_ifs <;> simp

theorem measurable_fmArcMap (w v : ℂ) :
    Measurable fun φ : ℝ => w + v * Complex.exp ((φ : ℂ) * Complex.I) := by fun_prop

instance isFiniteMeasure_fmArc (w v : ℂ) : IsFiniteMeasure (fmArc w v) := by
  unfold fmArc; infer_instance

theorem fmArc_univ (w v : ℂ) : fmArc w v univ = fmBase univ := by
  unfold fmArc
  rw [Measure.map_apply (measurable_fmArcMap w v) MeasurableSet.univ, preimage_univ]

theorem fmMeas_univ (w v : ℂ) (s : ℝ) : fmMeas w v s univ = fmBase univ := by
  unfold fmMeas
  rw [CircleFubini.bind_circle_univ, fmArc_univ]

/-! ## Rescaled clamped block coordinates -/

/-- Clamp to `[a, b]`. -/
def fmCl (a b x : ℝ) : ℝ := max a (min x b)

/-- Clamped rescaled radius `∈ [1/2, 1]`. -/
def fmTq (q : Fin 4 → ℝ) : ℝ := fmCl (1 / 2) 1 (q 2)

/-- Centre of the clamped parameters. -/
def fmCq (m n : ℕ) (q : Fin 4 → ℝ) : ℂ :=
  ⟨(2 : ℝ)⁻¹ ^ n * fmCl (-(((m : ℝ) + 1) * 2 ^ n)) (((m : ℝ) + 1) * 2 ^ n) (q 0),
    (2 : ℝ)⁻¹ ^ n * fmCl (2 ^ n / ((m : ℝ) + 1)) (((m : ℝ) + 1) * 2 ^ n) (q 1)⟩

/-- Radius of the clamped parameters. -/
def fmRq (n : ℕ) (q : Fin 4 → ℝ) : ℝ := (2 : ℝ)⁻¹ ^ n * fmTq q

/-- Smoothing radius of the clamped parameters (`∈ [0, radius]`). -/
def fmSq (n : ℕ) (q : Fin 4 → ℝ) : ℝ := (2 : ℝ)⁻¹ ^ n * fmCl 0 (fmTq q) (q 3)

/-- Positive first-mode measure at the rescaled parameter `q`. -/
def fmPos (m n : ℕ) (k : Fin 2) (q : Fin 4 → ℝ) : Measure ℂ :=
  fmMeas (fmCq m n q) ((fmRq n q : ℂ) * fmDir k) (fmSq n q)

/-- Negative first-mode measure at the rescaled parameter `q`. -/
def fmNeg (m n : ℕ) (k : Fin 2) (q : Fin 4 → ℝ) : Measure ℂ :=
  fmMeas (fmCq m n q) (-((fmRq n q : ℂ) * fmDir k)) (fmSq n q)

/-! ## The nodes -/

/-- **Node FM-REPR (part F).** For a regular version, almost surely the `k`-th part of the first
mode is the pair `X(fmMeas w (τ u_k) s) − X(fmMeas w (−τ u_k) s)`. -/
def FMReprStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ G : Ω → ℂ × ℝ → ℝ,
    WedgeTK.IsRegVersion X P G → ∀ (k : Fin 2) (w : ℂ) (τ s : ℝ), 0 < τ → τ ≤ w.im → 0 < s →
      ∀ᵐ ω ∂P, fmPart k (fmInt (G ω) w τ s) =
        X ω (fmMeas w ((τ : ℂ) * fmDir k) s) - X ω (fmMeas w (-((τ : ℂ) * fmDir k)) s)

/-- **Node FM-ADM.** First-mode measures inside `H` are admissible (`v ≠ 0`: for `v = s = 0`
the measure is a point mass). -/
def FMAdmStmt : Prop :=
  ∀ (w v : ℂ) (s : ℝ), 0 ≤ s → 0 < ‖v‖ → ‖v‖ + s < w.im → IsAdmissibleH (fmMeas w v s)

/-- **Node FM-ENERGY (part E).** Neumann energies of the first-mode pairs: `≤ c`, and for
increments at comparable radii `≤ c (‖w − w'‖ + |τ − τ'| + |s − s'|) / τ`. -/
def N2ZFMEnergyStmt : Prop :=
  ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∀ u : ℂ, ‖u‖ = 1 → ∀ w w' : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → ‖w'‖ ≤ 2 * ((m : ℝ) + 1) →
      1 / ((m : ℝ) + 1) ≤ w.im → 1 / ((m : ℝ) + 1) ≤ w'.im →
      ∀ τ τ' : ℝ, 0 < τ → τ ≤ τ₀ → τ ≤ 2 * τ' → τ' ≤ 2 * τ →
      ∀ s s' : ℝ, 0 ≤ s → s ≤ τ → 0 ≤ s' → s' ≤ τ' →
        kernelCov2 neumannH (fmMeas w ((τ : ℂ) * u) s, fmMeas w (-((τ : ℂ) * u)) s)
            (fmMeas w ((τ : ℂ) * u) s, fmMeas w (-((τ : ℂ) * u)) s) ≤ c ∧
        kernelCov2 neumannH
            (fmMeas w ((τ : ℂ) * u) s + fmMeas w' (-((τ' : ℂ) * u)) s',
              fmMeas w (-((τ : ℂ) * u)) s + fmMeas w' ((τ' : ℂ) * u) s')
            (fmMeas w ((τ : ℂ) * u) s + fmMeas w' (-((τ' : ℂ) * u)) s',
              fmMeas w (-((τ : ℂ) * u)) s + fmMeas w' ((τ' : ℂ) * u) s') ≤
          c * (‖w - w'‖ + |τ - τ'| + |s - s'|) / τ

end D3Plus
end QuantumZipper
