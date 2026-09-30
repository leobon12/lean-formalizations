import QuantumZipper.Proofs.LQG.WedgeCanonical2
import QuantumZipper.Proofs.LQG.GoodSample

/-!
# M4-A5-WEDGE (TASKS R23): probabilistic consequences of the wedge density rule

Ingredient lemmas for R23 (a) that sit on top of the local density rule
(`WedgeCan.qAreaMeasure_wedgeField_eq`):

* `dyadicRoundC_eq_grid`, `ae_raw_dyadic`: the dyadic centres `dyadicRoundC n z` form a countable
  grid, so the raw-circle hypothesis `hraw` of the density rule holds a.s. for a regular version
  `G` of a free field (`WedgeTK.IsRegVersion.raw`);
* `withDensity_eq_zero_of_measure_eq_zero`, `qAreaMeasure_wedgeField_sphere_eq_zero`: no circle
  atoms for the wedge field, from the density rule and the free field's `AreaCircles.ae_sphere_null`
  (a measure with density against `μ_x` vanishes on `μ_x`-null sets).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeCan

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
  {G : Ω → ℂ × ℝ → ℝ}

/-! ## 1. The dyadic grid and the raw-circle hypothesis -/

/-- The dyadic grid point with integer coordinates `(a, b)` at scale `n`. -/
def gridPt (p : ℕ × ℤ × ℤ) : ℂ :=
  Complex.ofReal ((p.2.1 : ℝ) / (2 : ℝ) ^ p.1) +
    Complex.ofReal ((p.2.2 : ℝ) / (2 : ℝ) ^ p.1) * Complex.I

/-- Every dyadic rounding `dyadicRoundC n z` is the grid point with integer coordinates
`(⌊2^n z.re⌋, ⌊2^n z.im⌋)`; the dyadic grid is therefore countable (it is the range of `gridPt`). -/
theorem dyadicRoundC_eq_grid (n : ℕ) (z : ℂ) :
    dyadicRoundC n z = gridPt (n, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋) :=
  (Complex.re_add_im (dyadicRoundC n z)).symm.trans rfl

/-- **The raw-circle hypothesis `hraw`, almost surely.** For a regular version `G` of the free
field, a.s. the raw values of `X ω` at the circles `foldedCircle (dyadicRoundC n z) (radius k)`
agree with `G ω`; it suffices to test the countable grid (the range of `gridPt`). -/
theorem ae_raw_dyadic (hG : WedgeTK.IsRegVersion X P G) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      X ω (foldedCircle (dyadicRoundC n z) (radius k)) = G ω (dyadicRoundC n z, radius k) := by
  have hper : ∀ p : ℕ × ℤ × ℤ, ∀ᵐ ω ∂P, gridPt p ∈ Hbar → ∀ k : ℕ,
      X ω (foldedCircle (gridPt p) (radius k)) = G ω (gridPt p, radius k) := by
    intro p
    by_cases hc : gridPt p ∈ Hbar
    · refine (show ∀ᵐ ω ∂P, ∀ k : ℕ,
          X ω (foldedCircle (gridPt p) (radius k)) = G ω (gridPt p, radius k) from ?_).mono
        fun ω h _ => h
      rw [ae_all_iff]
      intro k
      filter_upwards [hG.raw (gridPt p) hc (radius k) (radius_pos k)] with ω h
      exact h.symm
    · filter_upwards with ω hcon
      exact absurd hcon hc
  have hall : ∀ᵐ ω ∂P, ∀ p : ℕ × ℤ × ℤ, gridPt p ∈ Hbar → ∀ k : ℕ,
      X ω (foldedCircle (gridPt p) (radius k)) = G ω (gridPt p, radius k) := by
    rw [ae_all_iff]
    exact hper
  filter_upwards [hall] with ω hω n z hz k
  have hpc : dyadicRoundC n z ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz n
  rw [dyadicRoundC_eq_grid n z]
  refine hω (n, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋) ?_ k
  rwa [← dyadicRoundC_eq_grid n z]

/-! ## 2. Null sets and circle atoms through the density rule -/

/-- A measure with a density against `μ` vanishes on `μ`-null sets. -/
theorem withDensity_eq_zero_of_measure_eq_zero {μ : Measure ℂ} {f : ℂ → ℝ≥0∞} {s : Set ℂ}
    (h : μ s = 0) : μ.withDensity f s = 0 :=
  (withDensity_absolutelyContinuous μ f) h

/-- **No circle atoms for the wedge field** (R23 (a), second input), from the local density rule and
the free field's `ae_sphere_null`. Note the radiality of `wedgeProfile` is not needed: the density
is finite and the free field gives the null set. -/
theorem qAreaMeasure_wedgeField_sphere_eq_zero {γ : ℝ} {x : FieldSample} {A : ℝ → ℝ} {Q : ℝ}
    (hdens : qAreaMeasure γ (wedgeField (lateralPart x) A Q) =
      (qAreaMeasure γ x).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * wedgeProfile x A Q z))))
    {a : ℝ} (hnull : qAreaMeasure γ x (Metric.sphere 0 a ∩ H) = 0) :
    qAreaMeasure γ (wedgeField (lateralPart x) A Q) (Metric.sphere 0 a ∩ H) = 0 := by
  rw [hdens]
  exact withDensity_eq_zero_of_measure_eq_zero hnull

/-- **Positivity for the wedge field** (R23 (a), third input), from the local density rule, the
free field's positivity on nonempty open subsets of `ℍ`, and continuity of the profile: on a closed
ball inside `V` the density `e^{γ g}` has a positive lower bound. -/
theorem qAreaMeasure_wedgeField_pos {γ : ℝ} {x : FieldSample} {A : ℝ → ℝ} {Q : ℝ}
    (hdens : qAreaMeasure γ (wedgeField (lateralPart x) A Q) =
      (qAreaMeasure γ x).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * wedgeProfile x A Q z))))
    (hcont : ContinuousOn (wedgeProfile x A Q) H)
    (hpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < qAreaMeasure γ x V)
    {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (hne : V.Nonempty) :
    0 < qAreaMeasure γ (wedgeField (lateralPart x) A Q) V := by
  obtain ⟨z, hzV⟩ := hne
  have hzH : z ∈ H := hVH hzV
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 hV z hzV
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 isOpen_H z hzH
  set r : ℝ := min r₁ r₂ / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; exact half_pos (lt_min hr₁ hr₂)
  have hrmin : r < min r₁ r₂ := by rw [hrdef]; linarith
  have hKV : Metric.closedBall z r ⊆ V := fun u hu =>
    hb₁ (by have h := Metric.mem_closedBall.1 hu; rw [Metric.mem_ball]
            linarith [min_le_left r₁ r₂])
  have hKH : Metric.closedBall z r ⊆ H := fun u hu =>
    hb₂ (by have h := Metric.mem_closedBall.1 hu; rw [Metric.mem_ball]
            linarith [min_le_right r₁ r₂])
  have hKmeas : MeasurableSet (Metric.closedBall z r) := Metric.isClosed_closedBall.measurableSet
  have hcontK : ContinuousOn (fun u => Real.exp (γ * wedgeProfile x A Q u))
      (Metric.closedBall z r) :=
    Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul (hcont.mono hKH)))
  obtain ⟨u₀, hu₀K, hu₀min⟩ := (isCompact_closedBall z r).exists_isMinOn
    ⟨z, Metric.mem_closedBall_self hr.le⟩ hcontK
  set c : ℝ := Real.exp (γ * wedgeProfile x A Q u₀) with hc
  have hcpos : 0 < c := Real.exp_pos _
  have hcK : ∀ u ∈ Metric.closedBall z r,
      ENNReal.ofReal c ≤ ENNReal.ofReal (Real.exp (γ * wedgeProfile x A Q u)) := by
    intro u hu
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hc]
    exact hu₀min hu
  have hμK : 0 < qAreaMeasure γ x (Metric.closedBall z r) :=
    lt_of_lt_of_le (hpos _ Metric.isOpen_ball
        (fun u hu => hKH (Metric.ball_subset_closedBall hu))
        ⟨z, Metric.mem_ball_self hr⟩) (measure_mono Metric.ball_subset_closedBall)
  rw [hdens]
  refine lt_of_lt_of_le
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hcpos).ne' (ne_of_gt hμK)) ?_
  calc ENNReal.ofReal c * qAreaMeasure γ x (Metric.closedBall z r)
      = ∫⁻ u in Metric.closedBall z r, ENNReal.ofReal c ∂qAreaMeasure γ x :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ u in Metric.closedBall z r,
          ENNReal.ofReal (Real.exp (γ * wedgeProfile x A Q u)) ∂qAreaMeasure γ x :=
        setLIntegral_mono' hKmeas hcK
    _ = (qAreaMeasure γ x).withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * wedgeProfile x A Q z)))
          (Metric.closedBall z r) := (withDensity_apply _ hKmeas).symm
    _ ≤ (qAreaMeasure γ x).withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * wedgeProfile x A Q z))) V :=
        measure_mono hKV

end WedgeCan

end QuantumZipper
