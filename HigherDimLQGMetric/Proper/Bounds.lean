import HigherDimLQGMetric.Proper.Tight
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Metric.ContMetric
import LQGMetric.Papers.GM.S2.TightA

/-!
# Lower sphere and upper compact-set bounds from sharp weak tightness

This is the d-dimensional specialization of the generic compactness argument in
`LQGMetric.Papers.GM.S2.TightA`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
  {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistRd d)

/-- Uniform lower bound for the normalized distance from the origin to the unit sphere. -/
theorem proper_exists_sphere_lower (hD : IsSharpWeakExpMetric d ξ Q D)
    (hh : IsWholeSpaceLGF h P) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℝ, 0 < r →
      P {ω | ∃ v ∈ Metric.sphere (0 : Rd d) 1,
        normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r (0, v) ≤ a} < ε := by
  have hT : TightOver P (fun r ω => normalizedAtScale ξ D
      (fun s => s ^ (ξ * Q)) (h ω) r) (Ioi 0) :=
    hD.tight_bdd P h hh.isLGFPlusBddCont
  let A : ℕ → Set (Rd d × Rd d) := fun _ => ({0} : Set (Rd d)) ×ˢ Metric.sphere 0 1
  let U : ℕ → Set ℝ := fun n => Ioi ((1 : ℝ) / (n + 1))
  have hA : ∀ n, IsCompact (A n) := fun _ => isCompact_singleton.prod (isCompact_sphere _ _)
  have hAa : Antitone A := fun _ _ _ => le_refl _
  have hU : ∀ n, IsOpen (U n) := fun _ => isOpen_Ioi
  have hUm : Monotone U := fun m n hmn =>
    Ioi_subset_Ioi (LQGMetric.GM.Tight.one_div_succ_anti hmn)
  have hmet : ∀ e : C(Rd d × Rd d, ℝ), IsContinuousMetric e →
      ∀ x ∈ ⋂ n, A n, ∃ n, e x ∈ U n := by
    intro e he x hx
    have hx' : x ∈ A 0 := mem_iInter.1 hx 0
    have hx0 : x.1 = 0 := hx'.1
    have hx1 : x.2 ∈ Metric.sphere (0 : Rd d) 1 := hx'.2
    have hv : x.2 ≠ 0 := by
      intro heq
      rw [heq, Metric.mem_sphere, dist_self] at hx1
      norm_num at hx1
    have hp : 0 < e x := by
      exact ContMetric.apply_pos (⟨e, he⟩ : ContMetric d) (by
        intro h
        apply hv
        exact h.symm.trans hx0)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hp
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := proper_tight_mapsTo hT hA hAa hU hUm hmet hε
  refine ⟨1 / (n + 1), by positivity, fun r hr => ?_⟩
  have hevent : {ω | ∃ v ∈ Metric.sphere (0 : Rd d) 1,
        normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r (0, v) ≤
          1 / (n + 1)} =
      {ω | ¬ MapsTo (normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r)
        (A n) (U n)} := by
    ext ω
    simp only [A, U, MapsTo, not_forall, not_lt, mem_Ioi, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, hle⟩
      exact ⟨(0, v), ⟨rfl, hv⟩, hle⟩
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, hle⟩
      have hux : u = 0 := by simpa only [Set.mem_singleton_iff] using hu
      rw [hux] at hle
      exact ⟨v, hv, hle⟩
  rw [hevent]
  exact hn r hr

/-- Uniform upper bound for the normalized diameter of a fixed Euclidean closed ball. -/
theorem proper_exists_diameter_upper (hD : IsSharpWeakExpMetric d ξ Q D)
    (hh : IsWholeSpaceLGF h P) (L : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℝ, 0 < r →
      P {ω | ∃ u ∈ Metric.closedBall (0 : Rd d) L,
        ∃ v ∈ Metric.closedBall (0 : Rd d) L,
          b ≤ normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r (u, v)} < ε := by
  have hT : TightOver P (fun r ω => normalizedAtScale ξ D
      (fun s => s ^ (ξ * Q)) (h ω) r) (Ioi 0) :=
    hD.tight_bdd P h hh.isLGFPlusBddCont
  let A : ℕ → Set (Rd d × Rd d) := fun _ =>
    Metric.closedBall (0 : Rd d) L ×ˢ Metric.closedBall 0 L
  let U : ℕ → Set ℝ := fun n => Iio ((n : ℝ) + 1)
  have hA : ∀ n, IsCompact (A n) := fun _ => (isCompact_closedBall _ _).prod
    (isCompact_closedBall _ _)
  have hAa : Antitone A := fun _ _ _ => le_refl _
  have hU : ∀ n, IsOpen (U n) := fun _ => isOpen_Iio
  have hUm : Monotone U := fun m n hmn => Iio_subset_Iio (by exact_mod_cast Nat.succ_le_succ hmn)
  have hmet : ∀ e : C(Rd d × Rd d, ℝ), IsContinuousMetric e →
      ∀ x ∈ ⋂ n, A n, ∃ n, e x ∈ U n := by
    intro e _ x _
    obtain ⟨n, hn⟩ := exists_nat_gt (e x)
    exact ⟨n, show e x < (n : ℝ) + 1 by linarith⟩
  obtain ⟨n, hn⟩ := proper_tight_mapsTo hT hA hAa hU hUm hmet hε
  refine ⟨n + 1, by positivity, fun r hr => ?_⟩
  have hevent : {ω | ∃ u ∈ Metric.closedBall (0 : Rd d) L,
        ∃ v ∈ Metric.closedBall (0 : Rd d) L,
          (n : ℝ) + 1 ≤ normalizedAtScale ξ D
            (fun s => s ^ (ξ * Q)) (h ω) r (u, v)} =
      {ω | ¬ MapsTo (normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r)
        (A n) (U n)} := by
    ext ω
    simp only [A, U, MapsTo, not_forall, not_lt, mem_Iio, Set.mem_prod]
    constructor
    · rintro ⟨u, hu, v, hv, hle⟩
      exact ⟨(u, v), ⟨hu, hv⟩, hle⟩
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, hle⟩
      exact ⟨u, hu, v, hv, hle⟩
  rw [hevent]
  exact hn r hr

end HigherDimLQGMetric
