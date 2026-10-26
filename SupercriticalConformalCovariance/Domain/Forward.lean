import SupercriticalConformalCovariance.Domain.Sample

/-!
# Forward curve transfer for unbounded continuous Weyl shifts

For a length space `D` with continuous identity `(ℂ, D) → ℂ` and an LSC
metric `E = e^{ξ g} · D` with `g ∈ C(ℂ)` **unbounded**, the identity `(ℂ, D) → (ℂ, E)` is continuous
(`continuous_weyl_forward`), so every `D`-curve is an `E`-curve (`isCurve_weyl_forward`). The sealed
`Toolkit.WeylShift.curve_forward` needs a global bound on `g`; here near-geodesics of `D` from `x`
stay in a small Euclidean ball, where `g` is bounded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open SupercriticalLQGUniqueness (LSCMetric weylScale)

theorem continuous_weyl_forward (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) (hL : D.IsLengthSpace)
    (hE : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q) :
    Continuous (fun z : D.Space => E.pt (forget D z)) := by
  rw [continuous_iff_continuousAt]
  intro x
  set x0 : ℂ := forget D x with hx0
  -- `g ≤ M` on a Euclidean ball around `x0`
  set M : ℝ := g x0 + 1 with hM
  obtain ⟨ρ, hρ, hρg⟩ := Metric.continuousAt_iff.1 g.continuous.continuousAt 1 one_pos
  -- small `D`-balls lie in that Euclidean ball
  have hAt := hforget.continuousAt (x := D.pt x0)
  rw [ContinuousAt, (Metric.nhds_basis_eball).tendsto_iff Metric.nhds_basis_ball] at hAt
  obtain ⟨r, hr, hrball⟩ := hAt ρ hρ
  set k : ℝ := Real.exp (ξ * M) with hk
  have hk0 : 0 < k := Real.exp_pos _
  rw [ContinuousAt, (Metric.nhds_basis_eball).tendsto_iff Metric.nhds_basis_eball]
  intro η hη
  set η₀ : ℝ≥0∞ := min η 1 with hη₀
  have hη₀t : η₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hη₀p : 0 < η₀ := lt_min hη one_pos
  set η' : ℝ := η₀.toReal with hη'
  have hη'p : 0 < η' := ENNReal.toReal_pos hη₀p.ne' hη₀t
  have hη'le : ENNReal.ofReal η' ≤ η := by
    rw [hη', ENNReal.ofReal_toReal hη₀t]; exact min_le_left _ _
  set δ : ℝ≥0∞ := min r (ENNReal.ofReal (η' / (2 * k))) with hδ
  have hδp : 0 < δ := lt_min hr (ENNReal.ofReal_pos.2 (by positivity))
  refine ⟨δ, hδp, fun y hy => ?_⟩
  rw [Metric.mem_eball] at hy ⊢
  have hDy : D (x0, forget D y) < δ := by
    have : edist y x = D (forget D y, x0) := rfl
    rw [this, D.isExtMetric.2.2.1] at hy
    exact hy
  -- a near-geodesic from `x0` to `y`
  obtain ⟨ε, hε0, hεlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hDy
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ :=
    hL x0 (forget D y) (hDy.trans_le le_top) (ε : ℝ) (by exact_mod_cast hε0)
  rw [ENNReal.ofReal_coe_nnreal] at hlen
  have hlenδ : D.len P a b < δ := hlen.trans_lt hεlt
  -- the near-geodesic stays where `g ≤ M`
  have hgP : ∀ t ∈ Icc a b, g (P t) ≤ M := by
    intro t ht
    have h1 : D (x0, P t) ≤ D.len P a b := by
      have := eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.2 hP.1) ht
      rw [← hPa]
      exact this
    have h2 : edist (D.pt (P t)) (D.pt x0) < r := by
      have : edist (D.pt (P t)) (D.pt x0) = D (x0, P t) := D.isExtMetric.2.2.1 _ _
      rw [this]
      exact (h1.trans_lt hlenδ).trans_le (min_le_left _ _)
    have h3 := hrball (D.pt (P t)) (Metric.mem_eball.2 h2)
    rw [Metric.mem_ball] at h3
    have h4 := hρg h3
    rw [Real.dist_eq] at h4
    have : g (P t) - g x0 < 1 := (abs_lt.1 h4).2
    show g (P t) ≤ g x0 + 1
    linarith
  -- the Weyl bound along it
  have hEle : E (x0, forget D y) ≤ ENNReal.ofReal k * D.len P a b := by
    rw [hE, SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.weylScale_eq_weylDistOn
      D ξ g hforget]
    have hw := HigherDimLQGMetric.weylDistOn_le_of_curve
      (w := fun z : D.Space => Real.exp (ξ * g (forget D z))) hP.1 hP.2
      (mapsTo_univ (D.pt ∘ P) (Icc a b))
    have hb := HigherDimLQGMetric.weightedLength_le_ofReal_mul_curveLength
      (w := fun z : D.Space => Real.exp (ξ * g (forget D z))) (P := D.pt ∘ P) (a := a) (b := b)
      (M := k) (fun s hs => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hgP s hs) hξ))
    calc _ = HigherDimLQGMetric.weylDistOn (fun z : D.Space => Real.exp (ξ * g (forget D z)))
          univ ((D.pt ∘ P) a) ((D.pt ∘ P) b) := by
          simp only [Function.comp_apply, hPa, hPb]; rfl
      _ ≤ _ := hw.trans hb
  calc edist (E.pt (forget D y)) (E.pt (forget D x)) = E (x0, forget D y) :=
        E.isExtMetric.2.2.1 _ _
    _ ≤ ENNReal.ofReal k * D.len P a b := hEle
    _ ≤ ENNReal.ofReal k * ENNReal.ofReal (η' / (2 * k)) :=
        mul_le_mul' le_rfl (hlenδ.le.trans (min_le_right _ _))
    _ = ENNReal.ofReal (η' / 2) := by
        rw [← ENNReal.ofReal_mul hk0.le]
        congr 1
        field_simp
    _ < ENNReal.ofReal η' := (ENNReal.ofReal_lt_ofReal_iff hη'p).2 (half_lt_self hη'p)
    _ ≤ η := hη'le

/-- Every `D`-curve is a curve of the continuously Weyl-shifted metric (no bound on the shift). -/
theorem isCurve_weyl_forward {D E : LSCMetric} {ξ : ℝ} (hξ : 0 ≤ ξ) {g : C(ℂ, ℝ)}
    (hforget : Continuous (forget D)) (hL : D.IsLengthSpace)
    (hE : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q) {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    E.IsCurve P a b :=
  ⟨hP.1, (continuous_weyl_forward D E ξ hξ g hforget hL hE).comp_continuousOn hP.2⟩

end SupercriticalConformalCovariance.Domain
