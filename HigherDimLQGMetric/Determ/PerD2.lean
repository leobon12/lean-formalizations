import HigherDimLQGMetric.Determ.ChainBound

/-! Mesh-uniform domination of the Efron–Stein increments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_perD₂ {d : ContMetric dim} (hd : d.IsLength) {C : ℝ} (hC : 1 ≤ C) {n : ℕ} {z w : Rd dim}
    (hz : ‖z‖ < n) (hw : ‖w‖ < n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)), θ ∈ determUnitShift dim →
      ∃ b : determFixedBox (d := dim) ε ((n : ℝ) + 1) → ℝ, (∀ k, 0 ≤ b k) ∧
        (∀ (k : determFixedBox (d := dim) ε ((n : ℝ) + 1)) (d'' : ContMetric dim),
          DetermCompat C ε θ (determFixedBox (d := dim) ε ((n : ℝ) + 1)) d d'' k.1 →
          max ((determF (n + 1) z w d'').toReal - (determF (n + 1) z w d).toReal) 0 ^ 2 ≤ b k) ∧
        ∑ k, b k ≤ (C ^ 2 - 1) * (determF (n + 1) z w d).toReal *
          (C ^ 2 * ((determF (n + 1) z w d).toReal + ε ^ (dim + 1)) +
            ε ^ (dim + 1) * (determFixedBox (d := dim) ε ((n : ℝ) + 1)).card) := by
  have hn1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  set c := C ^ 2 with hcdef
  have hc1 : 1 ≤ c := by nlinarith
  have hzn : z ∈ Metric.ball (0 : Rd dim) ((n + 1 : ℕ) : ℝ) :=
    Metric.ball_subset_ball hn1.le (mem_ball_zero_iff.2 hz)
  have hwn : w ∈ Metric.ball (0 : Rd dim) ((n + 1 : ℕ) : ℝ) :=
    Metric.ball_subset_ball hn1.le (mem_ball_zero_iff.2 hw)
  have hI1 : d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w ≠ ⊤ :=
    d.internal_ne_top_of_isPreconnected hd Metric.isOpen_ball (convex_ball _ _).isPreconnected hzn hwn
  have e1 : determF (n + 1) z w d = d.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w :=
    (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm
  have hε3 : (0 : ℝ) < ε ^ (dim + 1) := by positivity
  obtain ⟨P₂, hP₂c, hP₂0, hP₂1, hP₂m, hP₂l⟩ := determ_near_path d hI1 hε3
  have g2 := @determ_grid_null dim ε hε P₂ hP₂c.measurable (LQGMetric.LM.t17LenMeas (d.pt ∘ P₂) 0 1)
    (determ_sfinite_lenMeas d P₂ 0 1)
  filter_upwards [g2] with θ hθb hθ
  set s := determFixedBox (d := dim) ε ((n : ℝ) + 1) with hs
  set F₁ := (determF (n + 1) z w d).toReal
  have hfin₂ : d.len P₂ 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
  have hcb : Metric.ball (0 : Rd dim) ((n + 1 : ℕ) : ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by push_cast; rfl))
  have hPR₂ : MapsTo P₂ (Icc 0 1) (Metric.closedBall 0 ((n : ℝ) + 1)) :=
    fun t ht => hcb (hP₂m ht)
  have hnull₂ : LQGMetric.LM.t17LenMeas (d.pt ∘ P₂) 0 1 (Icc 0 1 ∩ P₂ ⁻¹' determGrid ε θ) = 0 :=
    measure_mono_null inter_subset_right hθb
  have hlen₂ : (d.len P₂ 0 1).toReal ≤ F₁ + ε ^ (dim + 1) := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
    rwa [ENNReal.toReal_add hI1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε3.le, ← e1] at this
  have hF₁len₂ : F₁ ≤ (d.len P₂ 0 1).toReal := by
    refine ENNReal.toReal_mono hfin₂ ?_
    rw [e1, ← hP₂0, ← hP₂1]
    exact internalEDist_le_curveLength (X := d.Space) zero_le_one
      (d.continuous_pt.comp_continuousOn hP₂c.continuousOn) (fun t ht => ⟨P₂ t, hP₂m ht, rfl⟩)
  have hF₁0 : 0 ≤ F₁ := ENNReal.toReal_nonneg
  have hsum₂ : (d.len P₂ 0 1).toReal = ∑ k ∈ s, determPiece d P₂ 0 1 ε θ k :=
    (determ_resample (D' := d) zero_le_one (fun x y => by rw [one_mul]) hε hθ hP₂c
      zero_le_one hfin₂ hPR₂ hnull₂ (k₀ := fun _ => 0) (fun _ _ _ _ _ _ _ => rfl)).2.2.2.1
  have hpn : ∀ k, 0 ≤ determPiece d P₂ 0 1 ε θ k := fun _ => ENNReal.toReal_nonneg
  set b₂ : s → ℝ := fun k => (d.len P₂ 0 1).toReal - F₁ + (c - 1) * determPiece d P₂ 0 1 ε θ k
  have hb₂ : ∀ k, 0 ≤ b₂ k := by
    intro k
    have h2 := hpn k
    simp only [b₂]
    nlinarith
  have hF0 : determF (n + 1) z w d ≠ ⊤ := e1 ▸ hI1
  have hA : ∀ (k : s) (d'' : ContMetric dim), DetermCompat C ε θ s d d'' k.1 →
      max ((determF (n + 1) z w d'').toReal - F₁) 0 ≤ b₂ k ∧
        max ((determF (n + 1) z w d'').toReal - F₁) 0 ≤ (c - 1) * F₁ := by
    intro k d'' hcomp
    refine ⟨determ_A_bound hc1 hcomp.2.1 hε hθ hP₂c zero_le_one hfin₂ hPR₂ hP₂m hP₂0 hP₂1
      hnull₂ k.2 hcomp.2.2.2, max_le ?_ (by nlinarith)⟩
    have h1 := determ_chainInf_le_of_le hd (by positivity : (0 : ℝ) < c) hcomp.2.1
      (Metric.isOpen_ball (x := (0 : Rd dim)) (ε := ((n + 1 : ℕ) : ℝ))) z w
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF0) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    have : (determF (n + 1) z w d'').toReal ≤ c * F₁ := h2
    linarith
  refine ⟨fun k => (c - 1) * F₁ * b₂ k, fun k => mul_nonneg (mul_nonneg (by linarith) hF₁0)
    (hb₂ k), fun k d'' hcomp => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hA k d'' hcomp
    have h0 : 0 ≤ max ((determF (n + 1) z w d'').toReal - F₁) 0 := le_max_right _ _
    rw [sq]
    exact mul_le_mul h2 h1 h0 (h0.trans h2)
  · rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) hF₁0)
    have hsplit : ∑ k, b₂ k = s.card * ((d.len P₂ 0 1).toReal - F₁) +
        (c - 1) * ∑ k ∈ s, determPiece d P₂ 0 1 ε θ k := by
      simp only [b₂, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, ← Finset.mul_sum]
      rw [Finset.sum_coe_sort s (fun k => determPiece d P₂ 0 1 ε θ k)]
    rw [hsplit, ← hsum₂]
    have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    nlinarith

end HigherDimLQGMetric
