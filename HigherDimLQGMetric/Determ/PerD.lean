import HigherDimLQGMetric.Determ.NearPiece
import HigherDimLQGMetric.Determ.GridJoint
import LQGMetric.Papers.DFGPS.T12P1A

/-! Two path bounds for every compatible resampling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

theorem determ_perD {D : ContMetric d} (hD : D.IsLength) {C : ℝ} (hC : 1 ≤ C) {n : ℕ} {z w : (Rd d)}
    (hz : ‖z‖ < n) (hw : ‖w‖ < n) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ᵐ θ ∂(volume : Measure (Fin d → ℝ)),
      θ ∈ determUnitShift d →
      ∃ b : determFixedBox (d := d) ε ((n : ℝ) + 1) → ℝ, (∀ k, 0 ≤ b k) ∧
        (∀ (k : determFixedBox (d := d) ε ((n : ℝ) + 1)) (D' : ContMetric d),
          DetermCompat C ε θ (determFixedBox (d := d) ε ((n : ℝ) + 1)) D D' k.1 →
          max ((determF (n + 1) z w D').toReal - (determF (n + 1) z w D).toReal) 0 ^ 2 ≤ b k) ∧
        ∑ k, b k ≤ C ^ 2 * ((determF n z w D).toReal - (determF (n + 1) z w D).toReal + ε ^ (d + 1) + κ) *
          (C ^ 2 * ((determF (n + 1) z w D).toReal + ε ^ (d + 1)) +
            ε ^ (d + 1) * (determFixedBox (d := d) ε ((n : ℝ) + 1)).card) := by
  have hn1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨r, hr, hnb⟩ := determ_near_bound hD hn1 hκ
  refine ⟨r / (Real.sqrt d + 1), by positivity, fun ε hε hεr => ?_⟩
  set c := C ^ 2 with hcdef
  have hc1 : 1 ≤ c := by nlinarith
  have hzn : z ∈ Metric.ball (0 : (Rd d)) (n : ℝ) := mem_ball_zero_iff.2 hz
  have hwn : w ∈ Metric.ball (0 : (Rd d)) (n : ℝ) := mem_ball_zero_iff.2 hw
  have hsub : Metric.ball (0 : (Rd d)) (n : ℝ) ⊆ Metric.ball 0 ((n + 1 : ℕ) : ℝ) :=
    Metric.ball_subset_ball hn1.le
  have hI0 : D.internal (Metric.ball 0 (n : ℝ)) z w ≠ ⊤ :=
    D.internal_ne_top_of_isPreconnected hD Metric.isOpen_ball (convex_ball _ _).isPreconnected hzn hwn
  have hI1 : D.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w ≠ ⊤ :=
    D.internal_ne_top_of_isPreconnected hD Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (hsub hzn) (hsub hwn)
  have e0 : determF n z w D = D.internal (Metric.ball 0 (n : ℝ)) z w :=
    (D.internal_eq_chainInf hD Metric.isOpen_ball z w).symm
  have e1 : determF (n + 1) z w D = D.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) z w :=
    (D.internal_eq_chainInf hD Metric.isOpen_ball z w).symm
  have hε3 : (0 : ℝ) < ε ^ (d + 1) := by positivity
  obtain ⟨P₁, hP₁c, hP₁0, hP₁1, hP₁m, hP₁l⟩ := determ_near_path D hI0 hε3
  obtain ⟨P₂, hP₂c, hP₂0, hP₂1, hP₂m, hP₂l⟩ := determ_near_path D hI1 hε3
  have g1 := @determ_grid_null d ε hε P₁ hP₁c.measurable
    (LQGMetric.LM.t17LenMeas (D.pt ∘ P₁) 0 1)
    (determ_sfinite_lenMeas D P₁ 0 1)
  have g2 := @determ_grid_null d ε hε P₂ hP₂c.measurable
    (LQGMetric.LM.t17LenMeas (D.pt ∘ P₂) 0 1)
    (determ_sfinite_lenMeas D P₂ 0 1)
  filter_upwards [g1, g2] with θ hθa hθb hθ
  set s := determFixedBox (d := d) ε ((n : ℝ) + 1) with hs
  set F₀ := (determF n z w D).toReal
  set F₁ := (determF (n + 1) z w D).toReal
  -- the two curves
  have hfin₁ : D.len P₁ 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI0, ENNReal.ofReal_ne_top⟩) hP₁l
  have hfin₂ : D.len P₂ 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
  have hcb : Metric.ball (0 : (Rd d)) ((n + 1 : ℕ) : ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by push_cast; rfl))
  have hPR₁ : MapsTo P₁ (Icc 0 1) (Metric.closedBall 0 ((n : ℝ) + 1)) :=
    fun t ht => hcb (hsub (hP₁m ht))
  have hPR₂ : MapsTo P₂ (Icc 0 1) (Metric.closedBall 0 ((n : ℝ) + 1)) :=
    fun t ht => hcb (hP₂m ht)
  have hnull₁ : LQGMetric.LM.t17LenMeas (D.pt ∘ P₁) 0 1 (Icc 0 1 ∩ P₁ ⁻¹' determGrid ε θ) = 0 :=
    measure_mono_null inter_subset_right hθa
  have hnull₂ : LQGMetric.LM.t17LenMeas (D.pt ∘ P₂) 0 1 (Icc 0 1 ∩ P₂ ⁻¹' determGrid ε θ) = 0 :=
    measure_mono_null inter_subset_right hθb
  -- real-valued facts
  have hlen₁ : (D.len P₁ 0 1).toReal ≤ F₀ + ε ^ (d + 1) := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI0, ENNReal.ofReal_ne_top⟩) hP₁l
    rwa [ENNReal.toReal_add hI0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε3.le, ← e0] at this
  have hlen₂ : (D.len P₂ 0 1).toReal ≤ F₁ + ε ^ (d + 1) := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hI1, ENNReal.ofReal_ne_top⟩) hP₂l
    rwa [ENNReal.toReal_add hI1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε3.le, ← e1] at this
  have hF₁len₂ : F₁ ≤ (D.len P₂ 0 1).toReal := by
    refine ENNReal.toReal_mono hfin₂ ?_
    rw [e1, ← hP₂0, ← hP₂1]
    exact internalEDist_le_curveLength (X := D.Space) zero_le_one
      (D.continuous_pt.comp_continuousOn hP₂c.continuousOn) (fun t ht => ⟨P₂ t, hP₂m ht, rfl⟩)
  have hF₁F₀ : F₁ ≤ F₀ := by
    dsimp [F₀, F₁]
    rw [e0, e1]
    exact ENNReal.toReal_mono hI0 (internalEDist_anti
      (image_mono (Metric.ball_subset_ball hn1.le)) _ _)
  have hpiece₁ : ∀ k : Fin d → ℤ, determPiece D P₁ 0 1 ε θ k ≤ F₀ + ε ^ (d + 1) + κ - F₁ := by
    intro k
    have hnear : D.len P₁ 0 1 ≤ D.internal (Metric.ball 0 (n : ℝ)) (P₁ 0) (P₁ 1) +
        ENNReal.ofReal (ε ^ (d + 1)) := by rw [hP₁0, hP₁1]; exact hP₁l
    have := determ_piece_le hnb hP₁c hfin₁ (fun t ht => Metric.ball_subset_closedBall (hP₁m ht))
      hε3.le hnear (by rw [hP₁0, hP₁1]; exact hI0) hκ.le hε (show Real.sqrt d * ε < r by
        have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
        have he : ε * (Real.sqrt d + 1) < r :=
          (lt_div_iff₀ (by positivity : 0 < Real.sqrt d + 1)).1 hεr
        nlinarith) θ k
    rwa [hP₁0, hP₁1, ← e0, ← e1] at this
  have hsum₂ : (D.len P₂ 0 1).toReal = ∑ k ∈ s, determPiece D P₂ 0 1 ε θ k :=
    (determ_resample (D' := D) zero_le_one (fun x y => by rw [one_mul]) hε hθ hP₂c
      zero_le_one hfin₂ hPR₂ hnull₂ (k₀ := fun _ => 0) (fun _ _ _ _ _ _ _ => rfl)).2.2.2.1
  have hpn : ∀ (P : ℝ → (Rd d)) k, 0 ≤ determPiece D P 0 1 ε θ k := fun _ _ => ENNReal.toReal_nonneg
  -- the bounds `b₁, b₂`
  set b₁ : s → ℝ := fun k => (D.len P₁ 0 1).toReal - F₁ + (c - 1) * determPiece D P₁ 0 1 ε θ k
  set b₂ : s → ℝ := fun k => (D.len P₂ 0 1).toReal - F₁ + (c - 1) * determPiece D P₂ 0 1 ε θ k
  have hA : ∀ (k : s) (D' : ContMetric d), DetermCompat C ε θ s D D' k.1 →
      max ((determF (n + 1) z w D').toReal - F₁) 0 ≤ b₁ k ∧
        max ((determF (n + 1) z w D').toReal - F₁) 0 ≤ b₂ k := by
    intro k D' hcomp
    exact ⟨determ_A_bound hc1 hcomp.2.1 hε hθ hP₁c zero_le_one hfin₁ hPR₁
      (fun t ht => hsub (hP₁m ht)) hP₁0 hP₁1 hnull₁ k.2 hcomp.2.2.2,
      determ_A_bound hc1 hcomp.2.1 hε hθ hP₂c zero_le_one hfin₂ hPR₂ hP₂m hP₂0 hP₂1 hnull₂
        k.2 hcomp.2.2.2⟩
  set β := c * (F₀ - F₁ + ε ^ (d + 1) + κ)
  have hb₁ : ∀ k, b₁ k ≤ β := by
    intro k
    have h1 := hpiece₁ k
    have h2 := hpn P₁ k
    simp only [b₁, β]
    nlinarith
  have hb₂ : ∀ k, 0 ≤ b₂ k := by
    intro k
    have h2 := hpn P₂ k
    simp only [b₂]
    nlinarith
  have hF₀len₁ : F₀ ≤ (D.len P₁ 0 1).toReal := by
    refine ENNReal.toReal_mono hfin₁ ?_
    rw [e0, ← hP₁0, ← hP₁1]
    exact internalEDist_le_curveLength (X := D.Space) zero_le_one
      (D.continuous_pt.comp_continuousOn hP₁c.continuousOn) (fun t ht => ⟨P₁ t, hP₁m ht, rfl⟩)
  have hb₁0 : ∀ k, 0 ≤ b₁ k := by
    intro k
    have h2 := hpn P₁ k
    simp only [b₁]
    nlinarith
  refine ⟨fun k => b₁ k * b₂ k, fun k => mul_nonneg (hb₁0 k) (hb₂ k), fun k D' hcomp => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hA k D' hcomp
    have h0 : 0 ≤ max ((determF (n + 1) z w D').toReal - F₁) 0 := le_max_right _ _
    rw [sq]
    exact mul_le_mul h1 h2 h0 (h0.trans h1)
  · have hβ : 0 ≤ β := by
      simp only [β]; nlinarith
    calc ∑ k, b₁ k * b₂ k ≤ ∑ k, β * b₂ k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hb₁ k) (hb₂ k)
      _ = β * ∑ k, b₂ k := (Finset.mul_sum _ _ _).symm
      _ ≤ β * (c * (F₁ + ε ^ (d + 1)) + ε ^ (d + 1) * s.card) := by
          refine mul_le_mul_of_nonneg_left ?_ hβ
          have hsplit : ∑ k, b₂ k = s.card * ((D.len P₂ 0 1).toReal - F₁) +
              (c - 1) * ∑ k ∈ s, determPiece D P₂ 0 1 ε θ k := by
            simp only [b₂, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_coe, nsmul_eq_mul, ← Finset.mul_sum]
            rw [Finset.sum_coe_sort s (fun k => determPiece D P₂ 0 1 ε θ k)]
          rw [hsplit, ← hsum₂]
          have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
          have hF₁0 : 0 ≤ F₁ := ENNReal.toReal_nonneg
          nlinarith

end HigherDimLQGMetric
