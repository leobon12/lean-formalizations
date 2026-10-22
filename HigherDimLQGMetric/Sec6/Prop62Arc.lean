import HigherDimLQGMetric.Sec6.Prop62Witness
import HigherDimLQGMetric.Routing.Lemma41Arc

/-!
# [S] Proposition 6.2: simple favourable arcs from witness paths

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Construction*: "For `κ ∈ 𝒢`, Lemma 4.1 applies with
arcs = shortest `D̃^U` paths in the witness images"), blueprint Part A §6 (`prop:62`, step (7)),
source l. 1078–1081.

`s6b_simpleArc_of_witness`: a witness path of a configuration with `c ζ ≤ ζ̃` contains a simple arc
with the same endpoints, of `ζ̃`-length at most that of the witness and of finite `ζ`-length: the
input of S2b's `lemma41_outer_routing_coordinates`. The arc is S2b's injective intrinsic geodesic
inside the compact image (`lemma41_exists_simple_in_pathImage`), in the `ζ̃` metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter _root_.Topology BoundedContinuousFunction unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- Comparison of coordinate lengths: `ζ ≤ c⁻¹ ζ̃` pointwise gives `len_ζ ≤ c⁻¹ len_ζ̃`. -/
theorem s6b_curveLengthWith_le_inv_mul {X : Type*} {ζ ζt : X × X → ℝ} {c : ℝ} (hc : 0 < c)
    (hcmp : ∀ x y, c * ζ (x, y) ≤ ζt (x, y)) (P : ℝ → X) (a b : ℝ) :
    curveLengthWith (fun x y => ENNReal.ofReal (ζ (x, y))) P a b ≤
      ENNReal.ofReal c⁻¹ * curveLengthWith (fun x y => ENNReal.ofReal (ζt (x, y))) P a b := by
  rw [← curveLengthWith_const_mul]
  refine curveLengthWith_mono fun u v _ _ _ => ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hcmp (P u) (P v)
  rw [le_inv_mul_iff₀ hc]
  exact h

/-- **Simple arcs from witnesses.** -/
theorem s6b_simpleArc_of_witness {q : ConfigC d} (hq1 : IsCoordinate q.1)
    (hq2 : IsCoordinate q.2.1) {c : ℝ} (hc : 0 < c)
    (hcmp : ∀ x y, c * q.1 (x, y) ≤ q.2.1 (x, y)) {B : Set (Rd d)} {A a₁ c₂ : ℝ}
    (ha₁ : 0 < a₁) (hw : s6bWitness q B A a₁ c₂) :
    ∃ γ : ℝ → configOuter d, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (γ t : Rd d) ∈ B) ∧
      curveLength (MetricFunSpace.pt q.1 hq1.metric ∘ γ) 0 1 ≠ ∞ ∧
      a₁ ≤ q.1 (γ 0, γ 1) ∧
      curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y))) γ 0 1 ≤
        ENNReal.ofReal (c₂ * q.1 (γ 0, γ 1)) := by
  obtain ⟨P, hPB, -, hPsep, hPlen⟩ := hw
  set ρ : configOuter d × configOuter d → ℝ := ⇑q.2.1 with hρ_def
  set pt := MetricFunSpace.pt ρ hq2.metric with hpt
  set val := LQGMetric.metricFunSpaceVal ρ hq2.metric with hval
  set x₀ := P 0 with hx₀
  set x₁ := P 1 with hx₁
  -- the witness as a path in the `ζ̃` metric space
  let Γ : Path (pt x₀) (pt x₁) :=
    { toFun := fun t => pt (P t)
      continuous_toFun := hq2.pt_continuous.comp P.continuous
      source' := rfl
      target' := rfl }
  have hΓext : ∀ t, Γ.extend t = pt (Set.IccExtend zero_le_one P t) := fun t => rfl
  have hΓlen : pathLength Γ = curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y)))
      (Set.IccExtend zero_le_one P) 0 1 := by
    rw [curveLengthWith_metricFunSpace hq2.metric]
    rfl
  have hfin : pathLength Γ ≠ ∞ := by
    rw [hΓlen]
    exact (hPlen.trans_lt ENNReal.ofReal_lt_top).ne
  obtain ⟨Q, hQc, hQrange, hQ0, hQℓ, hQunit, hQinj⟩ :=
    lemma41_exists_simple_in_pathImage Γ hfin (a := pt x₀) (b := pt x₁)
      ⟨0, rfl⟩ ⟨1, rfl⟩
  set ℓ := (internalEDist (range Γ) (pt x₀) (pt x₁)).toReal with hℓ_def
  -- the internal distance is finite and positive
  have hint_le : internalEDist (range Γ) (pt x₀) (pt x₁) ≤ pathLength Γ :=
    internalEDist_le_pathLength Γ (fun t => mem_range_self t)
  have hint_fin : internalEDist (range Γ) (pt x₀) (pt x₁) ≠ ∞ := (hint_le.trans_lt
    (lt_top_iff_ne_top.2 hfin)).ne
  have hx01 : x₀ ≠ x₁ := by
    intro h
    have : q.1 (x₀, x₁) = 0 := by rw [h]; exact hq1.metric.self_eq_zero x₁
    linarith [hPsep]
  have hpos_edist : 0 < edist (pt x₀) (pt x₁) := edist_pos.2 (fun h => hx01 h)
  have hℓpos : 0 < ℓ := ENNReal.toReal_pos
    ((hpos_edist.trans_le (edist_le_internalEDist _ _ _)).ne') hint_fin
  have hℓeq : ENNReal.ofReal ℓ = internalEDist (range Γ) (pt x₀) (pt x₁) :=
    ENNReal.ofReal_toReal hint_fin
  -- the arc on `[0, 1]`
  let φ : ℝ → ℝ := fun t => ℓ * t
  have hφmap : MapsTo φ (Icc (0 : ℝ) 1) (Icc 0 ℓ) := fun t ht =>
    ⟨mul_nonneg hℓpos.le ht.1, mul_le_of_le_one_right hℓpos.le ht.2⟩
  let γ : ℝ → configOuter d := fun t => val (Q (φ t))
  have hγc : ContinuousOn γ (Icc 0 1) :=
    hq2.val_continuous.comp_continuousOn (hQc.comp (by fun_prop) hφmap)
  have hγi : InjOn γ (Icc 0 1) := by
    intro s hs t ht hst
    have h1 : Q (φ s) = Q (φ t) := hst
    have h2 := hQinj (hφmap hs) (hφmap ht) h1
    exact mul_left_cancel₀ hℓpos.ne' h2
  have hγB : ∀ t ∈ Icc (0 : ℝ) 1, (γ t : Rd d) ∈ B := by
    intro t ht
    obtain ⟨s, hs⟩ := hQrange (hφmap ht)
    change ((val (Q (φ t)) : configOuter d) : Rd d) ∈ B
    rw [← hs]
    exact hPB s
  have hγ0 : γ 0 = x₀ := by
    change val (Q (ℓ * 0)) = x₀
    rw [mul_zero, hQ0]
    rfl
  have hγ1 : γ 1 = x₁ := by
    change val (Q (ℓ * 1)) = x₁
    rw [mul_one, hQℓ]
    rfl
  -- the `ζ̃`-length of the arc is at most `ℓ`
  have hγlen : curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) γ 0 1 ≤
      ENNReal.ofReal ℓ := by
    rw [curveLengthWith_metricFunSpace hq2.metric]
    have hcomp : (pt ∘ γ) = Q ∘ φ := by
      funext t
      rfl
    rw [hcomp, curveLength_comp_of_continuousOn_monotoneOn Q zero_le_one (by fun_prop)
      (fun s _ t _ hst => mul_le_mul_of_nonneg_left hst hℓpos.le)]
    simp only [mul_zero, mul_one]
    rw [← curveLengthWith_edist]
    have h := s6b_curveLengthWith_le_of_speed (δ := edist) (P := Q) (a := 0) (b := ℓ)
      (L := 1) zero_le_one (fun s t hs hst ht => by
        rw [one_mul]
        calc edist (Q s) (Q t) ≤ internalEDist (range Γ) (Q s) (Q t) :=
              edist_le_internalEDist _ _ _
          _ = ENNReal.ofReal |t - s| := hQunit s ⟨hs, hst.trans ht⟩ t ⟨hs.trans hst, ht⟩
          _ = ENNReal.ofReal (t - s) := by rw [abs_of_nonneg (sub_nonneg.2 hst)])
    simpa using h
  refine ⟨γ, hγc, hγi, hγB, ?_, ?_, ?_⟩
  · -- finite `ζ`-length
    rw [← curveLengthWith_metricFunSpace hq1.metric]
    refine ((s6b_curveLengthWith_le_inv_mul hc hcmp γ 0 1).trans_lt ?_).ne
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hγlen.trans_lt ENNReal.ofReal_lt_top)
  · rw [hγ0, hγ1]
    exact hPsep
  · rw [hγ0, hγ1]
    calc curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y))) γ 0 1
        ≤ ENNReal.ofReal ℓ := hγlen
      _ = internalEDist (range Γ) (pt x₀) (pt x₁) := hℓeq
      _ ≤ pathLength Γ := hint_le
      _ = _ := hΓlen
      _ ≤ _ := hPlen

end HigherDimLQGMetric
