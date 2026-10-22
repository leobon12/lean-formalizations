import HigherDimLQGMetric.Coord.PathAgreement

/-!
# Transfer from an inner coordinate to an outer coordinate

The inner coordinate lives on a subtype `V`; the outer coordinate lives on
`X`.  This keeps the boundary limit points in the correct carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal NNReal

namespace HigherDimLQGMetric

/-- Lemma 2.2′(iv): bounded inner-coordinate distances with moving endpoints
yield an outer-coordinate curve in the compact closure of the inner domain. -/
theorem lemma22iv
    {X : Type*} [MetricSpace X] (V : Set X)
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (τ : ℕ → V × V → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n))
    (hτ : ∀ n, IsLengthCoordinate (τ n))
    (hL : IsCompact (closure V))
    (hconv : TendstoUniformlyOn ρ ρlim atTop (closure V ×ˢ closure V))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ u ∈ closure V, ∀ v ∈ closure V,
        ρ n (u, v) < δ → dist u v < ε)
    (hlen : ∀ n, ∀ P : I →ᵇ V,
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one (fun t : I => (P t : X))) 0 1 =
      curveLengthWith (fun u v => ENNReal.ofReal (τ n (u, v)))
        (Set.IccExtend zero_le_one P) 0 1)
    (xseq yseq : ℕ → V) (x y : X)
    (hxlim : Tendsto (fun n => (xseq n : X)) atTop (𝓝 x))
    (hylim : Tendsto (fun n => (yseq n : X)) atTop (𝓝 y))
    (A : ℝ) (hbound : ∀ n, τ n (xseq n, yseq n) ≤ A) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ closure V) ∧ Q 0 = x ∧ Q 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal A := by
  have hA : 0 ≤ A := by
    have hnonneg : 0 ≤ τ 0 (xseq 0, yseq 0) := by
      change 0 ≤ dist (MetricFunSpace.pt (τ 0) (hτ 0).metric (xseq 0))
        (MetricFunSpace.pt (τ 0) (hτ 0).metric (yseq 0))
      exact dist_nonneg
    exact hnonneg.trans (hbound 0)
  let a : ℝ := 4 * (A + 2)
  have ha : 0 < a := by dsimp [a]; linarith
  let ε : ℕ → ℝ := fun n => min (a / 4) (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : 0 < ε n := lt_min (by positivity) (by positivity)
  have hεa (n : ℕ) : ε n ≤ a / 4 := min_le_left _ _
  have hshort (n : ℕ) : τ n (xseq n, yseq n) < a / 4 := by
    dsimp [a]
    linarith [hbound n]
  choose γ hγlen hγlip hγV using fun n =>
    (hτ n).exists_short_path_in (O := (univ : Set V)) isOpen_univ
      (mem_univ _) ha (by simp) (hshort n) (hεpos n) (hεa n)
  let Pv : ℕ → I →ᵇ V := fun n =>
    mkOfCompact ((γ n).map (hτ n).val_continuous).toContinuousMap
  let P : ℕ → I →ᵇ X := fun n =>
    mkOfCompact ⟨fun t => (Pv n t : X), continuous_subtype_val.comp (Pv n).continuous⟩
  have hPL : ∀ n t, P n t ∈ closure V := fun n t => subset_closure (Pv n t).property
  have hρres (n : ℕ) : IsMetricFun
      (fun p : V × V => ρ n (p.1.1, p.2.1)) :=
    HigherDimLQGMetric.IsMetricFun.restrictTo (hρ n).metric V
  have hlenV (n : ℕ) (R : I →ᵇ V) :
      curveLengthWith (fun p q : V => ENNReal.ofReal (ρ n (p.1, q.1)))
        (Set.IccExtend zero_le_one R) 0 1 =
      curveLengthWith (fun p q => ENNReal.ofReal (τ n (p, q)))
        (Set.IccExtend zero_le_one R) 0 1 := by
    convert hlen n R using 1
    rfl
  have hdom (n : ℕ) (p q : V) : ρ n (p.1, q.1) ≤ τ n (p, q) :=
    coordinate_le_internal_coordinate (hρres n) (hτ n) (hlenV n) p q
  have hspeed : ∀ n : ℕ, ∀ s t : I,
      ρ n (P n s, P n t) ≤ a * dist s t := by
    intro n s t
    have hτlip := (hγlip n).dist_le_mul s t
    change τ n (Pv n s, Pv n t) ≤ (Real.toNNReal a : ℝ) * dist s t at hτlip
    have hτlip' : τ n (Pv n s, Pv n t) ≤ a * dist s t := by
      simpa [Real.coe_toNNReal', max_eq_left ha.le] using hτlip
    exact (hdom n (Pv n s) (Pv n t)).trans hτlip'
  obtain ⟨Q, hQL, φ, hφ, hPconv, _, hQlen, _⟩ :=
    lemmaCC zero_le_one hL ρ ρlim
      (fun n => (hρ n).continuous.continuousOn) hconv a P hPL hmod hspeed
  have hP0 (n : ℕ) : P n 0 = (xseq n : X) := by
    change ((LQGMetric.metricFunSpaceVal (τ n) (hτ n).metric (γ n 0) : V) : X) = _
    rw [(γ n).source]
    rfl
  have hP1 (n : ℕ) : P n 1 = (yseq n : X) := by
    change ((LQGMetric.metricFunSpaceVal (τ n) (hτ n).metric (γ n 1) : V) : X) = _
    rw [(γ n).target]
    rfl
  have hQ0 : Q 0 = x :=
    tendsto_nhds_unique (hPconv.tendsto_at 0)
      (by simpa only [Function.comp_def, hP0] using hxlim.comp hφ.tendsto_atTop)
  have hQ1 : Q 1 = y :=
    tendsto_nhds_unique (hPconv.tendsto_at 1)
      (by simpa only [Function.comp_def, hP1] using hylim.comp hφ.tendsto_atTop)
  have hPlen (n : ℕ) :
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one (P n)) 0 1 = pathLength (γ n) := by
    calc
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one (P n)) 0 1 =
        curveLengthWith (fun u v => ENNReal.ofReal (τ n (u, v)))
          (Set.IccExtend zero_le_one (Pv n)) 0 1 := by
            convert hlen n (Pv n) using 1
            rfl
      _ = pathLength (γ n) := by
        convert pathLength_eq_coordinateLength (hτ n).metric (γ n) using 1
        rfl
  have hεlim : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => min (a / 4) (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (min (a / 4) (0 : ℝ))) := tendsto_const_nhds.min h1
    simpa [ε, min_eq_right (by linarith : (0 : ℝ) ≤ a / 4)] using h2
  have hcostlim : Tendsto (fun n => ENNReal.ofReal (A + ε (φ n))) atTop
      (𝓝 (ENNReal.ofReal A)) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_const_nhds.add (hεlim.comp hφ.tendsto_atTop))
  have hcost (n : ℕ) :
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (φ n) (u, v)))
        (Set.IccExtend zero_le_one (P (φ n))) 0 1 ≤
      ENNReal.ofReal (A + ε (φ n)) := by
    rw [hPlen]
    exact (hγlen (φ n)).trans (ENNReal.ofReal_le_ofReal
      (by simpa [add_comm] using add_le_add_right (hbound (φ n)) (ε (φ n))))
  refine ⟨Q, hQL, hQ0, hQ1, ?_⟩
  calc
    curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
        (Set.IccExtend zero_le_one Q) 0 1
        ≤ liminf (fun n => curveLengthWith
            (fun u v => ENNReal.ofReal (ρ (φ n) (u, v)))
            (Set.IccExtend zero_le_one (P (φ n))) 0 1) atTop :=
          hQlen le_rfl zero_le_one le_rfl
    _ ≤ liminf (fun n => ENNReal.ofReal (A + ε (φ n))) atTop :=
          Filter.liminf_le_liminf (Eventually.of_forall hcost)
    _ = ENNReal.ofReal A := hcostlim.liminf_eq

end HigherDimLQGMetric
