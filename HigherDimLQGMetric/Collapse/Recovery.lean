import HigherDimLQGMetric.Collapse.Graph

/-!
# Recovery estimates for weighted collapse onto a compact set

The estimates here are the upper-bound half of Lemma 3.1. They use the exact path infimum
defining `internalEDist`, so they do not assume a graph geodesic exists.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- A short ambient realization costs at most its ambient length when the weight is at most one. -/
theorem weylDistOn_le_edist_of_realization {Y : Set X} {w : X → ℝ} {x y : X}
    (hreal : ∃ P : ℝ → X, ContinuousOn P (Icc 0 1) ∧
      P 0 = x ∧ P 1 = y ∧ MapsTo P (Icc 0 1) Y ∧
      curveLength P 0 1 = edist x y)
    (hw1 : ∀ z, w z ≤ 1) : weylDistOn w Y x y ≤ edist x y := by
  obtain ⟨P, hP, h0, h1, hY, hlen⟩ := hreal
  calc weylDistOn w Y x y ≤ weightedLength w P 0 1 := weylDistOn_le hP h0 h1 hY
    _ ≤ ENNReal.ofReal 1 * curveLength P 0 1 :=
      weightedLength_le_ofReal_mul_curveLength (fun t _ => hw1 (P t))
    _ = edist x y := by rw [hlen]; norm_num

/-- On the set where the weight is constant `λ`, its weighted internal distance is at most
`λ` times the original internal distance. -/
theorem weylDistOn_le_mul_internalEDist {Y K : Set X} (hKY : K ⊆ Y)
    {w : X → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hwK : ∀ z ∈ K, w z = lam) (u v : X) :
    weylDistOn w Y u v ≤ ENNReal.ofReal lam * internalEDist K u v := by
  have hlam0 : ENNReal.ofReal lam ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hlam)
  have hlamtop : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [internalEDist, ENNReal.mul_iInf_of_ne hlam0 hlamtop]
  apply le_iInf
  intro γ
  have hγY : ∀ t, γ.1 t ∈ Y := fun t => hKY (γ.2 t)
  have hP : ContinuousOn γ.1.extend (Icc 0 1) := γ.1.continuous_extend.continuousOn
  have hPK : MapsTo γ.1.extend (Icc 0 1) K := by
    intro t ht
    rw [Path.extend_apply γ.1 ht]
    exact γ.2 ⟨t, ht⟩
  calc weylDistOn w Y u v
      ≤ weightedLength w γ.1.extend 0 1 :=
        weylDistOn_le hP (Path.extend_zero γ.1) (Path.extend_one γ.1) (hPK.mono_right hKY)
    _ ≤ ENNReal.ofReal lam * curveLength γ.1.extend 0 1 :=
      weightedLength_le_ofReal_mul_curveLength
        (fun t ht => (hwK _ (hPK ht)).le)
    _ = ENNReal.ofReal lam * pathLength γ.1 := rfl

set_option maxHeartbeats 500000 in
/-- Recovery through two short access paths and a graph path. -/
theorem collapse_recovery_bound {Y K : Set X} (hKY : K ⊆ Y)
    {δ : ℝ} (hreal : ∀ p ∈ Y, ∀ q ∈ K, dist p q < δ →
      ∃ P : ℝ → X, ContinuousOn P (Icc 0 1) ∧
        P 0 = p ∧ P 1 = q ∧ MapsTo P (Icc 0 1) Y ∧
        curveLength P 0 1 = edist p q)
    {w : X → ℝ} (hw1 : ∀ z, w z ≤ 1) {lam eta : ℝ} (hlam : 0 < lam)
    (hwK : ∀ z ∈ K, w z = lam)
    {x y u v : X} (hx : x ∈ Y) (hy : y ∈ Y) (hu : u ∈ K) (hv : v ∈ K)
    (hxu : dist x u ≤ eta) (hyv : dist y v ≤ eta) (hetaδ : eta < δ) :
    weylDistOn w Y x y ≤
      ENNReal.ofReal eta + ENNReal.ofReal lam * internalEDist K u v +
        ENNReal.ofReal eta := by
  have hxu' : dist x u < δ := hxu.trans_lt hetaδ
  have hyv' : dist y v < δ := hyv.trans_lt hetaδ
  have h1 : weylDistOn w Y x u ≤ ENNReal.ofReal eta := by
    calc weylDistOn w Y x u ≤ edist x u :=
        weylDistOn_le_edist_of_realization (hreal x hx u hu hxu') hw1
      _ ≤ ENNReal.ofReal eta := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hxu
  have h2 : weylDistOn w Y v y ≤ ENNReal.ofReal eta := by
    rw [weylDistOn_comm]
    calc weylDistOn w Y y v ≤ edist y v :=
        weylDistOn_le_edist_of_realization (hreal y hy v hv hyv') hw1
      _ ≤ ENNReal.ofReal eta := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hyv
  have htri1 : weylDistOn w Y x y ≤ weylDistOn w Y x u + weylDistOn w Y u y :=
    weylDistOn_triangle x u y
  have htri2 : weylDistOn w Y u y ≤ weylDistOn w Y u v + weylDistOn w Y v y :=
    weylDistOn_triangle u v y
  have hmid : weylDistOn w Y u v ≤ ENNReal.ofReal lam * internalEDist K u v :=
    weylDistOn_le_mul_internalEDist hKY hlam hwK u v
  calc weylDistOn w Y x y
      ≤ weylDistOn w Y x u + weylDistOn w Y u y := htri1
    _ ≤ weylDistOn w Y x u + (weylDistOn w Y u v + weylDistOn w Y v y) :=
      add_le_add_right htri2 _
    _ = weylDistOn w Y x u + weylDistOn w Y u v + weylDistOn w Y v y := by
      rw [add_assoc]
    _ ≤ ENNReal.ofReal eta + ENNReal.ofReal lam * internalEDist K u v +
        ENNReal.ofReal eta := by
      exact add_le_add (add_le_add h1 hmid) h2

end HigherDimLQGMetric
