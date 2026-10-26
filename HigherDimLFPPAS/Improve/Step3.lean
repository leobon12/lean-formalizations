import HigherDimLFPPAS.Improve.Step2

/-! `setDistIn` approximation helpers use a positive ENNReal slack and take its limit explicitly. -/

/-!
# Proposition 4.1, Step 3: the replacement cost estimate
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Improve

open Set
open scoped ENNReal

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- Restrict and shift a unit-speed internal geodesic to any closed subinterval. -/
theorem d4InternalGeodesic_restrict (D : ContMetric d) {V : Set (Rd d)}
    {P : ℝ → Rd d} {T a b : ℝ}
    (hgeo : d4InternalGeodesic D V P T) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    d4InternalGeodesic D V (fun s => P (a + s)) (b - a) := by
  rcases hgeo with ⟨hT, hPc, hPV, hdist, hlen⟩
  have hspan : 0 ≤ b - a := sub_nonneg.mpr hab
  refine ⟨hspan, ?_, ?_, ?_, ?_⟩
  · have hφc : ContinuousOn (fun s : ℝ => a + s) (Icc 0 (b - a)) :=
      continuousOn_const.add continuousOn_id
    have hφmaps : MapsTo (fun s : ℝ => a + s) (Icc 0 (b - a)) (Icc 0 T) := by
      intro s hs
      constructor
      · linarith [hs.1]
      · linarith [hs.2]
    exact hPc.comp hφc hφmaps
  · intro s hs
    have hs' : a + s ∈ Icc 0 T := by
      constructor
      · linarith [hs.1]
      · linarith [hs.2]
    exact hPV hs'
  · intro s hs t ht
    have hs' : a + s ∈ Icc 0 T := by
      constructor
      · linarith [hs.1]
      · linarith [hs.2]
    have ht' : a + t ∈ Icc 0 T := by
      constructor
      · linarith [ht.1]
      · linarith [ht.2]
    change D.internal V (P (a + s)) (P (a + t)) = ENNReal.ofReal |t - s|
    calc
      D.internal V (P (a + s)) (P (a + t)) = ENNReal.ofReal |(a + t) - (a + s)| :=
        hdist (a + s) hs' (a + t) ht'
      _ = ENNReal.ofReal |t - s| := by congr 2 <;> ring
  · intro s hs t ht hst
    have hs' : a + s ∈ Icc 0 T := by
      constructor
      · linarith [hs.1]
      · linarith [hs.2]
    have ht' : a + t ∈ Icc 0 T := by
      constructor
      · linarith [ht.1]
      · linarith [ht.2]
    have hφc : ContinuousOn (fun u : ℝ => a + u) (Icc s t) :=
      continuousOn_const.add continuousOn_id
    have hφm : MonotoneOn (fun u : ℝ => a + u) (Icc s t) := by
      intro u hu v hv huv
      linarith
    have hcomp : (D.pt ∘ fun u : ℝ => P (a + u)) = (D.pt ∘ P) ∘ (fun u : ℝ => a + u) := rfl
    change curveLength (D.pt ∘ fun u : ℝ => P (a + u)) s t = ENNReal.ofReal (t - s)
    rw [hcomp, curveLength_comp_of_continuousOn_monotoneOn (D.pt ∘ P) hst hφc hφm]
    calc
      curveLength (D.pt ∘ P) (a + s) (a + t) = ENNReal.ofReal ((a + t) - (a + s)) :=
        hlen (a + s) hs' (a + t) ht' (by linarith)
      _ = ENNReal.ofReal (t - s) := by congr 1 <;> ring

/-- A finite set-to-set internal distance bound has an endpoint pair within any positive slack. -/
theorem d4_setDistIn_exists_pair_lt (D : ContMetric d) {V A B : Set (Rd d)} {K : ℝ≥0∞}
    (h : setDistIn D V A B < K) :
    ∃ x ∈ A, ∃ y ∈ B, D.internal V x y < K := by
  unfold setDistIn at h
  obtain ⟨x, h⟩ := iInf_lt_iff.mp h
  obtain ⟨hx, h⟩ := iInf_lt_iff.mp h
  obtain ⟨y, h⟩ := iInf_lt_iff.mp h
  obtain ⟨hy, hxy⟩ := iInf_lt_iff.mp h
  exact ⟨x, hx, y, hy, hxy⟩

/-- A singleton pair gives an upper bound for a set distance as soon as its endpoints belong to
the two sets. -/
theorem d4_setDistIn_le_pair (D : ContMetric d) {V A B : Set (Rd d)}
    {x y : Rd d} (hx : x ∈ A) (hy : y ∈ B) :
    setDistIn D V A B ≤ D.internal V x y := by
  unfold setDistIn
  exact (iInf₂_le x hx).trans (iInf₂_le y hy)

/-- Finiteness of an internal distance forces both endpoints into its domain. -/
theorem d4_internal_finite_mem {D : ContMetric d} {V : Set (Rd d)} {x y : Rd d}
    (hxy : D.internal V x y ≠ ⊤) : x ∈ V ∧ y ∈ V := by
  constructor
  · by_contra hx
    rw [D.internal_eq_top_of_notMem_left hx] at hxy
    exact hxy rfl
  · by_contra hy
    rw [D.internal_eq_top_of_notMem_right hy] at hxy
    exact hxy rfl

/-- Endpoint balls of radius `ρ` overlap when their centers are less than `2ρ` apart; the
midpoint lies in the required bounded output domain because that Euclidean ball is convex. -/
theorem d4_midpoint_setDistIn_zero (D : ContMetric d) {R ρ : ℝ} {x y : Rd d}
    (hR : 0 ≤ R) (hx : x ∈ Metric.ball 0 R) (hy : y ∈ Metric.ball 0 R)
    (hxy : dist x y < 2 * ρ) :
    setDistIn D (Metric.ball 0 (R + 2)) (Metric.ball x ρ) (Metric.ball y ρ) = 0 := by
  let z : Rd d := midpoint ℝ x y
  have hzR : z ∈ Metric.ball 0 R := by
    exact (convex_ball (0 : Rd d) R).midpoint_mem hx hy
  have hzx : dist z x = dist x y / 2 := by
    rw [dist_midpoint_left]
    norm_num [Real.norm_eq_abs]
    ring
  have hzy : dist z y = dist x y / 2 := by
    rw [dist_midpoint_right]
    norm_num [Real.norm_eq_abs]
    ring
  have hzV : z ∈ Metric.ball 0 (R + 2) := by
    rw [Metric.mem_ball] at hzR ⊢
    linarith
  have hza : z ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball]
    rw [hzx]
    linarith
  have hzb : z ∈ Metric.ball y ρ := by
    rw [Metric.mem_ball]
    rw [hzy]
    linarith
  apply le_antisymm
  · exact (d4_setDistIn_le_pair D hza hzb).trans (by
      rw [D.internal_self hzV])
  · exact bot_le

/-- Attach a fixed endpoint after an infimal set-distance estimate. The intermediate endpoint
is selected with slack; letting that slack decrease to zero yields the exact inequality. -/
theorem d4_setDistIn_attach_terminal (D : ContMetric d) {V A B : Set (Rd d)}
    {x : Rd d} {K E : ℝ≥0∞} (hset : setDistIn D V A B ≤ K) (hK : K ≠ ∞)
    (hconnect : ∀ y ∈ B, D.internal V y x ≤ E) :
    setDistIn D V A {x} ≤ K + E := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hlt : setDistIn D V A B < K + δ :=
    hset.trans_lt (ENNReal.lt_add_right hK (by simpa using hδ.ne'))
  obtain ⟨u, hu, v, hv, huv⟩ := d4_setDistIn_exists_pair_lt D hlt
  have hpair : D.internal V u x ≤ (K + E) + δ := by
    calc
      D.internal V u x ≤ D.internal V u v + D.internal V v x := D.internal_triangle V u v x
      _ ≤ (K + δ) + E := add_le_add huv.le (hconnect v hv)
      _ = (K + E) + δ := by ac_rfl
  have hsingleton : setDistIn D V A {x} ≤ D.internal V u x := by
    unfold setDistIn
    exact (iInf₂_le u hu).trans (iInf₂_le x (by simp))
  exact hsingleton.trans hpair

/-- Attach a fixed endpoint before an infimal set-distance estimate, again with an honest
positive-slack argument. -/
theorem d4_setDistIn_attach_initial (D : ContMetric d) {V A B : Set (Rd d)}
    {x : Rd d} {K E : ℝ≥0∞} (hset : setDistIn D V A B ≤ K) (hK : K ≠ ∞)
    (hconnect : ∀ u ∈ A, D.internal V x u ≤ E) :
    setDistIn D V {x} B ≤ E + K := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hlt : setDistIn D V A B < K + δ :=
    hset.trans_lt (ENNReal.lt_add_right hK (by simpa using hδ.ne'))
  obtain ⟨u, hu, v, hv, huv⟩ := d4_setDistIn_exists_pair_lt D hlt
  have hpair : D.internal V x v ≤ (E + K) + δ := by
    calc
      D.internal V x v ≤ D.internal V x u + D.internal V u v := D.internal_triangle V x u v
      _ ≤ E + (K + δ) := add_le_add (hconnect u hu) huv.le
      _ = (E + K) + δ := by ac_rfl
  have hsingleton : setDistIn D V {x} B ≤ D.internal V x v := by
    unfold setDistIn
    exact (iInf₂_le x (by simp)).trans (iInf₂_le v hv)
  exact hsingleton.trans hpair

/-- A finite chain of internal distances is bounded by the sum of its edge costs. -/
theorem d4_internal_chain (D : ContMetric d) {V : Set (Rd d)}
    (p : ℕ → Rd d) (w : ℕ → ℝ≥0∞) (n : ℕ)
    (hp : ∀ i ≤ n, p i ∈ V)
    (hedge : ∀ i < n, D.internal V (p i) (p (i + 1)) ≤ w i) :
    D.internal V (p 0) (p n) ≤ ∑ i ∈ Finset.range n, w i := by
  induction n with
  | zero =>
      simp only [Finset.sum_range_zero]
      simpa using D.internal_self (hp 0 le_rfl)
  | succ n ih =>
      have hprev := ih (fun i hi => hp i (by omega)) (fun i hi => hedge i (by omega))
      calc
        D.internal V (p 0) (p (n + 1)) ≤
            D.internal V (p 0) (p n) + D.internal V (p n) (p (n + 1)) :=
          D.internal_triangle V (p 0) (p n) (p (n + 1))
        _ ≤ (∑ i ∈ Finset.range n, w i) + w n :=
          add_le_add hprev (hedge n (by omega))
        _ = ∑ i ∈ Finset.range (n + 1), w i := by rw [Finset.sum_range_succ]

/-- The same finite-chain estimate viewed as a set distance between singleton endpoint sets. -/
theorem d4_setDistIn_chain (D : ContMetric d) {V : Set (Rd d)}
    (p : ℕ → Rd d) (w : ℕ → ℝ≥0∞) (n : ℕ)
    (hp : ∀ i ≤ n, p i ∈ V)
    (hedge : ∀ i < n, D.internal V (p i) (p (i + 1)) ≤ w i) :
    setDistIn D V {p 0} {p n} ≤ ∑ i ∈ Finset.range n, w i := by
  calc
    setDistIn D V {p 0} {p n} ≤ D.internal V (p 0) (p n) := by
      unfold setDistIn
      exact (iInf₂_le (p 0) (by simp)).trans (iInf₂_le (p n) (by simp))
    _ ≤ ∑ i ∈ Finset.range n, w i := d4_internal_chain D p w n hp hedge

/-- A chain with four edges per stage. This is the form used by the replacement construction:
comparison, a connector to the crossing, the crossing itself, and the connector to the next
comparison point. -/
theorem d4_internal_chain_four (D : ContMetric d) {V : Set (Rd d)}
    (a b c e : ℕ → Rd d) (w₁ w₂ w₃ w₄ : ℕ → ℝ≥0∞) (n : ℕ)
    (hp : ∀ i ≤ n, a i ∈ V)
    (hq : ∀ i < n, b i ∈ V ∧ c i ∈ V ∧ e i ∈ V ∧ a (i + 1) ∈ V)
    (h₁ : ∀ i < n, D.internal V (a i) (b i) ≤ w₁ i)
    (h₂ : ∀ i < n, D.internal V (b i) (c i) ≤ w₂ i)
    (h₃ : ∀ i < n, D.internal V (c i) (e i) ≤ w₃ i)
    (h₄ : ∀ i < n, D.internal V (e i) (a (i + 1)) ≤ w₄ i) :
    D.internal V (a 0) (a n) ≤
      ∑ i ∈ Finset.range n, (w₁ i + w₂ i + w₃ i + w₄ i) := by
  induction n with
  | zero =>
      simp only [Finset.sum_range_zero]
      simpa using D.internal_self (hp 0 le_rfl)
  | succ n ih =>
      have hprev := ih (fun i hi => hp i (by omega))
        (fun i hi => hq i (by omega)) (fun i hi => h₁ i (by omega))
        (fun i hi => h₂ i (by omega)) (fun i hi => h₃ i (by omega))
        (fun i hi => h₄ i (by omega))
      have hnq := hq n (by omega)
      rcases hnq with ⟨hbn, hcn, hen, han1⟩
      have hbe : D.internal V (b n) (a (n + 1)) ≤
          D.internal V (b n) (c n) +
            (D.internal V (c n) (e n) + D.internal V (e n) (a (n + 1))) := by
        calc
          D.internal V (b n) (a (n + 1)) ≤
              D.internal V (b n) (c n) + D.internal V (c n) (a (n + 1)) :=
            D.internal_triangle V (b n) (c n) (a (n + 1))
          _ ≤ D.internal V (b n) (c n) +
                (D.internal V (c n) (e n) + D.internal V (e n) (a (n + 1))) :=
            add_le_add le_rfl (D.internal_triangle V (c n) (e n) (a (n + 1)))
      have hlocal : D.internal V (a n) (a (n + 1)) ≤
          w₁ n + w₂ n + w₃ n + w₄ n := by
        calc
          D.internal V (a n) (a (n + 1)) ≤
              D.internal V (a n) (b n) + D.internal V (b n) (a (n + 1)) :=
            D.internal_triangle V (a n) (b n) (a (n + 1))
          _ ≤ w₁ n + (D.internal V (b n) (c n) +
                (D.internal V (c n) (e n) + D.internal V (e n) (a (n + 1)))) := by
            exact add_le_add (h₁ n (by omega)) hbe
          _ ≤ w₁ n + (w₂ n + (w₃ n + w₄ n)) := by
            gcongr
            · exact h₂ n (by omega)
            · exact h₃ n (by omega)
            · exact h₄ n (by omega)
          _ = w₁ n + w₂ n + w₃ n + w₄ n := by ac_rfl
      calc
        D.internal V (a 0) (a (n + 1)) ≤
            D.internal V (a 0) (a n) + D.internal V (a n) (a (n + 1)) :=
          D.internal_triangle V (a 0) (a n) (a (n + 1))
        _ ≤ (∑ i ∈ Finset.range n, (w₁ i + w₂ i + w₃ i + w₄ i)) +
              (w₁ n + w₂ n + w₃ n + w₄ n) := add_le_add hprev hlocal
        _ = ∑ i ∈ Finset.range (n + 1), (w₁ i + w₂ i + w₃ i + w₄ i) := by
          rw [Finset.sum_range_succ]

/-- The algebraic estimate (4.6). Replacing `C` by `max C m` makes the coefficient of the
gap contribution nonnegative, so the contraction bound for `B` applies. -/
theorem d4_step3_cost_bound {C m η θ B G : ℝ}
    (hm : 0 ≤ m) (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hfrac : B ≤ θ * (B + G)) :
    C * B + m * G + 3 * η * m * G ≤
      (θ * max C m + (1 - θ + 3 * η) * m) * (B + G) := by
  let C' : ℝ := max C m
  have hCm : m ≤ C' := by dsimp [C']; exact le_max_right C m
  have hCC' : C ≤ C' := by dsimp [C']; exact le_max_left C m
  have hC'm : 0 ≤ C' - m := sub_nonneg.mpr hCm
  have h3ηm : 0 ≤ 3 * η * m := by positivity
  calc
    C * B + m * G + 3 * η * m * G ≤ C' * B + m * G + 3 * η * m * G := by
      have hCB : C * B ≤ C' * B := mul_le_mul_of_nonneg_right hCC' hB
      nlinarith [hCB]
    _ = m * (B + G) + (C' - m) * B + 3 * η * m * G := by ring
    _ ≤ m * (B + G) + (C' - m) * (θ * (B + G)) +
          (3 * η * m) * (B + G) := by
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac hC'm)
      · exact mul_le_mul_of_nonneg_left (by linarith : G ≤ B + G) h3ηm
    _ = (θ * C' + (1 - θ + 3 * η) * m) * (B + G) := by ring

end HigherDimLFPPAS.Improve

end
