import SupercriticalLFPPAS.Separating.Geometry

/-!
# Lemma 3.5: the deterministic separating-path conclusion

Given good one-annulus events at a finite set of nested scales around a lattice point `w`, every
Euclidean-continuous geodesic segment through a point `p` near `w`, with endpoints far from `p`,
is surrounded by a short separating curve of the other metric (packet P35; planning audit SB2,
Details D3, steps 4–5). The probabilistic part (the scales are good with high probability) is in
`Separating/Lemma35.lean`, `Separating/Lemma35Canonical.lean` and `Separating/Lemma35Final.lean`.

* `p35_separator_core`: from the hypotheses of Lemma 3.4′ to a separating curve with explicit
  geometry (`B_ρ(p)` inside its complementary component, which lies in `B_R(p)`) and length bound
  `B (1 + 2/C)^{-(n-1)} len(I; d)`;
* `p35_decay_le`: `(1 + 2/C)^{-(n-1)} ≤ α² η^θ` with `θ = log(1 + 2/C)/(4 log 16)` when
  `n ≥ N(η)/2`;
* `p35_separator_of_goodFinset`: the conclusion of Lemma 3.5 at one lattice point, for both
  directions `(D, X̂_ε)` and `(X̂_ε, D)`, from the good one-annulus events (`plEventLoc`) at a set of
  at least `N(η)/2` scales and the scale-ratio bound (2.6).
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn plEventLoc plLocMetric annAround)
open LQGMetric (DistC)

/-- A curve on `[α, β]` through `p` whose starting point is at positive distance from `p` has
positive length. -/
theorem p35_len_pos_of_far (d : LSCMetric) {P : ℝ → ℂ} {α β : ℝ} {p : ℂ}
    (hp : p ∈ P '' Icc α β) (hα : P α ≠ p) (hαβ : α ≤ β) : 0 < d.len P α β := by
  obtain ⟨t, ht, rfl⟩ := hp
  have hle : d (P α, P t) ≤ d.len P α β := by
    have h := eVariationOn.edist_le (d.pt ∘ P) (s := Icc α β) ⟨le_rfl, hαβ⟩ ht
    exact h
  have hpos : 0 < d (P α, P t) :=
    pos_iff_ne_zero.2 (fun h => hα (d.isExtMetric.2.1 _ _ h))
  exact lt_of_lt_of_le hpos hle

/-- **Core of Lemma 3.5.** Under the hypotheses of Lemma 3.4′ at the nested radii `ρ_0 > ⋯ >
ρ_{n-1}` around `w`, and for a point `p` with `ρ + |p - w| ≤ 2ρ_{n-1}`, `|p - w| ≤ ρ_{n-1}`,
`3ρ_0 + |p - w| ≤ R`, every Euclidean-continuous `d`-geodesic segment through `p` with endpoints
outside `B_R(p)` is surrounded by a `d'`-curve: its trace lies in `B_R(p)`, the component of the
complement of its trace containing `p` contains `B_ρ(p)` and lies in `B_R(p)`, and its length is at
most `B (1 + 2/C)^{-(n-1)} len(I; d)`. -/
theorem p35_separator_core (d d' : LSCMetric) (w p : ℂ) {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) {n : ℕ}
    (hn : 0 < n) (hstep : ∀ i, i + 1 < n → ρ (i + 1) < ρ i / 4) {C B : ℝ} (hC : 0 < C)
    (hB : 0 < B)
    (hW : ∀ i, i + 1 < n → aroundDist d (annAround w ⟨ρ i, hρ i⟩) ≤
      ENNReal.ofReal C * acrossIn d w (ρ i) (2 * ρ i))
    (hZ : aroundDist d' (annAround w ⟨ρ (n - 1), hρ (n - 1)⟩) ≤
      ENNReal.ofReal B * acrossIn d w (ρ (n - 1)) (2 * ρ (n - 1)))
    {ρin R : ℝ} (hin : ρin + dist p w ≤ 2 * ρ (n - 1)) (hvis : dist p w ≤ ρ (n - 1))
    (hout : 3 * ρ 0 + dist p w ≤ R)
    {P : ℝ → ℂ} {α β : ℝ} (hgeoc : LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) α β)
    (hPc : ContinuousOn P (Icc α β))
    (hZfin : aroundDist d' (annAround w ⟨ρ (n - 1), hρ (n - 1)⟩) < ⊤) (hp : p ∈ P '' Icc α β)
    (hfarα : R ≤ dist (P α) p) (hfarβ : R ≤ dist (P β) p) :
    ∃ (σ : ℝ → ℂ) (a b : ℝ), d'.IsCurve σ a b ∧ ContinuousOn σ (Icc a b) ∧
      σ '' Icc a b ⊆ ball p R ∧
      ball p ρin ⊆ connectedComponentIn (σ '' Icc a b)ᶜ p ∧
      connectedComponentIn (σ '' Icc a b)ᶜ p ⊆ ball p R ∧
      d'.len σ a b ≤ ENNReal.ofReal (B / (1 + 2 / C) ^ (n - 1)) * d.len P α β := by
  have hP : d.IsCurve P α β := ⟨hgeoc.1, hgeoc.2.1⟩
  have hlast0 : ρ (n - 1) ≤ ρ 0 := d1_radius_le_prefix n ρ hρ hstep (by omega) (by omega)
  have hρn := hρ (n - 1)
  have hρ0 := hρ 0
  have hdpw : 0 ≤ dist p w := dist_nonneg
  have hRpos : 0 < R := by linarith
  -- endpoints of the segment lie outside `B_{3ρ₀}(w)`
  have hfar : ∀ x : ℂ, R ≤ dist x p → 3 * ρ 0 ≤ dist x w := by
    intro x hx
    have := dist_triangle x w p
    rw [dist_comm w p] at this
    linarith
  obtain ⟨t₀, ht₀, hPt₀⟩ := hp
  have hvisit : ∃ q ∈ Icc α β, dist (P q) w ≤ ρ (n - 1) := ⟨t₀, ht₀, by rw [hPt₀]; exact hvis⟩
  have hαβ : α ≤ β := hP.1
  have hcoef : 0 < B / (1 + 2 / C) ^ (n - 1) := by positivity
  -- a strict upper bound for the around cost, dominated by the claimed length bound
  obtain ⟨Bnd, hlt, hBnd⟩ : ∃ Bnd : ℝ≥0∞, aroundDist d' (annAround w ⟨ρ (n - 1), hρn⟩) < Bnd ∧
      Bnd ≤ ENNReal.ofReal (B / (1 + 2 / C) ^ (n - 1)) * d.len P α β := by
    by_cases hlenTop : d.len P α β = ⊤
    · refine ⟨aroundDist d' (annAround w ⟨ρ (n - 1), hρn⟩) + 1,
        ENNReal.lt_add_right hZfin.ne one_ne_zero, ?_⟩
      rw [hlenTop, ENNReal.mul_top (by simpa using hcoef)]
      exact le_top
    have hlen : d.len P α β < ⊤ := lt_top_iff_ne_top.2 hlenTop
    -- the geodesic property on subintervals
    have hgeo : ∀ u v : ℝ, u ∈ Icc α β → v ∈ Icc α β → u ≤ v → d.len P u v = d (P u, P v) := by
      intro u v hu hv huv
      have hfin : edist (d.pt (P α)) (d.pt (P β)) ≠ ⊤ := by
        have h1 : d.len P α β = edist (d.pt (P α)) (d.pt (P β)) := hgeoc.2.2
        rw [← h1]
        exact hlenTop
      exact LQGMetric.MetricGeometry.curveLength_eq_edist_of_subinterval hgeoc.2.2 hfin hu.1 huv
        hv.2
    -- Lemma 3.4′
    have hZbound := p35_lemma_3_4_in d d' w n hn C B hC hB ρ hρ hstep
      (fun i hi => by rw [p35_d1OuterAnnulus_eq_annAround]; exact hW i hi)
      (by rw [p35_d1OuterAnnulus_eq_annAround]; exact hZ)
      hP hPc hgeo hlen (hfar _ hfarα) (hfar _ hfarβ) hvisit
    rw [p35_d1OuterAnnulus_eq_annAround] at hZbound
    -- the bound is positive and finite
    have hPα : P α ≠ p := by
      intro hEq
      rw [hEq, dist_self] at hfarα
      linarith
    have hlenpos : 0 < d.len P α β := p35_len_pos_of_far d ⟨t₀, ht₀, hPt₀⟩ hPα hαβ
    set κs : ℝ := B / (2 * (1 + 2 / C) ^ (n - 1)) with hκs
    have hκspos : 0 < κs := by rw [hκs]; positivity
    set X : ℝ≥0∞ := ENNReal.ofReal κs * d.len P α β with hX
    have hXpos : 0 < X := ENNReal.mul_pos (by simpa using hκspos) hlenpos.ne'
    have hXtop : X < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlen
    refine ⟨2 * X, ?_, le_of_eq ?_⟩
    · refine lt_of_le_of_lt hZbound ?_
      have h2 : X * 1 < X * 2 := ENNReal.mul_lt_mul_right hXpos.ne' hXtop.ne (by norm_num)
      rw [mul_one, mul_comm] at h2
      exact h2
    · rw [hX, ← mul_assoc]
      congr 1
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num), hκs]
      congr 1
      field_simp
  obtain ⟨σ, a, b, hσ, hσc, hσann, hσlen, _hσcpt, hinner, houter⟩ :=
    p35_exists_separator_of_aroundDist_lt d' w hρn hlt
  -- the component of `p` is the component of `w`
  have hpw : p ∈ closedBall w (2 * ρ (n - 1)) := by
    rw [mem_closedBall]
    linarith
  have hpU : p ∈ connectedComponentIn (σ '' Icc a b)ᶜ w := hinner hpw
  have hUeq : connectedComponentIn (σ '' Icc a b)ᶜ w = connectedComponentIn (σ '' Icc a b)ᶜ p :=
    connectedComponentIn_eq hpU
  have hball_out : ball w (3 * ρ (n - 1)) ⊆ ball p R := by
    intro y hy
    rw [mem_ball] at hy ⊢
    have := dist_triangle y w p
    rw [dist_comm w p] at this
    linarith
  refine ⟨σ, a, b, hσ, hσc, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hball_out (by rw [mem_ball]; exact (hσann hy).2)
  · intro y hy
    rw [← hUeq]
    apply hinner
    rw [mem_closedBall]
    rw [mem_ball] at hy
    have := dist_triangle y p w
    linarith
  · rw [← hUeq]
    exact houter.trans hball_out
  · exact hσlen.le.trans hBnd

/-- Decay of the geometric factor: if `n ≥ N(η)/2`, then
`(1 + 2/C)^{-(n-1)} ≤ (1 + 2/C)² η^θ` with `θ = log(1 + 2/C)/(4 log 16)`. -/
theorem p35_decay_le {A η : ℝ} (hA : 1 < A) (hη : 0 < η) (hη1 : η < 1) {n : ℕ} (hn : 0 < n)
    (hnN : (p35ScaleCount η : ℝ) / 2 ≤ n) :
    1 / A ^ (n - 1) ≤ A ^ 2 * η ^ (Real.log A / (4 * Real.log 16)) := by
  have hl := log_sixteen_pos
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hApos : 0 < A := lt_trans zero_lt_one hA
  have hcount := p35_count_gt (η := η)
  set x : ℝ := Real.log η⁻¹ / (4 * Real.log 16) with hx
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  -- `n - 1 ≥ x - 2`
  have hexp : x - 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hn1, hx]
    have : Real.log η⁻¹ / (4 * Real.log 16) = (Real.log η⁻¹ / (2 * Real.log 16)) / 2 := by
      field_simp
      ring
    rw [this]
    linarith
  have hpowle : A ^ (x - 2) ≤ A ^ (n - 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hA.le hexp
  have hsplit : A ^ (x - 2) = A ^ x * (A ^ 2)⁻¹ := by
    rw [Real.rpow_sub hApos, Real.rpow_two]
    ring
  have hAx : A ^ x = (η ^ (Real.log A / (4 * Real.log 16)))⁻¹ := by
    rw [← Real.rpow_neg hη.le, Real.rpow_def_of_pos hApos, Real.rpow_def_of_pos hη, hx,
      Real.log_inv]
    congr 1
    ring
  have hηθ : 0 < η ^ (Real.log A / (4 * Real.log 16)) := Real.rpow_pos_of_pos hη _
  have hlow : (η ^ (Real.log A / (4 * Real.log 16)))⁻¹ * (A ^ 2)⁻¹ ≤ A ^ (n - 1) := by
    rw [← hAx, ← hsplit]
    exact hpowle
  have hpos : 0 < A ^ (n - 1) := pow_pos hApos _
  rw [div_le_iff₀ hpos]
  have hA2 : 0 < A ^ 2 := by positivity
  calc (1 : ℝ) = (A ^ 2 * η ^ (Real.log A / (4 * Real.log 16))) *
        ((η ^ (Real.log A / (4 * Real.log 16)))⁻¹ * (A ^ 2)⁻¹) := by
          field_simp
    _ ≤ (A ^ 2 * η ^ (Real.log A / (4 * Real.log 16))) * A ^ (n - 1) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-! ### The conclusion shape of Lemma 3.5 -/

/-- `P` on `[α, β]` is a Euclidean-continuous `d`-geodesic segment (length equal to the distance of
its endpoints, possibly infinite) through `p` whose endpoints lie outside `B_R(p)` (the segments `I`
of Lemma 3.5). -/
def P35GeodesicThrough (d : LSCMetric) (P : ℝ → ℂ) (α β : ℝ) (p : ℂ) (R : ℝ) : Prop :=
  LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) α β ∧ ContinuousOn P (Icc α β) ∧
    p ∈ P '' Icc α β ∧ R ≤ dist (P α) p ∧ R ≤ dist (P β) p

/-- There is a Euclidean-continuous `d'`-curve whose trace lies in `B_R(p)`, whose complementary
component containing `p` contains `B_ρ(p)` and lies in `B_R(p)` (so the trace disconnects `B_ρ(p)`
from `∞`), and whose `d'`-length is at most `ℓ` (the separating paths of Lemma 3.5). -/
def P35SeparatingCurve (d' : LSCMetric) (p : ℂ) (ρ R : ℝ) (ℓ : ℝ≥0∞) : Prop :=
  ∃ (σ : ℝ → ℂ) (a b : ℝ), d'.IsCurve σ a b ∧ ContinuousOn σ (Icc a b) ∧
    σ '' Icc a b ⊆ ball p R ∧ ball p ρ ⊆ connectedComponentIn (σ '' Icc a b)ᶜ p ∧
    connectedComponentIn (σ '' Icc a b)ᶜ p ⊆ ball p R ∧ d'.len σ a b ≤ ℓ

/-- A separating curve of `P35SeparatingCurve` disconnects `B_ρ(p)` from the exterior of `B_R(p)`
and its trace lies in `B_R(p)`; this is the form of the separator fields of
`Contraction.D4GoodScaleData` (with `R = r/10`). -/
theorem P35SeparatingCurve.disconnects {d' : LSCMetric} {p : ℂ} {ρ R R' : ℝ} {ℓ : ℝ≥0∞}
    (h : P35SeparatingCurve d' p ρ R ℓ) (hRR' : R ≤ R') :
    ∃ (σ : ℝ → ℂ) (a b : ℝ), d'.IsCurve σ a b ∧ ContinuousOn σ (Icc a b) ∧
      σ '' Icc a b ⊆ ball p R' ∧
      SupercriticalLQGUniqueness.Disconnects (σ '' Icc a b) (ball p ρ) {x | R' ≤ dist x p} ∧
      d'.len σ a b ≤ ℓ := by
  obtain ⟨σ, a, b, hσ, hσc, htr, hin, hout, hlen⟩ := h
  exact ⟨σ, a, b, hσ, hσc, htr.trans (ball_subset_ball hRR'),
    p35_disconnects_of_component hin (hout.trans (ball_subset_ball hRR')), hlen⟩

/-- The constant `C² C_κ (1 + 2/C²)²` of Lemma 3.5. -/
def p35Const (C Cκ : ℝ) : ℝ := C ^ 2 * Cκ * (1 + 2 / C ^ 2) ^ 2

/-- The exponent `θ = log(1 + 2/C²) / (4 log 16)` of Lemma 3.5. -/
def p35Theta (C : ℝ) : ℝ := Real.log (1 + 2 / C ^ 2) / (4 * Real.log 16)

theorem p35_one_lt_A {C : ℝ} (hC : 0 < C) : 1 < 1 + 2 / C ^ 2 := by
  have : 0 < 2 / C ^ 2 := by positivity
  linarith

theorem p35Theta_pos {C : ℝ} (hC : 0 < C) : 0 < p35Theta C := by
  unfold p35Theta
  have hl := log_sixteen_pos
  exact div_pos (Real.log_pos (p35_one_lt_A hC)) (by positivity)

theorem p35Const_pos {C Cκ : ℝ} (hC : 0 < C) (hCκ : 0 < Cκ) : 0 < p35Const C Cκ := by
  unfold p35Const
  positivity

/-- The increasing enumeration of a finite set of naturals (extended by `0`). -/
def p35Enum (G : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < G.card then G.orderEmbOfFin rfl ⟨i, h⟩ else 0

theorem p35Enum_mem {G : Finset ℕ} {i : ℕ} (hi : i < G.card) : p35Enum G i ∈ G := by
  simp only [p35Enum, hi, dite_true]
  exact Finset.orderEmbOfFin_mem G rfl _

theorem p35Enum_lt {G : Finset ℕ} {i j : ℕ} (hij : i < j) (hj : j < G.card) :
    p35Enum G i < p35Enum G j := by
  simp only [p35Enum, lt_trans hij hj, hj, dite_true]
  exact (G.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 hij)

/-- `dist (z + r k) (z + r c) = r · dist k c` for `r > 0`. -/
theorem p35_dist_affine (z k c : ℂ) {r : ℝ} (hr : 0 < r) :
    dist (z + (r : ℂ) * k) (z + (r : ℂ) * c) = r * dist k c := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hr.le]

/-- **Lemma 3.5 at one lattice point (deterministic).** Let `w = z + r c` be a lattice point and
`p = z + r k` with `|k - c| ≤ η/20`. Suppose that at every scale `r s_j` with `j` in a set `G` of at
least `N(η)/2` indices in `[1, N(η)]`, the field `g` lies in the one-annulus event `E^ε_{r s_j}(w; C)`
and the scale ratio satisfies `κ_ε(r s_j) ≤ C_κ κ_ε(r)` and `κ_ε(r s_j)⁻¹ ≤ C_κ κ_ε(r)⁻¹`. Then for
`(d, d', κ') = (D_g, X̂_ε, κ_ε(r))` and `(X̂_ε, D_g, κ_ε(r)⁻¹)`, every Euclidean-continuous
`d`-geodesic segment through `p` with endpoints outside `B_{2η^{1/2} r}(p)` is surrounded by a
`d'`-separating curve around `B_{ηr}(p)` inside `B_{2η^{1/2} r}(p)` of `d'`-length at most
`p35Const C C_κ · κ' · η^θ · len(I; d)`, `θ = p35Theta C`. -/
theorem p35_separator_of_goodFinset (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (qp : ℝ) (g : DistC) (z : ℂ) {r : ℝ} (hr : 0 < r) (ε : ℝ)
    (hε : ε ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {C Cκ : ℝ} (hC : 0 < C)
    (hCκ : 0 < Cκ) (c k : ℂ) (hck : dist k c ≤ η / 20) (G : Finset ℕ)
    (hG : G ⊆ Finset.Icc 1 (p35ScaleCount η)) (hGcard : (p35ScaleCount η : ℝ) / 2 ≤ G.card)
    (hG0 : 0 < G.card)
    (hgood : ∀ j ∈ G, g ∈ plEventLoc (ξ : ℝ) D (Compare.powScale ξ Q) m qp (z + (r : ℂ) * c) ε hε
      ⟨r * p35Scale η j, mul_pos hr (p35Scale_pos hη j)⟩ C)
    (hκ : ∀ j ∈ G,
      Compare.kappa ξ Q m ⟨ε, hε.1⟩ ⟨r * p35Scale η j, mul_pos hr (p35Scale_pos hη j)⟩ ≤
          Cκ * Compare.kappa ξ Q m ⟨ε, hε.1⟩ ⟨r, hr⟩ ∧
        (Compare.kappa ξ Q m ⟨ε, hε.1⟩ ⟨r * p35Scale η j, mul_pos hr (p35Scale_pos hη j)⟩)⁻¹ ≤
          Cκ * (Compare.kappa ξ Q m ⟨ε, hε.1⟩ ⟨r, hr⟩)⁻¹) :
    (∀ (P : ℝ → ℂ) (α β : ℝ),
      P35GeodesicThrough (D g) P α β (z + (r : ℂ) * k) (2 * Real.sqrt η * r) →
      P35SeparatingCurve (plLocMetric (ξ : ℝ) qp m ε hε g) (z + (r : ℂ) * k) (η * r)
        (2 * Real.sqrt η * r)
        (ENNReal.ofReal (p35Const C Cκ * Compare.kappa ξ Q m ⟨ε, hε.1⟩ ⟨r, hr⟩ *
          η ^ p35Theta C) * (D g).len P α β)) ∧
    (∀ (P : ℝ → ℂ) (α β : ℝ),
      P35GeodesicThrough (plLocMetric (ξ : ℝ) qp m ε hε g) P α β (z + (r : ℂ) * k)
        (2 * Real.sqrt η * r) →
      P35SeparatingCurve (D g) (z + (r : ℂ) * k) (η * r) (2 * Real.sqrt η * r)
        (ENNReal.ofReal (p35Const C Cκ * (Compare.kappa ξ Q m ⟨ε, hε.1⟩ ⟨r, hr⟩)⁻¹ *
          η ^ p35Theta C) * (plLocMetric (ξ : ℝ) qp m ε hε g).len P α β)) := by
  set n := G.card with hn
  set w : ℂ := z + (r : ℂ) * c with hw
  set p : ℂ := z + (r : ℂ) * k with hp
  set N := p35ScaleCount η with hN
  set κr := Compare.kappa ξ Q m ⟨ε, hε.1⟩ ⟨r, hr⟩ with hκr
  have hκrpos : 0 < κr := p35_kappa_pos ξ Q m _ _
  let ρ : ℕ → ℝ := fun i => r * p35Scale η (p35Enum G i)
  have hρ : ∀ i, 0 < ρ i := fun i => mul_pos hr (p35Scale_pos hη _)
  have hmemG : ∀ i, i < n → p35Enum G i ∈ G := fun i hi => p35Enum_mem hi
  have hrange : ∀ i, i < n → 1 ≤ p35Enum G i ∧ p35Enum G i ≤ N := by
    intro i hi
    have := hG (hmemG i hi)
    simpa [Finset.mem_Icc] using this
  have hstep : ∀ i, i + 1 < n → ρ (i + 1) < ρ i / 4 := by
    intro i hi
    have hlt := p35Enum_lt (G := G) (Nat.lt_succ_self i) hi
    have h16 := p35Scale_anti hη hlt
    have hpos := p35Scale_pos hη (p35Enum G i)
    show r * p35Scale η (p35Enum G (i + 1)) < r * p35Scale η (p35Enum G i) / 4
    have : p35Scale η (p35Enum G (i + 1)) < p35Scale η (p35Enum G i) / 4 := by linarith
    nlinarith
  -- geometry
  have hsqrt_pos : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hη_le_sqrt : η ≤ Real.sqrt η := by
    have h := Real.sqrt_le_sqrt hη1.le
    rw [Real.sqrt_one] at h
    have hss : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη.le
    nlinarith
  have hdpw : dist p w = r * dist k c := p35_dist_affine z k c hr
  have hdpw_le : dist p w ≤ r * (η / 20) := by
    rw [hdpw]
    exact mul_le_mul_of_nonneg_left hck hr.le
  have hρlast : 4 * η * r ≤ ρ (n - 1) := by
    have h := p35Scale_ge hη (hrange (n - 1) (by omega)).2
    show 4 * η * r ≤ r * p35Scale η (p35Enum G (n - 1))
    nlinarith
  have hρfirst : ρ 0 ≤ r * (Real.sqrt η / 4) := by
    have h := p35Scale_le hη hη1 (hrange 0 hG0).1
    exact mul_le_mul_of_nonneg_left h hr.le
  have hin : η * r + dist p w ≤ 2 * ρ (n - 1) := by nlinarith
  have hvis : dist p w ≤ ρ (n - 1) := by nlinarith
  have hout : 3 * ρ 0 + dist p w ≤ 2 * Real.sqrt η * r := by nlinarith
  -- the one-annulus bounds at the good scales
  have hbounds : ∀ i, i < n →
      let ρi : Set.Ioi (0 : ℝ) := ⟨ρ i, hρ i⟩
      aroundDist (D g) (annAround w ρi) ≤ ENNReal.ofReal (C ^ 2) * acrossIn (D g) w ρi (2 * ρi) ∧
      aroundDist (plLocMetric (ξ : ℝ) qp m ε hε g) (annAround w ρi) ≤
        ENNReal.ofReal (C ^ 2) * acrossIn (plLocMetric (ξ : ℝ) qp m ε hε g) w ρi (2 * ρi) ∧
      aroundDist (plLocMetric (ξ : ℝ) qp m ε hε g) (annAround w ρi) ≤
        ENNReal.ofReal (C ^ 2 * Compare.kappa ξ Q m ⟨ε, hε.1⟩ ρi) * acrossIn (D g) w ρi (2 * ρi) ∧
      aroundDist (D g) (annAround w ρi) ≤
        ENNReal.ofReal (C ^ 2 * (Compare.kappa ξ Q m ⟨ε, hε.1⟩ ρi)⁻¹) *
          acrossIn (plLocMetric (ξ : ℝ) qp m ε hε g) w ρi (2 * ρi) := by
    intro i hi
    exact p35_plEventLoc_bounds ξ Q D m qp w ε hε ⟨ρ i, hρ i⟩ hC (hgood _ (hmemG i hi))
  have hfin : ∀ i, i < n →
      aroundDist (D g) (annAround w ⟨ρ i, hρ i⟩) < ⊤ ∧
      aroundDist (plLocMetric (ξ : ℝ) qp m ε hε g) (annAround w ⟨ρ i, hρ i⟩) < ⊤ := by
    intro i hi
    exact p35_plEventLoc_around_lt_top ξ Q D m qp w ε hε ⟨ρ i, hρ i⟩ (hgood _ (hmemG i hi))
  have hκlast := hκ _ (hmemG (n - 1) (by omega))
  have hdecay := p35_decay_le (A := 1 + 2 / C ^ 2) (p35_one_lt_A hC) hη hη1 hG0 hGcard
  have hC2 : 0 < C ^ 2 := by positivity
  have hA : 0 < 1 + 2 / C ^ 2 := by positivity
  -- the final constant
  have hfinal : ∀ κ' : ℝ, 0 < κ' →
      ENNReal.ofReal (C ^ 2 * Cκ * κ' / (1 + 2 / C ^ 2) ^ (n - 1)) ≤
        ENNReal.ofReal (p35Const C Cκ * κ' * η ^ p35Theta C) := by
    intro κ' hκ'
    apply ENNReal.ofReal_le_ofReal
    unfold p35Const p35Theta
    have hpos : 0 ≤ C ^ 2 * Cκ * κ' := by positivity
    calc C ^ 2 * Cκ * κ' / (1 + 2 / C ^ 2) ^ (n - 1)
        = (C ^ 2 * Cκ * κ') * (1 / (1 + 2 / C ^ 2) ^ (n - 1)) := by ring
      _ ≤ (C ^ 2 * Cκ * κ') * ((1 + 2 / C ^ 2) ^ 2 *
            η ^ (Real.log (1 + 2 / C ^ 2) / (4 * Real.log 16))) :=
          mul_le_mul_of_nonneg_left hdecay hpos
      _ = C ^ 2 * Cκ * (1 + 2 / C ^ 2) ^ 2 * κ' *
            η ^ (Real.log (1 + 2 / C ^ 2) / (4 * Real.log 16)) := by ring
  constructor
  · -- source `D`, target `X̂`
    intro P α β hgeoP
    obtain ⟨hgeoc, hPc, hpP, hfα, hfβ⟩ := hgeoP
    have hBpos : 0 < C ^ 2 * Cκ * κr := by positivity
    obtain ⟨σ, a, b, hσ, hσc, htr, hcin, hcout, hσlen⟩ :=
      p35_separator_core (D g) (plLocMetric (ξ : ℝ) qp m ε hε g) w p hρ hG0 hstep hC2 hBpos
        (fun i hi => (hbounds i (by omega)).1)
        (by
          refine (hbounds (n - 1) (by omega)).2.2.1.trans
            (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hκlast.1 hC2.le)
        hin hvis hout hgeoc hPc (hfin (n - 1) (by omega)).2 hpP hfα hfβ
    exact ⟨σ, a, b, hσ, hσc, htr, hcin, hcout,
      hσlen.trans (mul_le_mul_left (hfinal κr hκrpos) _)⟩
  · -- source `X̂`, target `D`
    intro P α β hgeoP
    obtain ⟨hgeoc, hPc, hpP, hfα, hfβ⟩ := hgeoP
    have hκrinv : 0 < κr⁻¹ := inv_pos.2 hκrpos
    have hBpos : 0 < C ^ 2 * Cκ * κr⁻¹ := by positivity
    obtain ⟨σ, a, b, hσ, hσc, htr, hcin, hcout, hσlen⟩ :=
      p35_separator_core (plLocMetric (ξ : ℝ) qp m ε hε g) (D g) w p hρ hG0 hstep hC2 hBpos
        (fun i hi => (hbounds i (by omega)).2.1)
        (by
          refine (hbounds (n - 1) (by omega)).2.2.2.trans
            (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hκlast.2 hC2.le)
        hin hvis hout hgeoc hPc (hfin (n - 1) (by omega)).1 hpP hfα hfβ
    exact ⟨σ, a, b, hσ, hσc, htr, hcin, hcout,
      hσlen.trans (mul_le_mul_left (hfinal κr⁻¹ hκrinv) _)⟩

end SupercriticalLFPPAS.Separating
