import SupercriticalLFPPAS.Separating.CrossingRecursion
import SupercriticalLFPPAS.Compare.ScaleRatio
import SupercriticalLQGUniqueness.B2.Polylog.P4Local

/-!
# Lemma 3.5: one-annulus consequences, separator extraction, lattice and scales

Deterministic ingredients of Lemma 3.5 (packet P35; planning audit SB2, Details D3):

* `p35_plEventLoc_bounds`: on the field-local one-annulus event `B2.Polylog.plEventLoc` of
  [2, Lemma 3.1] (both metrics, across `Ā_{ρ,2ρ}(w)`, around `A_{2ρ,3ρ}(w)`), with the strong
  metric's scale `ρ^{ξQ}` and the localized LFPP scale `ρ 𝔞_{ε/ρ}/𝔞_ε`, the around cost of each
  metric is at most `C²` times its own across cost, and at most `C² κ_ε(ρ)^{±1}` times the across
  cost of the other metric (`κ = Compare.kappa`, (2.5));
* `p35_exists_separator_of_aroundDist_lt`: a separating curve of length below any strict upper
  bound for the around cost, with its compact trace and the component bounds;
* `p35_disconnects_of_component`: the separator disconnects an inner ball from the exterior of an
  outer ball;
* the lattice `p35Lattice K a` of mesh `a` near a set `K`, with a nearest point and a cardinality
  bound;
* the scale ladder `s_k = 4η 16^{N-k}`, `N = ⌊log(1/η) / (2 log 16)⌋`, with `16^N ≤ η^{-1/2}`.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn plEventLoc plLocMetric normD normL annAround
  lfppScaleFactor lfppScaleFactor_pos)
open LQGMetric (DistC)

/-! ### Normalized one-annulus bounds -/

/-- From normalized upper and lower bounds with two (positive) normalizations, the around cost is at
most `C² β/α` times the across cost. -/
theorem p35_le_mul_of_norms {α β C : ℝ} (hα : 0 < α) (hβ : 0 < β) (hC : 0 < C) {W Y : ℝ≥0∞}
    (hW : ENNReal.ofReal α * W ≤ ENNReal.ofReal C)
    (hY : ENNReal.ofReal C⁻¹ ≤ ENNReal.ofReal β * Y) :
    W ≤ ENNReal.ofReal (C ^ 2 * (β / α)) * Y := by
  have hα0 : ENNReal.ofReal α ≠ 0 := by simpa using hα
  have hβ0 : ENNReal.ofReal β ≠ 0 := by simpa using hβ
  have hW' : W ≤ ENNReal.ofReal (C / α) := by
    have hEq : W = (ENNReal.ofReal α)⁻¹ * (ENNReal.ofReal α * W) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hα0 ENNReal.ofReal_ne_top, one_mul]
    rw [hEq, ENNReal.ofReal_div_of_pos hα, div_eq_mul_inv, mul_comm (ENNReal.ofReal C)]
    exact mul_le_mul_right hW _
  have hY' : ENNReal.ofReal (C⁻¹ / β) ≤ Y := by
    have hEq : Y = (ENNReal.ofReal β)⁻¹ * (ENNReal.ofReal β * Y) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hβ0 ENNReal.ofReal_ne_top, one_mul]
    rw [hEq, ENNReal.ofReal_div_of_pos hβ, div_eq_mul_inv, mul_comm (ENNReal.ofReal C⁻¹)]
    exact mul_le_mul_right hY _
  have hsplit : ENNReal.ofReal (C / α) =
      ENNReal.ofReal (C ^ 2 * (β / α)) * ENNReal.ofReal (C⁻¹ / β) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc W ≤ ENNReal.ofReal (C / α) := hW'
    _ = ENNReal.ofReal (C ^ 2 * (β / α)) * ENNReal.ofReal (C⁻¹ / β) := hsplit
    _ ≤ ENNReal.ofReal (C ^ 2 * (β / α)) * Y := mul_le_mul_right hY' _

/-- The strong-metric normalization `ρ^{-ξQ} e^{-ξ g_ρ(w)}` as a real number. -/
def p35NormDReal (ξ Q : ℝ) (g : DistC) (w : ℂ) (ρ : Set.Ioi (0 : ℝ)) : ℝ :=
  ((ρ : ℝ) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * LQGMetric.circleAvg g ρ w))

/-- The localized LFPP normalization `(ρ 𝔞_{ε/ρ}/𝔞_ε)^{-1} e^{-ξ g_ρ(w)}` as a real number. -/
def p35NormLReal (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : Set.Ioi (0 : ℝ))
    (g : DistC) (w : ℂ) (ρ : Set.Ioi (0 : ℝ)) : ℝ :=
  (lfppScaleFactor m ε ρ)⁻¹ * Real.exp (-(ξ * LQGMetric.circleAvg g ρ w))

theorem p35NormDReal_pos (ξ Q : ℝ) (g : DistC) (w : ℂ) (ρ : Set.Ioi (0 : ℝ)) :
    0 < p35NormDReal ξ Q g w ρ := by
  unfold p35NormDReal
  have hρ : (0 : ℝ) < ρ := ρ.2
  have := Real.rpow_pos_of_pos hρ (ξ * Q)
  positivity

theorem p35NormLReal_pos (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : Set.Ioi (0 : ℝ))
    (g : DistC) (w : ℂ) (ρ : Set.Ioi (0 : ℝ)) : 0 < p35NormLReal ξ m ε g w ρ := by
  unfold p35NormLReal
  have := lfppScaleFactor_pos m ε ρ
  positivity

theorem p35_normD_powScale (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (g : DistC) (w : ℂ)
    (ρ : Set.Ioi (0 : ℝ)) :
    normD (ξ : ℝ) (Compare.powScale ξ Q) g w ρ = ENNReal.ofReal (p35NormDReal ξ Q g w ρ) := rfl

theorem p35_normL_eq (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : Set.Ioi (0 : ℝ))
    (g : DistC) (w : ℂ) (ρ : Set.Ioi (0 : ℝ)) :
    normL ξ m ε g w ρ = ENNReal.ofReal (p35NormLReal ξ m ε g w ρ) := rfl

/-- The ratio of the two normalizations is the scale ratio `κ_ε(ρ)` of (2.5). -/
theorem p35_normD_div_normL (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : Set.Ioi (0 : ℝ)) (g : DistC) (w : ℂ) (ρ : Set.Ioi (0 : ℝ)) :
    p35NormDReal ξ Q g w ρ / p35NormLReal ξ m ε g w ρ = Compare.kappa ξ Q m ε ρ := by
  unfold p35NormDReal p35NormLReal Compare.kappa lfppScaleFactor
  have hρ : (0 : ℝ) < ρ := ρ.2
  have hp := Real.rpow_pos_of_pos hρ ((ξ : ℝ) * Q)
  have hm1 := (m ε).2
  have hm2 := (m ⟨(ε : ℝ) / ρ, Set.mem_Ioi.mpr (div_pos ε.2 ρ.2)⟩).2
  simp only [Set.mem_Ioi] at hm1 hm2
  have he := Real.exp_pos (-((ξ : ℝ) * LQGMetric.circleAvg g ρ w))
  field_simp

theorem p35_kappa_pos (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε ρ : Set.Ioi (0 : ℝ)) : 0 < Compare.kappa ξ Q m ε ρ := by
  unfold Compare.kappa
  have hρ : (0 : ℝ) < ρ := ρ.2
  have hp := Real.rpow_pos_of_pos hρ ((ξ : ℝ) * Q)
  have hm1 := (m ε).2
  have hm2 := (m ⟨(ε : ℝ) / ρ, Set.mem_Ioi.mpr (div_pos ε.2 ρ.2)⟩).2
  simp only [Set.mem_Ioi] at hm1 hm2
  positivity

/-- **Deterministic content of the one-annulus event** `E^ε_ρ(w; C)` of [2, Lemma 3.1], for the
strong metric `D` with scale `ρ^{ξQ}` and the localized LFPP metric with polylogarithmic window parameter
`qp` (`qp = 1`: `X̂_ε`; `qp = uniformLocalizationExponent δ L`: `Y_{δ,L}`): each around
cost is at most `C²` times the across cost of the same metric, and the cross bounds carry
`κ_ε(ρ)` (target `X̂`) and `κ_ε(ρ)⁻¹` (target `D`). -/
theorem p35_plEventLoc_bounds (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (qp : ℝ) (w : ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (ρ : Set.Ioi (0 : ℝ)) {C : ℝ} (hC : 0 < C) {g : DistC}
    (hg : g ∈ plEventLoc (ξ : ℝ) D (Compare.powScale ξ Q) m qp w ε hε ρ C) :
    aroundDist (D g) (annAround w ρ) ≤ ENNReal.ofReal (C ^ 2) * acrossIn (D g) w ρ (2 * ρ) ∧
    aroundDist (plLocMetric (ξ : ℝ) qp m ε hε g) (annAround w ρ) ≤
      ENNReal.ofReal (C ^ 2) * acrossIn (plLocMetric (ξ : ℝ) qp m ε hε g) w ρ (2 * ρ) ∧
    aroundDist (plLocMetric (ξ : ℝ) qp m ε hε g) (annAround w ρ) ≤
      ENNReal.ofReal (C ^ 2 * Compare.kappa ξ Q m ⟨ε, hε.1⟩ ρ) * acrossIn (D g) w ρ (2 * ρ) ∧
    aroundDist (D g) (annAround w ρ) ≤
      ENNReal.ofReal (C ^ 2 * (Compare.kappa ξ Q m ⟨ε, hε.1⟩ ρ)⁻¹) *
        acrossIn (plLocMetric (ξ : ℝ) qp m ε hε g) w ρ (2 * ρ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  rw [p35_normD_powScale] at h1 h2
  rw [p35_normL_eq] at h3 h4
  set nD := p35NormDReal ξ Q g w ρ with hnD
  set nL := p35NormLReal (ξ : ℝ) m ⟨ε, hε.1⟩ g w ρ with hnL
  have hnDpos : 0 < nD := p35NormDReal_pos _ _ _ _ _
  have hnLpos : 0 < nL := p35NormLReal_pos _ _ _ _ _ _
  have hκ : nD / nL = Compare.kappa ξ Q m ⟨ε, hε.1⟩ ρ := p35_normD_div_normL ξ Q m _ g w ρ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := p35_le_mul_of_norms hnDpos hnDpos hC h2 h1
    rwa [div_self hnDpos.ne', mul_one] at h
  · have h := p35_le_mul_of_norms hnLpos hnLpos hC h4 h3
    rwa [div_self hnLpos.ne', mul_one] at h
  · have h := p35_le_mul_of_norms hnLpos hnDpos hC h4 h1
    rwa [hκ] at h
  · have h := p35_le_mul_of_norms hnDpos hnLpos hC h2 h3
    have hinv : nL / nD = (Compare.kappa ξ Q m ⟨ε, hε.1⟩ ρ)⁻¹ := by
      rw [← hκ, inv_div]
    rwa [hinv] at h

/-- A normalized upper bound with a positive normalization makes the around cost finite. -/
theorem p35_lt_top_of_norm_mul_le {α C : ℝ} (hα : 0 < α) {W : ℝ≥0∞}
    (hW : ENNReal.ofReal α * W ≤ ENNReal.ofReal C) : W < ⊤ := by
  have hα0 : ENNReal.ofReal α ≠ 0 := by simpa using hα
  have hEq : W = (ENNReal.ofReal α)⁻¹ * (ENNReal.ofReal α * W) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hα0 ENNReal.ofReal_ne_top, one_mul]
  rw [hEq]
  exact lt_of_le_of_lt (mul_le_mul_right hW _)
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by simpa using hα)) ENNReal.ofReal_lt_top)

/-- On the one-annulus event both around costs are finite. -/
theorem p35_plEventLoc_around_lt_top (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (qp : ℝ) (w : ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (ρ : Set.Ioi (0 : ℝ)) {C : ℝ} {g : DistC}
    (hg : g ∈ plEventLoc (ξ : ℝ) D (Compare.powScale ξ Q) m qp w ε hε ρ C) :
    aroundDist (D g) (annAround w ρ) < ⊤ ∧
    aroundDist (plLocMetric (ξ : ℝ) qp m ε hε g) (annAround w ρ) < ⊤ := by
  obtain ⟨_, h2, _, h4⟩ := hg
  rw [p35_normD_powScale] at h2
  rw [p35_normL_eq] at h4
  exact ⟨p35_lt_top_of_norm_mul_le (p35NormDReal_pos _ _ _ _ _) h2,
    p35_lt_top_of_norm_mul_le (p35NormLReal_pos _ _ _ _ _ _) h4⟩

/-- `annAround`, the separating annulus `A_{2ρ,3ρ}(w)` of the event, is the outer annulus of
Lemma 3.4′ at the same radius. -/
theorem p35_d1OuterAnnulus_eq_annAround (w : ℂ) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (j : ℕ) :
    d1OuterAnnulus w r hr j = annAround w ⟨r j, hr j⟩ := rfl

/-! ### Separators from around costs -/

/-- **A separating curve below any strict bound for the around cost**, with its compact trace in
the open annulus and the component bounds `B̄_{2r}(x) ⊆ U ⊆ B_{3r}(x)` for the component `U` of the
complement containing `x`. Adapted from `B2.Polylog.exists_paid_separator_in`. -/
theorem p35_exists_separator_of_aroundDist_lt (M : LSCMetric) (x : ℂ) {r : ℝ} (hr : 0 < r)
    {B : ℝ≥0∞} (hlt : aroundDist M (annAround x ⟨r, hr⟩) < B) :
    ∃ (Q : ℝ → ℂ) (a b : ℝ), M.IsCurve Q a b ∧ ContinuousOn Q (Icc a b) ∧
      Q '' Icc a b ⊆ {w | 2 * r < dist w x ∧ dist w x < 3 * r} ∧
      M.len Q a b < B ∧ IsCompact (Q '' Icc a b) ∧
      closedBall x (2 * r) ⊆ connectedComponentIn (Q '' Icc a b)ᶜ x ∧
      connectedComponentIn (Q '' Icc a b)ᶜ x ⊆ ball x (3 * r) := by
  dsimp only [aroundDist] at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp hlt
  obtain ⟨a, ha⟩ := iInf_lt_iff.mp hP
  obtain ⟨b, hb⟩ := iInf_lt_iff.mp ha
  obtain ⟨hcurve, hc⟩ := iInf_lt_iff.mp hb
  obtain ⟨hinside, hi⟩ := iInf_lt_iff.mp hc
  obtain ⟨hsep, hlen⟩ := iInf_lt_iff.mp hi
  have hAnn : P '' Icc a b ⊆ {w | 2 * r < dist w x ∧ dist w x < 3 * r} := by
    rintro y ⟨t, ht, rfl⟩
    exact Uniqueness.Toolkit.PlanarSeparation.candidate_annulus_subset_radii
      (annAround x ⟨r, hr⟩) (hinside t ht)
  have hball : P '' Icc a b ⊆ ball x (3 * r) := fun y hy => (hAnn hy).2
  have hPc : ContinuousOn P (Icc a b) :=
    Uniqueness.Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded M P hcurve
      (isBounded_ball.subset hball)
  have hcompact : IsCompact (P '' Icc a b) := isCompact_Icc.image_of_continuousOn hPc
  have hcert : LQGMetric.Disconnects (P '' Icc a b) (sphere x (2 * r)) (sphere x (3 * r)) :=
    Uniqueness.Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  obtain ⟨hinner, houter⟩ :=
    Uniqueness.Toolkit.PlanarSeparation.annular_component_bounds (by linarith : 0 < 2 * r)
      (by linarith : 2 * r < 3 * r) hcompact hAnn hcert
  exact ⟨P, a, b, hcurve, hPc, hAnn, hlen, hcompact, hinner, houter⟩

/-- A set whose complement-component containing `p` contains `B_ρ(p)` and lies in `B_R(p)`
disconnects `B_ρ(p)` from the exterior of `B_R(p)`. -/
theorem p35_disconnects_of_component {K : Set ℂ} {p : ℂ} {ρ R : ℝ}
    (hin : ball p ρ ⊆ connectedComponentIn Kᶜ p)
    (hout : connectedComponentIn Kᶜ p ⊆ ball p R) :
    SupercriticalLQGUniqueness.Disconnects K (ball p ρ) {x | R ≤ dist x p} := by
  rintro ⟨S, hS, hSK, ⟨x, hxS, hxB⟩, ⟨y, hyS, hyF⟩⟩
  have hxU : x ∈ connectedComponentIn Kᶜ p := hin hxB
  have hSU : S ⊆ connectedComponentIn Kᶜ p := by
    rw [connectedComponentIn_eq hxU]
    exact hS.subset_connectedComponentIn hxS hSK
  have hyB := hout (hSU hyS)
  rw [mem_ball] at hyB
  have hyF' : R ≤ dist y p := hyF
  linarith

/-! ### The lattice -/

/-- The point of the lattice `(a ℤ)²` obtained by rounding both coordinates of `p`. -/
def p35LatticePt (a : ℝ) (p : ℂ) : ℂ :=
  ((a * (round (p.re / a) : ℝ) : ℝ) : ℂ) + ((a * (round (p.im / a) : ℝ) : ℝ) : ℂ) * Complex.I

theorem p35_abs_sub_round_mul {a x : ℝ} (ha : 0 < a) : |x - a * (round (x / a) : ℝ)| ≤ a / 2 := by
  have h := abs_sub_round (x / a)
  have hx : x - a * (round (x / a) : ℝ) = a * (x / a - round (x / a)) := by
    field_simp
  rw [hx, abs_mul, abs_of_pos ha]
  nlinarith

/-- The rounded lattice point is within `a` of `p`. -/
theorem p35_dist_latticePt_le {a : ℝ} (ha : 0 < a) (p : ℂ) : dist p (p35LatticePt a p) ≤ a := by
  rw [dist_eq_norm]
  have hre : (p - p35LatticePt a p).re = p.re - a * (round (p.re / a) : ℝ) := by
    simp [p35LatticePt]
  have him : (p - p35LatticePt a p).im = p.im - a * (round (p.im / a) : ℝ) := by
    simp [p35LatticePt]
  calc ‖p - p35LatticePt a p‖ ≤ |(p - p35LatticePt a p).re| + |(p - p35LatticePt a p).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ a / 2 + a / 2 := by
        rw [hre, him]
        exact add_le_add (p35_abs_sub_round_mul ha) (p35_abs_sub_round_mul ha)
    _ = a := by ring

/-- The lattice box `{a(m + i n) : |m|, |n| ≤ N}`. -/
def p35LatticeBox (a : ℝ) (N : ℕ) : Finset ℂ :=
  ((Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(N : ℤ)) N)).image
    (fun z : ℤ × ℤ => ((a * (z.1 : ℝ) : ℝ) : ℂ) + ((a * (z.2 : ℝ) : ℝ) : ℂ) * Complex.I)

theorem p35_card_latticeBox_le (a : ℝ) (N : ℕ) : (p35LatticeBox a N).card ≤ (2 * N + 1) ^ 2 := by
  unfold p35LatticeBox
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Int.card_Icc, sq]
  have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [this]

theorem p35_round_mem_Icc {a x B : ℝ} (ha : 0 < a) (hx : |x| ≤ B) :
    round (x / a) ∈ Finset.Icc (-(⌈B / a⌉₊ : ℤ)) (⌈B / a⌉₊) := by
  rw [Finset.mem_Icc]
  have h1 := abs_sub_round (x / a)
  have hxa : |x / a| ≤ B / a := by
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right hx ha.le
  have hc : B / a ≤ (⌈B / a⌉₊ : ℝ) := Nat.le_ceil _
  have hr1 : ((round (x / a) : ℤ) : ℝ) ≤ (⌈B / a⌉₊ : ℝ) + 1 / 2 := by
    have := (abs_le.1 h1).1
    have := (abs_le.1 hxa).2
    linarith
  have hr2 : -((⌈B / a⌉₊ : ℝ) + 1 / 2) ≤ ((round (x / a) : ℤ) : ℝ) := by
    have := (abs_le.1 h1).2
    have := (abs_le.1 hxa).1
    linarith
  constructor
  · have : (-(⌈B / a⌉₊ : ℤ) : ℝ) - 1 < ((round (x / a) : ℤ) : ℝ) := by push_cast; linarith
    have : -(⌈B / a⌉₊ : ℤ) - 1 < round (x / a) := by exact_mod_cast this
    omega
  · have : ((round (x / a) : ℤ) : ℝ) < (⌈B / a⌉₊ : ℤ) + 1 := by push_cast; linarith
    have : round (x / a) < (⌈B / a⌉₊ : ℤ) + 1 := by exact_mod_cast this
    omega

/-- The rounded lattice point of a point of norm at most `B` lies in the box of size `⌈B/a⌉`. -/
theorem p35_latticePt_mem_box {a B : ℝ} (ha : 0 < a) {p : ℂ} (hp : ‖p‖ ≤ B) :
    p35LatticePt a p ∈ p35LatticeBox a ⌈B / a⌉₊ := by
  unfold p35LatticeBox p35LatticePt
  refine Finset.mem_image.2 ⟨(round (p.re / a), round (p.im / a)), ?_, rfl⟩
  rw [Finset.mem_product]
  exact ⟨p35_round_mem_Icc ha ((Complex.abs_re_le_norm p).trans hp),
    p35_round_mem_Icc ha ((Complex.abs_im_le_norm p).trans hp)⟩

open Classical in
/-- **The lattice of Lemma 3.5**: the points of `(a ℤ)²` within distance `a` of `K` (box of size
`⌈3/a⌉`, enough for `K ⊆ B̄_3(0)`). -/
def p35Lattice (K : Set ℂ) (a : ℝ) : Finset ℂ :=
  (p35LatticeBox a ⌈3 / a⌉₊).filter (fun c => ∃ k ∈ K, dist k c ≤ a)

theorem p35_latticePt_mem {K : Set ℂ} (hK : ∀ k ∈ K, ‖k‖ ≤ 3) {a : ℝ} (ha : 0 < a) {k : ℂ}
    (hk : k ∈ K) : p35LatticePt a k ∈ p35Lattice K a := by
  classical
  unfold p35Lattice
  rw [Finset.mem_filter]
  exact ⟨p35_latticePt_mem_box ha (hK k hk), k, hk, p35_dist_latticePt_le ha k⟩

theorem p35_mem_lattice_near {K : Set ℂ} {a : ℝ} {c : ℂ} (hc : c ∈ p35Lattice K a) :
    ∃ k ∈ K, dist k c ≤ a := by
  classical
  unfold p35Lattice at hc
  exact (Finset.mem_filter.1 hc).2

theorem p35_card_lattice_le (K : Set ℂ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ((p35Lattice K a).card : ℝ) ≤ 81 / a ^ 2 := by
  classical
  have h1 : (p35Lattice K a).card ≤ (2 * ⌈3 / a⌉₊ + 1) ^ 2 :=
    (Finset.card_filter_le _ _).trans (p35_card_latticeBox_le a _)
  have h2 : ((p35Lattice K a).card : ℝ) ≤ ((2 * ⌈3 / a⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h1
  have hceil : (⌈3 / a⌉₊ : ℝ) < 3 / a + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : ((2 * ⌈3 / a⌉₊ + 1 : ℕ) : ℝ) ≤ 9 / a := by
    push_cast
    have h1a : 1 ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith
    have : 3 / a = 3 * (1 / a) := by ring
    have : 9 / a = 9 * (1 / a) := by ring
    nlinarith
  have hnn : (0 : ℝ) ≤ ((2 * ⌈3 / a⌉₊ + 1 : ℕ) : ℝ) := by positivity
  calc ((p35Lattice K a).card : ℝ) ≤ ((2 * ⌈3 / a⌉₊ + 1 : ℕ) : ℝ) ^ 2 := h2
    _ ≤ (9 / a) ^ 2 := pow_le_pow_left₀ hnn h3 2
    _ = 81 / a ^ 2 := by ring

/-! ### The scale ladder -/

/-- The number of scales `N(η) = ⌊log(1/η) / (2 log 16)⌋`. -/
def p35ScaleCount (η : ℝ) : ℕ := ⌊Real.log η⁻¹ / (2 * Real.log 16)⌋₊

/-- The canonical scales `s_k = 4η 16^N / 16^k` (for `1 ≤ k ≤ N` they lie in `[4η, η^{1/2}/4]`). -/
def p35Scale (η : ℝ) (k : ℕ) : ℝ := 4 * η * 16 ^ p35ScaleCount η / 16 ^ k

theorem p35Scale_pos {η : ℝ} (hη : 0 < η) (k : ℕ) : 0 < p35Scale η k := by
  unfold p35Scale
  positivity

theorem p35Scale_succ (η : ℝ) (k : ℕ) : p35Scale η (k + 1) = p35Scale η k / 16 := by
  unfold p35Scale
  rw [pow_succ]
  field_simp

theorem log_sixteen_pos : 0 < Real.log 16 := Real.log_pos (by norm_num)

/-- `16^N ≤ η^{-1/2}`. -/
theorem p35_sixteen_pow_count_le {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    (16 : ℝ) ^ p35ScaleCount η ≤ Real.sqrt η⁻¹ := by
  have hl := log_sixteen_pos
  have hlog : 0 < Real.log η⁻¹ := Real.log_pos (one_lt_inv₀ hη |>.2 hη1)
  have hN : (p35ScaleCount η : ℝ) ≤ Real.log η⁻¹ / (2 * Real.log 16) :=
    Nat.floor_le (by positivity)
  have hexp : (16 : ℝ) ^ p35ScaleCount η = Real.exp ((p35ScaleCount η : ℝ) * Real.log 16) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have hsqrt : Real.sqrt η⁻¹ = Real.exp (Real.log η⁻¹ / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (inv_pos.2 hη)]
    ring_nf
  rw [hexp, hsqrt]
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_right hN hl.le
  calc (p35ScaleCount η : ℝ) * Real.log 16 ≤ Real.log η⁻¹ / (2 * Real.log 16) * Real.log 16 := this
    _ = Real.log η⁻¹ / 2 := by field_simp

/-- `N > log(1/η)/(2 log 16) - 1`. -/
theorem p35_count_gt {η : ℝ} :
    Real.log η⁻¹ / (2 * Real.log 16) - 1 < (p35ScaleCount η : ℝ) := by
  have := Nat.lt_floor_add_one (Real.log η⁻¹ / (2 * Real.log 16))
  unfold p35ScaleCount
  linarith

/-- The scales with `1 ≤ k ≤ N` are at least `4η`. -/
theorem p35Scale_ge {η : ℝ} (hη : 0 < η) {k : ℕ} (hk : k ≤ p35ScaleCount η) :
    4 * η ≤ p35Scale η k := by
  unfold p35Scale
  have h16 : (16 : ℝ) ^ k ≤ 16 ^ p35ScaleCount η := pow_le_pow_right₀ (by norm_num) hk
  have hpos : (0 : ℝ) < 16 ^ k := by positivity
  rw [le_div_iff₀ hpos]
  have : 0 ≤ 4 * η := by positivity
  nlinarith

/-- The scales with `k ≥ 1` are at most `η^{1/2}/4`. -/
theorem p35Scale_le {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {k : ℕ} (hk : 1 ≤ k) :
    p35Scale η k ≤ Real.sqrt η / 4 := by
  unfold p35Scale
  have h16 : (16 : ℝ) ≤ 16 ^ k := by
    calc (16 : ℝ) = 16 ^ 1 := (pow_one _).symm
      _ ≤ 16 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hN := p35_sixteen_pow_count_le hη hη1
  have hsq : Real.sqrt η⁻¹ * η = Real.sqrt η := by
    rw [Real.sqrt_inv]
    have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
    have hss : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη.le
    field_simp
    linarith [hss]
  have hpos : (0 : ℝ) < 16 ^ k := by positivity
  rw [div_le_iff₀ hpos]
  have h1 : 4 * η * 16 ^ p35ScaleCount η ≤ 4 * η * Real.sqrt η⁻¹ :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have h2 : 4 * η * Real.sqrt η⁻¹ = 4 * Real.sqrt η := by rw [mul_assoc, mul_comm η, hsq]
  have hs : 0 ≤ Real.sqrt η := Real.sqrt_nonneg η
  nlinarith

/-- Scales strictly decrease by the factor `16`. -/
theorem p35Scale_anti {η : ℝ} (hη : 0 < η) {j k : ℕ} (hjk : j < k) :
    p35Scale η k ≤ p35Scale η j / 16 := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [p35Scale_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | h
      · have := ih h
        have hpos := p35Scale_pos hη k
        have hposj := p35Scale_pos hη j
        linarith
      · rw [h]

end SupercriticalLFPPAS.Separating
