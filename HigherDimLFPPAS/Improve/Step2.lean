import HigherDimLFPPAS.Improve.Defs
import Mathlib.Tactic.Linarith

/-!
# Proposition 4.1, Step 2: the old-cost fraction
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Improve

open Set Filter Topology Metric
open scoped ENNReal

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The closed crossing annulus is contained in its buffered open neighborhood. -/
theorem d4F_subset_d4U {z : Rd d} {r : ℝ} (hr : 0 < r) :
    d4F z r ⊆ d4U z r := by
  intro x hx
  change 3 * r / 4 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ r at hx
  change r / 4 < ‖x - z‖ ∧ ‖x - z‖ < 2 * r
  constructor <;> linarith

/-- The buffered annulus stays in the old comparison domain when the mesh center is close to
the path inside `B_R` and the scale error satisfies (E2) of the MA2 audit. -/
theorem d4U_subset_ball_R1 {z : Rd d} {R r rmin rmax : ℝ}
    (hr : r ≤ rmax) (hz : dist z 0 < R + rmin / 100)
    (hscale : rmin / 100 + 2 * rmax < 1) :
    d4U z r ⊆ Metric.ball 0 (R + 1) := by
  intro x hx
  change r / 4 < ‖x - z‖ ∧ ‖x - z‖ < 2 * r at hx
  have htriangle := dist_triangle x z 0
  have hdistxz : dist x z = ‖x - z‖ := dist_eq_norm x z
  have hx0 : dist x 0 < R + rmin / 100 + 2 * rmax := by
    nlinarith [htriangle, hdistxz, hx.2, hz]
  have hbound : R + rmin / 100 + 2 * rmax < R + 1 := by linarith
  rw [Metric.mem_ball]
  exact hx0.trans hbound

/-- The good-annulus properties are invariant when the two metrics are exchanged and the
positive scale ratio is inverted. -/
theorem d4GoodAt_symm {D M : ContMetric d} {z : Rd d} {r c η A b : ℝ}
    (hgood : d4GoodAt D M z r c η A b) :
    d4GoodAt M D z r c⁻¹ η A b := by
  rcases hgood with ⟨hr, hc, hη, hA, hb, hcmp₁, hcmp₂, hdiamD, hdiamM, hshort₁, hshort₂⟩
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  refine ⟨hr, hcinv, hη, hA, hb, ?_, ?_, hdiamM, hdiamD, ?_, ?_⟩
  · intro x hx y hy
    simpa only [div_eq_mul_inv] using hcmp₂ x hx y hy
  · intro x hx y hy
    simpa only [div_eq_mul_inv, inv_inv] using hcmp₁ x hx y hy
  · intro x hx w hw
    simpa only [div_eq_mul_inv] using hshort₂ x hx w hw
  · intro x hx w hw
    simpa only [div_eq_mul_inv, inv_inv] using hshort₁ x hx w hw

/-- A gap before a good crossing costs at most `A` times that crossing. This is (4.4) with
the internal geodesic and closed-annulus endpoints written explicitly. -/
theorem d4_gap_bound {D M : ContMetric d} {R A r c η b : ℝ} {z : Rd d}
    {P : ℝ → Rd d} {T q a s t : ℝ}
    (hgeo : d4InternalGeodesic D (Metric.ball 0 (R + 1)) P T)
    (hq0 : 0 ≤ q) (hTt : t ≤ T) (hqa : q ≤ a) (has : a ≤ s) (hst : s ≤ t)
    (hq : P q ∈ Metric.sphere z (3 * r / 4))
    (hs : P s ∈ Metric.sphere z (3 * r / 4))
    (ht : P t ∈ Metric.sphere z r)
    (hU : d4U z r ⊆ Metric.ball 0 (R + 1))
    (hgood : d4GoodHalf D M z r c η A b)
    (hF : MapsTo P (Icc s t) (d4F z r)) :
    s - a ≤ A * (t - s) := by
  rcases hgeo with ⟨hT, hPc, hPV, hdist, hlen⟩
  rcases hgood with ⟨hr, hc, hη, hA, hb, hcmp₁, hdiamD, hshort₁⟩
  have hqT : q ∈ Icc 0 T := ⟨hq0, by linarith [hqa, has, hst, hTt]⟩
  have hsT : s ∈ Icc 0 T := ⟨by linarith [hq0, hqa, has], hst.trans hTt⟩
  have htT : t ∈ Icc 0 T := ⟨by linarith [hq0, hqa, has, hst], hTt⟩
  have hgeo_qs := hdist q hqT s hsT
  have hgeo_qs' : D.internal (Metric.ball 0 (R + 1)) (P q) (P s) =
      ENNReal.ofReal (s - q) := by
    rw [hgeo_qs, abs_of_nonneg (sub_nonneg.mpr (le_trans hqa has))]
  have hpointdiam : D.internal (d4U z r) (P q) (P s) ≤
      ENNReal.ofReal A * d4Crossing D z r := by
    calc
      D.internal (d4U z r) (P q) (P s) ≤
          ⨆ x ∈ Metric.sphere z (3 * r / 4),
            ⨆ y ∈ Metric.sphere z (3 * r / 4), D.internal (d4U z r) x y :=
        le_iSup₂_of_le (P q) hq (le_iSup₂_of_le (P s) hs le_rfl)
      _ ≤ ENNReal.ofReal A * d4Crossing D z r := hdiamD
  have hgapENN : ENNReal.ofReal (s - a) ≤ ENNReal.ofReal A * d4Crossing D z r := by
    calc
      ENNReal.ofReal (s - a) ≤ ENNReal.ofReal (s - q) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = D.internal (Metric.ball 0 (R + 1)) (P q) (P s) := hgeo_qs'.symm
      _ ≤ D.internal (d4U z r) (P q) (P s) := D.internal_anti hU (P q) (P s)
      _ ≤ ENNReal.ofReal A * d4Crossing D z r := hpointdiam
  have hcross : d4Crossing D z r ≤ ENNReal.ofReal (t - s) := by
    calc
      d4Crossing D z r ≤ D.internal (d4F z r) (P s) (P t) := by
        unfold d4Crossing setDistIn
        exact (iInf₂_le _ hs).trans (iInf₂_le _ ht)
      _ ≤ D.len P s t := D.internal_le_len hst (hPc.mono
        (Icc_subset_Icc (by linarith [hq0, hqa, has]) hTt)) hF
      _ = ENNReal.ofReal (t - s) := hlen s hsT t htT hst
  have hgapENN' : ENNReal.ofReal (s - a) ≤ ENNReal.ofReal A * ENNReal.ofReal (t - s) := by
    calc
      ENNReal.ofReal (s - a) ≤ ENNReal.ofReal A * d4Crossing D z r := hgapENN
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (t - s) := by gcongr
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ A)] at hgapENN'
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by linarith : 0 ≤ A) (sub_nonneg.mpr hst))).1 hgapENN'

/-- Continuity supplies the earlier inner-sphere hit used to charge an actual gap to its
crossing. -/
theorem d4_prior_inner_sphere_hit {P : ℝ → Rd d} {T a ρ : ℝ} {z : Rd d}
    (hP : ContinuousOn P (Icc 0 T)) (ha : 0 ≤ a) (haT : a ≤ T)
    (hstart : ρ < dist (P 0) z) (hcurrent : dist (P a) z < ρ) :
    ∃ q ∈ Icc 0 a, dist (P q) z = ρ := by
  have hPa : ContinuousOn P (Icc 0 a) := hP.mono (Icc_subset_Icc le_rfl haT)
  have hcontDist : ContinuousOn (fun t => dist (P t) z) (Icc 0 a) := by
    change ContinuousOn (fun t => ‖P t - z‖) (Icc 0 a)
    exact (hPa.sub continuousOn_const).norm
  have hcont : ContinuousOn (fun t => -dist (P t) z) (Icc 0 a) := hcontDist.neg
  have hρ : -ρ ∈ Icc (-(dist (P 0) z)) (-(dist (P a) z)) := by
    constructor <;> linarith
  obtain ⟨q, hq, hqeq⟩ := intermediate_value_Icc ha hcont hρ
  have hqdist : dist (P q) z = ρ := by linarith
  exact ⟨q, hq, hqdist⟩

/-- The cost of one good crossing in the forward direction, before the endpoint connectors are
added. -/
theorem d4_crossing_bound_forward {D M : ContMetric d} {R r c η A b : ℝ} {z : Rd d}
    {P : ℝ → Rd d} {T s t : ℝ}
    (hgeo : d4InternalGeodesic D (Metric.ball 0 (R + 1)) P T)
    (hs0 : 0 ≤ s) (htT : t ≤ T) (hst : s ≤ t)
    (hs : P s ∈ Metric.sphere z (3 * r / 4)) (ht : P t ∈ Metric.sphere z r)
    (hgood : d4GoodHalf D M z r c η A b)
    (hF : MapsTo P (Icc s t) (d4F z r)) :
    M.internal (d4U z r) (P s) (P t) ≤ ENNReal.ofReal ((1 + η) * c * (t - s)) := by
  rcases hgeo with ⟨hT, hPc, hPV, hdist, hlen⟩
  rcases hgood with ⟨hr, hc, hη, hA, hb, hcmp₁, hdiamD, hshort₁⟩
  have hsT : s ∈ Icc 0 T := ⟨hs0, by linarith [hst, htT]⟩
  have htT' : t ∈ Icc 0 T := ⟨by linarith [hs0, hst], htT⟩
  have hlen' : D.len P s t = ENNReal.ofReal (t - s) := hlen s hsT t htT' hst
  have hcross : D.internal (d4F z r) (P s) (P t) ≤ ENNReal.ofReal (t - s) := by
    calc
      D.internal (d4F z r) (P s) (P t) ≤ D.len P s t :=
        D.internal_le_len hst (hPc.mono
          (Icc_subset_Icc (by linarith [hs0]) htT'.2)) hF
      _ = ENNReal.ofReal (t - s) := hlen'
  calc
    M.internal (d4U z r) (P s) (P t) ≤
        ENNReal.ofReal ((1 + η) * c) * D.internal (d4F z r) (P s) (P t) :=
      hcmp₁ (P s) hs (P t) ht
    _ ≤ ENNReal.ofReal ((1 + η) * c) * ENNReal.ofReal (t - s) := by gcongr
    _ = ENNReal.ofReal ((1 + η) * c * (t - s)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + η) * c)]

/-- The same local crossing estimate with the metrics interchanged. -/
theorem d4_crossing_bound_reverse {D M : ContMetric d} {R r c η A b : ℝ} {z : Rd d}
    {P : ℝ → Rd d} {T s t : ℝ}
    (hgeo : d4InternalGeodesic M (Metric.ball 0 (R + 1)) P T)
    (hs0 : 0 ≤ s) (htT : t ≤ T) (hst : s ≤ t)
    (hs : P s ∈ Metric.sphere z (3 * r / 4)) (ht : P t ∈ Metric.sphere z r)
    (hgood : d4GoodAt D M z r c η A b)
    (hF : MapsTo P (Icc s t) (d4F z r)) :
    D.internal (d4U z r) (P s) (P t) ≤ ENNReal.ofReal ((1 + η) / c * (t - s)) := by
  rcases hgeo with ⟨hT, hPc, hPV, hdist, hlen⟩
  rcases hgood with ⟨hr, hc, hη, hA, hb, hcmp₁, hcmp₂, hdiamD, hdiamM, hshort₁, hshort₂⟩
  have hsT : s ∈ Icc 0 T := ⟨hs0, by linarith [hst, htT]⟩
  have htT' : t ∈ Icc 0 T := ⟨by linarith [hs0, hst], htT⟩
  have hlen' : M.len P s t = ENNReal.ofReal (t - s) := hlen s hsT t htT' hst
  have hcross : M.internal (d4F z r) (P s) (P t) ≤ ENNReal.ofReal (t - s) := by
    calc
      M.internal (d4F z r) (P s) (P t) ≤ M.len P s t :=
        M.internal_le_len hst (hPc.mono
          (Icc_subset_Icc (by linarith [hs0]) htT'.2)) hF
      _ = ENNReal.ofReal (t - s) := hlen'
  calc
    D.internal (d4U z r) (P s) (P t) ≤
        ENNReal.ofReal ((1 + η) / c) * M.internal (d4F z r) (P s) (P t) :=
      hcmp₂ (P s) hs (P t) ht
    _ ≤ ENNReal.ofReal ((1 + η) / c) * ENNReal.ofReal (t - s) := by gcongr
    _ = ENNReal.ofReal ((1 + η) / c * (t - s)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + η) / c)]

/-- The old-cost gap estimate for the reversed comparison, using the sphere-diameter condition
for `M`. -/
theorem d4_gap_bound_reverse {D M : ContMetric d} {R A r c η b : ℝ} {z : Rd d}
    {P : ℝ → Rd d} {T q a s t : ℝ}
    (hgeo : d4InternalGeodesic M (Metric.ball 0 (R + 1)) P T)
    (hq0 : 0 ≤ q) (hTt : t ≤ T) (hqa : q ≤ a) (has : a ≤ s) (hst : s ≤ t)
    (hq : P q ∈ Metric.sphere z (3 * r / 4))
    (hs : P s ∈ Metric.sphere z (3 * r / 4))
    (ht : P t ∈ Metric.sphere z r)
    (hU : d4U z r ⊆ Metric.ball 0 (R + 1))
    (hgood : d4GoodAt D M z r c η A b)
    (hF : MapsTo P (Icc s t) (d4F z r)) :
    s - a ≤ A * (t - s) := by
  rcases hgeo with ⟨hT, hPc, hPV, hdist, hlen⟩
  rcases hgood with ⟨hr, hc, hη, hA, hb, hcmp₁, hcmp₂, hdiamD, hdiamM, hshort₁, hshort₂⟩
  have hqT : q ∈ Icc 0 T := ⟨hq0, by linarith [hqa, has, hst, hTt]⟩
  have hsT : s ∈ Icc 0 T := ⟨by linarith [hq0, hqa, has], hst.trans hTt⟩
  have hpointdiam : M.internal (d4U z r) (P q) (P s) ≤
      ENNReal.ofReal A * d4Crossing M z r := by
    calc
      M.internal (d4U z r) (P q) (P s) ≤
          ⨆ x ∈ Metric.sphere z (3 * r / 4),
            ⨆ y ∈ Metric.sphere z (3 * r / 4), M.internal (d4U z r) x y :=
        le_iSup₂_of_le (P q) hq (le_iSup₂_of_le (P s) hs le_rfl)
      _ ≤ ENNReal.ofReal A * d4Crossing M z r := hdiamM
  have hgeo_qs : M.internal (Metric.ball 0 (R + 1)) (P q) (P s) =
      ENNReal.ofReal (s - q) := by
    rw [hdist q hqT s hsT, abs_of_nonneg (sub_nonneg.mpr (le_trans hqa has))]
  have hgapENN : ENNReal.ofReal (s - a) ≤ ENNReal.ofReal A * d4Crossing M z r := by
    calc
      ENNReal.ofReal (s - a) ≤ ENNReal.ofReal (s - q) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = M.internal (Metric.ball 0 (R + 1)) (P q) (P s) := hgeo_qs.symm
      _ ≤ M.internal (d4U z r) (P q) (P s) := M.internal_anti hU (P q) (P s)
      _ ≤ ENNReal.ofReal A * d4Crossing M z r := hpointdiam
  have hcross : d4Crossing M z r ≤ ENNReal.ofReal (t - s) := by
    calc
      d4Crossing M z r ≤ M.internal (d4F z r) (P s) (P t) := by
        unfold d4Crossing setDistIn
        exact (iInf₂_le _ hs).trans (iInf₂_le _ ht)
      _ ≤ M.len P s t := M.internal_le_len hst (hPc.mono
        (Icc_subset_Icc (by linarith [hq0, hqa, has]) hTt)) hF
      _ = ENNReal.ofReal (t - s) := hlen s hsT t ⟨by linarith [hq0, hqa, has, hst], hTt⟩ hst
  have hgapENN' : ENNReal.ofReal (s - a) ≤ ENNReal.ofReal A * ENNReal.ofReal (t - s) := by
    calc
      ENNReal.ofReal (s - a) ≤ ENNReal.ofReal A * d4Crossing M z r := hgapENN
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (t - s) := by gcongr
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ A)] at hgapENN'
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by linarith : 0 ≤ A) (sub_nonneg.mpr hst))).1 hgapENN'

/-- The contraction fraction from (3.10). -/
def d4Theta (A : ℝ) : ℝ := A / (A + 1)

/-- The elementary fraction estimate used after summing the annular gap bounds. -/
theorem d4_step2_fraction {A B G : ℝ} (hA : 0 ≤ A)
    (hBG : B ≤ A * G) : B ≤ d4Theta A * (B + G) := by
  rw [d4Theta]
  have hden : 0 < A + 1 := by linarith
  have hmul : B * (A + 1) ≤ A * (B + G) := by nlinarith [hBG]
  calc
    B ≤ A * (B + G) / (A + 1) := (le_div_iff₀ hden).2 hmul
    _ = A / (A + 1) * (B + G) := by ring

/-- Summed gap and crossing times satisfy (4.5) whenever each gap is bounded by `A` times
its crossing. -/
theorem d4_step2_sum {n : ℕ} (A : ℝ) (B₀ G₀ : Fin n → ℝ)
    (hA : 0 ≤ A) (hBG : ∀ i, B₀ i ≤ A * G₀ i) :
    (∑ i, B₀ i) ≤ d4Theta A * ((∑ i, B₀ i) + (∑ i, G₀ i)) := by
  apply d4_step2_fraction hA
  calc
    (∑ i, B₀ i) ≤ ∑ i, A * G₀ i := Finset.sum_le_sum fun i _ => hBG i
    _ = A * ∑ i, G₀ i := by rw [Finset.mul_sum]

end HigherDimLFPPAS.Improve

end
