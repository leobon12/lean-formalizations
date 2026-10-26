import SupercriticalConformalCovariance.BiLip.Target
import SupercriticalConformalCovariance.GoodAnnulus.Literal
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Shield
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ELocalA

/-!
# Lemma 5.1, (G5): the shield for the transported domain metric `e`

Paper l. 425–434: "On (9), choose a surrounding source loop of length less than `2kS`. By Lemma 2.1, its
`e`-length is less than `2CkS = S/(2C)`, whereas an `e`-path escaping `A` from the middle region costs at least
`S/C`. […] Therefore both distances between `u` and `v` agree with the distances intrinsic to `A`. […]
Near-minimizing paths suffice; no `e`-geodesic is needed."

`target_shield`: under the pointwise two-sided Lemma 2.1 comparison on `U` (`e ≤ C d_U`, `d_U ≤ C e`), for
`v ∈ ∂B_r(z)`, `|u − v| ≤ q r` and a `D_h`-loop `ℓ` in `A_{qr,√q r}(v)` separating its circles with
`D_h`-length `< S/(2C²) = 2kS` (`k = 1/(4C²)`, `S = D_h(A_{3r/4,3r/2}, ∂A_{r/2,2r})`):

  `e(u, v) = e(u, v; cl A_{r/2,2r}(z))`.

The proof uses only metric values of `e` along the loop. With `x₁ = ℓ(σ_a)`, `x₂ = ℓ(σ_b)`,
`e(x₁, x₂) ≤ C·d_U(x₁, x₂) ≤ C·len ℓ < S/(2C)`. A second near-geodesic between `x₁` and `x₂` cannot reach
`∂A` (cost `≥ S/C`). In particular the source loop need not be an admissible `e`-curve: no continuity of
`D_{g₀}` in the Euclidean topology is used. A near-geodesic `e`-path from `u` to `v` leaving `A` is replaced
between its first hit of the loop (before the first exit from `B̄(v, √q r)`) and its last hit.

Also ported: `barrier_pos`, `barrier_eq_ambient` (the
first-exit identity of the internal barrier with the ambient set distance).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.L51

open SupercriticalLQGUniqueness (LSCMetric weylScale Disconnects)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events (eventCarrier eventMiddle eventBoundary
  eventOpen)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)
open SupercriticalConformalCovariance.Domain (dV SV)
open HigherDimLQGMetric (curveLengthWith internalWith)
open SupercriticalConformalCovariance.BiLip (eT lenT AdmT confT pathInf)

/-! ## The barrier -/

section Barrier

open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

theorem barrier_pos (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) :
    0 < SupercriticalConformalCovariance.GoodAnnulus.barrier D z r :=
  (setDist_middle_pos D z r.2).trans_le (SupercriticalConformalCovariance.GoodAnnulus.ambient_setDist_le_barrier D z r)

/-- First-exit identification of the internal barrier with the ambient middle-to-boundary distance
(`SupercriticalConformalCovariance.Good.barrier_eq_ambient`, ported). -/
theorem barrier_eq_ambient (D : LSCMetric)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : D.IsLengthSpace) (z : ℂ) (r : Ioi (0 : ℝ)) :
    SupercriticalConformalCovariance.GoodAnnulus.barrier D z r = setDist D (eventMiddle z r) (eventBoundary z r) := by
  have hV : IsOpen (eventOpen z r) := eventOpen_isOpen z r
  have hcl : closure (eventOpen z r) ⊆ eventOpen z r ∪ eventBoundary z r := closure_eventOpen_subset z r
  have hS : IsClosed (eventBoundary z r) := isClosed_eventBoundary z r
  have hVU : eventOpen z r ∪ eventBoundary z r ⊆ eventCarrier z r := by
    rw [eventOpen_union_boundary z r.2]
  have hMV : eventMiddle z r ⊆ eventOpen z r := eventMiddle_subset_open z r.2
  have hfirst := setDist_eq_iInf_intExt hcont hL hV hcl hS hVU hMV
  apply le_antisymm
  · rw [hfirst]
    unfold SupercriticalConformalCovariance.GoodAnnulus.barrier LSCMetric.internalSetDist
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    have hxC : x ∈ eventCarrier z r := hVU (Or.inl (hMV hx))
    have hyC : y ∈ eventCarrier z r := hVU (Or.inr hy)
    rw [← internal_eq_intExt D (eventCarrier z r) (⟨⟨x, hxC⟩, ⟨y, hyC⟩⟩)]
    let Y : Set ℂ := eventCarrier z r
    let M : Set ℂ := eventMiddle z r
    let B : Set ℂ := eventBoundary z r
    let F : Y → ℝ≥0∞ := fun xx =>
      ⨅ (_ : (xx : ℂ) ∈ M) (yy : Y) (_ : (yy : ℂ) ∈ B), D.internal Y (xx, yy)
    change (⨅ xx : Y, F xx) ≤ D.internal Y (⟨x, hxC⟩, ⟨y, hyC⟩)
    calc
      (⨅ xx : Y, F xx) ≤ F ⟨x, hxC⟩ := iInf_le F _
      _ ≤ ⨅ yy : Y, ⨅ (_ : (yy : ℂ) ∈ B), D.internal Y (⟨x, hxC⟩, yy) := iInf_le _ hx
      _ ≤ ⨅ (_ : ((⟨y, hyC⟩ : Y) : ℂ) ∈ B), D.internal Y (⟨x, hxC⟩, ⟨y, hyC⟩) :=
          iInf_le _ (⟨y, hyC⟩ : Y)
      _ ≤ D.internal Y (⟨x, hxC⟩, ⟨y, hyC⟩) := iInf_le _ hy
  · exact SupercriticalConformalCovariance.GoodAnnulus.ambient_setDist_le_barrier D z r

end Barrier

/-! ## Geometry -/

section Geometry

variable {z v : ℂ} {r q : ℝ}

theorem sqrt_mul_lt_tenth (hr : 0 < r) (hq0 : 0 < q) (hq : q < 1 / 100) :
    Real.sqrt q * r < r / 10 := by
  have := SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.sqrt_lt_tenth hq0.le hq
  nlinarith

theorem q_le_sqrt (hq0 : 0 < q) (hq : q < 1 / 100) : q ≤ Real.sqrt q := by
  have h1 : q < 1 := by linarith
  exact (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.lt_sqrt_self hq0 h1).le

/-- `B̄_{√q r}(v)` lies in the middle annulus `A_{3r/4,3r/2}(z)` for `v ∈ ∂B_r(z)` -/
theorem closedBall_subset_middle (hr : 0 < r) (hq0 : 0 < q) (hq : q < 1 / 100)
    (hv : v ∈ sphere z r) : closedBall v (Real.sqrt q * r) ⊆ eventMiddle z r := by
  intro y hy
  rw [mem_closedBall] at hy
  rw [mem_sphere] at hv
  have h1 := dist_triangle y v z
  have h2 := dist_triangle v y z
  have h3 : dist v y = dist y v := dist_comm v y
  have hσ := sqrt_mul_lt_tenth hr hq0 hq
  exact ⟨mem_ball.2 (by linarith), by rw [mem_closedBall, not_le]; linarith⟩

theorem middle_subset_carrier : eventMiddle z r ⊆ eventCarrier z r := by
  rintro y ⟨h1, h2⟩
  rw [mem_ball] at h1
  rw [mem_closedBall, not_le] at h2
  refine ⟨mem_closedBall.2 (by linarith), ?_⟩
  rw [mem_ball, not_lt]
  linarith

/-- a continuous path from the carrier to its complement hits the boundary circles -/
theorem exists_boundary_of_carrier {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (ha : P a ∈ eventCarrier z r) (hb : P b ∉ eventCarrier z r) :
    ∃ c ∈ Icc a b, P c ∈ eventBoundary z r := by
  have hf : ContinuousOn (fun t => dist (P t) z) (Icc a b) :=
    continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  obtain ⟨ha1, ha2⟩ := ha
  rw [mem_closedBall] at ha1
  rw [mem_ball, not_lt] at ha2
  have hb' : ¬ (dist (P b) z ≤ 2 * r ∧ r / 2 ≤ dist (P b) z) := fun h =>
    hb ⟨mem_closedBall.2 h.1, by rw [mem_ball, not_lt]; exact h.2⟩
  by_cases h2 : dist (P b) z ≤ 2 * r
  · have h3 : dist (P b) z < r / 2 := by
      by_contra h; exact hb' ⟨h2, not_lt.1 h⟩
    obtain ⟨c, hc, hce⟩ := intermediate_value_Icc' hab hf ⟨h3.le, ha2⟩
    exact ⟨c, hc, Or.inl (mem_sphere.2 hce)⟩
  · obtain ⟨c, hc, hce⟩ := intermediate_value_Icc hab hf ⟨ha1, (not_le.1 h2).le⟩
    exact ⟨c, hc, Or.inr (mem_sphere.2 hce)⟩

/-- the reverse form -/
theorem exists_boundary_of_carrier_rev {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b))
    (ha : P a ∉ eventCarrier z r) (hb : P b ∈ eventCarrier z r) :
    ∃ c ∈ Icc a b, P c ∈ eventBoundary z r := by
  have hP' : ContinuousOn (fun t => P (a + b - t)) (Icc a b) :=
    hP.comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  obtain ⟨c, hc, hce⟩ := exists_boundary_of_carrier (P := fun t => P (a + b - t)) hab hP'
    (by simpa using hb) (by simpa using ha)
  exact ⟨a + b - c, ⟨by linarith [hc.2], by linarith [hc.1]⟩, hce⟩

end Geometry

/-! ## The shield -/

section Shield

variable {D₀ D₁ : LSCMetric} {ξ : ℝ} {U V : Set ℂ} (k : C(V, ℝ)) {φ ψ : ℂ → ℂ}

/-- the `e`-cost of reaching `∂A` from the middle region, by the lower Lemma 2.1 comparison -/
theorem escape_cost {C : ℝ} (hC : 1 ≤ C)
    (hcmp : ∀ x ∈ U, ∀ y ∈ U, pathInf D₁ U x y ≤ ENNReal.ofReal C * eT D₀ ξ k φ x y)
    {z : ℂ} {r : ℝ} {x y : ℂ} (hx : x ∈ eventMiddle z r) (hy : y ∈ eventBoundary z r)
    (hxU : x ∈ U) (hyU : y ∈ U) :
    ENNReal.ofReal C⁻¹ * setDist D₁ (eventMiddle z r) (eventBoundary z r) ≤ eT D₀ ξ k φ x y := by
  have hC0 : 0 < C := by linarith
  have h1 : setDist D₁ (eventMiddle z r) (eventBoundary z r) ≤ D₁ (x, y) :=
    iInf₂_le_of_le x hx (iInf₂_le y hy)
  have h2 : D₁ (x, y) ≤ pathInf D₁ U x y :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.dist_le_intExt D₁ U x y
  have h3 := hcmp x hxU y hyU
  calc ENNReal.ofReal C⁻¹ * setDist D₁ (eventMiddle z r) (eventBoundary z r)
      ≤ ENNReal.ofReal C⁻¹ * (ENNReal.ofReal C * eT D₀ ξ k φ x y) := by gcongr; exact h1.trans (h2.trans h3)
    _ = eT D₀ ξ k φ x y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hC0.le), inv_mul_cancel₀ hC0.ne',
          ENNReal.ofReal_one, one_mul]

/-- an admissible path from the middle region leaving the carrier has `e`-length `≥ S/C` -/
theorem escape_lenT {C : ℝ} (hC : 1 ≤ C)
    (hcmp : ∀ x ∈ U, ∀ y ∈ U, pathInf D₁ U x y ≤ ENNReal.ofReal C * eT D₀ ξ k φ x y)
    {z : ℂ} {r : ℝ} {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hPU : ∀ t ∈ Icc a b, P t ∈ U) (ha : P a ∈ eventMiddle z r) (hb : P b ∉ eventCarrier z r) :
    ENNReal.ofReal C⁻¹ * setDist D₁ (eventMiddle z r) (eventBoundary z r) ≤ lenT D₀ ξ k φ P a b := by
  obtain ⟨c, hc, hcB⟩ := exists_boundary_of_carrier hab hP (middle_subset_carrier ha) hb
  calc _ ≤ eT D₀ ξ k φ (P a) (P c) :=
        escape_cost k hC hcmp ha hcB (hPU a ⟨le_rfl, hab⟩) (hPU c hc)
    _ ≤ lenT D₀ ξ k φ P a c := SupercriticalConformalCovariance.BiLip.eT_le_lenT k P hc.1
    _ ≤ lenT D₀ ξ k φ P a b := HigherDimLQGMetric.curveLengthWith_mono_interval le_rfl hc.1 hc.2

/-- the reverse form: entering the middle region from outside the carrier -/
theorem escape_lenT_rev {C : ℝ} (hC : 1 ≤ C)
    (hcmp : ∀ x ∈ U, ∀ y ∈ U, pathInf D₁ U x y ≤ ENNReal.ofReal C * eT D₀ ξ k φ x y)
    {z : ℂ} {r : ℝ} {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hPU : ∀ t ∈ Icc a b, P t ∈ U) (ha : P a ∉ eventCarrier z r) (hb : P b ∈ eventMiddle z r) :
    ENNReal.ofReal C⁻¹ * setDist D₁ (eventMiddle z r) (eventBoundary z r) ≤ lenT D₀ ξ k φ P a b := by
  obtain ⟨c, hc, hcB⟩ := exists_boundary_of_carrier_rev hab hP ha (middle_subset_carrier hb)
  calc _ ≤ eT D₀ ξ k φ (P b) (P c) :=
        escape_cost k hC hcmp hb hcB (hPU b ⟨hab, le_rfl⟩) (hPU c hc)
    _ = eT D₀ ξ k φ (P c) (P b) := SupercriticalConformalCovariance.BiLip.eT_comm k _ _
    _ ≤ lenT D₀ ξ k φ P c b := SupercriticalConformalCovariance.BiLip.eT_le_lenT k P hc.2
    _ ≤ lenT D₀ ξ k φ P a b := HigherDimLQGMetric.curveLengthWith_mono_interval hc.1 hc.2 le_rfl

/-- `e(·,·; C) ≤ e`-length for an admissible path inside `C` -/
theorem confT_le_lenT {C : Set ℂ} {P : ℝ → ℂ} {a b : ℝ} (hP : AdmT D₀ φ U P a b)
    (hPC : ∀ t ∈ Icc a b, P t ∈ C) :
    confT D₀ ξ k φ C (P a) (P b) ≤ lenT D₀ ξ k φ P a b := by
  have h := SupercriticalConformalCovariance.BiLip.internalWith_le_curveLengthWith (dV D₀ ξ k) (S := SV D₀ (φ '' C))
    (Q := D₀.pt ∘ φ ∘ P) hP.1 hP.2.2.1 (fun t ht => by
      show forget D₀ (D₀.pt (φ (P t))) ∈ φ '' C
      exact ⟨P t, hPC t ht, rfl⟩)
  exact h

/-- the `D`-internal distance of `U` between two points of a curve in `U` is at most its length -/
theorem pathInf_le_len_of_curve {D : LSCMetric} {L : ℝ → ℂ} {σ₀ σ₁ : ℝ} (hL : D.IsCurve L σ₀ σ₁)
    (hLU : ∀ t ∈ Icc σ₀ σ₁, L t ∈ U) {σa σb : ℝ} (ha : σa ∈ Icc σ₀ σ₁) (hb : σb ∈ Icc σ₀ σ₁) :
    pathInf D U (L σa) (L σb) ≤ D.len L σ₀ σ₁ := by
  have key : ∀ {s t : ℝ}, s ∈ Icc σ₀ σ₁ → t ∈ Icc σ₀ σ₁ → s ≤ t →
      pathInf D U (L s) (L t) ≤ D.len L σ₀ σ₁ := by
    intro s t hs ht hst
    have hc : D.IsCurve L s t := ⟨hst, hL.2.mono (Icc_subset_Icc hs.1 ht.2)⟩
    calc pathInf D U (L s) (L t) ≤ D.len L s t := by
          unfold pathInf
          exact iInf_le_of_le L <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hc <|
            iInf_le_of_le (fun τ hτ => hLU τ ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩) <|
            iInf_le_of_le rfl <| iInf_le_of_le rfl le_rfl
      _ ≤ D.len L σ₀ σ₁ :=
          SupercriticalLQGUniqueness.B2.PfeWeyl.len_mono_Icc D L hs.1 ht.2
  rcases le_total σa σb with h | h
  · exact key ha hb h
  · rw [(SupercriticalConformalCovariance.BiLip.isPMetricOn_pathInf D U).2.1 _ (hLU σa ha) _ (hLU σb hb)]
    exact key hb ha h

/-- **The shield for `e`** (paper l. 425–434): at a (G5)-antecedent pair, `e(u, v)` is the internal
`e`-distance of the closed event annulus `cl A_{r/2,2r}(z)`. -/
theorem target_shield (hξ : 0 ≤ ξ) (hf₀ : Continuous (forget D₀)) (hL₀ : D₀.IsLengthSpace)
    (hV : IsOpen V) (E : C(ℂ, ℝ) → LSCMetric) (hE : ∀ F q, E F q = weylScale ξ F D₀ q)
    (hφc : ContinuousOn φ U) (hφU : MapsTo φ U V)
    (hψV : MapsTo ψ V U) (hψc : ContinuousOn ψ V) (hφψ : ∀ y ∈ V, φ (ψ y) = y)
    (hψφ : ∀ x ∈ U, ψ (φ x) = x)
    {C : ℝ} (hC : 1 ≤ C)
    (hup : ∀ x ∈ U, ∀ y ∈ U, eT D₀ ξ k φ x y ≤ ENNReal.ofReal C * pathInf D₁ U x y)
    (hlo : ∀ x ∈ U, ∀ y ∈ U, pathInf D₁ U x y ≤ ENNReal.ofReal C * eT D₀ ξ k φ x y)
    {z u v : ℂ} {r q : ℝ} (hr : 0 < r) (hq0 : 0 < q) (hq : q < 1 / 100)
    (hYU : eventCarrier z r ⊆ U) (hv : v ∈ sphere z r) (huv : dist u v ≤ q * r)
    {L : ℝ → ℂ} {σ₀ σ₁ : ℝ} (hL : D₁.IsCurve L σ₀ σ₁)
    (hLA : ∀ t ∈ Icc σ₀ σ₁, L t ∈ ball v (Real.sqrt q * r))
    (hLd : Disconnects (L '' Icc σ₀ σ₁) (sphere v (q * r)) (sphere v (Real.sqrt q * r)))
    (hLlen : D₁.len L σ₀ σ₁ < ENNReal.ofReal (1 / (2 * C ^ 2)) *
      setDist D₁ (eventMiddle z r) (eventBoundary z r))
    (hSt : setDist D₁ (eventMiddle z r) (eventBoundary z r) < ⊤) :
    eT D₀ ξ k φ u v = confT D₀ ξ k φ (eventCarrier z r) u v := by
  set S := setDist D₁ (eventMiddle z r) (eventBoundary z r) with hSdef
  set Y := eventCarrier z r with hYdef
  set ρ := Real.sqrt q * r with hρdef
  have hC0 : 0 < C := by linarith
  have hS0 : 0 < S :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.setDist_middle_pos D₁ z hr
  have hYc : IsCompact Y :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.isCompact_eventCarrier z r
  have hpm := SupercriticalConformalCovariance.BiLip.isPMetricOn_confT k hξ hf₀ hL₀ hV E hE hφc hφU hYc hYU
  have hBM : closedBall v ρ ⊆ eventMiddle z r := closedBall_subset_middle hr hq0 hq hv
  have hBY : closedBall v ρ ⊆ Y := hBM.trans middle_subset_carrier
  have hqρ : q * r ≤ ρ := mul_le_mul_of_nonneg_right (q_le_sqrt hq0 hq) hr.le
  have huY : u ∈ Y := hBY (mem_closedBall.2 (huv.trans hqρ))
  have hvY : v ∈ Y := hBY (mem_closedBall_self (by positivity))
  refine le_antisymm (SupercriticalConformalCovariance.BiLip.eT_le_confT k hf₀ hV hYU hφU u v) ?_
  by_cases hfin : eT D₀ ξ k φ u v = ⊤
  · rw [hfin]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  obtain ⟨P, a, b, hP, hPU, hPa, hPb, hPlen⟩ := SupercriticalConformalCovariance.BiLip.exists_admT_le k hf₀ hV hψV hψc hφψ hψφ
    u (hYU huY) v (hYU hvY) (lt_top_iff_ne_top.2 hfin) (δ : ℝ≥0∞) (by exact_mod_cast hδ)
  have hab : a ≤ b := hP.1
  have hPc : ContinuousOn P (Icc a b) := hP.2.1
  by_cases hstay : ∀ t ∈ Icc a b, P t ∈ Y
  · calc confT D₀ ξ k φ Y u v = confT D₀ ξ k φ Y (P a) (P b) := by rw [hPa, hPb]
      _ ≤ lenT D₀ ξ k φ P a b := confT_le_lenT k hP hstay
      _ ≤ eT D₀ ξ k φ u v + δ := hPlen
  push Not at hstay
  obtain ⟨t₀, ht₀, ht₀Y⟩ := hstay
  have hfar : ρ < dist (P t₀) v := by
    by_contra h; push Not at h; exact ht₀Y (hBY (mem_closedBall.2 h))
  have hdc : ContinuousOn (fun t => dist (P t) v) (Icc a b) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  -- the first exit from `B̄_ρ(v)` and the first hit of the loop before it
  set A₁ : Set ℝ := Icc a t₀ ∩ (fun t => dist (P t) v) ⁻¹' Ici ρ with hA₁
  have hA₁ne : A₁.Nonempty := ⟨t₀, ⟨ht₀.1, le_rfl⟩, hfar.le⟩
  have hA₁cl : IsClosed A₁ :=
    (hdc.mono (Icc_subset_Icc le_rfl ht₀.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hA₁bdd : BddBelow A₁ := ⟨a, fun t ht => ht.1.1⟩
  set T₁ := sInf A₁ with hT₁def
  have hT₁ : T₁ ∈ A₁ := hA₁cl.csInf_mem hA₁ne hA₁bdd
  have hbefore : ∀ t ∈ Icc a t₀, t < T₁ → dist (P t) v < ρ := fun t ht htT => by
    by_contra h; push Not at h
    exact absurd (csInf_le hA₁bdd ⟨ht, h⟩) (not_le.2 htT)
  obtain ⟨s₁, hs₁, hs₁L⟩ := SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.path_hits_of_disconnects
    hT₁.1.1 (hPc.mono (Icc_subset_Icc le_rfl (hT₁.1.2.trans ht₀.2))) hqρ hLd
    (by rw [hPa]; exact huv) hT₁.2
  -- the last exit and the last hit after it
  set A₂ : Set ℝ := Icc t₀ b ∩ (fun t => dist (P t) v) ⁻¹' Ici ρ with hA₂
  have hA₂ne : A₂.Nonempty := ⟨t₀, ⟨le_rfl, ht₀.2⟩, hfar.le⟩
  have hA₂cl : IsClosed A₂ :=
    (hdc.mono (Icc_subset_Icc ht₀.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hA₂bdd : BddAbove A₂ := ⟨b, fun t ht => ht.1.2⟩
  set T₂ := sSup A₂ with hT₂def
  have hT₂ : T₂ ∈ A₂ := hA₂cl.csSup_mem hA₂ne hA₂bdd
  have hafter : ∀ t ∈ Icc t₀ b, T₂ < t → dist (P t) v < ρ := fun t ht htT => by
    by_contra h; push Not at h
    exact absurd (le_csSup hA₂bdd ⟨ht, h⟩) (not_le.2 htT)
  obtain ⟨s₂, hs₂, hs₂L⟩ :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.path_hits_of_disconnects_rev
    hT₂.1.2 (hPc.mono (Icc_subset_Icc (ht₀.1.trans hT₂.1.1) le_rfl)) hqρ hLd hT₂.2
    (by rw [hPb, dist_self]; positivity)
  have h1 : a ≤ s₁ := hs₁.1
  have h2 : s₁ ≤ t₀ := hs₁.2.trans hT₁.1.2
  have h3 : t₀ ≤ s₂ := hT₂.1.1.trans hs₂.1
  have h4 : s₂ ≤ b := hs₂.2
  obtain ⟨σa, hσa, hσae⟩ := hs₁L
  obtain ⟨σb, hσb, hσbe⟩ := hs₂L
  have hx₁M : P s₁ ∈ eventMiddle z r := by
    rw [← hσae]; exact hBM (ball_subset_closedBall (hLA σa hσa))
  have hx₂M : P s₂ ∈ eventMiddle z r := by
    rw [← hσbe]; exact hBM (ball_subset_closedBall (hLA σb hσb))
  -- the two sides of the replaced excursion stay in `Y`
  have hpre : ∀ t ∈ Icc a s₁, P t ∈ Y := by
    intro t ht
    rcases lt_or_eq_of_le (ht.2.trans hs₁.2) with hlt | heq
    · exact hBY (mem_closedBall.2
        (hbefore t ⟨ht.1, (ht.2.trans hs₁.2).trans hT₁.1.2⟩ hlt).le)
    · have hts : t = s₁ := le_antisymm ht.2 (heq ▸ hs₁.2)
      rw [hts]; exact middle_subset_carrier hx₁M
  have hpost : ∀ t ∈ Icc s₂ b, P t ∈ Y := by
    intro t ht
    rcases lt_or_eq_of_le (hs₂.1.trans ht.1) with hlt | heq
    · exact hBY (mem_closedBall.2
        (hafter t ⟨h3.trans ht.1, ht.2⟩ hlt).le)
    · have hts : t = s₂ := le_antisymm (heq ▸ hs₂.1) ht.1
      rw [hts]; exact middle_subset_carrier hx₂M
  -- the two escape crossings
  have hes1 : ENNReal.ofReal C⁻¹ * S ≤ lenT D₀ ξ k φ P s₁ t₀ :=
    escape_lenT k hC hlo h2 (hPc.mono (Icc_subset_Icc h1 (h3.trans h4)))
      (fun t ht => hPU t ⟨h1.trans ht.1, ht.2.trans (h3.trans h4)⟩) hx₁M ht₀Y
  have hes2 : ENNReal.ofReal C⁻¹ * S ≤ lenT D₀ ξ k φ P t₀ s₂ :=
    escape_lenT_rev k hC hlo h3 (hPc.mono (Icc_subset_Icc (h1.trans h2) h4))
      (fun t ht => hPU t ⟨(h1.trans h2).trans ht.1, ht.2.trans h4⟩) ht₀Y hx₂M
  -- the shortcut along the loop, measured by `e`
  have hs₁U : P s₁ ∈ U := hPU s₁ ⟨h1, h2.trans ht₀.2⟩
  have hs₂U : P s₂ ∈ U := hPU s₂ ⟨ht₀.1.trans h3, h4⟩
  have hloopU : ∀ t ∈ Icc σ₀ σ₁, L t ∈ U := fun t ht =>
    hYU (hBY (ball_subset_closedBall (hLA t ht)))
  have hpi : pathInf D₁ U (P s₁) (P s₂) ≤ D₁.len L σ₀ σ₁ := by
    rw [← hσae, ← hσbe]; exact pathInf_le_len_of_curve hL hloopU hσa hσb
  have hCne : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 hC0).ne'
  have he12 : eT D₀ ξ k φ (P s₁) (P s₂) < ENNReal.ofReal (1 / (2 * C)) * S :=
    calc eT D₀ ξ k φ (P s₁) (P s₂) ≤ ENNReal.ofReal C * pathInf D₁ U (P s₁) (P s₂) :=
          hup _ hs₁U _ hs₂U
      _ ≤ ENNReal.ofReal C * D₁.len L σ₀ σ₁ := by gcongr
      _ < ENNReal.ofReal C * (ENNReal.ofReal (1 / (2 * C ^ 2)) * S) :=
          (ENNReal.mul_lt_mul_iff_right hCne ENNReal.ofReal_ne_top).2 hLlen
      _ = ENNReal.ofReal (1 / (2 * C)) * S := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC0.le]
          congr 2
          field_simp
  have hhalf : 0 < ENNReal.ofReal (1 / (2 * C)) * S :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hS0.ne'
  have hhalft : ENNReal.ofReal (1 / (2 * C)) * S < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSt
  obtain ⟨Qp, a', b', hQ, hQU, hQa, hQb, hQlen⟩ := SupercriticalConformalCovariance.BiLip.exists_admT_le k hf₀ hV hψV hψc hφψ hψφ
    (P s₁) hs₁U (P s₂) hs₂U (he12.trans hhalft) _ hhalf
  have hQshort : lenT D₀ ξ k φ Qp a' b' < ENNReal.ofReal C⁻¹ * S := by
    refine hQlen.trans_lt ?_
    calc eT D₀ ξ k φ (P s₁) (P s₂) + ENNReal.ofReal (1 / (2 * C)) * S
        < ENNReal.ofReal (1 / (2 * C)) * S + ENNReal.ofReal (1 / (2 * C)) * S :=
          ENNReal.add_lt_add_right hhalft.ne he12
      _ = ENNReal.ofReal C⁻¹ * S := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          field_simp
          ring
  have hQstay : ∀ t ∈ Icc a' b', Qp t ∈ Y := by
    intro t ht
    by_contra hQt
    have hesc := escape_lenT k hC hlo ht.1 (hQ.2.1.mono (Icc_subset_Icc le_rfl ht.2))
      (fun τ hτ => hQU τ ⟨hτ.1, hτ.2.trans ht.2⟩) (by rw [hQa]; exact hx₁M) hQt
    exact absurd (hesc.trans (HigherDimLQGMetric.curveLengthWith_mono_interval le_rfl ht.1 ht.2))
      (not_le.2 hQshort)
  have hc12 : confT D₀ ξ k φ Y (P s₁) (P s₂) ≤ lenT D₀ ξ k φ Qp a' b' := by
    rw [← hQa, ← hQb]; exact confT_le_lenT k hQ hQstay
  have hc1 : confT D₀ ξ k φ Y (P a) (P s₁) ≤ lenT D₀ ξ k φ P a s₁ :=
    confT_le_lenT k (U := U) ⟨h1, hPc.mono (Icc_subset_Icc le_rfl (h2.trans ht₀.2)),
      hP.2.2.1.mono (Icc_subset_Icc le_rfl (h2.trans ht₀.2)),
      fun t ht => hPU t ⟨ht.1, ht.2.trans (h2.trans ht₀.2)⟩⟩ hpre
  have hc2 : confT D₀ ξ k φ Y (P s₂) (P b) ≤ lenT D₀ ξ k φ P s₂ b :=
    confT_le_lenT k (U := U) ⟨h4, hPc.mono (Icc_subset_Icc (ht₀.1.trans h3) le_rfl),
      hP.2.2.1.mono (Icc_subset_Icc (ht₀.1.trans h3) le_rfl),
      fun t ht => hPU t ⟨(ht₀.1.trans h3).trans ht.1, ht.2⟩⟩ hpost
  have hx₁Y : P s₁ ∈ Y := middle_subset_carrier hx₁M
  have hx₂Y : P s₂ ∈ Y := middle_subset_carrier hx₂M
  have huY' : P a ∈ Y := by rw [hPa]; exact huY
  have hvY' : P b ∈ Y := by rw [hPb]; exact hvY
  have htri : confT D₀ ξ k φ Y (P a) (P b) ≤ confT D₀ ξ k φ Y (P a) (P s₁) +
      confT D₀ ξ k φ Y (P s₁) (P s₂) + confT D₀ ξ k φ Y (P s₂) (P b) :=
    (hpm.2.2 _ huY' _ hx₁Y _ hvY').trans (by
      rw [add_assoc]; exact add_le_add le_rfl (hpm.2.2 _ hx₁Y _ hx₂Y _ hvY'))
  have hsplit : lenT D₀ ξ k φ P a b = lenT D₀ ξ k φ P a s₁ + lenT D₀ ξ k φ P s₁ t₀ +
      lenT D₀ ξ k φ P t₀ s₂ + lenT D₀ ξ k φ P s₂ b := by
    rw [SupercriticalConformalCovariance.BiLip.lenT_add k P a s₁ b h1 ((h2.trans h3).trans h4),
      SupercriticalConformalCovariance.BiLip.lenT_add k P s₁ t₀ b h2 (h3.trans h4), SupercriticalConformalCovariance.BiLip.lenT_add k P t₀ s₂ b h3 h4]
    ring
  calc confT D₀ ξ k φ Y u v = confT D₀ ξ k φ Y (P a) (P b) := by rw [hPa, hPb]
    _ ≤ lenT D₀ ξ k φ P a s₁ + lenT D₀ ξ k φ Qp a' b' + lenT D₀ ξ k φ P s₂ b :=
        htri.trans (add_le_add (add_le_add hc1 hc12) hc2)
    _ ≤ lenT D₀ ξ k φ P a s₁ + (lenT D₀ ξ k φ P s₁ t₀ + lenT D₀ ξ k φ P t₀ s₂) +
          lenT D₀ ξ k φ P s₂ b := by
        gcongr
        exact hQshort.le.trans (hes1.trans le_self_add)
    _ = lenT D₀ ξ k φ P a b := by rw [hsplit]; ring
    _ ≤ eT D₀ ξ k φ u v + δ := hPlen

end Shield

end SupercriticalConformalCovariance.BiLip.L51
