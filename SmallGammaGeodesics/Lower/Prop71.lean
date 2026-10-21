import SmallGammaGeodesics.Lower.Windows
import SmallGammaGeodesics.Lower.MobiusLaw
import SmallGammaGeodesics.Lower.Drift
import SmallGammaGeodesics.Lower.TV
import SmallGammaGeodesics.Core.Interfaces
import SmallGammaGeodesics.Geodesic.Basic
import SmallGammaGeodesics.Assembly.Scalar

/-!
# Proposition 7.1 (the lower bound), assembled against the interface `CC.MCInput` (packet P-L3)

Source: `source/small-parameter-lqg-geodesics.pdf`, §7, Proposition 7.1, in the corrected form of
planning audit GA4 (`planning/audits/GA4-sections-7-8.md`), "Details for later use", item **A8**
(with A2–A7). The Möbius covariance of internal metrics modulo constants (GA4 (MC)) enters as the
interface hypothesis `CC.MCInput` (rulings G10, G19; discharged by packet CC12).

Notation: `φ_θ = mobPhi θ`, `ψ_θ = mobPhi (-θ)`, `U_R = rectU 100 R`, `T_r = tube r`,
`W = B₅(0)`, `V = ψ_θ(U_R)`.

* `isMobius_mobPhi`, `isConfNbhd_mobPhi`, `mobPhi_image_image_rectU`: for `|θ| ≤ 1/10` and
  `R ≤ 10⁻³`, `φ_θ` is a Möbius map, holomorphic and injective on `W ⊇ closure V`, and
  `φ_θ(V) = U_R`; so `MCInput` applies to `(φ_θ, W, V)`.
* `confPull_mobPhi_eq`, `confPair0_mobPhi_eq`: the conformal pullback `CC.confPull` is the
  transport `mobTransport` of `Lower/MobiusLaw.lean` (both are `|φ_θ′|² (f ∘ φ_θ)` near `V`), so
  the pairing vector `CC.confPair0` of `h ∘ ψ_θ + Q log |ψ_θ′|` is the transported pairing vector
  shifted by `ψ ↦ ∫ ψ g`, for any test function `g` equal to `Q log |ψ_θ′|` on `U_R`.
* `exists_winEvent_ge` (A8, steps 1–3, for one map): a measurable event `E`, a.s. equal to the
  window event of `D_h(·,·;U_R)` for the window of radius `2r` around `tan(θ/2)/2`, with
  `P[η ⊆ T_r] ≤ P[E] + √(e^{‖g‖²_∇} − 1)`.
* `measure_subset_tube_le` (A8, for one γ): with `b = Q r^{3/2} ≤ 1`, `N = ⌊b^{-2/5}⌋` and
  `R = N r ≤ 10⁻³`, the events of `θ_k = 64 k r` (`k ≤ N`) are a.s. pairwise disjoint (W2, W3),
  so `P[η ⊆ T_r] ≤ 1/(N+1) + √(2 C_g) Q R^{3/2} ≤ (1 + √(2 C_g)) b^{2/5}`.
* `lowerBound71_of_MC`: the target `LowerBound71 P η`, with `C = 1 + √(2 C_g)` (`C_g` from
  `exists_bendingDrift`) and `r_* = 2·10^{-15/2}`.

Of the `σ₀` functional `d` provided by `MCInput`, only its measurability and its validity for
`h` itself (`CC.IsSigma0Metric` with `g = 0`) are used: the Cameron–Martin and law steps compare
events of the form `{d(·) ∈ B}` for one measurable `d`, and the covariance step uses the coupled
identity of `MCInput`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric

/-! ### The Möbius maps `φ_θ` satisfy the hypotheses of `CC.MCInput` -/

/-- `‖ψ_θ u‖ ≤ 5/2` for `‖u‖ ≤ 2` and `|θ| ≤ 1/10`. -/
theorem norm_mobPhi_neg_le {θ : ℝ} {u : ℂ} (hθ : |θ| ≤ 1 / 10) (hu : ‖u‖ ≤ 2) :
    ‖mobPhi (-θ) u‖ ≤ 5 / 2 := by
  have hden := one_sub_abs_mul_norm_le_norm_denom (-θ) u
  rw [abs_neg] at hden
  have h1 : |θ| * ‖u‖ ≤ 1 / 10 * 2 := mul_le_mul hθ hu (norm_nonneg u) (by norm_num)
  have hpos : (4 / 5 : ℝ) ≤ ‖1 + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - 1) * u‖ := by
    linarith
  unfold mobPhi
  rw [norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    div_le_iff₀ (by linarith)]
  linarith

/-- Points of `ψ_θ(U_R)` have norm at most `5/2`. -/
theorem norm_le_of_mem_image_rectU {R θ : ℝ} (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 1 / 10) {z : ℂ}
    (hz : z ∈ mobPhi (-θ) '' rectU 100 R) : ‖z‖ ≤ 5 / 2 := by
  obtain ⟨u, hu, rfl⟩ := hz
  exact norm_mobPhi_neg_le hθ (norm_le_two_of_mem_rectU hR hu)

/-- `φ_θ(ψ_θ(U_R)) = U_R`. -/
theorem mobPhi_image_image_rectU {R θ : ℝ} (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 1 / 10) :
    mobPhi θ '' (mobPhi (-θ) '' rectU 100 R) = rectU 100 R := by
  rw [image_image]
  refine ext fun z => ⟨?_, fun hz => ⟨z, hz, ?_⟩⟩
  · rintro ⟨u, hu, rfl⟩
    show mobPhi θ (mobPhi (-θ) u) ∈ rectU 100 R
    rwa [mobPhi_mobPhi_neg_of_norm_le hθ ((norm_le_two_of_mem_rectU hR hu).trans (by norm_num))]
  · exact mobPhi_mobPhi_neg_of_norm_le hθ ((norm_le_two_of_mem_rectU hR hz).trans (by norm_num))

/-- `ψ_θ(U_R) = B₅(0) ∩ φ_θ⁻¹(U_R)`. -/
theorem image_rectU_eq_inter_preimage {R θ : ℝ} (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 1 / 10) :
    mobPhi (-θ) '' rectU 100 R = Metric.ball 0 5 ∩ mobPhi θ ⁻¹' rectU 100 R := by
  refine ext fun z => ⟨fun hz => ⟨?_, ?_⟩, fun hz => ⟨mobPhi θ z, hz.2, ?_⟩⟩
  · rw [mem_ball_zero_iff]
    exact (norm_le_of_mem_image_rectU hR hθ hz).trans_lt (by norm_num)
  · rw [mem_preimage, ← mobPhi_image_image_rectU hR hθ]
    exact mem_image_of_mem _ hz
  · exact mobPhi_neg_mobPhi (mobDen_ne_zero_of_mem_ball hθ hz.1)

/-- `φ_θ` is complex differentiable on `B₅(0)` for `|θ| ≤ 1/10`. -/
theorem differentiableAt_mobPhi {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10)
    (hz : z ∈ Metric.ball (0 : ℂ) 5) : DifferentiableAt ℂ (mobPhi θ) z :=
  (hasDerivAt_mobPhi (mobDen_ne_zero_of_mem_ball hθ hz)).differentiableAt

/-- `φ_θ` is a Möbius map. -/
theorem isMobius_mobPhi (θ : ℝ) : CC.IsMobius (mobPhi θ) := by
  refine ⟨Complex.exp (θ * Complex.I), 0, Complex.exp (θ * Complex.I) - 1, 1, ?_, fun z => ?_⟩
  · rw [mul_one, zero_mul, sub_zero]
    exact Complex.exp_ne_zero _
  · rw [mobPhi, add_zero, add_comm (_ * z) 1]

/-- **The conformal neighbourhood** of §7: `φ_θ` is holomorphic and injective on `W = B₅(0)`,
which contains the closure of the bounded open set `V = ψ_θ(U_R)`. -/
theorem isConfNbhd_mobPhi {R θ : ℝ} (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 1 / 10) :
    CC.IsConfNbhd (mobPhi θ) (Metric.ball 0 5) (mobPhi (-θ) '' rectU 100 R) where
  isOpen_W := Metric.isOpen_ball
  isOpen_V := by
    rw [image_rectU_eq_inter_preimage hR hθ]
    exact ContinuousOn.isOpen_inter_preimage
      (fun z hz => (differentiableAt_mobPhi hθ hz).continuousAt.continuousWithinAt)
      Metric.isOpen_ball (isOpen_rectU 100 R)
  isBounded_V := (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 5 / 2)).subset fun z hz => by
    rw [mem_closedBall_zero_iff]
    exact norm_le_of_mem_image_rectU hR hθ hz
  closure_subset := by
    refine (closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by norm_num : (5 / 2 : ℝ) < 5))
    rw [mem_closedBall_zero_iff]
    exact norm_le_of_mem_image_rectU hR hθ hz
  differentiableOn z hz := (differentiableAt_mobPhi hθ hz).differentiableWithinAt
  injOn := (injOn_mobPhi θ).mono fun _ hz => mobDen_ne_zero_of_mem_ball hθ hz

/-! ### The conformal pullback of `CC.MCInput` is the transport of `Lower/MobiusLaw.lean` -/

section Pullback

variable {θ : ℝ} {U : Set ℂ}

/-- The transport `T f = (f ∘ φ_θ) |φ_θ′|²` on `ψ_θ(U)` is a conformal pullback of `f` by `φ_θ`
on `W = B₅(0)`, for `f` supported in `U ⊆ B̄₂(0)`. -/
theorem isConfPull_mobTransport_ball (hθ : |θ| ≤ 1 / 10) (hU2 : ∀ u ∈ U, ‖u‖ ≤ 2)
    (hW : U ⊆ Metric.ball 0 5) (f : TestC) (hf : tsupport (f : ℂ → ℝ) ⊆ U) :
    CC.IsConfPull (mobPhi θ) (Metric.ball 0 5) f (mobTransport hθ hW f hf) := by
  intro x
  rw [mobTransport_apply]
  by_cases hx : x ∈ Metric.ball (0 : ℂ) 5
  · rw [indicator_of_mem hx, mobTransportFun_eq hf (mobDen_ne_zero_of_mem_ball hθ hx), mul_comm]
  · rw [indicator_of_notMem hx]
    refine mobTransportFun_eq_zero hθ hW fun ⟨z, hz, hzx⟩ => hx ?_
    rw [← hzx, mem_ball_zero_iff]
    exact (norm_mobPhi_neg_le hθ (hU2 z (hf hz))).trans_lt (by norm_num)

/-- **The identification `confPull = mobTransport`** (packet P-L3, notes). -/
theorem confPull_mobPhi_eq (hθ : |θ| ≤ 1 / 10) (hU2 : ∀ u ∈ U, ‖u‖ ≤ 2)
    (hW : U ⊆ Metric.ball 0 5) (f : TestC) (hf : tsupport (f : ℂ → ℝ) ⊆ U) :
    CC.confPull (mobPhi θ) (Metric.ball 0 5) f = mobTransport hθ hW f hf := by
  have hP := isConfPull_mobTransport_ball hθ hU2 hW f hf
  have hex : ∃ τg : TestC, CC.IsConfPull (mobPhi θ) (Metric.ball 0 5) f τg := ⟨_, hP⟩
  unfold CC.confPull
  rw [dite_eq_left hex]
  exact TestFunction.ext fun x => (hex.choose_spec x).trans (hP x).symm

/-- `log ‖φ_θ′(ψ_θ z)‖ = −log ‖ψ_θ′(z)‖` on `B₅(0)`. -/
theorem log_norm_deriv_mobPhi_mobPhi_neg (hθ : |θ| ≤ 1 / 10) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 5) :
    Real.log ‖deriv (mobPhi θ) (mobPhi (-θ) z)‖ = -Real.log ‖deriv (mobPhi (-θ)) z‖ := by
  have h1 := norm_deriv_mobPhi_mobPhi_neg (θ := θ) (mobDen_neg_ne_zero_of_mem_ball hθ hz)
  have ha : ‖deriv (mobPhi θ) (mobPhi (-θ) z)‖ ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hb : ‖deriv (mobPhi (-θ)) z‖ ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h2 := Real.log_mul ha hb
  rw [h1, Real.log_one] at h2
  linarith

/-- **The `σ₀` pairing vector of `CC.MCInput` for `φ_θ`** is the transported pairing vector shifted
by a drift `g = Q log |ψ_θ′|` on `U = φ_θ(V)`:
`confPair0 γ φ_θ W V x ψ = ⟨x, T ψ⟩ + ∫ ψ g`. -/
theorem confPair0_mobPhi_eq {γ : ℝ} {V : Set ℂ} (hθ : |θ| ≤ 1 / 10)
    (hU2 : ∀ u ∈ mobPhi θ '' V, ‖u‖ ≤ 2) (hW : mobPhi θ '' V ⊆ Metric.ball 0 5) (g : TestC)
    (hg : ∀ z ∈ mobPhi θ '' V, g z = Q γ * Real.log ‖deriv (mobPhi (-θ)) z‖) (x : DistC)
    (ψ : TestC0On (mobPhi θ '' V)) :
    CC.confPair0 γ (mobPhi θ) (Metric.ball 0 5) V x ψ =
      x (mobTransport0 hθ hW ψ).1 + ∫ y, ψ.1.1 y * g y := by
  unfold CC.confPair0
  rw [confPull_mobPhi_eq hθ hU2 hW ψ.1.1 ψ.2, mobTransport0_coe, sub_eq_add_neg]
  congr 1
  have e1 : ∫ y, Real.log ‖deriv (mobPhi θ) y‖ * mobTransport hθ hW ψ.1.1 ψ.2 y =
      ∫ y, ψ.1.1 y * Real.log ‖deriv (mobPhi θ) (mobPhi (-θ) y)‖ := by
    refine (integral_congr_ae (ae_of_all _ fun y => ?_)).trans
      (integral_mobTransportFun_mul hθ hW ψ.2 fun y => Real.log ‖deriv (mobPhi θ) y‖)
    rw [mobTransport_apply, mul_comm]
  rw [e1, ← integral_const_mul, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  by_cases hy : y ∈ mobPhi θ '' V
  · rw [hg y hy, log_norm_deriv_mobPhi_mobPhi_neg hθ (hW hy)]
    ring
  · have h0 : ψ.1.1 y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (ψ.2 h)
    rw [h0]
    ring

end Pullback

/-! ### The shift by `0`; congruence of window events; the window sets `S_θ` -/

/-- `h + 0 = h`. -/
theorem addFun_testCont_zero (x : DistC) : addFun x (testCont 0) = x := by
  have h0 : testCont (0 : TestC) = 0 := ContinuousMap.ext fun _ => rfl
  rw [h0, addFun, GM.ofCont_zero_eq, add_zero]

/-- The window event only reads `d` on `U × U` when `0, 1 ∈ U` and `S ⊆ U`. -/
theorem winEvent_congr {d₁ d₂ : ℂ → ℂ → ℝ≥0∞} {U S : Set ℂ} (h0 : (0 : ℂ) ∈ U)
    (h1 : (1 : ℂ) ∈ U) (hS : S ⊆ U) (hd : ∀ z ∈ U, ∀ w ∈ U, d₁ z w = d₂ z w) :
    winEvent d₁ S ↔ winEvent d₂ S := by
  unfold winEvent
  rw [hd 0 h0 1 h1]
  refine and_congr_right fun _ => exists_congr fun δ => and_congr_right fun _ =>
    forall_congr' fun q => imp_congr_right fun hq => ?_
  rw [hd 0 h0 _ (hS hq), hd _ (hS hq) 1 h1]

/-- The midline set `(U_R ∩ L) \ J` of the window event `B_k` (GA4 A6), for the window `J` of
radius `2r` around `tan(θ/2)/2`. -/
def winSet (R r θ : ℝ) : Set ℂ :=
  (rectU 100 R ∩ {z | z.re = 1 / 2}) \ window (Real.tan (θ / 2) / 2) (2 * r)

theorem winSet_subset_rectU (R r θ : ℝ) : winSet R r θ ⊆ rectU 100 R := fun _ hz => hz.1.1

/-! ### Steps 1–3 of A8 for one Möbius map -/

/-- **A8, steps 1–3, for one map `φ_θ`.** Let `D` be a strong γ-LQG metric satisfying the Möbius
covariance `CC.MCInput D γ`, `h` a whole-plane GFF, `η` an a.s. `D_h`-geodesic from `0` to `1`,
`0 < r ≤ R ≤ 10⁻³`, `|θ| ≤ 64 R`, and `g` a test function equal to `Q log |ψ_θ′|` on `U_R`.
Then there is a measurable event `E`, a.s. equal to the window event `B_θ` of the internal metric
`D_h(·,·;U_R)` (for the window of radius `2r` around `tan(θ/2)/2`), with
`P[η ⊆ T_r] ≤ P[E] + √(e^{‖g‖²_∇} − 1)`.

The proof is the chain of GA4 A8: on `{η ⊆ T_r}` the window event holds for the `σ₀(U_R)`
functional `d` of `MCInput` evaluated at the pairings of `h ∘ ψ_θ + Q log |ψ_θ′|` (A7); these
pairings are those of the transport `T` of `Lower/MobiusLaw.lean` shifted by `g`
(`confPair0_mobPhi_eq`); their law is that of the pairings of `h + g` (A3,
`map_mobTransport0_add_eq`); the Cameron–Martin bound (A5) compares `h + g` with `h`; and for `h`
itself `d` is a.s. a positive multiple of `D_h(·,·;U_R)` (`CC.IsSigma0Metric` with `g = 0`, W2). -/
theorem exists_winEvent_ge {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) (hMC : CC.MCInput D γ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {η : Ω → C(unitInterval, ℂ)} (hη : ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D (h ω)) 0 1 (η ω))
    {r R θ : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R)
    (g : TestC) (hg : ∀ z ∈ rectU 100 R, g z = Q γ * Real.log ‖deriv (mobPhi (-θ)) z‖) :
    ∃ E : Set Ω, MeasurableSet E ∧
      (∀ᵐ ω ∂P, ω ∈ E ↔ winEvent ((D (h ω)).internal (rectU 100 R)) (winSet R r θ)) ∧
      P.real {ω | ∀ t, η ω t ∈ tube r} ≤
        P.real E + Real.sqrt (Real.exp (gradEnergy g) - 1) := by
  have hθ' : |θ| ≤ 1 / 10 := abs_le_tenth_of_abs_le hR hθ
  have hR0 : 0 < R := hr.trans_le hrR
  have hKR : (0 : ℝ) < 100 * R := by linarith
  set V := mobPhi (-θ) '' rectU 100 R
  set U' := mobPhi θ '' V
  have hU' : U' = rectU 100 R := mobPhi_image_image_rectU hR hθ'
  have hU2 : ∀ u ∈ U', ‖u‖ ≤ 2 := fun u hu => norm_le_two_of_mem_rectU hR (hU' ▸ hu)
  have hW : U' ⊆ Metric.ball 0 5 := hU' ▸ rectU_subset_ball hR
  have h0U : (0 : ℂ) ∈ U' := hU' ▸ zero_mem_rectU hKR
  have h1U : (1 : ℂ) ∈ U' := hU' ▸ one_mem_rectU hKR
  have hSU : winSet R r θ ⊆ U' := hU' ▸ winSet_subset_rectU R r θ
  have hgU' : ∀ z ∈ U', g z = Q γ * Real.log ‖deriv (mobPhi (-θ)) z‖ :=
    fun z hz => hg z (hU' ▸ hz)
  obtain ⟨d, ⟨hdm, hdσ⟩, hdMC⟩ :=
    hMC (mobPhi θ) (Metric.ball 0 5) V (isMobius_mobPhi θ) (isConfNbhd_mobPhi hR hθ')
  -- the events, as preimages of measurable sets of pairing vectors
  have hdzw : ∀ z w : ℂ, Measurable fun v : TestC0On U' → ℝ => d v z w := fun z w =>
    (measurable_pi_apply w).comp ((measurable_pi_apply z).comp hdm)
  set B : Set (TestC0On U' → ℝ) := {v | winEvent (d v) (winSet R r θ)}
  have hB : MeasurableSet B := measurableSet_winEvent d hdzw _
  have hres : Measurable fun (ξ : TestC0 → ℝ) (ψ : TestC0On U') => ξ ψ.1 :=
    measurable_pi_iff.2 fun (ψ : TestC0On U') => measurable_pi_apply ψ.1
  set A : Set (TestC0 → ℝ) := (fun (ξ : TestC0 → ℝ) (ψ : TestC0On U') => ξ ψ.1) ⁻¹' B
  have hA : MeasurableSet A := hres hB
  have hm0 : Measurable fun ω => pair0 (h ω) := measurable_pair0.comp hh.measurable
  refine ⟨(fun ω => pair0 (h ω)) ⁻¹' A, hm0 hA, ?_, ?_⟩
  · -- for `h` itself, `d` is a.s. a positive multiple of `D_h(·,·;U_R)` (W2)
    filter_upwards [hdσ P h 0 hh] with ω ⟨c, hc0, hct, hc⟩
    rw [addFun_testCont_zero] at hc
    show winEvent (d (CC.pair0On U' (h ω))) (winSet R r θ) ↔ _
    rw [← winEvent_smul_iff (d (CC.pair0On U' (h ω))) _ hc0.ne' hct.ne, ← hU']
    exact winEvent_congr h0U h1U hSU fun z hz w hw => (hc z hz w hw).symm
  · -- Step 3 (covariance, A7): on `{η ⊆ T_r}` the window event holds for the transformed field
    set Bc : Set Ω :=
      {ω | winEvent (d (CC.confPair0 γ (mobPhi θ) (Metric.ball 0 5) V (h ω))) (winSet R r θ)}
    have hle1 : P {ω | ∀ t, η ω t ∈ tube r} ≤ P Bc := by
      refine measure_mono_ae ?_
      filter_upwards [hD.length P h (GM.isGFFPlusCont_of_isWholePlaneGFF hh),
        ae_exists_geod01_all hγ hγ2 hD P h hh, ae_existsUnique_geod01 hγ hγ2 hD P h hh 0 1, hη,
        hdMC P h hh] with ω hlen hgeo huniq hηω hcω hω
      obtain ⟨c, hc0, hct, hc⟩ := hcω
      exact winEvent_of_geod_subset_tube (D (h ω)) hlen hgeo hηω
        (fun η' hη' => huniq.unique hη' hηω) hr hrR hR hθ hω hc0.ne' hct.ne hc
    -- the pairing vector of the transformed field is the transported one, shifted by `g`
    set c : TestC0On U' → ℝ := fun ψ => ∫ y, ψ.1.1 y * g y
    set X : Ω → TestC0On U' → ℝ := fun ω ψ => h ω (mobTransport0 hθ' hW ψ).1 + c ψ
    set Y : Ω → TestC0On U' → ℝ := fun ω ψ => h ω ψ.1.1 + c ψ
    have hBcX : Bc = X ⁻¹' B := by
      ext ω
      have e : CC.confPair0 γ (mobPhi θ) (Metric.ball 0 5) V (h ω) = X ω :=
        funext fun ψ => confPair0_mobPhi_eq hθ' hU2 hW g hgU' (h ω) ψ
      show winEvent (d _) _ ↔ winEvent (d _) _
      rw [e]
    have hXm : Measurable X := measurable_pi_iff.2 fun ψ =>
      ((GFFInv.measurable_pair _).comp hh.measurable).add_const _
    have hYm : Measurable Y := measurable_pi_iff.2 fun ψ =>
      ((GFFInv.measurable_pair _).comp hh.measurable).add_const _
    -- Step 2 (law, A3)
    have hlaw : P (X ⁻¹' B) = P (Y ⁻¹' B) := by
      rw [← Measure.map_apply hXm hB, ← Measure.map_apply hYm hB,
        map_mobTransport0_add_eq hh hθ' hW c]
    -- `Y` is the restricted pairing vector of `h + g`
    have hpair : (fun ω => pair0 (addFun (h ω) (testCont g))) =
        fun ω (ψ : TestC0) => pair0 (h ω) ψ + ∫ x, ψ.1 x * g x :=
      funext fun ω => funext fun ψ => pair0_addFun (h ω) g ψ
    have hm1 : Measurable fun ω => pair0 (addFun (h ω) (testCont g)) := by
      rw [hpair]
      exact measurable_pi_iff.2 fun ψ =>
        ((measurable_pi_apply ψ).comp hm0).add_const _
    have hYA : Y ⁻¹' B = (fun ω => pair0 (addFun (h ω) (testCont g))) ⁻¹' A := by
      ext ω
      show Y ω ∈ B ↔ (fun ψ : TestC0On U' => pair0 (addFun (h ω) (testCont g)) ψ.1) ∈ B
      have e : (fun ψ : TestC0On U' => pair0 (addFun (h ω) (testCont g)) ψ.1) = Y ω :=
        funext fun ψ => pair0_addFun (h ω) g ψ.1
      rw [e]
    -- Step 1 (total variation, A5)
    have hTV := abs_lawPair0_addFun_sub_le hh g A hA
    have e2 : (lawPair0 (fun ω => addFun (h ω) (testCont g)) P).real A =
        P.real ((fun ω => pair0 (addFun (h ω) (testCont g))) ⁻¹' A) := by
      rw [lawPair0, measureReal_def, measureReal_def, Measure.map_apply hm1 hA]
    have e3 : (lawPair0 h P).real A = P.real ((fun ω => pair0 (h ω)) ⁻¹' A) := by
      rw [lawPair0, measureReal_def, measureReal_def, Measure.map_apply hm0 hA]
    rw [e2, e3] at hTV
    have hTV' := (abs_sub_le_iff.1 hTV).1
    calc P.real {ω | ∀ t, η ω t ∈ tube r} ≤ P.real Bc :=
          ENNReal.toReal_mono (measure_ne_top P _) hle1
      _ = P.real ((fun ω => pair0 (addFun (h ω) (testCont g))) ⁻¹' A) := by
          rw [measureReal_def, measureReal_def, hBcX, hlaw, hYA]
      _ ≤ P.real ((fun ω => pair0 (h ω)) ⁻¹' A) +
            Real.sqrt (Real.exp (gradEnergy g) - 1) := by linarith

/-! ### The arithmetic of A8 -/

/-- `Q = 2/γ + γ/2 ≥ 2` for `γ > 0`. -/
theorem two_le_Q {γ : ℝ} (hγ : 0 < γ) : 2 ≤ Q γ := by
  unfold Q
  rw [div_add_div _ _ hγ.ne' two_ne_zero, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (γ - 2)]

/-- The Cameron–Martin term of A8, step 1: if `p ≤ q + √(e^E − 1)`, `p ≤ 1`, `q, E, T ≥ 0` and
`2E ≤ T²`, then `p ≤ q + T`. For `E ≤ 1` use `e^E − 1 ≤ 2E`; for `E > 1`, `T > 1 ≥ p`. -/
theorem le_add_of_le_add_sqrt_exp {p q E T : ℝ} (hp : p ≤ q + Real.sqrt (Real.exp E - 1))
    (hp1 : p ≤ 1) (hq : 0 ≤ q) (hE : 0 ≤ E) (hT : 0 ≤ T) (hET : 2 * E ≤ T ^ 2) :
    p ≤ q + T := by
  by_cases hE1 : E ≤ 1
  · have h1 : Real.sqrt (Real.exp E - 1) ≤ T := by
      calc Real.sqrt (Real.exp E - 1) ≤ Real.sqrt (2 * E) :=
            Real.sqrt_le_sqrt (exp_sub_one_le_two_mul hE hE1)
        _ ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt hET
        _ = T := Real.sqrt_sq hT
    linarith
  · have hT1 : 1 < T := by
      by_contra hcon
      have hcon' : T ≤ 1 := not_lt.1 hcon
      have hE1' : 1 < E := not_le.1 hE1
      nlinarith
    linarith

/-- `(Q r^{3/2})^{-2/5} r = (r/Q)^{2/5} ≤ 10⁻³` for `Q ≥ 2` and `0 < r ≤ r_* = 2·10^{-15/2}`
(A8: `R = N r ≤ R₀`). -/
theorem rpow_neg_two_fifths_mul_le {Q r : ℝ} (hQ : 2 ≤ Q) (hr : 0 < r)
    (hrs : r ≤ 2 * (1 / 1000) ^ (5 / 2 : ℝ)) :
    (Q * r ^ (3 / 2 : ℝ)) ^ (-(2 / 5) : ℝ) * r ≤ 1 / 1000 := by
  have hQ0 : 0 < Q := by linarith
  have e : (Q * r ^ (3 / 2 : ℝ)) ^ (-(2 / 5) : ℝ) * r = (r / Q) ^ (2 / 5 : ℝ) := by
    rw [Real.mul_rpow hQ0.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
      Real.div_rpow hr.le hQ0.le, Real.rpow_neg hQ0.le]
    have h1 : r ^ ((3 / 2 : ℝ) * (-(2 / 5))) * r = r ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_add_one hr.ne']
      norm_num
    rw [mul_assoc, h1, inv_mul_eq_div]
  rw [e]
  have h1 : r / Q ≤ (1 / 1000) ^ (5 / 2 : ℝ) := by
    rw [div_le_iff₀ hQ0]
    have : 0 ≤ (1 / 1000 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  calc (r / Q) ^ (2 / 5 : ℝ) ≤ ((1 / 1000 : ℝ) ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) :=
        Real.rpow_le_rpow (div_pos hr hQ0).le h1 (by norm_num)
    _ = 1 / 1000 := by
        rw [← Real.rpow_mul (by norm_num)]
        norm_num

/-- The choice `N = ⌊b^{-2/5}⌋` of A8, step 5, for `0 < b ≤ 1`: `N ≥ 1`, `N ≤ b^{-2/5}`,
`1/(N+1) ≤ b^{2/5}` and `N^{3/2} b ≤ b^{2/5}`. -/
theorem floor_rpow_facts {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    1 ≤ ⌊b ^ (-(2 / 5) : ℝ)⌋₊ ∧ (⌊b ^ (-(2 / 5) : ℝ)⌋₊ : ℝ) ≤ b ^ (-(2 / 5) : ℝ) ∧
      1 / ((⌊b ^ (-(2 / 5) : ℝ)⌋₊ : ℝ) + 1) ≤ b ^ (2 / 5 : ℝ) ∧
      (⌊b ^ (-(2 / 5) : ℝ)⌋₊ : ℝ) ^ (3 / 2 : ℝ) * b ≤ b ^ (2 / 5 : ℝ) := by
  set x := b ^ (-(2 / 5) : ℝ) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb0 hb1 (by norm_num)
  have hx0 : 0 ≤ x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hx1)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hxinv : x⁻¹ = b ^ (2 / 5 : ℝ) := by rw [hx, Real.rpow_neg hb0.le, inv_inv]
  refine ⟨hN1, hNx, ?_, ?_⟩
  · rw [← hxinv, one_div]
    exact inv_anti₀ (by linarith) hxN.le
  · calc (⌊x⌋₊ : ℝ) ^ (3 / 2 : ℝ) * b ≤ x ^ (3 / 2 : ℝ) * b :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num))
            hb0.le
      _ = b ^ (2 / 5 : ℝ) := by
          rw [hx, ← Real.rpow_mul hb0.le, ← Real.rpow_add_one hb0.ne']
          norm_num

/-! ### Proposition 7.1 -/

/-- **Proposition 7.1 for one γ** (GA4 A8), for a strong γ-LQG metric `D` with the Möbius
covariance `CC.MCInput D γ`, any whole-plane GFF `h` and any a.s. geodesic `η` from `0` to `1`:
`P[η ⊆ T_r] ≤ (1 + √(2 C_g)) (Q r^{3/2})^{2/5}` for `0 < r ≤ r_* = 2·10^{-15/2}`, where `C_g` is
any constant for the bending drifts of (7.4) (`exists_bendingDrift`). -/
theorem measure_subset_tube_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) (hMC : CC.MCInput D γ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {η : Ω → C(unitInterval, ℂ)} (hη : ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D (h ω)) 0 1 (η ω))
    {Cg : ℝ} (hCg : 0 < Cg)
    (hdrift : ∀ Q : ℝ, 0 ≤ Q → ∀ R θ : ℝ, 0 < R → R ≤ 1 / 1000 → |θ| ≤ 64 * R →
      ∃ g : TestC, (∀ z ∈ rectU 100 R, g z = Q * Real.log ‖deriv (mobPhi (-θ)) z‖) ∧
        gradEnergy ⇑g ≤ Cg * Q ^ 2 * R ^ 3)
    {r : ℝ} (hr : 0 < r) (hrs : r ≤ 2 * (1 / 1000) ^ (5 / 2 : ℝ)) :
    P {ω | ∀ t, η ω t ∈ tube r} ≤
      ENNReal.ofReal ((1 + Real.sqrt (2 * Cg)) * (Q γ * r ^ (3 / 2 : ℝ)) ^ (2 / 5 : ℝ)) := by
  set C₁ := Real.sqrt (2 * Cg)
  have hC₁0 : 0 ≤ C₁ := Real.sqrt_nonneg _
  set A := {ω | ∀ t, η ω t ∈ tube r}
  set b := Q γ * r ^ (3 / 2 : ℝ) with hbdef
  have hQ2 : 2 ≤ Q γ := two_le_Q hγ
  have hb0 : 0 < b := mul_pos (by linarith) (Real.rpow_pos_of_pos hr _)
  rw [← ENNReal.ofReal_toReal (measure_ne_top P A)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpA1 : P.real A ≤ 1 := measureReal_le_one
  by_cases hb1 : 1 < b
  · -- trivial case `b > 1`
    have h1 : 1 ≤ b ^ (2 / 5 : ℝ) := Real.one_le_rpow hb1.le (by norm_num)
    have h2 : 1 ≤ 1 + C₁ := by linarith
    calc (P A).toReal ≤ 1 := hpA1
      _ ≤ (1 + C₁) * b ^ (2 / 5 : ℝ) := by nlinarith
  have hb1' : b ≤ 1 := not_lt.1 hb1
  obtain ⟨hN1, hNx, hN3, hN4⟩ := floor_rpow_facts hb0 hb1'
  set N := ⌊b ^ (-(2 / 5) : ℝ)⌋₊
  set R : ℝ := N * r with hRdef
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hR0 : 0 < R := mul_pos (by linarith) hr
  have hrR : r ≤ R := by
    rw [hRdef]
    nlinarith
  have hR1 : R ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_right hNx hr.le).trans (rpow_neg_two_fifths_mul_le hQ2 hr hrs)
  have hKR : (0 : ℝ) < 100 * R := by linarith
  -- steps 1–3 for each `θ_k = 64 k r`, `k ≤ N`
  have hk : ∀ k ∈ Finset.range (N + 1), ∃ E : Set Ω, MeasurableSet E ∧
      (∀ᵐ ω ∂P, ω ∈ E ↔
        winEvent ((D (h ω)).internal (rectU 100 R)) (winSet R r (64 * (k : ℝ) * r))) ∧
      P.real A ≤ P.real E + C₁ * (Q γ * R ^ (3 / 2 : ℝ)) := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hθ : |64 * (k : ℝ) * r| ≤ 64 * R := by
      rw [abs_of_nonneg (by positivity), hRdef]
      nlinarith
    obtain ⟨g, hg, hgE⟩ := hdrift (Q γ) (by linarith) R _ hR0 hR1 hθ
    obtain ⟨E, hEm, hEiff, hEle⟩ := exists_winEvent_ge hγ hγ2 hD hMC hh hη hr hrR hR1 hθ g hg
    refine ⟨E, hEm, hEiff, le_add_of_le_add_sqrt_exp hEle hpA1 measureReal_nonneg
      (gradEnergy_nonneg _) (by positivity) ?_⟩
    have hsq : (C₁ * (Q γ * R ^ (3 / 2 : ℝ))) ^ 2 = 2 * Cg * Q γ ^ 2 * R ^ 3 := by
      have hR3 : (R ^ (3 / 2 : ℝ)) ^ 2 = R ^ 3 := by
        rw [← Real.rpow_natCast (R ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hR0.le,
          ← Real.rpow_natCast R 3]
        norm_num
      rw [mul_pow, mul_pow, hR3, Real.sq_sqrt (by positivity)]
      ring
    rw [hsq]
    linarith
  choose! E hEm hEiff hEle using hk
  -- step 4: the events are a.s. pairwise disjoint (W2, W3)
  have hdisj : Set.Pairwise (↑(Finset.range (N + 1))) (Function.onFun (AEDisjoint P) E) := by
    intro j hj k hk hjk
    have hj' : j ∈ Finset.range (N + 1) := hj
    have hk' : k ∈ Finset.range (N + 1) := hk
    have hπ : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj')
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk')
    have hj32 : 32 * (j : ℝ) * r < Real.pi / 2 := by
      have : 32 * (j : ℝ) * r ≤ 32 * R := by rw [hRdef]; nlinarith
      linarith
    have hk32 : 32 * (k : ℝ) * r < Real.pi / 2 := by
      have : 32 * (k : ℝ) * r ≤ 32 * R := by rw [hRdef]; nlinarith
      linarith
    show P (E j ∩ E k) = 0
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hEiff j hj', hEiff k hk',
      hD.length P h (GM.isGFFPlusCont_of_isWholePlaneGFF hh)] with ω hωj hωk hlen hω
    exact not_winEvent_and_winEvent (D (h ω)) hlen hKR
      (window_centres_separated hr hjk hj32 hk32) ⟨hωj.1 hω.1, hωk.1 hω.2⟩
  have hsum : ∑ k ∈ Finset.range (N + 1), P.real (E k) ≤ 1 := by
    have h1 := sum_measure_le_measure_univ (fun i hi => (hEm i hi).nullMeasurableSet) hdisj
    have h2 := ENNReal.toReal_mono (measure_ne_top P univ) h1
    rwa [ENNReal.toReal_sum (fun k _ => measure_ne_top P (E k)), measure_univ,
      ENNReal.toReal_one] at h2
  have hsumle : ((N : ℝ) + 1) * P.real A ≤ 1 + ((N : ℝ) + 1) * (C₁ * (Q γ * R ^ (3 / 2 : ℝ))) := by
    have h1 := Finset.sum_le_sum hEle
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    push_cast at h1
    linarith
  -- step 5: optimisation
  have hp : P.real A ≤ 1 / ((N : ℝ) + 1) + C₁ * (Q γ * R ^ (3 / 2 : ℝ)) := by
    have hN0 : (0 : ℝ) < N + 1 := by positivity
    rw [div_add' _ _ _ hN0.ne', le_div_iff₀ hN0]
    linarith
  have hQR : Q γ * R ^ (3 / 2 : ℝ) ≤ b ^ (2 / 5 : ℝ) := by
    rw [hRdef, Real.mul_rpow (Nat.cast_nonneg _) hr.le]
    calc Q γ * ((N : ℝ) ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) = (N : ℝ) ^ (3 / 2 : ℝ) * b := by
          rw [hbdef]
          ring
      _ ≤ b ^ (2 / 5 : ℝ) := hN4
  calc (P A).toReal = P.real A := rfl
    _ ≤ 1 / ((N : ℝ) + 1) + C₁ * (Q γ * R ^ (3 / 2 : ℝ)) := hp
    _ ≤ b ^ (2 / 5 : ℝ) + C₁ * b ^ (2 / 5 : ℝ) :=
        add_le_add hN3 (mul_le_mul_of_nonneg_left hQR hC₁0)
    _ = (1 + C₁) * b ^ (2 / 5 : ℝ) := by ring

/-- **Proposition 7.1** (source §7; GA4 A8), assembled against the Möbius covariance interface
`CC.MCInput` (ruling G10; discharged by packet CC12): for the canonical γ-LQG metrics `D γ`, the
normalized whole-plane GFF `h` and any a.s. geodesics `η γ` from `0` to `1`, there are numerical
`C` and `r_*` with `P[M_γ ≤ r] ≤ C (Q r^{3/2})^{2/5}` for all `γ ∈ (0,2)` and `r ∈ (0, r_*]`.
Constants: `r_* = 2·10^{-15/2}` and `C = 1 + √(2 C_g)`, `C_g` from `exists_bendingDrift`. -/
theorem lowerBound71_of_MC (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → GaussianLQG.IsCanonicalLQGMetric γ (D γ))
    (hMC : ∀ γ, 0 < γ → γ < 2 → CC.MCInput (D γ) γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, LQGMetric.Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)) :
    LowerBound71 P η := by
  obtain ⟨Cg, hCg, hdrift⟩ := exists_bendingDrift
  refine ⟨1 + Real.sqrt (2 * Cg), 2 * (1 / 1000) ^ (5 / 2 : ℝ), by positivity, by positivity, ?_⟩
  intro γ hγ hγ2 r hr
  have hset : {ω | maxDev (η γ ω) ≤ r} = {ω | ∀ t, η γ ω t ∈ tube r} :=
    ext fun ω => maxDev_le_iff_forall_mem_tube (η γ ω) r
  rw [hset]
  exact measure_subset_tube_le hγ hγ2 (hD γ hγ hγ2).1 (hMC γ hγ hγ2) hh.1 (hη γ hγ hγ2) hCg
    (fun Q hQ R θ hR hR1 hθ => (hdrift Q hQ R θ hR hR1 hθ).imp fun _ hg => ⟨hg.1, hg.2.2⟩)
    hr.1 hr.2

end SmallGammaGeodesics
