import SmallGammaGeodesics.Upper.Defs
import SmallGammaGeodesics.Upper.ProbeInv
import SmallGammaGeodesics.Upper.CompetitorWeyl
import SmallGammaGeodesics.CC.Coupling
import SmallGammaGeodesics.CC.ConfMetric

/-!
# The competitor (5.3)–(5.4′) (blueprint `lem:competitor`; BP2 details D2, D3, D5; packet P-U2)

For a probe map `ϕ = ϕ_{j,a,θ}` with `|θ| ≤ ε_c ℓ_j`, a strong γ-LQG metric `D` with the one-sided
conformal covariance `CC.ConfCovLE γ D` (interface, ruling G10), and a coupling `(h, h̄, K)` with
the clauses (b3), (b5) of Lemma 4.2′, `competitor_probe` bounds, for a.e. `ω` such that the
geodesic `η` stays in `{|Re z − 1/2| ≤ 9/16, |Im z| ≤ ℓ_j/16}`,
`ξ G_θ(h) + Z_b(h̄) − Z_b(h) ≤ log ∫₀¹ exp(p log|ϕ'(η(t))|) dt + 2ξ sup_{V_j} |K|`.

Proof (blueprint, Steps 1–8):
* the conformal setting `W = S_j`, `V = S_j ∩ ϕ⁻¹(V_j)` (`isConfNbhd_probeDomV`), with the
  localization `mem_probeDomV`;
* the cutoff `β` (`CC.IsConfNbhd.exists_cutoff` for `(id, ϕ(W) ∩ U_j, ϕ(V))`) and the measurable
  random continuous function `f = β · (K − Q log|ϕ' ∘ ψ|)` (equal to `K + Q log|ψ'|` on `ϕ(W)`);
* the coupling `IsConfCoupling` from (b3) and `CC.IsConfPull.integral_log_mul`;
* `ConfCovLE`, then `D_{h̄+f}(ϕη(s), ϕη(t)) ≤ (t − s) D_h(0,1)` from `isGeod01_restrictPath` and
  `GM.internal_le_of_isGeod01`;
* Weyl scaling `e^{-ξ f}·D_{h̄+f} = D_{h̄}` and `dist_le_mul_integral_exp_of_weyl`;
* the pairing identity (b5) and `|∫ K dλ| ≤ sup_{V_j} |K|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Function
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## Products with a cutoff -/

/-- If `u` is continuous on an open set `O` and `v` is continuous with `tsupport v ⊆ O`, then
`v · u` is continuous (it vanishes near every point off `O`). -/
theorem continuous_mul_of_continuousOn_of_tsupport {u v : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hu : ContinuousOn u O) (hv : Continuous v) (hsupp : tsupport v ⊆ O) :
    Continuous fun y => v y * u y := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y ∈ O
  · exact hv.continuousAt.mul (hu.continuousAt (hO.mem_nhds hy))
  · have hy' : y ∉ tsupport v := fun h => hy (hsupp h)
    have hev : v =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 hy'
    have hz : ∀ᶠ x in 𝓝 y, v x * u x = 0 := hev.mono fun x hx => by
      rw [hx, Pi.zero_apply, zero_mul]
    have hy0 : v y * u y = 0 := by rw [hz.self_of_nhds]
    rw [ContinuousAt, hy0]
    exact tendsto_const_nhds.congr' (hz.mono fun x hx => hx.symm)

/-- `u · v` is integrable when `u` is continuous on an open `O ⊇ tsupport v` and `v` is a
continuous compactly supported function. -/
theorem integrable_mul_of_continuousOn_of_tsupport {u v : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hu : ContinuousOn u O) (hv : Continuous v) (hvc : HasCompactSupport v)
    (hsupp : tsupport v ⊆ O) : Integrable (fun y => u y * v y) := by
  have hc : Continuous fun y => u y * v y := by
    have := continuous_mul_of_continuousOn_of_tsupport hO hu hv hsupp
    simpa only [mul_comm] using this
  exact hc.integrable_of_hasCompactSupport (hvc.mul_left (f := u))

/-! ## The rectangles -/

theorem isOpen_probeRectU (j : ℕ) : IsOpen (probeRectU j) := by
  have h1 : IsOpen {z : ℂ | z.re ∈ Ioo (-1 / 4 : ℝ) (5 / 4)} :=
    isOpen_Ioo.preimage Complex.continuous_re
  have h2 : IsOpen {z : ℂ | |z.im| < ell j / 4} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

theorem isOpen_probeRectV (j : ℕ) : IsOpen (probeRectV j) := by
  have h1 : IsOpen {z : ℂ | z.re ∈ Ioo (-1 / 8 : ℝ) (9 / 8)} :=
    isOpen_Ioo.preimage Complex.continuous_re
  have h2 : IsOpen {z : ℂ | |z.im| < ell j / 8} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

/-- `closure V_j ⊆ [-1/8, 9/8] × [-ℓ/8, ℓ/8]`. -/
theorem closure_probeRectV_subset (j : ℕ) :
    closure (probeRectV j) ⊆ {z : ℂ | z.re ∈ Icc (-1 / 8 : ℝ) (9 / 8) ∧ |z.im| ≤ ell j / 8} := by
  refine closure_minimal (fun z hz => ⟨Ioo_subset_Icc_self hz.1, le_of_lt hz.2⟩) ?_
  have h1 : IsClosed {z : ℂ | z.re ∈ Icc (-1 / 8 : ℝ) (9 / 8)} :=
    isClosed_Icc.preimage Complex.continuous_re
  have h2 : IsClosed {z : ℂ | |z.im| ≤ ell j / 8} :=
    isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

theorem closure_probeRectV_subset_U (j : ℕ) : closure (probeRectV j) ⊆ probeRectU j := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3⟩ := closure_probeRectV_subset j hz
  have hℓ := ell_pos j
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

theorem probeRectV_subset_U (j : ℕ) : probeRectV j ⊆ probeRectU j :=
  subset_closure.trans (closure_probeRectV_subset_U j)

theorem isBounded_probeRectV (j : ℕ) : Bornology.IsBounded (probeRectV j) := by
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset fun z hz => ?_
  rw [mem_closedBall, dist_zero_right]
  have hℓ1 := ell_le_one j
  have hre : |z.re| ≤ 9 / 8 := abs_le.2 ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |z.im| ≤ 1 := by linarith [hz.2]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 3 := by linarith

theorem isCompact_closure_probeRectV (j : ℕ) : IsCompact (closure (probeRectV j)) :=
  (isBounded_probeRectV j).isCompact_closure

/-! ## The supremum of `|K|` over `V_j` -/

theorem iSup_probeRectV_nonneg (j : ℕ) (K : ℂ → ℝ) : 0 ≤ ⨆ w ∈ probeRectV j, |K w| :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

theorem abs_le_iSup_probeRectV {j : ℕ} {K : ℂ → ℝ} (hK : ContinuousOn K (probeRectU j)) {w : ℂ}
    (hw : w ∈ probeRectV j) : |K w| ≤ ⨆ w ∈ probeRectV j, |K w| := by
  obtain ⟨B, hB⟩ := (isCompact_closure_probeRectV j).exists_bound_of_continuousOn
    (hK.mono (closure_probeRectV_subset_U j))
  have hbdd : BddAbove (range fun w => ⨆ (_ : w ∈ probeRectV j), |K w|) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Real.iSup_le (fun hx => (hB x (subset_closure hx)).trans (le_max_left _ _))
      (le_max_right _ _)
  calc |K w| = ⨆ (_ : w ∈ probeRectV j), |K w| := (ciSup_pos (f := fun _ => |K w|) hw).symm
    _ ≤ ⨆ w ∈ probeRectV j, |K w| := le_ciSup hbdd w

/-- `|∫ K dλ| ≤ sup_{V_j} |K|` for the uniform measure `λ` on `[0,1] ⊆ V_j`. -/
theorem abs_integral_segMeasure_le {j : ℕ} {K : ℂ → ℝ} (hK : ContinuousOn K (probeRectU j))
    (hKm : Measurable K) :
    |∫ w, K w ∂(segMeasure 0 1)| ≤ ⨆ w ∈ probeRectV j, |K w| := by
  set S := ⨆ w ∈ probeRectV j, |K w|
  have hmap : Measurable fun u : ℝ => ((1 - u : ℝ) : ℂ) * 0 + (u : ℂ) * 1 := by fun_prop
  have hae : ∀ᵐ w ∂(segMeasure 0 1), ‖K w‖ ≤ S := by
    rw [segMeasure, ae_map_iff hmap.aemeasurable (measurableSet_le hKm.norm measurable_const)]
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun u hu => ?_)
    rw [Real.norm_eq_abs]
    refine abs_le_iSup_probeRectV hK ?_
    have hℓ := ell_pos j
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> linarith [hu.1, hu.2]
  have h := norm_integral_le_of_norm_le_const hae
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-! ## The conformal domain `V = S_j ∩ ϕ⁻¹(V_j)` -/

/-- The domain `V = S_j ∩ ϕ⁻¹(V_j)` of the conformal setting (BP2 D2). -/
def probeDomV (j : ℕ) (a θ : ℝ) : Set ℂ := probeStrip j ∩ probeMap j a θ ⁻¹' probeRectV j

theorem continuous_probeMap (j : ℕ) (a θ : ℝ) : Continuous (probeMap j a θ) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_probeMap j a θ z).continuousAt

theorem differentiable_probeMap (j : ℕ) (a θ : ℝ) : Differentiable ℂ (probeMap j a θ) :=
  fun z => (hasDerivAt_probeMap j a θ z).differentiableAt

theorem deriv_probeMap_eq (j : ℕ) (a θ : ℝ) :
    deriv (probeMap j a θ) = fun z => 1 + Complex.I * θ * deriv (probeH j a) z := by
  funext z
  exact (hasDerivAt_probeMap j a θ z).deriv

theorem continuous_deriv_probeMap (j : ℕ) (a θ : ℝ) : Continuous (deriv (probeMap j a θ)) := by
  rw [deriv_probeMap_eq]
  exact continuous_const.add (continuous_const.mul (continuous_deriv_probeH j a))

/-- The image of `V` lies in `V_j`. -/
theorem image_probeDomV_subset (j : ℕ) (a θ : ℝ) :
    probeMap j a θ '' probeDomV j a θ ⊆ probeRectV j := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz.2

/-- Geometry of the conformal setting (BP2 D2): with `‖ϕ(z) − z‖ ≤ ℓ/32` on the closed strip and
`ψ ∘ ϕ = id` on `S_j`, `(ϕ, S_j, V)` is a conformal neighbourhood. -/
theorem isConfNbhd_probeDomV {j : ℕ} {a θ : ℝ}
    (hφ : ∀ z : ℂ, |z.im| ≤ ell j → ‖probeMap j a θ z - z‖ ≤ ell j / 32)
    (hψ : ∀ z ∈ probeStrip j, probeInv j a θ (probeMap j a θ z) = z) :
    CC.IsConfNbhd (probeMap j a θ) (probeStrip j) (probeDomV j a θ) := by
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  -- points of `V` are close to `V_j`
  have hclose : ∀ z ∈ probeDomV j a θ, |z.im| ≤ 5 * ell j / 32 ∧ |z.re - 1 / 2| ≤ 21 / 32 := by
    intro z hz
    have hzS : |z.im| ≤ ell j := le_of_lt hz.1
    have hd := hφ z hzS
    have hV : probeMap j a θ z ∈ probeRectV j := hz.2
    have him : |(probeMap j a θ z).im - z.im| ≤ ell j / 32 := by
      rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans hd
    have hre : |(probeMap j a θ z).re - z.re| ≤ ell j / 32 := by
      rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hd
    have h1 := abs_sub_abs_le_abs_sub z.im (probeMap j a θ z).im
    rw [abs_sub_comm] at him
    refine ⟨by linarith [hV.2], ?_⟩
    rw [abs_le] at hre ⊢
    obtain ⟨hv1, hv2⟩ := hV.1
    constructor <;> linarith [hre.1, hre.2]
  refine ⟨isOpen_probeStrip j, (isOpen_probeStrip j).inter
    ((isOpen_probeRectV j).preimage (continuous_probeMap j a θ)), ?_, ?_,
    (differentiable_probeMap j a θ).differentiableOn, ?_⟩
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset fun z hz => ?_
    rw [mem_closedBall, dist_zero_right]
    obtain ⟨h1, h2⟩ := hclose z hz
    have hre : |z.re| ≤ 2 := by
      rw [abs_le] at h2 ⊢; constructor <;> linarith [h2.1, h2.2]
    have him : |z.im| ≤ 1 := by linarith
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 3 := by linarith
  · have hcl : IsClosed {z : ℂ | |z.im| ≤ 5 * ell j / 32} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    refine (closure_minimal (fun z hz => (hclose z hz).1) hcl).trans fun z hz => ?_
    show |z.im| < ell j
    have : |z.im| ≤ 5 * ell j / 32 := hz
    linarith
  · intro z hz w hw hzw
    rw [← hψ z hz, ← hψ w hw, hzw]

/-- **Localization** (BP2 D2): `|Re z − 1/2| ≤ 9/16`, `|Im z| ≤ ℓ/16` imply `z ∈ V`. -/
theorem mem_probeDomV {j : ℕ} {a θ : ℝ}
    (hφ : ∀ z : ℂ, |z.im| ≤ ell j → ‖probeMap j a θ z - z‖ ≤ ell j / 32) {z : ℂ}
    (hre : |z.re - 1 / 2| ≤ 9 / 16) (him : |z.im| ≤ ell j / 16) : z ∈ probeDomV j a θ := by
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  have hd := hφ z (by linarith)
  have him' : |(probeMap j a θ z).im - z.im| ≤ ell j / 32 := by
    rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans hd
  have hre' : |(probeMap j a θ z).re - z.re| ≤ ell j / 32 := by
    rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hd
  refine ⟨show |z.im| < ell j by linarith, ?_, ?_⟩
  · rw [abs_le] at hre hre'
    constructor <;> linarith [hre.1, hre.2, hre'.1, hre'.2]
  · have := abs_sub_abs_le_abs_sub (probeMap j a θ z).im z.im
    linarith


/-! ## Small facts on fields and metrics -/

private theorem ofCont_add_u2 (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

/-- `(x + f) − f = x` for a distribution `x` and a continuous `f`. -/
theorem addFun_addFun_neg (x : DistC) (f : C(ℂ, ℝ)) : addFun (addFun x f) (-f) = x := by
  have h0 : ofCont (0 : C(ℂ, ℝ)) = 0 := by
    have := ofCont_add_u2 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have h1 : ofCont f + ofCont (-f) = 0 := by rw [← ofCont_add_u2, add_neg_cancel, h0]
  simp only [addFun, add_assoc, h1, add_zero]

/-- `D(z, w) ≤ D(z, w; V)`, with `D(z, w) ∈ ℝ` embedded in `[0, ∞]` (as `Lower/Windows.lean`'s
`ofReal_le_internal`, restated here to keep the imports light). -/
theorem ofReal_dist_le_internal (D : ContMetric) (V : Set ℂ) (z w : ℂ) :
    ENNReal.ofReal (D.1 (z, w)) ≤ D.internal V z w := by
  have h := MetricGeometry.edist_le_internalEDist (X := D.Space) (D.pt '' V) (D.pt z) (D.pt w)
  rw [edist_dist] at h
  exact h

/-! ## The random continuous function `f` and the conformal coupling (Steps 3–4) -/

/-- **Steps 3–4** (BP2 D3): the measurable random continuous function
`f = β · (K − Q log|ϕ' ∘ ψ|)`, equal to `K − Q log|ϕ' ∘ ψ| = K + Q log|ψ'|` on `ϕ(V)`, for which
`(h, h̄, f)` is a.s. a conformal coupling for `(ϕ, S_j, V)`. -/
theorem exists_competitor_field {γ : ℝ} {j : ℕ} {a θ : ℝ}
    (hconf : CC.IsConfNbhd (probeMap j a θ) (probeStrip j) (probeDomV j a θ))
    (hψ : ∀ z ∈ probeStrip j, probeInv j a θ (probeMap j a θ z) = z)
    (hderφ : ∀ z ∈ probeStrip j, 3 / 4 ≤ ‖deriv (probeMap j a θ) z‖)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h hbar : Ω → DistC} {K : Ω → ℂ → ℝ}
    (hKm : Measurable (fun p : Ω × ℂ => K p.1 p.2))
    (hKh : ∀ ω, InnerProductSpace.HarmonicOnNhd (K ω) (probeRectU j))
    (hcoup : ∀ᵐ ω ∂P, ∀ f g : TestC, tsupport (f : ℂ → ℝ) ⊆ probeRectU j →
        (∀ z ∈ probeStrip j, g z = ‖deriv (probeMap j a θ) z‖ ^ 2 * f (probeMap j a θ z)) →
        (∀ z ∉ probeStrip j, g z = 0) → h ω g = hbar ω f + ∫ w, K ω w * f w) :
    ∃ f : Ω → C(ℂ, ℝ), Measurable f ∧
      (∀ ω, ∀ y ∈ probeMap j a θ '' probeDomV j a θ,
        f ω y = K ω y - Q γ * Real.log ‖deriv (probeMap j a θ) (probeInv j a θ y)‖) ∧
      ∀ᵐ ω ∂P, CC.IsConfCoupling γ (probeMap j a θ) (probeStrip j) (probeDomV j a θ)
        (h ω) (hbar ω) (f ω) := by
  have hWo := isOpen_probeStrip j
  have hφd := hconf.differentiableOn
  have hφi := hconf.injOn
  have hφWo : IsOpen (probeMap j a θ '' probeStrip j) := CC.isOpen_image_conf hWo hφd hφi
  have hφVsub := image_probeDomV_subset j a θ
  set O := probeMap j a θ '' probeStrip j ∩ probeRectU j with hOdef
  have hOo : IsOpen O := hφWo.inter (isOpen_probeRectU j)
  have hconfO : CC.IsConfNbhd id O (probeMap j a θ '' probeDomV j a θ) := by
    refine ⟨hOo, hconf.isOpen_image, (isBounded_probeRectV j).subset hφVsub,
      fun y hy => ⟨?_, ?_⟩, differentiableOn_id, injOn_id _⟩
    · exact (hconf.closure_image_subset.trans (image_mono hconf.closure_subset)) hy
    · exact closure_probeRectV_subset_U j (closure_mono hφVsub hy)
  obtain ⟨β, -, hβO, hβ1⟩ := hconfO.exists_cutoff
  set ulog : ℂ → ℝ := fun y => Real.log ‖deriv (probeMap j a θ) (probeInv j a θ y)‖
    with hulogdef
  have hψc : ContinuousOn (probeInv j a θ) (probeMap j a θ '' probeStrip j) :=
    CC.continuousOn_leftInv hWo hφd hφi hψ
  have hulog : ContinuousOn ulog O := by
    have h1 : ContinuousOn (fun y => ‖deriv (probeMap j a θ) (probeInv j a θ y)‖)
        (probeMap j a θ '' probeStrip j) :=
      ((continuous_deriv_probeMap j a θ).comp_continuousOn hψc).norm
    refine (h1.log fun y hy => ?_).mono inter_subset_left
    have := hderφ _ (CC.leftInv_mem hψ hy)
    exact (lt_of_lt_of_le (by norm_num) this).ne'
  have hKc : ∀ ω, ContinuousOn (K ω) (probeRectU j) := fun ω x hx =>
    (hKh ω x hx).1.continuousAt.continuousWithinAt
  have huc : ∀ ω, ContinuousOn (fun y => K ω y - Q γ * ulog y) O := fun ω =>
    ((hKc ω).mono inter_subset_right).sub (continuousOn_const.mul hulog)
  refine ⟨fun ω => ⟨fun y => β y * (K ω y - Q γ * ulog y),
    continuous_mul_of_continuousOn_of_tsupport hOo (huc ω) β.continuous hβO⟩, ?_, ?_, ?_⟩
  · refine ContinuousMap.measurable_iff_eval.2 fun y => ?_
    exact measurable_const.mul
      ((hKm.comp (measurable_id.prodMk measurable_const)).sub measurable_const)
  · intro ω y hy
    show β y * (K ω y - Q γ * ulog y) = _
    rw [hβ1 y (subset_closure hy), one_mul]
  · filter_upwards [hcoup] with ω hω
    intro g τg hg hτ
    have hgU : tsupport (g : ℂ → ℝ) ⊆ probeRectU j :=
      hg.trans (hφVsub.trans (probeRectV_subset_U j))
    have hgO : tsupport (g : ℂ → ℝ) ⊆ O := fun y hy => ⟨hconf.image_subset (hg hy), hgU hy⟩
    have e1 := hω g τg hgU (fun z hz => by rw [hτ z, indicator_of_mem hz])
      (fun z hz => by rw [hτ z, indicator_of_notMem hz])
    have e2 := hτ.integral_log_mul hconf hψ hg
    have hiK : Integrable (fun y => K ω y * g y) :=
      integrable_mul_of_continuousOn_of_tsupport (isOpen_probeRectU j) (hKc ω) g.continuous
        g.hasCompactSupport hgU
    have hiL : Integrable (fun y => ulog y * g y) :=
      integrable_mul_of_continuousOn_of_tsupport hOo hulog g.continuous g.hasCompactSupport hgO
    have e3 : ∫ y, β y * (K ω y - Q γ * ulog y) * g y =
        (∫ y, K ω y * g y) - Q γ * ∫ y, ulog y * g y := by
      rw [← integral_const_mul, ← integral_sub hiK (hiL.const_mul (Q γ))]
      congr 1
      funext y
      by_cases hgy : g y = 0
      · rw [hgy]; ring
      · rw [hβ1 y (subset_closure (hg (subset_tsupport _ hgy)))]; ring
    have e4 : ∫ y, Real.log ‖deriv (probeInv j a θ) y‖ * g y = -∫ y, ulog y * g y := by
      rw [← integral_neg]
      congr 1
      funext y
      by_cases hgy : g y = 0
      · rw [hgy]; ring
      · have hy : y ∈ probeMap j a θ '' probeStrip j :=
          hconf.image_subset (hg (subset_tsupport _ hgy))
        have := CC.log_norm_deriv_leftInv hWo hφd hφi hψ hy
        simp only [hulogdef]
        rw [this]
        ring
    show h ω τg - Q γ * ∫ x, Real.log ‖deriv (probeMap j a θ) x‖ * τg x =
      hbar ω g + ∫ y, β y * (K ω y - Q γ * ulog y) * g y
    rw [e1, e2, e4, e3]
    ring


/-! ## The deterministic core (Steps 7–8) -/

/-- **Steps 7–8**, for one sample: from the one-sided conformal covariance (`hle`), Weyl scaling
(`hweyl`) and the geodesic property, `log D_{h̄}(0,1) − log D_h(0,1) + ξ∫K dλ` is at most
`log ∫₀¹ exp(p log|ϕ'(η)|) + 2ξ sup_{V_j}|K|`. -/
theorem competitor_det {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} {j : ℕ} {a θ : ℝ}
    (hφ32 : ∀ z : ℂ, |z.im| ≤ ell j → ‖probeMap j a θ z - z‖ ≤ ell j / 32)
    (hderφ : ∀ z ∈ probeStrip j, 3 / 4 ≤ ‖deriv (probeMap j a θ) z‖)
    (hψ : ∀ z ∈ probeStrip j, probeInv j a θ (probeMap j a θ z) = z)
    {g₀ g₁ : DistC} {K : ℂ → ℝ} (hKc : ContinuousOn K (probeRectU j)) (hKm : Measurable K)
    {f : C(ℂ, ℝ)}
    (hfV : ∀ y ∈ probeMap j a θ '' probeDomV j a θ,
      f y = K y - Q γ * Real.log ‖deriv (probeMap j a θ) (probeInv j a θ y)‖)
    {η : C(unitInterval, ℂ)} (hgeo : IsGeod01 (D g₀) 0 1 η)
    (hle : ∀ z ∈ probeDomV j a θ, ∀ w ∈ probeDomV j a θ,
      CC.confMetric D (probeMap j a θ) (probeDomV j a θ) g₁ f z w ≤
        (D g₀).internal (probeDomV j a θ) z w)
    (hweyl : ∀ (F : C(ℂ, ℝ)) (z w : ℂ), weylScale (xiGamma γ) F (D (addFun g₁ f)) z w =
      ENNReal.ofReal ((D (addFun (addFun g₁ f) F)).1 (z, w)))
    (hloc : ∀ t, |(η t).re - 1/2| ≤ 9/16 ∧ |(η t).im| ≤ ell j / 16) :
    Real.log ((D g₁).1 (0, 1)) - Real.log ((D g₀).1 (0, 1)) +
        xiGamma γ * ∫ w, K w ∂(segMeasure 0 1) ≤
      Real.log (∫ t in (0:ℝ)..1, Real.exp (xiGamma γ * Q γ *
          Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖)) +
        2 * xiGamma γ * ⨆ w ∈ probeRectV j, |K w| := by
  have hξ0 : 0 ≤ xiGamma γ := (LQGMetric.GM.xiGamma_pos hγ).le
  set S := ⨆ w ∈ probeRectV j, |K w| with hSdef
  have hS0 : 0 ≤ S := iSup_probeRectV_nonneg j K
  have hKS : ∀ w ∈ probeRectV j, |K w| ≤ S := fun w hw => abs_le_iSup_probeRectV hKc hw
  -- Step 2: the geodesic stays in `V`
  have hηV : ∀ τ : unitInterval, η τ ∈ probeDomV j a θ := fun τ =>
    mem_probeDomV hφ32 (hloc τ).1 (hloc τ).2
  have hL0 : 0 < (D g₀).1 (0, 1) := GaussianLQG.contMetric_pos _ zero_ne_one
  have hD10 : 0 < (D g₁).1 (0, 1) := GaussianLQG.contMetric_pos _ zero_ne_one
  set c : ℝ → ℂ := fun t => probeMap j a θ (η (Set.projIcc 0 1 zero_le_one t)) with hcdef
  have hcc : Continuous c :=
    (continuous_probeMap j a θ).comp (η.continuous.comp continuous_projIcc)
  -- Step 7: the bent path is `D_h(0,1)`-Lipschitz for `D_{h̄+f}`
  have hLip : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, s ≤ t →
      (D (addFun g₁ f)).1 (c s, c t) ≤ (D g₀).1 (0, 1) * (t - s) := by
    intro s hs t ht hst
    have hcs : c s = probeMap j a θ (η ⟨s, hs⟩) := by
      simp only [hcdef, Set.projIcc_of_mem _ hs]
    have hct : c t = probeMap j a θ (η ⟨t, ht⟩) := by
      simp only [hcdef, Set.projIcc_of_mem _ ht]
    have hrest := GaussianLQG.isGeod01_restrictPath hgeo (s := ⟨s, hs⟩) (t := ⟨t, ht⟩) hst
    have hrange : range (GaussianLQG.restrictPath η ⟨s, hs⟩ ⟨t, ht⟩) ⊆ probeDomV j a θ := by
      rintro _ ⟨u, rfl⟩
      exact hηV _
    have h1 := LQGMetric.GM.internal_le_of_isGeod01 hrest hrange
    rw [hgeo.2.2 ⟨s, hs⟩ ⟨t, ht⟩] at h1
    have h2 := hle (η ⟨s, hs⟩) (hηV _) (η ⟨t, ht⟩) (hηV _)
    have h3 := ofReal_dist_le_internal (D (addFun g₁ f)) (probeMap j a θ '' probeDomV j a θ)
      (probeMap j a θ (η ⟨s, hs⟩)) (probeMap j a θ (η ⟨t, ht⟩))
    have h4 : ENNReal.ofReal ((D (addFun g₁ f)).1 (c s, c t)) ≤
        ENNReal.ofReal (|t - s| * (D g₀).1 (0, 1)) := by
      rw [hcs, hct]
      exact h3.trans (h2.trans h1)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity), abs_of_nonneg (sub_nonneg.2 hst)] at h4
    linarith
  -- Step 6: `e^{-ξ f}·D_{h̄+f} = D_{h̄}`
  have hW : ∀ x y, weylScale (xiGamma γ) (-f) (D (addFun g₁ f)) x y =
      ENNReal.ofReal ((D g₁).1 (x, y)) := by
    intro x y
    rw [hweyl (-f) x y, addFun_addFun_neg]
  have hmain := dist_le_mul_integral_exp_of_weyl hW hcc.continuousOn hL0.le hLip
  have hc0 : c 0 = 0 := by
    simp only [hcdef, Set.projIcc_left]
    rw [show η ⟨0, left_mem_Icc.2 zero_le_one⟩ = η 0 from rfl, hgeo.1, probeMap_zero]
  have hc1 : c 1 = 1 := by
    simp only [hcdef, Set.projIcc_right]
    rw [show η ⟨1, right_mem_Icc.2 zero_le_one⟩ = η 1 from rfl, hgeo.2.1, probeMap_one]
  rw [hc0, hc1] at hmain
  -- the integrand
  have hpt : ∀ t, Real.exp (xiGamma γ * (-f) (c t)) ≤ Real.exp (xiGamma γ * S) *
      Real.exp (xiGamma γ * Q γ *
        Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖) := by
    intro t
    have hzV := hηV (Set.projIcc 0 1 zero_le_one t)
    have hct : c t = probeMap j a θ (η (Set.projIcc 0 1 zero_le_one t)) := rfl
    have hφzV : c t ∈ probeMap j a θ '' probeDomV j a θ := hct ▸ mem_image_of_mem _ hzV
    have hfz : f (c t) = K (c t) - Q γ *
        Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖ := by
      rw [hfV _ hφzV, hct, hψ _ hzV.1]
    have hK := hKS _ (image_probeDomV_subset j a θ hφzV)
    rw [← Real.exp_add, ContinuousMap.coe_neg, Pi.neg_apply, hfz]
    refine Real.exp_le_exp.2 ?_
    have h1 : -K (c t) ≤ S := (neg_le_abs _).trans hK
    have h2 : xiGamma γ * -K (c t) ≤ xiGamma γ * S := mul_le_mul_of_nonneg_left h1 hξ0
    have h3 : xiGamma γ * -(K (c t) - Q γ *
        Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖) =
        xiGamma γ * -K (c t) + xiGamma γ * Q γ *
          Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖ := by ring
    rw [h3]
    linarith
  have hcont1 : Continuous fun t => Real.exp (xiGamma γ * (-f) (c t)) :=
    Real.continuous_exp.comp (continuous_const.mul ((-f).continuous.comp hcc))
  have hne : ∀ t, ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖ ≠ 0 := fun t =>
    (lt_of_lt_of_le (by norm_num) (hderφ _ (hηV _).1)).ne'
  have hcont2 : Continuous fun t => Real.exp (xiGamma γ * Q γ *
      Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖) :=
    Real.continuous_exp.comp (continuous_const.mul
      ((((continuous_deriv_probeMap j a θ).comp
        (η.continuous.comp continuous_projIcc)).norm).log hne))
  set J := ∫ t in (0:ℝ)..1, Real.exp (xiGamma γ * Q γ *
      Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖) with hJdef
  have hJ0 : 0 < J := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hcont2.intervalIntegrable 0 1) (fun t _ => Real.exp_pos _) zero_lt_one
  have hint : ∫ t in (0:ℝ)..1, Real.exp (xiGamma γ * (-f) (c t)) ≤
      Real.exp (xiGamma γ * S) * J := by
    rw [hJdef, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one (hcont1.intervalIntegrable 0 1)
      ((continuous_const.mul hcont2).intervalIntegrable 0 1) fun t _ => hpt t
  have hD1 : (D g₁).1 (0, 1) ≤ (D g₀).1 (0, 1) * (Real.exp (xiGamma γ * S) * J) :=
    hmain.trans (mul_le_mul_of_nonneg_left hint hL0.le)
  have hlog : Real.log ((D g₁).1 (0, 1)) ≤
      Real.log ((D g₀).1 (0, 1)) + (xiGamma γ * S + Real.log J) := by
    have := Real.log_le_log hD10 hD1
    rwa [Real.log_mul hL0.ne' (by positivity), Real.log_mul (Real.exp_pos _).ne' hJ0.ne',
      Real.log_exp] at this
  -- Step 8: `|∫ K dλ| ≤ sup_{V_j} |K|`
  have hKint : ∫ w, K w ∂(segMeasure 0 1) ≤ S :=
    (le_abs_self _).trans (abs_integral_segMeasure_le hKc hKm)
  have hξK : xiGamma γ * ∫ w, K w ∂(segMeasure 0 1) ≤ xiGamma γ * S :=
    mul_le_mul_of_nonneg_left hKint hξ0
  linarith

/-! ## The competitor -/

/-- **Lemma `lem:competitor`** ((5.3)–(5.4′); BP2 D2, D3, D5), with the one-sided conformal
covariance `CC.ConfCovLE γ D` as interface hypothesis (ruling G10). -/
theorem competitor_probe : ∃ εc, 0 < εc ∧ ∀ {γ}, 0 < γ → γ < 2 → ∀ {D : DistC → ContMetric},
    IsStrongLQGMetric γ D → CC.ConfCovLE γ D → ∀ (j : ℕ) (a θ : ℝ), a ∈ Icc (0:ℝ) 1 →
    |θ| ≤ εc * ell j →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ),
    IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable (fun p : Ω × ℂ => K p.1 p.2) →
    (∀ ω, InnerProductSpace.HarmonicOnNhd (K ω) (probeRectU j)) →
    (∀ᵐ ω ∂P, ∀ f g : TestC, tsupport (f : ℂ → ℝ) ⊆ probeRectU j →
        (∀ z ∈ probeStrip j, g z = ‖deriv (probeMap j a θ) z‖ ^ 2 * f (probeMap j a θ z)) →
        (∀ z ∉ probeStrip j, g z = 0) → h ω g = hbar ω f + ∫ w, K ω w * f w) →
    (∀ᵐ ω ∂P, measPairing (hbar ω) (segMeasure 0 1) =
        measPairing (h ω) ((segMeasure 0 1).map (probeInv j a θ)) -
          ∫ w, K ω w ∂(segMeasure 0 1)) →
    ∀ η : Ω → C(unitInterval, ℂ), (∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 0 1 (η ω)) → ∀ b : ℝ,
    ∀ᵐ ω ∂P, (∀ t, |(η ω t).re - 1/2| ≤ 9/16 ∧ |(η ω t).im| ≤ ell j / 16) →
      xiGamma γ * probePair j a θ (h ω) + Zf γ b D (hbar ω) - Zf γ b D (h ω) ≤
        Real.log (∫ t in (0:ℝ)..1, Real.exp (xiGamma γ * Q γ *
          Real.log ‖deriv (probeMap j a θ) (η ω (Set.projIcc 0 1 zero_le_one t))‖)) +
        2 * xiGamma γ * ⨆ w ∈ probeRectV j, |K ω w| := by
  obtain ⟨εψ, C₀, hεψ, hC₀, hspec⟩ := probeInv_spec
  refine ⟨min εψ (1 / (32 * C₀ + 32)), lt_min hεψ (by positivity), ?_⟩
  intro γ hγ _hγ2 D hD hCC j a θ _ha hθ Ω _ P _ h hbar K hh hhb hKm hKh hcoup hb5 η hη b
  have hℓ := ell_pos j
  -- Step 0: constants
  have hθψ : |θ| ≤ εψ * ell j :=
    hθ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le)
  have hθc : |θ| ≤ 1 / (32 * C₀ + 32) * ell j :=
    hθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ.le)
  obtain ⟨hA, -, hψ, -, -, -⟩ := hspec j a θ hθψ
  have hC₀θ : C₀ * |θ| ≤ ell j / 32 := by
    have h1 : C₀ * |θ| ≤ C₀ * (1 / (32 * C₀ + 32) * ell j) := mul_le_mul_of_nonneg_left hθc hC₀
    have h3 : C₀ * (1 / (32 * C₀ + 32)) ≤ 1 / 32 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : C₀ * (1 / (32 * C₀ + 32) * ell j) ≤ ell j / 32 :=
      calc C₀ * (1 / (32 * C₀ + 32) * ell j) = (C₀ * (1 / (32 * C₀ + 32))) * ell j := by ring
        _ ≤ 1 / 32 * ell j := mul_le_mul_of_nonneg_right h3 hℓ.le
        _ = ell j / 32 := by ring
    linarith
  have hφ32 : ∀ z : ℂ, |z.im| ≤ ell j → ‖probeMap j a θ z - z‖ ≤ ell j / 32 :=
    fun z hz => (hA z hz).1.trans hC₀θ
  have hderφ : ∀ z ∈ probeStrip j, 3 / 4 ≤ ‖deriv (probeMap j a θ) z‖ := by
    intro z hz
    have h1 := (hA z (le_of_lt hz)).2
    have h2 : ‖(1 : ℂ)‖ ≤ ‖deriv (probeMap j a θ) z‖ + ‖deriv (probeMap j a θ) z - 1‖ := by
      calc ‖(1 : ℂ)‖ = ‖deriv (probeMap j a θ) z - (deriv (probeMap j a θ) z - 1)‖ := by
            ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [norm_one] at h2
    linarith
  -- Step 1: the conformal setting
  have hconf := isConfNbhd_probeDomV hφ32 hψ
  -- Steps 3–4: the field and the coupling
  obtain ⟨f, hfm, hfV, hcoupl⟩ := exists_competitor_field (γ := γ) hconf hψ hderφ hKm hKh hcoup
  -- Step 5: one-sided conformal covariance
  have hle := hCC _ _ _ hconf P h hbar f hh hhb hfm hcoupl
  -- Step 6: Weyl scaling for `h̄ + f`
  have hweyl := hD.weyl P (fun ω => addFun (hbar ω) (f ω)) (CC.isGFFPlusCont_addFun_of_wp hhb hfm)
  have hKc : ∀ ω, ContinuousOn (K ω) (probeRectU j) := fun ω x hx =>
    (hKh ω x hx).1.continuousAt.continuousWithinAt
  have hKmeas : ∀ ω, Measurable (K ω) := fun ω =>
    hKm.comp (measurable_const.prodMk measurable_id)
  filter_upwards [hη, hle, hweyl, hb5] with ω hgeo hleω hwω hb5ω hloc
  have key := competitor_det hγ hφ32 hderφ hψ (hKc ω) (hKmeas ω) (hfV ω) hgeo hleω hwω hloc
  have e : xiGamma γ * probePair j a θ (h ω) + Zf γ b D (hbar ω) - Zf γ b D (h ω) =
      Real.log ((D (hbar ω)).1 (0, 1)) - Real.log ((D (h ω)).1 (0, 1)) +
        xiGamma γ * ∫ w, K ω w ∂(segMeasure 0 1) := by
    simp only [Zf, probePair]
    rw [hb5ω]
    ring
  rw [e]
  exact key

end SmallGammaGeodesics
