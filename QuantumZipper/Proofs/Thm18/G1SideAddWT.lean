import QuantumZipper.Proofs.Thm18.G1SideAddOn
import QuantumZipper.Proofs.Zipper.SWCoreB7bWTLem
import QuantumZipper.Proofs.Zipper.SWCoreB7bWTInt
import QuantumZipper.Proofs.Zipper.SWCoreB7Fam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (2): uniform weighted boundary transport for `X + g`, any continuous `g`, over a family

Almost surely (ONE event, with the quantifier over the continuous function `g : ℂ → ℝ` inside),
for a finite-parameter family `q ↦ Ψ q` of class maps (compact parameter set, Lipschitz in `q`),
for every continuous test function `f` supported in `(a,b)`, uniformly in `q ∈ K`,

  `∫ f d(bdryApprox γ (coordChange (X + g) Ψ_q Q) k) → ∫_{[Ψ_q(a),Ψ_q(b)]} f(Ψ_q⁻¹ u) e^{(γ/2) g(u)} dν_X`

(`ae_transport_family_addFun`).

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
(5.1) / Prop. 2.1 (adding a continuous function multiplies the boundary measure by `e^{γ g/2}`),
combined with Sheffield–Wang arXiv:1605.06171 Thm 4.3 in the repository's family form
(`ae_transport_family`). The proof is the proved `𝔥₀` chain (`ae_transport_family_h0rev`) with
`𝔥₀` replaced by `g`: the Lipschitz estimates of the cut-off `𝔥₀` are replaced by the uniform
continuity of `g` on the closed `M`-ball (compactness; finite-net argument). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

/-- Exponential weights with close exponents are uniformly close (own elementary estimate). -/
theorem exp_weight_close {γ : ℝ} (hγ : 0 < γ) (Cf Bh : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' > 0, ∀ u v y : ℝ, |v| ≤ Bh → |u - v| ≤ ε' → |y| ≤ |Cf| →
      |y * Real.exp (γ / 2 * u) - y * Real.exp (γ / 2 * v)| ≤ ε := by
  set EB : ℝ := Real.exp (γ / 2 * Bh) with hEB
  set Λ : ℝ := |Cf| * (2 * EB) * (γ / 2) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨min (1 / (γ / 2 + 1)) (ε / (Λ + 1)), lt_min (by positivity) (by positivity),
    fun u v y hv huv hy => ?_⟩
  have h1 : |γ / 2 * u - γ / 2 * v| = γ / 2 * |u - v| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < γ / 2)]
  have h2 : γ / 2 * |u - v| ≤ 1 :=
    calc γ / 2 * |u - v| ≤ (γ / 2 + 1) * (1 / (γ / 2 + 1)) :=
          mul_le_mul (by linarith) (huv.trans (min_le_left _ _)) (abs_nonneg _) (by positivity)
      _ = 1 := by field_simp
  have he := abs_exp_sub_exp_le (by rw [h1]; exact h2 : |γ / 2 * u - γ / 2 * v| ≤ 1)
  rw [h1] at he
  have hEv : Real.exp (γ / 2 * v) ≤ EB :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self v).trans hv) (by positivity))
  have h3 : Λ * |u - v| ≤ ε :=
    calc Λ * |u - v| ≤ (Λ + 1) * (ε / (Λ + 1)) :=
          mul_le_mul (by linarith) (huv.trans (min_le_right _ _)) (abs_nonneg _) (by positivity)
      _ = ε := by field_simp
  rw [← mul_sub, abs_mul]
  calc |y| * |Real.exp (γ / 2 * u) - Real.exp (γ / 2 * v)|
      ≤ |Cf| * (2 * EB * (γ / 2 * |u - v|)) :=
        mul_le_mul hy (he.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))
          (abs_nonneg _) (abs_nonneg _)
    _ = Λ * |u - v| := by rw [hΛ]; ring
    _ ≤ ε := h3

/-- **The `g` weight in the target**: on `[ψ(a), ψ(b)]`, `ψ (ψ⁻¹ u) = u`. -/
theorem setIntegral_fun_conv {a b ρ M m γ : ℝ} {ψ : ℂ → ℂ} (g : ℂ → ℝ)
    (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) (hab : a ≤ b) (f : ℝ → ℝ) (ν : Measure ℝ) :
    ∫ u in Icc (ψ a).re (ψ b).re,
        f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) *
          Real.exp (γ / 2 * g (ψ ((projIcc a b hab
            (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) : ℝ) : ℂ))) ∂ν =
      ∫ u in Icc (ψ a).re (ψ b).re,
        f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) *
          Real.exp (γ / 2 * g u) ∂ν := by
  refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  have hcont : ContinuousOn (fun t : ℝ => (ψ t).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (hψ.1.continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun t ht =>
        self_subset_thickening hρ _ (ofReal_mem_segC ht))
  obtain ⟨hmem, heq⟩ := Function.invFunOn_pos (intermediate_value_Icc hab hcont hu)
  set s := Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u with hs
  have hps : ((projIcc a b hab s : ℝ)) = s := by rw [projIcc_of_mem hab hmem]
  have hz : ψ (s : ℂ) = (u : ℂ) :=
    Complex.ext (by simpa using heq) (by simpa using hψ.2.2.1 s hmem)
  rw [hps, hz]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

set_option maxHeartbeats 1000000 in
/-- **Uniform weighted boundary transport for `X + g`, a.s., for every continuous `g` (one
event).** -/
theorem ae_transport_family_addFun (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ) (K : Set (Fin n → ℝ)) {a b ρ M m : ℚ}
    {L R : ℝ} {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : (a : ℝ) < b) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ Ioo (a : ℝ) b → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ K,
        |∫ t, f t ∂bdryApprox γ (coordChange (X ω + ofFun g) (Ψ q) (Qc γ)) k -
          ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
            f (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u) *
              Real.exp (γ / 2 * g u) ∂qBoundaryMeasure γ (X ω)| ≤ η := by
  filter_upwards [ae_transport_family hX hγ hγ2 Ψ K hab hρ hm hL hcl hlip hπ hπK hπid hR hKR,
    ae_integrable_family hX hγ hγ2 Ψ K hab hρ hm hL hcl hlip hπ hπK hπid hR hKR,
    ae_avgReg_add_fun_family (Qc γ) hab hρ hm hcl hL hlip hπ hπK hπid hX,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2]
    with ω hT hI hAdd hV g hg f hf hfc hfs η hη
  have := hV.1
  set ν0 := qBoundaryMeasure γ (X ω) with hν0
  -- bound and uniform continuity of `g` on the closed `M`-ball
  obtain ⟨Bh, hBh⟩ := (isCompact_closedBall (0 : ℂ) (M : ℝ)).exists_bound_of_continuousOn
    hg.continuousOn
  have hUC := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) (M : ℝ)).uniformContinuousOn_of_continuous hg.continuousOn)
  have hBall : ∀ q ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), Ψ q z ∈ closedBall (0 : ℂ) M :=
    fun q hq z hz => mem_closedBall_zero_iff.2 ((hcl q hq).2.1 z hz)
  have hgB : ∀ q ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), |g (Ψ q z)| ≤ Bh := fun q hq z hz => by
    simpa [Real.norm_eq_abs] using hBh _ (hBall q hq z hz)
  set p : ℝ → ℝ := fun t => (projIcc (a : ℝ) b hab.le t : ℝ) with hp
  have hpI : ∀ t, p t ∈ Icc (a : ℝ) b := fun t => (projIcc (a : ℝ) b hab.le t).2
  have hpc : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpid : ∀ t ∈ Icc (a : ℝ) b, p t = t := fun t ht => by
    simp only [hp, projIcc_of_mem hab.le ht]
  have hthk : ∀ t ∈ Icc (a : ℝ) b, ((t : ℝ) : ℂ) ∈ thickening (ρ : ℝ) (segC a b) :=
    fun t ht => self_subset_thickening hρ _ (ofReal_mem_segC ht)
  set gf : (Fin n → ℝ) → ℝ → ℝ :=
    fun q t => f t * Real.exp (γ / 2 * g (Ψ q (p t))) with hgf
  have hgc : ∀ q ∈ K, Continuous (gf q) := fun q hq =>
    hf.mul (Real.continuous_exp.comp (continuous_const.mul (hg.comp
      ((hcl q hq).1.continuousOn.comp_continuous (Complex.continuous_ofReal.comp hpc)
        fun t => hthk _ (hpI t)))))
  have hgK : ∀ q, ∀ x ∉ tsupport f, gf q x = 0 := fun q x hx => by
    simp only [hgf, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hgs : ∀ q, tsupport (gf q) ⊆ tsupport f := fun q => tsupport_mul_subset_left
  have hgcs : ∀ q, HasCompactSupport (gf q) := fun q => hfc.mul_right
  have hgb : ∀ q ∈ K, ∃ C, ∀ x, |gf q x| ≤ C := fun q hq => by
    obtain ⟨C, hC⟩ := (hgc q hq).bounded_above_of_compact_support (hgcs q)
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  -- the dominating bump `φ`
  obtain ⟨φc, hφs, hφ1, hφ01⟩ := exists_tsupport_one_of_isOpen_isClosed (X := ℝ) isOpen_Ioo
    (by rw [closure_Ioo hab.ne]; exact isCompact_Icc) (isClosed_tsupport f) hfs
  set φ : ℝ → ℝ := ⇑φc with hφdef
  have hφc : Continuous φ := φc.continuous
  have hφcs : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hφs.trans Ioo_subset_Icc_self)
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => (hφ01 x).1
  have hφle1 : ∀ x, φ x ≤ 1 := fun x => (hφ01 x).2
  have hφK : ∀ x ∈ tsupport f, 1 ≤ φ x := fun x hx => le_of_eq (hφ1 hx).symm
  -- mass bound for the limit functional
  set Mφ : ℝ := ν0.real (Icc (-(M : ℝ)) M) with hMφ
  have hre : ∀ q ∈ K, ∀ t ∈ Icc (a : ℝ) b, (Ψ q t).re ∈ Icc (-(M : ℝ)) M := fun q hq t ht => by
    have h1 := (hcl q hq).2.1 _ (hthk t ht)
    have h2 := abs_le.1 ((Complex.abs_re_le_norm (Ψ q t)).trans h1)
    exact ⟨h2.1, h2.2⟩
  have hLφ : ∀ q ∈ K, ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
      φ (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u) ∂ν0 ≤ Mφ := by
    intro q hq
    have hsub : Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re ⊆ Icc (-(M : ℝ)) M :=
      Icc_subset_Icc (hre q hq a ⟨le_rfl, hab.le⟩).1 (hre q hq b ⟨hab.le, le_rfl⟩).2
    have hfin : ν0 (Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re) ≠ ⊤ :=
      isCompact_Icc.measure_lt_top.ne
    calc _ ≤ ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re, (1 : ℝ) ∂ν0 :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => hφ0 _)
            (integrableOn_const hfin) (Eventually.of_forall fun u => hφle1 _)
      _ = ν0.real (Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re) := by simp
      _ ≤ Mφ := measureReal_mono hsub isCompact_Icc.measure_lt_top.ne
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hfx : ∀ x, |f x| ≤ |Cf| := fun x =>
    (by simpa [Real.norm_eq_abs] using hCf x : |f x| ≤ Cf).trans (le_abs_self _)
  -- finite nets of the weighted family (uniform continuity of `g`, Lipschitz `Ψ`)
  have hnet : ∀ ε > 0, ∃ S : Finset (ℝ → ℝ), (∀ h ∈ S, h ∈ gf '' K) ∧
      ∀ h ∈ gf '' K, ∃ h' ∈ S, ∀ x, |h x - h' x| ≤ ε := by
    intro ε hε
    obtain ⟨ε', hε', hW⟩ := exp_weight_close hγ Cf Bh hε
    obtain ⟨δ', hδ', hδ'g⟩ := hUC ε' hε'
    set δ : ℝ := δ' / (L + 1) with hδ
    have hδ0 : 0 < δ := div_pos hδ' (by linarith)
    obtain ⟨T, hTK, hTf, hcov⟩ := finite_approx_of_totallyBounded hK.totallyBounded δ hδ0
    classical
    refine ⟨hTf.toFinset.image gf, ?_, ?_⟩
    · intro h hh
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hh
      exact ⟨y, hTK (hTf.mem_toFinset.1 hy), rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨y, hyT, hqy⟩ := mem_iUnion₂.1 (hcov hq)
      have hy := hTK hyT
      refine ⟨gf y, Finset.mem_image.2 ⟨y, hTf.mem_toFinset.2 hyT, rfl⟩, fun x => ?_⟩
      have hd : ‖q - y‖ < δ := by rw [← dist_eq_norm]; exact mem_ball.1 hqy
      have hz := hthk _ (hpI x)
      have hdist : dist (Ψ q (p x)) (Ψ y (p x)) < δ' := by
        rw [dist_eq_norm]
        calc ‖Ψ q (p x) - Ψ y (p x)‖ ≤ L * ‖q - y‖ := hlip q hq y hy _ hz
          _ ≤ (L + 1) * ‖q - y‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
          _ < (L + 1) * δ := mul_lt_mul_of_pos_left hd (by linarith)
          _ = δ' := by rw [hδ]; field_simp
      have hu := hδ'g _ (hBall q hq _ hz) _ (hBall y hy _ hz) hdist
      rw [Real.dist_eq] at hu
      exact hW _ _ _ (hgB y hy _ hz) hu.le (hfx x)
  -- convergence for the members of the family, and for `φ`
  have hconvF : ∀ h ∈ gf '' K, ∀ η > 0, ∀ᶠ k in atTop, ∀ i : K,
      |∫ x, h x ∂bdryApprox γ (coordChange (X ω) (Ψ i.1) (Qc γ)) k -
        ∫ u in Icc (Ψ i.1 (a : ℝ)).re (Ψ i.1 (b : ℝ)).re,
          h (Function.invFunOn (fun t : ℝ => (Ψ i.1 t).re) (Icc (a : ℝ) b) u) ∂ν0| ≤ η := by
    rintro _ ⟨q, hq, rfl⟩ η hη
    filter_upwards [hT (gf q) (hgc q hq) (hgcs q) ((hgs q).trans hfs) η hη] with k hk i
    exact hk i.1 i.2
  have hφint : ∀ᶠ k in atTop, ∀ i : K,
      Integrable φ (bdryApprox γ (coordChange (X ω) (Ψ i.1) (Qc γ)) k) := by
    filter_upwards [hI φ hφc hφcs hφs hφ0] with k hk i
    exact hk i.1 i.2
  have hφconv : ∀ η > 0, ∀ᶠ k in atTop, ∀ i : K,
      |∫ x, φ x ∂bdryApprox γ (coordChange (X ω) (Ψ i.1) (Qc γ)) k -
        ∫ u in Icc (Ψ i.1 (a : ℝ)).re (Ψ i.1 (b : ℝ)).re,
          φ (Function.invFunOn (fun t : ℝ => (Ψ i.1 t).re) (Icc (a : ℝ) b) u) ∂ν0| ≤ η := by
    intro η hη
    filter_upwards [hT φ hφc hφcs hφs η hη] with k hk i
    exact hk i.1 i.2
  have hLlip : ∀ i : K, ∀ f₁ ∈ gf '' K, ∀ f₂ ∈ gf '' K, ∀ ε : ℝ, 0 ≤ ε →
      (∀ x, |f₁ x - f₂ x| ≤ ε) →
      |(∫ u in Icc (Ψ i.1 (a : ℝ)).re (Ψ i.1 (b : ℝ)).re,
          f₁ (Function.invFunOn (fun t : ℝ => (Ψ i.1 t).re) (Icc (a : ℝ) b) u) ∂ν0) -
        ∫ u in Icc (Ψ i.1 (a : ℝ)).re (Ψ i.1 (b : ℝ)).re,
          f₂ (Function.invFunOn (fun t : ℝ => (Ψ i.1 t).re) (Icc (a : ℝ) b) u) ∂ν0| ≤
        |Mφ| * ε := by
    rintro i _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩ ε hε hsup
    obtain ⟨C₁, hC₁⟩ := hgb q₁ hq₁
    obtain ⟨C₂, hC₂⟩ := hgb q₂ hq₂
    have key := abs_sub_le_of_limits (μ := fun k => bdryApprox γ (coordChange (X ω) (Ψ i.1)
      (Qc γ)) k) hε hφ0 hφK (hgK q₁) (hgK q₂) (hgc q₁ hq₁).stronglyMeasurable
      (hgc q₂ hq₂).stronglyMeasurable hC₁ hC₂ hsup (hφint.mono fun k hk => hk i)
      (fun η hη => (hconvF _ ⟨q₁, hq₁, rfl⟩ η hη).mono fun k hk => hk i)
      (fun η hη => (hconvF _ ⟨q₂, hq₂, rfl⟩ η hη).mono fun k hk => hk i)
      (fun η hη => (hφconv η hη).mono fun k hk => hk i)
    calc _ ≤ ε * _ := key
      _ ≤ ε * Mφ := mul_le_mul_of_nonneg_left (hLφ i.1 i.2) hε
      _ ≤ |Mφ| * ε := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hε
  have hU := unif_testFamily (K := tsupport f) (Mφ := Mφ) (D := |Mφ|) (F := gf '' K)
    hφ0 hφK hφint hφconv (fun i => hLφ i.1 i.2)
    (by rintro _ ⟨q, hq, rfl⟩ x hx; exact hgK q x hx)
    (by rintro _ ⟨q, hq, rfl⟩; exact (hgc q hq).stronglyMeasurable)
    (by rintro _ ⟨q, hq, rfl⟩; exact hgb q hq) hLlip hnet hconvF
  -- the weight: eventual closeness
  set c : ℝ := η / (2 * (|Mφ| + 1)) with hcdef
  have hc0 : 0 < c := by positivity
  obtain ⟨ε', hε', hW⟩ := exp_weight_close hγ Cf Bh hc0
  obtain ⟨δ', hδ', hδ'g⟩ := hUC ε' hε'
  have hrad : Tendsto (fun k : ℕ => radius k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ev1 : ∀ᶠ k in atTop, radius k < (ρ : ℝ) / 2 := hrad.eventually (gt_mem_nhds (by positivity))
  have ev2 : ∀ᶠ k in atTop, 4 * (M : ℝ) / ρ * radius k < δ' := by
    have : Tendsto (fun k => 4 * (M : ℝ) / ρ * radius k) atTop (𝓝 0) := by
      simpa using hrad.const_mul (4 * (M : ℝ) / ρ)
    exact this.eventually (gt_mem_nhds hδ')
  filter_upwards [hU (η / 2) (by positivity), hAdd g hg, ev1, ev2, hφint, hφconv 1 one_pos]
    with k hkU hkA hk1 hk2 hkI hkφ q hq
  set μ := bdryApprox γ (coordChange (X ω) (Ψ q) (Qc γ)) k with hμ
  set W : ℝ → ℝ := fun t => Real.exp (γ / 2 *
    (avgReg (coordChange (X ω + ofFun g) (Ψ q) (Qc γ)) k (t : ℂ) -
      avgReg (coordChange (X ω) (Ψ q) (Qc γ)) k (t : ℂ))) with hW'
  have hUq : |∫ x, gf q x ∂μ - ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
      f (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u) *
        Real.exp (γ / 2 * g u) ∂ν0| ≤ η / 2 := by
    rw [← setIntegral_fun_conv (γ := γ) g (hcl q hq) hρ hab.le f ν0]
    exact hkU ⟨q, hq⟩ (gf q) ⟨q, hq, rfl⟩
  have hwc : ∀ x, |f x * W x - gf q x| ≤ c * φ x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have hxI : x ∈ Icc (a : ℝ) b := Ioo_subset_Icc_self (hfs hx)
      have hWx : W x = Real.exp (γ / 2 *
          ∫ w, g w ∂((foldedCircle (x : ℂ) (radius k)).map (Ψ q))) := by
        simp only [hW']; rw [hkA q hq x hxI, add_sub_cancel_left]
      have hH := gavg_push_close hg (hcl q hq) hρ (ε := ε') (δ := δ')
        (fun z hz w hw hzw => (Real.dist_eq _ _ ▸ hδ'g z hz w hw hzw).le) hxI (radius_pos k)
        hk1 hk2
      have hgx : gf q x = f x * Real.exp (γ / 2 * g (Ψ q x)) := by
        simp only [hgf, hpid x hxI]
      rw [hWx, hgx]
      calc _ ≤ c := hW _ _ _ (hgB q hq _ (hthk _ hxI)) hH (hfx x)
        _ = c * 1 := (mul_one c).symm
        _ ≤ c * φ x := mul_le_mul_of_nonneg_left (hφK x hx) hc0.le
    · rw [image_eq_zero_of_notMem_tsupport hx, hgK q x hx, zero_mul, sub_zero, abs_zero]
      exact mul_nonneg hc0.le (hφ0 x)
  obtain ⟨Cg, hCg⟩ := hgb q hq
  have hb₂ := abs_le_mul_of_vanish (hgK q) hCg hφ0 hφK
  have hb₁ : ∀ x, |f x * W x| ≤ (Cg + c) * φ x := fun x => by
    have := abs_sub_abs_le_abs_sub (f x * W x) (gf q x)
    linarith [hwc x, hb₂ x, add_mul Cg c (φ x)]
  have hWm : Measurable W := Real.measurable_exp.comp (measurable_const.mul
    ((measurable_avgReg_real _ k).sub (measurable_avgReg_real _ k)))
  have key := abs_integral_sub_le_dom (hkI ⟨q, hq⟩)
    (hf.measurable.mul hWm).aestronglyMeasurable (hgc q hq).aestronglyMeasurable hb₁ hb₂ hwc
  have hφle : ∫ x, φ x ∂μ ≤ |Mφ| + 1 := by
    have := (abs_le.1 (hkφ ⟨q, hq⟩)).2
    linarith [hLφ q hq, le_abs_self Mφ]
  have hm1 : c * ∫ x, φ x ∂μ ≤ η / 2 := by
    calc c * ∫ x, φ x ∂μ ≤ c * (|Mφ| + 1) := mul_le_mul_of_nonneg_left hφle hc0.le
      _ = η / 2 := by rw [hcdef]; field_simp
  simp only [Pi.mul_apply] at key
  rw [integral_bdryApprox_eq_weighted γ (coordChange (X ω) (Ψ q) (Qc γ)) _ k f]
  have hWe : ∀ t : ℝ, Real.exp (γ / 2 *
      (avgReg (coordChange (X ω + ofFun g) (Ψ q) (Qc γ)) k (t : ℂ) -
        avgReg (coordChange (X ω) (Ψ q) (Qc γ)) k (t : ℂ))) = W t := fun t => rfl
  simp only [hWe]
  change |∫ x, f x * W x ∂μ - _| ≤ η
  change |∫ x, f x * W x ∂μ - ∫ x, gf q x ∂μ| ≤ c * ∫ x, φ x ∂μ at key
  rw [abs_le] at key hUq ⊢
  constructor <;> linarith [key.1, key.2, hUq.1, hUq.2]

end G1Side
end QuantumZipper
