import QuantumZipper.Proofs.Zipper.SWCoreB7bWTLem
import QuantumZipper.Proofs.Zipper.SWCoreB7bWTInt
import QuantumZipper.Proofs.Zipper.SWCoreB7Fam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7c (4): weighted family transport with parameter-dependent test functions

`ae_transport_family_h0rev_mov`: the statement of `SWCore.ae_transport_family_h0rev`
(SWCoreB7bWT.lean) for a family of test functions `fam q` depending on the parameter `q`
(common compact support `T0 ⊂ (a,b)`, uniform bound, uniform modulus of continuity in `q`).
The proof is that of `ae_transport_family_h0rev`, with the sup-norm modulus of `q ↦ fam q` added in
the total-boundedness step. This is what the moving test functions `f ∘ F_s⁻¹` of AC-fam need.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

set_option maxHeartbeats 1000000 in
/-- **Uniform weighted transport for `𝔥₀ + X` over a family, with test functions depending on the
parameter** (a.s.). -/
theorem ae_transport_family_h0rev_mov (κ : ℝ) (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ) (K : Set (Fin n → ℝ)) {a b ρ M m : ℚ}
    {L R : ℝ} {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : (a : ℝ) < b) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R) (hK : IsCompact K) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), c₀ ≤ ‖Ψ q z‖) :
    ∀ᵐ ω ∂P, ∀ (fam : (Fin n → ℝ) → ℝ → ℝ) (T0 : Set ℝ), IsCompact T0 → T0 ⊆ Ioo (a : ℝ) b →
      (∀ q ∈ K, Continuous (fam q)) → (∀ q ∈ K, tsupport (fam q) ⊆ T0) → ∀ Cf : ℝ,
      (∀ q ∈ K, ∀ x, |fam q x| ≤ Cf) →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ K, ∀ q' ∈ K, ‖q - q'‖ ≤ δ →
        ∀ x, |fam q x - fam q' x| ≤ ε) →
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ K,
        |∫ t, fam q t ∂bdryApprox γ (coordChange (ofFun (h0rev κ) + X ω) (Ψ q) (Qc γ)) k -
          ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
            fam q (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u) *
              Real.exp (γ / 2 * h0rev κ u) ∂qBoundaryMeasure γ (X ω)| ≤ η := by
  filter_upwards [ae_transport_family hX hγ hγ2 Ψ K hab hρ hm hL hcl hlip hπ hπK hπid hR hKR,
    ae_integrable_family hX hγ hγ2 Ψ K hab hρ hm hL hcl hlip hπ hπK hπid hR hKR,
    ae_avgReg_add_h0rev_family κ (Qc γ) hab hρ hm hcl hL hlip hπ hπK hπid hc₀ hsep hX,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2]
    with ω hT hI hAdd hV fam T0 hT0c hT0s hfamc hfams Cf₀ hCf₀ hmod η hη
  have := hV.1
  set ν0 := qBoundaryMeasure γ (X ω) with hν0
  have hc1 : 0 < c₀ / 2 := by positivity
  have hLh0 : 0 ≤ |2 / Real.sqrt κ| / (c₀ / 2) := div_nonneg (abs_nonneg _) hc1.le
  set Bh : ℝ := |2 / Real.sqrt κ| * (|Real.log (c₀ / 2)| + |Real.log (max (M : ℝ) (c₀ / 2))|)
    with hBh
  set EB : ℝ := Real.exp (γ / 2 * Bh) with hEB
  have hEB0 : 0 ≤ EB := (Real.exp_pos _).le
  set p : ℝ → ℝ := fun t => (projIcc (a : ℝ) b hab.le t : ℝ) with hp
  have hpI : ∀ t, p t ∈ Icc (a : ℝ) b := fun t => (projIcc (a : ℝ) b hab.le t).2
  have hpc : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpid : ∀ t ∈ Icc (a : ℝ) b, p t = t := fun t ht => by
    simp only [hp, projIcc_of_mem hab.le ht]
  have hthk : ∀ t ∈ Icc (a : ℝ) b, ((t : ℝ) : ℂ) ∈ thickening (ρ : ℝ) (segC a b) :=
    fun t ht => self_subset_thickening hρ _ (ofReal_mem_segC ht)
  set g : (Fin n → ℝ) → ℝ → ℝ :=
    fun q t => fam q t * Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p t))) with hg
  have hgc : ∀ q ∈ K, Continuous (g q) := fun q hq =>
    (hfamc q hq).mul (Real.continuous_exp.comp (continuous_const.mul ((continuous_h0cut κ hc1).comp
      ((hcl q hq).1.continuousOn.comp_continuous (Complex.continuous_ofReal.comp hpc)
        fun t => hthk _ (hpI t)))))
  have hgK : ∀ q ∈ K, ∀ x ∉ T0, g q x = 0 := fun q hq x hx => by
    simp only [hg, image_eq_zero_of_notMem_tsupport (fun h => hx (hfams q hq h)), zero_mul]
  have hgs : ∀ q ∈ K, tsupport (g q) ⊆ T0 := fun q hq =>
    tsupport_mul_subset_left.trans (hfams q hq)
  have hgcs : ∀ q ∈ K, HasCompactSupport (g q) := fun q hq =>
    hT0c.of_isClosed_subset (isClosed_tsupport _) (hgs q hq)
  have hgb : ∀ q ∈ K, ∃ C, ∀ x, |g q x| ≤ C := fun q hq => by
    obtain ⟨C, hC⟩ := (hgc q hq).bounded_above_of_compact_support (hgcs q hq)
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  -- the dominating bump `φ`
  obtain ⟨φc, hφs, hφ1, hφ01⟩ := exists_tsupport_one_of_isOpen_isClosed (X := ℝ) isOpen_Ioo
    (by rw [closure_Ioo hab.ne]; exact isCompact_Icc) hT0c.isClosed hT0s
  set φ : ℝ → ℝ := ⇑φc with hφdef
  have hφc : Continuous φ := φc.continuous
  have hφcs : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hφs.trans Ioo_subset_Icc_self)
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => (hφ01 x).1
  have hφle1 : ∀ x, φ x ≤ 1 := fun x => (hφ01 x).2
  have hφK : ∀ x ∈ T0, 1 ≤ φ x := fun x hx => le_of_eq (hφ1 hx).symm
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
  -- sup-norm Lipschitz dependence of `g q` on `q`
  set Cf : ℝ := Cf₀ with hCfdef
  have hfx : ∀ q ∈ K, ∀ x, |fam q x| ≤ |Cf| := fun q hq x => (hCf₀ q hq x).trans (le_abs_self _)
  set A : ℝ := γ / 2 * (|2 / Real.sqrt κ| / (c₀ / 2) * L) with hA
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (mul_nonneg hLh0 hL)
  have hEq : ∀ q ∈ K, ∀ x, Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p x))) ≤ EB := fun q hq x =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans
      (h0cut_abs_le_bound κ hc1 ((hcl q hq).2.1 _ (hthk _ (hpI x))))) (by positivity))
  have hgsup : ∀ q ∈ K, ∀ q' ∈ K, A * ‖q - q'‖ ≤ 1 → ∀ x,
      |g q x - g q' x| ≤ EB * |fam q x - fam q' x| + |Cf| * (2 * EB) * (A * ‖q - q'‖) := by
    intro q hq q' hq' hA1 x
    have hd : |γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p x)) - γ / 2 * h0cut κ (c₀ / 2) (Ψ q' (p x))| ≤
        A * ‖q - q'‖ := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < γ / 2), hA, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc _ ≤ |2 / Real.sqrt κ| / (c₀ / 2) * ‖Ψ q (p x) - Ψ q' (p x)‖ :=
            h0cut_abs_sub_le κ hc1 _ _
        _ ≤ |2 / Real.sqrt κ| / (c₀ / 2) * (L * ‖q - q'‖) :=
            mul_le_mul_of_nonneg_left (hlip q hq q' hq' _ (hthk _ (hpI x))) hLh0
        _ = _ := by ring
    have he := abs_exp_sub_exp_le (hd.trans hA1)
    have e : g q x - g q' x = (fam q x - fam q' x) *
        Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p x))) +
        fam q' x * (Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p x))) -
        Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q' (p x)))) := by simp only [hg]; ring
    rw [e]
    have he' : |Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p x))) -
        Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q' (p x)))| ≤ 2 * EB * (A * ‖q - q'‖) :=
      he.trans (mul_le_mul (by linarith [hEq q' hq' x]) hd (abs_nonneg _) (by positivity))
    have t1 : |(fam q x - fam q' x) * Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p x)))| ≤
        EB * |fam q x - fam q' x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hEq q hq x) (abs_nonneg _)
    have t2 : |fam q' x * (Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q (p x))) -
        Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q' (p x))))| ≤
        |Cf| * (2 * EB) * (A * ‖q - q'‖) := by
      rw [abs_mul]
      calc _ ≤ |Cf| * (2 * EB * (A * ‖q - q'‖)) :=
            mul_le_mul (hfx q' hq' x) he' (abs_nonneg _) (abs_nonneg _)
        _ = _ := by ring
    exact (abs_add_le _ _).trans (add_le_add t1 t2)
  have hnet : ∀ ε > 0, ∃ S : Finset (ℝ → ℝ), (∀ h ∈ S, h ∈ g '' K) ∧
      ∀ h ∈ g '' K, ∃ h' ∈ S, ∀ x, |h x - h' x| ≤ ε := by
    intro ε hε
    set Λ : ℝ := |Cf| * (2 * EB) * A with hΛ
    have hΛ0 : 0 ≤ Λ := mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) hA0
    obtain ⟨δm, hδm, hmodδ⟩ := hmod (ε / (2 * (EB + 1))) (by positivity)
    set δ : ℝ := min (min (1 / (A + 1)) (ε / (2 * (Λ + 1)))) δm with hδ
    have hδ0 : 0 < δ := lt_min (lt_min (div_pos one_pos (by linarith))
      (div_pos hε (by linarith))) hδm
    obtain ⟨T, hTK, hTf, hcov⟩ := finite_approx_of_totallyBounded hK.totallyBounded δ hδ0
    classical
    refine ⟨hTf.toFinset.image g, ?_, ?_⟩
    · intro h hh
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hh
      exact ⟨y, hTK (hTf.mem_toFinset.1 hy), rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨y, hyT, hqy⟩ := mem_iUnion₂.1 (hcov hq)
      refine ⟨g y, Finset.mem_image.2 ⟨y, hTf.mem_toFinset.2 hyT, rfl⟩, fun x => ?_⟩
      have hd : ‖q - y‖ ≤ δ := by rw [← dist_eq_norm]; exact (mem_ball.1 hqy).le
      have hd1 : ‖q - y‖ ≤ 1 / (A + 1) := hd.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hd2 : ‖q - y‖ ≤ ε / (2 * (Λ + 1)) :=
        hd.trans ((min_le_left _ _).trans (min_le_right _ _))
      have hd3 : ‖q - y‖ ≤ δm := hd.trans (min_le_right _ _)
      have h1 : A * ‖q - y‖ ≤ 1 :=
        calc A * ‖q - y‖ ≤ (A + 1) * (1 / (A + 1)) :=
              mul_le_mul (by linarith) hd1 (norm_nonneg _) (by linarith)
          _ = 1 := by field_simp
      have h2 : Λ * ‖q - y‖ ≤ ε / 2 :=
        calc Λ * ‖q - y‖ ≤ (Λ + 1) * (ε / (2 * (Λ + 1))) :=
              mul_le_mul (by linarith) hd2 (norm_nonneg _) (by linarith)
          _ = ε / 2 := by field_simp
      have h3 : EB * |fam q x - fam y x| ≤ ε / 2 :=
        calc EB * |fam q x - fam y x| ≤ (EB + 1) * (ε / (2 * (EB + 1))) :=
              mul_le_mul (by linarith) (hmodδ q hq y (hTK hyT) hd3 x) (abs_nonneg _)
                (by linarith)
          _ = ε / 2 := by field_simp
      have h4 := hgsup q hq y (hTK hyT) h1 x
      have e4 : |Cf| * (2 * EB) * (A * ‖q - y‖) = Λ * ‖q - y‖ := by rw [hΛ]; ring
      linarith
  -- convergence for the members of the family, and for `φ`
  have hconvF : ∀ h ∈ g '' K, ∀ η > 0, ∀ᶠ k in atTop, ∀ i : K,
      |∫ x, h x ∂bdryApprox γ (coordChange (X ω) (Ψ i.1) (Qc γ)) k -
        ∫ u in Icc (Ψ i.1 (a : ℝ)).re (Ψ i.1 (b : ℝ)).re,
          h (Function.invFunOn (fun t : ℝ => (Ψ i.1 t).re) (Icc (a : ℝ) b) u) ∂ν0| ≤ η := by
    rintro _ ⟨q, hq, rfl⟩ η hη
    filter_upwards [hT (g q) (hgc q hq) (hgcs q hq) ((hgs q hq).trans hT0s) η hη] with k hk i
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
  have hLlip : ∀ i : K, ∀ f₁ ∈ g '' K, ∀ f₂ ∈ g '' K, ∀ ε : ℝ, 0 ≤ ε →
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
      (Qc γ)) k) hε hφ0 hφK (hgK q₁ hq₁) (hgK q₂ hq₂) (hgc q₁ hq₁).stronglyMeasurable
      (hgc q₂ hq₂).stronglyMeasurable hC₁ hC₂ hsup (hφint.mono fun k hk => hk i)
      (fun η hη => (hconvF _ ⟨q₁, hq₁, rfl⟩ η hη).mono fun k hk => hk i)
      (fun η hη => (hconvF _ ⟨q₂, hq₂, rfl⟩ η hη).mono fun k hk => hk i)
      (fun η hη => (hφconv η hη).mono fun k hk => hk i)
    calc _ ≤ ε * _ := key
      _ ≤ ε * Mφ := mul_le_mul_of_nonneg_left (hLφ i.1 i.2) hε
      _ ≤ |Mφ| * ε := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hε
  have hU := unif_testFamily (K := T0) (Mφ := Mφ) (D := |Mφ|) (F := g '' K)
    hφ0 hφK hφint hφconv (fun i => hLφ i.1 i.2)
    (by rintro _ ⟨q, hq, rfl⟩ x hx; exact hgK q hq x hx)
    (by rintro _ ⟨q, hq, rfl⟩; exact (hgc q hq).stronglyMeasurable)
    (by rintro _ ⟨q, hq, rfl⟩; exact hgb q hq) hLlip hnet hconvF
  -- the weight: eventual closeness
  have hrad : Tendsto (fun k : ℕ => radius k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  set G : ℝ := γ / 2 * (|2 / Real.sqrt κ| / (c₀ / 2) * (4 * (M : ℝ) / ρ)) with hG
  set Cw : ℝ := |Cf| * (2 * EB) * G with hCw
  have ev1 : ∀ᶠ k in atTop, radius k < (ρ : ℝ) / 2 := hrad.eventually (gt_mem_nhds (by positivity))
  have ev2 : ∀ᶠ k in atTop, G * radius k ≤ 1 := by
    have : Tendsto (fun k => G * radius k) atTop (𝓝 0) := by simpa using hrad.const_mul G
    exact (this.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have ev3 : ∀ᶠ k in atTop, Cw * radius k * (|Mφ| + 1) ≤ η / 2 := by
    have : Tendsto (fun k => Cw * radius k * (|Mφ| + 1)) atTop (𝓝 0) := by
      simpa using (hrad.const_mul Cw).mul_const (|Mφ| + 1)
    exact (this.eventually (gt_mem_nhds (by positivity))).mono fun k hk => hk.le
  filter_upwards [hU (η / 2) (by positivity), hAdd, ev1, ev2, ev3, hφint, hφconv 1 one_pos]
    with k hkU hkA hk1 hk2 hk3 hkI hkφ q hq
  set μ := bdryApprox γ (coordChange (X ω) (Ψ q) (Qc γ)) k with hμ
  set W : ℝ → ℝ := fun t => Real.exp (γ / 2 *
    (avgReg (coordChange (ofFun (h0rev κ) + X ω) (Ψ q) (Qc γ)) k (t : ℂ) -
      avgReg (coordChange (X ω) (Ψ q) (Qc γ)) k (t : ℂ))) with hW
  have hUq : |∫ x, g q x ∂μ - ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
      fam q (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u) *
        Real.exp (γ / 2 * h0rev κ u) ∂ν0| ≤ η / 2 := by
    rw [← setIntegral_h0cut_conv (c := c₀ / 2) (κ := κ) (γ := γ) (hcl q hq) hρ hab.le
      (fun z hz => le_trans (by linarith : c₀ / 2 ≤ c₀) (hsep q hq z hz)) (fam q) ν0]
    exact hkU ⟨q, hq⟩ (g q) ⟨q, hq, rfl⟩
  have hCw0 : 0 ≤ Cw * radius k :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity))
      (mul_nonneg (by positivity) (mul_nonneg hLh0 (by
        have := norm_deriv_le_of_class' (hcl q hq) hρ (t := (a : ℝ)) ⟨le_rfl, hab.le⟩
        exact (norm_nonneg _).trans this)))) (radius_pos k).le
  have hwc : ∀ x, |fam q x * W x - g q x| ≤ Cw * radius k * φ x := by
    intro x
    by_cases hx : x ∈ T0
    · have hxI : x ∈ Icc (a : ℝ) b := Ioo_subset_Icc_self (hT0s hx)
      have hWx : W x = Real.exp (γ / 2 *
          ∫ w, h0rev κ w ∂((foldedCircle (x : ℂ) (radius k)).map (Ψ q))) := by
        simp only [hW]; rw [hkA q hq x hxI, add_sub_cancel_left]
      have hH := h0avg_push_close κ (hcl q hq) hρ hc₀ (hsep q hq) hxI (radius_pos k) hk1
      have hd : |γ / 2 * ∫ w, h0rev κ w ∂((foldedCircle (x : ℂ) (radius k)).map (Ψ q)) -
          γ / 2 * h0cut κ (c₀ / 2) (Ψ q x)| ≤ G * radius k := by
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < γ / 2), hG]
        calc _ ≤ γ / 2 * (|2 / Real.sqrt κ| / (c₀ / 2) * (4 * (M : ℝ) / ρ * radius k)) :=
              mul_le_mul_of_nonneg_left hH (by positivity)
          _ = _ := by ring
      have he := abs_exp_sub_exp_le (hd.trans hk2)
      have hEy : Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q x)) ≤ EB :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans
          (h0cut_abs_le_bound κ hc1 ((hcl q hq).2.1 _ (hthk _ hxI)))) (by positivity))
      have hgx : g q x = fam q x * Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q x)) := by
        simp only [hg, hpid x hxI]
      rw [hWx, hgx, ← mul_sub, abs_mul]
      have he' := he.trans (mul_le_mul_of_nonneg_right
        (by linarith [hEy] : 2 * Real.exp (γ / 2 * h0cut κ (c₀ / 2) (Ψ q x)) ≤ 2 * EB)
        (abs_nonneg _))
      calc _ ≤ |Cf| * (2 * EB * (G * radius k)) := mul_le_mul (hfx q hq x) (he'.trans
            (mul_le_mul_of_nonneg_left hd (by positivity))) (abs_nonneg _) (abs_nonneg _)
        _ = Cw * radius k * 1 := by rw [hCw]; ring
        _ ≤ Cw * radius k * φ x := mul_le_mul_of_nonneg_left (hφK x hx) hCw0
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hfams q hq h)), hgK q hq x hx, zero_mul, sub_zero, abs_zero]
      exact mul_nonneg hCw0 (hφ0 x)
  obtain ⟨Cg, hCg⟩ := hgb q hq
  have hb₂ := abs_le_mul_of_vanish (hgK q hq) hCg hφ0 hφK
  have hb₁ : ∀ x, |fam q x * W x| ≤ (Cg + Cw * radius k) * φ x := fun x => by
    have := abs_sub_abs_le_abs_sub (fam q x * W x) (g q x)
    linarith [hwc x, hb₂ x, add_mul Cg (Cw * radius k) (φ x)]
  have hWm : Measurable W := Real.measurable_exp.comp (measurable_const.mul
    ((measurable_avgReg_real _ k).sub (measurable_avgReg_real _ k)))
  have key := abs_integral_sub_le_dom (hkI ⟨q, hq⟩)
    ((hfamc q hq).measurable.mul hWm).aestronglyMeasurable (hgc q hq).aestronglyMeasurable hb₁ hb₂ hwc
  have hφle : ∫ x, φ x ∂μ ≤ |Mφ| + 1 := by
    have := (abs_le.1 (hkφ ⟨q, hq⟩)).2
    linarith [hLφ q hq, le_abs_self Mφ]
  have hm1 : Cw * radius k * ∫ x, φ x ∂μ ≤ Cw * radius k * (|Mφ| + 1) :=
    mul_le_mul_of_nonneg_left hφle hCw0
  simp only [Pi.mul_apply] at key
  rw [integral_bdryApprox_eq_weighted γ (coordChange (X ω) (Ψ q) (Qc γ)) _ k (fam q)]
  have hWe : ∀ t : ℝ, Real.exp (γ / 2 *
      (avgReg (coordChange (ofFun (h0rev κ) + X ω) (Ψ q) (Qc γ)) k (t : ℂ) -
        avgReg (coordChange (X ω) (Ψ q) (Qc γ)) k (t : ℂ))) = W t := fun t => rfl
  simp only [hWe]
  change |∫ x, fam q x * W x ∂μ - _| ≤ η
  change |∫ x, fam q x * W x ∂μ - ∫ x, g q x ∂μ| ≤ Cw * radius k * ∫ x, φ x ∂μ at key
  rw [abs_le] at key hUq ⊢
  constructor <;> linarith [key.1, key.2, hUq.1, hUq.2]

end SWCore
end QuantumZipper
