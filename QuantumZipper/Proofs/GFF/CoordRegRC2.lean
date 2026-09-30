import QuantumZipper.Proofs.GFF.CoordRegPush
import QuantumZipper.Proofs.GFF.CoordRegKolm

/-!
# RC2: every-circle regularity after an unzip map (`AUDIT3.md` §4.1)

Main result `ae_isRegularSample_coordChange_revMap`: for a free-boundary GFF modulo constants
`X`, a continuous driver `W`, `T ≥ 0`, `f = revMap W T`, a mean `g = a · log ‖·‖ + g₁` with `g₁`
continuous (this includes `h0rev κ`, `ae_isRegularSample_coordChange_h0rev`) and any `Q`,
almost surely `coordChange (ofFun g + X ω) f Q` is a regular sample, provided the energy modulus
(E) of `f` holds (`EnergyModulus W T β`, the statement of
`TwoPoint.abs_kernelCov2_revMap_foldedCircle_le` in `Proofs/Loewner/TwoPointEnergy.lean` with
exponent `β = 1/12`; taken as a hypothesis because that module is not built yet).

Route: the proof of Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185
(2011), pp. 333–393, Proposition 3.1 as numbered in the arXiv version (arXiv:0808.1560, p. 18;
**adapted**: DS consider circle averages of a zero-boundary field, here they are pushed forward by
the unzip map) — circle averages have a continuous modification: a variance modulus
gives high Gaussian moments, then the multiparameter Kolmogorov–Čentsov theorem, as formalized in
node M4-R3 (`RegularSample.lean`), with the Frostman bound (F) and the energy modulus (E) of the
unzip map supplying the constants (a Hölder instead of a Lipschitz variance modulus):

1. The process `V(q) = X(f_* fc(cen q, rad q))`, `q ∈ ℝ⁴` (the last coordinate is unused), has
   Gaussian increments of variance `≤ K_R ‖q − q'‖^β` on boxes, by (E) for close parameters and a
   crude bound otherwise; Kolmogorov's criterion with general exponents (`KolmG`; Revuz–Yor,
   *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. I, Thm (2.1), pp. 26–27) gives a
   continuous modification `V̂`.
2. At the countably many dyadic circles, RC1 (log form, `CoordRegLog`) identifies the raw values
   of the unzipped field: `y(fc(c, r)) = V(c, r) + D(c, r)`, `D = Dfun` the deterministic part.
   The witness is `F(w, r) = V̂(w, r) + D(w, r)`; clause (i) follows.
3. Clause (ii): `∫ F(u, ρ) dfc(w, r)(u)` equals `Φ(w, r, ρ) = ∫ F(v, r) dfc(w, ρ)(v)`: for the
   deterministic part by the smoothing symmetry `integral_Dfun_swap`; for `V̂` almost surely at
   each point, by stochastic Fubini (`integral_kernelAvg_ae_eq_bind`) on both sides and
   `fc(w,r).bind fc(·,ρ) = fc(w,ρ).bind fc(·,r)` (`foldedCircle_bind_comm`); everywhere by
   continuity and density. `Φ` is jointly continuous up to `ρ = 0`, with `Φ(w, r, 0) = F(w, r)`.

The commutation step (3) replaces the four-parameter process `X(ν_q)` of M4-R3; it is our own
elementary argument (no source needed: both sides are the law of `foldH(w + r e^{iθ} + ρ e^{iφ})`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace CoordReg

open RegSample KolmD KolmG CircleFubini FrostmanReg

/-- The energy modulus (E) of the unzip map `revMap W T`, with exponent `β` (the conclusion of
`TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`, where `β = 1/12`). -/
def EnergyModulus (W : ℝ → ℝ) (T β : ℝ) : Prop :=
  ∀ r₀ R : ℝ, 0 < r₀ → ∃ Cst : ℝ, ∀ (w w' : ℂ) (r r' : ℝ), r₀ ≤ r → r₀ ≤ r' →
    ‖w‖ + r ≤ R → ‖w'‖ + r' ≤ R → ‖w - w'‖ + |r - r'| ≤ 1 →
    |kernelCov2 neumannH ((foldedCircle w r).map (revMap W T), (foldedCircle w' r').map (revMap W T))
        ((foldedCircle w r).map (revMap W T), (foldedCircle w' r').map (revMap W T))| ≤
      Cst * (‖w - w'‖ + |r - r'|) ^ β

variable {W : ℝ → ℝ} {T : ℝ}

/-! ## Parameters on boxes -/

theorem norm_cen_add_rad_le {R : ℕ} {q : Fin 4 → ℝ} (hq : q ∈ boxD R) :
    ‖cen q‖ + rad q ≤ 2 * R + Real.exp R := by
  have h0 := abs_le.1 (hq 0)
  have h1 := abs_le.1 (hq 1)
  have h2 := abs_le.1 (hq 2)
  have hc : ‖cen q‖ ≤ 2 * R := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (cen q).re = q 0 := rfl
    have e2 : (cen q).im = |q 1| := rfl
    rw [e1, e2, abs_abs]
    have := hq 0; have := hq 1
    linarith
  have hr : rad q ≤ Real.exp R := by
    apply Real.exp_le_exp.2
    have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hl1 := log_two_le_one
    nlinarith
  linarith

theorem dist_param_le {R : ℕ} {q q' : Fin 4 → ℝ} (hq : q ∈ boxD R) (hq' : q' ∈ boxD R) :
    ‖cen q - cen q'‖ + |rad q - rad q'| ≤ (Real.exp R + 3) * ‖q - q'‖ := by
  have := param_lip hq hq'
  linarith [abs_nonneg (sm q - sm q')]

variable (hW : Continuous W) (hT : 0 ≤ T)
include hW hT

/-- Raw increment variance bound on boxes, from (E). -/
theorem kernelCov2_pK_le_box {β : ℝ} (hβ : 0 < β) (hE : EnergyModulus W T β) (R : ℕ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ q ∈ boxD (d := 4) R, ∀ q' ∈ boxD R,
      |kernelCov2 neumannH (pK hW hT (rad q) (cen q), pK hW hT (rad q') (cen q'))
        (pK hW hT (rad q) (cen q), pK hW hT (rad q') (cen q'))| ≤ K₁ * ‖q - q'‖ ^ β := by
  set r₀ := Real.exp (-(R : ℝ)) with hr₀
  have hr₀0 : 0 < r₀ := Real.exp_pos _
  set R₀ := 2 * (R : ℝ) + Real.exp R with hR₀
  obtain ⟨Cst, hCst⟩ := hE r₀ R₀ hr₀0
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT R₀
  set Cc := ENNReal.ofReal (frostC T r₀ R₀ * 1 ^ (1 / 3 : ℝ) / (1 / 3)) with hCc
  set b₀ := (ENNReal.ofReal (2 * Real.log (max (2 * Bf) 1)) + 2 * Cc).toReal with hb₀
  have hb₀0 : 0 ≤ b₀ := ENNReal.toReal_nonneg
  set L := Real.exp R + 3 with hL
  have hL0 : 0 < L := by positivity
  have hbox : ∀ q ∈ boxD (d := 4) R, r₀ ≤ rad q ∧ ‖cen q‖ + rad q ≤ R₀ := fun q hq =>
    ⟨rad_ge hq, norm_cen_add_rad_le hq⟩
  have hkc : ∀ q ∈ boxD (d := 4) R, ∀ q' ∈ boxD R,
      |kernelCov neumannH (pK hW hT (rad q) (cen q)) (pK hW hT (rad q') (cen q'))| ≤ b₀ := by
    intro q hq q' hq'
    obtain ⟨a1, a2⟩ := hbox q hq
    obtain ⟨b1, b2⟩ := hbox q' hq'
    have := abs_kernelCov_le (pushK_support hW hT hBf (rad_pos q) a2)
      (pushK_support hW hT hBf (rad_pos q') b2) ENNReal.ofReal_ne_top
      (pushK_pot hW hT hr₀0 b1 b2)
    have e : nBound (pK hW hT (rad q) (cen q)) (pK hW hT (rad q') (cen q')) Bf Cc =
        ENNReal.ofReal (2 * Real.log (max (2 * Bf) 1)) + 2 * Cc := by
      simp only [nBound, measure_univ, one_mul, mul_one]
    rwa [e] at this
  refine ⟨(|Cst| + 4 * b₀) * L ^ β, by positivity, fun q hq q' hq' => ?_⟩
  set E := kernelCov2 neumannH (pK hW hT (rad q) (cen q), pK hW hT (rad q') (cen q'))
    (pK hW hT (rad q) (cen q), pK hW hT (rad q') (cen q'))
  have hcrude : |E| ≤ 4 * b₀ := by
    simp only [E, kernelCov2]
    have a1 := abs_le.1 (hkc q hq q hq)
    have a2 := abs_le.1 (hkc q hq q' hq')
    have a3 := abs_le.1 (hkc q' hq' q hq)
    have a4 := abs_le.1 (hkc q' hq' q' hq')
    rw [abs_le]; constructor <;> linarith
  set δ := ‖cen q - cen q'‖ + |rad q - rad q'| with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδL : δ ≤ L * ‖q - q'‖ := dist_param_le hq hq'
  have hpow : δ ^ β ≤ L ^ β * ‖q - q'‖ ^ β := by
    rw [← Real.mul_rpow hL0.le (norm_nonneg _)]
    exact Real.rpow_le_rpow hδ0 hδL hβ.le
  have hLq : 0 ≤ L ^ β * ‖q - q'‖ ^ β := by positivity
  rcases le_or_gt δ 1 with h1 | h1
  · obtain ⟨a1, a2⟩ := hbox q hq
    obtain ⟨b1, b2⟩ := hbox q' hq'
    have hE' := hCst (cen q) (cen q') (rad q) (rad q') a1 b1 a2 b2 h1
    have : |E| ≤ |Cst| * δ ^ β :=
      hE'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    calc |E| ≤ |Cst| * (L ^ β * ‖q - q'‖ ^ β) :=
          this.trans (mul_le_mul_of_nonneg_left hpow (abs_nonneg _))
      _ ≤ (|Cst| + 4 * b₀) * L ^ β * ‖q - q'‖ ^ β := by
          nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb₀0) hLq]
  · have hone : 1 ≤ L ^ β * ‖q - q'‖ ^ β :=
      (Real.one_le_rpow h1.le hβ.le).trans hpow
    calc |E| ≤ 4 * b₀ * (L ^ β * ‖q - q'‖ ^ β) :=
          hcrude.trans (le_mul_of_one_le_right (by positivity) hone)
      _ ≤ (|Cst| + 4 * b₀) * L ^ β * ‖q - q'‖ ^ β := by
          nlinarith [mul_nonneg (abs_nonneg Cst) hLq]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem pK_admissible' (u : ℂ) {r : ℝ} (hr : 0 < r) : IsAdmissibleH (pK hW hT r u) := by
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT (‖u‖ + r)
  exact pushK_admissible hW hT hBf hr le_rfl

theorem map_pK_diff_eq_gaussianReal (hX : IsFreeGFFModConstH X P) {a b : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    P.map (fun ω => X ω (pK hW hT r a) - X ω (pK hW hT s b)) =
      gaussianReal 0 (kernelCov2 neumannH (pK hW hT r a, pK hW hT s b)
        (pK hW hT r a, pK hW hT s b)).toNNReal := by
  have hadz := pK_admissible' hW hT a hr
  have hadw := pK_admissible' hW hT b hs
  have hmass : (pK hW hT r a) univ = (pK hW hT s b) univ := by simp [measure_univ]
  have hG : HasGaussianLaw (fun ω => X ω (pK hW hT r a) - X ω (pK hW hT s b)) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(pK hW hT r a, pK hW hT s b), hadz, hadw, hmass⟩
  have hm : AEMeasurable (fun ω => X ω (pK hW hT r a) - X ω (pK hW hT s b)) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω (pK hW hT r a) - X ω (pK hW hT s b)] = 0 :=
    hX.centered _ _ hadz hadw hmass
  have hcov := hX.covariance_eq (pK hW hT r a, pK hW hT s b) (pK hW hT r a, pK hW hT s b)
    hadz hadw hmass hadz hadw hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

/-- Moment bound for the pushed circle process. -/
theorem momentBound_pK (hX : IsFreeGFFModConstH X P) {β : ℝ} (hβ : 0 < β)
    (hE : EnergyModulus W T β) (m : ℕ) (R : ℕ) :
    ∃ K, 0 ≤ K ∧ MomentBoundG (fun q ω => X ω (pK hW hT (rad q) (cen q))) P (2 * m)
      (m * β) K R := by
  obtain ⟨K₁, hK₁, hb⟩ := kernelCov2_pK_le_box hW hT hβ hE R
  refine ⟨K₁ ^ m * gaussianAbsMoment (2 * m),
    mul_nonneg (pow_nonneg hK₁ _) (gaussianAbsMoment_nonneg _), fun q hq q' hq' => ?_⟩
  beta_reduce
  rw [lintegral_pow_two_mul_of_map_eq (U := fun ω => X ω (pK hW hT (rad q) (cen q)) -
    X ω (pK hW hT (rad q') (cen q'))) ((hX.measurable_coord _).sub (hX.measurable_coord _)) m
    (map_pK_diff_eq_gaussianReal hW hT hX (rad_pos q) (rad_pos q'))]
  apply ENNReal.ofReal_le_ofReal
  set E := kernelCov2 neumannH (pK hW hT (rad q) (cen q), pK hW hT (rad q') (cen q'))
    (pK hW hT (rad q) (cen q), pK hW hT (rad q') (cen q'))
  have hv : ((E.toNNReal : ℝ≥0) : ℝ) ≤ K₁ * ‖q - q'‖ ^ β := by
    rw [Real.coe_toNNReal']
    exact max_le ((le_abs_self E).trans (hb q hq q' hq')) (by positivity)
  have hm := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv m
  have e : (K₁ * ‖q - q'‖ ^ β) ^ m = K₁ ^ m * ‖q - q'‖ ^ ((m : ℝ) * β) := by
    rw [mul_pow, mul_comm (m : ℝ) β, Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]
  calc ((E.toNNReal : ℝ≥0) : ℝ) ^ m * gaussianAbsMoment (2 * m)
      ≤ (K₁ * ‖q - q'‖ ^ β) ^ m * gaussianAbsMoment (2 * m) :=
        mul_le_mul_of_nonneg_right hm (gaussianAbsMoment_nonneg _)
    _ = K₁ ^ m * gaussianAbsMoment (2 * m) * ‖q - q'‖ ^ ((m : ℝ) * β) := by rw [e]; ring

omit hW hT in
/-- The Kolmogorov exponents: `θ = 2^{-β/4}`, `m = ⌈8/β⌉ + 1`. -/
theorem kolm_exponents {β : ℝ} (hβ : 0 < β) :
    0 < (2 : ℝ) ^ (-β / 4) ∧ (2 : ℝ) ^ (-β / 4) < 1 ∧
      16 * ((1 / 2 : ℝ) ^ (((⌈8 / β⌉₊ + 1 : ℕ) : ℝ) * β) /
        ((2 : ℝ) ^ (-β / 4)) ^ (2 * (⌈8 / β⌉₊ + 1))) < 1 := by
  set m : ℕ := ⌈8 / β⌉₊ + 1 with hm
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith), ?_⟩
  have hmβ : 8 < (m : ℝ) * β := by
    have h1 : 8 / β ≤ (⌈8 / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m : ℝ) = ⌈8 / β⌉₊ + 1 := by rw [hm]; push_cast; ring
    rw [h2]
    have : 8 / β * β = 8 := div_mul_cancel₀ _ hβ.ne'
    nlinarith
  have e1 : (1 / 2 : ℝ) ^ ((m : ℝ) * β) = (2 : ℝ) ^ (-((m : ℝ) * β)) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have e2 : ((2 : ℝ) ^ (-β / 4)) ^ (2 * m) = (2 : ℝ) ^ (-β / 4 * (2 * m : ℕ)) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have e3 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [e1, e2, e3, ← Real.rpow_sub (by norm_num), ← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  push_cast
  nlinarith

/-! ## Assembly -/

omit hW hT in
theorem countable_dyadic_Hbar :
    ((⋃ n : ℕ, Set.range (dyadicRoundC n)) ∩ Hbar).Countable := by
  refine (Set.countable_iUnion fun n => ?_).mono inter_subset_left
  refine (Set.countable_range fun p : ℤ × ℤ => CircleCont.lpt n p.1 p.2).mono ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), (CircleCont.dyadicRoundC_eq_lpt n z).symm⟩

/-- Stochastic Fubini for the pushed circles, in the form used for clause (ii). -/
theorem ae_integral_Vhat_eq (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    {Vh : (Fin 4 → ℝ) → Ω → ℝ} (hVc : ∀ ω, Continuous fun q => Vh q ω)
    (hVV : ∀ q, (fun ω => Vh q ω) =ᵐ[P] fun ω => X ω (pK hW hT (rad q) (cen q)))
    {w : ℂ} (hw : w ∈ Hbar) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ u, Vh (pr u ρ 0) ω ∂foldedCircle w r =
      X ω ((foldedCircle w r).bind (pK hW hT ρ)) := by
  set R₁ := ‖w‖ + r with hR₁
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT (R₁ + ρ)
  have hK' : ∀ z ∈ ballH R₁, ‖z‖ + ρ ≤ R₁ + ρ := fun z hz => by
    have := hz.1; rw [mem_closedBall, dist_zero_right] at this; linarith
  have hpr : ∀ u ∈ Hbar, pK hW hT (rad (pr u ρ 0)) (cen (pr u ρ 0)) = pK hW hT ρ u :=
    fun u hu => by rw [cen_pr hu, rad_pr u hρ]
  have hYc : ∀ ω, ContinuousOn (fun u => Vh (pr u ρ 0) ω - Vh (pr w ρ 0) ω) Hbar := fun ω =>
    (((hVc ω).comp (continuous_pr_fst ρ 0)).sub continuous_const).continuousOn
  have hY : ∀ u ∈ Hbar, (fun ω => Vh (pr u ρ 0) ω - Vh (pr w ρ 0) ω) =ᵐ[P]
      fun ω => X ω (pK hW hT ρ u) - X ω (pK hW hT ρ w) := by
    intro u hu
    filter_upwards [hVV (pr u ρ 0), hVV (pr w ρ 0)] with ω h1 h2
    beta_reduce at h1 h2 ⊢
    rw [h1, h2, hpr u hu, hpr w hw]
  have hw' : w ∈ ballH R₁ := ⟨by rw [mem_closedBall, dist_zero_right]; linarith, hw⟩
  have hF := integral_kernelAvg_ae_eq_bind hX (pK hW hT ρ) (K' := ballH R₁) (R := Bf)
    ENNReal.ofReal_ne_top (fun z hz => pushK_support hW hT hBf hρ (hK' z hz))
    (fun z hz y => pushK_pot hW hT hρ le_rfl (hK' z hz) y) hw' hYc hY (foldedCircle w r)
    (isCompact_ballH R₁) inter_subset_right subset_rfl (foldedCircle_support hr.le le_rfl)
  filter_upwards [hF, hVV (pr w ρ 0)] with ω h1 h2
  have hint : Integrable (fun u => Vh (pr u ρ 0) ω) (foldedCircle w r) :=
    RegClosure.integrable_fc ((hVc ω).comp (continuous_pr_fst ρ 0)).continuousOn w hr.le
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul,
    measure_univ, one_smul] at h1
  beta_reduce at h2
  rw [hpr w hw] at h2
  linarith

omit hW hT in
theorem continuousOn_Vh_pr {Vh : (Fin 4 → ℝ) → Ω → ℝ} (hVc : ∀ ω, Continuous fun q => Vh q ω)
    (ω : Ω) : ContinuousOn (fun p : ℂ × ℝ => Vh (pr p.1 p.2 0) ω) {p | 0 < p.2} :=
  (hVc ω).comp_continuousOn (continuousOn_pr.comp
    (continuous_id.prodMk continuous_const).continuousOn fun _ hp => hp)

/-- **RC2 with an explicit witness.** -/
theorem exists_regular_witness_revMap (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 < β) (hE : EnergyModulus W T β) (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁)
    (Q : ℝ) :
    ∃ Vh : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Vh q ω) ∧
      (∀ q, (fun ω => Vh q ω) =ᵐ[P] fun ω => X ω (pK hW hT (rad q) (cen q))) ∧
      ∀ᵐ ω ∂P, IsRegularWith
        (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q)
        (fun p => Vh (pr p.1 p.2 0) ω + Dfun W T a g₁ Q p) := by
  obtain ⟨hθ0, hθ1, hρ⟩ := kolm_exponents hβ
  obtain ⟨Vh, hVc, hVV, hVlim⟩ := exists_continuous_modification_G (d := 4)
    (Z := fun q ω => X ω (pK hW hT (rad q) (cen q))) le_rfl hθ0 hθ1
    (fun q => (hX.measurable_coord _).aemeasurable) (by positivity) hρ
    (fun R => momentBound_pK hW hT hX hβ hE (⌈8 / β⌉₊ + 1) R)
  refine ⟨Vh, hVc, hVV, ?_⟩
  set G : ℂ → ℝ := fun v => a * Real.log ‖v‖ + g₁ v with hG
  set Sd : Set ℂ := (⋃ n : ℕ, Set.range (dyadicRoundC n)) ∩ Hbar with hSd
  have hraw : ∀ᵐ ω ∂P, ∀ c ∈ Sd, ∀ k : ℕ,
      evalReg (ofFun G + X ω) (pK hW hT (radius k) c) =
        (∫ v, G v ∂pK hW hT (radius k) c) + X ω (pK hW hT (radius k) c) :=
    (eventually_countable_ball countable_dyadic_Hbar).2 fun c _ => ae_all_iff.2 fun k => by
      obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT (‖c‖ + radius k)
      exact ae_evalReg_logAdd_eq_frostman hX (pushK_support hW hT hBf (radius_pos k) le_rfl)
        (pushK_frostman hW hT (radius_pos k) le_rfl le_rfl) (by norm_num) a hg₁.continuousOn
  set S : Set (ℂ × ℝ) := Hbar ×ˢ Ioi 0 with hS
  set S3 : Set ((ℂ × ℝ) × ℝ) := S ×ˢ Ioi 0 with hS3
  have hpt : ∀ p ∈ S3, ∀ᵐ ω ∂P, ∫ u, Vh (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2 =
      ∫ v, Vh (pr v p.1.2 0) ω ∂foldedCircle p.1.1 p.2 := by
    rintro ⟨⟨w, r⟩, ρ⟩ ⟨⟨hw, hr⟩, hρ'⟩
    simp only [mem_Ioi] at hr hρ'
    filter_upwards [ae_integral_Vhat_eq hW hT hX hVc hVV hw hr hρ',
      ae_integral_Vhat_eq hW hT hX hVc hVV hw hρ' hr] with ω h1 h2
    show ∫ u, Vh (pr u ρ 0) ω ∂foldedCircle w r = ∫ v, Vh (pr v r 0) ω ∂foldedCircle w ρ
    rw [h1, h2, pushKernel_bind_comm]
  obtain ⟨Dn, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S3
  have hall : ∀ᵐ ω ∂P, ∀ p ∈ Dn, ∫ u, Vh (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2 =
      ∫ v, Vh (pr v p.1.2 0) ω ∂foldedCircle p.1.1 p.2 :=
    (eventually_countable_ball hDc).2 fun p hp => hpt p (hDS hp)
  filter_upwards [hVlim, hraw, hall] with ω hlim hraw' hD
  have hDfc := continuousOn_Dfun hW hT a hg₁ Q
  have hVpr := continuousOn_Vh_pr hVc ω
  set F : ℂ × ℝ → ℝ := fun p => Vh (pr p.1 p.2 0) ω + Dfun W T a g₁ Q p with hF
  have hFc' : ContinuousOn F {p | 0 < p.2} := hVpr.add hDfc
  refine ⟨hFc'.mono fun p hp => (show (0 : ℝ) < p.2 from hp.2), fun k z hz => ?_, ?_⟩
  · -- clause (i)
    have hr := radius_pos k
    have hdz : ∀ n, dyadicRoundC n z ∈ Hbar := fun n => CircleCont.dyadicRoundC_mem_Hbar hz n
    have e : ∀ n, (coordChange (ofFun G + X ω) (revMap W T) Q)
        (foldedCircle (dyadicRoundC n z) (radius k)) =
        Dfun W T a g₁ Q (dyadicRoundC n z, radius k) +
          X ω (pK hW hT (rad (rndD n (pr z (radius k) 0))) (cen (rndD n (pr z (radius k) 0)))) := by
      intro n
      rw [rndD_pr, cen_pr (hdz n), rad_pr _ hr]
      have h1 := hraw' _ ⟨mem_iUnion.2 ⟨n, z, rfl⟩, hdz n⟩ k
      have h2 := integral_logAdd_pK hW hT a hg₁ Q (dyadicRoundC n z) hr
      show evalReg (ofFun G + X ω) (pK hW hT (radius k) (dyadicRoundC n z)) +
        Q * ∫ u, Real.log ‖deriv (revMap W T) u‖ ∂foldedCircle (dyadicRoundC n z) (radius k) = _
      rw [h1, ← h2, hG]
      ring
    have hDt : Tendsto (fun n => Dfun W T a g₁ Q (dyadicRoundC n z, radius k)) atTop
        (𝓝 (Dfun W T a g₁ Q (z, radius k))) :=
      (hDfc (z, radius k) (show (0 : ℝ) < radius k from hr)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨(RegClosure.tendsto_dyadicRoundC z).prodMk_nhds
          tendsto_const_nhds, Eventually.of_forall fun n => (show (0 : ℝ) < radius k from hr)⟩)
    have hVt := hlim (pr z (radius k) 0)
    have := hDt.add hVt
    rw [show F (z, radius k) = Dfun W T a g₁ Q (z, radius k) + Vh (pr z (radius k) 0) ω by
      simp only [hF]; ring]
    exact this.congr fun n => (e n).symm
  · -- clause (ii)
    have hH : ∀ {s : Set ((ℂ × ℝ) × ℝ)}, (∀ p ∈ s, 0 < p.1.2) →
        ContinuousOn (fun q : ((ℂ × ℝ) × ℝ) × ℂ => F (q.2, q.1.1.2)) (s ×ˢ Hbar) := by
      intro s hs
      have hm : Continuous fun q : ((ℂ × ℝ) × ℝ) × ℂ => (q.2, q.1.1.2) := by fun_prop
      exact hFc'.comp hm.continuousOn fun q hq => (show (0 : ℝ) < q.1.1.2 from hs _ hq.1)
    set Φ : (ℂ × ℝ) × ℝ → ℝ := fun p => ∫ v, F (v, p.1.2) ∂foldedCircle p.1.1 p.2 with hΦ
    have hΦc : ContinuousOn Φ (S ×ˢ Ici 0) :=
      RegClosure.continuousOn_integral_fc (P := (ℂ × ℝ) × ℝ) (H := fun p v => F (v, p.1.2))
        (c := fun p => p.1.1) (r := fun p => p.2) (hH fun p hp => hp.1.2)
        (continuous_fst.comp continuous_fst).continuousOn continuous_snd.continuousOn
    have hΦ0 : ∀ p ∈ S, Φ (p, 0) = F p := by
      intro p hp
      simp only [hΦ]
      rw [fc_zero, integral_dirac, foldH_of_mem' hp.1]
    -- the smoothed witness
    set GLw : (ℂ × ℝ) × ℝ → ℝ := fun p => ∫ u, Vh (pr u p.2 0) ω ∂foldedCircle p.1.1 p.1.2
    set GRw : (ℂ × ℝ) × ℝ → ℝ := fun p => ∫ v, Vh (pr v p.1.2 0) ω ∂foldedCircle p.1.1 p.2
    have hGL : ContinuousOn GLw S3 := by
      have hm : Continuous fun q : ((ℂ × ℝ) × ℝ) × ℂ => (q.2, q.1.2) := by fun_prop
      exact RegClosure.continuousOn_integral_fc (P := (ℂ × ℝ) × ℝ)
        (H := fun p u => Vh (pr u p.2 0) ω) (c := fun p => p.1.1) (r := fun p => p.1.2)
        (hVpr.comp hm.continuousOn fun q hq => (show (0 : ℝ) < q.1.2 from hq.1.2))
        (continuous_fst.comp continuous_fst).continuousOn
        (continuous_snd.comp continuous_fst).continuousOn
    have hGR : ContinuousOn GRw S3 := by
      have hm : Continuous fun q : ((ℂ × ℝ) × ℝ) × ℂ => (q.2, q.1.1.2) := by fun_prop
      exact RegClosure.continuousOn_integral_fc (P := (ℂ × ℝ) × ℝ)
        (H := fun p v => Vh (pr v p.1.2 0) ω) (c := fun p => p.1.1) (r := fun p => p.2)
        (hVpr.comp hm.continuousOn fun q hq => (show (0 : ℝ) < q.1.1.2 from hq.1.1.2))
        (continuous_fst.comp continuous_fst).continuousOn continuous_snd.continuousOn
    have hEqV : EqOn GLw GRw S3 := eqOn_of_dense hDS hSD hGL hGR fun p hp => hD p hp
    have hEq : ∀ p ∈ S, ∀ ρ : ℝ, 0 < ρ → ∫ u, F (u, ρ) ∂foldedCircle p.1 p.2 = Φ (p, ρ) := by
      rintro ⟨w, r⟩ ⟨hw, hr⟩ ρ hρ'
      simp only [mem_Ioi] at hr
      have iV : ∀ {s t : ℝ}, 0 < s → 0 ≤ t →
          Integrable (fun u => Vh (pr u s 0) ω) (foldedCircle w t) := fun hs ht =>
        RegClosure.integrable_fc (((hVc ω).comp (continuous_pr_fst _ 0)).continuousOn) w ht
      have iD : ∀ {s t : ℝ}, 0 < s → 0 ≤ t →
          Integrable (fun u => Dfun W T a g₁ Q (u, s)) (foldedCircle w t) := fun {s t} hs ht =>
        RegClosure.integrable_fc (hDfc.comp (continuous_id.prodMk continuous_const).continuousOn
          fun u _ => (show (0 : ℝ) < s from hs)) w ht
      simp only [hΦ, hF]
      rw [integral_add (iV hρ' hr.le) (iD hρ' hr.le), integral_add (iV hr hρ'.le)
        (iD hr hρ'.le), integral_Dfun_swap hW hT a hg₁ Q w hr hρ']
      congr 1
      exact hEqV (show ((w, r), ρ) ∈ S3 from ⟨⟨hw, hr⟩, hρ'⟩)
    refine RegClosure.tluo_of_dist_le (tluo_of_continuousOn (Φ := Φ) (hΦc.mono ?_)) ?_
    · intro p hp; exact ⟨⟨hp.1.1, hp.1.2⟩, hp.2⟩
    · filter_upwards [self_mem_nhdsWithin] with ρ (hρ' : 0 < ρ) q hq
      beta_reduce
      rw [hEq q hq ρ hρ', ← hΦ0 q hq]

/-- **RC2: every-circle regularity after an unzip map.** -/
theorem ae_isRegularSample_coordChange_revMap (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P] {β : ℝ} (hβ : 0 < β) (hE : EnergyModulus W T β) (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ∀ᵐ ω ∂P, IsRegularSample
      (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q) := by
  obtain ⟨Vh, -, -, h⟩ := exists_regular_witness_revMap hW hT hX hβ hE a hg₁ Q
  filter_upwards [h] with ω hω
  exact ⟨_, hω⟩

/-- **RC2 for the reverse coupling mean `h0rev κ`.** -/
theorem ae_isRegularSample_coordChange_h0rev (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P] {β : ℝ} (hβ : 0 < β) (hE : EnergyModulus W T β) (κ Q : ℝ) :
    ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (h0rev κ) + X ω) (revMap W T) Q) := by
  rw [h0rev_eq_logAdd κ]
  exact ae_isRegularSample_coordChange_revMap hW hT hX hβ hE _ continuous_const Q

end CoordReg
end QuantumZipper
