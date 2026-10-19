import GaussianLQG.Uniform.Holder.Chain

/-!
# U12, probabilistic part: moments of the coarse field and of the decoupled level bounds

Phase B, packet PB-U12 (ledger U12, Finding `fd:U12`, changes (i)–(iii); audit B-0b, M-1). With
`φ_{m,n} = phiMN W P m n` and covering data `ChainGeom A Q T P`:

* `lintegral_exp_supQ_le` (ledger change (i), audit M-1):
  `E e^{γ sup_Q |φ_{0,K}|} ≤ |A| 4^{γK + K₀√K}` for `0 ≤ γ ≤ 3/2`, with `K₀` chosen before the
  noise. Each offset square `c + [0,1]²` is moved to `[0,1]²` by the noise motion
  `W ∘ motionL2 1 c` (a white noise, `isWhiteNoise_isometry`, with `phi_motion`), where DDDF (2.11)
  (`prop2_expMoment_int` at `γ' = 3/2`) applies; Jensen (`lintegral_rpow_le_rpow`, exponent
  `2γ/3 ≤ 1`) then gives every `γ ≤ 3/2` with the same `K₀`;
* `Xdec`: the decoupled bound `e^{ξ sup_Q |φ_{0,K}|} (Σ_{r ∈ J} L(φ_{K,n}, r)^p)^{1/p}` of a family
  of moved `2^{-K} R_{2,1}` (as `S6P28U.XH`, `S6P28U.XS`, with `sup_Q` in place of `sup_{[0,1]²}`);
  `ae_len21_le_Xdec`: a.s. every crossing of the family for `φ_{0,n}` is at most `Xdec`
  (`eq:Decouplage`);
* `lintegral_Xdec_pow_le` (ledger change (ii), a `p`-th power `level_mean`): by independence of
  `φ_{0,K}` and `φ_{K,n}` and scaling (`lintegral_len21V_pow`),
  `E Xdec^p ≤ E e^{pξ sup_Q |φ_{0,K}|} · |J| 2^{-Kp} E L_{n−K}(R_{2,1})^p`;
* `lintegral_rectLen_pow_le`: the ledger's U10 moments in the form used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Holder

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.Blueprint LQGMetric.WhiteNoise
  LQGMetric.SupTail

/-! ### The supremum of the field over `Q` -/

/-- `sup_Q |g|` -/
def supQ (Q : Set ℂ) (g : ℂ → ℝ) : ℝ := ⨆ z : Q, |g z|

lemma abs_le_supQ {Q : Set ℂ} (hQ : IsCompact Q) {g : ℂ → ℝ} (hg : Continuous g) {z : ℂ}
    (hz : z ∈ Q) : |g z| ≤ supQ Q g := by
  have hbdd : BddAbove (range fun z : Q => |g z|) := by
    have := hQ.bddAbove_image (continuous_abs.comp hg).continuousOn
    rwa [image_eq_range] at this
  exact le_ciSup hbdd ⟨z, hz⟩

lemma measurable_comap_supQ {Q : Set ℂ} (hQ : IsCompact Q) (hne : Q.Nonempty) {Ω' : Type*}
    (F : Ω' → ℂ → ℝ) (hFc : ∀ ω, Continuous (F ω)) :
    Measurable[MeasurableSpace.comap F inferInstance] fun ω => supQ Q (F ω) := by
  let : MeasurableSpace Ω' := MeasurableSpace.comap F inferInstance
  have : CompactSpace Q := isCompact_iff_compactSpace.1 hQ
  have : Nonempty Q := hne.to_subtype
  exact measurable_iSup_of_continuous (X := fun (x : Q) ω => |F ω x|)
    (fun ω => continuous_abs.comp ((hFc ω).comp continuous_subtype_val))
    (fun x => continuous_abs.measurable.comp ((measurable_pi_apply (x : ℂ)).comp
      (comap_measurable F)))

lemma measurable_supQ {Q : Set ℂ} (hQ : IsCompact Q) (hne : Q.Nonempty) {Ω : Type*}
    [MeasurableSpace Ω] {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) : Measurable fun ω => supQ Q (fun z => Y z ω) := by
  have : CompactSpace Q := isCompact_iff_compactSpace.1 hQ
  have : Nonempty Q := hne.to_subtype
  exact measurable_iSup_of_continuous (X := fun (x : Q) ω => |Y x ω|)
    (fun ω => continuous_abs.comp ((hYc ω).comp continuous_subtype_val))
    (fun x => continuous_abs.measurable.comp (hYm x))

/-- `e^{γ sup_Q |g|} ≤ Σ_{c ∈ A} e^{γ sup_{[0,1]²} |g(· + c)|}` (the squares cover `Q`) -/
lemma exp_supQ_le_sum {A : Finset ℂ} {Q T : Set ℂ} {P : ℕ} (G : ChainGeom A Q T P)
    (hne : Q.Nonempty) {g : ℂ → ℝ} (hg : Continuous g) {γ : ℝ} (hγ : 0 ≤ γ) :
    Real.exp (γ * supQ Q g) ≤ ∑ c ∈ A, Real.exp (γ * S6D.supAbs (fun z => g (z + c))) := by
  have hA : A.Nonempty := G.nonempty_A hne.some_mem
  have h1 : supQ Q g ≤ A.sup' hA (fun c => S6D.supAbs (fun z => g (z + c))) := by
    have : Nonempty Q := hne.to_subtype
    refine ciSup_le fun z => ?_
    obtain ⟨c, hc, hzc⟩ := G.coverQ z z.2
    have h := S6D.abs_le_supAbs (g := fun z => g (z + c))
      (hg.comp (continuous_id.add continuous_const)) hzc
    simp only [sub_add_cancel] at h
    exact h.trans (Finset.le_sup' (fun c => S6D.supAbs (fun z => g (z + c))) hc)
  obtain ⟨c, hc, hcT⟩ := Finset.exists_mem_eq_sup' hA (fun c => S6D.supAbs (fun z => g (z + c)))
  calc Real.exp (γ * supQ Q g)
      ≤ Real.exp (γ * A.sup' hA (fun c => S6D.supAbs (fun z => g (z + c)))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hγ)
    _ = Real.exp (γ * S6D.supAbs (fun z => g (z + c))) := by rw [hcT]
    _ ≤ ∑ c ∈ A, Real.exp (γ * S6D.supAbs (fun z => g (z + c))) :=
        Finset.single_le_sum (f := fun c => Real.exp (γ * S6D.supAbs (fun z => g (z + c))))
          (fun _ _ => (Real.exp_pos _).le) hc

/-! ### The exponential moment of the coarse field -/

/-- **Jensen** for an exponent `θ ∈ [0,1]` (`S6D.lintegral_rpow_inv_le` for `θ ∈ (0,1)`) -/
lemma lintegral_rpow_le_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} (hY : AEMeasurable Y P) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) : ∫⁻ ω, Y ω ^ θ ∂P ≤ (∫⁻ ω, Y ω ∂P) ^ θ := by
  rcases h0.eq_or_lt with rfl | h0
  · simp
  rcases h1.eq_or_lt with rfl | h1
  · simp
  have hp : 1 < θ⁻¹ := (one_lt_inv₀ h0).2 h1
  have h := S6D.lintegral_rpow_inv_le hY hp
  rwa [one_div, inv_inv] at h

/-- **The exponential moment of `sup_Q |φ_{0,K}|`** (DDDF (2.11) on each offset square through the
noise motion, and Jensen from `γ' = 3/2`; ledger change (i), audit M-1): `K₀` is chosen before the
probability space and works for every `0 ≤ γ ≤ 3/2`. -/
theorem lintegral_exp_supQ_le : ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ {A : Finset ℂ} {Q T : Set ℂ} {Pn : ℕ}, ChainGeom A Q T Pn → Q.Nonempty →
    ∀ (K : ℕ) (γ : ℝ), 0 ≤ γ → γ ≤ 3 / 2 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 K z ω))) ∂P ≤
        ENNReal.ofReal (A.card * (4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))) := by
  obtain ⟨K₁, hK₁⟩ := prop2_expMoment_int (γ := 3 / 2) (by norm_num) (by norm_num)
  refine ⟨max K₁ 0, le_max_right _ _,
    fun {Ω} _ {P} {W} hW {A} {Q} {T} {Pn} G hne K γ hγ0 hγ1 => ?_⟩
  have hP := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  set K₀ := max K₁ 0 with hK₀
  have hsK : 0 ≤ √(K : ℝ) := Real.sqrt_nonneg _
  -- one offset square, moved to `[0,1]²` by the noise motion
  have hone : ∀ c : ℂ,
      AEMeasurable (fun ω => ENNReal.ofReal
        (Real.exp (γ * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω)))) P ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω))) ∂P ≤
        ENNReal.ofReal ((4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))) := by
    intro c
    set W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 c f)
    have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
    have hY' : ∀ x, (fun ω => phiMN W P 0 K (x + c) ω) =ᵐ[P] phi W' ((2 : ℝ) ^ K)⁻¹ 1 x := by
      intro x
      have e := phi_motion W (a := ((2 : ℝ) ^ K)⁻¹) (by positivity) 1 1 x c
      simp only [Circle.coe_one, one_mul] at e
      rw [← e]
      have := hφ.ae_eq (x + c)
      rwa [inv_pow, pow_zero] at this
    have hYc : ∀ ω, Continuous fun x => phiMN W P 0 K (x + c) ω :=
      fun ω => (hφ.cont ω).comp (continuous_id.add continuous_const)
    have hYm : ∀ x, Measurable fun ω => phiMN W P 0 K (x + c) ω := fun x => hφ.meas _
    obtain ⟨hint, hbd⟩ := hK₁ hW' K (fun x ω => phiMN W P 0 K (x + c) ω) hY' hYc
    have hSm : Measurable fun ω => S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω) :=
      measurable_supQ (Y := fun x ω => phiMN W P 0 K (x + c) ω) (isCompact_ferniqueBox 0 1)
        ⟨0, mem_ferniqueBox_self zero_le_one⟩ hYc hYm
    refine ⟨(ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (hSm.const_mul γ))).aemeasurable, ?_⟩
    set Z : Ω → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (Real.exp (3 / 2 * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω)))
    have hZ : AEMeasurable Z P :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hSm.const_mul _))).aemeasurable
    set θ := γ / (3 / 2) with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by norm_num)]; exact hγ1
    have e1 : ∀ ω, ENNReal.ofReal
        (Real.exp (γ * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω))) = Z ω ^ θ := by
      intro ω
      simp only [Z]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hθ0, ← Real.exp_mul]
      congr 2
      rw [hθ]; field_simp
    simp_rw [e1]
    refine (lintegral_rpow_le_rpow hZ hθ0 hθ1).trans ?_
    have hZint : ∫⁻ ω, Z ω ∂P = ENNReal.ofReal
        (∫ ω, Real.exp (3 / 2 * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω)) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
    have hI0 : 0 ≤ ∫ ω, Real.exp (3 / 2 * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω)) ∂P :=
      integral_nonneg fun ω => (Real.exp_pos _).le
    rw [hZint, ENNReal.ofReal_rpow_of_nonneg hI0 hθ0]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (∫ ω, Real.exp (3 / 2 * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω)) ∂P) ^ θ
        ≤ ((4 : ℝ) ^ (3 / 2 * (K : ℝ) + K₁ * √(K : ℝ))) ^ θ :=
          Real.rpow_le_rpow hI0 hbd hθ0
      _ = (4 : ℝ) ^ (γ * K + θ * K₁ * √(K : ℝ)) := by
          rw [← Real.rpow_mul (by norm_num)]
          congr 1
          rw [hθ]; field_simp
      _ ≤ (4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have : θ * K₁ ≤ K₀ := by
            rcases le_total 0 K₁ with h | h
            · calc θ * K₁ ≤ 1 * K₁ := mul_le_mul_of_nonneg_right hθ1 h
                _ = K₁ := one_mul _
                _ ≤ K₀ := le_max_left _ _
            · calc θ * K₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ0 h
                _ ≤ K₀ := le_max_right _ _
          have := mul_le_mul_of_nonneg_right this hsK
          linarith
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 K z ω))) ∂P
      ≤ ∫⁻ ω, ∑ c ∈ A, ENNReal.ofReal
          (Real.exp (γ * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (exp_supQ_le_sum G hne (hφ.cont ω) hγ0)
    _ = ∑ c ∈ A, ∫⁻ ω, ENNReal.ofReal
          (Real.exp (γ * S6D.supAbs (fun z => phiMN W P 0 K (z + c) ω))) ∂P :=
        lintegral_finsetSum' _ fun c _ => (hone c).1
    _ ≤ ∑ _c ∈ A, ENNReal.ofReal ((4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))) :=
        Finset.sum_le_sum fun c _ => (hone c).2
    _ = ENNReal.ofReal (A.card * (4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-! ### The decoupled level bounds -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the decoupled bound `e^{ξ sup_Q |φ_{0,K}|} (Σ_{r ∈ J} L(φ_{K,n}, r)^p)^{1/p}` of the crossings
of a family `J` of moved `2^{-K} R_{2,1}` (as `S6P28U.XH`, `S6P28U.XS`) -/
def Xdec (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (Q : Set ℂ) (n p K : ℕ) {ι : Type*}
    (J : Finset ι) (j : ι → Circle × ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ξ * supQ Q (fun z => phiMN W P 0 K z ω))) *
    S6P28U.ZqG ξ (fun x => phiMN W P K n x ω) K p J j

lemma phiMN_zero_eq (W : WNSpace → Ω → ℝ) (P : Measure Ω) (n : ℕ) :
    phiMN W P 0 n = phiVer W P ((2 : ℝ)⁻¹ ^ n) 1 := by
  rw [phiMN, pow_zero]

lemma inv_two_pow_le {K n : ℕ} (h : K ≤ n) : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ K :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem measurable_Xdec (hW : IsWhiteNoise P W) {Q : Set ℂ} (hQ : IsCompact Q)
    (hne : Q.Nonempty) {n K : ℕ} (hKn : K ≤ n) (p : ℕ) {ι : Type*} (J : Finset ι)
    (j : ι → Circle × ℂ) : Measurable (Xdec ξ W P Q n p K J j) := by
  have hφF := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  have hφG := isPhiVersion_phiMN (P := P) hW hKn
  have hGm : Measurable (fun ω x => phiMN W P K n x ω) :=
    measurable_pi_iff.2 fun x => hφG.meas x
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_supQ hQ hne hφF.cont hφF.meas).const_mul ξ))).mul
    ((S6P28U.measurable_comap_ZqG (ξ := ξ) _ hφG.cont _ p _ _).mono hGm.comap_le le_rfl)

/-- **`eq:Decouplage` on `Q`**: a.s., every crossing of the family for `φ_{0,n}` is at most the
decoupled bound -/
theorem ae_len21_le_Xdec (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) {Q : Set ℂ} (hQ : IsCompact Q)
    {n K p : ℕ} (hKn : K ≤ n) (hp : p ≠ 0) {ι : Type*} (J : Finset ι) (j : ι → Circle × ℂ)
    (hJ : ∀ r ∈ J, T20B.mot K (j r).1 (j r).2 '' (rectAB 2 1).toSet ⊆ Q) :
    ∀ᵐ ω ∂P, ∀ r ∈ J, S6D.len21 ξ (fun x => phiMN W P 0 n x ω) K (j r) ≤
      Xdec ξ W P Q n p K J j ω := by
  have hφF := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  filter_upwards [S6P28U.ae_phiVer_split hW (δ := (2 : ℝ)⁻¹ ^ n) (K := K) (by positivity)
    (inv_two_pow_le hKn)] with ω hω r hr
  have hdec : S6D.len21 ξ (fun x => phiMN W P 0 n x ω) K (j r) ≤
      ENNReal.ofReal (Real.exp (ξ * supQ Q (fun z => phiMN W P 0 K z ω))) *
        S6D.len21 ξ (fun x => phiMN W P K n x ω) K (j r) := by
    have h := crossLenIn_le_of_abs_sub_le (ξ := ξ) (f := fun x => phiMN W P 0 n x ω)
      (g := fun x => phiMN W P K n x ω)
      (U := T20B.mot K (j r).1 (j r).2 '' (rectAB 2 1).toSet)
      (A := T20B.mot K (j r).1 (j r).2 '' (rectAB 2 1).side₁)
      (B := T20B.mot K (j r).1 (j r).2 '' (rectAB 2 1).side₂)
      (c := supQ Q (fun z => phiMN W P 0 K z ω)) (fun x hx => by
        have e := hω x
        rw [← phiMN_zero_eq] at e
        have e' : phiVer W P ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ K) x ω = phiMN W P K n x ω := rfl
        rw [e, e', add_sub_cancel_right]
        exact abs_le_supQ hQ (hφF.cont ω) (hJ r hr hx))
    rwa [abs_of_nonneg hξ] at h
  refine hdec.trans ?_
  unfold Xdec
  gcongr
  exact S6P28U.len21_le_ZqG hp hr

/-- **The `p`-th moment of the decoupled bound** (a `p`-th power `level_mean`; ledger change (ii)):
independence of `φ_{0,K}` and `φ_{K,n}`, and the scaling `lintegral_len21V_pow`. -/
theorem lintegral_Xdec_pow_le (hW : IsWhiteNoise P W) {Q : Set ℂ} (hQ : IsCompact Q)
    (hne : Q.Nonempty) {n K p : ℕ} (hKn : K ≤ n) (hp : p ≠ 0) {ι : Type*} (J : Finset ι)
    (j : ι → Circle × ℂ) {a b : ℝ}
    (ha : ∫⁻ ω, ENNReal.ofReal (Real.exp ((p * ξ) * supQ Q (fun z => phiMN W P 0 K z ω))) ∂P ≤
      ENNReal.ofReal a)
    (hb : ∫⁻ ω, rectLen ξ (fun x => phiMN W P 0 (n - K) x ω) (rectAB 2 1) ^ p ∂P ≤
      ENNReal.ofReal b) :
    ∫⁻ ω, Xdec ξ W P Q n p K J j ω ^ p ∂P ≤
      ENNReal.ofReal a * ENNReal.ofReal (J.card * (((2 : ℝ)⁻¹ ^ K) ^ p * b)) := by
  have hφF := isPhiVersion_phiMN (P := P) hW (Nat.zero_le K)
  have hφG := isPhiVersion_phiMN (P := P) hW hKn
  set F : Ω → ℂ → ℝ := fun ω x => phiMN W P 0 K x ω with hF
  set G : Ω → ℂ → ℝ := fun ω x => phiMN W P K n x ω with hG
  have hFm : Measurable F := measurable_pi_iff.2 fun x => hφF.meas x
  have hGm : Measurable G := measurable_pi_iff.2 fun x => hφG.meas x
  have hGF : IndepFun G F P :=
    indepFun_phi_version hW (a := (2 : ℝ)⁻¹ ^ n) (b := (2 : ℝ)⁻¹ ^ K) (c := (2 : ℝ)⁻¹ ^ 0)
      (by positivity) (inv_two_pow_le hKn) hφG.meas hφF.meas hφG.ae_eq hφF.ae_eq
  have hind : Indep (MeasurableSpace.comap F inferInstance)
      (MeasurableSpace.comap G inferInstance) P := (IndepFun_iff_Indep F G P).1 hGF.symm
  have hA' : Measurable[MeasurableSpace.comap F inferInstance]
      fun ω => ENNReal.ofReal (Real.exp (ξ * supQ Q (F ω))) ^ p :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_comap_supQ hQ hne F hφF.cont).const_mul ξ))).pow_const p
  have hB' : Measurable[MeasurableSpace.comap G inferInstance]
      fun ω => S6P28U.ZqG ξ (G ω) K p J j ^ p :=
    (S6P28U.measurable_comap_ZqG (ξ := ξ) G hφG.cont K p J j).pow_const p
  have hsplit : ∫⁻ ω, Xdec ξ W P Q n p K J j ω ^ p ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (ξ * supQ Q (F ω))) ^ p ∂P) *
        ∫⁻ ω, S6P28U.ZqG ξ (G ω) K p J j ^ p ∂P := by
    simp_rw [Xdec, mul_pow]
    exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      hFm.comap_le hGm.comap_le hind hA' hB'
  rw [hsplit]
  gcongr
  · -- the coarse field
    refine le_trans (le_of_eq ?_) ha
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, mul_assoc]
  · -- the fine crossings: scaling and the moments of `L_{n−K}(R_{2,1})`
    have hZ : ∀ ω, S6P28U.ZqG ξ (G ω) K p J j ^ p =
        ∑ r ∈ J, S6D.len21 ξ (G ω) K (j r) ^ p := fun ω => by
      unfold S6P28U.ZqG
      exact ENNReal.rpow_inv_natCast_pow hp _
    simp_rw [hZ]
    have hmeas : ∀ r ∈ J, Measurable fun ω => S6D.len21 ξ (G ω) K (j r) ^ p := fun r _ =>
      (measurable_crossLenIn ((rectAB 2 1).isCompact_toSet.image (by unfold T20B.mot; fun_prop))
        hφG.cont hφG.meas).pow_const _
    rw [lintegral_finsetSum _ hmeas]
    have hφ' : phiVer W P ((2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ n) 1 = phiMN W P 0 (n - K) := by
      rw [phiMN_zero_eq]
      congr 1
      have e : (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ (n - K) * (2 : ℝ)⁻¹ ^ K := by
        rw [← pow_add, Nat.sub_add_cancel hKn]
      rw [e, mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
    have hone : ∀ r ∈ J, ∫⁻ ω, S6D.len21 ξ (G ω) K (j r) ^ p ∂P ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ K) ^ p) * ENNReal.ofReal b := by
      intro r _
      have h := S6P28U.lintegral_len21V_pow (ξ := ξ) hW (δ := (2 : ℝ)⁻¹ ^ n) (K := K)
        (by positivity) (inv_two_pow_le hKn) (j r) p
      rw [hφ'] at h
      rw [show (fun ω => S6D.len21 ξ (G ω) K (j r) ^ p) = fun ω =>
        S6D.len21 ξ (fun x => phiVer W P ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ K) x ω) K (j r) ^ p from rfl,
        h]
      gcongr
    calc ∑ r ∈ J, ∫⁻ ω, S6D.len21 ξ (G ω) K (j r) ^ p ∂P
        ≤ ∑ _r ∈ J, ENNReal.ofReal (((2 : ℝ)⁻¹ ^ K) ^ p) * ENNReal.ofReal b :=
          Finset.sum_le_sum hone
      _ = ENNReal.ofReal (J.card * (((2 : ℝ)⁻¹ ^ K) ^ p * b)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity)]

/-- **U10 in the form used here**: from `E (L_m(R_{2,1})/λ_m)^p ≤ C`,
`E L_m(R_{2,1})^p ≤ max C 0 · λ_m^p`. -/
lemma lintegral_rectLen_pow_le (hW : IsWhiteNoise P W) {m p : ℕ} {C : ℝ}
    (hlam : 0 < lambdaN ξ W P m)
    (hC : ∫⁻ ω, ENNReal.ofReal ((lenObs ξ (phiMN W P 0 m) (rectAB 2 1) ω /
      lambdaN ξ W P m) ^ (p : ℝ)) ∂P ≤ ENNReal.ofReal C) :
    ∫⁻ ω, rectLen ξ (fun x => phiMN W P 0 m x ω) (rectAB 2 1) ^ p ∂P ≤
      ENNReal.ofReal (max C 0 * lambdaN ξ W P m ^ p) := by
  have hφ := isPhiVersion_phiMN (P := P) hW (Nat.zero_le m)
  set lam := lambdaN ξ W P m
  have hpt : ∀ ω, rectLen ξ (fun x => phiMN W P 0 m x ω) (rectAB 2 1) ^ p =
      ENNReal.ofReal ((lenObs ξ (phiMN W P 0 m) (rectAB 2 1) ω / lam) ^ (p : ℝ)) *
        ENNReal.ofReal (lam ^ p) := by
    intro ω
    have hL0 : 0 ≤ lenObs ξ (phiMN W P 0 m) (rectAB 2 1) ω := ENNReal.toReal_nonneg
    rw [← ofReal_lenObs hφ.cont (rectAB 2 1) (by simp [rectAB]) (by simp [rectAB]) ω,
      ← ENNReal.ofReal_pow hL0, ← ENNReal.ofReal_mul (by positivity), Real.rpow_natCast,
      div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hlam.ne')]
  simp_rw [hpt]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc (∫⁻ ω, ENNReal.ofReal ((lenObs ξ (phiMN W P 0 m) (rectAB 2 1) ω / lam) ^ (p : ℝ)) ∂P) *
        ENNReal.ofReal (lam ^ p)
      ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (lam ^ p) :=
        mul_le_mul_left (hC.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) _
    _ = ENNReal.ofReal (max C 0 * lam ^ p) := (ENNReal.ofReal_mul (le_max_right _ _)).symm

end Holder
end Uniform
end GaussianLQG
