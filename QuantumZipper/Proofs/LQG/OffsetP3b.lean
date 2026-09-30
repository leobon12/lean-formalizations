import QuantumZipper.Proofs.LQG.LogSingGoodBasic
import QuantumZipper.Proofs.LQG.AllOffsetsModulus

/-!
# M4-P3(b) with the supremum over all radii (`OffsetP3b`)

Blueprint `M4_BLUEPRINT.md`, node M4-P3(b), strengthened from the dyadic radii `2^{-k}` to all
radii `0 < r ≤ 2^{-n}` (as needed by M4-P4 along the offsets `a 2^{-k}` of `goodFilter`).

Main result `lintegral_annTo_rpow_le`: for `0 < γ < 2`, `p ∈ (0,1]` there is `C` with
`E (sup_{q ∈ ℚ, 0 < q ≤ 2^{-n}} ν_q(Z)([−2^{−n}, 2^{−n}]))^p ≤ C 2^{n(γ²p²/4 − p(1+γ²/4))}`
for all `n ≥ 1`, `Z = zField X 2`.

Proof (own adaptation; no published proof with the supremum over the continuum of radii inside
the fractional moment was found). It combines two arguments of this repository:
* the inner-field decomposition of `FracMom` (M4-P3(a)): on `S = [−δ/2, δ/2]`, `δ = 4·2^{-n}`,
  `ν_r(S) = e^{(γ/2)Ω} δ^{γ²/4} M_r`, where `Ω = Z_δ(0)` is independent of the inner field and
  `M_r` is the rescaled inner mass, now at **every** radius `r` (`bdryR_eq_omega_mul`), through
  the regularized real-centred values `avgR`;
* the grid-plus-chaining argument of `AllOffsets` (M4-B4) for the offsets: for
  `r ∈ [ε, 2ε]`, `ε = 2^{-k-1}`,
  `M_r ≤ M_{2ε} + ∫_S w_{2ε} sup_d chainT_m + Σ_{grid} (M_{cε} − M_{2ε})` (`massR_dpt_le`, and
  Fatou for non-dyadic `r`), with `E` of the chain term `≤ δ C θ^m` (`lintegral_chainM_le`) and
  of each grid term `≤ cInc δ (δ/2ε)^{-β}` (two-radius lemma for the inner field at the radii
  `cε, 2ε`, `integral_abs_massR_step_le`).
With `m = ⌊β j/2⌋`, `j = k − n`, the scale-`k` terms are `≤ δ K ρ^j`; subadditivity of `x^p`,
Jensen, and independence of `Ω` then give the bound exactly as in `FracMom.fracMoment_dyadic`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace OffsetP3b

open BdryExist GaussTK TwoRadius FracMom AllOffsets GoodSample LogSing LogSingGood

/-! ## A. Real-centred regularized values at an arbitrary radius -/

/-- `avgR y r s`: the limit of the raw values `y (fc(d_j, r))` along the dyadic roundings
`d_j → s` (junk `0` if the limit does not exist). At `r = 2^{-k}` this is `avgReg y k s`. -/
def avgR (y : FieldSample) (r s : ℝ) : ℝ :=
  limUnder atTop fun j : ℕ => y (foldedCircle ((dyadicRound j s : ℝ) : ℂ) r)

theorem measurable_avgR (r : ℝ) : Measurable (fun p : FieldSample × ℝ => avgR p.1 r p.2) := by
  have hj : ∀ j : ℕ, Measurable (fun p : FieldSample × ℝ =>
      p.1 (foldedCircle ((dyadicRound j p.2 : ℝ) : ℂ) r)) := by
    intro j
    have hg : Measurable (fun q : FieldSample × ℤ =>
        q.1 (foldedCircle ((((q.2 : ℝ) / (2 : ℝ) ^ j : ℝ)) : ℂ) r)) :=
      measurable_from_prod_countable_left fun z =>
        measurable_pi_apply (foldedCircle ((((z : ℝ) / (2 : ℝ) ^ j : ℝ)) : ℂ) r)
    have hf : Measurable (fun p : FieldSample × ℝ => (p.1, ⌊(2 : ℝ) ^ j * p.2⌋)) :=
      measurable_fst.prodMk (measurable_const.mul measurable_snd).floor
    exact hg.comp hf
  unfold avgR
  exact (StronglyMeasurable.limUnder fun j => (hj j).stronglyMeasurable).measurable

/-- Rescaled inner density `(r/δ)^{γ²/4} e^{(γ/2) avgR y r s}`. -/
def wR (γ δ r : ℝ) (y : FieldSample) (s : ℝ) : ℝ :=
  (r / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * avgR y r s)

/-- Rescaled inner mass of `bI t δ` at radius `r`. -/
def massR (γ t δ r : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  ∫⁻ s in bI t δ, ENNReal.ofReal (wR γ δ r y s)

theorem measurable_wR₂ (γ δ r : ℝ) :
    Measurable (fun p : FieldSample × ℝ => wR γ δ r p.1 p.2) :=
  measurable_const.mul (((measurable_avgR r).const_mul _).exp)

theorem measurable_wR_slice (γ δ r : ℝ) (y : FieldSample) : Measurable (fun s => wR γ δ r y s) :=
  Measurable.comp (g := fun p : FieldSample × ℝ => wR γ δ r p.1 p.2) (f := fun s : ℝ => (y, s))
    (measurable_wR₂ γ δ r) measurable_prodMk_left

theorem measurable_massR (γ t δ r : ℝ) : Measurable (massR γ t δ r) :=
  (ENNReal.measurable_ofReal.comp (measurable_wR₂ γ δ r)).lintegral_prod_right'

theorem wR_nonneg (γ : ℝ) {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (y : FieldSample) (s : ℝ) :
    0 ≤ wR γ δ r y s :=
  mul_nonneg (rpow_nonneg (div_nonneg hr.le hδ.le) _) (exp_pos _).le

theorem massR_radius (γ t δ : ℝ) (k : ℕ) (y : FieldSample) :
    massR γ t δ (radius k) y = massFun γ t δ k y := by
  simp only [massR, massFun, wR, wDens, avgR, avgReg, dyadicRoundC_ofReal]

/-- The band factor `H(a) = (a/2)^{γ²/4} e^{(γ/2)(avgR y (aε) s − avgR y (2ε) s)}`. -/
def HR (γ ε : ℝ) (y : FieldSample) (s a : ℝ) : ℝ :=
  (a / 2) ^ (γ ^ 2 / 4) * exp (γ / 2 * (avgR y (a * ε) s - avgR y (2 * ε) s))

theorem wR_eq_mul_HR (γ : ℝ) {δ ε a : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (ha : 0 < a)
    (y : FieldSample) (s : ℝ) :
    wR γ δ (a * ε) y s = wR γ δ (2 * ε) y s * HR γ ε y s a := by
  have h1 : (a * ε / δ) ^ (γ ^ 2 / 4) = (2 * ε / δ) ^ (γ ^ 2 / 4) * (a / 2) ^ (γ ^ 2 / 4) := by
    rw [← mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
  rw [wR, wR, HR, h1]
  have h2 : exp (γ / 2 * avgR y (a * ε) s) = exp (γ / 2 * avgR y (2 * ε) s) *
      exp (γ / 2 * (avgR y (a * ε) s - avgR y (2 * ε) s)) := by
    rw [← exp_add]; congr 1; ring
  rw [h2]; ring

theorem measurable_HR (γ ε a : ℝ) :
    Measurable (fun p : FieldSample × ℝ => HR γ ε p.1 p.2 a) :=
  measurable_const.mul ((((measurable_avgR _).sub (measurable_avgR _)).const_mul _).exp)

theorem measurable_chainT_HR (γ ε : ℝ) (m n : ℕ) :
    Measurable (fun p : FieldSample × ℝ => chainT m n (HR γ ε p.1 p.2)) := by
  unfold chainT incr
  exact Finset.measurable_sum _ fun j _ => measurable_const.add
    ((Finset.measurable_sum _ fun l _ =>
      ((measurable_HR _ _ _).sub (measurable_HR _ _ _)).pow_const 4).div_const _)

/-- The chain term `∫_S w_{2ε} sup_d chainT m (m+d) H`. -/
def chainM (γ t δ ε : ℝ) (m : ℕ) (y : FieldSample) : ℝ≥0∞ :=
  ∫⁻ s in bI t δ, ENNReal.ofReal (wR γ δ (2 * ε) y s) *
    ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (HR γ ε y s))

/-- The grid term `Σ_{l ≤ 2^m} (M_{(1 + l 2^{-m})ε} − M_{2ε})`. -/
def gridM (γ t δ ε : ℝ) (m : ℕ) (y : FieldSample) : ℝ≥0∞ :=
  ∑ l ∈ Finset.range (2 ^ m + 1), (massR γ t δ (dpt m l * ε) y - massR γ t δ (2 * ε) y)

theorem measurable_chainM (γ t δ ε : ℝ) (m : ℕ) : Measurable (chainM γ t δ ε m) :=
  ((ENNReal.measurable_ofReal.comp (measurable_wR₂ γ δ _)).mul
    (Measurable.iSup fun d => ENNReal.measurable_ofReal.comp
      (measurable_chainT_HR γ ε m (m + d)))).lintegral_prod_right'

theorem measurable_gridM (γ t δ ε : ℝ) (m : ℕ) : Measurable (gridM γ t δ ε m) :=
  Finset.measurable_sum _ fun _ _ => (measurable_massR _ _ _ _).sub (measurable_massR _ _ _ _)

/-- **Deterministic chaining** at a dyadic offset: `M_{aε} ≤ M_{2ε} + chain + grid`. -/
theorem massR_dpt_le (γ t : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (m d : ℕ) {i : ℕ}
    (hi : i ≤ 2 ^ (m + d)) (y : FieldSample) :
    massR γ t δ (dpt (m + d) i * ε) y ≤
      massR γ t δ (2 * ε) y + chainM γ t δ ε m y + gridM γ t δ ε m y := by
  have ha : 0 < dpt (m + d) i := by linarith [dpt_ge_one (m + d) i]
  have hb : 0 < dpt m (i / 2 ^ d) := by linarith [dpt_ge_one m (i / 2 ^ d)]
  have hil : i / 2 ^ d ≤ 2 ^ m :=
    Nat.div_le_of_le_mul (by rw [pow_add] at hi; rw [mul_comm]; exact hi)
  have hsl : ∀ r, Measurable (fun s => ENNReal.ofReal (wR γ δ r y s)) := fun r =>
    (measurable_wR_slice γ δ r y).ennreal_ofReal
  have h1 : massR γ t δ (dpt (m + d) i * ε) y ≤
      massR γ t δ (dpt m (i / 2 ^ d) * ε) y + chainM γ t δ ε m y := by
    unfold massR chainM
    rw [← lintegral_add_left (hsl _)]
    refine lintegral_mono fun s => ?_
    set H := HR γ ε y s with hH
    have hc : |H (dpt (m + d) i) - H (dpt m (i / 2 ^ d))| ≤ chainT m (m + d) H :=
      chain_bound H m d i hi
    have hw0 := wR_nonneg γ hδ (by positivity : (0 : ℝ) < 2 * ε) y s
    have hpt : wR γ δ (dpt (m + d) i * ε) y s ≤
        wR γ δ (dpt m (i / 2 ^ d) * ε) y s + wR γ δ (2 * ε) y s * chainT m (m + d) H := by
      rw [wR_eq_mul_HR γ hδ hε ha, wR_eq_mul_HR γ hδ hε hb, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hw0
      have := (le_abs_self _).trans hc
      linarith
    calc ENNReal.ofReal (wR γ δ (dpt (m + d) i * ε) y s)
        ≤ ENNReal.ofReal (wR γ δ (dpt m (i / 2 ^ d) * ε) y s) +
            ENNReal.ofReal (wR γ δ (2 * ε) y s * chainT m (m + d) H) :=
          (ENNReal.ofReal_le_ofReal hpt).trans ENNReal.ofReal_add_le
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [ENNReal.ofReal_mul hw0]
          exact mul_le_mul' le_rfl (le_iSup (fun d' => ENNReal.ofReal (chainT m (m + d') H)) d)
  have h2 : massR γ t δ (dpt m (i / 2 ^ d) * ε) y ≤
      massR γ t δ (2 * ε) y + gridM γ t δ ε m y := by
    refine le_add_tsub.trans (add_le_add le_rfl ?_)
    exact Finset.single_le_sum
      (f := fun l => massR γ t δ (dpt m l * ε) y - massR γ t δ (2 * ε) y)
      (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
  calc massR γ t δ (dpt (m + d) i * ε) y
      ≤ massR γ t δ (dpt m (i / 2 ^ d) * ε) y + chainM γ t δ ε m y := h1
    _ ≤ massR γ t δ (2 * ε) y + gridM γ t δ ε m y + chainM γ t δ ε m y := add_le_add h2 le_rfl
    _ = _ := by ring

/-- Fatou in the radius, for a regular sample. -/
theorem bdryR_le_iSup_of_tendsto {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (γ : ℝ) {S : Set ℝ} (hS : MeasurableSet S) {r : ℝ} (hr : 0 < r) {q : ℕ → ℝ}
    (hq : ∀ j, 0 < q j) (hqt : Tendsto q atTop (𝓝 r)) :
    bdryR γ x r S ≤ ⨆ j, bdryR γ x (q j) S := by
  have hdens : ∀ t, Tendsto (fun j => ENNReal.ofReal (bdryDens γ x (q j) t)) atTop
      (𝓝 (ENNReal.ofReal (bdryDens γ x r t))) := by
    intro t
    have ht : ((t : ℂ)) ∈ Hbar := GaussTK.ofReal_mem_Hbar t
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have hFt : Tendsto (fun j => F ((t : ℂ), q j)) atTop (𝓝 (F ((t : ℂ), r))) :=
      (hF.1 ((t : ℂ), r) ⟨ht, hr⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨tendsto_const_nhds.prodMk_nhds hqt, Eventually.of_forall fun j => ⟨ht, hq j⟩⟩)
    have e : ∀ ρ, 0 < ρ → bdryDens γ x ρ t = ρ ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * F ((t : ℂ), ρ)) :=
      fun ρ hρ => by rw [bdryDens, hF.evalReg_fc_of_mem ht hρ]
    rw [e r hr]
    have e' : (fun j => bdryDens γ x (q j) t) =
        fun j => q j ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * F ((t : ℂ), q j)) :=
      funext fun j => e _ (hq j)
    rw [e']
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hr.ne')).tendsto.comp hqt).mul
      ((Real.continuous_exp.tendsto _).comp (hFt.const_mul _))
  calc bdryR γ x r S = ∫⁻ t in S, ENNReal.ofReal (bdryDens γ x r t) := withDensity_apply _ hS
    _ = ∫⁻ t in S, liminf (fun j => ENNReal.ofReal (bdryDens γ x (q j) t)) atTop := by
        congr 1; funext t; exact ((hdens t).liminf_eq).symm
    _ ≤ liminf (fun j => ∫⁻ t in S, ENNReal.ofReal (bdryDens γ x (q j) t)) atTop :=
        lintegral_liminf_le fun j => (continuous_bdryDens γ hF (hq j)).measurable.ennreal_ofReal
    _ ≤ ⨆ j, ∫⁻ t in S, ENNReal.ofReal (bdryDens γ x (q j) t) :=
        le_trans Filter.liminf_le_limsup Filter.limsup_le_iSup
    _ = ⨆ j, bdryR γ x (q j) S := by
        congr 1; funext j; exact (withDensity_apply _ hS).symm

/-! ## B. The inner-field decomposition at an arbitrary radius -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- At radius `ρ`, the raw values at the dyadic real centres equal the regularized ones. -/
def EvR (X : Ω → FieldSample) (ρ : ℝ) (ω : Ω) : Prop :=
  ∀ j : ℕ, ∀ z : ℤ, X ω (foldedCircle ((((z : ℝ) / (2 : ℝ) ^ j : ℝ)) : ℂ) ρ) =
    evalReg (X ω) (foldedCircle ((((z : ℝ) / (2 : ℝ) ^ j : ℝ)) : ℂ) ρ)

theorem ae_evR [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, EvR X ρ ω :=
  ae_all_iff.2 fun _ => ae_all_iff.2 fun _ =>
    (ae_evalReg_fc_eq hX (ofReal_mem_Hbar _) hρ).mono fun _ h => h.symm

theorem tendsto_dyadicRound_real (s : ℝ) :
    Tendsto (fun j : ℕ => dyadicRound j s) atTop (𝓝 s) := by
  have h0 : Tendsto (fun j : ℕ => (1 : ℝ) / 2 ^ j) atTop (𝓝 0) := by
    simp_rw [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun j => by rw [Real.norm_eq_abs]; exact CircleCont.abs_dyadicRound_sub_le j s) h0

/-- On a regular sample with `EvR`, the raw values at the dyadic centres converge to `F(s,ρ)`. -/
theorem tendsto_raw_of_evR {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F) {ρ : ℝ}
    (hρ : 0 < ρ) (hE : EvR X ρ ω) (s : ℝ) :
    Tendsto (fun j : ℕ => X ω (foldedCircle ((dyadicRound j s : ℝ) : ℂ) ρ)) atTop
      (𝓝 (F ((s : ℂ), ρ))) := by
  have e : ∀ j : ℕ, X ω (foldedCircle ((dyadicRound j s : ℝ) : ℂ) ρ) =
      F (((dyadicRound j s : ℝ) : ℂ), ρ) := by
    intro j
    have h := hE j ⌊(2 : ℝ) ^ j * s⌋
    rw [show ((⌊(2 : ℝ) ^ j * s⌋ : ℝ) / (2 : ℝ) ^ j) = dyadicRound j s from rfl] at h
    rw [h, hF.evalReg_fc_of_mem (ofReal_mem_Hbar _) hρ]
  simp_rw [e]
  have hc : Tendsto (fun j : ℕ => ((((dyadicRound j s : ℝ) : ℂ), ρ) : ℂ × ℝ)) atTop
      (𝓝[Hbar ×ˢ Ioi 0] (((s : ℂ), ρ))) :=
    tendsto_nhdsWithin_iff.2 ⟨((Complex.continuous_ofReal.tendsto s).comp
      (tendsto_dyadicRound_real s)).prodMk_nhds tendsto_const_nhds,
      Eventually.of_forall fun j => ⟨ofReal_mem_Hbar _, hρ⟩⟩
  exact (hF.1 ((s : ℂ), ρ) ⟨ofReal_mem_Hbar s, hρ⟩).tendsto.comp hc

/-- The inner sample at radius `ρ`: `avgR (innerSample) ρ s = F(s,ρ) − X(fc(t,δ))`. -/
theorem avgR_innerSample_eq {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F) {ρ : ℝ}
    (hρ : 0 < ρ) (hE : EvR X ρ ω) {t δ s : ℝ} (hδ : 0 < δ) (hs : |s - t| + ρ < δ) :
    avgR (innerSample X t δ ω) ρ s = F ((s : ℂ), ρ) - X ω (foldedCircle (t : ℂ) δ) := by
  have hε : 0 < δ - |s - t| - ρ := by linarith
  have hev : ∀ᶠ j : ℕ in atTop, |dyadicRound j s - s| < δ - |s - t| - ρ := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_dyadicRound_real s)).eventually
      (gt_mem_nhds hε)
    exact h.mono fun j hj => by rwa [Real.norm_eq_abs] at hj
  have heq : ∀ᶠ j : ℕ in atTop,
      X ω (foldedCircle ((dyadicRound j s : ℝ) : ℂ) ρ) - X ω (foldedCircle (t : ℂ) δ) =
        innerSample X t δ ω (foldedCircle ((dyadicRound j s : ℝ) : ℂ) ρ) := by
    filter_upwards [hev] with j hj
    set d := dyadicRound j s with hd
    have hdt : |d - t| ≤ |d - s| + |s - t| := by
      have := abs_add_le (d - s) (s - t); rwa [sub_add_sub_cancel] at this
    have hq : 0 < ρ / δ ∧ |(d - t) / δ| + ρ / δ ≤ 1 := by
      refine ⟨div_pos hρ hδ, ?_⟩
      rw [abs_div, abs_of_pos hδ, ← add_div, div_le_one hδ]
      linarith
    let q : InnerQ := ⟨((d - t) / δ, ρ / δ), hq⟩
    have hm : innerMeas t δ q = foldedCircle ((d : ℝ) : ℂ) ρ := by
      simp only [innerMeas, q]
      congr 1
      · congr 1; field_simp; ring
      · field_simp
    rw [← hm, innerSample_apply]
  exact ((tendsto_raw_of_evR hF hρ hE s).sub_const _).congr' heq |>.limUnder_eq

/-- `ν_ρ(Z)(bI t δ) = e^{(γ/2)Ω} δ^{γ²/4} M_ρ(inner)`, on the event. -/
theorem bdryR_eq_omega_mul {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F) (γ R : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hE : EvR X ρ ω) {t δ : ℝ} (hδ : 0 < δ) (hρδ : 2 * ρ < δ) :
    bdryR γ (zField X R ω) ρ (bI t δ) =
      ENNReal.ofReal (exp (γ / 2 * omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 4)) *
        massR γ t δ ρ (innerSample X t δ ω) := by
  have hm : Measurable (fun s => ENNReal.ofReal (wR γ δ ρ (innerSample X t δ ω) s)) :=
    (measurable_wR_slice γ δ ρ _).ennreal_ofReal
  rw [bdryR, withDensity_apply _ (measurableSet_bI t δ), massR, ← lintegral_const_mul _ hm]
  refine setLIntegral_congr_fun (measurableSet_bI t δ) fun s hs => ?_
  have hst : |s - t| + ρ < δ := by
    have : |s - t| ≤ δ / 2 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
    linarith
  have hδa : 0 < δ ^ (γ ^ 2 / 4) := rpow_pos_of_pos hδ _
  rw [bdryDens_zField, zV_eq_of_regular hF s hρ, wR, avgR_innerSample_eq hF hρ hE hδ hst,
    ← ENNReal.ofReal_mul (mul_pos (exp_pos _) hδa).le]
  congr 1
  simp only [omegaAvg, fcPairVal]
  rw [div_rpow hρ.le hδ.le]
  have e : exp (γ / 2 * (F ((s : ℂ), ρ) - X ω (foldedCircle 0 R))) =
      exp (γ / 2 * (X ω (foldedCircle (t : ℂ) δ) - X ω (foldedCircle 0 R))) *
        exp (γ / 2 * (F ((s : ℂ), ρ) - X ω (foldedCircle (t : ℂ) δ))) := by
    rw [← exp_add]; congr 1; ring
  rw [e]
  field_simp

/-- At a fixed point, `avgR (innerSample) ρ s` is a.s. the raw pair value. -/
theorem avgR_inner_ae_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {ρ t δ s : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hs : |s - t| + ρ < δ) :
    (fun ω => avgR (innerSample X t δ ω) ρ s) =ᵐ[P] fcPairVal X ((s : ℂ), ρ, (t : ℂ), δ) := by
  filter_upwards [RegSample.ae_isRegularSample hX, ae_evR hX hρ,
    ae_evalReg_fc_eq hX (ofReal_mem_Hbar s) hρ] with ω hreg hE h1
  obtain ⟨F, hF⟩ := hreg
  rw [avgR_innerSample_eq hF hρ hE hδ hs, ← hF.evalReg_fc_of_mem (ofReal_mem_Hbar s) hρ, h1]
  rfl

theorem measurable_avgR_inner (hX : IsFreeGFFModConstH X P) (t δ ρ : ℝ) :
    Measurable (fun p : ℝ × Ω => avgR (innerSample X t δ p.2) ρ p.1) :=
  Measurable.comp (g := fun p : FieldSample × ℝ => avgR p.1 ρ p.2)
    (f := fun p : ℝ × Ω => (innerSample X t δ p.2, p.1)) (measurable_avgR ρ)
    (((measurable_innerSample hX t δ).comp measurable_snd).prodMk measurable_fst)

theorem measurable_wR_inner (hX : IsFreeGFFModConstH X P) (γ δ r t : ℝ) :
    Measurable (fun q : Ω × ℝ => wR γ δ r (innerSample X t δ q.1) q.2) :=
  Measurable.comp (g := fun p : FieldSample × ℝ => wR γ δ r p.1 p.2)
    (f := fun q : Ω × ℝ => (innerSample X t δ q.1, q.2)) (measurable_wR₂ γ δ r)
    (((measurable_innerSample hX t δ).comp measurable_fst).prodMk measurable_snd)

theorem hasLaw_avgR_inner [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {ρ t δ s : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hs : |s - t| + ρ < δ) :
    HasLaw (fun ω => avgR (innerSample X t δ ω) ρ s)
      (gaussianReal 0 (2 * log δ - 2 * log ρ).toNNReal) P := by
  have := (hasLaw_fcPairVal hX (good_real (s := s) (t := t) hρ hδ)).congr
    (avgR_inner_ae_eq hX hρ hδ hs)
  rwa [fcPairCov_innerU_self hρ hs.le] at this

/-- `E[wR] = 1` exactly. -/
theorem integral_wR_inner [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {ρ t δ s : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hs : |s - t| + ρ < δ) :
    Integrable (fun ω => wR γ δ ρ (innerSample X t δ ω) s) P ∧
    ∫ ω, wR γ δ ρ (innerSample X t δ ω) s ∂P = 1 := by
  have hL := hasLaw_avgR_inner hX hρ hδ hs
  have hρδ : ρ < δ := lt_of_le_of_lt (by linarith [abs_nonneg (s - t)]) hs
  have hi : Integrable (fun ω => exp (0 + γ / 2 * avgR (innerSample X t δ ω) ρ s)) P :=
    hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (γ / 2) 0)
  simp only [zero_add] at hi
  refine ⟨hi.const_mul _, ?_⟩
  have h2 := integral_exp_mul_add_gaussianReal (2 * log δ - 2 * log ρ).toNNReal (γ / 2) 0
  simp only [zero_add] at h2
  have h3 : ∫ ω, exp (γ / 2 * avgR (innerSample X t δ ω) ρ s) ∂P =
      exp ((2 * log δ - 2 * log ρ).toNNReal * (γ / 2) ^ 2 / 2) := by
    rw [← h2]; exact hL.integral_comp (f := fun x => exp (γ / 2 * x)) (by fun_prop)
  simp only [wR]
  rw [integral_const_mul, h3, Real.coe_toNNReal _ (by linarith [log_le_log hρ hρδ.le]),
    rpow_def_of_pos (div_pos hρ hδ), ← exp_add, log_div hρ.ne' hδ.ne']
  rw [← exp_zero]; congr 1; ring

/-- `E M_ρ = δ`. -/
theorem lintegral_massR [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {ρ t δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hρδ : 2 * ρ < δ) :
    ∫⁻ ω, massR γ t δ ρ (innerSample X t δ ω) ∂P = ENNReal.ofReal δ := by
  have hmeas : Measurable (fun q : Ω × ℝ =>
      ENNReal.ofReal (wR γ δ ρ (innerSample X t δ q.1) q.2)) :=
    (measurable_wR_inner hX γ δ ρ t).ennreal_ofReal
  simp only [massR]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  rw [setLIntegral_congr_fun (g := fun _ => 1) (measurableSet_bI t δ) fun s hs => ?_]
  · rw [setLIntegral_const, one_mul, volume_bI hδ.le]
  · have hst : |s - t| + ρ < δ := by
      have : |s - t| ≤ δ / 2 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
      linarith
    obtain ⟨hi, he⟩ := integral_wR_inner hX γ hρ hδ hst (P := P)
    simp only
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun ω => wR_nonneg γ hδ hρ _ s), he, ENNReal.ofReal_one]

theorem integrable_massR_toReal [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {ρ t δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hρδ : 2 * ρ < δ) :
    Integrable (fun ω => (massR γ t δ ρ (innerSample X t δ ω)).toReal) P :=
  integrable_toReal_of_lintegral_ne_top
    ((measurable_massR γ t δ ρ).comp (measurable_innerSample hX t δ)).aemeasurable
    (by rw [lintegral_massR hX γ hρ hδ hρδ]; exact ENNReal.ofReal_ne_top)

theorem ae_massR_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {ρ t δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hρδ : 2 * ρ < δ) :
    ∀ᵐ ω ∂P, massR γ t δ ρ (innerSample X t δ ω) < ⊤ :=
  ae_lt_top ((measurable_massR γ t δ ρ).comp (measurable_innerSample hX t δ))
    (by rw [lintegral_massR hX γ hρ hδ hρδ]; exact ENNReal.ofReal_ne_top)

theorem integrableOn_wR_of_massR_lt_top (γ : ℝ) {t δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    {y : FieldSample} (hy : massR γ t δ ρ y < ⊤) :
    IntegrableOn (fun s => wR γ δ ρ y s) (bI t δ) ∧
      ∫ s in bI t δ, wR γ δ ρ y s = (massR γ t δ ρ y).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict (bI t δ)] fun s => wR γ δ ρ y s :=
    ae_of_all _ fun s => wR_nonneg γ hδ hρ y s
  have hm : Measurable (fun s => wR γ δ ρ y s) := measurable_wR_slice γ δ ρ y
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hy⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
  rfl

/-! ## C. The two-radius lemma for the inner field at the radii `cε`, `2ε` -/

theorem fcPairCov_incr_innerU_same' {s t ρ' ρ δ : ℝ} (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ ρ)
    (h : |s - t| + ρ ≤ δ) :
    fcPairCov ((s : ℂ), ρ', (s : ℂ), ρ) ((s : ℂ), ρ, (t : ℂ), δ) = 0 := by
  have hρ : 0 < ρ := hρ'.trans_le hρ'ρ
  have h2 : |s - t| + ρ' ≤ δ := by linarith
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hρ' hρ, kernelCov_fc_real_nested' hρ' h2,
    kernelCov_fc_real_sameCenter hρ hρ, kernelCov_fc_real_nested' hρ h,
    max_eq_right hρ'ρ, max_self]
  ring

theorem fcPairCov_incr_innerU_far' {s u t ρ' ρ δ : ℝ} (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ ρ)
    (hs : |s - t| + ρ ≤ δ) (hsu : 2 * ρ ≤ |s - u|) :
    fcPairCov ((s : ℂ), ρ', (s : ℂ), ρ) ((u : ℂ), ρ, (t : ℂ), δ) = 0 := by
  have hρ : 0 < ρ := hρ'.trans_le hρ'ρ
  have h2 : |s - t| + ρ' ≤ δ := by linarith
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_separated hρ' hρ (by linarith), kernelCov_fc_real_nested' hρ' h2,
    kernelCov_fc_real_separated hρ hρ (by linarith), kernelCov_fc_real_nested' hρ hs]
  ring

/-- **`TRLHyp` for the inner field** at the radii `2ε` (coarse) and `cε` (fine), `c ∈ [1,2]`. -/
theorem trlHyp_innerR [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {t δ ε c : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) {S : Set ℝ}
    (hS : ∀ s ∈ S, |s - t| + 2 * ε < δ) :
    TRLHyp P S (2 * (2 * ε)) 0 (2 * log 2) (fun _ => log (δ / (2 * ε)))
      (fun _ => (2 * log δ - 2 * log (2 * ε)).toNNReal)
      (fun _ => (2 * log (2 * ε) - 2 * log (c * ε)).toNNReal)
      (fun s ω => avgR (innerSample X t δ ω) (2 * ε) s)
      (fun s ω => avgR (innerSample X t δ ω) (c * ε) s - avgR (innerSample X t δ ω) (2 * ε) s) := by
  have h2ε : 0 < 2 * ε := by positivity
  have hcε : 0 < c * ε := by positivity
  have hcε2 : c * ε ≤ 2 * ε := by nlinarith
  have hS1 : ∀ s ∈ S, |s - t| + c * ε < δ := fun s hs =>
    lt_of_le_of_lt (by linarith) (hS s hs)
  have hUe : ∀ s ∈ S, (fun ω => avgR (innerSample X t δ ω) (2 * ε) s) =ᵐ[P]
      fcPairVal X ((s : ℂ), 2 * ε, (t : ℂ), δ) :=
    fun s hs => avgR_inner_ae_eq hX h2ε hδ (hS s hs)
  have hΔe : ∀ s ∈ S, (fun ω => avgR (innerSample X t δ ω) (c * ε) s -
      avgR (innerSample X t δ ω) (2 * ε) s) =ᵐ[P]
      fcPairVal X ((s : ℂ), c * ε, (s : ℂ), 2 * ε) := by
    intro s hs
    filter_upwards [avgR_inner_ae_eq hX hcε hδ (hS1 s hs) (P := P), hUe s hs] with ω h1 h2
    simp only [h1, h2, fcPairVal]
    ring
  refine
    { measU := measurable_avgR_inner hX t δ _
      measΔ := (measurable_avgR_inner hX t δ _).sub (measurable_avgR_inner hX t δ _)
      measL := measurable_const
      measw := measurable_const
      lawU := fun s hs => hasLaw_avgR_inner hX h2ε hδ (hS s hs)
      lawΔ := ?_, varU := ?_, varΔ := ?_, indep := ?_, decor := ?_ }
  · intro s hs
    have := (hasLaw_fcPairVal hX (good_real (s := s) (t := s) hcε h2ε)).congr (hΔe s hs)
    rwa [fcPairCov_incr_self_gen hcε hcε2] at this
  · intro s hs
    have hrδ : 2 * ε < δ := lt_of_le_of_lt (by linarith [abs_nonneg (s - t)]) (hS s hs)
    show ((2 * log δ - 2 * log (2 * ε)).toNNReal : ℝ) ≤ 2 * log (δ / (2 * ε)) + 0
    rw [Real.coe_toNNReal _ (by linarith [log_le_log h2ε hrδ.le]), log_div hδ.ne' h2ε.ne']
    linarith
  · intro s _
    show ((2 * log (2 * ε) - 2 * log (c * ε)).toNNReal : ℝ) ≤ 2 * log 2
    rw [Real.coe_toNNReal _ (by linarith [log_le_log hcε hcε2]),
      log_mul two_ne_zero hε.ne', log_mul (by linarith) hε.ne']
    linarith [log_nonneg hc1]
  · intro s hs
    have hI := indepFun_fcPair hX
      (fun _ : Unit => (⟨((s : ℂ), c * ε, (s : ℂ), 2 * ε), good_real hcε h2ε⟩ :
        {p : FcIdx // p.Good}))
      (fun _ : Unit => (⟨((s : ℂ), 2 * ε, (t : ℂ), δ), good_real h2ε hδ⟩ :
        {p : FcIdx // p.Good}))
      (fun _ _ => fcPairCov_incr_innerU_same' hcε hcε2 (hS s hs).le)
    have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
    exact hI2.congr (hΔe s hs).symm (hUe s hs).symm
  · intro s hs u hu hsu
    have hg : ∀ i : Fin 3, FcIdx.Good
        (![((s : ℂ), 2 * ε, (t : ℂ), δ), ((u : ℂ), 2 * ε, (t : ℂ), δ),
          ((u : ℂ), c * ε, (u : ℂ), 2 * ε)] i) := by
      intro i; fin_cases i
      · exact good_real h2ε hδ
      · exact good_real h2ε hδ
      · exact good_real hcε h2ε
    have hI := indepFun_fcPair hX
      (fun _ : Unit => (⟨((s : ℂ), c * ε, (s : ℂ), 2 * ε), good_real hcε h2ε⟩ :
        {p : FcIdx // p.Good}))
      (fun i : Fin 3 => (⟨_, hg i⟩ : {p : FcIdx // p.Good})) (by
        intro _ i
        fin_cases i
        · exact fcPairCov_incr_innerU_same' hcε hcε2 (hS s hs).le
        · exact fcPairCov_incr_innerU_far' hcε hcε2 (hS s hs).le (by linarith)
        · exact fcPairCov_incr_incr_far hcε hcε2 hcε hcε2 (by linarith))
    have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
      (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
    have hI2 := hI.comp (measurable_pi_apply ()) hφ
    refine hI2.congr (hΔe s hs).symm ?_
    filter_upwards [hUe s hs, hUe u hu, hΔe u hu] with ω h1 h2 h3
    simp [h1, h2, ← h3]

/-- **Grid increment bound** (two-radius lemma for the inner field):
`E|M_{2ε} − M_{cε}| ≤ cInc · δ · (δ/2ε)^{-β}`, `β = bdryRate γ`, `c ∈ [1,2]`. -/
theorem integral_abs_massR_step_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {t δ ε c : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hc1 : 1 ≤ c)
    (hc2 : c ≤ 2) (hk : 2 * (2 * ε) < δ) :
    ∫ ω, |(massR γ t δ (2 * ε) (innerSample X t δ ω)).toReal -
        (massR γ t δ (c * ε) (innerSample X t δ ω)).toReal| ∂P ≤
      cInc γ * δ * exp (-bdryRate γ * log (δ / (2 * ε))) := by
  have h2ε : 0 < 2 * ε := by positivity
  have hcε : 0 < c * ε := by positivity
  have hcε2 : c * ε ≤ 2 * ε := by nlinarith
  have hrδ : 2 * ε < δ := by linarith
  have hk' : 2 * (c * ε) < δ := by linarith
  have hlog2 : (0 : ℝ) ≤ 2 * log 2 := mul_nonneg zero_le_two (log_nonneg one_le_two)
  have hw0 : 0 ≤ 2 * log (2 * ε) - 2 * log (c * ε) := by linarith [log_le_log hcε hcε2]
  set L := log (δ / (2 * ε)) with hL
  have hL0 : 0 ≤ L := log_nonneg (by rw [le_div_iff₀ h2ε]; linarith)
  have hS : ∀ s ∈ bI t δ, |s - t| + 2 * ε < δ := fun s hs => by
    have : |s - t| ≤ δ / 2 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
    linarith
  have h := trlHyp_innerR hX (P := P) hδ hε hc1 hc2 (S := bI t δ) hS
  have hb := trl_bound hγ hγ2 (f := fun _ => 1) (M := 1) (Lmin := L) (Lmax := L)
    (by positivity) (measurableSet_bI t δ) (by rw [volume_bI hδ.le]; exact ENNReal.ofReal_lt_top)
    measurable_const (fun _ => by simp) h (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have hpt : ∀ s ω, trlD γ (fun _ => (1 : ℝ)) (fun _ => L)
      (fun _ => (2 * log (2 * ε) - 2 * log (c * ε)).toNNReal)
      (fun s ω => avgR (innerSample X t δ ω) (2 * ε) s)
      (fun s ω => avgR (innerSample X t δ ω) (c * ε) s - avgR (innerSample X t δ ω) (2 * ε) s)
      s ω = wR γ δ (2 * ε) (innerSample X t δ ω) s - wR γ δ (c * ε) (innerSample X t δ ω) s := by
    intro s ω
    simp only [trlD, tiltY, wR, one_mul]
    rw [Real.coe_toNNReal _ hw0, rpow_def_of_pos (div_pos h2ε hδ),
      rpow_def_of_pos (div_pos hcε hδ), log_div h2ε.ne' hδ.ne', log_div hcε.ne' hδ.ne', hL,
      log_div hδ.ne' h2ε.ne', mul_sub, mul_one, ← exp_add, ← exp_add, ← exp_add]
    congr 1 <;> congr 1 <;> ring
  have hae : ∀ᵐ ω ∂P, ∫ s in bI t δ, trlD γ (fun _ => (1 : ℝ)) (fun _ => L)
      (fun _ => (2 * log (2 * ε) - 2 * log (c * ε)).toNNReal)
      (fun s ω => avgR (innerSample X t δ ω) (2 * ε) s)
      (fun s ω => avgR (innerSample X t δ ω) (c * ε) s - avgR (innerSample X t δ ω) (2 * ε) s)
      s ω = (massR γ t δ (2 * ε) (innerSample X t δ ω)).toReal -
        (massR γ t δ (c * ε) (innerSample X t δ ω)).toReal := by
    filter_upwards [ae_massR_lt_top hX γ h2ε hδ hk (P := P) (t := t),
      ae_massR_lt_top hX γ hcε hδ hk' (P := P) (t := t)] with ω h1 h2
    obtain ⟨i1, e1⟩ := integrableOn_wR_of_massR_lt_top γ hδ h2ε h1
    obtain ⟨i2, e2⟩ := integrableOn_wR_of_massR_lt_top γ hδ hcε h2
    simp_rw [hpt]
    rw [integral_sub i1 i2, e1, e2]
  have hEq : (fun ω => |(massR γ t δ (2 * ε) (innerSample X t δ ω)).toReal -
        (massR γ t δ (c * ε) (innerSample X t δ ω)).toReal|)
      =ᵐ[P] fun ω => |∫ s in bI t δ, trlD γ (fun _ => (1 : ℝ)) (fun _ => L)
        (fun _ => (2 * log (2 * ε) - 2 * log (c * ε)).toNNReal)
        (fun s ω => avgR (innerSample X t δ ω) (2 * ε) s)
        (fun s ω => avgR (innerSample X t δ ω) (c * ε) s - avgR (innerSample X t δ ω) (2 * ε) s)
        s ω| :=
    hae.mono fun ω hω => by dsimp only; rw [hω]
  refine (le_of_eq (integral_congr_ae hEq)).trans (hb.trans ?_)
  set β := bdryRate γ with hβ
  set θ := max 0 ((3 * γ - 2) / 4) with hθ
  set E := 1 + exp (γ ^ 2 / 4 * (2 * log 2)) with hE
  have hβ1 : β ≤ (1 - γ ^ 2 / 2 + θ ^ 2) / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 16 := min_le_right _ _
  have hvol : volume.real (bI t δ) = δ := by
    rw [measureReal_def, volume_bI hδ.le, ENNReal.toReal_ofReal hδ.le]
  have hrad : 2 * ε = δ * exp (-L) := by
    rw [exp_neg, hL, exp_log (div_pos hδ h2ε)]; field_simp
  rw [hvol, hrad]
  have hE0 : 0 ≤ E := by positivity
  have hin : (1 : ℝ) ^ 2 * (E * (exp ((γ - θ) ^ 2 * 0 / 2) * exp ((γ ^ 2 / 2 - θ ^ 2) * L))) *
      (2 * (2 * (δ * exp (-L))) * δ) ≤ (2 * √E * δ * exp (-β * L)) ^ 2 := by
    have e1 : exp ((γ ^ 2 / 2 - θ ^ 2) * L) * exp (-L) ≤ exp (-β * L) ^ 2 := by
      rw [← exp_add, ← exp_nat_mul]; apply exp_le_exp.2; push_cast; nlinarith
    have hsq : √E ^ 2 = E := sq_sqrt hE0
    calc (1 : ℝ) ^ 2 * (E * (exp ((γ - θ) ^ 2 * 0 / 2) * exp ((γ ^ 2 / 2 - θ ^ 2) * L))) *
          (2 * (2 * (δ * exp (-L))) * δ)
        = 4 * E * δ ^ 2 * (exp ((γ ^ 2 / 2 - θ ^ 2) * L) * exp (-L)) := by
          simp only [mul_zero, zero_div, exp_zero]; ring
      _ ≤ 4 * E * δ ^ 2 * exp (-β * L) ^ 2 :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = (2 * √E * δ * exp (-β * L)) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, hsq]; ring
  have ht1 := Real.sqrt_le_sqrt hin
  rw [Real.sqrt_sq (by positivity)] at ht1
  have ht2 : (1 : ℝ) * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * 0 / 2) *
      exp (-((2 - γ) ^ 2 / 16) * L))) * δ ≤ 2 * δ * exp (-β * L) := by
    have : exp (-((2 - γ) ^ 2 / 16) * L) ≤ exp (-β * L) := exp_le_exp.2 (by nlinarith)
    simp only [mul_zero, zero_div, exp_zero, one_mul]
    nlinarith [exp_pos (-((2 - γ) ^ 2 / 16) * L)]
  calc _ ≤ 2 * √E * δ * exp (-β * L) + 2 * δ * exp (-β * L) := add_le_add ht1 ht2
    _ = cInc γ * δ * exp (-β * L) := by rw [cInc, ← hE]; ring

/-- The tsub form: `E (M_{cε} − M_{2ε}) ≤ cInc · δ · (δ/2ε)^{-β}`. -/
theorem lintegral_massR_tsub_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {t δ ε c : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hc1 : 1 ≤ c)
    (hc2 : c ≤ 2) (hk : 2 * (2 * ε) < δ) :
    ∫⁻ ω, (massR γ t δ (c * ε) (innerSample X t δ ω) -
        massR γ t δ (2 * ε) (innerSample X t δ ω)) ∂P ≤
      ENNReal.ofReal (cInc γ * δ * exp (-bdryRate γ * log (δ / (2 * ε)))) := by
  have h2ε : 0 < 2 * ε := by positivity
  have hcε : 0 < c * ε := by positivity
  have hk' : 2 * (c * ε) < δ := by nlinarith
  have hint : Integrable (fun ω => |(massR γ t δ (2 * ε) (innerSample X t δ ω)).toReal -
      (massR γ t δ (c * ε) (innerSample X t δ ω)).toReal|) P :=
    ((integrable_massR_toReal hX γ h2ε hδ hk).sub (integrable_massR_toReal hX γ hcε hδ hk')).abs
  have hpt : ∀ᵐ ω ∂P, massR γ t δ (c * ε) (innerSample X t δ ω) -
      massR γ t δ (2 * ε) (innerSample X t δ ω) ≤
      ENNReal.ofReal |(massR γ t δ (2 * ε) (innerSample X t δ ω)).toReal -
        (massR γ t δ (c * ε) (innerSample X t δ ω)).toReal| := by
    filter_upwards [ae_massR_lt_top hX γ h2ε hδ hk (P := P) (t := t),
      ae_massR_lt_top hX γ hcε hδ hk' (P := P) (t := t)] with ω h1 h2
    rw [← ENNReal.ofReal_toReal h1.ne, ← ENNReal.ofReal_toReal h2.ne,
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg, abs_sub_comm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine (lintegral_mono_ae hpt).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (integral_abs_massR_step_le hX hγ hγ2 hδ hε hc1 hc2 hk)

/-! ## D. The chain term -/

theorem indepFun_band_inner (hX : IsFreeGFFModConstH X P) {s t ε δ : ℝ} (hε : 0 < ε)
    (hs : |s - t| + 2 * ε ≤ δ) :
    IndepFun (fun ω (a : Icc (1 : ℝ) 2) => fcPairVal X ((s : ℂ), a.1 * ε, (s : ℂ), 2 * ε) ω)
      (fun ω (_ : Unit) => fcPairVal X ((s : ℂ), 2 * ε, (t : ℂ), δ) ω) P := by
  have hδ : 0 < δ := by linarith [abs_nonneg (s - t)]
  refine indepFun_fcPair hX
    (fun a => ⟨_, good_real (mul_pos (by linarith [a.2.1]) hε) (by positivity : (0 : ℝ) < 2 * ε)⟩)
    (fun _ => ⟨_, good_real (by positivity : (0 : ℝ) < 2 * ε) hδ⟩) ?_
  intro a _
  exact fcPairCov_incr_innerU_same' (mul_pos (by linarith [a.2.1]) hε)
    (mul_le_mul_of_nonneg_right a.2.2 hε.le) hs

theorem chainT_mono (m : ℕ) (h : ℝ → ℝ) : Monotone (fun d : ℕ => chainT m (m + d) h) := by
  refine monotone_nat_of_le_succ fun d => ?_
  show chainT m (m + d) h ≤ chainT m (m + d + 1) h
  rw [chainT, chainT, Finset.sum_Ico_succ_top (by omega)]
  have : 0 ≤ θm ^ (m + d) + incr (m + d) h / θm ^ (3 * (m + d)) :=
    add_nonneg (pow_pos θm_pos _).le (div_nonneg (incr_nonneg _ h) (pow_pos θm_pos _).le)
  linarith

theorem measurable_chainT_band (hX : IsFreeGFFModConstH X P) (γ s ε : ℝ) (m n : ℕ) :
    Measurable (fun ω => chainT m n (fun a => bandH γ X s ε a ω)) := by
  have hH : ∀ a, Measurable (fun ω => bandH γ X s ε a ω) := fun a =>
    measurable_const.mul (((measurable_fcPairVal hX _).const_mul _).exp)
  unfold chainT incr
  exact Finset.measurable_sum _ fun j _ => measurable_const.add
    ((Finset.measurable_sum _ fun l _ => ((hH _).sub (hH _)).pow_const 4).div_const _)

/-- `E[w_{2ε}(s) · sup_d chainT m (m+d) H_s] ≤ C θ^m` at a fixed point `s`. -/
theorem lintegral_chain_pt [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {t δ ε s : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hs : |s - t| + 2 * ε < δ) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (wR γ δ (2 * ε) (innerSample X t δ ω) s) *
        ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (HR γ ε (innerSample X t δ ω) s)) ∂P ≤
      ENNReal.ofReal ((8 + 4 * (2544 * exp 16)) * θm ^ m) := by
  have h2ε : 0 < 2 * ε := by positivity
  set V : Ω → ℝ := fcPairVal X ((s : ℂ), 2 * ε, (t : ℂ), δ) with hV
  have hpts : ∀ᵐ ω ∂P, ∀ j l : ℕ, l ≤ 2 ^ j →
      avgR (innerSample X t δ ω) (dpt j l * ε) s =
        fcPairVal X ((s : ℂ), dpt j l * ε, (t : ℂ), δ) ω := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun l => ?_
    by_cases hl : l ≤ 2 ^ j
    · have ha1 := dpt_ge_one j l
      have ha2 := dpt_le_two hl
      have hlt : |s - t| + dpt j l * ε < δ := by nlinarith
      filter_upwards [avgR_inner_ae_eq hX (mul_pos (by linarith) hε) hδ hlt (P := P)] with ω h
      exact fun _ => h
    · exact ae_of_all _ fun ω h => absurd h hl
  have hae2 := avgR_inner_ae_eq hX h2ε hδ hs (P := P)
  set G : Ω → ℝ≥0∞ := fun ω =>
    ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (fun a => bandH γ X s ε a ω)) with hG
  set E0 : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal ((2 * ε / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * V ω)) with hE0
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (wR γ δ (2 * ε) (innerSample X t δ ω) s) *
      ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (HR γ ε (innerSample X t δ ω) s)) =
      (E0 * G) ω := by
    filter_upwards [hpts, hae2] with ω h1 h2
    simp only [Pi.mul_apply, hE0, hG, wR, h2]
    congr 1
    refine iSup_congr fun d => congrArg ENNReal.ofReal (chainT_congr m (m + d) fun j l hl => ?_)
    simp only [HR, bandH, bandΦ, h1 j l hl, h2, hV, fcPairVal]
    congr 2
    ring
  refine (lintegral_congr_ae hae).trans_le ?_
  -- independence
  have hI0 := indepFun_band_inner hX (P := P) (t := t) (δ := δ) hε hs.le
  let hfun : (Icc (1 : ℝ) 2 → ℝ) → ℝ → ℝ := fun φ a =>
    if h : a ∈ Icc (1 : ℝ) 2 then (a / 2) ^ (γ ^ 2 / 4) * exp (γ / 2 * φ ⟨a, h⟩) else 0
  have hmeas_pt : ∀ a : ℝ, Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ => hfun φ a) := by
    intro a
    by_cases ha : a ∈ Icc (1 : ℝ) 2
    · simp only [hfun, dif_pos ha]
      exact measurable_const.mul (((measurable_pi_apply _).const_mul _).exp)
    · simp only [hfun, dif_neg ha]; exact measurable_const
  have hmG : Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ =>
      ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (hfun φ))) := by
    refine Measurable.iSup fun d => ENNReal.measurable_ofReal.comp ?_
    unfold chainT incr
    exact Finset.measurable_sum _ fun j _ => measurable_const.add
      ((Finset.measurable_sum _ fun l _ =>
        ((hmeas_pt _).sub (hmeas_pt _)).pow_const 4).div_const _)
  have hGeq : G = (fun φ => ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (hfun φ))) ∘
      (fun ω (a : Icc (1 : ℝ) 2) => fcPairVal X ((s : ℂ), a.1 * ε, (s : ℂ), 2 * ε) ω) := by
    funext ω
    simp only [Function.comp, hG]
    refine iSup_congr fun d => congrArg ENNReal.ofReal (chainT_congr m (m + d) fun j l hl => ?_)
    have hmem : dpt j l ∈ Icc (1 : ℝ) 2 := ⟨dpt_ge_one j l, dpt_le_two hl⟩
    simp only [hfun, dif_pos hmem, bandH, bandΦ]
  have hmE : Measurable (fun v : Unit → ℝ =>
      ENNReal.ofReal ((2 * ε / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * v ()))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hE0eq : E0 = (fun v : Unit → ℝ =>
      ENNReal.ofReal ((2 * ε / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * v ()))) ∘
      (fun ω (_ : Unit) => V ω) := rfl
  have hI : IndepFun E0 G P := by
    rw [hGeq, hE0eq]
    exact (hI0.comp hmG hmE).symm
  have hGm : Measurable G := Measurable.iSup fun d =>
    (measurable_chainT_band hX γ s ε m (m + d)).ennreal_ofReal
  have hE0m : Measurable E0 := hmE.comp (measurable_pi_iff.2 fun _ => measurable_fcPairVal hX _)
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hE0m hGm hI]
  have hE1 : ∫⁻ ω, E0 ω ∂P = 1 := by
    obtain ⟨hi, he⟩ := integral_wR_inner hX γ h2ε hδ hs (P := P)
    have hcongr : (fun ω => ENNReal.ofReal (wR γ δ (2 * ε) (innerSample X t δ ω) s)) =ᵐ[P] E0 :=
      hae2.mono fun ω h => by simp only [hE0, hV, wR, h]
    rw [← lintegral_congr_ae hcongr, ← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun ω => wR_nonneg γ hδ h2ε _ s), he, ENNReal.ofReal_one]
  have hGb : ∫⁻ ω, G ω ∂P ≤ ENNReal.ofReal ((8 + 4 * (2544 * exp 16)) * θm ^ m) := by
    simp only [hG]
    rw [lintegral_iSup (fun d => (measurable_chainT_band hX γ s ε m (m + d)).ennreal_ofReal)
      (fun d1 d2 h ω => ENNReal.ofReal_le_ofReal (chainT_mono m _ h))]
    refine iSup_le fun d => ?_
    obtain ⟨hiG, hEG⟩ := chainT_band_moment hX hγ hγ2 hε m (m + d) (t := s)
    rw [← ofReal_integral_eq_lintegral_ofReal hiG (ae_of_all _ fun ω => chainT_nonneg _ _ _)]
    exact ENNReal.ofReal_le_ofReal hEG
  rw [hE1, one_mul]
  exact hGb

/-- `E chainM ≤ δ C θ^m`. -/
theorem lintegral_chainM_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {t δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hk : 2 * (2 * ε) < δ)
    (m : ℕ) :
    ∫⁻ ω, chainM γ t δ ε m (innerSample X t δ ω) ∂P ≤
      ENNReal.ofReal (δ * ((8 + 4 * (2544 * exp 16)) * θm ^ m)) := by
  have hmeas : Measurable (fun q : Ω × ℝ =>
      ENNReal.ofReal (wR γ δ (2 * ε) (innerSample X t δ q.1) q.2) *
        ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (HR γ ε (innerSample X t δ q.1) q.2))) :=
    Measurable.comp (g := fun p : FieldSample × ℝ => ENNReal.ofReal (wR γ δ (2 * ε) p.1 p.2) *
        ⨆ d : ℕ, ENNReal.ofReal (chainT m (m + d) (HR γ ε p.1 p.2)))
      (f := fun q : Ω × ℝ => (innerSample X t δ q.1, q.2))
      ((ENNReal.measurable_ofReal.comp (measurable_wR₂ γ δ _)).mul
        (Measurable.iSup fun d => ENNReal.measurable_ofReal.comp
          (measurable_chainT_HR γ ε m (m + d))))
      (((measurable_innerSample hX t δ).comp measurable_fst).prodMk measurable_snd)
  simp only [chainM]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hC0 : 0 ≤ (8 + 4 * (2544 * exp 16)) * θm ^ m := by
    have := θm_pos; positivity
  calc _ ≤ ∫⁻ _ in bI t δ, ENNReal.ofReal ((8 + 4 * (2544 * exp 16)) * θm ^ m) :=
        setLIntegral_mono' (measurableSet_bI t δ) fun s hs => by
          have hst : |s - t| + 2 * ε < δ := by
            have : |s - t| ≤ δ / 2 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
            linarith
          exact lintegral_chain_pt hX hγ hγ2 hδ hε hst m
    _ = _ := by
        rw [setLIntegral_const, volume_bI hδ.le, ← ENNReal.ofReal_mul hC0, mul_comm]

/-! ## E. Assembly -/

/-- Geometric domination of the scale-`j` bound (the estimates of `AllOffsets.summable_bnd`). -/
theorem exists_geom_bound {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {A C : ℝ} (hA : 0 ≤ A)
    (hC : 0 ≤ C) :
    ∃ K ρ : ℝ, 0 ≤ K ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ j : ℕ,
      A * θm ^ (⌊bdryRate γ * j / 2⌋₊) +
        (2 ^ (⌊bdryRate γ * j / 2⌋₊) + 1) * (C * exp (-bdryRate γ * (j * log 2))) ≤
        K * ρ ^ j := by
  set β := bdryRate γ with hβd
  have hβ : 0 < β := bdryRate_pos hγ hγ2
  have hlθ : log θm < 0 := log_neg θm_pos θm_lt_one
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set q₁ := exp (β / 2 * log θm) with hq₁
  set q₂ := exp (-(β / 2) * log 2) with hq₂
  have hq₁1 : q₁ < 1 := exp_lt_one_iff.2 (mul_neg_of_pos_of_neg (by positivity) hlθ)
  have hq₂1 : q₂ < 1 := exp_lt_one_iff.2 (by nlinarith)
  have b1 : ∀ k : ℕ, θm ^ (⌊β * k / 2⌋₊) ≤ θm⁻¹ * q₁ ^ k := by
    intro k
    have hk1 : β * k / 2 - 1 < (⌊β * k / 2⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (β * k / 2); linarith
    have e1 : θm ^ (⌊β * k / 2⌋₊) = exp ((⌊β * k / 2⌋₊ : ℝ) * log θm) := by
      rw [Real.exp_nat_mul, Real.exp_log θm_pos]
    have e2 : θm⁻¹ * q₁ ^ k = exp ((β * k / 2 - 1) * log θm) := by
      rw [hq₁, ← Real.exp_nat_mul, show θm⁻¹ = exp (-log θm) by rw [exp_neg, exp_log θm_pos],
        ← exp_add]
      congr 1; ring
    rw [e1, e2]
    exact exp_le_exp.2 (by nlinarith)
  have b2 : ∀ k : ℕ, (2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2)) ≤ 2 * q₂ ^ k := by
    intro k
    have hk1 : (⌊β * k / 2⌋₊ : ℝ) ≤ β * k / 2 := Nat.floor_le (by positivity)
    have h1 : (1 : ℝ) ≤ 2 ^ (⌊β * k / 2⌋₊) := one_le_pow₀ (by norm_num)
    have e1 : (2 : ℝ) ^ (⌊β * k / 2⌋₊) = exp ((⌊β * k / 2⌋₊ : ℝ) * log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    have h2 : (2 : ℝ) ^ (⌊β * k / 2⌋₊) * exp (-β * (k * log 2)) ≤ q₂ ^ k := by
      rw [e1, ← exp_add, hq₂, ← Real.exp_nat_mul]
      exact exp_le_exp.2 (by nlinarith)
    calc (2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2))
        ≤ (2 * 2 ^ (⌊β * k / 2⌋₊)) * exp (-β * (k * log 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
      _ = 2 * (2 ^ (⌊β * k / 2⌋₊) * exp (-β * (k * log 2))) := by ring
      _ ≤ 2 * q₂ ^ k := mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hθi : 0 ≤ θm⁻¹ := inv_nonneg.2 θm_pos.le
  refine ⟨A * θm⁻¹ + C * 2, max q₁ q₂, by positivity, le_max_of_le_left (exp_pos _).le,
    max_lt hq₁1 hq₂1, fun k => ?_⟩
  have hp1 : q₁ ^ k ≤ max q₁ q₂ ^ k := pow_le_pow_left₀ (exp_pos _).le (le_max_left _ _) k
  have hp2 : q₂ ^ k ≤ max q₁ q₂ ^ k := pow_le_pow_left₀ (exp_pos _).le (le_max_right _ _) k
  calc A * θm ^ (⌊β * k / 2⌋₊) + (2 ^ (⌊β * k / 2⌋₊) + 1) * (C * exp (-β * (k * log 2)))
      = A * θm ^ (⌊β * k / 2⌋₊) + C * ((2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2))) := by
        ring
    _ ≤ A * (θm⁻¹ * q₁ ^ k) + C * (2 * q₂ ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left (b1 k) hA) (mul_le_mul_of_nonneg_left (b2 k) hC)
    _ ≤ A * (θm⁻¹ * max q₁ q₂ ^ k) + C * (2 * max q₁ q₂ ^ k) := by gcongr
    _ = (A * θm⁻¹ + C * 2) * max q₁ q₂ ^ k := by ring

/-- The scale-`(n+j)` term of the bound. -/
def Bj (γ δ : ℝ) (n : ℕ) (mm : ℕ → ℕ) (j : ℕ) (y : FieldSample) : ℝ≥0∞ :=
  chainM γ 0 δ (radius (n + j + 1)) (mm j) y + gridM γ 0 δ (radius (n + j + 1)) (mm j) y

/-- The inner majorant `Ψ = sup_i M_{2^{-(n+i)}} + Σ_j B_j`. -/
def Psi (γ δ : ℝ) (n : ℕ) (mm : ℕ → ℕ) (y : FieldSample) : ℝ≥0∞ :=
  (⨆ i : ℕ, massFun γ 0 δ (n + i) y) + ∑' j, Bj γ δ n mm j y

theorem measurable_Bj (γ δ : ℝ) (n : ℕ) (mm : ℕ → ℕ) (j : ℕ) : Measurable (Bj γ δ n mm j) :=
  (measurable_chainM _ _ _ _ _).add (measurable_gridM _ _ _ _ _)

theorem measurable_Psi (γ δ : ℝ) (n : ℕ) (mm : ℕ → ℕ) : Measurable (Psi γ δ n mm) :=
  (Measurable.iSup fun i => measurable_massFun γ 0 δ (n + i)).add
    (Measurable.ennreal_tsum fun j => measurable_Bj γ δ n mm j)

/-- **Pathwise domination**: a.s. `sup_{q ≤ 2^{-n}} ν_q(annI 0 n) ≤ e^{(γ/2)Ω} δ^{γ²/4} Ψ(inner)`,
`δ = 4·2^{-n}`. -/
theorem ae_annTo_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ R : ℝ) (n : ℕ)
    (mm : ℕ → ℕ) :
    ∀ᵐ ω ∂P, annTo γ (zField X R ω) n ≤
      ENNReal.ofReal (exp (γ / 2 * omegaAvg X R 0 (4 * radius n) ω) *
          (4 * radius n) ^ (γ ^ 2 / 4)) *
        Psi γ (4 * radius n) n mm (innerSample X 0 (4 * radius n) ω) := by
  set δ := 4 * radius n with hδdef
  have hrn := radius_pos n
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hEv : ∀ᵐ ω ∂P, ∀ k j l : ℕ, EvR X (dpt j l * radius (k + 1)) ω :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun j => ae_all_iff.2 fun l =>
      ae_evR hX (mul_pos (by linarith [dpt_ge_one j l]) (radius_pos _))
  filter_upwards [RegSample.ae_isRegularSample hX, hEv] with ω hreg hE1
  obtain ⟨F, hF⟩ := hreg
  have hZ := regular_zField (R := R) hF
  set A := ENNReal.ofReal (exp (γ / 2 * omegaAvg X R 0 δ ω) * δ ^ (γ ^ 2 / 4)) with hA
  set y := innerSample X 0 δ ω with hy
  refine iSup₂_le fun q hq => ?_
  obtain ⟨hq0, hqn⟩ := hq
  classical
  have hex : ∃ j : ℕ, radius (n + j + 1) < q := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hq0 (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨j, lt_of_le_of_lt (AreaExist.aradius_anti (by omega)) hj⟩
  set j := Nat.find hex with hjdef
  have hj1 : radius (n + j + 1) < q := Nat.find_spec hex
  have hj2 : (q : ℝ) ≤ radius (n + j) := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, add_zero]; exact hqn
    · have := Nat.find_min hex (show j - 1 < j by omega)
      push_neg at this
      have e : n + (j - 1) + 1 = n + j := by omega
      rwa [e] at this
  set ε := radius (n + j + 1) with hεdef
  have hε : 0 < ε := radius_pos _
  have h2ε : 2 * ε = radius (n + j) := by rw [hεdef, radius_succ]; ring
  have hnj : radius (n + j) ≤ radius n := AreaExist.aradius_anti (by omega)
  set a := (q : ℝ) / ε with hadef
  have ha1 : 1 < a := by rw [hadef, lt_div_iff₀ hε]; linarith
  have ha2 : a ≤ 2 := by rw [hadef, div_le_iff₀ hε]; linarith
  have haq : a * ε = q := by rw [hadef]; field_simp
  set m := mm j with hm
  set i : ℕ → ℕ := fun d => ⌊(a - 1) * 2 ^ (m + d)⌋₊ with hidef
  have h0 : ∀ d, 0 ≤ (a - 1) * (2 : ℝ) ^ (m + d) := fun d =>
    mul_nonneg (by linarith) (by positivity)
  have hi : ∀ d, i d ≤ 2 ^ (m + d) := by
    intro d
    have h1 : (a - 1) * (2 : ℝ) ^ (m + d) ≤ 2 ^ (m + d) := by
      have : (0 : ℝ) < 2 ^ (m + d) := by positivity
      nlinarith
    have h2 : ((i d : ℕ) : ℝ) ≤ ((2 ^ (m + d) : ℕ) : ℝ) := by
      push_cast; exact (Nat.floor_le (h0 d)).trans h1
    exact Nat.cast_le.mp h2
  have had : ∀ d, |dpt (m + d) (i d) - a| ≤ (1 / 2 : ℝ) ^ d := by
    intro d
    have hN : (0 : ℝ) < 2 ^ (m + d) := by positivity
    have hfl : (i d : ℝ) ≤ (a - 1) * 2 ^ (m + d) := Nat.floor_le (h0 d)
    have hlt : (a - 1) * 2 ^ (m + d) < (i d : ℝ) + 1 := Nat.lt_floor_add_one _
    have key : a - dpt (m + d) (i d) = ((a - 1) * 2 ^ (m + d) - i d) / 2 ^ (m + d) := by
      simp only [dpt]; field_simp; ring
    have hk0 : 0 ≤ a - dpt (m + d) (i d) := by rw [key]; exact div_nonneg (by linarith) hN.le
    have hk1 : a - dpt (m + d) (i d) ≤ 1 / 2 ^ (m + d) := by
      rw [key]; exact div_le_div_of_nonneg_right (by linarith) hN.le
    have hpw : (1 : ℝ) / 2 ^ (m + d) ≤ (1 / 2) ^ d := by
      rw [one_div, ← inv_pow, one_div]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [abs_sub_comm, abs_of_nonneg hk0]
    linarith
  have htend : Tendsto (fun d => dpt (m + d) (i d) * ε) atTop (𝓝 q) := by
    rw [← haq]
    refine Tendsto.mul_const ε ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun d : ℕ => (1 / 2 : ℝ) ^ d) (fun _ => norm_nonneg _)
      (fun d => (Real.norm_eq_abs _).trans_le (had d)) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpos : ∀ d, 0 < dpt (m + d) (i d) * ε := fun d =>
    mul_pos (by linarith [dpt_ge_one (m + d) (i d)]) hε
  have hsub : annI 0 n ⊆ bI 0 δ := by
    unfold annI bI
    exact Icc_subset_Icc (by linarith) (by linarith)
  calc bdryR γ (zField X R ω) q (annI 0 n) ≤ bdryR γ (zField X R ω) q (bI 0 δ) := measure_mono hsub
    _ ≤ ⨆ d, bdryR γ (zField X R ω) (dpt (m + d) (i d) * ε) (bI 0 δ) :=
        bdryR_le_iSup_of_tendsto hZ γ (measurableSet_bI 0 δ) hq0 hpos htend
    _ ≤ A * Psi γ δ n mm y := iSup_le fun d => ?_
  have hd2 : dpt (m + d) (i d) ≤ 2 := dpt_le_two (hi d)
  have hρδ : 2 * (dpt (m + d) (i d) * ε) < δ := by nlinarith
  rw [bdryR_eq_omega_mul hF γ R (hpos d) (hE1 (n + j) (m + d) (i d)) hδ hρδ]
  refine mul_le_mul' le_rfl ?_
  calc massR γ 0 δ (dpt (m + d) (i d) * ε) y
      ≤ massR γ 0 δ (2 * ε) y + chainM γ 0 δ ε m y + gridM γ 0 δ ε m y :=
        massR_dpt_le γ 0 hδ hε m d (hi d) y
    _ = massFun γ 0 δ (n + j) y + Bj γ δ n mm j y := by
        rw [h2ε, massR_radius, add_assoc]; rfl
    _ ≤ Psi γ δ n mm y :=
        add_le_add (le_iSup (fun i => massFun γ 0 δ (n + i) y) j) (ENNReal.le_tsum (f := fun j' => Bj γ δ n mm j' y) j)

/-- **M4-P3(b) with the supremum over all rational radii `0 < q ≤ 2^{-n}`.** -/
theorem lintegral_annTo_rpow_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ω, annTo γ (zField X 2 ω) n ^ p ∂P ≤
        ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) := by
  set β := bdryRate γ with hβ
  have hβ0 : 0 < β := bdryRate_pos hγ hγ2
  set Cθ : ℝ := 8 + 4 * (2544 * exp 16) with hCθ
  have hCθ0 : 0 ≤ Cθ := by positivity
  obtain ⟨K, ρ, hK0, hρ0, hρ1, hKρ⟩ := exists_geom_bound hγ hγ2 hCθ0 (cInc_nonneg γ)
  set mm : ℕ → ℕ := fun j => ⌊β * j / 2⌋₊ with hmm
  set q := exp (-(p * β) * log 2) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, exp_lt_one_iff]
    have := log_pos one_lt_two
    have : 0 < p * β := by positivity
    nlinarith
  have hρp1 : ρ ^ p < 1 := rpow_lt_one hρ0 hρ1 hp0
  have hρp0 : 0 ≤ ρ ^ p := rpow_nonneg hρ0 _
  set K1 := cInc γ ^ p * (1 - q)⁻¹ + K ^ p * (1 - ρ ^ p)⁻¹ with hK1
  have hK10 : 0 ≤ K1 := by
    have h1 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
    have h2 : 0 ≤ (1 - ρ ^ p)⁻¹ := inv_nonneg.2 (by linarith)
    have := rpow_nonneg (cInc_nonneg γ) p
    have := rpow_nonneg hK0 p
    positivity
  refine ⟨4 ^ (p * (1 + γ ^ 2 / 4)) * 2 ^ (p ^ 2 * γ ^ 2 / 4) * (1 + K1), by positivity,
    fun n hn => ?_⟩
  set δ := 4 * radius n with hδdef
  have hr := radius_pos n
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδR : δ ≤ 2 := by
    have h1 := AreaExist.aradius_anti hn
    have : radius 1 = 1 / 2 := by simp [radius]
    linarith
  have hR : |(0 : ℝ)| + δ ≤ 2 := by simpa using hδR
  have hk : 2 * radius n < δ := by linarith
  -- the scale-`j` terms
  have hBj : ∀ j, ∫⁻ ω, Bj γ δ n mm j (innerSample X 0 δ ω) ∂P ≤
      ENNReal.ofReal (δ * (K * ρ ^ j)) := by
    intro j
    set ε := radius (n + j + 1) with hεdef
    have hε : 0 < ε := radius_pos _
    have h2ε : 2 * ε = radius (n + j) := by rw [hεdef, radius_succ]; ring
    have hnj : radius (n + j) ≤ radius n := AreaExist.aradius_anti (by omega)
    have hk2 : 2 * (2 * ε) < δ := by rw [h2ε]; linarith
    have hL : exp (-β * log (δ / (2 * ε))) ≤ exp (-β * (j * log 2)) := by
      apply exp_le_exp.2
      have e : δ / (2 * ε) = 4 * 2 ^ j := by
        rw [h2ε, hδdef]
        simp only [radius, pow_add, inv_pow]
        field_simp
      rw [e, log_mul (by norm_num) (by positivity), log_pow]
      have := log_pos (by norm_num : (1 : ℝ) < 4)
      nlinarith
    have hg : ∫⁻ ω, gridM γ 0 δ ε (mm j) (innerSample X 0 δ ω) ∂P ≤
        ((2 ^ (mm j) + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (cInc γ * δ * exp (-β * log (δ / (2 * ε)))) := by
      simp only [gridM]
      rw [lintegral_finsetSum (s := Finset.range (2 ^ mm j + 1)) (f := fun l ω =>
        massR γ 0 δ (dpt (mm j) l * ε) (innerSample X 0 δ ω) -
          massR γ 0 δ (2 * ε) (innerSample X 0 δ ω)) fun l _ =>
        ((measurable_massR _ _ _ _).comp (measurable_innerSample hX 0 δ)).sub
          ((measurable_massR _ _ _ _).comp (measurable_innerSample hX 0 δ))]
      refine (Finset.sum_le_sum fun l hl => lintegral_massR_tsub_le hX hγ hγ2 hδ hε
        (dpt_ge_one _ _) (dpt_le_two (by have := Finset.mem_range.1 hl; omega)) hk2).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold Bj
    rw [lintegral_add_left (f := fun ω => chainM γ 0 δ ε (mm j) (innerSample X 0 δ ω))
      ((measurable_chainM _ _ _ _ _).comp (measurable_innerSample hX 0 δ))]
    have hN : (((2 ^ (mm j) + 1 : ℕ) : ℝ)) = 2 ^ (mm j) + 1 := by push_cast; ring
    have he0 : 0 ≤ cInc γ * δ * exp (-β * log (δ / (2 * ε))) :=
      mul_nonneg (mul_nonneg (cInc_nonneg γ) hδ.le) (exp_pos _).le
    calc _ ≤ ENNReal.ofReal (δ * (Cθ * θm ^ (mm j))) +
          ((2 ^ (mm j) + 1 : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (cInc γ * δ * exp (-β * log (δ / (2 * ε)))) :=
          add_le_add (lintegral_chainM_le hX hγ hγ2 hδ hε hk2 (mm j)) hg
      _ = ENNReal.ofReal (δ * (Cθ * θm ^ (mm j)) +
            (2 ^ (mm j) + 1) * (cInc γ * δ * exp (-β * log (δ / (2 * ε))))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hN,
            ← ENNReal.ofReal_add (by have := θm_pos; positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (δ * (K * ρ ^ j)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hj := hKρ j
          have hc := cInc_nonneg γ
          calc δ * (Cθ * θm ^ (mm j)) +
                (2 ^ (mm j) + 1) * (cInc γ * δ * exp (-β * log (δ / (2 * ε))))
              ≤ δ * (Cθ * θm ^ (mm j)) +
                (2 ^ (mm j) + 1) * (cInc γ * δ * exp (-β * (j * log 2))) := by gcongr
            _ = δ * (Cθ * θm ^ (mm j) +
                (2 ^ (mm j) + 1) * (cInc γ * exp (-β * (j * log 2)))) := by ring
            _ ≤ δ * (K * ρ ^ j) := mul_le_mul_of_nonneg_left hj hδ.le
  -- the fractional moment of `Ψ`
  set W : Ω → ℝ≥0∞ := fun ω => Psi γ δ n mm (innerSample X 0 δ ω) ^ p with hW
  have hPsi : ∫⁻ ω, W ω ∂P ≤ ENNReal.ofReal (δ ^ p * (1 + K1)) := by
    have hpt : ∀ ω, W ω ≤ (⨆ i, massFun γ 0 δ (n + i) (innerSample X 0 δ ω)) ^ p +
        ∑' j, Bj γ δ n mm j (innerSample X 0 δ ω) ^ p := fun ω =>
      (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans
        (add_le_add le_rfl (rpow_tsum_le_tsum_rpow _ hp0 hp1))
    have hm1 : Measurable (fun ω => (⨆ i, massFun γ 0 δ (n + i) (innerSample X 0 δ ω)) ^ p) :=
      ((Measurable.iSup fun i => measurable_massFun γ 0 δ (n + i)).comp
        (measurable_innerSample hX 0 δ)).pow_const p
    have hm2 : ∀ j, Measurable (fun ω => Bj γ δ n mm j (innerSample X 0 δ ω) ^ p) := fun j =>
      ((measurable_Bj γ δ n mm j).comp (measurable_innerSample hX 0 δ)).pow_const p
    have hsup := lintegral_iSup_innerMass_rpow_le hX hγ hγ2 hδ hp0 hp1 hk (P := P) (t := 0)
    have hgeo : ∀ j, (∫⁻ ω, Bj γ δ n mm j (innerSample X 0 δ ω) ∂P) ^ p ≤
        ENNReal.ofReal ((δ * K) ^ p * (ρ ^ p) ^ j) := by
      intro j
      refine (ENNReal.rpow_le_rpow (hBj j) hp0.le).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le]
      congr 1
      rw [show δ * (K * ρ ^ j) = (δ * K) * ρ ^ j by ring,
        mul_rpow (by positivity) (by positivity), ← rpow_natCast, ← rpow_mul hρ0,
        mul_comm (j : ℝ) p, rpow_mul hρ0, rpow_natCast]
    have hsum : ∑' j, ENNReal.ofReal ((δ * K) ^ p * (ρ ^ p) ^ j) =
        ENNReal.ofReal ((δ * K) ^ p * (1 - ρ ^ p)⁻¹) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
        ((summable_geometric_of_lt_one hρp0 hρp1).mul_left _), tsum_mul_left,
        tsum_geometric_of_lt_one hρp0 hρp1]
    calc ∫⁻ ω, W ω ∂P
        ≤ ∫⁻ ω, ((⨆ i, massFun γ 0 δ (n + i) (innerSample X 0 δ ω)) ^ p +
            ∑' j, Bj γ δ n mm j (innerSample X 0 δ ω) ^ p) ∂P := lintegral_mono hpt
      _ = ∫⁻ ω, (⨆ i, massFun γ 0 δ (n + i) (innerSample X 0 δ ω)) ^ p ∂P +
            ∑' j, ∫⁻ ω, Bj γ δ n mm j (innerSample X 0 δ ω) ^ p ∂P := by
          rw [lintegral_add_left hm1, lintegral_tsum fun j => (hm2 j).aemeasurable]
      _ ≤ (ENNReal.ofReal δ ^ p + ENNReal.ofReal ((cInc γ * δ) ^ p) *
            (1 - ENNReal.ofReal (exp (-(p * bdryRate γ) * log 2)))⁻¹) +
            ∑' j, ENNReal.ofReal ((δ * K) ^ p * (ρ ^ p) ^ j) := by
          refine add_le_add hsup (ENNReal.tsum_le_tsum fun j => ?_)
          exact (lintegral_rpow_le_rpow_lintegral
            ((measurable_Bj γ δ n mm j).comp (measurable_innerSample hX 0 δ)).aemeasurable
            hp0 hp1).trans (hgeo j)
      _ = ENNReal.ofReal (δ ^ p * (1 + K1)) := by
          rw [hsum, ← hq]
          have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
            rw [ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
          have hi0 : (0 : ℝ) ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
          have hi1 : (0 : ℝ) ≤ (1 - ρ ^ p)⁻¹ := inv_nonneg.2 (by linarith)
          rw [e1, ← ENNReal.ofReal_inv_of_pos (by linarith),
            ENNReal.ofReal_rpow_of_nonneg hδ.le hp0.le,
            ← ENNReal.ofReal_mul (rpow_nonneg (mul_nonneg (cInc_nonneg γ) hδ.le) _),
            ← ENNReal.ofReal_add (rpow_nonneg hδ.le _)
              (mul_nonneg (rpow_nonneg (mul_nonneg (cInc_nonneg γ) hδ.le) _) hi0),
            ← ENNReal.ofReal_add (add_nonneg (rpow_nonneg hδ.le _)
              (mul_nonneg (rpow_nonneg (mul_nonneg (cInc_nonneg γ) hδ.le) _) hi0))
              (mul_nonneg (rpow_nonneg (mul_nonneg hδ.le hK0) _) hi1)]
          congr 1
          rw [hK1, mul_rpow (cInc_nonneg γ) hδ.le, mul_rpow hδ.le hK0]
          ring
  -- independence of `Ω` and the inner field
  set A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (exp (γ / 2 * omegaAvg X 2 0 δ ω) * δ ^ (γ ^ 2 / 4)) ^ p with hA
  have hφ : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (γ / 2 * x) * δ ^ (γ ^ 2 / 4)) ^ p) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).pow_const p
  have hψ : Measurable (fun y : FieldSample => Psi γ δ n mm y ^ p) :=
    (measurable_Psi γ δ n mm).pow_const p
  have hind : IndepFun A W P := (indepFun_omega_innerSample hX hδ hR).comp hφ hψ
  have hAm : Measurable A := hφ.comp (measurable_omegaAvg hX 2 0 δ)
  have hWm : Measurable W := hψ.comp (measurable_innerSample hX 0 δ)
  have hpath := ae_annTo_le hX γ 2 n mm (P := P)
  have hG0 : 0 ≤ δ ^ (p * (γ ^ 2 / 4)) *
      exp ((2 * log 2 - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2) := by positivity
  calc ∫⁻ ω, annTo γ (zField X 2 ω) n ^ p ∂P ≤ ∫⁻ ω, (A * W) ω ∂P := by
        refine lintegral_mono_ae (hpath.mono fun ω h => ?_)
        simp only [Pi.mul_apply, hA, hW]
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        exact ENNReal.rpow_le_rpow h hp0.le
    _ = (∫⁻ ω, A ω ∂P) * ∫⁻ ω, W ω ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hAm hWm hind
    _ ≤ ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
          exp ((2 * log 2 - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2)) *
        ENNReal.ofReal (δ ^ p * (1 + K1)) := by
        have hAint : ∫⁻ ω, A ω ∂P = ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
            exp ((2 * log 2 - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2)) :=
          lintegral_omega_factor_rpow hX γ hδ hR hp0.le
        rw [hAint]
        gcongr
    _ = ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
          exp ((2 * log 2 - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2) *
        (δ ^ p * (1 + K1))) := (ENNReal.ofReal_mul hG0).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (dyadic_real_le hp0 hK10 hδR)

end OffsetP3b
end QuantumZipper
