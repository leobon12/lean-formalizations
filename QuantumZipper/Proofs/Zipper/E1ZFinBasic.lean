import QuantumZipper.Proofs.Zipper.E1NuExist
import QuantumZipper.Proofs.LQG.InfiniteMass

/-!
# Z-FIN, deterministic and almost-sure ingredients

`handoff/E1-PLAN.md`, node **Z-FIN** (TASKS R24); `blueprint/E_BRANCH_BLUEPRINT.md` §4 Z-FIN.
Paper: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68): the Palm normalizer is
`E ν[−δ,0]`. This file collects the ingredients of `E1.zfin_of_tr` (`E1ZFin.lean`):

* **ZF-1** (time `0`): `realRevMap_zero_of_ne`, `isLive_zero_of_neg`, `Fder_zero`, `varpiT_zero`,
  `qt_zero`, `rhoT_zero` (`ρ_0(x; v) = ρ_ϖ(x)`);
* **ZF-2**: `lintegral_rhoNorm_pos_lt_top`: `0 < ∫_{[−δ,0)} ρ_ϖ < ∞` (`e^{γ 𝔥₀/2} = |x|`, and the
  potential `k_ϖ` is bounded on `[−δ,0]` since `ϖ` is carried by a compact subset of `ℍ`);
* **ZF-3**: `ae_nuPalm_singleton_zero`: under B3(a) (`Blueprint.RevCouplingBoundaryMeasureRegular`)
  `ν{0} = 0` a.s.

ZF-1 and ZF-2 are own elementary arguments; ZF-3 repeats the bookkeeping of
`E1.ae_exists_isVagueLimitR_nuPalm` (NU-EX).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun PalmNorm

variable {v : ℝ → ℝ} {κ : ℝ} {ϖ : Measure ℂ}

/-! ## ZF-1: the Palm-zip data at time `0` -/

theorem IsNormalizer.ae_mem_H (hϖ : IsNormalizer ϖ) : ∀ᵐ z ∂ϖ, z ∈ H := by
  obtain ⟨K, -, hKH, hK0⟩ := hϖ.cpt
  exact measure_mono_null (fun z hz => fun hzK => hz (hKH hzK)) hK0

theorem realRevMap_zero_of_ne (hv0 : v 0 = 0) {x : ℝ} (hx : x ≠ 0) : realRevMap v 0 x = x := by
  have h : ∃ u, IsRealRevSol v x 0 u := ⟨fun _ => x, continuousOn_const, fun t ht => by
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    exact ⟨hx, by simp [hv0]⟩⟩
  have e : realRevMap v 0 x = Classical.choose h 0 := by
    simp only [realRevMap, h, ↓reduceDIte]
  rw [e, RealLine.isRealRevSol_zero (Classical.choose_spec h) le_rfl, hv0, sub_zero]

theorem isLive_zero_of_neg (hv : Continuous v) (hv0 : v 0 = 0) {x : ℝ} (hx : x < 0) :
    IsLive v 0 x := by
  show ENNReal.ofReal 0 < realHitTime v x
  rw [ENNReal.ofReal_zero]
  exact RealLine.realHitTime_pos hv (by rw [hv0]; exact hx.ne)

theorem Fder_zero (V : ℝ → ℝ) (x : ℝ) : Fder V 0 x = 1 := by
  simp [Fder]

theorem varpiT_zero (hv : Continuous v) (hv0 : v 0 = 0) (hϖH : ∀ᵐ z ∂ϖ, z ∈ H) :
    varpiT v 0 ϖ = ϖ := by
  have h : revMap v 0 =ᵐ[ϖ] id := hϖH.mono fun z hz => revMap_zero_eq hv hv0 hz
  rw [varpiT, Measure.map_congr h, Measure.map_id]

theorem isOpen_H' : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

theorem qt_zero (hv : Continuous v) (hv0 : v 0 = 0) (hϖH : ∀ᵐ z ∂ϖ, z ∈ H) :
    qt κ v 0 ϖ = 0 := by
  have h : (fun z => Real.log ‖deriv (revMap v 0) z‖) =ᵐ[ϖ] fun _ => 0 := by
    filter_upwards [hϖH] with z hz
    have heq : revMap v 0 =ᶠ[𝓝 z] id :=
      Filter.eventually_of_mem (isOpen_H'.mem_nhds hz) fun w hw => revMap_zero_eq hv hv0 hw
    rw [heq.deriv_eq, deriv_id]
    simp
  rw [qt, integral_congr_ae h, integral_zero, mul_zero]

theorem rhoT_zero (hv : Continuous v) (hv0 : v 0 = 0) (hϖ : IsNormalizer ϖ) {x : ℝ}
    (hx : x ≠ 0) : rhoT κ v 0 ϖ x = rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x := by
  rw [rhoT, qt_zero hv hv0 hϖ.ae_mem_H, Fder_zero, varpiT_zero hv hv0 hϖ.ae_mem_H,
    realRevMap_zero_of_ne hv0 hx]
  simp

/-! ## ZF-2: the Palm normalizer of the deterministic density -/

theorem abs_log_le_of_mem {c M y : ℝ} (hc : 0 < c) (hcy : c ≤ y) (hyM : y ≤ M) :
    |Real.log y| ≤ |Real.log c| + |Real.log M| := by
  have h1 : Real.log c ≤ Real.log y := Real.log_le_log hc hcy
  have h2 : Real.log y ≤ Real.log M := Real.log_le_log (hc.trans_le hcy) hyM
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log M)]
  · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log c)]

/-- The potential `k_ϖ` is bounded on `[−δ, 0]`. -/
theorem exists_abs_kPot_le (hϖ : IsNormalizer ϖ) (δ : ℝ) :
    ∃ L : ℝ, ∀ x ∈ Icc (-δ) 0, |kPot ϖ (x : ℂ)| ≤ L := by
  have := hϖ.prob
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  have hK : ∀ᵐ z ∂ϖ, z ∈ K := measure_mono_null (fun z hz => hz) hK0
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  -- a positive lower bound for `Im` on `K`
  obtain ⟨c, hc, hcK⟩ : ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ z.im := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ :=
        hKc.exists_isMinOn hKne Complex.continuous_im.continuousOn
      exact ⟨z₀.im, hKH hz₀, fun z hz => hmin hz⟩
  set L := |Real.log c| + |Real.log (|δ| + R)| with hL
  refine ⟨(L + L) * 1, fun x hx => ?_⟩
  have hxδ : |x| ≤ |δ| := by
    rw [abs_le]; constructor <;> [linarith [hx.1, le_abs_self δ, neg_abs_le δ];
      linarith [hx.2, abs_nonneg δ]]
  have hbd : ∀ᵐ z ∂ϖ, ‖neumannH (x : ℂ) z‖ ≤ L + L := by
    filter_upwards [hK] with z hz
    have hzc := hcK z hz
    have hzR := hR z hz
    have hxn : ‖(x : ℂ)‖ ≤ |δ| := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hxδ
    have h1lo : c ≤ ‖(x : ℂ) - z‖ := by
      refine hzc.trans ((le_abs_self _).trans ?_)
      have := Complex.abs_im_le_norm ((x : ℂ) - z)
      simpa [abs_neg] using this
    have h1hi : ‖(x : ℂ) - z‖ ≤ |δ| + R := (norm_sub_le _ _).trans (add_le_add hxn hzR)
    have h2lo : c ≤ ‖(x : ℂ) - (starRingEnd ℂ) z‖ := by
      refine hzc.trans ((le_abs_self _).trans ?_)
      have := Complex.abs_im_le_norm ((x : ℂ) - (starRingEnd ℂ) z)
      simpa using this
    have h2hi : ‖(x : ℂ) - (starRingEnd ℂ) z‖ ≤ |δ| + R :=
      (norm_sub_le _ _).trans (add_le_add hxn (by rw [Complex.norm_conj]; exact hzR))
    rw [Real.norm_eq_abs, neumannH]
    have e1 := abs_log_le_of_mem hc h1lo h1hi
    have e2 := abs_log_le_of_mem hc h2lo h2hi
    calc |-Real.log ‖(x : ℂ) - z‖ - Real.log ‖(x : ℂ) - (starRingEnd ℂ) z‖|
        ≤ |Real.log ‖(x : ℂ) - z‖| + |Real.log ‖(x : ℂ) - (starRingEnd ℂ) z‖| := by
          rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
      _ ≤ L + L := add_le_add e1 e2
  have := norm_integral_le_of_norm_le_const hbd
  rw [probReal_univ] at this
  rw [kPot]
  simpa [Real.norm_eq_abs] using this

/-- For `x ≠ 0`, `ρ_ϖ(x) = |x| · exp(A − (γ²/4) k_ϖ(x))` with `A` independent of `x`. -/
theorem rhoNorm_h0rev_eq (hκ : 0 < κ) {x : ℝ} (hx : x ≠ 0) :
    rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x = |x| * Real.exp
      (-(Real.sqrt κ / 2 * ∫ u, h0rev κ u ∂ϖ) - Real.sqrt κ ^ 2 / 4 * kPot ϖ x +
        Real.sqrt κ ^ 2 / 8 * kkPot ϖ) := by
  rw [rhoNorm, ← InfMass.exp_h0rev hκ hx, ← Real.exp_add]
  congr 1
  ring

theorem lintegral_rhoNorm_pos_lt_top (hκ : 0 < κ) (hϖ : IsNormalizer ϖ) {δ : ℝ} (hδ : 0 < δ) :
    0 < ∫⁻ x in Ico (-δ) 0, ENNReal.ofReal (rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x) ∧
      ∫⁻ x in Ico (-δ) 0, ENNReal.ofReal (rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x) < ⊤ := by
  obtain ⟨L, hL⟩ := exists_abs_kPot_le hϖ δ
  set A := -(Real.sqrt κ / 2 * ∫ u, h0rev κ u ∂ϖ) + Real.sqrt κ ^ 2 / 8 * kkPot ϖ with hA
  set e₁ := Real.exp (A - Real.sqrt κ ^ 2 / 4 * L) with he₁
  set e₂ := Real.exp (A + Real.sqrt κ ^ 2 / 4 * L) with he₂
  have hk4 : 0 ≤ Real.sqrt κ ^ 2 / 4 := by positivity
  have hbd : ∀ x ∈ Ico (-δ) 0, |x| * e₁ ≤ rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x ∧
      rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x ≤ |x| * e₂ := by
    intro x hx
    have hx0 : x ≠ 0 := hx.2.ne
    have hk := abs_le.1 (hL x ⟨hx.1, hx.2.le⟩)
    rw [rhoNorm_h0rev_eq hκ hx0]
    constructor
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg x)
      rw [hA]; nlinarith [mul_le_mul_of_nonneg_left hk.2 hk4]
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg x)
      rw [hA]; nlinarith [mul_le_mul_of_nonneg_left hk.1 hk4]
  constructor
  · have hsub : Ico (-δ) (-δ / 2) ⊆ Ico (-δ) 0 := Ico_subset_Ico_right (by linarith)
    have hlow : ∫⁻ _ in Ico (-δ) (-δ / 2), ENNReal.ofReal (δ / 2 * e₁) ≤
        ∫⁻ x in Ico (-δ) (-δ / 2), ENNReal.ofReal (rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x) := by
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2
        (Eventually.of_forall fun x hx => ENNReal.ofReal_le_ofReal ?_))
      refine le_trans ?_ (hbd x (hsub hx)).1
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.2]
    refine lt_of_lt_of_le ?_ (hlow.trans (lintegral_mono_set hsub))
    rw [setLIntegral_const, Real.volume_Ico]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne'
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  · have hup : ∫⁻ x in Ico (-δ) 0, ENNReal.ofReal (rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x) ≤
        ∫⁻ _ in Ico (-δ) 0, ENNReal.ofReal (δ * e₂) := by
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2
        (Eventually.of_forall fun x hx => ENNReal.ofReal_le_ofReal ?_))
      refine (hbd x hx).2.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      rw [abs_of_neg hx.2]; linarith [hx.1]
    refine lt_of_le_of_lt hup ?_
    rw [setLIntegral_const, Real.volume_Ico]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-! ## ZF-3: `ν` has no atom at `0` -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

theorem ae_nuPalm_singleton_zero (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, nuPalm κ T B X ϖ ω {0} = 0 := by
  obtain ⟨B'', hB'', hind'', hV⟩ := b2_V_brownian (κ := κ) hB hind hT.le
  filter_upwards [hReg κ hκ hκ4 T hT P B'' X hB'' hX hind'', hV,
    b2_ident_qBoundaryMeasure hB hX hind hT.le, ae_nuPalm_eq_smul (κ := κ) hB hX hind hT.le ϖ]
    with ω hRω hVω hid hsm
  have hrevV : revMap (Vr κ T B ω) T = revMap (drive κ B'' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hcf : couplingFieldRev κ (Vr κ T B ω) T (X ω) =
      couplingFieldRev κ (drive κ B'' ω) T (X ω) := by
    simp only [couplingFieldRev, hrevV]
  rw [hsm, Measure.smul_apply, hid, hcf, hRω.1 0, smul_zero]

end E1
end QuantumZipper
