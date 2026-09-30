import QuantumZipper.Proofs.Zipper.F2WedgeCoupleFree
import QuantumZipper.Proofs.LQG.WedgeCanonical3
import QuantumZipper.Proofs.Zipper.B5LocDet

/-!
# WEDGE-COUPLE (2): the pathwise identity inside `B(0, 1/2)`

For the coupled free field `X' = coupleField X₁ X₂` (`F2WedgeCoupleFree.lean`) and the wedge
radial path `A = wedgePath α Q a b'` whose forward part is the radial process of `X₁`
(`√2 a = A^{X₁}`, i.e. `a = radialBMpos X₁`), almost surely, on every dyadic circle of radius
`≤ 1/2` centred in `B(0, 1/2)`,

  `wedgeField (lateralPart X') A Q = X₁ + α(−log|·|) − h¹_1(0)`

(`theorem ae_dyCircAgree_couple`). Source: Sheffield, arXiv:1012.4797, §1.6 (the wedge restricted
to `B₁` is `h† + A_{−log|·|} + Q log`, with `A_t` for `t ≥ 0` the radial process `B_{2t} + αt`
of a free field; Duplantier–Miller–Sheffield, arXiv:1409.7055, Def. 4.5). The circle
bookkeeping is our own: all these circles lie in the unit disc, where `A` only uses its forward
part, and the lateral part of `X'` equals that of `X₁` (its radial part is that of `X₂`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace F2

open WedgeTK

/-- `radAvgReg` only reads the dyadic semicircles about `0`. -/
theorem radAvgReg_congr_dyRad {x y : FieldSample}
    (h : ∀ n m : ℕ, x (foldedCircle 0 (dyRad n m)) = y (foldedCircle 0 (dyRad n m))) {r : ℝ}
    (hr : 0 < r) : radAvgReg x r = radAvgReg y r := by
  have hs : ∀ n : ℕ, dyadicRound n r + radius n = dyRad n (⌊(2 : ℝ) ^ n * r⌋.toNat) := by
    intro n
    rw [CoordsFull.radAvg_radius_eq_div, dyRad]
    have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * r⌋ := Int.floor_nonneg.2 (by positivity)
    have : ((⌊(2 : ℝ) ^ n * r⌋.toNat : ℕ) : ℝ) = (⌊(2 : ℝ) ^ n * r⌋ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [this]; push_cast; ring
  unfold radAvgReg
  congr 1
  funext n
  rw [hs n]
  exact h _ _

theorem radInt_fc0 (x : FieldSample) {a : ℝ} (ha : 0 < a) :
    radInt x (foldedCircle 0 a) = radAvgReg x a := by
  unfold radInt
  rw [integral_congr_ae ((fc_ae_norm ha).mono fun u hu =>
      show radAvgReg x ‖u‖ = radAvgReg x a by rw [hu]),
    integral_const, probReal_univ, one_smul]

/-- The radial part of the coupled field is that of `X₂`. -/
theorem radAvgReg_coupleField {Ω Ω' : Type*} {X₁ : Ω → FieldSample} {X₂ : Ω' → FieldSample}
    {ω : Ω × Ω'} {G₁ G₂ : ℂ × ℝ → ℝ} (hg₁ : GoodRad (X₁ ω.1) G₁) (hg₂ : GoodRad (X₂ ω.2) G₂)
    {s : ℝ} (hs : 0 < s) : radAvgReg (coupleField X₁ X₂ ω) s = radAvgReg (X₂ ω.2) s := by
  refine radAvgReg_congr_dyRad (fun n m => ?_) hs
  have hd := dyRad_pos n m
  rw [coupleField_apply ω (isAdmissibleH_foldedCircle GaussTK.zero_mem_Hbar hd),
    radInt_fc0 _ hd, radInt_fc0 _ hd, hg₁.2 n m, hg₁.radAvgReg_eq hd, hg₂.2 n m,
    hg₂.radAvgReg_eq hd]
  ring

/-- A.s. integrability of the radial profile on all dyadic circles. -/
theorem ae_integrable_radAvgReg_dyadic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      Integrable (fun u => radAvgReg (X ω) ‖u‖) (foldedCircle (dyadicRoundC n z) (radius k)) := by
  have hper : ∀ p : ℕ × ℤ × ℤ, ∀ᵐ ω ∂P, WedgeCan.gridPt p ∈ Hbar → ∀ k : ℕ,
      Integrable (fun u => radAvgReg (X ω) ‖u‖) (foldedCircle (WedgeCan.gridPt p) (radius k)) := by
    intro p
    by_cases hc : WedgeCan.gridPt p ∈ Hbar
    · have : ∀ᵐ ω ∂P, ∀ k : ℕ, Integrable (fun u => radAvgReg (X ω) ‖u‖)
          (foldedCircle (WedgeCan.gridPt p) (radius k)) :=
        ae_all_iff.2 fun k =>
          (ae_radInt_eq hX (isAdmissibleH_foldedCircle hc (radius_pos k))).mono fun ω h => h.1
      exact this.mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hc
  filter_upwards [ae_all_iff.2 hper] with ω h n z hz k
  have hm := CircleCont.dyadicRoundC_mem_Hbar hz n
  rw [WedgeCan.dyadicRoundC_eq_grid n z] at hm ⊢
  exact h _ hm k

/-- **The deterministic identity** for a good sample point. -/
theorem dyCircAgree_couple_of_good {Ω Ω' : Type*} {X₁ : Ω → FieldSample}
    {X₂ : Ω' → FieldSample} {ω : Ω × Ω'} {G₁ G₂ G' : ℂ × ℝ → ℝ}
    (hg₁ : GoodRad (X₁ ω.1) G₁) (hg₂ : GoodRad (X₂ ω.2) G₂)
    (hreg : IsRegularWith (coupleField X₁ X₂ ω) G')
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      coupleField X₁ X₂ ω (foldedCircle (dyadicRoundC n z) (radius k)) =
        G' (dyadicRoundC n z, radius k))
    (hint : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      Integrable (fun u => radAvgReg (X₁ ω.1) ‖u‖) (foldedCircle (dyadicRoundC n z) (radius k)))
    (α Q : ℝ) {a b' : ℝ≥0 → ℝ} (ha : ∀ t, a t = radialBMpos X₁ t ω.1) :
    B5.DyCircAgree (wedgeField (lateralPart (coupleField X₁ X₂ ω)) (wedgePath α Q a b') Q)
      (addConst (X₁ ω.1 + ofFun fun z => α * -Real.log ‖z‖) (-radAvgReg (X₁ ω.1) 1))
      (Metric.ball 0 (1 / 2)) 1 := by
  intro j hj n z hz hc
  set c := dyadicRoundC n z with hc_def
  have hcH : c ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz n
  have hr := radius_pos j
  have hrj : radius j ≤ 1 / 2 := by
    unfold radius
    calc (2 : ℝ)⁻¹ ^ j ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
      _ = 1 / 2 := by norm_num
  have hcn : ‖c‖ < 1 / 2 := mem_ball_zero_iff.1 hc
  have hadm := isAdmissibleH_foldedCircle hcH hr
  set μ := foldedCircle c (radius j) with hμ
  have hsupp : ∀ᵐ u ∂μ, u ≠ 0 ∧ ‖u‖ < 1 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (noAtoms_of_isAdmissibleH hadm 0),
      LocalRule.ae_fc_mem_closedBall hcH hr] with u h0 hb
    refine ⟨h0, ?_⟩
    have h2 := Metric.mem_closedBall.1 hb
    rw [dist_eq_norm] at h2
    linarith [norm_sub_norm_le u c]
  -- the lateral part of the coupled field
  have hev : evalReg (coupleField X₁ X₂ ω) μ = coupleField X₁ X₂ ω μ := by
    rw [hreg.evalReg_fc_of_mem hcH hr, ← hraw n z hz j]
  have hradX : ∫ u, radAvgReg (coupleField X₁ X₂ ω) ‖u‖ ∂μ = radInt (X₂ ω.2) μ := by
    refine integral_congr_ae (hsupp.mono fun u hu => ?_)
    exact radAvgReg_coupleField hg₁ hg₂ (norm_pos_iff.2 hu.1)
  have hlat : lateralPart (coupleField X₁ X₂ ω) μ = X₁ ω.1 μ - radInt (X₁ ω.1) μ := by
    show evalReg _ μ - _ = _
    rw [hev, hradX, coupleField_apply ω hadm]
    ring
  -- the radial integral
  have hprof : ∀ᵐ u ∂μ, Q * -Real.log ‖u‖ + wedgePath α Q a b' (-Real.log ‖u‖) =
      α * -Real.log ‖u‖ + (radAvgReg (X₁ ω.1) ‖u‖ - radAvgReg (X₁ ω.1) 1) := by
    filter_upwards [hsupp] with u hu
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu.1
    have ht : 0 ≤ -Real.log ‖u‖ := by linarith [Real.log_neg hpos hu.2]
    have hcoe : ((-Real.log ‖u‖).toNNReal : ℝ) = -Real.log ‖u‖ := Real.coe_toNNReal _ ht
    simp only [wedgePath, if_pos ht, ha, radialBMpos, radialProc, hcoe, neg_neg,
      Real.exp_log hpos]
    have h2 : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (by norm_num))
    linear_combination (radAvgReg (X₁ ω.1) ‖u‖ - radAvgReg (X₁ ω.1) 1) * h2
  have hL : Integrable (fun u : ℂ => α * -Real.log ‖u‖) μ :=
    (CoordReg.integrable_log_norm_foldedCircle c (radius j)).neg.const_mul α
  have hI : Integrable (fun u => radAvgReg (X₁ ω.1) ‖u‖) μ := hint n z hz j
  have hI2 : Integrable (fun u => radAvgReg (X₁ ω.1) ‖u‖ - radAvgReg (X₁ ω.1) 1) μ :=
    hI.sub (integrable_const _)
  have hwint : ∫ u, (Q * -Real.log ‖u‖ + wedgePath α Q a b' (-Real.log ‖u‖)) ∂μ =
      ∫ u, α * -Real.log ‖u‖ ∂μ + (radInt (X₁ ω.1) μ - radAvgReg (X₁ ω.1) 1) := by
    rw [integral_congr_ae hprof, integral_add hL hI2,
      integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul]
    rfl
  show lateralPart (coupleField X₁ X₂ ω) μ +
      ∫ u, (Q * -Real.log ‖u‖ + wedgePath α Q a b' (-Real.log ‖u‖)) ∂μ =
    (X₁ ω.1 μ + ∫ u, α * -Real.log ‖u‖ ∂μ) + -radAvgReg (X₁ ω.1) 1 * (μ Set.univ).toReal
  rw [hlat, hwint, measure_univ, ENNReal.toReal_one]
  ring

/-- **The pathwise identity, almost surely.** -/
theorem ae_dyCircAgree_couple {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X₁ : Ω → FieldSample} {X₂ : Ω' → FieldSample} (hX₁ : IsFreeGFFModConstH X₁ P)
    (hX₂ : IsFreeGFFModConstH X₂ P') {Pt : ℝ≥0 → Ω → ℝ}
    (hPt : ∀ᵐ ω ∂P, ∀ t, Pt t ω = radialBMpos X₁ t ω) (Bt : ℝ≥0 → Ω' → ℝ) (α Q : ℝ) :
    ∀ᵐ ω ∂(P.prod P'), B5.DyCircAgree
      (wedgeField (lateralPart (coupleField X₁ X₂ ω))
        (wedgePath α Q (fun s => Pt s ω.1) (fun s => Bt s ω.2)) Q)
      (addConst (X₁ ω.1 + ofFun fun z => α * -Real.log ‖z‖) (-radAvgReg (X₁ ω.1) 1))
      (Metric.ball 0 (1 / 2)) 1 := by
  obtain ⟨G₁, hG₁⟩ := exists_isRegVersion hX₁
  obtain ⟨G₂, hG₂⟩ := exists_isRegVersion hX₂
  obtain ⟨G', hG'⟩ := exists_isRegVersion (isFreeGFFModConstH_coupleField hX₁ hX₂)
  filter_upwards [ae_fst (P' := P') hG₁.ae_good, ae_snd (P := P) hG₂.ae_good, hG'.reg,
    WedgeCan.ae_raw_dyadic hG', ae_fst (P' := P') (ae_integrable_radAvgReg_dyadic hX₁),
    ae_fst (P' := P') hPt] with ω h1 h2 h3 h4 h5 h6
  exact dyCircAgree_couple_of_good h1 h2 h3 h4 h5 α Q h6

end F2
end QuantumZipper
