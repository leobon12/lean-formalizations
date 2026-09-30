import QuantumZipper.Proofs.GFF.K3.C5Norm
import QuantumZipper.Proofs.GFF.K3.BubbleGates
import QuantumZipper.Proofs.Thm11.AddendumArea

/-!
# GFF-K3, node C5: `zeroGFFTestCov (sleComplement) = ∬ ρ σ V_T` (unconditional)

Blueprint `blueprint/GFF_K3_BLUEPRINT.md` §3.C node C5, with the D8/D4 revisions (`hStab`
dropped; C5′ of `blueprint/EXT_PP_BLUEPRINT.md` §B), and `hRS` discharged by the proved
`RS.rohdeSchrammTraceGen_of_lt_eight` (through `ae_genTrace`), BUB-4 by `bub4Stmt`
(`BubbleGates.lean`) and AD-2 by `Thm11Area.ae_volume_sleTrace_eq_zero`.

From the dual-norm identity `dualNormSq_compl_image_eq` (`C5Norm.lean`) by polarization
(`dualCov_compl_image_eq`) and the splitting `ρ = ρ⁺ − ρ⁻` of `zeroGFFTestCov`
(`zeroGFFTestCov_compl_image_eq`); the final a.s. statement is `zeroGFFTestCov_sleComplement`.
Source: Sheffield, arXiv:1012.4797, Theorem 1.1 addendum (p. 12).
-/

noncomputable section

open Set Filter Topology MeasureTheory Function ProbabilityTheory
open scoped ENNReal NNReal

namespace QuantumZipper.K3

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

/-- The Borel version of `V_T`, restricted to `ℍ × ℍ`. -/
def c5Vm (W : ℝ → ℝ) (T : ℝ) : ℂ × ℂ → ℝ≥0∞ := (H ×ˢ H).indicator fun p => VTe W T p.1 p.2

/-- The bilinear `V_T`-energy `∬ g₁(a) g₂(b) V_T(a,b)`. -/
def c5E (W : ℝ → ℝ) (T : ℝ) (g₁ g₂ : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, g₁ p.1 * (g₂ p.2 * VTe W T p.1 p.2) ∂((volume : Measure ℂ).prod volume)

theorem c5_integrand_eq {g₁ g₂ : ℂ → ℝ≥0∞} (h1 : ∀ z ∉ H, g₁ z = 0) (h2 : ∀ z ∉ H, g₂ z = 0)
    (p : ℂ × ℂ) : g₁ p.1 * (g₂ p.2 * VTe W T p.1 p.2) = g₁ p.1 * (g₂ p.2 * c5Vm W T p) := by
  by_cases hp : p ∈ H ×ˢ H
  · rw [c5Vm, indicator_of_mem hp]
  · rcases not_and_or.1 hp with h | h
    · simp [h1 _ h]
    · simp [h2 _ h]

theorem measurable_c5_integrand (hW : Continuous W) (hW0 : W 0 = 0) {g₁ g₂ : ℂ → ℝ≥0∞}
    (hm1 : Measurable g₁) (hm2 : Measurable g₂) (h1 : ∀ z ∉ H, g₁ z = 0)
    (h2 : ∀ z ∉ H, g₂ z = 0) : Measurable fun p : ℂ × ℂ => g₁ p.1 * (g₂ p.2 * VTe W T p.1 p.2) := by
  rw [show (fun p : ℂ × ℂ => g₁ p.1 * (g₂ p.2 * VTe W T p.1 p.2)) = fun p =>
    g₁ p.1 * (g₂ p.2 * c5Vm W T p) from funext (c5_integrand_eq h1 h2)]
  exact (hm1.comp measurable_fst).mul ((hm2.comp measurable_snd).mul
    (measurable_indicator_VTe hW hW0 T))

theorem c5E_comm (g₁ g₂ : ℂ → ℝ≥0∞) : c5E W T g₁ g₂ = c5E W T g₂ g₁ := by
  unfold c5E
  rw [← lintegral_prod_swap]
  refine lintegral_congr fun p => ?_
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [VTe_comm]; ring

theorem c5E_add_left (hW : Continuous W) (hW0 : W 0 = 0) {g₁ g₁' g₂ : ℂ → ℝ≥0∞}
    (hm1 : Measurable g₁) (hm2 : Measurable g₂) (h1 : ∀ z ∉ H, g₁ z = 0)
    (h2 : ∀ z ∉ H, g₂ z = 0) :
    c5E W T (g₁ + g₁') g₂ = c5E W T g₁ g₂ + c5E W T g₁' g₂ := by
  unfold c5E
  rw [← lintegral_add_left (measurable_c5_integrand hW hW0 hm1 hm2 h1 h2)]
  refine lintegral_congr fun p => ?_
  simp only [Pi.add_apply]; ring

/-- Finiteness: `‖g dz‖²_{U} < ∞` for `U ⊆ ℍ` open (monotonicity into `ℍ = ℍ \ K_0`). -/
theorem dualNormSq_lt_top_of_subset_H (hW : Continuous W) (hW0 : W 0 = 0) {U : Set ℂ}
    (hU : IsOpen U) (hUH : U ⊆ H) {g : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ} (hu : BddDens g M R) :
    dualNormSq U (zeroSpace U) (volume.withDensity g) < ⊤ := by
  have hsub : U ⊆ H \ fwdHull W 0 := fun z hz => ⟨hUH hz, fun hK => by
    have := (swallowTime_pos hW (hUH hz)).trans_le hK.2
    simp at this⟩
  exact (dualNormSq_zeroSpace_mono hU hsub).trans_lt
    (dualNormSq_withDensity_lt_top (isConformalOnto_fwdMap hW hW0 le_rfl) diff_subset hu)

/-- **C5′, covariance form**, by polarization of `dualNormSq_compl_image_eq`. -/
theorem dualCov_compl_image_eq (hg : GenTrace W η) (hT : 0 ≤ T)
    (harea : volume (η '' Icc 0 T ∩ H) = 0) {g₁ g₂ : ℂ → ℝ≥0∞} {M₁ M₂ : ℝ≥0∞} {R₁ R₂ : ℝ}
    (hu₁ : BddDens g₁ M₁ R₁) (hu₂ : BddDens g₂ M₂ R₂) (h1 : ∀ z ∉ H, g₁ z = 0)
    (h2 : ∀ z ∉ H, g₂ z = 0) :
    dualCov (H \ η '' Icc 0 T) (zeroSpace (H \ η '' Icc 0 T)) (volume.withDensity g₁)
      (volume.withDensity g₂) = (c5E W T g₁ g₂).toReal := by
  have hW := hg.contW
  have hW0 := hg.zeroW
  have h12 : ∀ z ∉ H, (g₁ + g₂) z = 0 := fun z hz => by simp [h1 z hz, h2 z hz]
  have hN := fun {g : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ} (hu : BddDens g M R)
    (hgH : ∀ z ∉ H, g z = 0) => dualNormSq_compl_image_eq bub4Stmt hg hT harea hu hgH
  have hfin := fun {g : ℂ → ℝ≥0∞} {M : ℝ≥0∞} {R : ℝ} (hu : BddDens g M R) =>
    dualNormSq_lt_top_of_subset_H hW hW0 (hg.isOpen_compl_image T) diff_subset hu
  unfold dualCov
  rw [← withDensity_add_left hu₁.meas, hN hu₁ h1, hN hu₂ h2, hN (hu₁.add hu₂) h12]
  have hf12 := hfin (hu₁.add hu₂)
  rw [hN (hu₁.add hu₂) h12] at hf12
  have hexp : c5E W T (g₁ + g₂) (g₁ + g₂) =
      c5E W T g₁ g₁ + c5E W T g₁ g₂ + (c5E W T g₁ g₂ + c5E W T g₂ g₂) := by
    rw [c5E_add_left hW hW0 hu₁.meas (hu₁.add hu₂).meas h1 h12,
      c5E_comm g₁ (g₁ + g₂), c5E_comm g₂ (g₁ + g₂),
      c5E_add_left hW hW0 hu₁.meas hu₁.meas h1 h1, c5E_add_left hW hW0 hu₁.meas hu₂.meas h1 h2,
      c5E_comm g₂ g₁]
  show ((c5E W T (g₁ + g₂) (g₁ + g₂)).toReal - (c5E W T g₁ g₁).toReal -
    (c5E W T g₂ g₂).toReal) / 2 = (c5E W T g₁ g₂).toReal
  change c5E W T (g₁ + g₂) (g₁ + g₂) < ⊤ at hf12
  rw [hexp] at hf12 ⊢
  obtain ⟨hab, hbc⟩ := ENNReal.add_lt_top.1 hf12
  obtain ⟨ha, hb⟩ := ENNReal.add_lt_top.1 hab
  obtain ⟨-, hc⟩ := ENNReal.add_lt_top.1 hbc
  rw [ENNReal.toReal_add hab.ne hbc.ne, ENNReal.toReal_add ha.ne hb.ne,
    ENNReal.toReal_add hb.ne hc.ne]
  ring

/-- `c5E` is finite for bounded densities with bounded support in `ℍ`. -/
theorem c5E_lt_top (hg : GenTrace W η) (hT : 0 ≤ T) (harea : volume (η '' Icc 0 T ∩ H) = 0)
    {g₁ g₂ : ℂ → ℝ≥0∞} {M₁ M₂ : ℝ≥0∞} {R₁ R₂ : ℝ} (hu₁ : BddDens g₁ M₁ R₁)
    (hu₂ : BddDens g₂ M₂ R₂) (h1 : ∀ z ∉ H, g₁ z = 0) (h2 : ∀ z ∉ H, g₂ z = 0) :
    c5E W T g₁ g₂ < ⊤ := by
  have h12 : ∀ z ∉ H, (g₁ + g₂) z = 0 := fun z hz => by simp [h1 z hz, h2 z hz]
  have hf := dualNormSq_lt_top_of_subset_H hg.contW hg.zeroW (hg.isOpen_compl_image T)
    diff_subset (hu₁.add hu₂)
  rw [dualNormSq_compl_image_eq bub4Stmt hg hT harea (hu₁.add hu₂) h12] at hf
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hf
  exact mul_le_mul' (le_self_add) (mul_le_mul' le_add_self le_rfl)

/-- A bounded density with finite `c5E` gives an integrable real kernel with that integral. -/
theorem c5_integral_toReal (hW : Continuous W) (hW0 : W 0 = 0) {g₁ g₂ : ℂ → ℝ≥0∞}
    (hm1 : Measurable g₁) (hm2 : Measurable g₂) (h1 : ∀ z ∉ H, g₁ z = 0)
    (h2 : ∀ z ∉ H, g₂ z = 0) (hfin : c5E W T g₁ g₂ ≠ ⊤) :
    Integrable (fun q : ℂ × ℂ => (g₁ q.1).toReal * ((g₂ q.2).toReal * (c5Vm W T q).toReal))
      ((volume : Measure ℂ).prod volume) ∧
    ∫ q, (g₁ q.1).toReal * ((g₂ q.2).toReal * (c5Vm W T q).toReal)
      ∂((volume : Measure ℂ).prod volume) = (c5E W T g₁ g₂).toReal := by
  have heq : (fun q : ℂ × ℂ => (g₁ q.1).toReal * ((g₂ q.2).toReal * (c5Vm W T q).toReal)) =
      fun q => (g₁ q.1 * (g₂ q.2 * c5Vm W T q)).toReal := by
    funext q; simp [ENNReal.toReal_mul]
  have hmeas : Measurable fun q : ℂ × ℂ => g₁ q.1 * (g₂ q.2 * c5Vm W T q) :=
    (hm1.comp measurable_fst).mul ((hm2.comp measurable_snd).mul
      (measurable_indicator_VTe hW hW0 T))
  have hlint : ∫⁻ q, g₁ q.1 * (g₂ q.2 * c5Vm W T q) ∂((volume : Measure ℂ).prod volume) =
      c5E W T g₁ g₂ := by
    unfold c5E; exact lintegral_congr fun p => (c5_integrand_eq h1 h2 p).symm
  rw [heq]
  refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable (hlint ▸ hfin), ?_⟩
  rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas (hlint ▸ hfin)), hlint]

/-- A continuous compactly supported function gives a bounded density with bounded support. -/
theorem bddDens_ofReal_of_hasCompactSupport {f : ℂ → ℝ} (hc : Continuous f)
    (hcs : HasCompactSupport f) : ∃ M R, BddDens (fun z => ENNReal.ofReal (f z)) M R := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  refine ⟨ENNReal.ofReal C, R, ⟨ENNReal.measurable_ofReal.comp hc.measurable,
    ENNReal.ofReal_lt_top, fun z => ENNReal.ofReal_le_ofReal
      (le_trans (le_abs_self _) (by rw [← Real.norm_eq_abs]; exact hC z)), fun z hz => ?_⟩⟩
  rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hR h)), ENNReal.ofReal_zero]

/-- **C5 (deterministic form).** For a curve-generated chain whose trace has zero area,
`zeroGFFTestCov (ℍ \ η[0,T]) ρ σ = ∫∫ ρ(a) σ(b) V_T(a,b)`. -/
theorem zeroGFFTestCov_compl_image_eq (hg : GenTrace W η) (hT : 0 ≤ T)
    (harea : volume (η '' Icc 0 T ∩ H) = 0) (ρ σ : TestFun H) :
    zeroGFFTestCov (H \ η '' Icc 0 T) ρ.1 σ.1 = ∫ a, ∫ b, ρ.1 a * σ.1 b * VT W T a b := by
  have hW := hg.contW
  have hW0 := hg.zeroW
  have hρc : Continuous ρ.1 := ρ.2.1.continuous
  have hσc : Continuous σ.1 := σ.2.1.continuous
  obtain ⟨M₁, R₁, hp⟩ := bddDens_ofReal_of_hasCompactSupport hρc ρ.2.2.1
  obtain ⟨M₂, R₂, hm0⟩ := bddDens_ofReal_of_hasCompactSupport hρc.neg ρ.2.2.1.neg
  have hm : BddDens (fun z => ENNReal.ofReal (-ρ.1 z)) M₂ R₂ := hm0
  obtain ⟨M₃, R₃, hq⟩ := bddDens_ofReal_of_hasCompactSupport hσc σ.2.2.1
  obtain ⟨M₄, R₄, hn0⟩ := bddDens_ofReal_of_hasCompactSupport hσc.neg σ.2.2.1.neg
  have hn : BddDens (fun z => ENNReal.ofReal (-σ.1 z)) M₄ R₄ := hn0
  have hρH : ∀ z ∉ H, ρ.1 z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (ρ.2.2.2 h)
  have hσH : ∀ z ∉ H, σ.1 z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (σ.2.2.2 h)
  have z1 : ∀ z ∉ H, ENNReal.ofReal (ρ.1 z) = 0 := fun z hz => by simp [hρH z hz]
  have z2 : ∀ z ∉ H, ENNReal.ofReal (-ρ.1 z) = 0 := fun z hz => by simp [hρH z hz]
  have z3 : ∀ z ∉ H, ENNReal.ofReal (σ.1 z) = 0 := fun z hz => by simp [hσH z hz]
  have z4 : ∀ z ∉ H, ENNReal.ofReal (-σ.1 z) = 0 := fun z hz => by simp [hσH z hz]
  have I13 := c5_integral_toReal hW hW0 hp.meas hq.meas z1 z3
    (c5E_lt_top hg hT harea hp hq z1 z3).ne
  have I14 := c5_integral_toReal hW hW0 hp.meas hn.meas z1 z4
    (c5E_lt_top hg hT harea hp hn z1 z4).ne
  have I23 := c5_integral_toReal hW hW0 hm.meas hq.meas z2 z3
    (c5E_lt_top hg hT harea hm hq z2 z3).ne
  have I24 := c5_integral_toReal hW hW0 hm.meas hn.meas z2 z4
    (c5E_lt_top hg hT harea hm hn z2 z4).ne
  -- the covariance side
  have hcov : zeroGFFTestCov (H \ η '' Icc 0 T) ρ.1 σ.1 =
      (c5E W T (fun z => ENNReal.ofReal (ρ.1 z)) fun z => ENNReal.ofReal (σ.1 z)).toReal
      - (c5E W T (fun z => ENNReal.ofReal (ρ.1 z)) fun z => ENNReal.ofReal (-σ.1 z)).toReal
      - (c5E W T (fun z => ENNReal.ofReal (-ρ.1 z)) fun z => ENNReal.ofReal (σ.1 z)).toReal
      + (c5E W T (fun z => ENNReal.ofReal (-ρ.1 z)) fun z =>
          ENNReal.ofReal (-σ.1 z)).toReal := by
    unfold zeroGFFTestCov testMeasPos testMeasNeg
    rw [dualCov_compl_image_eq hg hT harea hp hq z1 z3,
      dualCov_compl_image_eq hg hT harea hp hn z1 z4,
      dualCov_compl_image_eq hg hT harea hm hq z2 z3,
      dualCov_compl_image_eq hg hT harea hm hn z2 z4]
  -- the integral side
  set F : ℂ × ℂ → ℝ := fun q => ρ.1 q.1 * σ.1 q.2 * (c5Vm W T q).toReal with hF
  have hpt : ∀ a b, ρ.1 a * σ.1 b * VT W T a b = F (a, b) := by
    intro a b
    by_cases hab : (a, b) ∈ H ×ˢ H
    · simp only [F, c5Vm, indicator_of_mem hab, VT]
    · rcases not_and_or.1 hab with h | h
      · simp [F, hρH a h]
      · simp [F, hσH b h]
  have hsplit : F = (((fun q : ℂ × ℂ =>
      (ENNReal.ofReal (ρ.1 q.1)).toReal * ((ENNReal.ofReal (σ.1 q.2)).toReal *
        (c5Vm W T q).toReal))
      - (fun q : ℂ × ℂ => (ENNReal.ofReal (ρ.1 q.1)).toReal *
        ((ENNReal.ofReal (-σ.1 q.2)).toReal * (c5Vm W T q).toReal)))
      - (fun q : ℂ × ℂ => (ENNReal.ofReal (-ρ.1 q.1)).toReal *
        ((ENNReal.ofReal (σ.1 q.2)).toReal * (c5Vm W T q).toReal)))
      + (fun q : ℂ × ℂ => (ENNReal.ofReal (-ρ.1 q.1)).toReal *
        ((ENNReal.ofReal (-σ.1 q.2)).toReal * (c5Vm W T q).toReal)) := by
    funext q
    simp only [F, ENNReal.toReal_ofReal', Pi.add_apply, Pi.sub_apply]
    conv_lhs => rw [← max_zero_sub_max_neg_zero_eq_self (ρ.1 q.1),
      ← max_zero_sub_max_neg_zero_eq_self (σ.1 q.2)]
    ring
  have hFint : Integrable F ((volume : Measure ℂ).prod volume) := by
    rw [hsplit]; exact ((I13.1.sub I14.1).sub I23.1).add I24.1
  calc zeroGFFTestCov (H \ η '' Icc 0 T) ρ.1 σ.1 = ∫ q, F q ∂((volume : Measure ℂ).prod volume) := by
        rw [hcov, hsplit, integral_add' ((I13.1.sub I14.1).sub I23.1) I24.1,
          integral_sub' (I13.1.sub I14.1) I23.1, integral_sub' I13.1 I14.1,
          I13.2, I14.2, I23.2, I24.2]
    _ = ∫ a, ∫ b, F (a, b) := integral_prod F hFint
    _ = ∫ a, ∫ b, ρ.1 a * σ.1 b * VT W T a b := by
        congr 1; funext a; congr 1; funext b; exact (hpt a b).symm

/-- **GFF-K3 node C5** (`GFF_K3_BLUEPRINT.md` §3.C, revised by D8/D4 and EXT_PP §B C5′):
almost surely, for all test functions `ρ, σ` supported in `ℍ`,
`zeroGFFTestCov (sleComplement κ B ω T) ρ σ = ∫∫ ρ(a) σ(b) V_T(a,b) da db`, where
`V_T = lim_{t ↑ τ_a ∧ τ_b ∧ T} G_ℍ(f_t a, f_t b)` (AD-4). Unconditional: `hStab` is dropped
(BUB-4 is `bub4Stmt`), `hRS` is `RS.rohdeSchrammTraceGen_of_lt_eight`, AD-2 is
`Thm11Area.ae_volume_sleTrace_eq_zero`. -/
theorem zeroGFFTestCov_sleComplement {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {κ T : ℝ} (hκ : 4 < κ ∧ κ < 8) (hT : 0 < T) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ρ σ : TestFun H, zeroGFFTestCov (sleComplement κ B ω T) ρ.1 σ.1 =
      ∫ a, ∫ b, ρ.1 a * σ.1 b * VT (drive κ B ω) T a b := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  filter_upwards [ae_genTrace hB (by linarith [hκ.1]) hκ.2,
    Thm11Area.ae_volume_sleTrace_eq_zero hB hκ.1 hκ.2] with ω hg harea ρ σ
  have harea' : volume (sleTrace κ B ω '' Icc 0 T ∩ H) = 0 :=
    measure_mono_null (inter_subset_left.trans (image_mono Icc_subset_Ici_self)) harea
  rw [sleComplement, hg.closure_image_eq]
  exact zeroGFFTestCov_compl_image_eq hg hT.le harea' ρ σ

end QuantumZipper.K3
