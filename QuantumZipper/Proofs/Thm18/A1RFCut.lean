import QuantumZipper.Proofs.Thm18.A1RGWire
import QuantumZipper.Proofs.Thm18.A1R2Far
import QuantumZipper.Proofs.Zipper.XPCMeas
import QuantumZipper.Proofs.Thm18.RTBeurMass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RF (1): the far node at the open-arc unzipping time, from the full smoothing of `Y`

Decision D90 and its addendum; orchestrator note of 2026-09-29 (the A1b chain reads the far node
only at `t = lenTimeArc γ ℓ c₀`, `A1RG.ae_sideRTXArc`).

`A1R2FarYStmt` integrates the pulled-back smoothings `E(ρ, z) = evalReg Y ((f_t⁻¹)_* fc(z, ρ))`
over the far part `{Im z > √ρ}` of the pushed side circle `μ = (f_t ∘ ψ)_* fc(d, s)`. The sharp
cut-off is not a continuous family of measures, so it cannot be fed to the Kolmogorov engine
(`G1RC.exists_smoothing_joint`), and removing it needs log growth near `ℝ`. At the single time
`t = lenTimeArc` that growth is proved (`A1RG.ae_arcGrowthNear`, open-arc E6 transfer). Hence:

* `A1RFFullYStmt` (open): the full smoothings `∫ E(ρ, z) dμ(z)` (fixed radius `ρ`, all `z`,
  folded circles, all `t > 0`) converge to `evalReg Y ((f_t⁻¹)_* μ)`. This is the continuum limit
  of Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1, for the continuous family of
  measures `(t, d, s, ρ) ↦ ∫ (f_t⁻¹)_* fc(z, ρ) dμ(z)`; no cut-off, no log-derivative term.
* `A1RF.tendsto_far_of_full`: full limit + log growth on the cut set + small mass ⇒ far limit
  (the converse direction of `A1R.tendsto_integral_of_cutoff`; the far part need not be
  integrable, since both Bochner integrals vanish otherwise). "Junk × small mass",
  Berestycki–Powell arXiv:2404.16642 Thm 8.16, Rem 8.10.
* `A1RF.ae_farArc : A1RFFullYStmt → (far limit of every witness of U_{lenTimeArc}, a.s.)`: on the
  cut set `E = F − Q ∫ log|(f_t⁻¹)'| dfc` (all-time RC3, `a1r2_ae_exactAll`), bounded by the arc
  growth of `F` and the log-derivative bound `A1R2.abs_integral_log_deriv_le`; mass from
  `a1rMassStmt_holds`; the rest is the proof of `a1rFarStmt_of_farY`.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- **The far node without cut-off** (open): the full pulled-back smoothings at radius `ρ`
converge along every pushed side circle, for all times. -/
def A1RFFullYStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ᵐ ω ∂P,
      ∀ t : ℝ, 0 < t → ∀ d ∈ Hbar, ∀ s : ℝ, 0 < s →
        Tendsto (fun ρ => ∫ z, evalReg (Y ω)
            ((foldedCircle z ρ).map (fwdMapInv (drive (γ ^ 2) B ω) t))
              ∂a1rMu (drive (γ ^ 2) B ω) t left d s)
          (𝓝[>] 0) (𝓝 (evalReg (Y ω)
            ((a1rMu (drive (γ ^ 2) B ω) t left d s).map (fwdMapInv (drive (γ ^ 2) B ω) t))))

namespace A1RF

/-- Measurability of the pulled-back smoothings. -/
theorem measurable_evalReg_fcmap (x : FieldSample) {g : ℂ → ℂ} (hg : Measurable g) (ρ : ℝ) :
    Measurable fun z : ℂ => evalReg x ((foldedCircle z ρ).map g) := by
  have e : ∀ z : ℂ, (foldedCircle z ρ).map g =
      E6.XAreaPC.angMeas.map (fun θ => g (foldH (circleMap z ρ θ))) := by
    intro z
    rw [E6.XAreaPC.foldedCircle_eq_map_angMeas]
    exact Measure.map_map hg (measurable_foldH.comp (measurable_circleMap _ _))
  simp_rw [e]
  have hc : Continuous fun p : ℂ × ℝ => circleMap p.1 ρ p.2 := by
    unfold circleMap
    fun_prop
  exact E6.XAreaPC.measurable_evalReg_map_gen (y := fun _ : ℂ => x) measurable_const
    (ψ := fun z θ => g (foldH (circleMap z ρ θ)))
    (hg.comp (measurable_foldH.comp hc.measurable)) E6.XAreaPC.angMeas

/-- **Far limit from the full limit** (log growth on the cut set, small mass). -/
theorem tendsto_far_of_full {μ : Measure ℂ} [IsFiniteMeasure μ] {f : ℝ → ℂ → ℝ}
    {L C Cm β : ℝ} (hβ : 0 < β) (hC : 0 ≤ C) (N : ℝ → Set ℂ) (hNm : ∀ ρ, MeasurableSet (N ρ))
    (hm : ∀ ρ, AEStronglyMeasurable (f ρ) μ)
    (hgr : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ᵐ z ∂μ, z ∈ N ρ → |f ρ z| ≤ C * (1 + |Real.log ρ|))
    (hmass : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → μ.real (N ρ) ≤ Cm * ρ ^ β)
    (hfull : Tendsto (fun ρ => ∫ z, f ρ z ∂μ) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ρ => ∫ z in (N ρ)ᶜ, f ρ z ∂μ) (𝓝[>] 0) (𝓝 L) := by
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ < 1 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  have hD : Tendsto (fun ρ => (∫ z in (N ρ)ᶜ, f ρ z ∂μ) - ∫ z, f ρ z ∂μ) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (A1R.tendsto_logGrowth_mul_rpow (C := C) (Cm := Cm) hβ)
    filter_upwards [hev] with ρ ⟨h0, h1⟩
    have hlog : |Real.log ρ| = -Real.log ρ := abs_of_nonpos (Real.log_nonpos h0.le h1.le)
    have hbd : ∀ᵐ z ∂μ.restrict (N ρ), ‖f ρ z‖ ≤ C * (1 + |Real.log ρ|) := by
      rw [ae_restrict_iff' (hNm ρ)]
      filter_upwards [hgr ρ h0 h1] with z hz hzN
      rw [Real.norm_eq_abs]; exact hz hzN
    have hb := norm_setIntegral_le_of_norm_le_const_ae' (f := f ρ) (measure_lt_top μ (N ρ))
      ((hgr ρ h0 h1).mono fun z hz hzN => by rw [Real.norm_eq_abs]; exact hz hzN)
    have hK : 0 ≤ C * (1 + |Real.log ρ|) := mul_nonneg hC (by positivity)
    have hNi : IntegrableOn (f ρ) (N ρ) μ :=
      Integrable.mono' (integrable_const (C * (1 + |Real.log ρ|))) (hm ρ).restrict hbd
    have hmain : ‖(∫ z in (N ρ)ᶜ, f ρ z ∂μ) - ∫ z, f ρ z ∂μ‖ ≤ ‖∫ z in N ρ, f ρ z ∂μ‖ := by
      by_cases hint : Integrable (f ρ) μ
      · rw [← integral_add_compl (hNm ρ) hint,
          show ∀ a b : ℝ, a - (b + a) = -b by intros; ring, norm_neg]
      · have hfar' : ¬ IntegrableOn (f ρ) (N ρ)ᶜ μ := fun h => hint (by
          have := hNi.union h
          rwa [union_compl_self, integrableOn_univ] at this)
        rw [integral_undef hfar', integral_undef hint, sub_zero, norm_zero]
        exact norm_nonneg _
    calc _ ≤ ‖∫ z in N ρ, f ρ z ∂μ‖ := hmain
      _ ≤ C * (1 + |Real.log ρ|) * μ.real (N ρ) := hb
      _ ≤ C * (1 + |Real.log ρ|) * (Cm * ρ ^ β) := mul_le_mul_of_nonneg_left (hmass ρ h0 h1) hK
      _ = C * Cm * (ρ ^ β - Real.log ρ * ρ ^ β) := by rw [hlog]; ring
  have h2 := hfull.add hD
  rw [add_zero] at h2
  exact h2.congr fun ρ => by ring

/-- **The far node at the open-arc unzipping time**, from the full smoothing node. -/
theorem ae_farArc (hFull : A1RFFullYStmt) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (left : Bool) :
    ∀ᵐ ω ∂P, 0 < unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) → ∀ F : ℂ × ℝ → ℝ,
      IsRegularWith (coordChange (Y ω) (fwdMapInv (drive (γ ^ 2) B ω)
        (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))) (Qc γ)) F →
      ∀ d ∈ Hbar, ∀ s : ℝ, 0 < s →
        Tendsto (fun ρ => ∫ z in (a1rNear ρ)ᶜ, F (z, ρ)
            ∂a1rMu (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (wedgeConfig γ B Y ω)) left d s)
          (𝓝[>] 0) (𝓝 (coordChange (Y ω) (fwdMapInv (drive (γ ^ 2) B ω)
            (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))) (Qc γ)
            (a1rMu (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (wedgeConfig γ B Y ω)) left d s))) := by
  filter_upwards [hFull γ P B Y hS hIn left, a1r2_ae_exactAll hS, ae_g1zDrvGood hS hIn,
    A1RG.ae_arcGrowthNear hS hIn hℓ, ae_lenTimeArc_pos hS hIn hℓ]
    with ω hfull hex hG hgr ht ha F hF d hd s hs
  set t := lenTimeArc γ ℓ (wedgeConfig γ B Y ω) with htdef
  set W := drive (γ ^ 2) B ω with hWdef
  set μ := a1rMu W t left d s with hμ
  set lg : ℂ → ℝ := fun z => Real.log ‖deriv (fwdMapInv W t) z‖ with hlg
  set E : ℝ → ℂ → ℝ := fun ρ z => evalReg (Y ω) ((foldedCircle z ρ).map (fwdMapInv W t))
    with hE
  -- the far limit of the `Y`-part
  have hEfar : Tendsto (fun ρ => ∫ z in (a1rNear ρ)ᶜ, E ρ z ∂μ) (𝓝[>] 0)
      (𝓝 (evalReg (Y ω) (μ.map (fwdMapInv W t)))) := by
    obtain ⟨Rr, hsupp⟩ := A1R.exists_ae_bdd_a1rMu hG ht left d hs
    obtain ⟨C, hC, hCb⟩ := hgr ha F hF Rr
    obtain ⟨K, hK, hKb⟩ := A1R2.abs_integral_log_deriv_le hG ht Rr
    obtain ⟨Cm, β, hβ, hmass⟩ := a1rMassStmt_holds W hG t ht left d hd s hs
    refine tendsto_far_of_full (half_pos hβ) (C := C + |Qc γ| * K) (Cm := Cm) (by positivity)
      a1rNear A1R.measurableSet_a1rNear
      (fun ρ => (measurable_evalReg_fcmap (Y ω)
        (RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le) ρ).aestronglyMeasurable)
      ?_ ?_ (hfull t ht d hd s hs)
    · intro ρ hρ hρ1
      filter_upwards [hsupp] with z hz hzN
      have e1 := hF.evalReg_fc_of_mem hz.1 hρ
      have e2 := hex t ht.le z hz.1 ρ hρ
      change evalReg (coordChange (Y ω) (fwdMapInv W t) (Qc γ)) (foldedCircle z ρ) =
        coordChange (Y ω) (fwdMapInv W t) (Qc γ) (foldedCircle z ρ) at e2
      have hFE : F (z, ρ) = E ρ z + Qc γ * ∫ u, lg u ∂foldedCircle z ρ := by
        rw [← e1, e2]; rfl
      have h1 := hCb ρ hρ hρ1 z hz.1 hz.2 hzN
      have h2 := hKb z hz.1 hz.2 ρ hρ hρ1 hzN
      have e3 : E ρ z = F (z, ρ) - Qc γ * ∫ u, lg u ∂foldedCircle z ρ := by rw [hFE]; ring
      rw [e3]
      calc |F (z, ρ) - Qc γ * ∫ u, lg u ∂foldedCircle z ρ|
          ≤ |F (z, ρ)| + |Qc γ| * |∫ u, lg u ∂foldedCircle z ρ| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ C * (1 + |Real.log ρ|) + |Qc γ| * (K * (1 + |Real.log ρ|)) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
        _ = (C + |Qc γ| * K) * (1 + |Real.log ρ|) := by ring
    · intro ρ hρ hρ1
      have h1 : Real.sqrt ρ < 1 := by
        rw [Real.sqrt_lt' one_pos]; simpa using hρ1
      have := hmass (Real.sqrt ρ) (Real.sqrt_pos.2 hρ) h1
      rwa [A1R.sqrt_rpow_eq hρ.le] at this
  -- the rest is the proof of `a1rFarStmt_of_farY`
  obtain ⟨L, hlgint, -⟩ := A1R2.integrable_log_deriv_a1rMu hG ht left d hs
  have hμH := A1R2.ae_mem_H_a1rMu hG ht left d hs
  have hWc := hG.1
  have hW0 := hG.2.1
  have hlgm : Measurable lg := Real.measurable_log.comp (measurable_deriv _).norm
  -- the witness on the far part
  have hpt : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ z ∈ H, z ∈ (a1rNear ρ)ᶜ →
      F (z, ρ) = E ρ z + Qc γ * lg z := by
    intro ρ hρ hρ1 z hz hzN
    have hzN' : Real.sqrt ρ < z.im := by
      simp only [a1rNear, mem_compl_iff, mem_ofPred_eq, not_le] at hzN; exact hzN
    have hρs : ρ < Real.sqrt ρ := by
      have h1 : Real.sqrt ρ < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hρ1
      have h2 := Real.mul_self_sqrt hρ.le
      have h3 : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
      nlinarith
    have hzH : z ∈ Hbar := le_of_lt (show 0 < z.im from hz)
    rw [← hF.evalReg_fc_of_mem hzH hρ]
    have e2 := hex t ht.le z hzH ρ hρ
    change evalReg (coordChange (Y ω) (fwdMapInv W t) (Qc γ)) (foldedCircle z ρ) =
      coordChange (Y ω) (fwdMapInv W t) (Qc γ) (foldedCircle z ρ) at e2
    rw [e2]
    show evalReg (Y ω) ((foldedCircle z ρ).map (fwdMapInv W t)) +
      Qc γ * ∫ u, Real.log ‖deriv (fwdMapInv W t) u‖ ∂foldedCircle z ρ = _
    rw [A1R2.integral_log_deriv_fc_eq hWc hW0 ht.le hρ (hρs.trans hzN')]
  -- the splitting of the far integral
  have hsplit : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∫ z in (a1rNear ρ)ᶜ, F (z, ρ) ∂μ =
      ∫ z in (a1rNear ρ)ᶜ, E ρ z ∂μ + Qc γ * ∫ z in (a1rNear ρ)ᶜ, lg z ∂μ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ρ ⟨hρ, hρ1⟩
    have hNm : MeasurableSet (a1rNear ρ)ᶜ := (A1R.measurableSet_a1rNear ρ).compl
    have hFi : IntegrableOn (fun z => F (z, ρ)) (a1rNear ρ)ᶜ μ :=
      (G1A1b.integrable_sideFamily hG ht left hF.1 d hs hρ).integrableOn
    have hlgi : IntegrableOn lg (a1rNear ρ)ᶜ μ := hlgint.integrableOn
    have hEF : ∫ z in (a1rNear ρ)ᶜ, E ρ z ∂μ =
        ∫ z in (a1rNear ρ)ᶜ, (F (z, ρ) - Qc γ * lg z) ∂μ := by
      refine setIntegral_congr_ae hNm ?_
      filter_upwards [hμH] with z hz hzN
      rw [hpt ρ hρ hρ1 z hz hzN]; ring
    rw [hEF, integral_sub hFi (hlgi.const_mul _), integral_const_mul]
    ring
  -- dominated convergence for the log-derivative part
  have hlglim : Tendsto (fun ρ => ∫ z in (a1rNear ρ)ᶜ, lg z ∂μ) (𝓝[>] 0) (𝓝 (∫ z, lg z ∂μ)) := by
    have e : (fun ρ => ∫ z in (a1rNear ρ)ᶜ, lg z ∂μ) =
        fun ρ => ∫ z, (a1rNear ρ)ᶜ.indicator lg z ∂μ := by
      funext ρ
      rw [integral_indicator (A1R.measurableSet_a1rNear ρ).compl]
    rw [e]
    refine tendsto_integral_filter_of_dominated_convergence (fun z => |lg z|)
      (Eventually.of_forall fun ρ =>
        (hlgm.indicator (A1R.measurableSet_a1rNear ρ).compl).aestronglyMeasurable)
      (Eventually.of_forall fun ρ => Eventually.of_forall fun z => ?_) hlgint.abs ?_
    · rw [Real.norm_eq_abs]
      by_cases hz : z ∈ (a1rNear ρ)ᶜ
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, abs_zero]; exact abs_nonneg _
    · filter_upwards [hμH] with z hz
      have hz' : 0 < z.im := hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < z.im ^ 2 by positivity)] with ρ ⟨hρ, hρz⟩
      have hmem : z ∈ (a1rNear ρ)ᶜ := by
        simp only [a1rNear, mem_compl_iff, mem_ofPred_eq, not_le]
        rw [Real.sqrt_lt' hz']
        exact hρz
      rw [indicator_of_mem hmem]
  have hlim := hEfar.add (hlglim.const_mul (Qc γ))
  refine (hlim.congr' (hsplit.mono fun ρ h => h.symm)).trans (le_of_eq ?_)
  rfl

end A1RF

end R18
end QuantumZipper
