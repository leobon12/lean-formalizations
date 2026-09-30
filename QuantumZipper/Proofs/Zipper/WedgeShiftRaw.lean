import QuantumZipper.Proofs.Zipper.WedgeShiftLaw
import QuantumZipper.Proofs.LQG.WedgeMeasCoord
import QuantumZipper.Proofs.GFF.FoldBound

/-!
# WEDGE-SHIFT (3): the re-centring identity on raw folded-circle values

Deterministic core of the node `F1.WedgeShiftRegStmt` (Duplantier–Miller–Sheffield,
arXiv:1409.7055, proof of Prop. 4.7(i), p. 77; Sheffield, arXiv:1012.4797, §1.6: the rescaling
`h ↦ h(b·) + Q log b` shifts the radial part by `-log b` and leaves the lateral part a lateral
part). For a `GoodRad` free sample `x`, `Z = wedgeField (lateralPart x) A Q`, `s ∈ ℝ`,
`b = e^{-s}`, constants `k, c`, and a folded circle `fc(d, r)`:

  `rescale (Z + (k + c)) Q b (fc(d, r)) = (wedgeField (lateralPart (rescale x Q b)) (A(s+·)+c) Q + k) (fc(d, r))`

provided (i) `Z + (k + c)` has raw value equal to its regularized value on `fc(bd, br)` (RC3 on
that circle) and (ii) `radAvgReg x ‖·‖` and `A(−log‖·‖)` are integrable on `fc(bd, br)`
(`raw_rescale_shift`). Hence the node follows from the a.s. versions of (i) and (ii) on all
folded circles (`wedgeShiftRegStmt_of`).

Own elementary computation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1

variable {x : FieldSample} {F : ℂ × ℝ → ℝ}

/-- Semicircle averages about `0` of a rescaled good sample. -/
theorem radAvgReg_rescale_good (hG : WedgeTK.GoodRad x F) (Q : ℝ) {b : ℝ} (hb : 0 < b) {ρ : ℝ}
    (hρ : 0 < ρ) : radAvgReg (rescale x Q b) ρ = radAvgReg x (b * ρ) + Q * Real.log b := by
  rw [hG.radAvgReg_eq (mul_pos hb hρ)]
  have hlim : Tendsto (fun n : ℕ => dyadicRound n ρ + radius n) atTop (𝓝 ρ) := by
    have h1 : Tendsto (fun n : ℕ => dyadicRound n ρ) atTop (𝓝 ρ) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact CircleCont.abs_dyadicRound_sub_le n ρ)
        WedgeTK.tendsto_one_div_two_pow
    have h2 : Tendsto (fun n : ℕ => radius n) atTop (𝓝 0) :=
      tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT
    simpa using h1.add h2
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < dyadicRound n ρ + radius n :=
    hlim.eventually (lt_mem_nhds hρ)
  have hin : Tendsto (fun n : ℕ => ((0 : ℂ), b * (dyadicRound n ρ + radius n))) atTop
      (𝓝[Hbar ×ˢ Ioi 0] ((0 : ℂ), b * ρ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds (hlim.const_mul b),
      hpos.mono fun n hn => ⟨WedgeMeasCoord.zero_mem_Hbar_wm, mul_pos hb hn⟩⟩
  have hF := ((hG.1.1 ((0 : ℂ), b * ρ)
    ⟨WedgeMeasCoord.zero_mem_Hbar_wm, show b * ρ ∈ Ioi 0 from mul_pos hb hρ⟩).tendsto.comp
    hin).add_const (Q * Real.log b)
  have heq : (fun n : ℕ => F ((0 : ℂ), b * (dyadicRound n ρ + radius n)) + Q * Real.log b)
      =ᶠ[atTop] fun n => rescale x Q b (foldedCircle 0 (dyadicRound n ρ + radius n)) := by
    filter_upwards [hpos] with n hn
    rw [WedgeMeasCoord.rescale_fc0 _ Q hb,
      hG.1.evalReg_fc_of_mem WedgeMeasCoord.zero_mem_Hbar_wm (mul_pos hb hn)]
  unfold radAvgReg
  exact (hF.congr' heq).limUnder_eq

/-- Folded circles have no atom at `0`. -/
theorem ae_ne_zero_fc (d : ℂ) {r : ℝ} (hr : 0 < r) : ∀ᵐ u ∂foldedCircle d r, u ≠ 0 := by
  rw [ae_iff]
  simpa using FoldBound.fb_fc_singleton d hr.ne' 0

theorem measurableEmbedding_mul_real {b : ℝ} (hb : 0 < b) :
    MeasurableEmbedding fun u : ℂ => (b : ℂ) * u := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have := (Homeomorph.mulLeft₀ (b : ℂ) hb').measurableEmbedding
  rwa [Homeomorph.coe_mulLeft₀] at this

theorem integral_fc_mul {b : ℝ} (hb : 0 < b) (d : ℂ) (r : ℝ) (g : ℂ → ℝ) :
    ∫ v, g v ∂foldedCircle ((b : ℂ) * d) (b * r) = ∫ u, g ((b : ℂ) * u) ∂foldedCircle d r := by
  rw [← WedgeTK.fc_map_mul d r hb, (measurableEmbedding_mul_real hb).integral_map]

theorem integrable_fc_mul {b : ℝ} (hb : 0 < b) (d : ℂ) (r : ℝ) {g : ℂ → ℝ}
    (hg : Integrable g (foldedCircle ((b : ℂ) * d) (b * r))) :
    Integrable (fun u => g ((b : ℂ) * u)) (foldedCircle d r) := by
  rw [← WedgeTK.fc_map_mul d r hb, (measurableEmbedding_mul_real hb).integrable_map_iff] at hg
  exact hg

theorem norm_mul_real {b : ℝ} (hb : 0 < b) (u : ℂ) : ‖(b : ℂ) * u‖ = b * ‖u‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]

/-- **The re-centring identity on one folded circle.** -/
theorem raw_rescale_shift (hG : WedgeTK.GoodRad x F) (A : ℝ → ℝ) (Q s k c : ℝ) (d : ℂ) {r : ℝ}
    (hr : 0 < r)
    (hRC : evalReg (addConst (wedgeField (lateralPart x) A Q) (k + c))
        (foldedCircle ((Real.exp (-s) : ℂ) * d) (Real.exp (-s) * r)) =
      addConst (wedgeField (lateralPart x) A Q) (k + c)
        (foldedCircle ((Real.exp (-s) : ℂ) * d) (Real.exp (-s) * r)))
    (hI1 : Integrable (fun u => radAvgReg x ‖u‖)
      (foldedCircle ((Real.exp (-s) : ℂ) * d) (Real.exp (-s) * r)))
    (hI2 : Integrable (fun u => A (-Real.log ‖u‖))
      (foldedCircle ((Real.exp (-s) : ℂ) * d) (Real.exp (-s) * r))) :
    rescale (addConst (wedgeField (lateralPart x) A Q) (k + c)) Q (Real.exp (-s))
        (foldedCircle d r) =
      addConst (wedgeField (lateralPart (rescale x Q (Real.exp (-s)))) (fun t => A (s + t) + c) Q)
        k (foldedCircle d r) := by
  set b := Real.exp (-s) with hbdef
  have hb : 0 < b := Real.exp_pos _
  have hlogb : Real.log b = -s := Real.log_exp _
  -- the left side
  have hL : rescale (addConst (wedgeField (lateralPart x) A Q) (k + c)) Q b (foldedCircle d r) =
      addConst (wedgeField (lateralPart x) A Q) (k + c) (foldedCircle ((b : ℂ) * d) (b * r)) +
        Q * Real.log b := by
    show evalReg _ ((foldedCircle d r).map fun z => (b : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (b : ℂ) * w) z‖ ∂foldedCircle d r = _
    rw [WedgeTK.fc_map_mul d r hb, integral_log_deriv_mul_const hb, hRC]
    simp
  rw [hL]
  simp only [addConst, wedgeField, lateralPart, measure_univ, ENNReal.toReal_one, mul_one]
  rw [hG.1.evalReg_fc _ (mul_pos hb hr), (hG.1.rescale' Q hb).evalReg_fc d hr,
    RegClosure.foldH_mul_pos _ hb]
  -- the radial average integrals
  have hR1 : ∫ u, radAvgReg x ‖u‖ ∂foldedCircle ((b : ℂ) * d) (b * r) =
      ∫ u, radAvgReg x (b * ‖u‖) ∂foldedCircle d r := by
    rw [integral_fc_mul hb]
    simp only [norm_mul_real hb]
  have hI1' : Integrable (fun u => radAvgReg x (b * ‖u‖)) (foldedCircle d r) := by
    have := integrable_fc_mul hb d r hI1
    simpa only [norm_mul_real hb] using this
  have hR2 : ∫ u, radAvgReg (rescale x Q b) ‖u‖ ∂foldedCircle d r =
      ∫ u, radAvgReg x (b * ‖u‖) ∂foldedCircle d r + Q * Real.log b := by
    rw [integral_congr_ae ((ae_ne_zero_fc d hr).mono fun u hu =>
        radAvgReg_rescale_good hG Q hb (norm_pos_iff.2 hu)),
      integral_add hI1' (integrable_const _)]
    simp
  -- the radial profile integrals
  set P : ℂ → ℝ := fun u => Q * -Real.log ‖u‖ + A (s + -Real.log ‖u‖) with hP
  have hlog : ∀ u : ℂ, u ≠ 0 → -Real.log (b * ‖u‖) = s + -Real.log ‖u‖ := fun u hu => by
    rw [Real.log_mul hb.ne' (norm_ne_zero_iff.2 hu), hlogb]; ring
  have hP1 : ∫ u, (Q * -Real.log ‖u‖ + A (-Real.log ‖u‖))
      ∂foldedCircle ((b : ℂ) * d) (b * r) = ∫ u, (P u + Q * s) ∂foldedCircle d r := by
    rw [integral_fc_mul hb (g := fun v => Q * -Real.log ‖v‖ + A (-Real.log ‖v‖))]
    refine integral_congr_ae ((ae_ne_zero_fc d hr).mono fun u hu => ?_)
    show Q * -Real.log ‖(b : ℂ) * u‖ + A (-Real.log ‖(b : ℂ) * u‖) = P u + Q * s
    rw [norm_mul_real hb, hlog u hu, hP]
    ring
  have hPint : Integrable P (foldedCircle d r) := by
    have h : Integrable (fun u => Q * -Real.log ‖(b : ℂ) * u‖ + A (-Real.log ‖(b : ℂ) * u‖))
        (foldedCircle d r) :=
      integrable_fc_mul hb d r (g := fun v => Q * -Real.log ‖v‖ + A (-Real.log ‖v‖))
        ((WedgeCan.integrable_logProfile_foldedCircle Q _ _).add hI2)
    refine (h.sub (integrable_const (Q * s))).congr
      ((ae_ne_zero_fc d hr).mono fun u hu => ?_)
    show Q * -Real.log ‖(b : ℂ) * u‖ + A (-Real.log ‖(b : ℂ) * u‖) - Q * s = P u
    rw [norm_mul_real hb, hlog u hu, hP]
    ring
  have hc' : ∫ u, (P u + c) ∂foldedCircle d r = ∫ u, P u ∂foldedCircle d r + c := by
    rw [integral_add hPint (integrable_const c)]
    simp
  have hc'' : ∫ u, (P u + Q * s) ∂foldedCircle d r = ∫ u, P u ∂foldedCircle d r + Q * s := by
    rw [integral_add hPint (integrable_const _)]
    simp
  have hP2 : ∫ u, (Q * -Real.log ‖u‖ + (A (s + -Real.log ‖u‖) + c)) ∂foldedCircle d r =
      ∫ u, P u ∂foldedCircle d r + c := by
    rw [← hc']
    exact integral_congr_ae (ae_of_all _ fun u => by simp only [hP]; ring)
  rw [hR1, hR2, hP1, hP2, hc'', hlogb]
  ring

/-- RC3 passes to `y + k` for a regular `y`. -/
theorem evalReg_addConst_fc_of {y : FieldSample} {G : ℂ × ℝ → ℝ} (hG : IsRegularWith y G)
    {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hrc : evalReg y (foldedCircle w ρ) = y (foldedCircle w ρ))
    (k : ℝ) : evalReg (addConst y k) (foldedCircle w ρ) = addConst y k (foldedCircle w ρ) := by
  rw [(hG.addConst' k).evalReg_fc w hρ, ← hG.evalReg_fc w hρ, hrc]
  simp [addConst]

/-! ## The node from RC3 and integrability on all folded circles -/

/-- **Sub-node (RC3 for the wedge field on every folded circle).** A.s. the raw value of the wedge
field on every folded circle is its regularized value. -/
def WedgeRC3AllStmt (γ α : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ), IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', ∀ (w : ℂ) (ρ : ℝ), 0 < ρ →
      evalReg (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) (foldedCircle w ρ) =
        wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ) (foldedCircle w ρ)

/-- **Sub-node (integrability of the radial pieces on every folded circle).** -/
def WedgeCircleIntStmt (γ α : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ), IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', ∀ (w : ℂ) (ρ : ℝ), 0 < ρ →
      Integrable (fun u => radAvgReg (X ω) ‖u‖) (foldedCircle w ρ) ∧
        Integrable (fun u => A (-Real.log ‖u‖) ω) (foldedCircle w ρ)

/-- **The re-centring node from the two sub-nodes.** -/
theorem wedgeShiftRegStmt_of {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (hRC : WedgeRC3AllStmt γ α) (hInt : WedgeCircleIntStmt γ α) : WedgeShiftRegStmt γ α := by
  intro Ω' _ P' _ X A hX hA hI
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [hG.ae_good, LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A inferInstance
    hX hA hI, hRC P' X A hX hA hI, hInt P' X A hX hA hI] with ω hg hZ hrc hint s k c j z
  obtain ⟨FW, hFW⟩ := hZ.1
  have hpos : 0 < Real.exp (-s) * radius j := mul_pos (Real.exp_pos _) (radius_pos j)
  unfold avgReg
  congr 1
  funext n
  exact raw_rescale_shift hg (fun t => A t ω) (Qc γ) s k c _ (radius_pos j)
    (evalReg_addConst_fc_of hFW hpos (hrc _ _ hpos) (k + c)) (hint _ _ hpos).1 (hint _ _ hpos).2

/-- **Field-level B4(c) from the two sub-nodes.** -/
theorem wedgeAddConstLawStmt_of_rc3
    (hRC : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeRC3AllStmt γ α)
    (hInt : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeCircleIntStmt γ α) :
    WedgeAddConstLawStmt :=
  wedgeAddConstLawStmt_of_reg fun γ α hγ hγ2 hα =>
    wedgeShiftRegStmt_of hγ hγ2 hα (hRC γ α hγ hγ2 hα) (hInt γ α hγ hγ2 hα)

end F1
end QuantumZipper
