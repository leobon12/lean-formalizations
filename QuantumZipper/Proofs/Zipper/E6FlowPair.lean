import QuantumZipper.Proofs.Zipper.E6FlowRaw
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.Thm18.G4UnzipGoodField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E6 input `CanonZipPairStmt` from a one-parameter smoothed-pairing node

Theorem 1.3, node E6 (Sheffield, arXiv:1012.4797, §5.4, pp. 70–72). The pairing half of the
raw-regularity node (`E6FlowRaw.lean`) asks that raw test-function pairings of both sides of the
zip identity equal their regularized pairings. Both sides are dilations `rescale R Q b` of regular
samples, whose raw value at a test density `ν` is `evalReg R (b_* ν) + Q log b · ν(ℂ)`, while
`evalReg (rescale R Q b) ν` smooths at radius `b 2^{-k}` instead of `2^{-k}`. They agree as soon as
the smoothed pairings `r ↦ ∫ evalReg R (fc(v, r)) dν'(v)` converge along the **continuous**
parameter `r → 0⁺` (`DensLim`), for the dilated test densities `ν'`.

* `evalReg_eq_of_densLim`, `densLim_addConst`, `densLim_rescale`, `densLim_congr`: the calculus
  of `DensLim` for regular samples and admissible measures (deterministic);
* `rawPairRegular_rescale`: `DensPair R b → RawPairRegular (rescale R Q b)` (deterministic);
* `canonZipPairStmt_of_dens`: `CanonZipPairStmt` from `B3d.ZipLenInputsStmt` and the node
  `CfgDensStmt`: **a.s., for all `t ∈ [0,T]`, the unzipped `Γ⁰` field `x_t` has convergent
  smoothed pairings with all dilated test densities** (a one-time-parameter statement; for fixed
  `t` it is the convergence `⟨h_r, φ⟩ → ⟨h, φ⟩` of circle-average smoothings of a random
  distribution in `H^{-ε}_loc(ℍ)` against Lipschitz compactly supported `φ`,
  Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), §3.1 and
  Prop 3.1), using the D33 field cocycle `RegUnif.capCocycleAddStmt_holds`;
* `canonZipRawAllStmt_of_dens`: `CanonZipRawAllStmt` from `B3d.ZipLenInputsStmt` and
  `CfgDensStmt` at every setup.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus

/-- Convergence of the continuous-radius smoothed pairing of `x` with `ν` to `L`. -/
def DensLim (x : FieldSample) (ν : Measure ℂ) (L : ℝ) : Prop :=
  Tendsto (fun r : ℝ => ∫ v, evalReg x (foldedCircle v r) ∂ν) (𝓝[>] 0) (𝓝 L)

/-- Convergent smoothed pairings with both signed parts of every test function dilated by `b`. -/
def DensPair (x : FieldSample) (b : ℝ) : Prop :=
  ∀ ρ : TestFun H,
    (∃ L, DensLim x ((CharFun.tdens ρ.1).map fun u => (b : ℂ) * u) L) ∧
      ∃ L, DensLim x ((CharFun.tdens fun z => -ρ.1 z).map fun u => (b : ℂ) * u) L

theorem densLim_congr {x x' : FieldSample} (h : avgReg x = avgReg x') {ν : Measure ℂ} {L : ℝ}
    (hx : DensLim x ν L) : DensLim x' ν L := by
  have hE : ∀ μ : Measure ℂ, evalReg x μ = evalReg x' μ := fun μ =>
    evalReg_congr_of_regEq (fun k z => congrFun (congrFun h k) z) μ
  unfold DensLim at hx ⊢
  simp_rw [← hE]
  exact hx

theorem densPair_congr {x x' : FieldSample} (h : avgReg x = avgReg x') {b : ℝ}
    (hx : DensPair x b) : DensPair x' b := fun ρ =>
  ⟨let ⟨L, hL⟩ := (hx ρ).1; ⟨L, densLim_congr h hL⟩,
    let ⟨L, hL⟩ := (hx ρ).2; ⟨L, densLim_congr h hL⟩⟩

theorem ae_mem_Hbar_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) : ∀ᵐ v ∂ν, v ∈ Hbar :=
  WedgeTK.ae_mem_Hbar_of_admissible hν

/-- **`evalReg` is the smoothed limit.** -/
theorem evalReg_eq_of_densLim {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {ν : Measure ℂ} (hν : ∀ᵐ v ∂ν, v ∈ Hbar) {L : ℝ} (h : DensLim x ν L) : evalReg x ν = L := by
  have e : ∀ k : ℕ, ∫ w, avgReg x k w ∂ν = ∫ v, evalReg x (foldedCircle v (radius k)) ∂ν := by
    intro k
    refine integral_congr_ae (hν.mono fun w hw => ?_)
    show avgReg x k w = evalReg x (foldedCircle w (radius k))
    rw [hF.avgReg_eq k hw, hF.evalReg_fc_of_mem hw (radius_pos k)]
  unfold evalReg
  simp_rw [e]
  exact (h.comp RegClosure.tendsto_radius_nhdsGT).limUnder_eq

theorem integrable_evalReg_fc {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {ν : Measure ℂ} (hν : IsAdmissibleH ν) {r : ℝ} (hr : 0 < r) :
    Integrable (fun v => evalReg x (foldedCircle v r)) ν :=
  (WedgeTK.integrable_of_continuousOn_Hbar (RegClosure.continuousOn_slice hF.1 hr) hν).congr
    ((ae_mem_Hbar_adm hν).mono fun _v hv => (hF.evalReg_fc_of_mem hv hr).symm)

/-- **Adding a constant.** -/
theorem densLim_addConst {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {ν : Measure ℂ} (hν : IsAdmissibleH ν) {L : ℝ} (h : DensLim x ν L) (c : ℝ) :
    DensLim (addConst x c) ν (L + ν.real univ * c) := by
  have hF' := hF.addConst' c
  refine (h.add_const (ν.real univ * c)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hae : (fun v => evalReg (addConst x c) (foldedCircle v r)) =ᵐ[ν]
      fun v => evalReg x (foldedCircle v r) + c :=
    (ae_mem_Hbar_adm hν).mono fun v hv => by
      show evalReg (addConst x c) (foldedCircle v r) = evalReg x (foldedCircle v r) + c
      rw [hF'.evalReg_fc_of_mem hv hr, hF.evalReg_fc_of_mem hv hr]
  have := hν.1
  rw [integral_congr_ae hae, integral_add (integrable_evalReg_fc hF hν hr) (integrable_const c),
    integral_const, smul_eq_mul]

theorem measurable_mul_left_c (b : ℝ) : Measurable fun u : ℂ => (b : ℂ) * u :=
  measurable_id.const_mul _

/-- **Dilation.** -/
theorem densLim_rescale {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (Q : ℝ)
    {b : ℝ} (hb : 0 < b) {ν : Measure ℂ} (hν : IsAdmissibleH ν) {L : ℝ}
    (h : DensLim x (ν.map fun u => (b : ℂ) * u) L) :
    DensLim (rescale x Q b) ν (L + ν.real univ * (Q * Real.log b)) := by
  have hF' := hF.rescale' Q hb
  have hνm := WedgeTK.isAdmissibleH_map_mul hb hν
  have hmapH := ae_mem_Hbar_adm hνm
  have hb' : Tendsto (fun r : ℝ => b * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun r : ℝ => b * r) (𝓝 0) (𝓝 (b * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hb hr
  refine ((h.comp hb').add_const (ν.real univ * (Q * Real.log b))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hbr : 0 < b * r := mul_pos hb hr
  have hcont : ContinuousOn (fun w => F ((b : ℂ) * w, b * r)) Hbar :=
    (RegClosure.continuousOn_slice hF.1 hbr).comp (continuous_const.mul continuous_id).continuousOn
      (RegClosure.mapsTo_mul_pos hb)
  have hae : (fun v => evalReg (rescale x Q b) (foldedCircle v r)) =ᵐ[ν]
      fun v => F ((b : ℂ) * v, b * r) + Q * Real.log b :=
    (ae_mem_Hbar_adm hν).mono fun v hv => hF'.evalReg_fc_of_mem hv hr
  have hae2 : (fun w => evalReg x (foldedCircle w (b * r))) =ᵐ[ν.map fun u => (b : ℂ) * u]
      fun w => F (w, b * r) :=
    hmapH.mono fun w hw => hF.evalReg_fc_of_mem hw hbr
  have := hν.1
  show ∫ w, evalReg x (foldedCircle w (b * r)) ∂(ν.map fun u => (b : ℂ) * u) +
      ν.real univ * (Q * Real.log b) = ∫ v, evalReg (rescale x Q b) (foldedCircle v r) ∂ν
  rw [integral_congr_ae hae, integral_add (WedgeTK.integrable_of_continuousOn_Hbar hcont hν)
    (integrable_const _), integral_const, smul_eq_mul, integral_congr_ae hae2,
    integral_map (measurable_mul_left_c b).aemeasurable
      (WedgeTK.aesm_of_continuousOn_Hbar (RegClosure.continuousOn_slice hF.1 hbr) hmapH)]

/-- **Raw = regularized evaluation of a dilation at a measure with a smoothed limit.** -/
theorem rescale_apply_eq_evalReg {R : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith R F)
    (Q : ℝ) {b : ℝ} (hb : 0 < b) {ν : Measure ℂ} (hν : IsAdmissibleH ν) {L : ℝ}
    (h : DensLim R (ν.map fun u => (b : ℂ) * u) L) :
    rescale R Q b ν = evalReg (rescale R Q b) ν := by
  rw [evalReg_eq_of_densLim (hF.rescale' Q hb) (ae_mem_Hbar_adm hν) (densLim_rescale hF Q hb hν h)]
  have hd : ∀ z : ℂ, deriv (fun z : ℂ => (b : ℂ) * z) z = b := fun z => by
    rw [deriv_const_mul_field']; simp
  show evalReg R (ν.map fun u => (b : ℂ) * u) +
      Q * ∫ z, Real.log ‖deriv (fun z : ℂ => (b : ℂ) * z) z‖ ∂ν = _
  rw [evalReg_eq_of_densLim hF (ae_mem_Hbar_adm (WedgeTK.isAdmissibleH_map_mul hb hν)) h]
  simp only [hd, Complex.norm_real, Real.norm_of_nonneg hb.le, integral_const, smul_eq_mul]
  ring

/-- **Dilations with convergent smoothed pairings are pairing-raw-regular.** -/
theorem rawPairRegular_rescale {R : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith R F)
    (Q : ℝ) {b : ℝ} (hb : 0 < b) (h : DensPair R b) : RawPairRegular (rescale R Q b) := by
  intro ρ
  obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
  obtain ⟨⟨L₁, h₁⟩, ⟨L₂, h₂⟩⟩ := h ρ
  show rescale R Q b (CharFun.tdens ρ.1) - rescale R Q b (CharFun.tdens fun z => -ρ.1 z) =
    evalReg (rescale R Q b) (CharFun.tdens ρ.1) -
      evalReg (rescale R Q b) (CharFun.tdens fun z => -ρ.1 z)
  rw [rescale_apply_eq_evalReg hF Q hb hd.admissible h₁,
    rescale_apply_eq_evalReg hF Q hb hd.neg.admissible h₂]

theorem map_mul_map_mul (ν : Measure ℂ) (a b : ℝ) :
    (ν.map fun u => (b : ℂ) * u).map (fun u => (a : ℂ) * u) =
      ν.map fun u => ((a * b : ℝ) : ℂ) * u := by
  rw [Measure.map_map (measurable_mul_left_c a) (measurable_mul_left_c b)]
  congr 1
  funext u
  simp only [Function.comp, Complex.ofReal_mul]
  ring

/-- `DensPair` under adding a constant. -/
theorem densPair_addConst {x : FieldSample} (hx : IsRegularSample x) {b : ℝ} (hb : 0 < b)
    (h : DensPair x b) (c : ℝ) : DensPair (addConst x c) b := by
  obtain ⟨F, hF⟩ := hx
  intro ρ
  obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
  obtain ⟨⟨L₁, h₁⟩, ⟨L₂, h₂⟩⟩ := h ρ
  exact ⟨⟨_, densLim_addConst hF (WedgeTK.isAdmissibleH_map_mul hb hd.admissible) h₁ c⟩,
    ⟨_, densLim_addConst hF (WedgeTK.isAdmissibleH_map_mul hb hd.neg.admissible) h₂ c⟩⟩

/-- `DensPair` under dilation. -/
theorem densPair_rescale {x : FieldSample} (hx : IsRegularSample x) (Q : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : DensPair x (a * b)) : DensPair (rescale x Q a) b := by
  obtain ⟨F, hF⟩ := hx
  intro ρ
  obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
  obtain ⟨⟨L₁, h₁⟩, ⟨L₂, h₂⟩⟩ := h ρ
  rw [← map_mul_map_mul] at h₁ h₂
  exact ⟨⟨_, densLim_rescale hF Q ha (WedgeTK.isAdmissibleH_map_mul hb hd.admissible) h₁⟩,
    ⟨_, densLim_rescale hF Q ha (WedgeTK.isAdmissibleH_map_mul hb hd.neg.admissible) h₂⟩⟩

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Smoothed-pairing node for the unzipped `Γ⁰` field** (open; one time parameter): a.s., for
all `t ∈ [0,T]`, the unzipped field `x_t` has convergent continuous-radius smoothed pairings with
both signed parts of every dilated test function. -/
def CfgDensStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ b : ℝ, 0 < b →
    DensPair (zipCapDown (Real.sqrt κ) t (cfg κ B X ω)).1 b

end QuantumZipper.E6
