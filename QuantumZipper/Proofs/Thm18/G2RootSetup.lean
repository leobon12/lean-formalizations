import QuantumZipper.Proofs.Thm18.G2RootRModel
import QuantumZipper.Proofs.Section5.Prop17PalmCMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2: the D3⁺ setup at a fixed point of the Palm field

For the model nodes `G2RootXModelStmt`, `G2RootRModelStmt` the D3⁺ data at a fixed point
`x ≠ 0`, `|x| < 1`, are (as in Proposition 1.7's `palmC_setup`, `Prop17PalmCMain.lean`):
`X' = palmCField X₀ x` (the free field translated by `x`), `ρ₀ = palmCRho refS x` (the reference
semicircle translated by `−x`), `α = γ`, trivial `Ξ`, and the deterministic correction

  `g2Corr γ x z = 𝔥₀(z + x) − (γ/2) k_S(z + x) − ∫ ψ_x dS`,

so that on probability measures `zoomField γ C (normField (X₀ + ψ_x)) x` is
`zoomModel γ γ C ρ₀ X' g2Corr` (the Palm shift `ψ_x(z + x) = γ(−log‖z‖) − (γ/2) k_S(z + x)`;
Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25). Near `0`, `k_S(· + x) = 0`
(`kPot_refS_eq`) and `g2Corr ∘ foldH = (2/γ) log‖· + x‖ − const` is harmonic.

* `g2Root_setup`: `D3Plus.Setup γ γ r (palmCRho refS x) P (palmCField X₀ x) () (g2Corr γ x)` for
  `0 < r < |x|`, `|x| + r < 1`.

Own elementary proof (AGENT_GUIDE cost rule), following `palmC_setup`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw

local notation "Ω₀" => gffBase.Ω

/-- The deterministic D3⁺ correction at `x`. -/
def g2Corr (γ x : ℝ) (z : ℂ) : ℝ :=
  h0rev (γ ^ 2) (z + x) - γ / 2 * PalmNorm.kPot refS (z + x) - ∫ u, g2PalmPsi γ x u ∂refS

theorem norm_foldH_add_real (w : ℂ) (x : ℝ) : ‖foldH w + (x : ℂ)‖ = ‖w + (x : ℂ)‖ := by
  unfold foldH
  split_ifs
  · rfl
  · rw [show (starRingEnd ℂ) w + (x : ℂ) = (starRingEnd ℂ) (w + (x : ℂ)) by
      rw [map_add, Complex.conj_ofReal], Complex.norm_conj]

/-- **The D3⁺ setup at a fixed point of the Palm field.** -/
theorem g2Root_setup {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {x r : ℝ} (hr : 0 < r)
    (hxr : r < |x|) (hx1 : |x| + r < 1) :
    D3Plus.Setup γ γ r (palmCRho refS x) gffBase.P (palmCField gffBase.X x)
      (fun _ : Ω₀ => ()) (fun _ => g2Corr γ x) := by
  have hxn : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  exact
    { hγ := hγ
      hγ2 := hγ2
      hα := gamma_lt_Qc' hγ hγ2
      hr := hr
      hX := isFreeGFFModConstH_translate gffBase.gff x
      hΞ := measurable_const
      hind := by
        rw [MeasurableSpace.comap_const]
        exact indep_bot_left _
      hρ := isAdmissibleH_map_add_real
        (isAdmissibleH_foldedCircle (by simp [Hbar]) (by norm_num)) (-x)
      hρ1 := by rw [palmCRho, map_add_real_univ, measure_univ]
      hρB := by
        rw [palmCRho, Measure.map_apply (measurable_add_const _) measurableSet_ball]
        refine measure_mono_null (fun z hz => ?_)
          (LateralGerm.foldedCircle_ball_eq_zero (s := 1) (δ := |x| + r) (by positivity)
            hx1.le)
        simp only [mem_preimage, mem_ball, dist_zero_right] at hz ⊢
        calc ‖z‖ = ‖(z + ((-x : ℝ) : ℂ)) + (x : ℂ)‖ := by push_cast; ring_nf
          _ ≤ ‖z + ((-x : ℝ) : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
          _ < |x| + r := by rw [hxn]; linarith
      harm := fun _ z hz => by
        rw [mem_ball, dist_zero_right] at hz
        set c : ℝ := ∫ u, g2PalmPsi γ x u ∂refS with hc
        have hev : (fun w => g2Corr γ x (foldH w)) =ᶠ[𝓝 z]
            fun w => (2 / Real.sqrt (γ ^ 2)) * Real.log ‖w + (x : ℂ)‖ - c := by
          filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
          rw [mem_ball, dist_zero_right] at hw
          have hle : ‖foldH w + (x : ℂ)‖ ≤ 1 := by
            rw [norm_foldH_add_real]
            exact (norm_add_le _ _).trans (by rw [hxn]; linarith)
          have hk : PalmNorm.kPot refS (foldH w + (x : ℂ)) = 0 := by
            rw [show refS = foldedCircle 0 1 from rfl, kPot_refS_eq]
            have hp : Real.posLog ‖foldH w + (x : ℂ)‖ = 0 :=
              max_eq_left (Real.log_nonpos (norm_nonneg _) hle)
            rw [hp, mul_zero]
          simp only [g2Corr, hk, mul_zero, sub_zero]
          rw [show h0rev (γ ^ 2) (foldH w + (x : ℂ)) =
            2 / Real.sqrt (γ ^ 2) * Real.log ‖foldH w + (x : ℂ)‖ from rfl, norm_foldH_add_real]
        refine (InnerProductSpace.harmonicAt_congr_nhds hev).2 ?_
        have hne : z + (x : ℂ) ≠ 0 := by
          intro h
          have e : (x : ℂ) = -z := by linear_combination h
          have : ‖(x : ℂ)‖ = ‖z‖ := by rw [e, norm_neg]
          rw [hxn] at this
          linarith
        have hlog := AnalyticAt.harmonicAt_log_norm (f := fun w => w + (x : ℂ))
          (analyticAt_id.add analyticAt_const) hne
        have h2 := (hlog.const_smul (c := 2 / Real.sqrt (γ ^ 2))).sub
          (InnerProductSpace.harmonicAt_const (x := z) c)
        convert h2 using 1
        funext w
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      gmeas := fun _ => measurable_const }

/-! ## The identification nodes (concrete D3⁺ data) -/

/-- **Identification node, `x` side** (the model node `G2RootXModelStmt` with the concrete D3⁺
data of `g2Root_setup`, radius `κ/2`; pattern of `Prop17PalmCAgreeStmt`): a wedge `Y'`, a radius
`R` and a local set `S` carrying the `μ`-mass of `s`; the conditioning variables are a.s. equal to
a `condSigma`-measurable map; the model data are a.e.-measurable and agree with the cylinder event
of the zoom except on an event of probability `→ 0` as `C → ∞` (Sheffield, arXiv:1012.4797, proof
of Prop. 1.6, p. 25). -/
def G2RootXAgreeStmt (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ x : ℝ,
    (∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η ∧ |x - i₀.t₁| + m < i₀.r₁) →
    ∃ (R : ℕ) (S : Set ((ℕ → ℝ) × (TestFun H → ℝ))) (Ω' : Type) (_ : MeasurableSpace Ω')
      (P' : Measure Ω') (Y' : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ Y' P' ∧ MeasurableSet S ∧
      ∫⁻ ω', S.indicator 1 (D3Plus.locFieldFull R (Y' ω')) ∂P' = ENNReal.ofReal (μ.real s) ∧
      (∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η → ∃ V : Ω₀ → (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ,
        Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)] V ∧
        ∀ᵐ ω ∂gffBase.P, V ω = g3PalmCond γ i κ x ω) ∧
      (∀ C : ℝ, AEMeasurable (g3ModelData γ (κ / 2) C (palmCRho refS x) R
        (palmCField gffBase.X x) (fun _ => g2Corr γ x)) gffBase.P) ∧
      Tendsto (fun C : ℝ => gffBase.P {ω | ¬ (zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ↔
        g3ModelData γ (κ / 2) C (palmCRho refS x) R (palmCField gffBase.X x)
          (fun _ => g2Corr γ x) ω ∈ S)}) atTop (𝓝 0)

/-- **Identification node, `R` side** (as `G2RootXAgreeStmt`, at `y` in region 2, with the
conditioning variables `g3PalmCondR`). -/
def G2RootRAgreeStmt (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ x : ℝ,
    (∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η ∧ |x - i₀.t₂| + m < i₀.r₂) →
    ∃ (R : ℕ) (S : Set ((ℕ → ℝ) × (TestFun H → ℝ))) (Ω' : Type) (_ : MeasurableSpace Ω')
      (P' : Measure Ω') (Y' : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ Y' P' ∧ MeasurableSet S ∧
      ∫⁻ ω', S.indicator 1 (D3Plus.locFieldFull R (Y' ω')) ∂P' = ENNReal.ofReal (μ.real s) ∧
      (∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η → ∃ V : Ω₀ → CondR i,
        Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)] V ∧
        ∀ᵐ ω ∂gffBase.P, V ω = g3PalmCondR γ i κ x ω) ∧
      (∀ C : ℝ, AEMeasurable (g3ModelData γ (κ / 2) C (palmCRho refS x) R
        (palmCField gffBase.X x) (fun _ => g2Corr γ x)) gffBase.P) ∧
      Tendsto (fun C : ℝ => gffBase.P {ω | ¬ (zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ↔
        g3ModelData γ (κ / 2) C (palmCRho refS x) R (palmCField gffBase.X x)
          (fun _ => g2Corr γ x) ω ∈ S)}) atTop (𝓝 0)

theorem g2RootXModelStmt_of_agree {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Measure LawD}
    (h : G2RootXAgreeStmt γ μ) : G2RootXModelStmt γ μ := by
  intro s hs δ η m κ hκ hκm x hx
  obtain ⟨R, S, Ω', _, P', Y', hP', hW, hS, hμ, hV, hMdl, hlim⟩ :=
    h s hs δ η m κ hκ hκm x hx
  obtain ⟨i₀, -, -, hx₀⟩ := hx
  have h1 := i₀.hη; have h2 := i₀.hηδ; have h3 := i₀.hδ
  have hlt : |x - i₀.t₁| < i₀.r₁ - m := by linarith
  rw [abs_lt] at hlt
  unfold G3Idx.t₁ G3Idx.r₁ at hlt
  have hxneg : x < 0 := by linarith
  have hxa : |x| = -x := abs_of_neg hxneg
  exact ⟨κ / 2, palmCRho refS x, palmCField gffBase.X x, fun _ => g2Corr γ x, R, S, Ω', _, P',
    Y', hP', hW, g2Root_setup hγ hγ2 (by positivity) (by rw [hxa]; linarith)
      (by rw [hxa]; linarith), hS, hμ, hV, hMdl, hlim⟩

theorem g2RootRModelStmt_of_agree {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Measure LawD}
    (h : G2RootRAgreeStmt γ μ) : G2RootRModelStmt γ μ := by
  intro s hs δ η m κ hκ hκm x hx
  obtain ⟨R, S, Ω', _, P', Y', hP', hW, hS, hμ, hV, hMdl, hlim⟩ :=
    h s hs δ η m κ hκ hκm x hx
  obtain ⟨i₀, -, -, hx₀⟩ := hx
  have h1 := i₀.hη; have h2 := i₀.hηδ; have h3 := i₀.hδ
  have hlt : |x - i₀.t₂| < i₀.r₂ - m := by linarith
  rw [abs_lt] at hlt
  unfold G3Idx.t₂ G3Idx.r₂ at hlt
  have hxpos : 0 < x := by linarith
  have hxa : |x| = x := abs_of_pos hxpos
  exact ⟨κ / 2, palmCRho refS x, palmCField gffBase.X x, fun _ => g2Corr γ x, R, S, Ω', _, P',
    Y', hP', hW, g2Root_setup hγ hγ2 (by positivity) (by rw [hxa]; linarith)
      (by rw [hxa]; linarith), hS, hμ, hV, hMdl, hlim⟩

/-- **`G2FixMixStmt` from D3⁺(i) (N2 form), the Palm identities, the identification nodes and
Sheffield's smoothing of the length coordinate** (both sides). -/
theorem g2FixMixStmt_of_agreeNodes {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ ν : Measure LawD}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hPX : G2RootXPalmIdStmt γ) (hAX : G2RootXAgreeStmt γ μ) (hSX : G2RootXLenSmoothStmt γ)
    (hPR : G2RootRPalmIdStmt γ) (hAR : G2RootRAgreeStmt γ ν) (hSR : G2RootRLenSmoothStmt γ) :
    G2FixMixStmt γ :=
  g2FixMixStmt_of_rootNodes hγ hγ2 hN2 hPX (g2RootXModelStmt_of_agree hγ hγ2 hAX) hSX hPR
    (g2RootRModelStmt_of_agree hγ hγ2 hAR) hSR

end Thm18Asm
end QuantumZipper
