/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51GQ
import InteractingSLE.Spec.Sec5.Prop49QExitMain
import InteractingSLE.Spec.Sec5.CrossCondThetaMart
import InteractingSLE.Spec.Sec7.Lemma75Bridge

/-!
# The first exit of the flow line from `ℍ ∖ R(K_s)` at a relative angle `θ > π/2` (below the critical gap)

Packet PROVE-PROP51G, step (4), up to the first contact. Specification §5, proof of Proposition 5.1 (pp. 134–135):
"Conditioning `h` on `η′([0, τ′])` and conformally mapping … Apply Aux. lemma 22 to this finite upper-boundary
profile … The critical-span conclusion … places the first endpoint on the left side of the revealed counterflow". In
the chart `Q` (`Prop51GQ`) the flow line `η = η_{θ₂}` of `h` and the counterflow of `h + (θ₁ − π/2)χ` are the flow line
of `h' = h + θ₂χ` and the counterflow of `h' − θχ`, `θ = θ₂ − θ₁ + π/2`: the glued setting of PROVE-CROSSCOND-THETA
(`CrossCond.Theta.CfGlueAET θ`). Its image word in the counterflow chart, killed at the first contact, has the junction
weights `cLT θ`, `cRT θ` (`CrossCond.Theta.exists_isWordEntrance_of_filtTheta`, proved), and Aux. lemma 22 for its
left span applies **below the critical gap** `θ₂ − θ₁ < πκ/(4 − κ)`, where Zhan's charge condition holds.

* `hasStripPrefixSums_jwT`, `abs_charge_jwT_lt`, `not_threshold_img_gen`: the image word's strip prefix sums
  (`θ ≥ π/2`), its charge condition (`−π/2 < θ`, `(1/2 + θ/π)(2 − κ/2) < 2`), and its start below the threshold;
* `ae_imgExitT`: Proposition 4.9's image exit (PROVE-GLUECOND11's `Prop49Exit.ae_imgExit`) at relative angle `θ`;
* `ae_exitT_of_noReturn`: the first exit pulled back to the flow line (PROVE-GLUECOND11's
  `prop49QExitStatement_of_noReturn` at relative angle `θ`, with the counterflow's no-return given almost surely);
* `firstContactNotEast_zero_of_exit` (deterministic): a first exit at a negative chart point is not eastern;
* **`fwdFirstExitQOn_smallGap`**: the first-exit input `FwdFirstExitQOn` of the forward route below the critical gap,
  from the counterflow's regularity (`Prop51Q.CfLineRegularQStatement`, from Zhan's Part A at `16/κ`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51G

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 CrossCond.Theta MartChar.RealFlow LawUnique Cond44Ref Prop411Q
  CfRegQ Prop49Exit
open Sec7.Lemma71C (capClock)

/-! ### The image word's weights at relative angle `θ` -/

section Weights

variable {nL nR : ℕ}

/-- `θ/π ≥ 1/2` for `θ ≥ π/2`. -/
theorem half_le_div_pi {θ : ℝ} (hθ : π / 2 ≤ θ) : 1 / 2 ≤ θ / π := by
  rw [le_div_iff₀ Real.pi_pos]; linarith

/-- **The strip prefix sums of the image word at relative angle `θ ≥ π/2`** (`0 < κ < 4`, an ordered (4.4) word). -/
theorem hasStripPrefixSums_jwT {κ θ : ℝ} (hκ4 : κ < 4) (hθ : π / 2 ≤ θ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h44 : Sec4.Cond44 κ ρL ρR) :
    Strip.HasStripPrefixSums κ (Fin.init (jwL (cLT θ) κ ρL)) (jwR (cRT θ) κ ρR) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have e : Fin.init (jwL (cLT θ) κ ρL) = ρL := by simp [jwL]
    rw [e]
    exact le_sum_Iic_left h44 j
  · induction j using Fin.lastCases with
    | last =>
      simp only [jwR, cRT]
      rw [sum_Iic_snoc_last]
      have h1 := half_le_div_pi hθ
      nlinarith
    | cast k =>
      simp only [jwR]
      rw [sum_Iic_snoc_castSucc]
      linarith [le_sum_Iic_right h44 k]

/-- **The charge condition of the image word at relative angle `θ`**: the left-span weight is
`q₋ = (3/2 + θ/π)(κ/2 − 2)`, and `|κ − 6 − 2q₋| < 2` exactly when `−π/2 < θ` and `(1/2 + θ/π)(2 − κ/2) < 2`. -/
theorem abs_charge_jwT_lt {κ θ : ℝ} (hκ4 : κ < 4) (hθ₁ : -(π / 2) < θ)
    (hθ₂ : (1 / 2 + θ / π) * (2 - κ / 2) < 2) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    |Strip.chargePlus κ (Fin.init (jwL (cLT θ) κ ρL)) (jwR (cRT θ) κ ρR) (jwL (cLT θ) κ ρL (Fin.last nL)) -
      Strip.chargeMinus (Fin.init (jwL (cLT θ) κ ρL)) (jwL (cLT θ) κ ρL (Fin.last nL))| < 2 := by
  have hm : Strip.chargeMinus (Fin.init (jwL (cLT θ) κ ρL)) (jwL (cLT θ) κ ρL (Fin.last nL)) =
      (3 / 2 + θ / π) * (κ / 2 - 2) := by
    simp only [Strip.chargeMinus, jwL, cLT, Fin.init_snoc, Fin.snoc_last]
    ring
  have hsum := Strip.chargePlus_add_chargeMinus κ (Fin.init (jwL (cLT θ) κ ρL)) (jwR (cRT θ) κ ρR)
    (jwL (cLT θ) κ ρL (Fin.last nL))
  have hθ' : -(1 / 2) < θ / π := by rw [lt_div_iff₀ Real.pi_pos]; linarith
  have hu : 0 < 2 - κ / 2 := by linarith
  have hpos : 0 < (1 / 2 + θ / π) * (2 - κ / 2) := mul_pos (by linarith) hu
  rw [abs_lt]
  constructor <;> nlinarith

/-- **The image word starts below the continuation threshold**, for any junction weights (the junction marks are away
from the driver at time `0`; PROVE-GLUECOND11's `Prop49Exit.not_threshold_img` with general junction weights). -/
theorem not_threshold_img_gen (cL cR : ℝ → ℝ → ℝ) {κ : ℝ} (hκ : 0 < κ) {Ω : Type*} {s : ℝ≥0}
    {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) :
    ¬ ForceWord.ThresholdCondition (jwL cL κ ρL) (jwR cR κ ρR) (imgW s ζ W E 0 p)
      (fun i => imgVL xL s ζ W E i 0 p) (fun j => imgVR xR s ζ W E j 0 p) := by
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p hp
  have hw := continuous_cfDrv0 s p.2
  simp only [imgW_zero hEg, imgVL_zero hF.2.1 hEg, imgVR_zero hF.2.2.2 hEg, gXL_of_mem hp, gXR_of_mem hp,
    ForceWord.ThresholdCondition, jwL, jwR, not_or, not_le]
  have hjL0 : junL (cfDrv0 s p.2) s ≠ 0 := div_ne_zero (by norm_num) hjL.ne'
  have hjR0 : junR (cfDrv0 s p.2) s ≠ 0 := div_ne_zero (by norm_num) hjR.ne
  rw [sum_filter_snoc_eq_zero _ _ _ _ hjL0, sum_filter_snoc_eq_zero _ _ _ _ hjR0]
  have eL : (Finset.univ.filter fun i => psiL (cfDrv0 s p.2) s (xL i) = 0) =
      Finset.univ.filter fun i => xL i = 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => psiL_ne_zero hw s.coe_nonneg hjL (hF.2.1 i) h0 h, fun h => ?_⟩
    simp [psiL, h]
  have eR : (Finset.univ.filter fun j => psiR (cfDrv0 s p.2) s (xR j) = 0) =
      Finset.univ.filter fun j => xR j = 0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => psiR_ne_zero hw s.coe_nonneg hjR (hF.2.2.2 j) h0 h, fun h => ?_⟩
    simp [psiR, h]
  rw [eL, eR]
  refine ⟨neg_two_lt_sum_filter_zero (c := κ / 2 - 2) (by linarith) (fun i i' hii h => ?_) h44.1,
    neg_two_lt_sum_filter_zero (c := 0) (by norm_num) (fun j j' hjj h => ?_) h44.2⟩
  · exact le_antisymm (hF.2.1 i') (h ▸ hF.1 hii)
  · exact le_antisymm (h ▸ hF.2.2.1 hjj) (hF.2.2.2 j')

end Weights

/-! ### The image exit at relative angle `θ` -/

section Exit

/-- **The image exit at relative angle `θ`** (PROVE-GLUECOND11's `Prop49Exit.ae_imgExit` with the counterflow of
`h − θχ`). In the glued setting of `CrossCond.Theta.CfGlueAET θ`, for `π/2 ≤ θ` below the critical gap and every
counterflow time `s > 0`, almost surely the killing time `imgT` of the image word is finite and the image trace
converges at `imgT`, either to a point of `ℍ` or to a real point strictly left of the left junction `Ψ(∞⁻)`
(Aux. lemma 22 for the image word's left span). -/
theorem ae_imgExitT {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : π / 2 ≤ θ)
    (hθ₂ : (1 / 2 + θ / π) * (2 - κ / 2) < 2) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p : ℝ≥0∞) ≠ ⊤ ∧
      ∃ z : ℂ, Tendsto (imgTr s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p)
        (𝓝[<] ENNReal.toNNReal (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p)) (𝓝 z) ∧
        (z ∈ H ∨ ∃ x₀ : ℝ, x₀ < gXL xL s (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p (Fin.last nL) ∧ z = x₀) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂
      hcf hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨-, hK, hWa, hVLa, hVRa, -, -, -, -, hζq⟩ := filtClauses (μ := μ) (xL := xL) (xR := xR) hWad hF hae
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, Bi, hB, hBc, hEnt⟩ :=
    exists_isWordEntrance_of_filtTheta (imageWordFiltThetaStatement θ) hκ hκ4 hF h44 hθb hC hcf hlaw k hk hs
  set 𝓖 := imgFilt μ xL xR s ζ W E with h𝓖
  have hTq' : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × Ω₀ | (q : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞)} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hthr : ∀ᵐ p ∂(μ.prod P₀), ¬ ForceWord.ThresholdCondition (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
      (imgW s ζ W E 0 p.1) (fun i => imgVL xL s ζ W E i 0 p.1) (fun j => imgVR xR s ζ W E j 0 p.1) := by
    have h1 : ∀ᵐ p ∂μ, ¬ ForceWord.ThresholdCondition (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
        (imgW s ζ W E 0 p) (fun i => imgVL xL s ζ W E i 0 p) (fun j => imgVR xR s ζ W E j 0 p) := by
      filter_upwards [ae_mem_glueGood hae] with p hp
      exact not_threshold_img_gen (cLT θ) (cRT θ) hκ hF h44 hEg hp
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hgeo : ∀ (p : (Ω × HistorySpace 0 0) × Ω₀) (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞) →
      ∀ y : ℝ, y < imgVL xL s ζ W E (Fin.last nL) t p.1 - imgW s ζ W E t p.1 →
        extendFrom H (fwdMapInv (fun r : ℝ => imgW s ζ W E r.toNNReal p.1) t) y ∉ H := by
    intro p t _ htT y hy
    obtain ⟨x₀, -, hx₀⟩ := imgGeo hF.2.1 hEg p.1 htT hy
    rw [hx₀]
    intro hH
    have h0 : (0 : ℝ) < ((x₀ : ℝ) : ℂ).im := hH
    simp at h0
  have hθ₁ : -(π / 2) < θ := by linarith [Real.pi_pos]
  have hX := ae_leftExit_of_killed_ord (P := μ.prod P₀) (𝓘 := WholeField.prodFiltration 𝓖 𝓦) hκ hκ4.le
    (hasStripPrefixSums_jwT hκ4 hθ h44) (abs_charge_jwT_lt hκ4 hθ₁ hθ₂ ρL ρR) hB hBc
    (W := fun t p => imgW s ζ W E t p.1) (VL := fun i t p => imgVL xL s ζ W E i t p.1)
    (VR := fun j t p => imgVR xR s ζ W E j t p.1)
    (Sec7.PhaseSelFull.stronglyAdapted_fst hWa) (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
    (fun j => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa j)) (T := fun p => (imgT s ζ W E p.1 : ℝ≥0∞)) hTq'
    (fun p => (isKilledArc_gCurve hEg p.1).zero_lt_kLife) hEnt
    (fun p t ht htT i => hK.sepL p.1 t ht htT i) (fun p t ht htT j => hK.sepR p.1 t ht htT j) hthr hgeo
  have h2 := Measure.ae_ae_of_ae_prod hX
  filter_upwards [h2] with p hp
  obtain ⟨_, hpω⟩ := hp.exists
  obtain ⟨hTne, z, hz, hzalt⟩ := hpω (imgTr s ζ W E p) (fun r hr => isGeneratingTraceIcc_imgTr hEg p hr)
    (fun t ht0 ht => imgTr_mem_H hEg p ht0 ht)
  refine ⟨hTne, z, hz, ?_⟩
  rcases hzalt with hzH | ⟨q, y, -, hqT, hy, rfl⟩
  · exact Or.inl hzH
  · obtain ⟨x₀, hx₀, hx₀e⟩ := imgGeo hF.2.1 hEg p hqT hy
    exact Or.inr ⟨x₀, hx₀, hx₀e⟩

/-- **The first exit of the flow line at relative angle `θ`** (PROVE-GLUECOND11's `prop49QExitStatement_of_noReturn`
with the counterflow of `h − θχ`, below the critical gap). In the glued setting of `CrossCond.Theta.CfGlueAET θ`, if
the counterflow almost surely never returns to its start, then for every positive rational `s`, almost surely the flow
line `η = seedLine ζ W` first meets `R(K_s)` at a time `t₀ > 0`, at a counterflow point `R(β(v))`, `0 < v ≤ s`, after
avoiding it, and `Ψ ∘ η` tends to a negative real point as `t ↑ t₀` (a hit of the western side). -/
theorem ae_exitT {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : π / 2 ≤ θ)
    (hθ₂ : (1 / 2 + θ / π) * (2 - κ / 2) < 2) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hNR : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      ∀ v : ℝ, 0 < v → histLine p.2 v ≠ 0)
    {s : ℚ} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      ∃ t₀ x₀ : ℝ, 0 < t₀ ∧ x₀ < 0 ∧ (∃ v ∈ Ioc (0 : ℝ) s, seedLine ζ W p.1 t₀ = revLine p.2 v) ∧
        (∀ t ∈ Ioo 0 t₀, seedLine ζ W p.1 t ∉ negInv '' fwdHull (cfDrv p.2) s) ∧
        Tendsto (fun t => revChart (cfDrv p.2) s (seedLine ζ W p.1 t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ)) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set s' : ℝ≥0 := (s : ℝ).toNNReal with hs'def
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs' : 0 < s' := Real.toNNReal_pos.2 hs0
  have hss' : (s' : ℝ) = (s : ℝ) := Real.coe_toNNReal _ hs0.le
  set E := glueGood μ s' ζ W with hEdef
  have hgood := cfGlueAE_isGood49T θ s' hs' κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂
    hcf hlaw k hk
  have hae : ∀ᵐ p ∂μ, IsGood49 s' ζ W p := by
    filter_upwards [hgood] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hexit := ae_imgExitT hκ hκ4 hθ hθ₂ hF h44 hθb hC hcf hlaw k hk hs'
  filter_upwards [hexit, hgood, hNR, ae_mem_glueGood hae] with p ⟨hTne, z, hz, hzalt⟩ hpg hpnr hpE
  obtain ⟨hα, hG0, hjL0, -, hQ⟩ := isGood49_of_mem_glueGood p hpE
  have hy : p.2 ∈ goodCfSet := hpg.2.1.1
  obtain ⟨-, hw, hw0, hβ⟩ := reg_of_mem_goodCfSet hy
  have hEq := eqOn_cfDrv0_cfDrv hy s'
  have hK0 := fwdHull_cfDrv0 hy s'
  have hR0 := revChart_cfDrv0 hy s'
  have hrI : rightImg (cfDrv0 s' p.2) 0 s' = rightImg (cfDrv p.2) 0 s' :=
    Sec7.Lemma71B.rightImg_congr hw s'.coe_nonneg hEq 0
  have hw0s : cfDrv0 s' p.2 s' = cfDrv p.2 s' := hEq s' ⟨s'.coe_nonneg, le_rfl⟩
  have hjL : 0 < rightImg (cfDrv p.2) 0 s - cfDrv p.2 s := by
    rw [← hss', ← hrI, ← hw0s]; exact hjL0
  have hG : IsClosed (negInv '' fwdHull (cfDrv p.2) s) := by rw [← hss', ← hK0]; exact hG0
  have hcurve : gCurve s' ζ W E p = imgCurve (cfDrv p.2) s (seedLine ζ W p.1) := by
    rw [gCurve_of_mem hpE]
    funext u
    simp only [imgCurve]
    rw [hR0, hss']
  have hpre : gPre s' ζ W E p = preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s) := by
    rw [gPre_of_mem hpE, hQ, hK0, hss']
  have hjun : gXL xL s' E p (Fin.last nL) = junL (cfDrv p.2) s := by
    rw [gXL_of_mem hpE, Fin.snoc_last]
    simp only [junL]
    rw [hrI, hw0s, hss']
  have hT' : ((ENNReal.toNNReal (imgT s' ζ W E p) : ℝ≥0) : WithTop ℝ≥0) =
      kLife (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
        (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)) := by
    rw [← hcurve, ← hpre]
    exact ENNReal.coe_toNNReal hTne
  have hz' : Tendsto (kTrace (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
      (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)))
      (𝓝[<] ENNReal.toNNReal (imgT s' ζ W E p)) (𝓝 z) := by
    rw [← hcurve, ← hpre]; exact hz
  have hzalt' : z ∈ H ∨ ∃ x₀ : ℝ, x₀ < junL (cfDrv p.2) s ∧ z = x₀ := by
    rcases hzalt with h1 | ⟨x₀, hx₀, rfl⟩
    · exact Or.inl h1
    · exact Or.inr ⟨x₀, hjun ▸ hx₀, rfl⟩
  have hNRp : ∀ v ∈ Ioc (0 : ℝ) s, histLine p.2 v ≠ 0 := fun v hv => hpnr v hv.1
  exact exit_of_imgExit hw hw0 hβ hs0 hNRp hjL hG hα hT' hz' hzalt'

end Exit

/-! ### From the first exit to `FirstContactNotEast` at the restart time `0` (deterministic) -/

section Det

/-- A cluster point of a function that converges is its limit. -/
theorem eq_of_mapClusterPt_of_tendsto {α : Type*} {F : Filter α} {f : α → ℂ} {x y : ℂ}
    (hc : MapClusterPt x F f) (ht : Tendsto f F (𝓝 y)) : x = y :=
  eq_of_nhds_neBot (hc.neBot.mono (inf_le_inf_left _ ht))

/-- **A first exit at a negative chart point is not eastern** (deterministic). If the proper arc `η` avoids
`R(K_s)` on `(0, t₀)` and `Ψ ∘ η` tends to a real point `x₀ < 0` as `t ↑ t₀`, then the excursion of `η` in
`ℍ ∖ R(K_s)` started at `0` does not end in the eastern part: it ends at `t₀` at `x₀` (in the chart), and it cannot
run on past `t₀` (`η(t₀)` would be a point of `ℍ ∖ R(K_s)` with a real chart value). -/
theorem firstContactNotEast_zero_of_exit {η : ℝ → ℂ} (hη : IsProperArc η) {w : ℝ → ℝ} (hw : Continuous w)
    {s : ℝ} (hs : 0 ≤ s) {t₀ x₀ : ℝ} (ht₀ : 0 < t₀) (hx₀ : x₀ < 0)
    (hpre : ∀ t ∈ Ioo 0 t₀, η t ∉ cfHullQ w s)
    (hlim : Tendsto (fun t => revChart w s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ))) : FirstContactNotEast w s 0 η := by
  have hcont : ∀ u, 0 < u → η u ∈ H \ cfHullQ w s → ContinuousAt (fun t => revChart w s (η t)) u := by
    intro u hu hD
    have h1 : ContinuousAt η u := hη.cont.continuousAt (Ici_mem_nhds hu)
    have h2 : ContinuousAt (revChart w s) (η u) :=
      (continuousOn_revChart hw hs).continuousAt ((isOpen_H_diff_negInv_fwdHull hw hs).mem_nhds hD)
    exact ContinuousAt.comp (g := revChart w s) (f := η) h2 h1
  have hreal : ∀ (u y : ℝ), η u ∈ H \ cfHullQ w s → revChart w s (η u) ≠ (y : ℂ) := by
    intro u y hD e
    have := revChart_mem_H hw hs hD
    rw [e] at this
    exact absurd this (by simp [QuantumZipper.H])
  have ht₀D : η t₀ ∉ H \ cfHullQ w s := fun hD => by
    have h1 := ((hcont t₀ ht₀ hD).tendsto).mono_left (nhdsWithin_le_nhds (s := Iio t₀))
    exact hreal t₀ x₀ hD (tendsto_nhds_unique h1 hlim)
  intro _
  refine ⟨fun u₀ hu₀ hD => ?_, fun hD => absurd (hD t₀ ht₀) ht₀D⟩
  rintro ⟨x, hx, hcl⟩
  have hu₀t : u₀ ≤ t₀ := le_of_not_gt fun h => ht₀D (hD t₀ ⟨ht₀, h⟩)
  rcases lt_or_eq_of_le hu₀t with hlt | heq
  · have hD₀ : η u₀ ∈ H \ cfHullQ w s := ⟨hη.mem_H u₀ hu₀, hpre u₀ ⟨hu₀, hlt⟩⟩
    have ht : Tendsto (fun u => revChart w s (η u)) (𝓝[Ioo 0 u₀] u₀ ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s})
        (𝓝 (revChart w s (η u₀))) :=
      (hcont u₀ hu₀ hD₀).tendsto.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
    exact hreal u₀ x hD₀ (eq_of_mapClusterPt_of_tendsto hcl ht).symm
  · subst heq
    have ht : Tendsto (fun u => revChart w s (η u)) (𝓝[Ioo 0 u₀] u₀ ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s})
        (𝓝 (x₀ : ℂ)) := hlim.mono_left (inf_le_left.trans (nhdsWithin_mono _ fun u hu => hu.2))
    have e := eq_of_mapClusterPt_of_tendsto hcl ht
    have : x = x₀ := by exact_mod_cast e
    linarith

end Det

/-! ### The first-exit input of the forward route below the critical gap -/

section Main

/-- The shifts `flowField 0 a` compose additively. -/
theorem flowField_zero_flowField_zero (a b : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Exist.flowField 0 a (Exist.flowField 0 b f) = Exist.flowField 0 (a + b) f := by
  ext φ
  simp only [Exist.flowField_apply, GlueCond.pushTest_shiftChart_zero]
  ring

/-- **The counterflow field of `Prop51QStatement` is the counterflow field at relative angle `θ = θ₂ − θ₁ + π/2` of
the flow line's field `h + θ₂χ`.** -/
theorem cfField_flowField_eq_cfFieldT (κ θ₁ θ₂ : ℝ) (f : DistOn upperHalfPlaneOpens) :
    cfField κ (Exist.flowField 0 (θ₁ * chiC κ) f) =
      cfFieldT κ (θ₂ - θ₁ + π / 2) (Exist.flowField 0 (θ₂ * chiC κ) f) := by
  simp only [cfField, cfFieldT, flowField_zero_flowField_zero]
  congr 1
  ring

/-- **The counterflow of `h + (θ₁ − π/2)χ` is admissible** for the flow word of `h` at angle `θ₂`, at relative angle
`θ₂ − θ₁ + π/2` (the data of (5.2)). -/
theorem cfThetaBounds_prop74 {κ : ℝ} (hκ : 0 < κ) {a b θ₁ θ₂ : ℝ}
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₁ * chiC κ ≤ a) :
    CfThetaBounds κ (θ₂ - θ₁ + π / 2) (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂)
      (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineXL (Sec7.prop74Data a b) {0} 0)
      (flowLineXR (Sec7.prop74Data a b) {0} 0) := by
  have hpc := Sec7.isPiecewiseConstant_prop74Data a b
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [Exist.forceBoundaryData_flowLine_seed hκ hpc 0 θ₂ hx.ne (by simp [hx.ne])]
    simp only [add_zero, Sec7.prop74Data, hx, ↓reduceIte]
    nlinarith
  · rw [Exist.forceBoundaryData_flowLine_seed hκ hpc 0 θ₂ hx.ne' (by simp [hx.ne'])]
    simp only [add_zero, Sec7.prop74Data, show ¬ x < 0 from not_lt.2 hx.le, ↓reduceIte]
    nlinarith

/-- Below the critical gap, the charge bound of `abs_charge_jwT_lt` at `θ = θ₂ − θ₁ + π/2`. -/
theorem charge_bound_of_not_isLargeGap {κ θ₁ θ₂ : ℝ} (hκ4 : κ < 4) (hG : ¬ IsLargeGap κ θ₁ θ₂) :
    (1 / 2 + (θ₂ - θ₁ + π / 2) / π) * (2 - κ / 2) < 2 := by
  have hπ := Real.pi_pos
  have h4 : 0 < 4 - κ := by linarith
  have hg : (θ₂ - θ₁) * (4 - κ) < π * κ := by
    have := not_le.1 hG
    rwa [lt_div_iff₀ h4] at this
  have e : (1 / 2 + (θ₂ - θ₁ + π / 2) / π) * (2 - κ / 2) =
      (4 - κ) / 2 + (θ₂ - θ₁) * (4 - κ) / (2 * π) := by
    field_simp
    ring
  rw [e]
  have : (θ₂ - θ₁) * (4 - κ) / (2 * π) < κ / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **The first-exit input of the forward route below the critical gap** (`FwdFirstExitQOn` on
`θ₂ − θ₁ < πκ/(4 − κ)`), from the counterflow's regularity: the cross-conditioning law at relative angle
`θ₂ − θ₁ + π/2` (PROVE-CROSSCOND-THETA) with Aux. lemma 22 (`ae_exitT`), read on the glued space of
`Cond44Ref.Prop51QStatement`. -/
theorem fwdFirstExitQOn_smallGap (hreg : Prop51Q.CfLineRegularQStatement.{u}) :
    FwdFirstExitQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hfl₀ := hfl
  obtain ⟨h', 𝓕, W, VL, VR, B, htrans, hC, htr⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htrans ω)
  set θ := θ₂ - θ₁ + π / 2 with hθdef
  have hXeq : (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = fun ω => cfFieldT κ θ (h' ω) := by
    funext ω
    rw [hh', cfField_flowField_eq_cfFieldT κ θ₁ θ₂]
  have hμ : glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)) =
      glueMeasure P k (fun ω => cfFieldT κ θ (h' ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) := by
    congr 1
  have hlaw' : P.map (fun ω => cfFieldT κ θ (h' ω)) = P₂.map h₂ := by rw [← hXeq]; exact hlaw
  have hθb : CfThetaBounds κ θ _ _ _ _ :=
    cfThetaBounds_prop74 (a := a) (b := b) (θ₁ := θ₁) (θ₂ := θ₂) hκ hb (by linarith)
  -- the counterflow's regularity, on the glued space
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  rw [hμ] at hregG ⊢
  have hNR : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h' ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      ∀ v : ℝ, 0 < v → histLine p.2 v ≠ 0 := by
    filter_upwards [hregG] with p hp
    exact hp.2.2.2.2.1
  have hexit := ae_exitT hκ hκ4 (by linarith) (charge_bound_of_not_isLargeGap hκ4 hG) hF h44 hθb hC hcf hlaw' k hk
    hNR hs
  -- the flow line is the coupling's seed line and a proper arc
  have hseed : ∀ᵐ ω ∂P, seedLine ζ W ω = fun u : ℝ => η ω u.toNNReal := by
    filter_upwards [ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1, htr, hC.1.2.2.2.2] with ω hω ht hp
    obtain ⟨hζ, -, -⟩ := hω
    have e : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
      funext t
      simp
    rw [e] at ht
    exact seedLine_eq_of_isGeneratingTrace hζ hp.2.2.2.1 hp.1 ht
  have hseedG := ae_glue_fst (μ := P) k ((measurable_cfFieldT κ θ).comp hC.2.1) hseed
  have harc := ae_glue_fst (μ := P) k ((measurable_cfFieldT κ θ).comp hC.2.1)
    (ae_isProperArc_of_isFlowLine hκ hκ4.le hadm hfl₀)
  filter_upwards [hexit, hseedG, harc, hregG] with p hp hps hpa hpr
  obtain ⟨t₀, x₀, ht₀, hx₀, -, havoid, hlim⟩ := hp
  rw [hps] at havoid hlim
  exact firstContactNotEast_zero_of_exit hpa hpr.2.1 (by exact_mod_cast hs.le) ht₀ hx₀ havoid hlim

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs at `16/κ` and the forward route, with the first exit
proved**: what remains is the no-wrap topology and the post-contact barrier below the critical gap, and no contact at
and above it. -/
theorem prop51QStatement_of_partA_of_fwd_post (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hnc : FwdNoContactQStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_fwd hA htopo
    (fwdFirstExitQOn_smallGap (CfLineRegQ.cfLineRegularQStatement_of_partA hA)) hpost hnc

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from the forward route**, with the first exit
proved (the drop-in for `hfirst` in `Wire.twoSeedGraphInput_of_open7`, through `cfFirstContactQStatement_of_prop51Q`).
-/
theorem cfFirstContactQStatement_of_partA_of_fwd_post (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hnc : FwdNoContactQStatement.{u}) : CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q (CfLineRegQ.cfLineRegularQStatement_of_partA hA)
    (prop51QStatement_of_partA_of_fwd_post hA htopo hpost hnc)

end Main

end InteractingSLE.Sec5.Prop51G
