import QuantumZipper.Proofs.Thm18.ASep4PhiC
import QuantumZipper.Proofs.Thm18.ASep2Conj2
import QuantumZipper.Proofs.LQG.WedgeToolkit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 6): raw values of the unzipped rescaled field at the A-sep measures

* `coordChange_nuA0_eq_evalReg` (deterministic): for any regular `y`, at a good parameter `p`,
  `coordChange y f_τ⁻¹ Q (ν_p) = evalReg y (fc(a d, a r)) + detLimA0 W 0 0 Q d r p`
  (`raw_id_A0`, `detLimA0_eq_raw`);
* `ae_raw_scale`: at fixed `p` and scale `s > 0`, almost surely the raw value for
  `y = rescale X Q s` is `X((muA0 p 0).map (s ·)) + detLimA0 + Q log s`
  (`WedgeTK.ae_evalReg_rescale_fc`);
* `continuousOn_raw_scale` (deterministic): continuity of that raw value in `q = (τ, a, s)`.

These are the raw-identity and raw-continuity inputs of the scale engine run (as `ae_hraw_A0`,
`ae_continuousOn_raw_A0`, ASepRawBox/ASepRawC). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont

/-- **Raw value at the A-sep measure** of the unzipped field of any regular sample. -/
theorem coordChange_nuA0_eq_evalReg (γ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ}
    (ha₀ : 0 < a₀) {S : Set (Fin 2 → ℝ)}
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁ ∧ 0 < p 0) {δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hsep : ∀ p ∈ S, ∀ w ∈ cthickening δ (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ T' > p 0, ∃ u, IsForwardSol W ((p 1 : ℂ) * w) T' u)
    {p : Fin 2 → ℝ} (hp : p ∈ S) {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) :
    coordChange y (fwdMapInv W (p 0)) (Qc γ) (nuA0 W d r p) =
      evalReg y (foldedCircle ((p 1 : ℂ) * d) (p 1 * r)) +
        detLimA0 W 0 (fun _ => 0) (Qc γ) d r p := by
  have hgood0 := hgood0_of_hgood hgood
  obtain ⟨m, -, -, -, hm, -, hlow, -⟩ := exists_geo_A0 hW hW0 hT.le ha₀ hgood0
  obtain ⟨hmeas, hgd, hint1, -, hI2, -, -⟩ :=
    pfacts_A0 hW hW0 hr ha₀ hm hδ hgood0 hlow (hSb p hp).1 (hSb p hp).2.2 (hSb p hp).2.1
      (hsep p hp) 0 (continuous_const (y := (0 : ℝ)))
  have hτ : 0 ≤ p 0 := (hSb p hp).1.1
  have ha : 0 < p 1 := ha₀.trans_le (hSb p hp).2.1.1
  have hadH : (p 1 : ℂ) * d ∈ Hbar := by
    show 0 ≤ ((p 1 : ℂ) * d).im
    have : 0 ≤ d.im := hd
    simpa using mul_nonneg ha.le this
  have e := raw_id_A0 γ hW hW0 hT hd hr ha₀ hSb hδ hgood hsep 0
    (continuous_const (y := (0 : ℝ))) hp hF
  have e0 : ofFun (fun _ : ℂ => (0 : ℝ)) + y = y := by
    funext μ; simp [ofFun]
  simp only [zero_mul, zero_add] at e
  rw [e0] at e
  have eL := detLimA0_eq_raw hW hW0 0 (continuous_const (y := (0 : ℝ))) (Qc γ) hτ ha hmeas hgd
    hint1 hI2
  rw [e, eL, hF.evalReg_fc_of_mem hadH (mul_pos ha hr)]
  simp only [zero_mul, zero_add, add_zero, integral_zero]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **The raw identity of the scale run** at a fixed parameter. -/
theorem ae_raw_scale [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ}
    (ha₀ : 0 < a₀) {S : Set (Fin 2 → ℝ)}
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁ ∧ 0 < p 0) {δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hsep : ∀ p ∈ S, ∀ w ∈ cthickening δ (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ T' > p 0, ∃ u, IsForwardSol W ((p 1 : ℂ) * w) T' u)
    {p : Fin 2 → ℝ} (hp : p ∈ S) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, coordChange (rescale (X ω) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ) (nuA0 W d r p) =
      X ω ((muA0 W d r p 0).map fun z => (s : ℂ) * z) +
        (detLimA0 W 0 (fun _ => 0) (Qc γ) d r p + Qc γ * Real.log s) := by
  have hgood0 := hgood0_of_hgood hgood
  obtain ⟨m, -, -, -, hm, -, hlow, -⟩ := exists_geo_A0 hW hW0 hT.le ha₀ hgood0
  obtain ⟨-, -, -, -, -, -, hmu0⟩ :=
    pfacts_A0 hW hW0 hr ha₀ hm hδ hgood0 hlow (hSb p hp).1 (hSb p hp).2.2 (hSb p hp).2.1
      (hsep p hp) 0 (continuous_const (y := (0 : ℝ)))
  have ha : 0 < p 1 := ha₀.trans_le (hSb p hp).2.1.1
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [RegSample.ae_isRegularSample hX, WedgeTK.ae_evalReg_rescale_fc hG (Qc γ) hs
    ((p 1 : ℂ) * d) (mul_pos ha hr)] with ω hreg h2
  obtain ⟨F, hF⟩ := hreg
  rw [coordChange_nuA0_eq_evalReg γ hW hW0 hT hd hr ha₀ hSb hδ hgood hsep hp
    (hF.rescale' (Qc γ) hs), h2, hmu0]
  simp only [measure_univ, ENNReal.toReal_one, mul_one]
  ring

/-- **Continuity of the raw value of the scale run** (deterministic). -/
theorem continuousOn_raw_scale (γ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ}
    (ha₀ : 0 < a₀) {S : Set (Fin 2 → ℝ)}
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁ ∧ 0 < p 0) {δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hsep : ∀ p ∈ S, ∀ w ∈ cthickening δ (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ T' > p 0, ∃ u, IsForwardSol W ((p 1 : ℂ) * w) T' u)
    {S3 : Set (Fin 3 → ℝ)} (hS3 : ∀ q ∈ S3, Fin.init q ∈ S ∧ 0 < q (Fin.last 2))
    {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) :
    ContinuousOn (fun q : Fin 3 → ℝ => coordChange (rescale x (Qc γ) (q (Fin.last 2)))
      (fwdMapInv W (Fin.init q 0)) (Qc γ) (nuA0 W d r (Fin.init q))) S3 := by
  have hdc := continuousOn_detLimA0 hW hW0 hT.le hr ha₀
    (fun p hp => ⟨(hSb p hp).1, (hSb p hp).2.1⟩) hgood 0 (continuous_const (y := (0 : ℝ)))
    (Qc γ)
  have hinit : Continuous fun q : Fin 3 → ℝ => Fin.init q :=
    continuous_pi fun i => continuous_apply _
  have hmemH : ∀ q ∈ S3, ((Fin.init q 1 : ℂ) * d) ∈ Hbar := fun q hq => by
    have ha : 0 < Fin.init q 1 := ha₀.trans_le (hSb _ (hS3 q hq).1).2.1.1
    show 0 ≤ ((Fin.init q 1 : ℂ) * d).im
    have : 0 ≤ d.im := hd
    simpa using mul_nonneg ha.le this
  have h1 : ContinuousOn (fun q : Fin 3 → ℝ =>
      F (((q (Fin.last 2) : ℝ) : ℂ) * ((Fin.init q 1 : ℂ) * d),
        q (Fin.last 2) * (Fin.init q 1 * r))) S3 := by
    refine hF.1.comp (Continuous.continuousOn (by fun_prop)) fun q hq => ⟨?_, ?_⟩
    · exact RegClosure.mapsTo_mul_pos (hS3 q hq).2 (hmemH q hq)
    · exact mul_pos (hS3 q hq).2 (mul_pos (ha₀.trans_le (hSb _ (hS3 q hq).1).2.1.1) hr)
  have h2 : ContinuousOn (fun q : Fin 3 → ℝ => Qc γ * Real.log (q (Fin.last 2))) S3 :=
    continuousOn_const.mul (Real.continuousOn_log.comp (continuous_apply _).continuousOn
      fun q hq => (hS3 q hq).2.ne')
  have h3 : ContinuousOn (fun q : Fin 3 → ℝ => detLimA0 W 0 (fun _ => 0) (Qc γ) d r
      (Fin.init q)) S3 := hdc.comp hinit.continuousOn fun q hq => (hS3 q hq).1
  refine ((h1.add h2).add h3).congr fun q hq => ?_
  have hs := (hS3 q hq).2
  have ha : 0 < Fin.init q 1 := ha₀.trans_le (hSb _ (hS3 q hq).1).2.1.1
  rw [coordChange_nuA0_eq_evalReg γ hW hW0 hT hd hr ha₀ hSb hδ hgood hsep (hS3 q hq).1
    (hF.rescale' (Qc γ) hs), (hF.rescale' (Qc γ) hs).evalReg_fc_of_mem (hmemH q hq)
      (mul_pos ha hr)]
  rfl

end ASep
end QuantumZipper
