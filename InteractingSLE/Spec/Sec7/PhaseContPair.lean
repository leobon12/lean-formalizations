/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseRead
import InteractingSLE.Spec.Sec7.PhaseContTilt

/-!
# Theorem 1.2's R.7: Gaussian tails for the pocket mean of a far test function at two times

Packet PROVE-PHASECONT. Setting of `PhaseClause.exists_measurableSet_iff_phase` (a driven curve with prefixes
adapted to `𝓗`, a measurable pocket chart, a field read through the chart): at two relative capacity times `q < r` the
field is conditionally Gaussian given `𝒢 ⊇ 𝓗_q` and given `𝒢' ⊇ 𝒢 ∨ 𝓗_r`, with chart-transported means that are the
coupling means of the phase words `d` and `d'`. On the event that the far bump `ψ_n` is safe at level `1/(m+1)` at
time `r`, the tested means are `phaseInt_q(d)` and `phaseInt_r(d')` and the Green energy decreased by at most
`C (r − q)` (`Coupling.IsSafeAt.abs_loewnerGreenEnergy_sub_le`), so the two-level tilt (`PhaseContTilt`) gives
`P(safe at r, |phaseInt_r(d') − phaseInt_q(d)| ≥ b) ≤ 2 exp(−b²/(2C(r − q)))`.

## Main results

* `farMean` (def), `farGap` (def), `farMean_eq_add_mul`;
* `ae_condExp_farBump_eq`: the conditional characteristic function of the far test pairing on its safe event;
* `ae_chartTransport_farBump_eq`: the tested mean is `farMean` on the safe event;
* **`measure_farMean_increment_le`**: the Gaussian tail of the increment.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PhaseCont

open Restart.DomainMarkov Restart.DomainMarkov.Mean Restart.DomainMarkov.Aux79 Coupling Ito PhaseSel PhaseMart
  PocketTraversal Lemma71C PhaseClause

variable {Ω : Type*} {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}

/-- The tested coupling mean of the phase-`c` word against the far bump `ψ_n` at relative time `p`. -/
def farMean (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ)
    (xR : Ω → Fin (nR + 1) → ℝ) (n : ℕ) (p : ℝ≥0) (c : ℝ) (ω : Ω) : ℝ :=
  phaseInt κ ρL ρR (fun t => segDriver (γ ω) t) (fun i t => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω)
    (fun j t => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω) p (farBump n) c

/-- The window weight of the far bump at relative time `p` (positive at positive times). -/
def farGap (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ)
    (xR : Ω → Fin (nR + 1) → ℝ) (n : ℕ) (p : ℝ≥0) (ω : Ω) : ℝ :=
  phaseGap κ ρL ρR (fun t => segDriver (γ ω) t) (fun i t => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω)
    (fun j t => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω) p (farBump n)

theorem farMean_eq_add_mul (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (n : ℕ)
    (p : ℝ≥0) (c : ℝ) (ω : Ω) :
    farMean κ ρL ρR γ xL xR n p c ω = farMean κ ρL ρR γ xL xR n p 0 ω + c * farGap κ ρL ρR γ xL xR n p ω := by
  unfold farMean farGap
  rw [phaseInt_eq_add_mul, phaseInt_eq_add_mul, zero_mul, add_zero]

section Kernel

variable {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The conditional characteristic function of the far test pairing on its safe event.** -/
theorem ae_condExp_farBump_eq [IsProbabilityMeasure P] {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) (p : ℝ≥0) (h𝒢 : 𝒢 ≤ mΩ) (M : Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (p : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) p) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) p))
            φ φ : ℝ) : ℂ)))
    (n : ℕ) {δ : ℝ} (hS : MeasurableSet[𝒢] (safeSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) univ
      (farBump n) δ p)) (t : ℝ) :
    ∀ᵐ ω ∂P, ω ∈ safeSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) univ (farBump n) δ p →
      P[fun ω => Complex.exp (Complex.I * ((t * Chart.chartTransport (hc ω) 1 a k (h ω) (farBump n) : ℝ) : ℂ)) |
        𝒢] ω = Complex.exp (Complex.I * ((t * Chart.chartTransport (hc ω) 1 a k (M ω) (farBump n) : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (t ^ 2 * loewnerGreenEnergy (fun s : ℝ => segDriver (γ ω) s.toNNReal) p
            (farBump n))) : ℝ) : ℂ) := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  set ζ : Ω → ℝ≥0∞ := fun ω => capLife (γ ω) with hζdef
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω => (hγ ω).segDriver_spec.2.1
  have hcl := ae_condExp_cexp_chartTransport_eq_energy (P := P) (ζ := ζ) (W := W) (𝒢 := 𝒢) h𝒢 hc hdom hfwd hliftm
    hliftc hh a k p (Mset := univ) (fun φ => by filter_upwards [hcond φ] with ω hω _ using hω) (t • farBump n)
    hS (ae_of_all _ fun ω hω => by
      have hs := hω.2
      have hdis := disjoint_fwdHull_of_isSafeAt (hWc ω) (tsupport_subset_H _) hs
      refine ⟨mem_univ ω, ⟨hs.1, ?_⟩, hWc ω, (hγ ω).segDriver_spec.1⟩
      exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ : ℂ => t) _) hdis)
  filter_upwards [hcl] with ω hω hωE
  have hcoe : (⇑(t • farBump n) : ℂ → ℝ) = t • ⇑(farBump n) := by
    funext y
    simp
  have e1 : (fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 a k (h ω') (t • farBump n) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * ((t * Chart.chartTransport (hc ω') 1 a k (h ω') (farBump n) : ℝ) : ℂ)) := by
    funext ω'
    rw [map_smul, smul_eq_mul]
  rw [e1] at hω
  rw [hω hωE, map_smul, smul_eq_mul, hcoe, Coupling.MartMeans.loewnerGreenEnergy_smul, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The tested mean of the far bump is `farMean` on its safe event.** -/
theorem ae_chartTransport_farBump_eq (hκ : 0 < κ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (a k : ℝ) (p : ℝ≥0) (M : Ω → DistOn upperHalfPlaneOpens) {d : Ω → ℝ}
    (hmean : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ p →
      Chart.chartTransport (hc ω) 1 a k (M ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) p
          (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
            (geomRW (fun t ω => segDriver (γ ω) t) xR) d ω p) z * ψ z)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ω ∈ safeSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) univ (farBump n) δ p →
      Chart.chartTransport (hc ω) 1 a k (M ω) (farBump n) = farMean κ ρL ρR γ xL xR n p (d ω) ω := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  set ζ : Ω → ℝ≥0∞ := fun ω => capLife (γ ω) with hζdef
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω => (hγ ω).segDriver_spec.2.1
  have hreg : ∀ ω, IsForceReg W (geomLW W xL) (geomRW W xR) ζ ω := PocketCoupling.isForceReg_segDriver hγ xL xR
  filter_upwards [hmean (farBump n)] with ω h2 hω
  have hs : IsSafeAt (tsupport (farBump n)) δ p p (ζ ω) (W · ω) p := hω.2
  have hlive : (p : ℝ≥0∞) < ζ ω := hs.1
  have hord := (hreg ω).2.2.2.2 p hlive
  have hdis : Disjoint (tsupport (farBump n)) (fwdHull (rpath (W · ω)) p) :=
    disjoint_fwdHull_of_isSafeAt (hWc ω) (tsupport_subset_H _) hs
  have hav : ω ∈ Restart.DomainMarkov.avoidSet W ζ (farBump n) p := ⟨hlive, hdis⟩
  rw [h2 hav]
  exact integral_couplingMean_phase (vL := fun i t => geomLW W xL i t ω) (vR := fun i t => geomRW W xR i t ω) hκ
    (farBump n).continuous (farBump n).hasCompactSupport (hWc ω) (tsupport_subset_H _) hs hδ le_rfl
    hord.1 hord.2 (isBoundedHarmonicExtension_phaseProc (ρL := ρL) (ρR := ρR) hκ d (hord.1 0) (hord.2 0))

/-- The Green energy of a test function safe at `r` is nonnegative. -/
theorem loewnerGreenEnergy_nonneg_of_isSafeAt {w : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞}
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀}) (hw0 : w 0 = 0) {ψ : TestOn upperHalfPlaneOpens} {δ N : ℝ}
    {σ₀ r : ℝ≥0} (hs : IsSafeAt (tsupport ψ) δ N σ₀ ζ₀ w r) :
    0 ≤ loewnerGreenEnergy (fun s : ℝ => w s.toNNReal) r ψ := by
  have hw : ContinuousOn (rpath w) (Icc 0 (r : ℝ)) := continuousOn_rpath hwc hs.1
  have hc := continuous_clampDrv r.coe_nonneg hw
  have h0 : clampDrv (rpath w) r 0 = 0 := by
    simp [clampDrv, rpath, hw0]
  have hdis : Disjoint (tsupport ψ) (fwdHull (clampDrv (rpath w) r) r) :=
    Set.disjoint_left.2 fun z hz =>
      (mem_diff_fwdHull_clampDrv r.coe_nonneg hw (tsupport_subset_H ψ hz) (hs.2.2.2 z hz).1).2
  have hE := Coupling.loewnerGreenEnergy_nonneg hc h0 r.coe_nonneg ψ hdis
  have he : loewnerGreenEnergy (clampDrv (rpath w) r) r ψ = loewnerGreenEnergy (fun s : ℝ => w s.toNNReal) r ψ := by
    simp only [loewnerGreenEnergy, fwdMap_clampDrv_of_le le_rfl]
    rfl
  rwa [he] at hE

/-- The constant of the Lipschitz bound of the energy of the far bump at safe level `1/(m+1)`. -/
def farConst (n m : ℕ) : ℝ := (2 / (1 / ((m : ℝ) + 1)) * ∫ z, |farBump n z|) ^ 2

theorem farConst_pos (n m : ℕ) : 0 < farConst n m := by
  have h1 : (∫ z, |farBump n z|) = ∫ z, farBump n z :=
    integral_congr_ae (Eventually.of_forall fun z => abs_of_nonneg (farBump_nonneg n z))
  have h2 := integral_farBump_pos n
  unfold farConst
  rw [h1]
  positivity

/-- **Continuity and positivity of the far-bump coefficients** along a path on which `ψ_n` is safe at `t`: the mean
`a_p = farMean_p(0)` and the window weight `J_p = farGap_p` are continuous on `[s, t]` and `J > 0` there (`s > 0`). -/
theorem farMean_farGap_props (hκ : 0 < κ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) {s t : ℝ≥0}
    (hs : 0 < s) {ω : Ω}
    (hω : ω ∈ safeSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) univ (farBump n) δ t) :
    ContinuousOn (fun p => farMean κ ρL ρR γ xL xR n p 0 ω) (Icc s t) ∧
      ContinuousOn (fun p => farGap κ ρL ρR γ xL xR n p ω) (Icc s t) ∧
      ∀ p ∈ Icc s t, 0 < farGap κ ρL ρR γ xL xR n p ω := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  have hreg := PocketCoupling.isForceReg_segDriver hγ xL xR ω
  have hsafe : IsSafeAt (tsupport (farBump n)) δ t t (capLife (γ ω)) (W · ω) t := hω.2
  have hA := continuousOn_phaseInt (κ := κ) (ρL := ρL) (ρR := ρR) (farBump n).continuous
    (farBump n).hasCompactSupport hreg.2.1 hreg.2.2.1 hreg.2.2.2.1 (tsupport_subset_H _) hsafe hδ 0
  have hB := continuousOn_phaseInt (κ := κ) (ρL := ρL) (ρR := ρR) (farBump n).continuous
    (farBump n).hasCompactSupport hreg.2.1 hreg.2.2.1 hreg.2.2.2.1 (tsupport_subset_H _) hsafe hδ 1
  have hsub : Icc s t ⊆ Iic t := fun p hp => hp.2
  have hgap : ∀ p, farGap κ ρL ρR γ xL xR n p ω = farMean κ ρL ρR γ xL xR n p 1 ω -
      farMean κ ρL ρR γ xL xR n p 0 ω := fun p => by
    rw [farMean_eq_add_mul (c := 1), one_mul]; ring
  refine ⟨hA.mono hsub, ?_, fun p hp => ?_⟩
  · exact ((hB.sub hA).mono hsub).congr fun p _ => hgap p
  · have hp0 : 0 < p := lt_of_lt_of_le hs hp.1
    have hlive : (p : ℝ≥0∞) < capLife (γ ω) :=
      lt_of_le_of_lt (by exact_mod_cast hp.2) hsafe.1
    have hsep := geomLW_lt_geomRW_of_pos (fun ω => (hγ ω).segDriver_spec.2.1) xL xR 0 0 hp0 hlive
    exact phaseGap_pos hκ (farBump n).continuous (farBump n).hasCompactSupport (farBump_nonneg n)
      (integral_farBump_pos n) hreg.2.1 (tsupport_subset_H _) hsafe hδ hp.2 hsep

end Kernel

section Pair

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Gaussian tails for the increment of the far-bump mean between two relative times** `q < r`: the field is
conditionally Gaussian given `𝓜 q ⊇ 𝓗 q` and given `𝓜 r ⊇ 𝓜 q ∨ 𝓗 r` (kernels `hcond`, `hcond'`) with chart-transported
means of the phase words `d`, `d'` (`hmean`, `hmean'`). On the event that the far bump `ψ_n` is safe at level
`1/(m+1)` at time `r`, the mean moved by at least `b` with probability at most `2 exp(−b²/(2C(r − q)))`. -/
theorem measure_farMean_increment_le [IsProbabilityMeasure P] (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ}
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hpre : IsPrefixAdapted 𝓗 γ)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓗 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓗 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓗 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) {q r : ℝ≥0} (hqr : q < r) (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓜qr : 𝓜 q ≤ 𝓜 r) (h𝓜r : 𝓜 r ≤ mΩ)
    (h𝓗q : 𝓗 q ≤ 𝓜 q) (h𝓗r : 𝓗 r ≤ 𝓜 r) (M M' : Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)))
    (hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) r) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 r] ω =
        Complex.exp (Complex.I * (M' ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) r))
            φ φ : ℝ) : ℂ)))
    {d d' : Ω → ℝ}
    (hmean : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ q →
      Chart.chartTransport (hc ω) 1 a k (M ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
            (geomRW (fun t ω => segDriver (γ ω) t) xR) d ω q) z * ψ z)
    (hmean' : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ r →
      Chart.chartTransport (hc ω) 1 a k (M' ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) r
          (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
            (geomRW (fun t ω => segDriver (γ ω) t) xR) d' ω r) z * ψ z)
    (n m : ℕ) {b : ℝ} (hb : 0 < b) :
    P (safeSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) univ (farBump n) (1 / ((m : ℝ) + 1)) r ∩
        {ω | b ≤ |farMean κ ρL ρR γ xL xR n r (d' ω) ω - farMean κ ρL ρR γ xL xR n q (d ω) ω|}) ≤
      2 * ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * (farConst n m * ((r : ℝ) - q)))))) := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  set ζ : Ω → ℝ≥0∞ := fun ω => capLife (γ ω) with hζdef
  have hWa : AdaptedBefore 𝓗 ζ W := adaptedBefore_segDriver_of_isDrivenCurve hγ hpre
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω => (hγ ω).segDriver_spec.2.1
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => (hγ ω).segDriver_spec.1
  have hG0 : MeasurableSet[𝓗 0] (univ : Set Ω) := MeasurableSet.univ
  have hGc : ∀ ω ∈ (univ : Set Ω), ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω _ => hWc ω
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have h𝓜q : 𝓜 q ≤ mΩ := h𝓜qr.trans h𝓜r
  have h0q : 𝓗 0 ≤ 𝓜 q := (𝓗.mono (zero_le : (0 : ℝ≥0) ≤ q)).trans h𝓗q
  have h0r : 𝓗 0 ≤ 𝓜 r := h0q.trans h𝓜qr
  have h𝓗0 : 𝓗 0 ≤ mΩ := 𝓗.le 0
  set Sq := safeSet W ζ univ (farBump n) δ q with hSqdef
  set Sr := safeSet W ζ univ (farBump n) δ r with hSrdef
  have hSq : MeasurableSet[𝓜 q] Sq := h𝓗q _ (measurableSet_safeSet hWa hGc hG0 (tsupport_subset_H _) hδ q)
  have hSr : MeasurableSet[𝓜 r] Sr := h𝓗r _ (measurableSet_safeSet hWa hGc hG0 (tsupport_subset_H _) hδ r)
  have hSrq : Sr ⊆ Sq := fun ω hω =>
    ⟨mem_univ ω, isSafeAt_self_of (hω.2.anti (hWc ω) (tsupport_subset_H _) hqr.le)⟩
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝓗0 _ (hdom z))
      (fun z => (hfwd z).mono h𝓗0 le_rfl) (fun z => (hliftm z).mono h𝓗0 le_rfl) hliftc hh 1 a k
  set X : Ω → ℝ := fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) (farBump n) with hXdef
  have hXm : Measurable X := (LQGMetric.measurable_distOn_apply (farBump n)).comp hX
  -- the two kernels on the safe events
  have hkq := fun t => ae_condExp_farBump_eq (P := P) hγ hc (fun z => h0q _ (hdom z))
    (fun z => (hfwd z).mono h0q le_rfl) (fun z => (hliftm z).mono h0q le_rfl) hliftc hh a k q h𝓜q M hcond n hSq t
  have hkr := fun t => ae_condExp_farBump_eq (P := P) hγ hc (fun z => h0r _ (hdom z))
    (fun z => (hfwd z).mono h0r le_rfl) (fun z => (hliftm z).mono h0r le_rfl) hliftc hh a k r h𝓜r M' hcond' n hSr t
  -- the energies
  set Vq := energyK W ζ univ (farBump n) δ q with hVqdef
  set Vr := energyK W ζ univ (farBump n) δ r with hVrdef
  have hVq : Measurable[𝓜 q] Vq := (measurable_energyK hWa hGc hG0 (tsupport_subset_H _) hδ
    (farBump n).continuous.measurable q).mono h𝓗q le_rfl
  have hVr : Measurable[𝓜 r] Vr := (measurable_energyK hWa hGc hG0 (tsupport_subset_H _) hδ
    (farBump n).continuous.measurable r).mono h𝓗r le_rfl
  have hVqe : ∀ ω ∈ Sq, Vq ω = loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) q (farBump n) := fun ω hω => by
    simp only [hVqdef, energyK, show ω ∈ safeSet W ζ univ (farBump n) δ q from hω, ↓reduceIte]
    rfl
  have hVre : ∀ ω ∈ Sr, Vr ω = loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) r (farBump n) := fun ω hω => by
    simp only [hVrdef, energyK, show ω ∈ safeSet W ζ univ (farBump n) δ r from hω, ↓reduceIte]
    rfl
  have hVqi : Sq.indicator (fun ω => loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) q (farBump n)) = Vq := by
    funext ω
    by_cases hω : ω ∈ Sq
    · rw [indicator_of_mem hω, hVqe ω hω]
    · rw [indicator_of_notMem hω]
      simp only [hVqdef, energyK, show ω ∉ safeSet W ζ univ (farBump n) δ q from hω, ↓reduceIte]
  have hVri : Sr.indicator (fun ω => loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) r (farBump n)) = Vr := by
    funext ω
    by_cases hω : ω ∈ Sr
    · rw [indicator_of_mem hω, hVre ω hω]
    · rw [indicator_of_notMem hω]
      simp only [hVrdef, energyK, show ω ∉ safeSet W ζ univ (farBump n) δ r from hω, ↓reduceIte]
  -- measurable versions of the means
  obtain ⟨μq, hμqm, hμqe⟩ := exists_measurable_eq_on_of_condCharFun h𝓜q hXm hSq (by rw [hVqi]; exact hVq) hkq
  obtain ⟨μr, hμrm, hμre⟩ := exists_measurable_eq_on_of_condCharFun h𝓜r hXm hSr (by rw [hVri]; exact hVr) hkr
  have hcq : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ Sq → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝓜 q] ω =
      cexp (I * ((t * μq ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * Vq ω)) : ℝ) : ℂ) := fun t => by
    filter_upwards [hkq t, hμqe] with ω h1 h2 hω
    rw [h1 hω, h2 hω, hVqe ω hω]
  have hcr : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ Sr → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝓜 r] ω =
      cexp (I * ((t * μr ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * Vr ω)) : ℝ) : ℂ) := fun t => by
    filter_upwards [hkr t, hμre] with ω h1 h2 hω
    rw [h1 hω, h2 hω, hVre ω hω]
  have hV0q : ∀ ω ∈ Sq, 0 ≤ Vq ω := fun ω hω => by
    rw [hVqe ω hω]; exact loewnerGreenEnergy_nonneg_of_isSafeAt (hWc ω) (hW0 ω) hω.2
  have hV0r : ∀ ω ∈ Sr, 0 ≤ Vr ω := fun ω hω => by
    rw [hVre ω hω]; exact loewnerGreenEnergy_nonneg_of_isSafeAt (hWc ω) (hW0 ω) hω.2
  have hd : 0 < farConst n m * ((r : ℝ) - q) :=
    mul_pos (farConst_pos n m) (sub_pos.2 (NNReal.coe_lt_coe.2 hqr))
  have hmain := measure_increment_le (P := P) h𝓜qr h𝓜r hXm hμqm hVq hμrm hVr hSq hSr hSrq hV0q hV0r hcq hcr hb hd
  -- the means are the far means, and the energy decreased by at most `C (r − q)`
  have hidq := ae_chartTransport_farBump_eq (P := P) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) hκ hγ hc a k q M
    hmean n hδ
  have hidr := ae_chartTransport_farBump_eq (P := P) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) hκ hγ hc a k r M'
    hmean' n hδ
  have hbad : ∀ᵐ ω ∂P, ω ∈ Sr → μr ω = farMean κ ρL ρR γ xL xR n r (d' ω) ω ∧
      μq ω = farMean κ ρL ρR γ xL xR n q (d ω) ω := by
    filter_upwards [hμqe, hμre, hidq, hidr] with ω h1 h2 h3 h4 hω
    exact ⟨(h2 hω).trans (h4 hω), (h1 (hSrq hω)).trans (h3 (hSrq hω))⟩
  have hsub : Sr ∩ {ω | b ≤ |farMean κ ρL ρR γ xL xR n r (d' ω) ω - farMean κ ρL ρR γ xL xR n q (d ω) ω|} ⊆
      (Sr ∩ {ω | b ≤ |μr ω - μq ω| ∧ Vq ω - Vr ω ≤ farConst n m * ((r : ℝ) - q)}) ∪
        {ω | ¬ (ω ∈ Sr → μr ω = farMean κ ρL ρR γ xL xR n r (d' ω) ω ∧
          μq ω = farMean κ ρL ρR γ xL xR n q (d ω) ω)} := by
    rintro ω ⟨hωS, hωb⟩
    by_cases hgood : ω ∈ Sr → μr ω = farMean κ ρL ρR γ xL xR n r (d' ω) ω ∧
        μq ω = farMean κ ρL ρR γ xL xR n q (d ω) ω
    · left
      obtain ⟨e1, e2⟩ := hgood hωS
      refine ⟨hωS, by rw [e1, e2]; exact hωb, ?_⟩
      have hs : IsSafeAt (tsupport (farBump n)) δ r r (ζ ω) (W · ω) r := hωS.2
      have hlip : |loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) q (farBump n) -
          loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) r (farBump n)| ≤
          ((r : ℝ) - q) * (2 / δ * ∫ z, |farBump n z|) ^ 2 :=
        hs.abs_loewnerGreenEnergy_sub_le (farBump n).continuous (farBump n).hasCompactSupport (hWc ω)
          (tsupport_subset_H _) hδ hqr.le le_rfl
      rw [hVqe ω (hSrq hωS), hVre ω hωS]
      have e : ((r : ℝ) - q) * (2 / δ * ∫ z, |farBump n z|) ^ 2 = farConst n m * ((r : ℝ) - q) := by
        rw [farConst, hδdef]; ring
      rw [← e]
      exact (le_abs_self _).trans hlip
    · exact Or.inr hgood
  calc P (Sr ∩ {ω | b ≤ |farMean κ ρL ρR γ xL xR n r (d' ω) ω - farMean κ ρL ρR γ xL xR n q (d ω) ω|})
      ≤ P ((Sr ∩ {ω | b ≤ |μr ω - μq ω| ∧ Vq ω - Vr ω ≤ farConst n m * ((r : ℝ) - q)}) ∪
        {ω | ¬ (ω ∈ Sr → μr ω = farMean κ ρL ρR γ xL xR n r (d' ω) ω ∧
          μq ω = farMean κ ρL ρR γ xL xR n q (d ω) ω)}) := measure_mono hsub
    _ ≤ P (Sr ∩ {ω | b ≤ |μr ω - μq ω| ∧ Vq ω - Vr ω ≤ farConst n m * ((r : ℝ) - q)}) +
        P {ω | ¬ (ω ∈ Sr → μr ω = farMean κ ρL ρR γ xL xR n r (d' ω) ω ∧
          μq ω = farMean κ ρL ρR γ xL xR n q (d ω) ω)} := measure_union_le _ _
    _ = P (Sr ∩ {ω | b ≤ |μr ω - μq ω| ∧ Vq ω - Vr ω ≤ farConst n m * ((r : ℝ) - q)}) := by
        rw [ae_iff.1 hbad, add_zero]
    _ ≤ _ := hmain

end Pair

end InteractingSLE.Sec7.PhaseCont
