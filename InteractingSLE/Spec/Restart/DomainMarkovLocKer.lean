/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovLocP
import InteractingSLE.Spec.Restart.DomainMarkovMain
import InteractingSLE.Spec.Exist.Param12Conv

/-!
# The domain Markov step, locality III: transfer of the member identities to the conditional laws

Packet PROVE-DOMAINMARKOV3. Tools for moving the `P`-side member identities of the restarted field
(`setIntegral_lapTest_restart`) to almost every conditional law `ν = condExpKernel P 𝓓_T ω₀`:

* `map_eq_fieldLaw0_of_isZBGFFProcess`: a field whose centred pairings form a zero-boundary GFF has the law
  `fieldLaw0 u₀` (the proof of `Exist.Param12.map_field_eq_zbLaw_map`, which assumes a whole coupling, for the process
  alone);
* `IsProjIndepMeasure.map_sub`: projection independence survives subtracting a deterministic harmonic mean;
* `ae_integral_condExpKernel_eq`: identities `∫_B X = ∫_B Y` for every `B ∈ 𝓔` hold under almost every
  `condExpKernel P 𝓔 ω₀`;
* `indK`, `tsupport_indK`, `measurableSet_safeU_indK`, `mem_safeU_indK_iff`: the safe event of a finite family of
  rational closed balls at a fixed time (`DomainMarkov.safeU` of the indicator of `ballsK F`), and its pathwise meaning
  (`s < ζ` and `ballsK F` avoids `K_s`);
* **`ae_isZBGFFProcess_restartField`**: under almost every conditional law the restarted field is a Gaussian free
  field with the restarted word's harmonic mean (from PROVE-DOMAINMARKOV2's items (E) and (S), as in
  `kernelRestartCouplingStatement_of_locality`, which does not use locality for this).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H fwdHull zeroGFFTestCov)
open scoped ENNReal NNReal RealInnerProductSpace

universe u

namespace InteractingSLE.Restart.DomainMarkov

open LQGMetric LQGMetric.MarkovZB LocalSets Coupling Ito Sec7 Sec7.Aux122Disint Sec2.Restart Sec5.Markov LocalExt
open QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### Laws of fields -/

section Law

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

open Exist.Param12 in
/-- **The law of a field whose centred pairings form a zero-boundary GFF** is the zero-boundary GFF law shifted by
the harmonic mean (`Exist.Param12.map_field_eq_zbLaw_map` for the process alone). -/
theorem map_eq_fieldLaw0_of_isZBGFFProcess {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X) {u₀ : ℂ → ℝ} (hcont : ContinuousOn u₀ H)
    (g₁ : IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) ν) :
    ν.map X = fieldLaw0 u₀ := by
  rw [fieldLaw0_eq_map]
  have g₂ : IsZBGFFProcess upperHalfPlaneOpens (fun φ (g : DistOn upperHalfPlaneOpens) => g φ)
      (zbLaw upperHalfPlaneOpens) := (isZeroBoundaryGFF_zbLaw (fun _ hz => hz)).process
  have e := g₁.map_eq g₂
  obtain ⟨c, hc⟩ : ∃ c : TestOn upperHalfPlaneOpens → ℝ, c = fun φ => ∫ z, u₀ z * φ z := ⟨_, rfl⟩
  have hadd : Measurable fun f : TestOn upperHalfPlaneOpens → ℝ => f + c := measurable_id.add_const c
  have hT : Measurable fun g : DistOn upperHalfPlaneOpens => g + meanH u₀ :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const _
  have hd₁ : distEval upperHalfPlaneOpens ∘ X =
      (fun f => f + c) ∘ zbPath (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) := by
    funext ω φ; simp [zbPath, distEval, hc]
  have hd₂ : distEval upperHalfPlaneOpens ∘ (fun g => g + meanH u₀) =
      (fun f => f + c) ∘ zbPath (fun φ (g : DistOn upperHalfPlaneOpens) => g φ) := by
    funext g φ
    have := meanH_apply_eq hcont φ
    simp only [Function.comp_apply, distEval, zbPath, Pi.add_apply, hc]
    rw [← this]
    rfl
  have hz₁ : Measurable (zbPath (fun φ ω => X ω φ - ∫ z, u₀ z * φ z)) := measurable_pi_iff.2 g₁.measurable
  have hz₂ : Measurable (zbPath fun φ (g : DistOn upperHalfPlaneOpens) => g φ) :=
    measurable_pi_iff.2 g₂.measurable
  have hD : ν.map (distEval upperHalfPlaneOpens ∘ X) =
      (zbLaw upperHalfPlaneOpens).map (distEval upperHalfPlaneOpens ∘ fun g => g + meanH u₀) := by
    rw [hd₁, hd₂, ← Measure.map_map hadd hz₁, ← Measure.map_map hadd hz₂, e]
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hS : MeasurableSet (distEval upperHalfPlaneOpens ⁻¹' t) := measurable_distEval _ ht
  have := congrArg (fun μ : Measure (TestOn upperHalfPlaneOpens → ℝ) => μ t) hD
  rw [Measure.map_apply ((measurable_distEval _).comp hXm) ht,
    Measure.map_apply ((measurable_distEval _).comp hT) ht] at this
  change (ν.map X) (distEval upperHalfPlaneOpens ⁻¹' t) =
    ((zbLaw upperHalfPlaneOpens).map fun g => g + meanH u₀) (distEval upperHalfPlaneOpens ⁻¹' t)
  rw [Measure.map_apply hXm hS, Measure.map_apply hT hS]
  exact this

/-- **Projection independence survives subtracting a harmonic mean**: if the law `μ` is projection-independent at
`V ⊆ ℍ`, so is its translate by `−c`, for a deterministic `c` harmonic on `ℍ` (it annihilates the Dirichlet
directions and its phase cancels). -/
theorem IsProjIndepMeasure.map_sub {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H) {μ : Measure (DistOn upperHalfPlaneOpens)}
    (hμ : IsProjIndepMeasure V μ) {c : DistOn upperHalfPlaneOpens} (hc : IsHarmonicDistOn c H) :
    IsProjIndepMeasure V (μ.map fun x => x - c) := by
  intro f Ξ
  have hm : Measurable fun x : DistOn upperHalfPlaneOpens => x - c := measurable_sub_distOnConst c
  have hc0 : c (lapTest V f) = 0 :=
    IsHarmonicDistOn.apply_lapTest_eq_zero QuantumZipper.isOpen_H hc (show V ≤ upperHalfPlaneOpens from hVH) hVH f
  rw [integral_map hm.aemeasurable (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable,
    integral_map hm.aemeasurable (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable]
  have e : ∀ x : DistOn upperHalfPlaneOpens, Complex.exp (Complex.I * ((x - c) (lapTest V f + Ξ) : ℂ)) =
      Complex.exp (-(Complex.I * (c Ξ : ℂ))) * Complex.exp (Complex.I * (x (lapTest V f + Ξ) : ℂ)) := fun x => by
    rw [← Complex.exp_add, sub_apply, map_add c, hc0, zero_add]
    congr 1
    push_cast
    ring
  have e' : ∀ x : DistOn upperHalfPlaneOpens, Complex.exp (Complex.I * ((x - c) Ξ : ℂ)) =
      Complex.exp (-(Complex.I * (c Ξ : ℂ))) * Complex.exp (Complex.I * (x Ξ : ℂ)) := fun x => by
    rw [← Complex.exp_add, sub_apply]
    congr 1
    push_cast
    ring
  simp_rw [e, e', integral_const_mul, hμ f Ξ]
  ring

end Law

/-! ### Transfer to the conditional laws -/

section Transfer

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P]

/-- **Identities on every event of `𝓔` hold under almost every conditional law given `𝓔`.** -/
theorem ae_integral_condExpKernel_eq (h𝓔 : 𝓔 ≤ mΩ) {X Y : Ω → ℂ} (hX : Integrable X P) (hY : Integrable Y P)
    (hXY : ∀ B, MeasurableSet[𝓔] B → ∫ ω in B, X ω ∂P = ∫ ω in B, Y ω ∂P) :
    ∀ᵐ ω₀ ∂P, ∫ ω, X ω ∂(condExpKernel P 𝓔 ω₀) = ∫ ω, Y ω ∂(condExpKernel P 𝓔 ω₀) := by
  have hc : P[Y | 𝓔] =ᵐ[P] P[X | 𝓔] :=
    ae_eq_condExp_of_forall_setIntegral_eq h𝓔 hX (fun _ _ _ => integrable_condExp.integrableOn)
      (fun B hB _ => by rw [setIntegral_condExp h𝓔 hY hB, hXY B hB])
      stronglyMeasurable_condExp.aestronglyMeasurable
  filter_upwards [hc, condExp_ae_eq_integral_condExpKernel h𝓔 hX,
    condExp_ae_eq_integral_condExpKernel h𝓔 hY] with ω₀ h1 h2 h3
  rw [← h2, ← h3, h1]

end Transfer

/-! ### The safe event of a finite family of rational closed balls -/

section Safe

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The indicator of `ballsK F` (its topological support is `ballsK F`). -/
def indK (F : Finset (ℚ × ℚ × ℚ)) : ℂ → ℝ := (ballsK F).indicator 1

theorem tsupport_indK (F : Finset (ℚ × ℚ × ℚ)) : tsupport (indK F) = ballsK F := by
  have hs : Function.support (indK F) = ballsK F := by
    ext z
    by_cases hz : z ∈ ballsK F <;> simp [indK, hz]
  rw [tsupport, hs]
  exact (isCompact_ballsK F).isClosed.closure_eq

omit mΩ in
/-- Hulls at `s` of two drivers agreeing before `a > s` coincide. -/
theorem fwdHull_rpath_congr_of_lt {w w' : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < a → w t = w' t)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < a) :
    fwdHull (fun r : ℝ => w r.toNNReal) (s : ℝ) = fwdHull (fun r : ℝ => w' r.toNNReal) (s : ℝ) := by
  obtain ⟨t₂, hst₂, ht₂a⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hst₂' : (s : ℝ) < t₂ := by exact_mod_cast hst₂
  refine InteractingSLE.fwdHull_eq_of_eqOn s.coe_nonneg hst₂' fun r hr => hww' _ ?_
  refine lt_of_le_of_lt ?_ ht₂a
  have : r.toNNReal ≤ t₂ := Real.toNNReal_le_iff_le_coe.2 hr.2
  exact_mod_cast this

/-- **The safe event of `F` at `s` is measurable at time `s`** for a driver adapted before `ζ` and continuous before
`ζ` on every path. -/
theorem measurableSet_safeU_indK {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hWa : AdaptedBefore 𝓖 ζ W) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H) (s : ℝ≥0) :
    MeasurableSet[𝓖 s] (safeU W ζ univ (indK F) s) :=
  MeasurableSet.iUnion fun _ => measurableSet_safeSet hWa (fun ω _ => hc ω) MeasurableSet.univ
    (by rw [tsupport_indK]; exact hFH) (by positivity) s

omit mΩ in
/-- **The pathwise meaning of the safe event**: for a driver continuous before `ζ` with `W₀ = 0`, the path is in the
safe event of `F` at `s` iff `s < ζ` and `ballsK F` avoids the hull `K_s`. -/
theorem mem_safeU_indK_iff {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hw0 : W 0 ω = 0)
    {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H) (s : ℝ≥0) :
    ω ∈ safeU W ζ univ (indK F) s ↔
      (s : ℝ≥0∞) < ζ ω ∧ Disjoint (ballsK F) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := by
  have hKH : tsupport (indK F) ⊆ H := by rw [tsupport_indK]; exact hFH
  constructor
  · intro hω
    obtain ⟨m, hm⟩ := mem_iUnion.1 hω
    have hs : IsSafeAt (tsupport (indK F)) (1 / ((m : ℝ) + 1)) s s (ζ ω) (W · ω) s := hm.2
    have hd := disjoint_fwdHull_of_isSafeAt hc hKH hs
    rw [tsupport_indK] at hd
    exact ⟨hs.1, hd⟩
  · rintro ⟨hlt, hd⟩
    have halive : ∀ z ∈ tsupport (indK F), ∃ v, QuantumZipper.IsForwardSol (rpath (W · ω)) z s v := fun z hz =>
      exists_isForwardSol_of_mem s.coe_nonneg ⟨hKH hz, fun hzK => by
        rw [tsupport_indK] at hz
        exact Set.disjoint_left.1 hd hz hzK⟩
    have hKc : IsCompact (tsupport (indK F)) := by rw [tsupport_indK]; exact isCompact_ballsK F
    obtain ⟨δ, hδ, hs⟩ := exists_isSafeAt_self hc hw0 hKc hKH hlt halive
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact mem_safeU_of_isSafeAt (mem_univ ω) (hs.mono hm.le le_rfl le_rfl)

end Safe

/-! ### The law of the restarted field under the conditional laws -/

section GFF

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {T : Ω → ℝ≥0}

/-- **Under almost every conditional law given `𝓓_T`, the restarted field is a Gaussian free field with the restarted
word's harmonic mean** (on `{T < ζ}`). This is the time-`0` clause of the restarted coupling, obtained from
PROVE-DOMAINMARKOV2's items (E) and (S) exactly as in `kernelRestartCouplingStatement_of_locality` (no locality is
used). -/
theorem ae_isZBGFFProcess_restartField (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) :
    ∀ᵐ ω₀ ∂P, (T ω₀ : ℝ≥0∞) < ζ ω₀ → ∀ u₀ : ℂ → ℝ,
      IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => VL i (T ω₀) ω₀ - W (T ω₀) ω₀)
          (fun j => VR j (T ω₀) ω₀ - W (T ω₀) ω₀))
        (forceJumpSet (fun i => VL i (T ω₀) ω₀ - W (T ω₀) ω₀) (fun j => VR j (T ω₀) ω₀ - W (T ω₀) ω₀)) u₀ →
      IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => restartField κ (h ω, K ω) φ - ∫ z, u₀ z * φ z)
        (condExpKernel P hT.measurableSpace ω₀) := by
  obtain ⟨𝓖, W', VL', VR', B', hev⟩ := ae_isIntegratedSLEEvolution_condExpKernel_restart hC.1 hX hT
  obtain ⟨N, hNm, hN0, hN⟩ := exists_isGoodOff hC.1 hX hT
  have hS := ae_setIntegral_cexp_eq_cfAt_restart hC hκ hX hT hKm hK hNm hN0 hN
  have hle : hT.measurableSpace ≤ mΩ := hT.measurableSpace_le
  have hNν := ae_ae_condExpKernel hle (measure_eq_zero_iff_ae_notMem.1 hN0)
  have hKm' : Measurable K := hKm.mono hle le_rfl
  have hh' : Measurable fun ω => restartField κ (h ω, K ω) :=
    (measurable_restartField κ).comp (hC.2.1.prodMk hKm')
  filter_upwards [hev, hS, hNν, ae_rsX_eq (T := T) hC.1] with ω₀ hev0 hS0 hN0' hword hTζ u₀ hu₀
  obtain ⟨hE', hag⟩ := hev0 hTζ
  obtain ⟨hΘL, hΘR, -⟩ := hword hTζ
  rw [hΘL, hΘR] at hE'
  have hagZ : ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), ∀ t, W' t ω = zW N ζ W VL VR T t ω ∧
      (∀ i, VL' i t ω = zVL N ζ W VL VR T i t ω) ∧ ∀ j, VR' j t ω = zVR N ζ W VL VR T j t ω := by
    filter_upwards [hag, hN0'] with ω ⟨hF, h1⟩ hωN t
    obtain ⟨e1, e2, e3⟩ := h1 t
    exact ⟨by rw [e1, zW, zData_none hωN hF], fun i => by rw [e2 i, zVL, zData_inl hωN hF],
      fun j => by rw [e3 j, zVR, zData_inr hωN hF]⟩
  have hX' := IsIntegratedSLEEvolution.isMeasurableKilledDriving hE'
  have hdy := isDyadicSampled_of_agree hX hT hNm hN hS0 hX' hagZ
  have hcf : MartMeans.IsCouplingCharFun κ ρL ρR (condExpKernel P hT.measurableSpace ω₀)
      (drivingFiltration (condExpKernel P hT.measurableSpace ω₀) hX') W' VL' VR' (restartLife ζ T)
      (fun ω => restartField κ (h ω, K ω)) := fun τ hτ hτζ uτ huτ φ =>
    condExp_cexp_eq_frozenRHS_of_dyadic hE' (bheProc κ ρL ρR W' VL' VR')
      (fun ω s => isBoundedHarmonicExtension_bheProc ω s) _
      (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hh') hX' hdy hτ hτζ uτ huτ φ
  have h0 : ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), 0 < restartLife ζ T ω ∧
      ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < restartLife ζ T ω} ∧ W' 0 ω = 0 ∧
      (∀ i, VL' i 0 ω = VL i (T ω₀) ω₀ - W (T ω₀) ω₀) ∧ ∀ j, VR' j 0 ω = VR j (T ω₀) ω₀ - W (T ω₀) ω₀ := by
    filter_upwards [hE'.2.2.2.2, hag] with ω hp hω
    exact ⟨tsub_pos_iff_lt.2 hω.1, hp.2.2.2.1, hp.1, hp.2.1, hp.2.2.1⟩
  exact Lemma71J.isZBGFFProcess_of_isCouplingCharFun hcf hh' h0 hu₀

end GFF

end InteractingSLE.Restart.DomainMarkov
