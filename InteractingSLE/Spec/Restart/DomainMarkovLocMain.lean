/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovLocKer

/-!
# The domain Markov step, locality IV: `KernelRestartLocalityStatement κ` and Aux. lemma 53 in kernel form

Packet PROVE-DOMAINMARKOV3. Proof of the locality half of Aux. lemma 53 in kernel form (PROVE-DOMAINMARKOV2's named
input) for every `κ > 0`, hence of `KernelRestartCouplingStatement κ`.

Route (specification p. 245; the history-marked locality of PROVE-LOCEXT-O, `LocalExt.exists_condDecomp_chart`):

1. **`P`-side member identities** (`setIntegral_lapTest_restart`, `DomainMarkovLocP.lean`): at every deterministic
   restarted time `s`, on every event of `𝓓_{T+s}` on which `ballsK F` avoids the restarted hull, the restarted field
   `h'` satisfies the projection identity at `ballsU F`.
2. **Transfer** (`ae_setIntegral_restart_shift`): for the countably many rational times `s`, families `F`, rational
   combinations `Φ_k`, Dirichlet approximations `f_{k,m}` of the projection of `Φ_k`, and events `A` of the countable
   π-system generating the restarted data filtration `dF s`, the shift identity
   `∫_{A∩S} e^{i h'(Φ_k)} = projFactor (f_{k,m}) (Φ_k + Δf_{k,m}/2π) ∫_{A∩S} e^{i h'(Φ_k + Δf_{k,m}/2π)}`
   (`S` the safe event of `F` at `s`) holds under almost every conditional law `ν = condExpKernel P 𝓓_T ω₀`.
3. **Under one `ν`**: Dynkin over `A` (`setIntegral_eq_of_isPiSystem`); the limit `m → ∞` identifies the
   characteristic functional of the law of `h'` on `A ∩ S` with that of its Gaussian resampling at `ballsU F`, at the
   countably many `Φ_k`, so the law is resampling invariant (`ext_of_integral_cexp_ratComb`), hence
   projection-independent (`isProjIndepMeasure_of_shift`); every event of the `ν`-augmented driving filtration of the
   versions `W'` before `s` is `ν`-a.e. an event of `dF s`.
4. **Locality** at every stopping time of the `ν`-driving filtration of `W'`: `isLocalSet_hull_of_members`
   (`DomainMarkovLocCrit.lean`) for the centred field `h' − 𝔥'₀`, `𝔥'₀` the harmonic mean of the restarted word.

Main results: `isProjIndepMeasure_of_shift`, `ae_setIntegral_restart_shift`, **`kernelRestartLocalityStatement`**,
**`kernelRestartCouplingStatement`**.
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

/-! ### Projection independence from the shift identities along Dirichlet approximations -/

section Resample

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Projection independence from the shift identities along Dirichlet approximations.** Let `ν` be a finite measure
and `h'` a measurable field with law `fieldLaw0 u₀` (`u₀` harmonic on `ℍ`); `G` a Borel version of the projection onto
`H(V)` for `zbLaw`; for every rational combination `Φ_k` a Dirichlet approximation `f k m` (`∇f_m → covVec_V Φ_k`,
`g(−Δf_m/2π) → G g Φ_k` `zbLaw`-almost surely). If on an event `D`, for all `k, m`,
`∫_D e^{i h'(Φ_k)} = projFactor V (f k m) (Φ_k + Δf_m/2π) · ∫_D e^{i h'(Φ_k + Δf_m/2π)}`, then the law of `h'` on `D`
is projection-independent at `V` (it equals its Gaussian resampling at `V`). -/
theorem isProjIndepMeasure_of_shift {ν : Measure Ω} [IsFiniteMeasure ν] {h' : Ω → DistOn upperHalfPlaneOpens}
    (hh' : Measurable h') {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hlaw : ν.map h' = fieldLaw0 u₀) {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hGm : Measurable G)
    (hGd : GFF.IsMarkovDecomposition V upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens))
    (f : RatComb → ℕ → zsSub (V : Set ℂ))
    (hfg : ∀ k, Tendsto (fun m => gradFeat (V : Set ℂ) (f k m).1) atTop
      (𝓝 (covVec (V : Set ℂ) (ratComb upperHalfPlaneOpens k))))
    (hfa : ∀ k, ∀ᵐ g ∂zbLaw upperHalfPlaneOpens,
      Tendsto (fun m => g (lapTest V (f k m))) atTop (𝓝 (G g (ratComb upperHalfPlaneOpens k))))
    {D : Set Ω}
    (hid : ∀ k m, ∫ ω in D, Complex.exp (Complex.I * (h' ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂ν =
      projFactor V (f k m) (ratComb upperHalfPlaneOpens k - lapTest V (f k m)) *
        ∫ ω in D, Complex.exp (Complex.I * (h' ω (ratComb upperHalfPlaneOpens k - lapTest V (f k m)) : ℂ)) ∂ν) :
    IsProjIndepMeasure V ((ν.restrict D).map h') := by
  set μ := (ν.restrict D).map h' with hμdef
  set c := meanH u₀ with hcdef
  have hμ : μ ≪ fieldLaw0 u₀ := by
    rw [← hlaw]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).map hh'
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have hcm : Measurable fun x : DistOn upperHalfPlaneOpens => x - c := measurable_sub_distOnConst c
  have heq : μ = resample G c μ := by
    refine ext_of_integral_cexp_ratComb fun k => ?_
    set Φ := ratComb upperHalfPlaneOpens k with hΦ
    rw [integral_cexp_resample hGm, integral_cexp_markovMap hGm hGd hVH]
    have hm₁ : Measurable fun x : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (x Φ : ℂ)) :=
      GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)
    have hGΦ : Measurable fun x : DistOn upperHalfPlaneOpens => G (x - c) Φ :=
      (measurable_distOn_apply Φ).comp (hGm.comp hcm)
    have hm₂ : Measurable fun x : DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * ((x Φ - G (x - c) Φ : ℝ) : ℂ)) :=
      GFF.measurable_exp_I_mul ((measurable_distOn_apply Φ).sub hGΦ)
    rw [integral_map hh'.aemeasurable hm₁.aestronglyMeasurable,
      integral_map hh'.aemeasurable hm₂.aestronglyMeasurable]
    -- the almost sure limit of the Dirichlet pairings
    have hconv : ∀ᵐ ω ∂ν, Tendsto (fun m => h' ω (lapTest V (f k m))) atTop (𝓝 (G (h' ω - c) Φ)) := by
      have hmeas : ∀ m, Measurable fun x : DistOn upperHalfPlaneOpens =>
          x (lapTest V (f k m)) - G (x - c) Φ := fun m => (measurable_distOn_apply _).sub hGΦ
      have hset : MeasurableSet {x : DistOn upperHalfPlaneOpens |
          Tendsto (fun m => x (lapTest V (f k m)) - G (x - c) Φ) atTop (𝓝 0)} :=
        measurableSet_tendsto (𝓝 0) hmeas
      have h1 := ae_fieldLaw0_of_ae_zbLaw (u₀ := u₀) hset (by
        filter_upwards [hfa k] with g hg
        simp only [hcdef, add_sub_cancel_right]
        have e : ∀ m, (g + meanH u₀) (lapTest V (f k m)) = g (lapTest V (f k m)) := fun m => by
          rw [add_apply, meanH_apply_lapTest hu₀ hVH, add_zero]
        simp_rw [e]
        exact tendsto_sub_nhds_zero_iff.2 hg)
      rw [← hlaw] at h1
      filter_upwards [(ae_map_iff hh'.aemeasurable hset).1 h1] with ω hω
      exact tendsto_sub_nhds_zero_iff.1 hω
    -- the limit of the integrals
    have hI : Tendsto (fun m => ∫ ω in D, Complex.exp (Complex.I * (h' ω (Φ - lapTest V (f k m)) : ℂ)) ∂ν)
        atTop (𝓝 (∫ ω in D, Complex.exp (Complex.I * ((h' ω Φ - G (h' ω - c) Φ : ℝ) : ℂ)) ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun m => (GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp hh')).aestronglyMeasurable)
        (integrable_const _) (fun m => Eventually.of_forall fun ω => hnorm _) ?_
      filter_upwards [ae_restrict_of_ae hconv] with ω hω
      have e : ∀ m, h' ω (Φ - lapTest V (f k m)) = h' ω Φ - h' ω (lapTest V (f k m)) := fun m => map_sub _ _ _
      simp_rw [e]
      exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).tendsto _).comp
        (tendsto_const_nhds.sub hω)
    -- the limit of the factors
    have hF : Tendsto (fun m => projFactor V (f k m) (Φ - lapTest V (f k m))) atTop
        (𝓝 (Complex.exp (((-(1 / 2) * ‖covVec (V : Set ℂ) Φ‖ ^ 2 : ℝ) : ℂ)))) := by
      simp_rw [projFactor_sub_lapTest hVH]
      refine ((Complex.continuous_exp.comp Complex.continuous_ofReal).tendsto _).comp ?_
      have h1 := ((hfg k).norm.pow 2).const_mul (1 / 2 : ℝ)
      have h2 := Filter.Tendsto.inner (𝕜 := ℝ) (hfg k) (tendsto_const_nhds (x := covVec (V : Set ℂ) Φ))
      have h3 := h1.sub h2
      rw [real_inner_self_eq_norm_sq] at h3
      convert h3 using 2
      ring
    have hL := (hF.mul hI).congr fun m => (hid k m).symm
    rw [tendsto_const_nhds_iff.1 hL, Complex.ofReal_exp, mul_comm]
  rw [heq]
  exact isProjIndepMeasure_resample hGm hGd hVH hu₀ hμ

end Resample

/-! ### The transferred shift identities -/

section Transfer

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {T : Ω → ℝ≥0} {N : Set Ω}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- On the safe event of the modified restarted data, almost surely, `s < ζ − T` and `ballsK F` avoids the hull of
the restarted driver at `s`. -/
theorem ae_safe_restartDrv (hN0 : P N = 0) (hN : IsGoodOff N ζ W VL VR T) {F : Finset (ℚ × ℚ × ℚ)}
    (hFH : ballsK F ⊆ H) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) s →
      (s : ℝ≥0∞) < restartLife ζ T ω ∧
        Disjoint (ballsK F) (fwdHull (fun r : ℝ => restartDrv W T r.toNNReal ω) (s : ℝ)) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hωN hS
  have hw := hN.isWeakPath ω
  obtain ⟨hlt, hd⟩ := (mem_safeU_indK_iff hw.2.1 hw.1 hFH s).1 hS
  refine ⟨hlt, ?_⟩
  rwa [← fwdHull_rpath_congr_of_lt (fun t ht => (hN.eq_restart hωN ht).1) hlt]

/-- **The shift identities of the restarted field under almost every conditional law.** For any family of test
directions `fam F k m ∈ C_c^∞(ballsU F)`: for `P`-almost every `ω₀`, for all rational `s`, families `F` of rational
closed balls in `ℍ`, rational combinations `Φ_k`, `m` and events `A` of the countable π-system generating the restarted
data filtration at `s`, with `S` the safe event of `F` at `s`,
`∫_{A∩S} e^{i h'(Φ_k)} dν = projFactor (f_m) (Φ_k + Δf_m/2π) · ∫_{A∩S} e^{i h'(Φ_k + Δf_m/2π)} dν`
(`f_m = fam F k m`, `ν = condExpKernel P 𝓓_T ω₀`). -/
theorem ae_setIntegral_restart_shift (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (hNm : MeasurableSet N) (hN0 : P N = 0) (hN : IsGoodOff N ζ W VL VR T)
    (fam : ∀ F : Finset (ℚ × ℚ × ℚ), RatComb → ℕ → zsSub (ballsU F)) :
    ∀ᵐ ω₀ ∂P, ∀ (s : ℚ≥0) (F : Finset (ℚ × ℚ × ℚ)), ballsK F ⊆ H → ∀ (k : RatComb) (m : ℕ)
      (A : piClosure (dataGens N (restartLife ζ T) (fun _ _ => (0 : ℝ)) (rsData ζ W VL VR T) (s : ℝ≥0))),
      ∫ ω in (A : Set Ω) ∩ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) (s : ℝ≥0),
          Complex.exp (Complex.I * (restartField κ (h ω, K ω) (ratComb upperHalfPlaneOpens k) : ℂ))
            ∂(condExpKernel P hT.measurableSpace ω₀) =
        projFactor (ballsOpen F) (fam F k m)
            (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen F) (fam F k m)) *
          ∫ ω in (A : Set Ω) ∩ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) (s : ℝ≥0),
            Complex.exp (Complex.I * (restartField κ (h ω, K ω)
              (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen F) (fam F k m)) : ℂ))
            ∂(condExpKernel P hT.measurableSpace ω₀) := by
  refine ae_all_iff.2 fun s => ae_all_iff.2 fun F => ?_
  by_cases hFH : ballsK F ⊆ H
  swap
  · exact Eventually.of_forall fun _ h => absurd h hFH
  refine (ae_all_iff.2 fun k => ae_all_iff.2 fun m => ?_).mono fun ω₀ h _ => h
  have hc : Countable (piClosure (dataGens N (restartLife ζ T) (fun _ _ => (0 : ℝ)) (rsData ζ W VL VR T)
      (s : ℝ≥0))) := (countable_piClosure (countable_dataGens _ _ _ _ _)).to_subtype
  refine ae_all_iff.2 fun A => ?_
  set Φ := ratComb upperHalfPlaneOpens k with hΦ
  set f := fam F k m with hf
  set S := safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) (s : ℝ≥0) with hS
  set D := (A : Set Ω) ∩ S with hDdef
  have hSm : MeasurableSet[dF N ζ W VL VR T (s : ℝ≥0)] S :=
    measurableSet_safeU_indK (adaptedBefore_zData_dF hX hT hNm hN none) (fun ω => (hN.isWeakPath ω).2.1) hFH _
  have hD : MeasurableSet[restartFiltration (drivingFiltration P hX) T hT (s : ℝ≥0)] D :=
    (dataFilt_le_restart hX hT hNm hN0 _ _ (measurableSet_dF_of_mem_piClosure hX hT hNm A.2)).inter
      (dataFilt_le_restart hX hT hNm hN0 _ _ hSm)
  have hDm : MeasurableSet D := (restartFiltration (drivingFiltration P hX) T hT).le _ _ hD
  have hKm' : Measurable K := hKm.mono hT.measurableSpace_le le_rfl
  have hh'm : Measurable fun ω => restartField κ (h ω, K ω) :=
    (measurable_restartField κ).comp (hC.2.1.prodMk hKm')
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * (restartField κ (h ω, K ω) χ : ℂ))) P := fun χ =>
    Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hh'm)).aestronglyMeasurable 1
      (ae_of_all _ fun _ => (Complex.norm_exp_I_mul_ofReal _).le)
  have hsafe := ae_safe_restartDrv hN0 hN hFH (s : ℝ≥0)
  have key := ae_integral_condExpKernel_eq hT.measurableSpace_le ((hint Φ).indicator hDm)
    (((hint (Φ - lapTest (ballsOpen F) f)).indicator hDm).const_mul
      (projFactor (ballsOpen F) f (Φ - lapTest (ballsOpen F) f))) (fun B hB => by
    rw [setIntegral_indicator hDm, integral_const_mul, setIntegral_indicator hDm]
    have hDB : MeasurableSet[restartFiltration (drivingFiltration P hX) T hT (s : ℝ≥0)] (B ∩ D) :=
      (measurableSpace_le_restartFiltration hT _ _ hB).inter hD
    have h1 := setIntegral_lapTest_restart hκ hC hX hT hKm hK (s : ℝ≥0) hFH hDB
      (hsafe.mono fun ω h hω => h hω.2.2) f (Φ - lapTest (ballsOpen F) f)
    rwa [add_sub_cancel] at h1)
  filter_upwards [key] with ω₀ h1
  rw [integral_indicator hDm, integral_const_mul, integral_indicator hDm] at h1
  exact h1

end Transfer

/-! ### Under one conditional law -/

section Kernel

variable {κ : ℝ} {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {N : Set Ω}

/-- **Events of the augmented killed driving filtration of versions of the restarted data are almost surely events of
the restarted data filtration**, for versions agreeing almost surely with the modified restarted data before the
restarted lifetime (PROVE-DOMAINMARKOV2's argument in `isDyadicSampled_of_agree`, with agreement only before the
lifetime). -/
theorem nullAugmented_le_dF (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hNm : MeasurableSet N) (hN : IsGoodOff N ζ W VL VR T) {ν : Measure Ω}
    {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR' : Fin nR → ℝ≥0 → Ω → ℝ}
    (hX' : IsMeasurableKilledDriving W' VL' VR' (restartLife ζ T))
    (hagree : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω → W' t ω = zW N ζ W VL VR T t ω ∧
      (∀ i, VL' i t ω = zVL N ζ W VL VR T i t ω) ∧ ∀ j, VR' j t ω = zVR N ζ W VL VR T j t ω) (q : ℝ≥0) :
    nullAugmented (killedDrivingFiltration hX') ν q ≤ eventuallyMeasurableSpace (dF N ζ W VL VR T q) (ae ν) := by
  have hZa := fun i => adaptedBefore_zData_dF hX hT hNm hN i
  have hXZ : IsMeasurableKilledDriving (zW N ζ W VL VR T) (zVL N ζ W VL VR T) (zVR N ζ W VL VR T)
      (restartLife ζ T) :=
    isMeasurableKilledDriving_of_adaptedBefore (hZa none) (fun i => hZa (some (Sum.inl i)))
      (fun j => hZa (some (Sum.inr j)))
  have hkZ := killedDrivingFiltration_le (hZa none) (fun i => hZa (some (Sum.inl i)))
    (fun j => hZa (some (Sum.inr j))) hXZ
  refine sup_le (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · rintro _ ⟨r, hrq, B, hB, rfl⟩
    refine ⟨{ω | (r : ℝ≥0∞) < restartLife ζ T ω ∧ (zW N ζ W VL VR T r ω, fun i => zVL N ζ W VL VR T i r ω,
      fun j => zVR N ζ W VL VR T j r ω) ∈ B}, hkZ q _ (MeasurableSpace.measurableSet_generateFrom
        ⟨r, hrq, B, hB, rfl⟩), ?_⟩
    filter_upwards [hagree] with ω hω
    change ((r : ℝ≥0∞) < restartLife ζ T ω ∧ _ ∈ B) = ((r : ℝ≥0∞) < restartLife ζ T ω ∧ _ ∈ B)
    by_cases hr : (r : ℝ≥0∞) < restartLife ζ T ω
    · obtain ⟨h1, h2, h3⟩ := hω r hr
      have e2 : (fun i => VL' i r ω) = fun i => zVL N ζ W VL VR T i r ω := funext h2
      have e3 : (fun j => VR' j r ω) = fun j => zVR N ζ W VL VR T j r ω := funext h3
      rw [h1, e2, e3]
    · simp only [hr, false_and]
  · rintro s ⟨-, hs0⟩
    exact ⟨∅, @MeasurableSet.empty _ (dF N ζ W VL VR T q), ae_eq_empty.2 hs0⟩

/-- **Projection independence on the restarted data events under one conditional law.** If the shift identities
hold under `ν` on `A ∩ S` for the events `A` of the countable π-system generating `dF s` (`S` the safe event of `F`
at `s`), then for every event `A` of `dF s` the law of the field `h'` on `A ∩ S` is projection-independent at
`ballsU F`. -/
theorem isProjIndepMeasure_restart_of_shift (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hNm : MeasurableSet N) (hN : IsGoodOff N ζ W VL VR T) {ν : Measure Ω} [IsFiniteMeasure ν]
    {h' : Ω → DistOn upperHalfPlaneOpens} (hh' : Measurable h') {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hlaw : ν.map h' = fieldLaw0 u₀)
    {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hGm : Measurable G)
    (hGd : GFF.IsMarkovDecomposition (ballsOpen F) upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens))
    (f : RatComb → ℕ → zsSub (ballsU F))
    (hfg : ∀ k, Tendsto (fun m => gradFeat (ballsU F) (f k m).1) atTop
      (𝓝 (covVec (ballsU F) (ratComb upperHalfPlaneOpens k))))
    (hfa : ∀ k, ∀ᵐ g ∂zbLaw upperHalfPlaneOpens,
      Tendsto (fun m => g (lapTest (ballsOpen F) (f k m))) atTop (𝓝 (G g (ratComb upperHalfPlaneOpens k))))
    (s : ℝ≥0)
    (hid : ∀ (k : RatComb) (m : ℕ)
      (A : piClosure (dataGens N (restartLife ζ T) (fun _ _ => (0 : ℝ)) (rsData ζ W VL VR T) s)),
      ∫ ω in (A : Set Ω) ∩ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) s,
          Complex.exp (Complex.I * (h' ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂ν =
        projFactor (ballsOpen F) (f k m) (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen F) (f k m)) *
          ∫ ω in (A : Set Ω) ∩ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) s,
            Complex.exp (Complex.I * (h' ω (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen F) (f k m)) : ℂ))
              ∂ν)
    {A : Set Ω} (hA : MeasurableSet[dF N ζ W VL VR T s] A) :
    IsProjIndepMeasure (ballsOpen F)
      ((ν.restrict (A ∩ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) s)).map h') := by
  set S := safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) s with hSdef
  have hSm : MeasurableSet S :=
    (dF N ζ W VL VR T).le s _ (measurableSet_safeU_indK (adaptedBefore_zData_dF hX hT hNm hN none)
      (fun ω => (hN.isWeakPath ω).2.1) hFH s)
  have hVH : ((ballsOpen F : Opens ℂ) : Set ℂ) ⊆ H := fun z hz => hFH (ballsU_subset_ballsK F hz)
  refine isProjIndepMeasure_of_shift hh' hu₀ hlaw hVH hGm hGd f hfg hfa fun k m => ?_
  set Φ := ratComb upperHalfPlaneOpens k
  set c := projFactor (ballsOpen F) (f k m) (Φ - lapTest (ballsOpen F) (f k m))
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (S.indicator fun ω => Complex.exp (Complex.I * (h' ω χ : ℂ))) ν := fun χ =>
    (Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hh')).aestronglyMeasurable 1
      (ae_of_all _ fun _ => hnorm _)).indicator hSm
  have key := setIntegral_eq_of_isPiSystem (hint Φ) ((hint (Φ - lapTest (ballsOpen F) (f k m))).const_mul c)
    ((dF N ζ W VL VR T).le s) (dF_eq hX hT hNm s) (isPiSystem_piClosure _) (by
      have := hid k m ⟨univ, univ_mem_piClosure _⟩
      rw [← setIntegral_univ, ← setIntegral_univ (f := fun ω => c * _), integral_const_mul,
        setIntegral_indicator hSm, setIntegral_indicator hSm]
      exact this) (fun A' hA' => by
      rw [integral_const_mul, setIntegral_indicator hSm, setIntegral_indicator hSm]
      exact hid k m ⟨A', hA'⟩) hA
  rwa [integral_const_mul, setIntegral_indicator hSm, setIntegral_indicator hSm] at key

end Kernel

/-! ### Assembly -/

section Main

open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- **The locality half of Aux. lemma 53 in kernel form** (specification p. 245: "History marking permits retention of
the canonical germ of `K_τ` … Forgetting that germ preserves locality"), for every `κ > 0`: for `P`-almost every `ω₀`
with `T ω₀ < ζ ω₀`, under `ν = condExpKernel P 𝓓_T ω₀`, for all versions `W'`, `V'` of the restarted driver and marks
and every stopping time `τ < ζ − T` of their `ν`-driving filtration, the restarted hull `K'_τ` is a local set of the
restarted field `restartField κ (h, K)`. -/
theorem kernelRestartLocalityStatement {κ : ℝ} (hκ : 0 < κ) : KernelRestartLocalityStatement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ _ P _ 𝓕 W VL VR B ζ h hC hX T hT K hKm hK
  have hVH : ∀ F : Finset (ℚ × ℚ × ℚ), ballsK F ⊆ H → ((ballsOpen F : Opens ℂ) : Set ℂ) ⊆ H :=
    fun F hF z hz => hF (ballsU_subset_ballsK F hz)
  -- Borel versions of the projections onto `H(ballsU F)` and Dirichlet approximations, chosen once
  have hGex : ∀ F : Finset (ℚ × ℚ × ℚ), ∃ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens,
      ballsK F ⊆ H → Measurable G ∧
        GFF.IsMarkovDecomposition (ballsOpen F) upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens) := by
    intro F
    by_cases hF : ballsK F ⊆ H
    · obtain ⟨G, hGm, hGd⟩ := exists_markovMap_zbLaw (ballsOpen F) (hVH F hF)
      exact ⟨G, fun _ => ⟨hGm, hGd⟩⟩
    · exact ⟨id, fun h => absurd h hF⟩
  choose G hG using hGex
  have hfex : ∀ (F : Finset (ℚ × ℚ × ℚ)) (k : RatComb), ∃ f : ℕ → zsSub (ballsU F), ballsK F ⊆ H →
      Tendsto (fun m => gradFeat (ballsU F) (f m).1) atTop
        (𝓝 (covVec (ballsU F) (ratComb upperHalfPlaneOpens k))) ∧
      ∀ᵐ g ∂zbLaw upperHalfPlaneOpens,
        Tendsto (fun m => g (lapTest (ballsOpen F) (f m))) atTop (𝓝 (G F g (ratComb upperHalfPlaneOpens k))) := by
    intro F k
    by_cases hF : ballsK F ⊆ H
    · obtain ⟨f, hf1, hf2⟩ := exists_tendsto_ae_zbLaw (hG F hF).1 (hG F hF).2 (hVH F hF)
        (ratComb upperHalfPlaneOpens k)
      exact ⟨f, fun _ => ⟨hf1, hf2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hF⟩
  choose fam hfam using hfex
  -- the `P`-side objects
  obtain ⟨N, hNm, hN0, hN⟩ := exists_isGoodOff hC.1 hX hT
  have hle : hT.measurableSpace ≤ mΩ := hT.measurableSpace_le
  have htr := ae_setIntegral_restart_shift hκ hC hX hT hKm hK hNm hN0 hN fam
  have hgff := ae_isZBGFFProcess_restartField hκ hC hX hT hKm hK
  have hNν := ae_ae_condExpKernel hle (measure_eq_zero_iff_ae_notMem.1 hN0)
  have hlive := ae_ae_condExpKernel_mem (P := P) hle (measurableSet_liveSet hX hT)
  have hKm' : Measurable K := hKm.mono hle le_rfl
  have hh'm : Measurable fun ω => restartField κ (h ω, K ω) :=
    (measurable_restartField κ).comp (hC.2.1.prodMk hKm')
  filter_upwards [htr, hgff, hNν, hlive] with ω₀ htr0 hgff0 hN0' hlive0 hTζ W' VL' VR' hX' hagree τ hτ hτζ
  have hlive1 := hlive0 hTζ
  -- agreement of the versions with the modified restarted data before the lifetime
  have hagZ : ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω →
      W' t ω = zW N ζ W VL VR T t ω ∧ (∀ i, VL' i t ω = zVL N ζ W VL VR T i t ω) ∧
        ∀ j, VR' j t ω = zVR N ζ W VL VR T j t ω := by
    filter_upwards [hagree, hN0'] with ω hω hωN t ht
    obtain ⟨e1, e2, e3⟩ := hω t ht
    obtain ⟨f1, f2, f3⟩ := hN.eq_restart hωN ht
    exact ⟨e1.trans f1.symm, fun i => (e2 i).trans (f2 i).symm, fun j => (e3 j).trans (f3 j).symm⟩
  have hpathW' : ∀ᵐ ω ∂(condExpKernel P hT.measurableSpace ω₀),
      ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < restartLife ζ T ω} ∧ W' 0 ω = 0 := by
    filter_upwards [hagZ, hlive1] with ω hω hωl
    have hw := hN.isWeakPath ω
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω := by
      rw [ENNReal.coe_zero]; exact tsub_pos_iff_lt.2 hωl
    exact ⟨hw.2.1.congr fun t ht => (hω t ht).1, by rw [(hω 0 h0).1]; exact hw.1⟩
  -- the harmonic mean of the restarted word and the law of the restarted field under `ν`
  have hu₀ := isBoundedHarmonicExtension_bheAt κ ρL ρR (fun i => VL i (T ω₀) ω₀ - W (T ω₀) ω₀)
    (fun j => VR j (T ω₀) ω₀ - W (T ω₀) ω₀)
  set u₀ := bheAt κ ρL ρR (fun i => VL i (T ω₀) ω₀ - W (T ω₀) ω₀) (fun j => VR j (T ω₀) ω₀ - W (T ω₀) ω₀)
    with hu₀def
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hp := hgff0 hTζ u₀ hu₀
  have hlaw := map_eq_fieldLaw0_of_isZBGFFProcess hh'm hu₀c hp
  have hXgff := isZeroBoundaryGFF_sub_smoothDist hh'm hu₀c hp
  have hsm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  -- the member identities under `ν`
  have hmem : HasRatMembers (condExpKernel P hT.measurableSpace ω₀) (killedDrivingFiltration hX') W'
      (restartLife ζ T) (fun ω => restartField κ (h ω, K ω) - smoothDist upperHalfPlaneOpens u₀) := by
    intro r s hrs F hFH
    have hSm : MeasurableSet (safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) (s : ℝ≥0)) :=
      (dF N ζ W VL VR T).le _ _ (measurableSet_safeU_indK (adaptedBefore_zData_dF hX hT hNm hN none)
        (fun ω => (hN.isWeakPath ω).2.1) hFH _)
    refine ⟨safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) (s : ℝ≥0), hSm, ?_, fun D hD => ?_⟩
    · filter_upwards [hagZ] with ω hω
      have hw := hN.isWeakPath ω
      refine propext ((mem_safeU_indK_iff hw.2.1 hw.1 hFH _).trans ?_)
      constructor
      · rintro ⟨hlt, hd⟩
        exact ⟨hlt, by rwa [fwdHull_rpath_congr_of_lt (fun t ht => (hω t ht).1) hlt]⟩
      · rintro ⟨hlt, hd⟩
        exact ⟨hlt, by rwa [← fwdHull_rpath_congr_of_lt (fun t ht => (hω t ht).1) hlt]⟩
    · obtain ⟨A', hA', hDA'⟩ := nullAugmented_le_dF hX hT hNm hN hX' hagZ (s : ℝ≥0) _
        (usualAugmentation_le_nullAugmented (killedDrivingFiltration hX') (by exact_mod_cast hrs) _ hD)
      have hpi := isProjIndepMeasure_restart_of_shift hX hT hNm hN hh'm hu₀.1 hlaw hFH (hG F hFH).1 (hG F hFH).2
        (fam F) (fun k => (hfam F k hFH).1) (fun k => (hfam F k hFH).2) (s : ℝ≥0)
        (fun k m A => htr0 s F hFH k m A) hA'
      have hres : (condExpKernel P hT.measurableSpace ω₀).restrict
          (D ∩ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) (s : ℝ≥0)) =
          (condExpKernel P hT.measurableSpace ω₀).restrict
            (A' ∩ safeU (zW N ζ W VL VR T) (restartLife ζ T) univ (indK F) (s : ℝ≥0)) :=
        Measure.restrict_congr_set (hDA'.inter (EventuallyEq.refl _ _))
      have ecomp : (fun ω => restartField κ (h ω, K ω) - smoothDist upperHalfPlaneOpens u₀) =
          (fun x => x - smoothDist upperHalfPlaneOpens u₀) ∘ fun ω => restartField κ (h ω, K ω) := rfl
      rw [hres, ecomp, ← Measure.map_map (measurable_sub_distOnConst _) hh'm]
      exact IsProjIndepMeasure.map_sub (hVH F hFH) hpi hsm
  -- locality of the centred field, then of the restarted field
  have hloc := isLocalSet_hull_of_members hXgff (adaptedBefore_killedDriving_W hX') hpathW' hmem hτ hτζ
  have h2 := Coupling.IsLocalSet.add_dist hloc hsm
  have e : (fun ω => restartField κ (h ω, K ω) - smoothDist upperHalfPlaneOpens u₀ +
      smoothDist upperHalfPlaneOpens u₀) = fun ω => restartField κ (h ω, K ω) :=
    funext fun ω => sub_add_cancel _ _
  rw [e] at h2
  exact h2

/-- **Aux. lemma 53 in kernel form, for every `κ > 0`** (PROVE-DOMAINMARKOV2's reduction with its locality half
proved here): under almost every conditional law given the stopped driving history `𝓓_T`, versions of the restarted
driver and marks and the restarted field form an optional hull coupling of the current word. -/
theorem kernelRestartCouplingStatement {κ : ℝ} (hκ : 0 < κ) : KernelRestartCouplingStatement.{u} κ :=
  kernelRestartCouplingStatement_of_locality hκ (kernelRestartLocalityStatement hκ)

end Main

end InteractingSLE.Restart.DomainMarkov
