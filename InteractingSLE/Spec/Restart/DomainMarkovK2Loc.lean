/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2Law

/-!
# K2, part 3: locality of a general continuation under the regular conditional law

Packet PROVE-DOMAINMARKOV5, item (K2), the locality half. PROVE-DOMAINMARKOV3 proved the locality of the restarted
hulls under almost every conditional law given `𝓓_T`, from `P`-side member identities (`setIntegral_lapTest_restart`)
transferred to the kernels. Here the transfer and the kernel-side argument are done for an **arbitrary** conditioning
σ-algebra `𝒢 ≤ 𝓗 0`, live event `F ∈ 𝒢` and continuation `(W, VL, VR, ζ)` adapted to `𝓗`, from the `P`-side input

* `HasSafeMembers P 𝓗 F ζ W X`: at every deterministic time `s`, on every event `D ∈ 𝓗_s` contained (almost surely) in
  `F` and in the event that the finite union of rational closed balls `ballsK Fb ⊆ ℍ` avoids the continuation hull
  `K_s`, the field satisfies the projection identity at `ballsU Fb`:
  `∫_D e^{i X(−Δf/2π + Ξ)} = projFactor f Ξ · ∫_D e^{i X(Ξ)}` (the history-marked locality of the hull at `s`).

Results: `ae_setIntegral_shift_k` (the shift identities for countably many indices under almost every
`ν = condExpKernel P 𝒢 ω₀`), `isProjIndepMeasure_k_of_shift` (Dynkin and the Dirichlet limit under one `ν`), and
**`ae_isLocalSet_k`**: for `P`-almost every `ω₀ ∈ F`, if under `ν` the field is a Gaussian free field with a bounded
harmonic mean, then for every version of the modified continuation and every stopping time `τ < ζ` of its `ν`-driving
filtration, the hull `K_τ` is a local set of the field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H fwdHull zeroGFFTestCov)
open scoped ENNReal NNReal RealInnerProductSpace

namespace InteractingSLE.Restart.DomainMarkov.K2

open LQGMetric LQGMetric.MarkovZB LocalSets Coupling Ito Sec7 Sec7.Aux122Disint Sec2.Restart Sec5.Markov LocalExt
open QuantumZipper.K3 QuantumZipper.Thm11Asm

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {N F : Set Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {X : Ω → DistOn upperHalfPlaneOpens} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- **`P`-side input (L): the member identities of the continuation hulls at deterministic times.** -/
def HasSafeMembers (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ) (F : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (X : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (s : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ H → ∀ D : Set Ω, MeasurableSet[𝓗 s] D →
    (∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ (s : ℝ≥0∞) < ζ ω ∧
      Disjoint (ballsK Fb) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ))) →
    ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
      ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P =
        projFactor (ballsOpen Fb) f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P

/-! ### The transferred shift identities -/

omit mΩ in
/-- On the safe event of the modified driver, off `N` and on `F`, `s < ζ` and `ballsK Fb` avoids the hull of `W`. -/
theorem safe_of_mem_safeU_k (hN : IsKGood N F ζ W VL VR) {ω : Ω} (hωN : ω ∉ N) (hωF : ω ∈ F)
    {Fb : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK Fb ⊆ H) {s : ℝ≥0}
    (hS : ω ∈ safeU (kW N F W VL VR) ζ univ (indK Fb) s) :
    (s : ℝ≥0∞) < ζ ω ∧ Disjoint (ballsK Fb) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := by
  have hw := hN.isWeakPath ω
  obtain ⟨hlt, hd⟩ := (mem_safeU_indK_iff hw.2.1 hw.1 hFH s).1 hS
  rw [kW_path_eq hωN hωF] at hd
  exact ⟨hlt, hd⟩

variable [StandardBorelSpace Ω] [IsProbabilityMeasure P]

/-- **The shift identities under almost every conditional law.** For any family of test directions
`fam Fb k m ∈ C_c^∞(ballsU Fb)`: for `P`-almost every `ω₀`, for all rational `s`, families `Fb` of rational closed
balls in `ℍ`, rational combinations `Φ_k`, `m` and events `A` of the countable π-system generating the data
filtration at `s`, with `S` the safe event of `Fb` at `s`,
`∫_{(A∩F)∩S} e^{i X(Φ_k)} dν = projFactor (f_m) (Φ_k + Δf_m/2π) · ∫_{(A∩F)∩S} e^{i X(Φ_k + Δf_m/2π)} dν`. -/
theorem ae_setIntegral_shift_k (h𝒢 : 𝒢 ≤ 𝓗 0) (hF : MeasurableSet[𝒢] F)
    (hW : AdaptedBefore 𝓗 ζ W) (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j))
    (hX : Measurable X) (hNm : MeasurableSet N) (hN0 : P N = 0) (hN : IsKGood N F ζ W VL VR)
    (hmem : HasSafeMembers P 𝓗 F ζ W X) (fam : ∀ Fb : Finset (ℚ × ℚ × ℚ), RatComb → ℕ → zsSub (ballsU Fb)) :
    ∀ᵐ ω₀ ∂P, ∀ (s : ℚ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ H → ∀ (k : RatComb) (m : ℕ)
      (A : piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) (s : ℝ≥0))),
      ∫ ω in ((A : Set Ω) ∩ F) ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0),
          Complex.exp (Complex.I * (X ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂(condExpKernel P 𝒢 ω₀) =
        projFactor (ballsOpen Fb) (fam Fb k m)
            (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen Fb) (fam Fb k m)) *
          ∫ ω in ((A : Set Ω) ∩ F) ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0),
            Complex.exp (Complex.I * (X ω (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen Fb) (fam Fb k m)) : ℂ))
            ∂(condExpKernel P 𝒢 ω₀) := by
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hdm := dataMeas_k hNm hF0 hW hVL hVR
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  refine ae_all_iff.2 fun s => ae_all_iff.2 fun Fb => ?_
  by_cases hFH : ballsK Fb ⊆ H
  swap
  · exact Eventually.of_forall fun _ h => absurd h hFH
  refine (ae_all_iff.2 fun k => ae_all_iff.2 fun m => ?_).mono fun ω₀ h _ => h
  have hc : Countable (piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) (s : ℝ≥0))) :=
    (countable_piClosure (countable_dataGens _ _ _ _ _)).to_subtype
  refine ae_all_iff.2 fun A => ?_
  set Φ := ratComb upperHalfPlaneOpens k with hΦ
  set f := fam Fb k m with hf
  set S := safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0) with hSdef
  have hAk : MeasurableSet[kF N F ζ W VL VR (s : ℝ≥0)] (A : Set Ω) := measurableSet_kF_of_mem_piClosure hdm A.2
  have hSk : MeasurableSet[kF N F ζ W VL VR (s : ℝ≥0)] S :=
    measurableSet_safeU_indK (adaptedBefore_kW hdm hN) (fun ω => (hN.isWeakPath ω).2.1) hFH _
  have hFm : MeasurableSet F := h𝒢m _ hF
  set D := ((A : Set Ω) ∩ F) ∩ S with hDdef
  have hDm : MeasurableSet D :=
    (((kF N F ζ W VL VR).le _ _ hAk).inter hFm).inter ((kF N F ζ W VL VR).le _ _ hSk)
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * (X ω χ : ℂ))) P := fun χ =>
    Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hX)).aestronglyMeasurable 1
      (ae_of_all _ fun _ => (Complex.norm_exp_I_mul_ofReal _).le)
  obtain ⟨A', hA', hAA'⟩ := exists_version_of_measurableSet_kF hF0 hW hVL hVR hAk
  obtain ⟨S', hS', hSS'⟩ := exists_version_of_measurableSet_kF hF0 hW hVL hVR hSk
  have key := ae_integral_condExpKernel_eq h𝒢m ((hint Φ).indicator hDm)
    (((hint (Φ - lapTest (ballsOpen Fb) f)).indicator hDm).const_mul
      (projFactor (ballsOpen Fb) f (Φ - lapTest (ballsOpen Fb) f))) (fun B hB => by
    rw [setIntegral_indicator hDm, integral_const_mul, setIntegral_indicator hDm]
    have hBq : MeasurableSet[𝓗 (s : ℝ≥0)] B := 𝓗.mono (zero_le (a := (s : ℝ≥0))) _ (h𝒢 _ hB)
    have hFq : MeasurableSet[𝓗 (s : ℝ≥0)] F := 𝓗.mono (zero_le (a := (s : ℝ≥0))) _ hF0
    set D' := B ∩ ((A' ∩ F) ∩ S') with hD'def
    have hD' : MeasurableSet[𝓗 (s : ℝ≥0)] D' := hBq.inter ((hA'.inter hFq).inter hS')
    have hDeq : D' =ᵐ[P] (B ∩ D : Set Ω) := by
      filter_upwards [hNc] with ω hωN
      have h1 := (diff_eq_diff_iff.1 hAA') ω hωN
      have h2 := (diff_eq_diff_iff.1 hSS') ω hωN
      simp only [hD'def, hDdef, mem_inter_iff, h1, h2]
    have hDin : ∀ᵐ ω ∂P, ω ∈ D' → ω ∈ F ∧ ((s : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        Disjoint (ballsK Fb) (fwdHull (fun r : ℝ => W r.toNNReal ω) ((s : ℝ≥0) : ℝ)) := by
      filter_upwards [hNc] with ω hωN hωD
      have hωS : ω ∈ S := ((diff_eq_diff_iff.1 hSS') ω hωN).2 hωD.2.2
      exact ⟨hωD.2.1.2, safe_of_mem_safeU_k hN hωN hωD.2.1.2 hFH hωS⟩
    have h1 := hmem (s : ℝ≥0) Fb hFH D' hD' hDin f (Φ - lapTest (ballsOpen Fb) f)
    rw [add_sub_cancel, setIntegral_congr_set hDeq, setIntegral_congr_set hDeq] at h1
    exact h1)
  filter_upwards [key] with ω₀ h1
  rw [integral_indicator hDm, integral_const_mul, integral_indicator hDm] at h1
  exact h1

/-! ### Under one conditional law -/

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Projection independence on the data events under one measure.** If the shift identities hold under `ν` on
`(A ∩ F) ∩ S` for the events `A` of the countable π-system generating `kF s` (`S` the safe event of `Fb` at `s`), and
`F` has full `ν`-measure, then for every event `A` of `kF s` the law of the field on `A ∩ S` is projection-independent
at `ballsU Fb`. -/
theorem isProjIndepMeasure_k_of_shift (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR))
    (hN : IsKGood N F ζ W VL VR) {ν : Measure Ω} [IsFiniteMeasure ν] (hFν : ∀ᵐ ω ∂ν, ω ∈ F)
    (hX : Measurable X) {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hlaw : ν.map X = fieldLaw0 u₀)
    {Fb : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK Fb ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hGm : Measurable G)
    (hGd : GFF.IsMarkovDecomposition (ballsOpen Fb) upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens))
    (f : RatComb → ℕ → zsSub (ballsU Fb))
    (hfg : ∀ k, Tendsto (fun m => gradFeat (ballsU Fb) (f k m).1) atTop
      (𝓝 (covVec (ballsU Fb) (ratComb upperHalfPlaneOpens k))))
    (hfa : ∀ k, ∀ᵐ g ∂zbLaw upperHalfPlaneOpens,
      Tendsto (fun m => g (lapTest (ballsOpen Fb) (f k m))) atTop (𝓝 (G g (ratComb upperHalfPlaneOpens k))))
    (s : ℝ≥0)
    (hid : ∀ (k : RatComb) (m : ℕ) (A : piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) s)),
      ∫ ω in ((A : Set Ω) ∩ F) ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) s,
          Complex.exp (Complex.I * (X ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂ν =
        projFactor (ballsOpen Fb) (f k m) (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen Fb) (f k m)) *
          ∫ ω in ((A : Set Ω) ∩ F) ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) s,
            Complex.exp (Complex.I * (X ω (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen Fb) (f k m)) : ℂ))
              ∂ν)
    {A : Set Ω} (hA : MeasurableSet[kF N F ζ W VL VR s] A) :
    IsProjIndepMeasure (ballsOpen Fb) ((ν.restrict (A ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) s)).map X) := by
  set S := safeU (kW N F W VL VR) ζ univ (indK Fb) s with hSdef
  have hSm : MeasurableSet S :=
    (kF N F ζ W VL VR).le s _ (measurableSet_safeU_indK (adaptedBefore_kW hdm hN)
      (fun ω => (hN.isWeakPath ω).2.1) hFH s)
  have hVH : ((ballsOpen Fb : Opens ℂ) : Set ℂ) ⊆ H := fun z hz => hFH (ballsU_subset_ballsK Fb hz)
  -- drop `F`, which has full measure
  have hid' : ∀ (k : RatComb) (m : ℕ) (A : piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) s)),
      ∫ ω in (A : Set Ω) ∩ S, Complex.exp (Complex.I * (X ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂ν =
        projFactor (ballsOpen Fb) (f k m) (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen Fb) (f k m)) *
          ∫ ω in (A : Set Ω) ∩ S,
            Complex.exp (Complex.I * (X ω (ratComb upperHalfPlaneOpens k - lapTest (ballsOpen Fb) (f k m)) : ℂ))
              ∂ν := fun k m A' => by
    have hAF : (((A' : Set Ω) ∩ F) ∩ S : Set Ω) =ᵐ[ν] ((A' : Set Ω) ∩ S : Set Ω) := by
      filter_upwards [hFν] with ω hω
      simp only [mem_inter_iff, hω, and_true]
    have h := hid k m A'
    rwa [setIntegral_congr_set hAF, setIntegral_congr_set hAF] at h
  refine isProjIndepMeasure_of_shift hX hu₀ hlaw hVH hGm hGd f hfg hfa fun k m => ?_
  set Φ := ratComb upperHalfPlaneOpens k
  set c := projFactor (ballsOpen Fb) (f k m) (Φ - lapTest (ballsOpen Fb) (f k m))
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (S.indicator fun ω => Complex.exp (Complex.I * (X ω χ : ℂ))) ν := fun χ =>
    (Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hX)).aestronglyMeasurable 1
      (ae_of_all _ fun _ => hnorm _)).indicator hSm
  have key := setIntegral_eq_of_isPiSystem (hint Φ) ((hint (Φ - lapTest (ballsOpen Fb) (f k m))).const_mul c)
    ((kF N F ζ W VL VR).le s) (kF_eq hdm s) (isPiSystem_piClosure _) (by
      have := hid' k m ⟨univ, univ_mem_piClosure _⟩
      rw [← setIntegral_univ, ← setIntegral_univ (f := fun ω => c * _), integral_const_mul,
        setIntegral_indicator hSm, setIntegral_indicator hSm]
      exact this) (fun A' hA' => by
      rw [integral_const_mul, setIntegral_indicator hSm, setIntegral_indicator hSm]
      exact hid' k m ⟨A', hA'⟩) hA
  rwa [integral_const_mul, setIntegral_indicator hSm, setIntegral_indicator hSm] at key

/-! ### Locality under almost every conditional law -/

open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- **The locality half of K2.** From the `P`-side member identities: for `P`-almost every `ω₀ ∈ F`, under
`ν = condExpKernel P 𝒢 ω₀`, if the field is a Gaussian free field with a harmonic mean `u₀` (`X − 𝔥` a zero-boundary
GFF process), then for every measurable version `(W', VL', VR')` of the modified continuation (equal to it
`ν`-almost surely before `ζ`) and every stopping time `τ < ζ` of its `ν`-driving filtration, the hull `K'_τ` is a
local set of `X` under `ν`. -/
theorem ae_isLocalSet_k (h𝒢 : 𝒢 ≤ 𝓗 0) (hF : MeasurableSet[𝒢] F)
    (hW : AdaptedBefore 𝓗 ζ W) (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j))
    (hX : Measurable X) (hNm : MeasurableSet N) (hN0 : P N = 0) (hN : IsKGood N F ζ W VL VR)
    (hmem : HasSafeMembers P 𝓗 F ζ W X) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ u₀ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u₀ H →
      IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) (condExpKernel P 𝒢 ω₀) →
      ∀ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
        (hX' : IsMeasurableKilledDriving W' VL' VR' ζ),
        (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = kW N F W VL VR t ω ∧
          (∀ i, VL' i t ω = kVL N F W VL VR i t ω) ∧ ∀ j, VR' j t ω = kVR N F W VL VR j t ω) →
        (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), 0 < ζ ω) →
        ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (drivingFiltration (condExpKernel P 𝒢 ω₀) hX') τ →
          (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (τ ω : ℝ≥0∞) < ζ ω) →
          IsLocalSet (fun ω => fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) X
            (condExpKernel P 𝒢 ω₀) := by
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hdm := dataMeas_k hNm hF0 hW hVL hVR
  have hVH : ∀ Fb : Finset (ℚ × ℚ × ℚ), ballsK Fb ⊆ H → ((ballsOpen Fb : Opens ℂ) : Set ℂ) ⊆ H :=
    fun Fb hFb z hz => hFb (ballsU_subset_ballsK Fb hz)
  -- Borel versions of the projections onto `H(ballsU Fb)` and Dirichlet approximations, chosen once
  have hGex : ∀ Fb : Finset (ℚ × ℚ × ℚ), ∃ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens,
      ballsK Fb ⊆ H → Measurable G ∧
        GFF.IsMarkovDecomposition (ballsOpen Fb) upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens) := by
    intro Fb
    by_cases hFb : ballsK Fb ⊆ H
    · obtain ⟨G, hGm, hGd⟩ := exists_markovMap_zbLaw (ballsOpen Fb) (hVH Fb hFb)
      exact ⟨G, fun _ => ⟨hGm, hGd⟩⟩
    · exact ⟨id, fun h => absurd h hFb⟩
  choose G hG using hGex
  have hfex : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) (k : RatComb), ∃ f : ℕ → zsSub (ballsU Fb), ballsK Fb ⊆ H →
      Tendsto (fun m => gradFeat (ballsU Fb) (f m).1) atTop
        (𝓝 (covVec (ballsU Fb) (ratComb upperHalfPlaneOpens k))) ∧
      ∀ᵐ g ∂zbLaw upperHalfPlaneOpens,
        Tendsto (fun m => g (lapTest (ballsOpen Fb) (f m))) atTop (𝓝 (G Fb g (ratComb upperHalfPlaneOpens k))) := by
    intro Fb k
    by_cases hFb : ballsK Fb ⊆ H
    · obtain ⟨f, hf1, hf2⟩ := exists_tendsto_ae_zbLaw (hG Fb hFb).1 (hG Fb hFb).2 (hVH Fb hFb)
        (ratComb upperHalfPlaneOpens k)
      exact ⟨f, fun _ => ⟨hf1, hf2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hFb⟩
  choose fam hfam using hfex
  have htr := ae_setIntegral_shift_k h𝒢 hF hW hVL hVR hX hNm hN0 hN hmem fam
  filter_upwards [htr, ae_ae_condExpKernel_mem (P := P) h𝒢m hF] with ω₀ htr0 hmemF hω₀F u₀ hu₀ hp
    W' VL' VR' hX' hagZ hζ0 τ hτ hτζ
  have hFν : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ F := hmemF hω₀F
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hpathW' : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W' 0 ω = 0 := by
    filter_upwards [hagZ, hζ0] with ω hω hω0
    have hw := hN.isWeakPath ω
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact hω0
    exact ⟨hw.2.1.congr fun t ht => (hω t ht).1, by rw [(hω 0 h0).1]; exact hw.1⟩
  have hlaw := map_eq_fieldLaw0_of_isZBGFFProcess hX hu₀c hp
  have hXgff := isZeroBoundaryGFF_sub_smoothDist hX hu₀c hp
  have hsm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := WholeField.isHarmonicDistOn_smoothDist hu₀
  -- the member identities under `ν`
  have hmemν : HasRatMembers (condExpKernel P 𝒢 ω₀) (killedDrivingFiltration hX') W' ζ
      (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀) := by
    intro r s hrs Fb hFH
    have hSm : MeasurableSet (safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0)) :=
      (kF N F ζ W VL VR).le _ _ (measurableSet_safeU_indK (adaptedBefore_kW hdm hN)
        (fun ω => (hN.isWeakPath ω).2.1) hFH _)
    refine ⟨safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0), hSm, ?_, fun D hD => ?_⟩
    · filter_upwards [hagZ] with ω hω
      have hw := hN.isWeakPath ω
      refine propext ((mem_safeU_indK_iff hw.2.1 hw.1 hFH _).trans ?_)
      constructor
      · rintro ⟨hlt, hd⟩
        exact ⟨hlt, by rwa [fwdHull_rpath_congr_of_lt (fun t ht => (hω t ht).1) hlt]⟩
      · rintro ⟨hlt, hd⟩
        exact ⟨hlt, by rwa [← fwdHull_rpath_congr_of_lt (fun t ht => (hω t ht).1) hlt]⟩
    · obtain ⟨A', hA', hDA'⟩ := nullAugmented_le_of_agree (adaptedBefore_kW hdm hN) (adaptedBefore_kVL hdm hN)
        (adaptedBefore_kVR hdm hN) hX' hagZ (s : ℝ≥0) _
        (usualAugmentation_le_nullAugmented (killedDrivingFiltration hX') (by exact_mod_cast hrs) _ hD)
      have hpi := isProjIndepMeasure_k_of_shift hdm hN hFν hX hu₀ hlaw hFH (hG Fb hFH).1 (hG Fb hFH).2
        (fam Fb) (fun k => (hfam Fb k hFH).1) (fun k => (hfam Fb k hFH).2) (s : ℝ≥0)
        (fun k m A => htr0 s Fb hFH k m A) hA'
      have hres : (condExpKernel P 𝒢 ω₀).restrict (D ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0)) =
          (condExpKernel P 𝒢 ω₀).restrict (A' ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0)) :=
        Measure.restrict_congr_set (hDA'.inter (EventuallyEq.refl _ _))
      have ecomp : (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀) =
          (fun x => x - smoothDist upperHalfPlaneOpens u₀) ∘ X := rfl
      rw [hres, ecomp, ← Measure.map_map (measurable_sub_distOnConst _) hX]
      exact IsProjIndepMeasure.map_sub (hVH Fb hFH) hpi hsm
  -- locality of the centred field, then of the field
  have hloc := isLocalSet_hull_of_members hXgff (adaptedBefore_killedDriving_W hX') hpathW' hmemν hτ hτζ
  have h2 := Coupling.IsLocalSet.add_dist hloc hsm
  have e : (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = X :=
    funext fun ω => sub_add_cancel _ _
  rw [e] at h2
  exact h2

end InteractingSLE.Restart.DomainMarkov.K2
