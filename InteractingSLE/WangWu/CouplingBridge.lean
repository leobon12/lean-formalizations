import InteractingSLE.WangWu.CouplingFrozenTwo
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

/-!
# Wang–Wu at `κ = 4`: the full level-line coupling and the frozen optional hull coupling

Packet PROVE-WW-A (orchestrator note: relate the document's coupling, Definition 1.5 / Theorem 3.8, to the
project's frozen Theorem 1.1 `exists_isOptionalHullCoupling` at `κ = 4`).

On the active domain `D_τ = ℍ \ K_τ` the document's objects are the frozen ones at `κ = 4`:

* `frozenMean_eq_couplingMean`: the frozen mean of an active point is the frozen `couplingMean 4` (with any
  bounded harmonic extension of the transported data);
* `retainedGreen_eq_greenH`: the retained Green kernel of two active points is `G_ℍ(f_τ a, f_τ b)`;
* `retainedGreenEnergy_eq_loewnerGreenEnergy`, `integral_frozenMean_mul_eq`: hence, for a test function supported
  off the hull, `Q_{U_τ}(φ, φ)` is the frozen `loewnerGreenEnergy` and `∫ η̄_τ φ = ∫ 𝔥_τ φ`.

**Bridge** (`IsFullLevelLineCoupling.isIntegratedSLEEvolution`, `.measurable`,
`IsFullLevelLineCoupling.condExp_cexp_eq_of_disjoint`): a full level-line coupling (Definition 1.5) is an integrated
`SLE₄(ρ)` evolution with a measurable field satisfying exactly the conditional-law clause of the frozen
`IsOptionalHullCoupling 4` (for every stopping time `τ < T` of the frozen `drivingFiltration`, every family of bounded
harmonic extensions `u`, every test function `φ`, almost surely on `{tsupport φ ∩ K_τ = ∅}`). What separates it from
`IsOptionalHullCoupling 4` are the two remaining clauses of the frozen definition: the zero-boundary GFF law of
`F − 𝔥₀` (the `τ = 0` case of the kernel identity, plus `∬ φ G_ℍ ψ = zeroGFFTestCov ℍ φ ψ` and joint Gaussianity from
linearity) and the local-set property of `K_τ` (the document's Corollary 3.9).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

variable {nL nR : ℕ}

section Path

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A point of `ℍ` outside the hull `K_t` is alive at `t`. -/
theorem exists_isForwardSol_of_not_mem_hull {W : ℝ → ℝ} {t : ℝ≥0} {z : ℂ} (hz : z ∈ H)
    (hK : z ∉ fwdHull W t) : ∃ v, IsForwardSol W z t v :=
  QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg hz hK

/-- **The frozen mean of an active point is the frozen `couplingMean 4`.** -/
theorem frozenMean_eq_couplingMean (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) {z : ℂ} (hz : 0 < z.im) (hsol : ∃ v, IsForwardSol (Ito.rpath w) z t v)
    {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR (fun i => vL i t - w t)
      (fun i => vR i t - w t)) (forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t)) u) :
    frozenMean ρL ρR w vL vR t z = couplingMean 4 (Ito.rpath w) t u z := by
  have hlt := lt_swallowTime_of_path hP ht hz hsol
  simp only [frozenMean, hlt, ↓reduceIte]
  exact (couplingMean_eq_meanAt_of_path hP ht hz hsol hu).symm

/-- **The retained Green kernel of two distinct active points** is `G_ℍ(f_t a, f_t b)`. -/
theorem retainedGreen_eq_greenH (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) {a c : ℂ} (ha : 0 < a.im) (hc : 0 < c.im) (hac : a ≠ c)
    (hsa : ∃ v, IsForwardSol (Ito.rpath w) a t v) (hsc : ∃ v, IsForwardSol (Ito.rpath w) c t v) :
    retainedGreen w t a c = greenH (fwdMap (Ito.rpath w) t a) (fwdMap (Ito.rpath w) t c) := by
  obtain ⟨T', htT', hT'ζ⟩ := exists_between_lt_lifetime ht
  have hwc : ContinuousOn (Ito.rpath w) (Icc 0 (T' : ℝ)) := Ito.continuousOn_rpath hP.2.2.2.1 hT'ζ
  set W' := Ito.clampDrv (Ito.rpath w) T' with hW'def
  have hW'c : Continuous W' := Ito.continuous_clampDrv T'.coe_nonneg hwc
  have heq : EqOn (Ito.rpath w) W' (Icc 0 (T' : ℝ)) := fun s hs => (Ito.clampDrv_eqOn hs).symm
  have htT'r : (t : ℝ) < T' := by exact_mod_cast htT'
  have hVe : K3.VTe (Ito.rpath w) t a c = K3.VTe W' t a c :=
    VTe_eq_of_eqOn htT'r hwc hW'c.continuousOn heq ha hc
  have halive : ∀ x : ℂ, 0 < x.im → (∃ v, IsForwardSol (Ito.rpath w) x t v) →
      ENNReal.ofReal (t : ℝ) < swallowTime W' x := fun x hx ⟨v, hv⟩ =>
    lt_swallowTime_of_isForwardSol t.coe_nonneg htT'r hW'c.continuousOn hx
      ⟨v, (Ito.isForwardSol_iff_of_eqOn (heq.mono (Icc_subset_Icc_right htT'r.le)) v).1 hv⟩
  have h := K3.VTe_eq_vtKer_of_lt hW'c ha hc t.coe_nonneg (halive a ha hsa) (halive c hc hsc)
  rw [retainedGreen, K3.VT, hVe, h, K3.vtKer]
  simp only [← Ito.fwdMap_congr_of_eqOn_of_le heq htT'r.le]
  rw [ENNReal.toReal_ofReal]
  obtain ⟨v, hv⟩ := hsa
  obtain ⟨v', hv'⟩ := hsc
  exact (greenH_fwdMap_mem_Icc_of_path hP ht ha hc hac ⟨v, hv⟩ ⟨v', hv'⟩).1

/-- **`Q_{U_t}(φ, φ)` is the frozen `loewnerGreenEnergy`** for a test function supported off the hull `K_t`. -/
theorem retainedGreenEnergy_eq_loewnerGreenEnergy (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {φ : ℂ → ℝ} (hφH : tsupport φ ⊆ H)
    (hdisj : Disjoint (tsupport φ) (fwdHull (Ito.rpath w) t)) :
    retainedGreenEnergy w t φ = loewnerGreenEnergy (Ito.rpath w) t φ := by
  have halive : ∀ x, φ x ≠ 0 → 0 < x.im ∧ ∃ v, IsForwardSol (Ito.rpath w) x t v := fun x hx => by
    have hxs : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 hx)
    exact ⟨hφH hxs, exists_isForwardSol_of_not_mem_hull (hφH hxs)
      (Set.disjoint_left.1 hdisj hxs)⟩
  unfold retainedGreenEnergy loewnerGreenEnergy
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton a)] with c hc
  by_cases ha : φ a = 0
  · simp [ha]
  by_cases hc0 : φ c = 0
  · simp [hc0]
  have hac : a ≠ c := fun h => hc (h ▸ rfl)
  obtain ⟨ha1, ha2⟩ := halive a ha
  obtain ⟨hc1, hc2⟩ := halive c hc0
  rw [retainedGreen_eq_greenH hP ht ha1 hc1 hac ha2 hc2]

/-- **`∫ η̄_t φ = ∫ 𝔥_t φ`** for a test function supported off the hull `K_t`. -/
theorem integral_frozenMean_mul_eq (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {φ : ℂ → ℝ} (hφH : tsupport φ ⊆ H)
    (hdisj : Disjoint (tsupport φ) (fwdHull (Ito.rpath w) t)) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR (fun i => vL i t - w t)
      (fun i => vR i t - w t)) (forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t)) u) :
    ∫ z, frozenMean ρL ρR w vL vR t z * φ z = ∫ z, couplingMean 4 (Ito.rpath w) t u z * φ z := by
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : φ z = 0
  · simp [hz]
  have hzs : z ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 hz)
  show frozenMean ρL ρR w vL vR t z * φ z = couplingMean 4 (Ito.rpath w) t u z * φ z
  rw [frozenMean_eq_couplingMean hP ht (hφH hzs)
    (exists_isForwardSol_of_not_mem_hull (hφH hzs) (Set.disjoint_left.1 hdisj hzs)) hu]

end Path

/-! ### The bridge -/

section Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {F : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

theorem IsFullLevelLineCoupling.isIntegratedSLEEvolution
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F) :
    IsIntegratedSLEEvolution 4 xL xR ρL ρR P 𝓕 W VL VR B ζ := hF.1

theorem IsFullLevelLineCoupling.measurable
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F) : Measurable F := hF.2.1

/-- **Bridge to the frozen Theorem 1.1 at `κ = 4`.** A full level-line coupling (Definition 1.5) satisfies, word for
word, the conditional-law clause of the frozen `IsOptionalHullCoupling 4`: for every stopping time `τ < T` of the
frozen `drivingFiltration`, every family `u` of bounded harmonic extensions of the transported data, and every test
function `φ`, almost surely on `{tsupport φ ∩ K_τ = ∅}`,
`E[e^{i(F, φ)} | 𝓕_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`. -/
theorem IsFullLevelLineCoupling.condExp_cexp_eq_of_disjoint
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F) :
    ∃ hX : IsMeasurableKilledDriving W VL VR ζ,
      ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ),
        (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
          ∀ u : Ω → ℂ → ℝ,
            (∀ ω, IsBoundedHarmonicExtension
                (forceBoundaryData 4 ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
                  (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
                (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
                  (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
                (u ω)) →
            ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
              Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
                  ((τ ω).untopD 0 : ℝ≥0)) →
                condExp hτ.measurableSpace P
                    (fun ω' => Complex.exp (Complex.I * (F ω' φ : ℂ))) ω =
                  Complex.exp (Complex.I * ((∫ z, couplingMean 4 (fun s : ℝ => W s.toNNReal ω)
                      ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
                    (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
                      ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  obtain ⟨hE, -, hX, hK⟩ := hF
  refine ⟨hX, fun τ hτ hτζ u hu φ => ?_⟩
  filter_upwards [hK τ hτ hτζ φ, hE.2.2.2.2, hτζ] with ω h1 hP hlt hdisj
  rw [h1]
  have hne : τ ω ≠ ⊤ := ne_top_of_lt hlt
  have ht : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    have : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) = τ ω := ENNReal.coe_toNNReal hne
    rw [this]; exact hlt
  have hφH : tsupport φ ⊆ H := φ.tsupport_subset
  rw [integral_frozenMean_mul_eq (ρL := ρL) (ρR := ρR) hP ht hφH hdisj (hu ω),
    retainedGreenEnergy_eq_loewnerGreenEnergy (ρL := ρL) (ρR := ρR) hP ht hφH hdisj]
  rfl

end Bridge

end WangWu

end InteractingSLE
