import SupercriticalConformalCovariance.GM24.Final
import SupercriticalConformalCovariance.TV.Proposition210

/-!
# IG4 Prop 2.10(i) from the total-variation module, in the normalized-field form

Consumes `SupercriticalConformalCovariance.TV.ig4_prop210_zeroBoundary_bounded` (
standard axioms). Its carrier is `ℕ → ℝ`, coordinates `u ↦ u (recTest B ρ (distGen B (unpair n)))`. With
`ρ = f_r` these are exactly the `distGen` coordinates of the normalized field `nrm f_r u` (which generate
the σ-algebra of `𝒟'(B)`, LQGMetric `distOn_measurableSpace_eq_comap`). Hence:

* `tvDist_nrm_le_carrier`: TV of normalized laws on `B` ≤ TV on the total-variation module's carrier;
* `ig4NrmInput_of_TV1`: `IG4NrmInput` for a centred disk `B = B(0,R)` (the total-variation module's theorem, by contradiction
  from its sequential form);
* the conditional CM/energy route is retained only in `SupercriticalConformalCovariance.GM24.Superseded`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter Topology
open scoped ENNReal
open LQGMetric QuantumZipper

namespace SupercriticalConformalCovariance.GM24

open SmallGammaGeodesics.CC (testOnOfSupp recTest coe_recTest inclTest coe_inclTest)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

theorem distGen_nrm_restrictDist {B V : Opens ℂ} (hBV : B ≤ V) {F : TestC}
    (hFB : tsupport (F : ℂ → ℝ) ⊆ B) (hF1 : ∫ x, F x = 1) (u : DistOn V) (j : ℕ × ℕ) :
    nrm (testOnOfSupp B F hFB) (restrictDist hBV u) (distGen B j) =
      SupercriticalConformalCovariance.TV.localCountablePathOn B V hBV F hFB hF1 u (Nat.pair j.1 j.2) := by
  rw [nrm_apply, restrictDist_apply, restrictDist_apply]
  change _ = u (SupercriticalConformalCovariance.TV.localMeanZeroGenOn B V hBV F hFB hF1 (Nat.pair j.1 j.2))
  have e : SupercriticalConformalCovariance.TV.localMeanZeroGenOn B V hBV F hFB hF1 (Nat.pair j.1 j.2) =
      TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) (distGen B j) -
        (∫ x, distGen B j x) • TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V)
          (testOnOfSupp B F hFB) := by
    ext x
    change recTest B F (distGen B (Nat.unpair (Nat.pair j.1 j.2))) x =
      TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) (distGen B j) x -
        (∫ x, distGen B j x) * TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V)
          (testOnOfSupp B F hFB) x
    rw [Nat.unpair_pair, coe_recTest, coe_monoCLM_le hBV, coe_monoCLM_le hBV]
    rfl
  rw [e, map_sub, map_smul, smul_eq_mul]
  ring

theorem distGen_nrm_restrictTo {B : Opens ℂ} {F : TestC}
    (hFB : tsupport (F : ℂ → ℝ) ⊆ B) (hF1 : ∫ x, F x = 1) (u : DistC) (j : ℕ × ℕ) :
    nrm (testOnOfSupp B F hFB) (restrictTo B u) (distGen B j) =
      SupercriticalConformalCovariance.TV.localCountablePath B F hFB hF1 u (Nat.pair j.1 j.2) := by
  rw [nrm_apply]
  change u (inclTest B (distGen B j)) - u (inclTest B (testOnOfSupp B F hFB)) * _ =
    u (recTest B F (distGen B (Nat.unpair (Nat.pair j.1 j.2))))
  rw [Nat.unpair_pair, recTest, map_sub, map_smul, smul_eq_mul]
  have e1 : inclTest B (testOnOfSupp B F hFB) = F := by
    ext x; rw [coe_inclTest]; rfl
  have e2 : (∫ x, inclTest B (distGen B j) x) = ∫ x, distGen B j x := by rw [coe_inclTest]
  rw [e1, e2]
  ring

/-- **Data processing to the total-variation module's carrier.** -/
theorem tvDist_nrm_le_carrier {B V : Opens ℂ} (hBV : B ≤ V) {F : TestC}
    (hFB : tsupport (F : ℂ → ℝ) ⊆ B) (hF1 : ∫ x, F x = 1) {z : Ω → DistOn V} (hz : Measurable z)
    {h : Ω → DistC} (hh : Measurable h) :
    TV.tvDist (P.map (nrm (testOnOfSupp B F hFB) ∘ fun ω => restrictDist hBV (z ω)))
        (P.map (nrm (testOnOfSupp B F hFB) ∘ fun ω => restrictTo B (h ω))) ≤
      TV.tvDist (SupercriticalConformalCovariance.TV.zbLocalCountableLaw B V hBV F hFB hF1 z P)
        (SupercriticalConformalCovariance.TV.wpLocalCountableLaw B F hFB hF1 h P) := by
  let ι : DistOn B → ℕ × ℕ → ℝ := fun u j => u (distGen B j)
  have hι : Measurable ι := measurable_pi_iff.2 fun j => measurable_distOn_apply _
  let re : (ℕ → ℝ) → ℕ × ℕ → ℝ := fun x j => x (Nat.pair j.1 j.2)
  have hre : Measurable re := measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hn := measurable_nrm (testOnOfSupp B F hFB)
  have hzr : Measurable fun ω => restrictDist hBV (z ω) := (measurable_restrictDist hBV).comp hz
  have hhr : Measurable fun ω => restrictTo B (h ω) := (measurable_restrictTo B).comp hh
  rw [tvDist_eq_map_of_comap (ι := ι) (distOn_measurableSpace_eq_comap B),
    Measure.map_map hι (hn.comp hzr), Measure.map_map hι (hn.comp hhr)]
  have e1 : ι ∘ (nrm (testOnOfSupp B F hFB) ∘ fun ω => restrictDist hBV (z ω)) =
      re ∘ (SupercriticalConformalCovariance.TV.localCountablePathOn B V hBV F hFB hF1 ∘ z) := by
    funext ω j
    exact distGen_nrm_restrictDist hBV hFB hF1 (z ω) j
  have e2 : ι ∘ (nrm (testOnOfSupp B F hFB) ∘ fun ω => restrictTo B (h ω)) =
      re ∘ (SupercriticalConformalCovariance.TV.localCountablePath B F hFB hF1 ∘ h) := by
    funext ω j
    exact distGen_nrm_restrictTo hFB hF1 (h ω) j
  rw [e1, e2, ← Measure.map_map hre ((SupercriticalConformalCovariance.TV.measurable_localCountablePathOn B V hBV F hFB hF1).comp hz),
    ← Measure.map_map hre ((SupercriticalConformalCovariance.TV.measurable_localCountablePath B F hFB hF1).comp hh)]
  exact TV.tvDist_map_le hre

/-- **`IG4NrmInput` from the total-variation module's IG4 Prop 2.10(i)**, for a centred disk `B = B(0,R)`. -/
theorem ig4NrmInput_of_TV1 {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {B : Opens ℂ} {R : ℝ}
    (hB : (B : Set ℂ) = ball 0 R) (hR : 0 < R) {F : TestC} (hFB : tsupport (F : ℂ → ℝ) ⊆ B)
    (hF1 : ∫ x, F x = 1) : IG4NrmInput P h B (testOnOfSupp B F hFB) := by
  by_contra hne
  simp only [IG4NrmInput, not_forall, not_exists, not_le, exists_prop] at hne
  obtain ⟨ε, hε, hbad⟩ := hne
  choose V hBV hVb hρV z hz hgt using fun n : ℕ => hbad (n : ℝ)
  have hT := SupercriticalConformalCovariance.TV.ig4_prop210_zeroBoundary_bounded (fun _ => Ω) B R hB hR F hFB hF1 h P hh V hVb
    (fun n => (n : ℝ)) tendsto_natCast_atTop_atTop
    (fun n => ball_subset_closedBall.trans (hρV n)) z (fun _ => P) hz
  have hev := (ENNReal.tendsto_nhds_zero.1 hT) (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨n, hn⟩ := hev.exists
  have hle := tvDist_nrm_le_carrier (P := P) (hBV n) hFB hF1 (hz n).measurable hh.measurable
  have e : SupercriticalConformalCovariance.TV.ig4ZBLaw (fun _ => Ω) B F hFB hF1 h P V z (fun _ => P) n =
      SupercriticalConformalCovariance.TV.zbLocalCountableLaw B (V n) (hBV n) F hFB hF1 (z n) P := by
    simp only [SupercriticalConformalCovariance.TV.ig4ZBLaw, dif_pos (show (B : Set ℂ) ⊆ V n from hBV n)]
  rw [e] at hn
  have := (hgt n).trans_le (hle.trans hn)
  exact absurd this (not_lt.2 (ENNReal.half_le_self))

end SupercriticalConformalCovariance.GM24
