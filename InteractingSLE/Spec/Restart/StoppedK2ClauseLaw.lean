/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Clause

/-!
# The stopped K2, part 2: the conditional-law clause at a stopping time `τ ≤ V`, from below

Packet PROVE-STOPPEDK2. For a field satisfying the conditional-law clause of the optional hull specification at every
stopping time **before** the stop `V` of the driving filtration killed at `V`, the clause holds at every stopping time
`τ ≤ V` (`condExp_cexp_eq_of_le_stop`), when `V` is announced by stopping times `σₙ < V` and the coordinates, frozen
after `V`, are continuous and ordered: along `τ ∧ σₙ`, Lévy's upward theorem (`ae_tendsto_condExp_stopMin`) and the
continuity of the tested coupling mean and Green energy (`tendsto_cfAt_of_isForceReg`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.StoppedK2

/-! ### The conditional-law clause at a stopping time `τ ≤ V`, from below -/

section Clause

open Coupling Ito
open QuantumZipper (H fwdHull)
open DomainMarkov.Aux79 (IsForceReg tendsto_cfAt_of_isForceReg)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ν : Measure Ω}

omit mΩ in
/-- The tested coupling mean does not depend on the choice of the bounded harmonic extension, at a time whose hull
avoids the support (continuous driver). -/
theorem integral_couplingMean_bhe_eq {w : ℝ≥0 → ℝ} (hw : Continuous fun s : ℝ => w s.toNNReal) {a : ℝ≥0}
    {φ : LQGMetric.TestOn upperHalfPlaneOpens} (hdis : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => w s.toNNReal) a))
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {u v : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u)
    (hv : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) v) :
    ∫ z, couplingMean κ (fun s : ℝ => w s.toNNReal) a u z * φ z =
      ∫ z, couplingMean κ (fun s : ℝ => w s.toNNReal) a v z * φ z := by
  have hfin : (forceJumpSet xL xR).Finite :=
    ((Set.finite_range xL).union (Set.finite_range xR)).insert 0
  have heq := Impl.eqOn_of_isBoundedHarmonicExtension hfin hu hv
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
  · have hzH : z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) a :=
      ⟨tsupport_subset_H φ hz, fun hK => Set.disjoint_left.1 hdis hz hK⟩
    have hpos := im_fwdMap_pos hw a.coe_nonneg hzH ⟨a.coe_nonneg, le_rfl⟩
    simp only [couplingMean]
    rw [heq hpos]
  · simp [image_eq_zero_of_notMem_tsupport hz]

omit mΩ in
/-- The frozen right-hand side with the canonical extension is `cfAt`. -/
theorem frozenRHS_bheProc_eq_cfAt (φ : ℂ → ℝ) (r : Ω → ℝ≥0) (ω : Ω) :
    frozenRHS κ W (fun ω => DomainMarkov.bheProc κ ρL ρR W VL VR ω (r ω)) φ r ω =
      cfAt κ W (DomainMarkov.bheProc κ ρL ρR W VL VR) φ 1 r ω := by
  simp only [frozenRHS, cfAt]
  congr 1
  push_cast
  ring

/-- **The conditional-law clause at every stopping time `τ ≤ V`, from the clause before `V`.** For the killed driving
filtration of `(W, VL, VR)` killed at `V`: if the field satisfies the conditional-law clause at every stopping time
`< V` (`IsCouplingCharFun` with lifetime `V`), the coordinates are almost surely continuous and ordered on all of
`ℝ≥0` (`IsForceReg` with lifetime `⊤`: the process frozen after `V`), and `V` is announced by nondecreasing stopping
times `σₙ < V`, then the clause holds at every stopping time `τ ≤ V`, `τ < ∞`: along `τ ∧ σₙ` the conditional
expectations converge to the one given `𝓕_τ` (`ae_tendsto_condExp_stopMin`) and the kernel values converge by
continuity of the tested mean and energy (`tendsto_cfAt_of_isForceReg`). -/
theorem condExp_cexp_eq_of_le_stop [IsProbabilityMeasure ν] (hX : IsMeasurableKilledDriving W VL VR V)
    {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hXm : ∀ ψ, Measurable fun ω => X ω ψ)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR ν (drivingFiltration ν hX) W VL VR V X)
    (hreg : ∀ᵐ ω ∂ν, IsForceReg W VL VR (fun _ => ⊤) ω)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime (drivingFiltration ν hX) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂ν, ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration ν hX) τ)
    (hτV : ∀ᵐ ω ∂ν, (τ ω : ℝ≥0∞) ≤ V ω ∧ τ ω ≠ ⊤) (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂ν, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace ν (fun ω' => Complex.exp (Complex.I * (X ω' φ : ℂ))) ω =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  set Y : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) with hY
  have hYi : Integrable Y ν :=
    Integrable.of_bound (GFF.measurable_exp_I_mul (hXm φ)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  set ub := DomainMarkov.bheProc κ ρL ρR W VL VR with hub
  have hn : ∀ n, ∀ᵐ ω ∂ν, Disjoint (tsupport φ)
      (fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (τ ω) (σ n ω)).untopD 0 : ℝ≥0)) →
      condExp (hτ.min (hσ n)).measurableSpace ν Y ω =
        cfAt κ W ub φ 1 (fun ω => (min (τ ω) (σ n ω)).untopD 0) ω := by
    intro n
    have hlt : ∀ᵐ ω ∂ν, ((min (τ ω) (σ n ω) : WithTop ℝ≥0) : ℝ≥0∞) < V ω := by
      filter_upwards [hσV] with ω hω using lt_of_le_of_lt (min_le_right _ _) (hω n)
    have h := hcf _ (hτ.min (hσ n)) hlt (fun ω => ub ω ((min (τ ω) (σ n ω)).untopD 0))
      (fun ω => DomainMarkov.isBoundedHarmonicExtension_bheProc ω _) φ
    filter_upwards [h] with ω hω hdis
    rw [hω hdis]
    exact frozenRHS_bheProc_eq_cfAt (φ := φ) (r := fun ω => (min (τ ω) (σ n ω)).untopD 0) ω
  have hlev := ae_tendsto_condExp_stopMin hX hτ hσ hσm hσlim hYi
  filter_upwards [ae_all_iff.2 hn, hlev, hreg, hτV, hσlim] with ω hnω hlω hrω hτω hσω hdis
  obtain ⟨a, hτa⟩ := WithTop.ne_top_iff_exists.1 hτω.2
  have ha : (τ ω).untopD 0 = a := by rw [← hτa, WithTop.untopD_coe]
  set t : ℕ → ℝ≥0 := fun n => (min (τ ω) (σ n ω)).untopD 0 with ht
  have hta : ∀ n, t n ≤ a := fun n => by
    simp only [ht]
    rw [← hτa]
    rcases le_total (a : WithTop ℝ≥0) (σ n ω) with h | h
    · rw [min_eq_left h, WithTop.untopD_coe]
    · rw [min_eq_right h]
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top h)
      rw [← hb, WithTop.untopD_coe]
      exact WithTop.coe_le_coe.1 (hb ▸ h)
  have htlim : Tendsto t atTop (𝓝 a) := by
    have h1 : Tendsto (fun n => min (τ ω : ℝ≥0∞) (σ n ω : ℝ≥0∞)) atTop (𝓝 (min (τ ω : ℝ≥0∞) (V ω))) :=
      tendsto_const_nhds.min hσω
    rw [min_eq_left hτω.1] at h1
    have h2 := (ENNReal.tendsto_toNNReal (show (τ ω : ℝ≥0∞) ≠ ⊤ from hτω.2)).comp h1
    rw [← ha]
    exact h2
  have hdis' : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a : ℝ)) := by
    rw [← ha]; exact hdis
  obtain ⟨-, hcfl⟩ := tendsto_cfAt_of_isForceReg (u := ub)
    (fun ω s => DomainMarkov.isBoundedHarmonicExtension_bheProc ω s) φ hrω
    (show ((a : ℝ≥0) : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) hdis' htlim
  have hdn : ∀ n, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (t n : ℝ)) := fun n =>
    hdis'.mono_right (QuantumZipper.fwdHull_mono.1 (by exact_mod_cast hta n))
  have hlim2 : Tendsto (fun n => condExp (hτ.min (hσ n)).measurableSpace ν Y ω) atTop
      (𝓝 (cfAt κ W ub φ 1 (fun _ => a) ω)) :=
    hcfl.congr fun n => (hnω n (hdn n)).symm
  have key := tendsto_nhds_unique hlω hlim2
  rw [key, ha]
  have hc : Continuous (W · ω) :=
    continuousOn_univ.1 (hrω.2.1.mono fun t _ => ENNReal.coe_lt_top)
  have hwc : Continuous fun s : ℝ => W s.toNNReal ω := hc.comp continuous_real_toNNReal
  have hu' := hu ω
  rw [ha] at hu'
  rw [integral_couplingMean_bhe_eq (w := (W · ω)) hwc hdis' hu'
    (DomainMarkov.isBoundedHarmonicExtension_bheProc ω a)]
  exact (frozenRHS_bheProc_eq_cfAt (W := W) (VL := VL) (VR := VR) (φ := φ) (r := fun _ => a) ω).symm

end Clause

end InteractingSLE.Restart.StoppedK2
