/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.TransferFilt
import InteractingSLE.Spec.Sec4.HistBorel

/-!
# The conditional-law clause at a general stopping time, read from the history

Packet PROVE-FLOWEXIST2, named input (i). `Sec4.IsOptionalHullCoupling.ae_condExp_hist` reads the frozen conditional-law
clause of `IsOptionalHullCoupling` at a *stopping rule* (a function of the killed history) through the history
through the stop. Here the same is done at an arbitrary stopping time `τ < ζ` of the frozen driving filtration, with
the history stopped at the (random) time `τ` (`stopHistory (fun _ => T)` at `T = τ.untopD 0`, pointwise):

* `IsOptionalHullCoupling.ae_condExp_histAt`: almost surely on the avoidance event of the history hull,
  `E[e^{i(h, φ)} | 𝓕_τ]` is the history functional `G φ` of the history stopped at `τ`;
* `histHull_eq_fwdHull`: at a good stop, the hull read from the history **is** the Loewner hull `K_T` (the hull is
  relatively closed in `ℍ`), so the history avoidance event is the frozen one;
* `histCharFun_eq_of_goodStop`: at a good stop, for **every** bounded harmonic extension `u` of the boundary data at
  `T`, the history functional `histCharFun` is the frozen right-hand side with `u` (bounded harmonic extensions agree
  on `ℍ`, and `f_T` maps `supp φ ⊆ ℍ ∖ K_T` into `ℍ`);
* `measurable_hitting_of_measurableSet_disjoint`: a random set with measurable avoidance events of compact sets is
  measurable for the hitting σ-algebra.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

open Sec4 LawUnique LQGMetric Coupling

variable {nL nR : ℕ}

/-- A finite `WithTop ℝ≥0` time is the coercion of its `untopD 0`. -/
theorem coe_untopD_of_lt {a : WithTop ℝ≥0} {b : ℝ≥0∞} (h : (a : ℝ≥0∞) < b) :
    (((a.untopD 0 : ℝ≥0) : WithTop ℝ≥0) = a) ∧ (((a.untopD 0 : ℝ≥0) : ℝ≥0∞) < b) := by
  have ha : a ≠ ⊤ := by
    rintro rfl
    exact absurd h (not_lt_of_ge le_top)
  obtain ⟨c, rfl⟩ := WithTop.ne_top_iff_exists.1 ha
  exact ⟨rfl, h⟩

/-! ### Deterministic facts at a good stop -/

section Det

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω}

/-- At a good stop the driver read from the history is continuous. -/
theorem continuous_histDrive_of_goodStop (hg : IsGoodStop (fun _ => T) W VL VR ζ ω) :
    Continuous (histDrive (stopHistory (fun _ => T) (killedHistory W VL VR ζ ω))) := by
  rw [histDrive_stopHistory hg.1 hg.2.1]
  exact (continuous_stopped hg.2.1 hg.1).comp continuous_real_toNNReal

/-- At a good stop `ℍ ∖ K_T` is open. -/
theorem isOpen_H_diff_fwdHull_of_goodStop (hg : IsGoodStop (fun _ => T) W VL VR ζ ω) :
    IsOpen (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) T) := by
  rw [fwdHull_histDrive hg]
  exact FwdHolo.isOpen_compl_fwdHull (continuous_histDrive_of_goodStop hg) T.coe_nonneg

/-- **At a good stop the hull read from the history is the Loewner hull `K_T`.** -/
theorem histHull_eq_fwdHull (hg : IsGoodStop (fun _ => T) W VL VR ζ ω) :
    histHull (stopHistory (fun _ => T) (killedHistory W VL VR ζ ω)) =
      fwdHull (fun s : ℝ => W s.toNNReal ω) T := by
  rw [histHull_stopHistory hg]
  have hO := isOpen_H_diff_fwdHull_of_goodStop hg
  refine Subset.antisymm ?_ fun z hz => ⟨subset_closure hz, hz.1⟩
  rintro z ⟨hzc, hzH⟩
  by_contra hzK
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hzc _ hO ⟨hzH, hzK⟩
  exact hy1.2 hy2

/-- **At a good stop, the history functional is the frozen right-hand side with any bounded harmonic
extension.** -/
theorem histCharFun_eq_of_goodStop (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hg : IsGoodStop (fun _ => T) W VL VR ζ ω) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i T ω - W T ω) (fun i => VR i T ω - W T ω))
      (forceJumpSet (fun i => VL i T ω - W T ω) (fun i => VR i T ω - W T ω)) u)
    {φ : TestOn upperHalfPlaneOpens}
    (hdis : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) T)) :
    histCharFun κ ρL ρR φ (stopHistory (fun _ => T) (killedHistory W VL VR ζ ω)) =
      Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (T : ℝ) u z * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (T : ℝ) φ : ℝ) : ℂ)) := by
  set γ := stopHistory (fun _ => T) (killedHistory W VL VR ζ ω) with hγ
  have hT : γ.1.toNNReal = T := stopHistory_fst_toNNReal _
  have hW : histPath γ γ.1.toNNReal = W T ω := by
    rw [hT, hγ, histPath_stopHistory hg.1 hg.2.1, min_self]
  have hspec := histHarm_spec κ ρL ρR γ
  have hL : (fun i => histVL γ i - histPath γ γ.1.toNNReal) = fun i => VL i T ω - W T ω := by
    funext i
    rw [hW, hγ, histVL_stopHistory hg.1 hg.2.2.1]
  have hR : (fun i => histVR γ i - histPath γ γ.1.toNNReal) = fun i => VR i T ω - W T ω := by
    funext i
    rw [hW, hγ, histVR_stopHistory hg.1 hg.2.2.2]
  rw [hL, hR] at hspec
  have hc := continuous_histDrive_of_goodStop hg
  have hK : fwdHull (fun s : ℝ => W s.toNNReal ω) T = fwdHull (histDrive γ) T := by
    exact fwdHull_histDrive hg
  have hI := integral_couplingMean_histDrive (κ := κ) hg u φ
  have hE := loewnerGreenEnergy_histDrive hg (φ := (φ : ℂ → ℝ))
  unfold histCharFun
  rw [hT, hI, hE]
  congr 4
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport φ
  · simp only [couplingMean]
    have hzH : z ∈ H := φ.tsupport_subset hz
    have hzK : z ∉ fwdHull (histDrive γ) T := by
      rw [← hK]; exact Set.disjoint_left.1 hdis hz
    have hpos : fwdMap (histDrive γ) T z ∈ H :=
      FwdHolo.mapsTo_fwdMap hc T.coe_nonneg ⟨hzH, hzK⟩
    rw [eq_meanHarmonic_of_isBoundedHarmonicExtension κ ρL ρR hspec hpos,
      eq_meanHarmonic_of_isBoundedHarmonicExtension κ ρL ρR hu hpos]
  · simp [image_eq_zero_of_notMem_tsupport hz]

end Det

/-! ### The conditional-law clause at a general stopping time -/

/-- **The conditional-law clause read from the history stopped at `τ`.** In a coupling with the frozen optional hull
specification, at a stopping time `τ < ζ` of the driving filtration, almost surely on the event that `supp φ` avoids
the hull read from the history stopped at `τ`, `E[e^{i(h, φ)} | 𝓕_τ]` is the functional `G φ` of that history, for
every `G` that is `histCharFun` on continuous histories avoiding `supp φ` and every `A` that is `histHull` on
continuous histories. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.ae_condExp_histAt {κ : ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {A : HistorySpace nL nR → Set ℂ} (hAeq : ∀ γ, IsContHist γ → A γ = histHull γ)
    {G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ}
    (hGeq : ∀ (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR), IsContHist γ →
      Disjoint (tsupport φ) (histHull γ) → G φ γ = histCharFun κ ρL ρR φ γ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ o ∂P, IsGoodStop (fun _ => (τ o).untopD 0) W VL VR ζ o ∧
      (Disjoint (tsupport φ) (A (stopHistory (fun _ => (τ o).untopD 0) (killedHistory W VL VR ζ o))) →
        P[fun o => Complex.exp (Complex.I * (h o φ : ℂ)) | hτ.measurableSpace] o =
          G φ (stopHistory (fun _ => (τ o).untopD 0) (killedHistory W VL VR ζ o))) := by
  classical
  have hgood : ∀ᵐ o ∂P, IsGoodStop (fun _ => (τ o).untopD 0) W VL VR ζ o := by
    filter_upwards [hτζ, hC.1.2.2.2.2] with o h1 hp
    exact ⟨(coe_untopD_of_lt h1).2, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
  obtain ⟨-, -, -, hX', hτc⟩ := hC
  let u : Ω → ℂ → ℝ := fun o => Classical.choose
    (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
      (fun i => VL i ((τ o).untopD 0) o - W ((τ o).untopD 0) o)
      (fun i => VR i ((τ o).untopD 0) o - W ((τ o).untopD 0) o))
  have hu : ∀ o, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ o).untopD 0) o - W ((τ o).untopD 0) o)
        (fun i => VR i ((τ o).untopD 0) o - W ((τ o).untopD 0) o))
      (forceJumpSet (fun i => VL i ((τ o).untopD 0) o - W ((τ o).untopD 0) o)
        (fun i => VR i ((τ o).untopD 0) o - W ((τ o).untopD 0) o)) (u o) := fun o =>
    Classical.choose_spec (exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR _ _)
  have hcl := (hτc τ hτ hτζ).2 u hu φ
  filter_upwards [hcl, hgood] with o ho hg
  refine ⟨hg, fun hdisj => ?_⟩
  have hcont := isContHist_stopHistory hg
  rw [hAeq _ hcont] at hdisj
  rw [hGeq _ _ hcont hdisj]
  rw [histHull_eq_fwdHull hg] at hdisj
  rw [histCharFun_eq_of_goodStop κ ρL ρR hg (hu o) hdisj]
  exact ho hdisj

/-! ### Hitting measurability -/

/-- A random set with measurable avoidance events of compact sets is measurable for the hitting σ-algebra. -/
theorem measurable_hitting_of_measurableSet_disjoint {Y : Type*} [MeasurableSpace Y] {A : Y → Set ℂ}
    (hA : ∀ K : Set ℂ, IsCompact K → MeasurableSet {y | Disjoint K (A y)}) :
    Measurable[_, hittingSigma] A := by
  refine @measurable_generateFrom _ _ _ _ _ ?_
  rintro _ ⟨U, hU, -, rfl⟩
  have e : A ⁻¹' {T : Set ℂ | (T ∩ U).Nonempty} =
      (⋂ b : ℚ × ℚ × ℚ, ⋂ (_ : ratCBall b ⊆ U), {y | Disjoint (ratCBall b) (A y)})ᶜ := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_iInter]
    rw [← not_disjoint_iff_nonempty_inter, disjoint_iff_forall_ratCBall hU]
  rw [e]
  exact (MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
    hA _ (isCompact_ratCBall b)).compl

end Exist

end InteractingSLE
