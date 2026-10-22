import HigherDimLQGMetric.Markov.BoundarySigma
import HigherDimLQGMetric.Field.Version

/-! The two Markov components determine the sphere-centered field across a null frontier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem markov_sphere_pair_recenter (g : DistRd d) (z : Rd d) (r : ℝ)
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) (φ : TestRd d) :
    (addConst g (-sphereAvg g r z)) φ =
      recenter ρ g φ +
        (addConst g (-sphereAvg g r z)) ρ * ∫ x, φ x := by
  let Z := addConst g (-sphereAvg g r z)
  have heq : recenter ρ Z φ = recenter ρ g φ := by
    exact congrArg (fun T : DistRd d => T φ) (recenter_addConst hρ g _)
  rw [← heq, recenter_apply]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- Each pairing of the sphere-normalized field has a version measurable from its two
Markov components when the frontier is null. -/
theorem markov_sphere_pair_ae_decompMeas (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    (z : Rd d) (r : ℝ) {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V))
    (hYm : Measurable Y)
    (hYae : ∀ x (hx : x ∈ extOpen V),
      (fun ω => Y ω x) =ᵐ[P]
        (markovPointVec (by omega : 1 ≤ d) hh V hVb hρ hρV x hx : Ω → ℝ))
    (hnull : volume (frontier (V : Set (Rd d))) = 0)
    (φ : TestRd d) :
    let R := markovSphereResidual (h := h) V z r ρ Y
    let X : Ω → DistOn V × DistOn (extOpen V) := fun ω =>
      (restrictTo V (markovSphereField h z r ω), R ω)
    AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun ω => markovSphereField h z r ω φ) P := by
  dsimp
  let R := markovSphereResidual (h := h) V z r ρ Y
  let X : Ω → DistOn V × DistOn (extOpen V) := fun ω =>
    (restrictTo V (markovSphereField h z r ω), R ω)
  have hq : Measurable[MeasurableSpace.comap X inferInstance]
      (markovSphereCorrection h z r ρ) := by
    have hi : Measurable[fieldSigmaRd (markovSphereField h z r) V]
        (markovSphereCorrection h z r ρ) :=
      markov_measurable_sphereCorrection V z r hρV
    have hfirst : Measurable[MeasurableSpace.comap X inferInstance]
        (fun ω => restrictTo V (markovSphereField h z r ω)) :=
      measurable_fst.comp (comap_measurable X)
    exact hi.mono hfirst.comap_le le_rfl
  have hc := markov_recenter_pair_ae_decompMeas hd hh V hVb z r hρ hρV
    Y hYc hYm hYae hnull φ
  have hsum : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun ω => (recenter ρ (h ω)) φ +
        markovSphereCorrection h z r ρ ω * ∫ x, φ x) P :=
    hc.add (hq.mul_const _).aestronglyMeasurable
  exact hsum.congr (Filter.Eventually.of_forall fun ω => by
    exact (markov_sphere_pair_recenter (h ω) z r hρ φ).symm)

/-- The entire sphere-normalized distribution, not merely each test pairing, is determined
almost surely by the two Markov components. -/
theorem markov_sphereField_aeDetermined (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    (z : Rd d) (r : ℝ) {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V))
    (hYm : Measurable Y)
    (hYae : ∀ x (hx : x ∈ extOpen V),
      (fun ω => Y ω x) =ᵐ[P]
        (markovPointVec (by omega : 1 ≤ d) hh V hVb hρ hρV x hx : Ω → ℝ))
    (hnull : volume (frontier (V : Set (Rd d))) = 0) :
    let Z := markovSphereField h z r
    let R := markovSphereResidual (h := h) V z r ρ Y
    let X : Ω → DistOn V × DistOn (extOpen V) := fun ω =>
      (restrictTo V (Z ω), R ω)
    LQGMetric.AEDeterminedBy Z X P := by
  dsimp
  let Z := markovSphereField h z r
  let R := markovSphereResidual (h := h) V z r ρ Y
  let X : Ω → DistOn V × DistOn (extOpen V) := fun ω =>
    (restrictTo V (Z ω), R ω)
  have hpair (φ : TestRd d) :
      AEStronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω => Z ω φ) P :=
    markov_sphere_pair_ae_decompMeas hd hh V hVb z r hρ hρV
      Y hYc hYm hYae hnull φ
  let Φ : Ω → CoordJ → ℝ := fun ω c =>
    (hpair (comb ⊤ c)).mk (fun ω => Z ω (comb ⊤ c)) ω
  have hΦ : Measurable[MeasurableSpace.comap X inferInstance] Φ := by
    apply (@measurable_pi_iff Ω CoordJ (fun _ => ℝ)
      (MeasurableSpace.comap X inferInstance) _ _).mpr
    intro c
    exact (hpair (comb ⊤ c)).measurable_mk
  let G : Ω → DistRd d := fun ω => pairJInv ⊤ (Φ ω)
  have hGm : Measurable[MeasurableSpace.comap X inferInstance] G :=
    (measurable_pairJInv ⊤).comp hΦ
  have hGeq : Z =ᵐ[P] G := by
    have hcoord : ∀ᵐ ω ∂P, ∀ c : CoordJ,
        Φ ω c = Z ω (comb ⊤ c) := by
      exact ae_all_iff.mpr fun c => (hpair (comb ⊤ c)).ae_eq_mk.symm
    filter_upwards [hcoord] with ω hω
    have heq : Φ ω = pairJ ⊤ (Z ω) := funext fun c => hω c
    simp only [G, heq, pairJInv_pairJ]
  obtain ⟨F, hFm, hFeq⟩ := hGm.exists_eq_measurable_comp
  refine ⟨F, hFm, ?_⟩
  exact hGeq.trans (Filter.Eventually.of_forall fun ω => congrFun hFeq ω)

end HigherDimLQGMetric
