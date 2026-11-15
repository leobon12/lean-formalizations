/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField3Noise
import InteractingSLE.Spec.Coupling.WholeField3Freeze
import InteractingSLE.Spec.Coupling.WholeField3QV
import InteractingSLE.Spec.Coupling.WholeField2Germ
import InteractingSLE.Spec.Coupling.MartMeansPath
import InteractingSLE.Spec.Sec7.CounterflowHullBound
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import InteractingSLE.Spec.Sec2.GirsanovDensity
import InteractingSLE.Impl.ForceBoundaryData
import MathFin.Probability.Brownian.BrownianMartingale

/-!
# C.2: the driving noise stays a martingale after the hull germ is retained

Packet PROVE-WHOLEFIELD3 (follow-up note Part C.2, `source/external/AstraIG1/ig1_followup_proofs.txt` L1497–1527;
additional note §7.4, Aux. lemma 47, `ig1_additional_proofs.txt` L3070–3092; rulings R38, R39).

Fix a bounded stop `S ≤ N` of the driving filtration with `S < ζ`, and the stopped germ filtration
`𝒢_t = Γ(𝓕_{t∧S}, K_{t∧S})` of `WholeField.exists_germFiltration_martingale`. **The stopped noise `B_{t∧S}` is a
`𝒢`-martingale** (`martingale_stoppedNoise_germ`). The proof is the one of the notes ("the high-point averaging test
and finite sums"):

* **High point** (`isSafeAt_highPt`). `z = iY`, `Y = 2√N + 3`; the closed ball `B̄(z, 1)` stays above height
  `2√N`, hence (hull-height bound `(Im f_t(y))² ≥ (Im y)² − 4t`) it is safe, at level `2`, at every time `≤ S`.
* **(WF5) in point form.** By the mean value property for the radial bump on `B̄(z, 1)`, the germ martingale of
  `exists_germFiltration_martingale` for that bump is `c (𝔥_{t∧S}(z) − 𝔥₀(z))`; so `t ↦ 𝔥_{t∧S}(z)` is a
  `𝒢`-martingale (`martingale_meanHigh_germ`), and so is its stop at each localizing time.
* **(WF6), brackets.** The localizing stops `ρ_n` of the Itô layer are stops of the driving filtration
  (`exists_localizingSeq_driving`). Stopped at `ρ_n`, `𝔥(z)`, `B` and their brackets `∫ k²`, `∫ k`, `t`
  (`k = Im(2/f_t(z))`) are martingales of the usual augmentation of the evolution's filtration (Itô layer).
* **Left-endpoint freeze** (`martingale_of_bracket_freeze_of_adapted`): `B_{·∧ρ_n}` is a `𝒢`-martingale. The
  localization is removed with the `L²` bound `E B_{t∧ρ_n}² ≤ t` (`Sec7.martingale_of_tendsto_of_sq_bound`); `ρ_n = S`
  eventually because the high point is never reached before `S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace WholeField

open QuantumZipper Ito Coupling

/-! ### The protected high point -/

section High

/-- The protected high point `iY`, `Y = 2√N + 3`. -/
def highPt (N : ℝ) : ℂ := Complex.I * ((2 * Real.sqrt N + 3 : ℝ) : ℂ)

theorem highPt_im (N : ℝ) : (highPt N).im = 2 * Real.sqrt N + 3 := by
  simp [highPt]

theorem im_ge_of_mem_closedBall_highPt {N : ℝ} {y : ℂ} (hy : y ∈ closedBall (highPt N) 1) :
    2 * Real.sqrt N + 2 ≤ y.im := by
  have h1 : |y.im - (highPt N).im| ≤ 1 := by
    have := Complex.abs_im_le_norm (y - highPt N)
    rw [Complex.sub_im] at this
    exact this.trans (by rw [← dist_eq_norm]; exact mem_closedBall.1 hy)
  rw [highPt_im] at h1
  linarith [(abs_le.1 h1).1]

theorem closedBall_highPt_subset (N : ℝ) : closedBall (highPt N) 1 ⊆ H := fun y hy => by
  have := im_ge_of_mem_closedBall_highPt hy
  show 0 < y.im
  linarith [Real.sqrt_nonneg N]

theorem highPt_mem_closedBall (N : ℝ) : highPt N ∈ closedBall (highPt N) 1 :=
  mem_closedBall_self zero_le_one

/-- **The ball about the high point is safe at every time `≤ N`**, at level `2`. -/
theorem isSafeAt_highPt {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {N : ℝ}
    (hN : 0 ≤ N) {σ₀ r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ) (hrσ : r ≤ σ₀) (hrN : (r : ℝ) ≤ N) :
    IsSafeAt (closedBall (highPt N) 1) 2 N σ₀ ζ w r := by
  refine ⟨hr, hrσ, hrN, fun y hy => ?_⟩
  set T : ℝ := (r : ℝ) with hT
  have hT0 : 0 ≤ T := r.coe_nonneg
  have hwc : ContinuousOn (rpath w) (Icc 0 T) := continuousOn_rpath hw hr
  have hW' : Continuous (clampDrv (rpath w) T) := continuous_clampDrv hT0 hwc
  have hyim := im_ge_of_mem_closedBall_highPt hy
  have hs := Real.sqrt_nonneg N
  have hss := Real.sq_sqrt hN
  have hy0 : 0 < y.im := by linarith
  have h4 : 4 * T < y.im ^ 2 := by nlinarith
  have hnot : y ∉ fwdHull (clampDrv (rpath w) T) T :=
    Sec7.notMem_fwdHull_of_four_mul_lt_im_sq hW' hy0 h4
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem hT0 (show y ∈ H \ fwdHull (clampDrv (rpath w) T) T from
    ⟨hy0, hnot⟩)
  have hu' : IsForwardSol (rpath w) y T u := (isForwardSol_iff_of_eqOn clampDrv_eqOn u).1 hu
  refine ⟨⟨u, hu'⟩, ?_⟩
  have hsq := Sec7.im_fwdMap_sq_ge hW' hy0 hT0 hu
  rw [fwdMap_clampDrv_of_le le_rfl] at hsq
  have hpos : 0 < (fwdMap (rpath w) T y).im :=
    im_fwdMap_pos_of_continuousOn hT0 hwc hy0 ⟨u, hu'⟩ ⟨hT0, le_rfl⟩
  nlinarith

end High

/-! ### Generic helpers -/

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- In a filtration whose σ-algebras contain the null sets, a measurable process that agrees almost surely at each
time with a martingale is a martingale. -/
theorem martingale_of_ae_eq_of_null [IsFiniteMeasure P] {𝒢 : Filtration ℝ≥0 mΩ} {M X : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝒢 P) (hX : ∀ t, Measurable (X t)) (hXM : ∀ t, X t =ᵐ[P] M t)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 t] N) :
    Martingale X 𝒢 P := by
  have hXa : StronglyAdapted 𝒢 X := fun t => by
    refine Measurable.stronglyMeasurable fun A hA => ?_
    have hMm : Measurable[𝒢 t] (M t) := (hM.stronglyAdapted t).measurable
    exact measurableSet_of_ae_eq (𝒢.le t) (hnull t) (hX t hA) (hMm hA)
      ((hXM t).mono fun ω h => by simp only [mem_preimage, h])
  refine ⟨hXa, fun s t hst => ?_⟩
  calc P[X t | 𝒢 s] =ᵐ[P] P[M t | 𝒢 s] := condExp_congr_ae (hXM t)
    _ =ᵐ[P] M s := hM.condExp_ae_eq hst
    _ =ᵐ[P] X s := (hXM s).symm

/-- Equal stopping times have equal σ-algebras. -/
theorem IsStoppingTime.measurableSpace_congr {𝓖 : Filtration ℝ≥0 mΩ} {τ₁ τ₂ : Ω → WithTop ℝ≥0}
    (h₁ : IsStoppingTime 𝓖 τ₁) (h₂ : IsStoppingTime 𝓖 τ₂) (e : τ₁ = τ₂) :
    h₁.measurableSpace = h₂.measurableSpace := by
  subst e; rfl

/-- **Values at `σ ∧ t` are measurable for the σ-algebra of `σ ∧ t`.** If a process `X`, continuous on `[0, σ]` on a
`𝓖₀`-event `G`, agrees there with adapted processes `K s` for `s ≤ σ`, then `ω ↦ X (σ ω ∧ t) ω` (and `c` off `G`) is
measurable for the stopped σ-algebra of `σ ∧ t`. -/
theorem measurable_stoppedAt_of_agree {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓖 : Filtration ℝ≥0 mΩ} {K X : ℝ≥0 → Ω → β} {σ : Ω → ℝ≥0}
    (hK : ∀ s, Measurable[𝓖 s] (K s))
    {G : Set Ω} (hG : MeasurableSet[𝓖 0] G) (c : β) (hKX : ∀ ω ∈ G, ∀ s ≤ σ ω, K s ω = X s ω)
    (hXc : ∀ ω ∈ G, ContinuousOn (X · ω) (Iic (σ ω))) (t : ℝ≥0)
    (hσt : IsStoppingTime 𝓖 fun ω => ((min (σ ω) t : ℝ≥0) : WithTop ℝ≥0)) :
    Measurable[hσt.measurableSpace] fun ω => if ω ∈ G then X (min (σ ω) t) ω else c := by
  have hst := measurable_stopped_of_agree hσt hK hG c
    (fun ω hω s hs => hKX ω hω s (hs.trans (min_le_left _ _)))
    (fun ω hω => (hXc ω hω).mono fun s hs => (mem_Iic.1 hs).trans (min_le_left _ _))
  refine measurable_stoppingTime_of_forall hσt hst fun r ω hr => ?_
  simp only [min_eq_right hr]

end Helpers

/-! ### (WF5) in point form at the high point -/

section Point

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- Bounded harmonic extensions of the force data exist at every state (`Impl`'s companion theorem, positions read
only through the data). -/
theorem exists_bhe (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u := by
  let F : Impl.ForceWord :=
    { nL := nL, nR := nR, xL := fun _ => 0, xR := fun _ => 0, ρL := ρL, ρR := ρR,
      antitone_xL := fun _ _ _ => le_rfl, xL_nonpos := fun _ => le_rfl,
      monotone_xR := fun _ _ _ => le_rfl, xR_nonneg := fun _ => le_rfl }
  obtain ⟨u, hu, -⟩ := Impl.existsUnique_isBoundedHarmonicExtension_forceBoundaryData κ F vL vR
  exact ⟨u, hu⟩

/-- A chosen bounded harmonic extension of the data at the centred state `(vL − w, vR − w)`. -/
def bheAt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ℂ → ℝ :=
  Classical.choose (exists_bhe κ ρL ρR (fun i => vL i - w) (fun i => vR i - w))

theorem bheAt_spec (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => vL i - w) (fun i => vR i - w))
      (forceJumpSet (fun i => vL i - w) (fun i => vR i - w)) (bheAt κ ρL ρR w vL vR) :=
  Classical.choose_spec (exists_bhe κ ρL ρR (fun i => vL i - w) (fun i => vR i - w))

/-- The tested coupling mean against the bump at the high point is the explicit mean at the high point times the
bump mass. -/
theorem integral_couplingMean_mul_bump_highPt {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {N δ : ℝ} {σ₀ r : ℝ≥0}
    (hsafe : IsSafeAt (closedBall (highPt N) 1) δ N σ₀ ζ w r) (hδ : 0 < δ)
    (hvL : ∀ i, vL i r ≤ w r) (hvR : ∀ i, w r ≤ vR i r) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i r - w r) (fun i => vR i r - w r))
      (forceJumpSet (fun i => vL i r - w r) (fun i => vR i r - w r)) u) :
    ∫ y, couplingMean κ (rpath w) r u y * GFF.bumpFun (highPt N) 1 y =
      meanCan κ ρL ρR w vL vR r (highPt N) * (1 ^ 2 * GFF.bumpMass) := by
  rw [← hsafe.integral_meanCan_mul_bumpFun hw (closedBall_highPt_subset N) le_rfl one_pos le_rfl]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ closedBall (highPt N) 1
  · simp only
    rw [couplingMean_eq_meanCan hw (closedBall_highPt_subset N) hsafe hδ le_rfl hy hvL hvR hu]
  · have h0 : GFF.bumpFun (highPt N) 1 y = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hy (GFF.tsupport_bumpFun_subset one_pos h)
    simp only [h0, mul_zero]

end Point

/-! ### The high-point mean is a martingale of the germ filtration -/

section Germ

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The explicit mean `𝔥_{S∧t}(iY)` at the high point (zero off `G`). -/
def meanHigh (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (N : ℝ) (G : Set Ω) (S : Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (min (S ω) t) (highPt N)
  else 0

/-- On the good event the ball about the high point is safe at every time `≤ S`. -/
theorem isSafeAt_highPt_of_path {N : ℝ} (hN : 0 ≤ N) {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {z : ℝ≥0∞} {S : ℝ≥0}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b z ∧ (S : ℝ≥0∞) < z ∧ (S : ℝ) ≤ N) {r : ℝ≥0}
    (hr : r ≤ S) : IsSafeAt (closedBall (highPt N) 1) 2 N S z w r :=
  isSafeAt_highPt hp.1.2.2.2.1 hN (lt_of_le_of_lt (by exact_mod_cast hr) hp.2.1) hr
    ((NNReal.coe_le_coe.2 hr).trans hp.2.2)

/-- **(WF5) in point form: the high-point mean is a germ martingale.** Let `Z` be a `𝒢`-martingale which, at each
time `t`, almost surely on `{supp φ ∩ A_t = ∅}` (`φ` the bump at the high point), equals the tested frozen mean
`(𝔥_{S∧t} − 𝔥₀, φ)`, where `A_t` is almost surely the hull `K_{S∧t}` (this is the germ martingale of
`exists_germFiltration_martingale`). If `𝒢` contains the null sets, then `t ↦ 𝔥_{S∧t}(iY)` is a `𝒢`-martingale. -/
theorem martingale_meanHigh [IsFiniteMeasure P] {𝒢 : Filtration ℝ≥0 mΩ} {N : ℝ} (hN : 0 ≤ N)
    {S : Ω → ℝ≥0} {G : Set Ω}
    (hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ (S ω : ℝ≥0∞) < ζ ω ∧ (S ω : ℝ) ≤ N)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) (hmeas : ∀ t, Measurable (meanHigh κ ρL ρR W VL VR N G S t))
    (hnull : ∀ t (N' : Set Ω), MeasurableSet N' → P N' = 0 → MeasurableSet[𝒢 t] N')
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {A : ℝ≥0 → Ω → Set ℂ}
    (hA : ∀ t, ∀ᵐ ω ∂P, A t ω = fwdHull (rpath (W · ω)) ((min (S ω) t : ℝ≥0) : ℝ))
    {Z : ℝ≥0 → Ω → ℝ} (hZ : Martingale Z 𝒢 P)
    (hid : ∀ t, ∀ᵐ ω ∂P, Disjoint (tsupport (GFF.bumpFun (highPt N) 1)) (A t ω) →
      Z t ω = (∫ y, couplingMean κ (rpath (W · ω)) ((min (S ω) t : ℝ≥0) : ℝ)
          (bheAt κ ρL ρR (W (min (S ω) t) ω) (fun i => VL i (min (S ω) t) ω)
            (fun i => VR i (min (S ω) t) ω)) y * GFF.bumpFun (highPt N) 1 y) -
        ∫ y, u₀ y * GFF.bumpFun (highPt N) 1 y) :
    Martingale (meanHigh κ ρL ρR W VL VR N G S) 𝒢 P := by
  set c : ℝ := 1 ^ 2 * GFF.bumpMass with hc
  have hc0 : 0 < c := by rw [hc]; have := GFF.bumpMass_pos; positivity
  set a : ℝ := u₀ (highPt N) * c with ha
  refine martingale_of_ae_eq_of_null ((hZ.add (martingale_const 𝒢 P a)).smul c⁻¹) hmeas
    (fun t => ?_) hnull
  filter_upwards [hA t, hid t, hGae] with ω hAω hidω hω
  have hp := hGp ω hω
  set r : ℝ≥0 := min (S ω) t with hr
  have hrS : r ≤ S ω := min_le_left _ _
  have hsafe := isSafeAt_highPt_of_path hN hp hrS
  have hw := hp.1.2.2.2.1
  have hrζ : (r : ℝ≥0∞) < ζ ω := hsafe.1
  have hdis : Disjoint (tsupport (GFF.bumpFun (highPt N) 1)) (A t ω) := by
    rw [hAω]
    refine Set.disjoint_left.2 fun y hy hyK => ?_
    have hyB : y ∈ closedBall (highPt N) 1 := GFF.tsupport_bumpFun_subset one_pos hy
    exact notMem_fwdHull_of_alive hw hrζ (closedBall_highPt_subset N hyB)
      (hsafe.2.2.2 y hyB).1 hyK
  have hZω := hidω hdis
  rw [integral_couplingMean_mul_bump_highPt (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hw hsafe
      two_pos (hp.1.2.2.2.2.2.2.2.1 r hrζ)
      (hp.1.2.2.2.2.2.2.2.2.1 r hrζ) (bheAt_spec κ ρL ρR _ _ _),
    GFF.integral_mul_bumpFun_of_harmonic isOpen_H hu₀ one_pos (closedBall_highPt_subset N)] at hZω
  simp only [meanHigh, hω, ↓reduceIte, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hZω]
  rw [← hc, ← ha, ← hr]
  field_simp
  ring

/-- On the good event the high-point mean is continuous in time (and constant off it). -/
theorem continuous_meanHigh {N : ℝ} (hN : 0 ≤ N) {S : Ω → ℝ≥0} {G : Set Ω}
    (hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ (S ω : ℝ≥0∞) < ζ ω ∧ (S ω : ℝ) ≤ N) (ω : Ω) :
    Continuous (meanHigh κ ρL ρR W VL VR N G S · ω) := by
  by_cases hω : ω ∈ G
  · simp only [meanHigh, hω, ↓reduceIte]
    have hp := hGp ω hω
    have hsafe := isSafeAt_highPt_of_path hN hp (le_refl (S ω))
    have hc := hsafe.continuousOn_meanCan_time (κ := κ) (ρL := ρL) (ρR := ρR)
      (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hp.1.2.2.2.1 hp.1.2.2.2.2.1
      hp.1.2.2.2.2.2.1 (closedBall_highPt_subset N) two_pos (highPt_mem_closedBall N)
    exact hc.comp_continuous (continuous_const.min continuous_id) fun t => mem_Iic.2 (min_le_left _ _)
  · simp only [meanHigh, hω, ↓reduceIte]; exact continuous_const

/-- The high-point mean is adapted (to any filtration in which the driving state is adapted before `ζ`, with `G`
in its initial σ-algebra and `S` a stopping time). -/
theorem measurable_meanHigh {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) {G : Set Ω}
    (hG : MeasurableSet[𝓖 0] G) {N : ℝ} (hN : 0 ≤ N) {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓖 fun ω => (S ω : WithTop ℝ≥0))
    (hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ (S ω : ℝ≥0∞) < ζ ω ∧ (S ω : ℝ) ≤ N) (t : ℝ≥0) :
    Measurable[𝓖 t] (meanHigh κ ρL ρR W VL VR N G S t) := by
  set φ : ℂ → ℝ := GFF.bumpFun (highPt N) 1 with hφ
  set c : ℝ := 1 ^ 2 * GFF.bumpMass with hc
  have hc0 : c ≠ 0 := by rw [hc]; have := GFF.bumpMass_pos; positivity
  have hKH := closedBall_highPt_subset N
  have hφB : tsupport φ ⊆ closedBall (highPt N) 1 := GFF.tsupport_bumpFun_subset one_pos
  have hφH : tsupport φ ⊆ H := hφB.trans hKH
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).1.2.2.2.1
  have hφm : Measurable φ := (GFF.contDiff_bumpFun _ _).continuous.measurable
  have hK : ∀ s, Measurable[𝓖 s] fun ω => meanK κ ρL ρR W VL VR ζ G φ 2 s ω / c := fun s =>
    (measurable_meanK hWa hGc hG hφH two_pos κ ρL ρR hVLa hVRa hφm s).div_const c
  have hKX : ∀ ω ∈ G, ∀ s ≤ S ω, meanK κ ρL ρR W VL VR ζ G φ 2 s ω / c =
      meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s (highPt N) := by
    intro ω hω s hs
    have hsafe := isSafeAt_highPt_of_path hN (hGp ω hω) hs
    have hmem : ω ∈ safeSet W ζ G φ 2 s :=
      ⟨hω, hsafe.1, le_rfl, le_rfl, fun y hy => hsafe.2.2.2 y (hφB hy)⟩
    simp only [meanK, hmem, ↓reduceIte]
    rw [hsafe.integral_meanCan_mul_bumpFun (hGc ω hω) hKH le_rfl one_pos le_rfl, ← hc,
      mul_div_cancel_right₀ _ hc0]
  have hXc : ∀ ω ∈ G, ContinuousOn
      (fun s => meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s (highPt N))
      (Iic (S ω)) := fun ω hω =>
    (isSafeAt_highPt_of_path hN (hGp ω hω) (le_refl (S ω))).continuousOn_meanCan_time
      (hGc ω hω) (hGp ω hω).1.2.2.2.2.1 (hGp ω hω).1.2.2.2.2.2.1 hKH two_pos (highPt_mem_closedBall N)
  have h := measurable_stopped_of_agree hS hK hG 0 hKX hXc t
  convert h using 1
  funext ω
  simp only [meanHigh, min_comm]

end Germ

/-! ### One localization level: the stopped noise -/

section Noise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem stoppedProcess_coe_apply {β : Type*} (X : ℝ≥0 → Ω → β) (σ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess X (fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) t ω = X (min t (σ ω)) ω := by
  show X (min (t : WithTop ℝ≥0) (σ ω)).untopA ω = _
  rw [← WithTop.coe_min]
  rfl

/-- The weight `1_{u < ρ}`. -/
def stopWeight (ρ : Ω → ℝ≥0) (u : ℝ) (ω : Ω) : ℝ := if u < (ρ ω : ℝ) then 1 else 0

theorem stopWeight_nonneg (ρ : Ω → ℝ≥0) (u : ℝ) (ω : Ω) : 0 ≤ stopWeight ρ u ω := by
  unfold stopWeight; split_ifs <;> norm_num

theorem stopWeight_le_one (ρ : Ω → ℝ≥0) (u : ℝ) (ω : Ω) : stopWeight ρ u ω ≤ 1 := by
  unfold stopWeight; split_ifs <;> norm_num

theorem measurable_stopWeight (ρ : Ω → ℝ≥0) (ω : Ω) : Measurable fun u => stopWeight ρ u ω :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- `∫₀ᵗ 1_{u<ρ} g(u) du = ∫₀^{t∧ρ} g(u) du`. -/
theorem integral_stopWeight_mul {ρ : Ω → ℝ≥0} {ω : Ω} {g : ℝ → ℝ} {t : ℝ≥0}
    (hg : IntervalIntegrable g volume 0 t) :
    ∫ u in (0 : ℝ)..t, stopWeight ρ u ω * g u = ∫ u in (0 : ℝ)..((min t (ρ ω) : ℝ≥0) : ℝ), g u := by
  set m : ℝ := ((min t (ρ ω) : ℝ≥0) : ℝ) with hm
  have hm0 : 0 ≤ m := (min t (ρ ω)).coe_nonneg
  have hmt : m ≤ t := by rw [hm]; exact_mod_cast min_le_left _ _
  have hmρ : m ≤ ρ ω := by rw [hm]; exact_mod_cast min_le_right _ _
  have hgi : IntervalIntegrable (fun u => stopWeight ρ u ω * g u) volume 0 t := by
    refine hg.norm.mono_fun' ((measurable_stopWeight ρ ω).aestronglyMeasurable.mul
      hg.def'.aestronglyMeasurable) ?_
    · refine ae_of_all _ fun u => ?_
      simp only [norm_mul, Real.norm_eq_abs]
      have h1 : |stopWeight ρ u ω| ≤ 1 := by
        rw [abs_of_nonneg (stopWeight_nonneg ρ u ω)]; exact stopWeight_le_one ρ u ω
      calc |stopWeight ρ u ω| * |g u| ≤ 1 * |g u| := by gcongr
        _ = ‖g u‖ := by rw [one_mul, Real.norm_eq_abs]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hgi.mono_set (by
      rw [uIcc_of_le hm0, uIcc_of_le t.coe_nonneg]; exact Icc_subset_Icc le_rfl hmt))
    (hgi.mono_set (by
      rw [uIcc_of_le hmt, uIcc_of_le t.coe_nonneg]; exact Icc_subset_Icc hm0 le_rfl))]
  have h2 : ∫ u in m..(t : ℝ), stopWeight ρ u ω * g u = 0 := by
    refine intervalIntegral.integral_zero_ae (ae_of_all _ fun u hu => ?_)
    rw [uIoc_of_le hmt] at hu
    by_cases hmt' : m = t
    · exact absurd hu.2 (by rw [← hmt']; exact not_le.2 hu.1)
    · have hmρ' : m = ρ ω := by
        rcases min_choice t (ρ ω) with h | h
        · exact absurd (by rw [hm, h]) hmt'
        · rw [hm, h]
      simp only [stopWeight, show ¬ u < (ρ ω : ℝ) from not_lt.2 (hmρ' ▸ hu.1.le), ↓reduceIte, zero_mul]
  rw [h2, add_zero]
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (ρ ω : ℝ) := by
    rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
  refine intervalIntegral.integral_congr_ae (hne.mono fun u hne hu => ?_)
  rw [uIoc_of_le hm0] at hu
  have hu' : u < (ρ ω : ℝ) := lt_of_le_of_ne (hu.2.trans hmρ) hne
  simp only [stopWeight, hu', ↓reduceIte, one_mul]

/-- The noise, set to `0` off `G` (a version with everywhere continuous paths). -/
def noiseOn (B : ℝ≥0 → Ω → ℝ) (G : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ := if ω ∈ G then B t ω else 0

theorem continuous_noiseOn {B : ℝ≥0 → Ω → ℝ} {G : Set Ω} (hBc : ∀ ω ∈ G, Continuous (B · ω)) (ω : Ω) :
    Continuous (noiseOn B G · ω) := by
  by_cases hω : ω ∈ G
  · simp only [noiseOn, hω, ↓reduceIte]; exact hBc ω hω
  · simp only [noiseOn, hω, ↓reduceIte]; exact continuous_const

/-- `B` and `B² − t`, modified off a full-measure event, stay martingales of a filtration containing the null
sets. -/
theorem martingale_noiseOn [IsProbabilityMeasure P] {𝓔 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓔 B P)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝓔 t] N) {G : Set Ω}
    (hG : MeasurableSet G) (hG0 : P Gᶜ = 0) :
    Martingale (noiseOn B G) 𝓔 P ∧ Martingale (fun t ω => noiseOn B G t ω ^ 2 - (t : ℝ)) 𝓔 P := by
  have := Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hm := ProbabilityTheory.IsPreBrownianReal.isMartingale B 𝓔 P
  have hsq : Martingale (fun t ω => B t ω ^ 2 - (t : ℝ)) 𝓔 P :=
    ProbabilityTheory.IsFilteredPreBrownian.squareSubTime_isMartingale
  have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓔.le t) le_rfl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have heq : ∀ t, noiseOn B G t =ᵐ[P] B t := fun t =>
    hGae.mono fun ω hω => by simp only [noiseOn, hω, ↓reduceIte]
  have hmeas : ∀ t, Measurable (noiseOn B G t) := fun t =>
    Measurable.ite hG (hBm t) measurable_const
  refine ⟨martingale_of_ae_eq_of_null hm hmeas heq hnull,
    martingale_of_ae_eq_of_null hsq (fun t => ((hmeas t).pow_const 2).sub measurable_const)
      (fun t => (heq t).mono fun ω h => by simp only [h]) hnull⟩

/-- **The stopped noise and its bracket at one localization level.** For a stop `ρ` of a filtration in which `B`
is Brownian and which contains the null sets, `B_{·∧ρ}` (modified off `G`) and `B_{·∧ρ}² − ∫₀ᵗ 1_{u<ρ}` are
martingales. -/
theorem martingale_stoppedNoise [IsProbabilityMeasure P] {𝓔 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓔 B P)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝓔 t] N) {G : Set Ω}
    (hG : MeasurableSet G) (hG0 : P Gᶜ = 0) (hBc : ∀ ω ∈ G, Continuous (B · ω)) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓔 fun ω => (ρ ω : WithTop ℝ≥0)) :
    Martingale (stoppedProcess (noiseOn B G) fun ω => (ρ ω : WithTop ℝ≥0)) 𝓔 P ∧
      Martingale (fun t ω => stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω ^ 2 -
        ∫ u in (0 : ℝ)..t, stopWeight ρ u ω) 𝓔 P := by
  obtain ⟨h1, h2⟩ := martingale_noiseOn hB hnull hG hG0
  refine ⟨Martingale.stoppedProcess_of_rightContinuous h1
    (fun ω t => (continuous_noiseOn hBc ω).continuousWithinAt) hρ, ?_⟩
  have e : (fun t ω => stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω ^ 2 -
      ∫ u in (0 : ℝ)..t, stopWeight ρ u ω) =
      stoppedProcess (fun t ω => noiseOn B G t ω ^ 2 - (t : ℝ)) fun ω => (ρ ω : WithTop ℝ≥0) := by
    funext t ω
    rw [stoppedProcess_coe_apply, stoppedProcess_coe_apply]
    have hi := integral_stopWeight_mul (ρ := ρ) (ω := ω) (g := fun _ => (1 : ℝ)) (t := t)
      intervalIntegrable_const
    simp only [mul_one] at hi
    rw [hi, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rw [e]
  exact Martingale.stoppedProcess_of_rightContinuous h2
    (fun ω t => (((continuous_noiseOn hBc ω).pow 2).sub NNReal.continuous_coe).continuousWithinAt) hρ

/-- **The stopped running integral is adapted.** For a continuous coefficient `g` adapted to `𝓖` and a stop `ρ`,
`ω ↦ ∫₀ᵗ 1_{u<ρ} g(u) du` is `𝓖_t`-measurable (the integrand is right-continuous and adapted, hence progressive). -/
theorem stronglyMeasurable_integral_stopWeight {𝓖 : Filtration ℝ≥0 mΩ} {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓖 fun ω => (ρ ω : WithTop ℝ≥0)) {g : ℝ → Ω → ℝ}
    (hgc : ∀ ω, Continuous (g · ω)) (hga : ∀ p : ℝ≥0, Measurable[𝓖 p] (g p)) (t : ℝ≥0) :
    StronglyMeasurable[𝓖 t] fun ω => ∫ u in (0 : ℝ)..t, stopWeight ρ u ω * g u ω := by
  set θ : ℝ≥0 → Ω → ℝ := fun p ω => stopWeight ρ p ω * g p ω with hθ
  have hθa : StronglyAdapted 𝓖 θ := fun p => by
    have hset : MeasurableSet[𝓖 p] {ω | ((p : ℝ≥0) : ℝ) < (ρ ω : ℝ)} := by
      have := hρ.measurableSet_gt p
      convert this using 1
      ext ω; simp only [mem_ofPred_eq, WithTop.coe_lt_coe, NNReal.coe_lt_coe]
    have hw : Measurable[𝓖 p] fun ω => stopWeight ρ p ω :=
      Measurable.ite hset measurable_const measurable_const
    exact (hw.mul (hga p)).stronglyMeasurable
  have hθrc : ∀ ω t, ContinuousWithinAt (θ · ω) (Ici t) t := by
    intro ω t
    by_cases ht : (t : ℝ) < ρ ω
    · have hev : ∀ᶠ p in 𝓝[Ici t] t, θ p ω = g p ω := by
        have hopen : {p : ℝ≥0 | (p : ℝ) < ρ ω} ∈ 𝓝 t :=
          (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds ht
        filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with p hp
        simp only [hθ, stopWeight, show (p : ℝ) < ρ ω from hp, ↓reduceIte, one_mul]
      have hc : ContinuousWithinAt (fun p : ℝ≥0 => g p ω) (Ici t) t :=
        ((hgc ω).comp NNReal.continuous_coe).continuousWithinAt
      refine hc.congr_of_eventuallyEq hev ?_
      simp only [hθ, stopWeight, ht, ↓reduceIte, one_mul]
    · have hzero : ∀ p ∈ Ici t, θ p ω = 0 := fun p hp => by
        have : ¬ (p : ℝ) < ρ ω := fun h => ht (lt_of_le_of_lt (by exact_mod_cast hp) h)
        simp only [hθ, stopWeight, this, ↓reduceIte, zero_mul]
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr hzero (hzero t self_mem_Ici)
  have hprog := isStronglyProgressive_of_rightContinuous hθa hθrc
  have h := Girsanov.stronglyMeasurable_integral_comp hprog measurable_id t
  have e : (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), id (θ u.toNNReal ω)) =
      fun ω => ∫ u in (0 : ℝ)..t, stopWeight ρ u ω * g u ω := by
    funext ω
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le t.coe_nonneg] at hu
    simp only [id, hθ, Real.coe_toNNReal _ hu.1]
  rwa [e] at h

end Noise

/-! ### One localization level: the coefficient `k = Im(2/f_t(iY))` -/

section Coef

/-- Pathwise properties of the coefficient `u ↦ Im(2/f_{r∧u}(iY))` up to a time `r ≤ N` before the lifetime:
continuity, `|k| ≤ 1`, and `|k| ≥ 4/L²` with `L = ‖iY‖ + 24R + 8√N` when `|w| ≤ R` on `[0, r]`. -/
theorem coef_pathwise {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {N : ℝ} (hN : 0 ≤ N) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ) (hrN : (r : ℝ) ≤ N) {R : ℝ}
    (hR : ∀ s ≤ r, |w s| ≤ R) :
    Continuous (fun u : ℝ => (2 / fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) (highPt N)).im) ∧
      ∀ u : ℝ, |(2 / fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) (highPt N)).im| ≤ 1 ∧
        4 / (‖highPt N‖ + 24 * R + 8 * Real.sqrt N) ^ 2 ≤
          |(2 / fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) (highPt N)).im| := by
  set z := highPt N with hz
  have hsafe := isSafeAt_highPt hw hN hr le_rfl hrN
  have hzB := highPt_mem_closedBall N
  have hKH := closedBall_highPt_subset N
  have hz0 : 0 < z.im := hKH hzB
  have hwc : ContinuousOn (rpath w) (Icc 0 (r : ℝ)) := continuousOn_rpath hw hr
  have halive : ∃ v, IsForwardSol (rpath w) z r v := (hsafe.2.2.2 z hzB).1
  have him : ∀ u : ℝ, 2 ≤ (fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) z).im := fun u =>
    hsafe.le_im_fwdMap hw hKH (min_le_left _ _) hzB
  -- the norm bound, through the clamped driver
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR 0 zero_le)
  have hnorm : ∀ u : ℝ, ‖fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) z‖ ≤
      ‖z‖ + 24 * R + 8 * Real.sqrt N := by
    intro u
    set s : ℝ := ((min r u.toNNReal : ℝ≥0) : ℝ) with hs
    have hsI : s ∈ Icc (0 : ℝ) r := ⟨NNReal.coe_nonneg _, by rw [hs]; exact_mod_cast min_le_left _ _⟩
    have hc := continuous_clampDrv r.coe_nonneg hwc
    have hc0 : clampDrv (rpath w) r 0 = 0 := by
      rw [clampDrv_eqOn ⟨le_rfl, r.coe_nonneg⟩]; simp [rpath, hw0]
    have hM : ∀ q ∈ Icc (0 : ℝ) r, |clampDrv (rpath w) r q| ≤ R := fun q hq => by
      rw [clampDrv_eqOn hq]
      exact hR _ (Real.toNNReal_le_iff_le_coe.2 hq.2)
    have h := InteractingSLE.norm_fwdMap_sub_self_le hc hc0 r.coe_nonneg hM
      (mem_diff_fwdHull_clampDrv r.coe_nonneg hwc hz0 halive) hsI
    rw [fwdMap_clampDrv_of_le hsI.2] at h
    have hsq : Real.sqrt r ≤ Real.sqrt N := Real.sqrt_le_sqrt hrN
    calc ‖fwdMap (rpath w) s z‖ ≤ ‖fwdMap (rpath w) s z - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖z‖ + 24 * R + 8 * Real.sqrt N := by linarith
  refine ⟨?_, fun u => ?_⟩
  · have hm : Continuous fun u : ℝ => ((min r u.toNNReal : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_const.min continuous_real_toNNReal)
    have hf : Continuous fun u : ℝ => fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) z :=
      (continuousOn_fwdMap_of_continuousOn r.coe_nonneg hwc hz0 halive).comp_continuous hm
        fun u => ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_left _ _⟩
    refine Complex.continuous_im.comp (continuous_const.div hf fun u h => ?_)
    have := him u
    rw [h, Complex.zero_im] at this
    linarith
  · set f := fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) z with hf
    have hfi := him u
    have hns : f.im ^ 2 ≤ Complex.normSq f := by
      rw [Complex.normSq_apply]; nlinarith [sq_nonneg f.re]
    have hnpos : 0 < Complex.normSq f := lt_of_lt_of_le (by positivity) hns
    have hk : |(2 / f).im| = 2 * f.im / Complex.normSq f := by
      rw [Sec7.im_two_div, abs_div, abs_of_pos hnpos, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < f.im)]
      norm_num
    rw [hk]
    have hL := hnorm u
    rw [← hf] at hL
    have hnsq : Complex.normSq f ≤ (‖z‖ + 24 * R + 8 * Real.sqrt N) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]; gcongr
    constructor
    · rw [div_le_one hnpos]; nlinarith
    · have hLpos : 0 < (‖z‖ + 24 * R + 8 * Real.sqrt N) ^ 2 := lt_of_lt_of_le hnpos hnsq
      rw [div_le_div_iff₀ hLpos hnpos]
      nlinarith

/-- The coefficient `k_u = Im(2/f_{u∧ρ}(iY))` (`−1` off `G`). -/
def coefHigh {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (G : Set Ω) (ρ : Ω → ℝ≥0) (N : ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  if ω ∈ G then (2 / fwdMap (rpath (W · ω)) ((min (ρ ω) u.toNNReal : ℝ≥0) : ℝ) (highPt N)).im else -1

end Coef

/-! ### One localization level: the brackets of (WF6) -/

section Level

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The good event of one level: the path conditions, continuous noise, `ρ ≤ S < ζ`, `S ≤ N`, and the bounds `R`
on `[0, ρ]`. -/
def IsLevelGood (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (N : ℝ) (S ρ : Ω → ℝ≥0) (R : ℝ) (ω : Ω) : Prop :=
  (IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
    (fun t => B t ω) (ζ ω) ∧ (S ω : ℝ≥0∞) < ζ ω ∧ (S ω : ℝ) ≤ N) ∧ Continuous (B · ω) ∧
    ρ ω ≤ S ω ∧ ∀ s ≤ ρ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R

theorem continuous_coefHigh {N : ℝ} (hN : 0 ≤ N) {S ρ : Ω → ℝ≥0} {R : ℝ} {G : Set Ω}
    (hG : ∀ ω ∈ G, IsLevelGood κ xL xR ρL ρR W VL VR B ζ N S ρ R ω) (ω : Ω) :
    Continuous (coefHigh W G ρ N · ω) := by
  by_cases hω : ω ∈ G
  · obtain ⟨⟨hp, hSζ, hSN⟩, -, hρS, hR⟩ := hG ω hω
    simp only [coefHigh, hω, ↓reduceIte]
    exact (coef_pathwise hp.2.2.2.1 hp.1 hN (lt_of_le_of_lt (by exact_mod_cast hρS) hSζ)
      ((NNReal.coe_le_coe.2 hρS).trans hSN) fun s hs => (hR s hs).1).1
  · simp only [coefHigh, hω, ↓reduceIte]; exact continuous_const

/-- **The brackets of one level** ((3.15) of the Itô layer, (WF6) of the note). In the usual augmentation `𝓔` of
the evolution's filtration, for a stop `ρ ≤ S`: the stopped high-point mean `X`, `X² − ∫₀ᵗ 1_{u<ρ} k²` and
`X Y − ∫₀ᵗ 1_{u<ρ} k` are martingales, where `Y` is the stopped noise and `k` the coefficient `Im(2/f(iY))`. -/
theorem martingale_brackets_level (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) {N : ℝ} (hN : 0 ≤ N) {S ρ : Ω → ℝ≥0} {R : ℝ} {G : Set Ω} (hGm : MeasurableSet G)
    (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsLevelGood κ xL xR ρL ρR W VL VR B ζ N S ρ R ω)
    (hρ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ ω : WithTop ℝ≥0))
    (hXm : ∀ t, Measurable (stoppedProcess (meanHigh κ ρL ρR W VL VR N G S)
      (fun ω => (ρ ω : WithTop ℝ≥0)) t))
    (hka : ∀ p : ℝ≥0, Measurable[usualAugmentation 𝓕 P p] (coefHigh W G ρ N p)) :
    Martingale (stoppedProcess (meanHigh κ ρL ρR W VL VR N G S) (fun ω => (ρ ω : WithTop ℝ≥0)))
        (usualAugmentation 𝓕 P) P ∧
      Martingale (fun t ω => stoppedProcess (meanHigh κ ρL ρR W VL VR N G S)
          (fun ω => (ρ ω : WithTop ℝ≥0)) t ω ^ 2 -
        ∫ u in (0 : ℝ)..t, stopWeight ρ u ω * coefHigh W G ρ N u ω ^ 2) (usualAugmentation 𝓕 P) P ∧
      Martingale (fun t ω => stoppedProcess (meanHigh κ ρL ρR W VL VR N G S)
          (fun ω => (ρ ω : WithTop ℝ≥0)) t ω *
          stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω -
        ∫ u in (0 : ℝ)..t, stopWeight ρ u ω * coefHigh W G ρ N u ω) (usualAugmentation 𝓕 P) P := by
  set 𝓔 := usualAugmentation 𝓕 P with h𝓔
  set z := highPt N with hz
  have hnull : ∀ t (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝓔 t] M :=
    fun t M hM h0 => measurableSet_usualAugmentation_of_null hM h0 t
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have hzB := highPt_mem_closedBall N
  have hKH := closedBall_highPt_subset N
  have hz0 : 0 < z.im := hKH hzB
  set u : Ω → ℝ≥0 → ℂ → ℝ := fun ω s =>
    bheAt κ ρL ρR (W s ω) (fun i => VL i s ω) (fun i => VR i s ω) with hu
  have hus : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    bheAt_spec κ ρL ρR (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)
  -- the Itô layer's protection hypothesis
  have hσp : ∀ᵐ ω ∂P, (ρ ω : ℝ≥0∞) < ζ ω ∧ (∃ v, IsForwardSol (rpath (W · ω)) z (ρ ω) v) ∧
      (2 : ℝ) ≤ (fwdMap (rpath (W · ω)) (ρ ω) z).im ∧ (ρ ω : ℝ) ≤ N ∧
      ∀ s ≤ ρ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R := by
    filter_upwards [hGae] with ω hω
    obtain ⟨hpS, -, hρS, hR⟩ := hG ω hω
    have hsafe := isSafeAt_highPt_of_path hN hpS hρS
    exact ⟨hsafe.1, (hsafe.2.2.2 z hzB).1, (hsafe.2.2.2 z hzB).2, hsafe.2.2.1, hR⟩
  obtain ⟨M1, hM1, hM1e⟩ := exists_martingale_couplingMean_usualAugmentation hE hκ hz0 hρ two_pos hσp u hus
  obtain ⟨M2, hM2, hM2e⟩ :=
    exists_martingale_couplingMean_sq_usualAugmentation hE hκ hz0 hρ two_pos hσp u hus
  obtain ⟨M3, hM3, hM3e⟩ :=
    exists_martingale_couplingMean_mul_B_usualAugmentation hE hκ hz0 hρ two_pos hσp u hus
  -- pathwise identification on `G`
  have hX : ∀ ω ∈ G, ∀ t : ℝ≥0, stoppedProcess (meanHigh κ ρL ρR W VL VR N G S)
      (fun ω => (ρ ω : WithTop ℝ≥0)) t ω =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ ω) : ℝ≥0) (u ω (min t (ρ ω))) z := by
    intro ω hω t
    obtain ⟨hpS, -, hρS, -⟩ := hG ω hω
    have hr : min t (ρ ω) ≤ S ω := (min_le_right _ _).trans hρS
    have hsafe := isSafeAt_highPt_of_path hN hpS (le_refl (S ω))
    have hrζ : ((min t (ρ ω) : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) hpS.2.1
    rw [stoppedProcess_coe_apply]
    simp only [meanHigh, hω, ↓reduceIte, min_eq_right hr]
    exact (couplingMean_eq_meanCan (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω)
      hpS.1.2.2.2.1 hKH hsafe two_pos hr hzB (hpS.1.2.2.2.2.2.2.2.1 _ hrζ)
      (hpS.1.2.2.2.2.2.2.2.2.1 _ hrζ) (hus ω _)).symm
  have hY : ∀ ω ∈ G, ∀ t : ℝ≥0, stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω =
      B (min t (ρ ω)) ω := by
    intro ω hω t
    rw [stoppedProcess_coe_apply]; simp only [noiseOn, hω, ↓reduceIte]
  have hint : ∀ ω ∈ G, ∀ (t : ℝ≥0) (n : ℕ), ∫ v in (0 : ℝ)..t, stopWeight ρ v ω * coefHigh W G ρ N v ω ^ n =
      ∫ s in (0 : ℝ)..(min t (ρ ω) : ℝ≥0), ((2 / fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im) ^ n := by
    intro ω hω t n
    rw [integral_stopWeight_mul (g := fun v => coefHigh W G ρ N v ω ^ n)
      (((continuous_coefHigh hN hG ω).pow n).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg _)] at hv
    have hv' : v.toNNReal ≤ ρ ω :=
      Real.toNNReal_le_iff_le_coe.2 (hv.2.trans (by exact_mod_cast min_le_right _ _))
    simp only [coefHigh, hω, ↓reduceIte, min_eq_right hv', Real.coe_toNNReal _ hv.1]
    rfl
  -- measurability
  have hYmart := martingale_stoppedNoise (isFilteredBrownianReal_usualAugmentation hE.1) hnull hGm hG0
    (fun ω hω => (hG ω hω).2.1) hρ
  have hYm : ∀ t, Measurable (stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t) :=
    fun t => (hYmart.1.stronglyAdapted t).measurable.mono (𝓔.le t) le_rfl
  have hIm : ∀ n : ℕ, ∀ t : ℝ≥0, Measurable fun ω => ∫ v in (0 : ℝ)..t, stopWeight ρ v ω * coefHigh W G ρ N v ω ^ n :=
    fun n t => ((stronglyMeasurable_integral_stopWeight hρ (g := fun v ω => coefHigh W G ρ N v ω ^ n)
      (fun ω => (continuous_coefHigh hN hG ω).pow n) (fun p => (hka p).pow_const n) t).measurable).mono
      (𝓔.le t) le_rfl
  refine ⟨martingale_of_ae_eq_of_null hM1 hXm (fun t => ?_) hnull,
    martingale_of_ae_eq_of_null hM2 (fun t => ((hXm t).pow_const 2).sub (by simpa using hIm 2 t))
      (fun t => ?_) hnull,
    martingale_of_ae_eq_of_null hM3 (fun t => ((hXm t).mul (hYm t)).sub (by simpa using hIm 1 t))
      (fun t => ?_) hnull⟩
  · filter_upwards [hGae, hM1e] with ω hω h; rw [hX ω hω t, h t]
  · filter_upwards [hGae, hM2e] with ω hω h; rw [hX ω hω t, h t, hint ω hω t 2]
  · filter_upwards [hGae, hM3e] with ω hω h
    have h1 := hint ω hω t 1
    simp only [pow_one] at h1
    rw [hX ω hω t, hY ω hω t, h t, h1]

/-- Continuity of the coefficient path `u ↦ Im(2/f_{r∧u}(iY))` up to a time `r ≤ N` before the lifetime. -/
theorem continuous_coef_pathwise {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {N : ℝ} (hN : 0 ≤ N) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ) (hrN : (r : ℝ) ≤ N) :
    Continuous (fun u : ℝ => (2 / fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) (highPt N)).im) := by
  have hsafe := isSafeAt_highPt hw hN hr le_rfl hrN
  have hzB := highPt_mem_closedBall N
  have hKH := closedBall_highPt_subset N
  have hwc : ContinuousOn (rpath w) (Icc 0 (r : ℝ)) := continuousOn_rpath hw hr
  have hm : Continuous fun u : ℝ => ((min r u.toNNReal : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_const.min continuous_real_toNNReal)
  have hf : Continuous fun u : ℝ => fwdMap (rpath w) ((min r u.toNNReal : ℝ≥0) : ℝ) (highPt N) :=
    (continuousOn_fwdMap_of_continuousOn r.coe_nonneg hwc (hKH hzB) (hsafe.2.2.2 _ hzB).1).comp_continuous
      hm fun u => ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_left _ _⟩
  refine Complex.continuous_im.comp (continuous_const.div hf fun u h => ?_)
  have := hsafe.le_im_fwdMap hw hKH (min_le_left r u.toNNReal) hzB
  rw [h, Complex.zero_im] at this
  linarith

/-- **The coefficient is measurable for the σ-algebra of `ρ ∧ p`.** -/
theorem measurable_coefHigh {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hWa : AdaptedBefore 𝓖 ζ W) {G : Set Ω}
    (hG : MeasurableSet[𝓖 0] G) (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {N : ℝ} (hN : 0 ≤ N) {ρ : Ω → ℝ≥0} (hGρ : ∀ ω ∈ G, (ρ ω : ℝ≥0∞) < ζ ω ∧ (ρ ω : ℝ) ≤ N)
    (p : ℝ≥0) (hρp : IsStoppingTime 𝓖 fun ω => ((min (ρ ω) p : ℝ≥0) : WithTop ℝ≥0)) :
    Measurable[hρp.measurableSpace] (coefHigh W G ρ N p) := by
  set z := highPt N with hz
  have hzB := highPt_mem_closedBall N
  have hKH := closedBall_highPt_subset N
  have hz0 : 0 < z.im := hKH hzB
  have hK : ∀ s, Measurable[𝓖 s] fun ω =>
      (2 / (if ω ∈ aliveSet W ζ G z s then fwdMap (rpath (W · ω)) s z else 0)).im := fun s =>
    Complex.measurable_im.comp ((measurable_fwdMap_alive hWa hGc hG hz0 s).const_div 2)
  have hKX : ∀ ω ∈ G, ∀ s ≤ ρ ω,
      (2 / (if ω ∈ aliveSet W ζ G z s then fwdMap (rpath (W · ω)) s z else 0)).im =
        (2 / fwdMap (rpath (W · ω)) s z).im := by
    intro ω hω s hs
    have hsafe := isSafeAt_highPt (hGc ω hω) hN (σ₀ := s) (r := s)
      (lt_of_le_of_lt (by exact_mod_cast hs) (hGρ ω hω).1) le_rfl
      ((NNReal.coe_le_coe.2 hs).trans (hGρ ω hω).2)
    have hal : ω ∈ aliveSet W ζ G z s := ⟨hω, hsafe.1, (hsafe.2.2.2 z hzB).1⟩
    simp only [hal, ↓reduceIte]
  have hXc : ∀ ω ∈ G, ContinuousOn (fun s : ℝ≥0 => (2 / fwdMap (rpath (W · ω)) s z).im) (Iic (ρ ω)) := by
    intro ω hω
    have hc := continuous_coef_pathwise (hGc ω hω) hN (hGρ ω hω).1 (hGρ ω hω).2
    refine (hc.comp NNReal.continuous_coe).continuousOn.congr fun s hs => ?_
    simp only [Function.comp, Real.toNNReal_coe, min_eq_right (mem_Iic.1 hs)]
    rfl
  have h := measurable_stoppedAt_of_agree hK hG (-1) hKX hXc p hρp
  convert h using 1
  funext ω
  simp only [coefHigh, Real.toNNReal_coe]
  rfl

/-- **The stopped noise is measurable for the σ-algebra of `ρ ∧ t`** (in the driving filtration, through noise
recovery). -/
theorem measurable_stoppedNoise {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hκ : 0 < κ) (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) {G : Set Ω} (hG : MeasurableSet[𝓖 0] G)
    (hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω))
    {ρ : Ω → ℝ≥0} (hGρ : ∀ ω ∈ G, (ρ ω : ℝ≥0∞) < ζ ω) (t : ℝ≥0)
    (hρt : IsStoppingTime 𝓖 fun ω => ((min (ρ ω) t : ℝ≥0) : WithTop ℝ≥0)) :
    Measurable[hρt.measurableSpace]
      (stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t) := by
  have hK : ∀ s, Measurable[𝓖 s] (killedNoise κ ρL ρR xL xR W VL VR ζ s) :=
    adapted_killedNoise κ ρL ρR xL xR hWa hVLa hVRa
  have hKX : ∀ ω ∈ G, ∀ s ≤ ρ ω, killedNoise κ ρL ρR xL xR W VL VR ζ s ω = B s ω := by
    intro ω hω s hs
    have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (hGρ ω hω)
    rw [killedNoise_of_lt κ ρL ρR xL xR hsζ]
    exact (IsIntegratedSLEPath.eq_noiseOf hκ (hGp ω hω).1 hsζ).symm
  have h := measurable_stoppedAt_of_agree (X := B) hK hG 0 hKX
    (fun ω hω => (hGp ω hω).2.continuousOn) t hρt
  convert h using 1
  funext ω
  rw [stoppedProcess_coe_apply]
  simp only [noiseOn, min_comm]

/-- **One level of (GB4): the stopped noise is a martingale of the germ filtration.** Let `S ≤ N` and `ρ ≤ S` be
stops of the driving filtration, `G` a full-measure event on which the level conditions hold, and `𝒢` a filtration
containing the stopped σ-algebras `𝓕_{S∧t}` in which the high-point mean is a martingale. Then `B_{·∧ρ}` (modified
off `G`) is a `𝒢`-martingale. -/
theorem martingale_stoppedNoise_level (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) {N : ℝ} (hN : 0 ≤ N) {S ρ : Ω → ℝ≥0}
    {R : ℝ} {G : Set Ω} (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsLevelGood κ xL xR ρL ρR W VL VR B ζ N S ρ R ω)
    (hS : IsStoppingTime (drivingFiltration P hX) fun ω => (S ω : WithTop ℝ≥0))
    (hρ : IsStoppingTime (drivingFiltration P hX) fun ω => (ρ ω : WithTop ℝ≥0)) (hρS : ∀ ω, ρ ω ≤ S ω)
    {𝒢 : Filtration ℝ≥0 mΩ} (h𝓓𝒢 : ∀ t, (hS.min_const t).measurableSpace ≤ 𝒢 t)
    (hmH : Martingale (meanHigh κ ρL ρR W VL VR N G S) 𝒢 P) :
    Martingale (stoppedProcess (noiseOn B G) fun ω => (ρ ω : WithTop ℝ≥0)) 𝒢 P := by
  set 𝓓 := drivingFiltration P hX with h𝓓
  set 𝓔 := usualAugmentation 𝓕 P with h𝓔
  set z := highPt N with hz
  have hnull𝓓 : ∀ t (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝓓 t] M :=
    fun t M hM h0 => measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hM h0 t
  have hnull𝓔 : ∀ t (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝓔 t] M :=
    fun t M hM h0 => measurableSet_usualAugmentation_of_null hM h0 t
  have hG𝓓 : MeasurableSet[𝓓 0] G := by
    have := (hnull𝓓 0 Gᶜ hGm.compl hG0).compl; rwa [compl_compl] at this
  have hWa : AdaptedBefore 𝓓 ζ W :=
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_W hX)
  have hVLa : ∀ i, AdaptedBefore 𝓓 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hVRa : ∀ i, AdaptedBefore 𝓓 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_VR hX i)
  have hGρ : ∀ ω ∈ G, (ρ ω : ℝ≥0∞) < ζ ω ∧ (ρ ω : ℝ) ≤ N := fun ω hω =>
    ⟨lt_of_le_of_lt (by exact_mod_cast hρS ω) (hG ω hω).1.2.1,
      (NNReal.coe_le_coe.2 (hρS ω)).trans (hG ω hω).1.2.2⟩
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hG ω hω).1.1.2.2.2.1
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  -- stopping times
  have hρ𝓔 : IsStoppingTime 𝓔 fun ω => (ρ ω : WithTop ℝ≥0) :=
    isStoppingTime_usualAugmentation_of_drivingFiltration hE hX hρ
  have hρt : ∀ t : ℝ≥0, IsStoppingTime 𝓓 fun ω => ((min (ρ ω) t : ℝ≥0) : WithTop ℝ≥0) := fun t => by
    simp only [WithTop.coe_min]; exact hρ.min_const t
  have hρS' : ∀ t : ℝ≥0, (hρt t).measurableSpace ≤ 𝒢 t := fun t =>
    ((hρt t).measurableSpace_mono (hS.min_const t) fun ω => by
      simp only [WithTop.coe_min]; exact min_le_min_right _ (by exact_mod_cast hρS ω)).trans (h𝓓𝒢 t)
  have hρ𝒢 : IsStoppingTime 𝒢 fun ω => (ρ ω : WithTop ℝ≥0) := fun t => by
    have h := IsStoppingTime.measurableSet_stopping_time_le hρ (hS.min_const t)
    have e : {ω | (ρ ω : WithTop ℝ≥0) ≤ min (S ω : WithTop ℝ≥0) (t : WithTop ℝ≥0)} =
        {ω | (ρ ω : WithTop ℝ≥0) ≤ t} := by
      ext ω
      simp only [mem_ofPred_eq, le_min_iff, and_iff_right_iff_imp]
      exact fun _ => by exact_mod_cast hρS ω
    rw [e] at h
    exact h𝓓𝒢 t _ h
  -- the processes
  have hXG : Martingale (stoppedProcess (meanHigh κ ρL ρR W VL VR N G S)
      fun ω => (ρ ω : WithTop ℝ≥0)) 𝒢 P :=
    Martingale.stoppedProcess_of_rightContinuous hmH
      (fun ω t => (continuous_meanHigh hN (fun ω hω => (hG ω hω).1) ω).continuousWithinAt) hρ𝒢
  have hXm : ∀ t, Measurable (stoppedProcess (meanHigh κ ρL ρR W VL VR N G S)
      (fun ω => (ρ ω : WithTop ℝ≥0)) t) := fun t =>
    (hXG.stronglyAdapted t).measurable.mono (𝒢.le t) le_rfl
  have hYG : StronglyAdapted 𝒢 (stoppedProcess (noiseOn B G) fun ω => (ρ ω : WithTop ℝ≥0)) := fun t =>
    ((measurable_stoppedNoise hκ hWa hVLa hVRa hG𝓓 (fun ω hω => ⟨(hG ω hω).1.1, (hG ω hω).2.1⟩)
      (fun ω hω => (hGρ ω hω).1) t (hρt t)).mono (hρS' t) le_rfl).stronglyMeasurable
  have hka𝓔 : ∀ p : ℝ≥0, Measurable[𝓔 p] (coefHigh W G ρ N p) := fun p =>
    (measurable_coefHigh hWa hG𝓓 hGc hN hGρ p (hρt p)).mono
      (((hρt p).measurableSpace_le_of_le_const fun ω => by exact_mod_cast min_le_right _ _).trans
        (drivingFiltration_le_usualAugmentation hE hX p)) le_rfl
  have hkaG : ∀ p : ℝ≥0, Measurable[𝒢 p] (coefHigh W G ρ N p) := fun p =>
    (measurable_coefHigh hWa hG𝓓 hGc hN hGρ p (hρt p)).mono (hρS' p) le_rfl
  obtain ⟨hX𝓔, hXX, hXY⟩ := martingale_brackets_level hE hκ hN hGm hG0 hG hρ𝓔 hXm hka𝓔
  obtain ⟨hY𝓔, hYY⟩ := martingale_stoppedNoise (isFilteredBrownianReal_usualAugmentation hE.1) hnull𝓔
    hGm hG0 (fun ω hω => (hG ω hω).2.1) hρ𝓔
  -- bounds
  set Km : ℝ := meanHarmonicBound κ ρL ρR + |chiC κ| * (2 / 2 ^ 2 * N) with hKm
  set L : ℝ := ‖z‖ + 24 * R + 8 * Real.sqrt N with hL
  have hR0 : ∀ ω ∈ G, 0 ≤ R := fun ω hω => (abs_nonneg _).trans ((hG ω hω).2.2.2 0 zero_le).1
  have hXb : ∀ t, ∀ᵐ ω ∂P, |stoppedProcess (meanHigh κ ρL ρR W VL VR N G S)
      (fun ω => (ρ ω : WithTop ℝ≥0)) t ω| ≤ max Km R := by
    intro t
    filter_upwards [hGae] with ω hω
    obtain ⟨hpS, -, -, -⟩ := hG ω hω
    have hsafe := isSafeAt_highPt_of_path hN hpS (le_refl (S ω))
    rw [stoppedProcess_coe_apply]
    simp only [meanHigh, hω, ↓reduceIte]
    have hb := hsafe.abs_meanCan_le (κ := κ) (ρL := ρL) (ρR := ρR) (vL := fun i t => VL i t ω)
      (vR := fun i t => VR i t ω) hpS.1.2.2.2.1 (closedBall_highPt_subset N) two_pos
      (min_le_left (S ω) (min t (ρ ω))) (highPt_mem_closedBall N)
    refine (hb.trans ?_).trans (le_max_left _ _)
    rw [hKm]
    gcongr
    exact hpS.2.2
  have hYb : ∀ t, ∀ᵐ ω ∂P, |stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω| ≤
      max Km R := by
    intro t
    filter_upwards [hGae] with ω hω
    rw [stoppedProcess_coe_apply]
    simp only [noiseOn, hω, ↓reduceIte]
    exact ((hG ω hω).2.2.2 _ (min_le_right _ _)).2.1.trans (le_max_right _ _)
  have hcoef : ∀ ω ∈ G, ∀ u, |coefHigh W G ρ N u ω| ≤ 1 ∧ 4 / L ^ 2 ≤ |coefHigh W G ρ N u ω| := by
    intro ω hω u
    obtain ⟨⟨hp, -, -⟩, -, -, hRb⟩ := hG ω hω
    simp only [coefHigh, hω, ↓reduceIte]
    exact (coef_pathwise hp.2.2.2.1 hp.1 hN (hGρ ω hω).1 (hGρ ω hω).2 fun s hs => (hRb s hs).1).2 u
  have hL3 : 3 ≤ L := by
    by_cases hGn : G.Nonempty
    · obtain ⟨ω, hω⟩ := hGn
      have hz3 : 3 ≤ ‖z‖ := by
        have h1 := Complex.abs_im_le_norm z
        rw [hz, highPt_im, abs_of_nonneg (by positivity)] at h1
        linarith [Real.sqrt_nonneg N]
      have := hR0 ω hω
      rw [hL]; linarith [Real.sqrt_nonneg N]
    · exfalso
      have hGe : G = ∅ := Set.not_nonempty_iff_eq_empty.1 hGn
      rw [hGe, compl_empty, measure_univ] at hG0
      exact one_ne_zero hG0
  have hc : 0 < 4 / L ^ 2 := by positivity
  have hc1 : 4 / L ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hkb : ∀ u ω, 4 / L ^ 2 ≤ |coefHigh W G ρ N u ω| := fun u ω => by
    by_cases hω : ω ∈ G
    · exact (hcoef ω hω u).2
    · simp only [coefHigh, hω, ↓reduceIte, abs_neg, abs_one]; exact hc1
  have hkC : ∀ u ω, |coefHigh W G ρ N u ω| ≤ 1 := fun u ω => by
    by_cases hω : ω ∈ G
    · exact (hcoef ω hω u).1
    · simp only [coefHigh, hω, ↓reduceIte, abs_neg, abs_one, le_refl]
  exact martingale_of_bracket_freeze_of_adapted (𝓕 := 𝓔) hX𝓔 hY𝓔 hXb hYb hXX hXY hYY
    (fun ω => continuous_coefHigh hN hG ω) (fun p => (hka𝓔 p).stronglyMeasurable)
    (fun p => (hkaG p).stronglyMeasurable) hc hkb hkC (measurable_stopWeight ρ)
    (stopWeight_nonneg ρ) (stopWeight_le_one ρ) hXG hYG

/-- The stopped clock `t ∧ ρ` is a slow clock. -/
theorem isSlowClock_min (ρ : Ω → ℝ≥0) :
    MathFin.LevyQuadraticSums.IsSlowClock fun t ω => ((min t (ρ ω) : ℝ≥0) : ℝ) where
  zero ω := by simp
  sub_nonneg p q hpq ω := sub_nonneg.2 (by exact_mod_cast min_le_min_right _ hpq)
  sub_le p q hpq ω := by
    rcases le_total q (ρ ω) with hq | hq
    · rw [min_eq_left hq, min_eq_left (hpq.trans hq)]
    · rw [min_eq_right hq]
      rcases le_total p (ρ ω) with hp | hp
      · rw [min_eq_left hp]
        have : ((ρ ω : ℝ≥0) : ℝ) ≤ q := by exact_mod_cast hq
        linarith
      · rw [min_eq_right hp, sub_self]; exact sub_nonneg.2 (by exact_mod_cast hpq)

/-- **One level of the bracket in the germ filtration.** Under the hypotheses of `martingale_stoppedNoise_level`
(with `R ≥ 0`), if `B_{·∧ρ}` is a `𝒢`-martingale then so is `B_{·∧ρ}² − (·∧ρ)`. -/
theorem martingale_stoppedNoise_sq_level (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {N : ℝ} {S ρ : Ω → ℝ≥0} {R : ℝ} (hR : 0 ≤ R) {G : Set Ω}
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsLevelGood κ xL xR ρL ρR W VL VR B ζ N S ρ R ω)
    (hS : IsStoppingTime (drivingFiltration P hX) fun ω => (S ω : WithTop ℝ≥0))
    (hρ : IsStoppingTime (drivingFiltration P hX) fun ω => (ρ ω : WithTop ℝ≥0)) (hρS : ∀ ω, ρ ω ≤ S ω)
    {𝒢 : Filtration ℝ≥0 mΩ} (h𝓓𝒢 : ∀ t, (hS.min_const t).measurableSpace ≤ 𝒢 t)
    (hYG : Martingale (stoppedProcess (noiseOn B G) fun ω => (ρ ω : WithTop ℝ≥0)) 𝒢 P) :
    Martingale (fun t ω => stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω ^ 2 -
      ((min t (ρ ω) : ℝ≥0) : ℝ)) 𝒢 P := by
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hρ𝓔 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ ω : WithTop ℝ≥0) :=
    isStoppingTime_usualAugmentation_of_drivingFiltration hE hX hρ
  obtain ⟨hY𝓔, hYY⟩ := martingale_stoppedNoise (isFilteredBrownianReal_usualAugmentation hE.1)
    (fun t M hM h0 => measurableSet_usualAugmentation_of_null hM h0 t) hGm hG0
    (fun ω hω => (hG ω hω).2.1) hρ𝓔
  have hweight : ∀ ω (q : ℝ≥0), ∫ u in (0 : ℝ)..q, stopWeight ρ u ω = ((min q (ρ ω) : ℝ≥0) : ℝ) := by
    intro ω q
    have hi := integral_stopWeight_mul (ρ := ρ) (ω := ω) (g := fun _ => (1 : ℝ)) (t := q)
      intervalIntegrable_const
    simp only [mul_one] at hi
    rw [hi, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  simp only [hweight] at hYY
  have hK : ∀ t ω, |stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω| ≤ R := by
    intro t ω
    rw [stoppedProcess_coe_apply]
    by_cases hω : ω ∈ G
    · simp only [noiseOn, hω, ↓reduceIte]
      exact ((hG ω hω).2.2.2 _ (min_le_right _ _)).2.1
    · simp only [noiseOn, hω, ↓reduceIte, abs_zero]; exact hR
  have hYc : ∀ ω, Continuous fun t => stoppedProcess (noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) t ω := by
    intro ω
    simp only [stoppedProcess_coe_apply]
    exact (continuous_noiseOn (fun ω hω => (hG ω hω).2.1) ω).comp (continuous_id.min continuous_const)
  have hAa : StronglyAdapted 𝒢 fun t ω => ((min t (ρ ω) : ℝ≥0) : ℝ) := fun t => by
    have hρt : IsStoppingTime 𝓓 fun ω => ((min (ρ ω) t : ℝ≥0) : WithTop ℝ≥0) := by
      simp only [WithTop.coe_min]; exact hρ.min_const t
    have hle : hρt.measurableSpace ≤ 𝒢 t :=
      (hρt.measurableSpace_mono (hS.min_const t) fun ω => by
        simp only [WithTop.coe_min]; exact min_le_min_right _ (by exact_mod_cast hρS ω)).trans (h𝓓𝒢 t)
    have h := measurable_stoppedAt_of_agree (X := fun s (_ : Ω) => ((s : ℝ≥0) : ℝ))
      (K := fun s (_ : Ω) => ((s : ℝ≥0) : ℝ)) (fun s => measurable_const) (G := univ)
      MeasurableSet.univ (0 : ℝ) (fun _ _ _ _ => rfl) (fun _ _ => NNReal.continuous_coe.continuousOn) t hρt
    simp only [mem_univ, ↓reduceIte] at h
    have e : (fun ω => ((min (ρ ω) t : ℝ≥0) : ℝ)) = fun ω => ((min t (ρ ω) : ℝ≥0) : ℝ) := by
      funext ω; rw [min_comm]
    rw [e] at h
    exact (h.mono hle le_rfl).stronglyMeasurable
  exact martingale_sq_sub_of_bracket (isSlowClock_min ρ) hY𝓔 hK hYc hYY hYG hAa

end Level

/-! ### The Brownian conclusion of C.2 -/

section Main

universe u

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **C.2 / Aux. lemma 47, Brownian conclusion (stopped form).** For a coupling with the optional hull specification
(`κ > 0`) and a bounded stop `S ≤ N` of the driving filtration with `S < ζ`, let `𝒢_t = Γ(𝓕_{S∧t}, K_{S∧t})` be the
stopped germ filtration of `exists_germFiltration_martingale` (history joined with the hull germ). Then the stopped
driving noise `t ↦ B_{t∧S}` has a version that is a `𝒢`-martingale: retaining the field near the hull does not make the
driving noise predictable. -/
theorem martingale_stoppedNoise_germ (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {S : Ω → ℝ≥0}
    (hS : IsStoppingTime (drivingFiltration P hX) fun ω => (S ω : WithTop ℝ≥0))
    (hSζ : ∀ᵐ ω ∂P, (S ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hSN : ∀ ω, S ω ≤ N) :
    ∃ (A : ℝ≥0 → Ω → Set ℂ) (𝒢 : Filtration ℝ≥0 mΩ),
      (∀ t, Measurable[mΩ, hittingSigma] (A t)) ∧
      (∀ t, ∀ᵐ ω ∂P, A t ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (S ω) t : ℝ≥0) : ℝ)) ∧
      (∀ t, 𝒢 t = histGerm (hS.min_const t).measurableSpace (A t) (centredField h u₀)) ∧
      (∀ t, (hS.min_const t).measurableSpace ≤ 𝒢 t) ∧
      ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝒢 P ∧ (∀ᵐ ω ∂P, ∀ t, Y t ω = B (min t (S ω)) ω) ∧
        ∃ ρ : ℕ → Ω → ℝ≥0, (∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
          (∀ n ω, ρ n ω ≤ S ω) ∧ (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ρ n ω = S ω) ∧
          ∀ n, Martingale (fun t ω => stoppedProcess Y (fun ω => (ρ n ω : WithTop ℝ≥0)) t ω ^ 2 -
            ((min t (ρ n ω) : ℝ≥0) : ℝ)) 𝒢 P := by
  have hE := hC.1
  set 𝓓 := drivingFiltration P hX with h𝓓
  set 𝓔 := usualAugmentation 𝓕 P with h𝓔
  have hN : (0 : ℝ) ≤ N := N.coe_nonneg
  set z := highPt (N : ℝ) with hz
  have hzB := highPt_mem_closedBall (N : ℝ)
  have hKH := closedBall_highPt_subset (N : ℝ)
  have hz0 : 0 < z.im := hKH hzB
  -- the germ filtration
  obtain ⟨A, 𝒢, hAm, hAe, h𝒢, h𝓓𝒢, hmart⟩ := exists_germFiltration_martingale hC hκ hu₀ hX hS hSζ
  have hmin : ∀ ω (t : ℝ≥0),
      ((min ((S ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) = min (S ω) t :=
    fun ω t => by rw [← WithTop.coe_min, WithTop.untopD_coe]
  have hA' : ∀ t, ∀ᵐ ω ∂P, A t ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (S ω) t : ℝ≥0) : ℝ) :=
    fun t => (hAe t).mono fun ω hω => by rw [hω, hmin]
  refine ⟨A, 𝒢, hAm, hA', h𝒢, h𝓓𝒢, ?_⟩
  -- null sets and adaptedness
  have hnull𝓓 : ∀ t (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝓓 t] M :=
    fun t M hM h0 => measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hM h0 t
  have hnull𝒢 : ∀ t (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝒢 t] M :=
    fun t M hM h0 => h𝓓𝒢 t _ (measurableSet_stopping_of_null hnull𝓓 (hS.min_const t) hM h0)
  have hWa : AdaptedBefore 𝓓 ζ W :=
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_W hX)
  have hVLa : ∀ i, AdaptedBefore 𝓓 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hVRa : ∀ i, AdaptedBefore 𝓓 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_VR hX i)
  -- the localizing sequence below `S`
  have hzs : ∀ i, 0 < ((![z] : Fin 1 → ℂ) i).im := fun i => by
    rw [Matrix.cons_val_fin_one]; exact hz0
  obtain ⟨ρ, hρst, hρle, -, hprot, hexh⟩ := exists_localizingSeq_driving hE hκ hX (zs := ![z]) hzs
    (m := z.im) hz0 (fun i => by rw [Matrix.cons_val_fin_one]) one_pos
    (fun i j hij => absurd (Subsingleton.elim i j) hij) (σ₀ := fun _ => S) (fun _ => hS)
    (fun _ => monotone_const) (fun _ => hSζ)
  set C₀ := initBound xL xR with hC₀
  set R : ℕ → ℝ := fun n => (n : ℝ) + C₀ with hR
  -- the good event
  set good : Ω → Prop := fun ω =>
    (∀ n, IsLevelGood κ xL xR ρL ρR W VL VR B ζ N S (ρ n) (R n) ω) ∧ B 0 ω = 0 ∧
      ∀ᶠ n in atTop, ρ n ω = S ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.toIsPreBrownianReal.eval_zero_ae_eq_zero, hSζ,
      ae_all_iff.2 hprot, hexh] with ω hp hBc hB0 hSζω hprotω hexhω
    have hpS : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ (S ω : ℝ≥0∞) < ζ ω ∧ (S ω : ℝ) ≤ N :=
      ⟨hp, hSζω, by exact_mod_cast hSN ω⟩
    refine ⟨fun n => ⟨hpS, hBc, hρle n ω, fun s hs => ?_⟩, hB0, ?_⟩
    · have h := hprotω n s hs
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩
    · have hsafe := isSafeAt_highPt_of_path hN hpS (le_refl (S ω))
      have hev := hexhω 0 (S ω) le_rfl fun i => by
        rw [Matrix.cons_val_fin_one]; exact (hsafe.2.2.2 z hzB).1
      filter_upwards [hev] with n hn
      exact le_antisymm (hρle n ω) hn
  obtain ⟨G, hGm, hG0, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have hG𝓓 : MeasurableSet[𝓓 0] G := by
    have := (hnull𝓓 0 Gᶜ hGm.compl hG0).compl; rwa [compl_compl] at this
  have hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ (S ω : ℝ≥0∞) < ζ ω ∧ (S ω : ℝ) ≤ N :=
    fun ω hω => ((hGgood ω hω).1 0).1
  -- (WF5) at the high point
  set φ : LQGMetric.TestOn upperHalfPlaneOpens :=
    GFF.bumpTest (D := upperHalfPlaneOpens) (highPt (N : ℝ)) one_pos hKH with hφ
  obtain ⟨hZ, hZid⟩ := hmart φ
  have hid := hZid (fun t ω => bheAt κ ρL ρR (W ((min ((S ω : ℝ≥0) : WithTop ℝ≥0)
      (t : WithTop ℝ≥0)).untopD 0) ω) (fun i => VL i ((min ((S ω : ℝ≥0) : WithTop ℝ≥0)
      (t : WithTop ℝ≥0)).untopD 0) ω) (fun i => VR i ((min ((S ω : ℝ≥0) : WithTop ℝ≥0)
      (t : WithTop ℝ≥0)).untopD 0) ω)) (fun t ω => bheAt_spec κ ρL ρR _ _ _)
  simp only [hmin] at hid
  have hmH : Martingale (meanHigh κ ρL ρR W VL VR N G S) 𝒢 P :=
    martingale_meanHigh hN hGp hGae
      (fun t => (measurable_meanHigh hWa hVLa hVRa hG𝓓 hN hS hGp t).mono (𝓓.le t) le_rfl) hnull𝒢
      hu₀.1 hA' hZ hid
  -- every level
  have hYn : ∀ n, Martingale (stoppedProcess (noiseOn B G) fun ω => (ρ n ω : WithTop ℝ≥0)) 𝒢 P :=
    fun n => martingale_stoppedNoise_level hE hκ hX hN hGm hG0 (fun ω hω => (hGgood ω hω).1 n) hS
      (hρst n) (hρle n) h𝓓𝒢 hmH
  -- removal of the localization
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess (noiseOn B G) fun ω => (ρ n ω : WithTop ℝ≥0)
    with hYdef
  set Yi : ℝ≥0 → Ω → ℝ := stoppedProcess (noiseOn B G) fun ω => (S ω : WithTop ℝ≥0) with hYi
  have hYval : ∀ n t, ∀ ω ∈ G, Y n t ω = B (min t (ρ n ω)) ω := fun n t ω hω => by
    simp only [hYdef]; rw [stoppedProcess_coe_apply]; simp only [noiseOn, hω, ↓reduceIte]
  have hYbd : ∀ n t, ∀ᵐ ω ∂P, |Y n t ω| ≤ R n := fun n t => by
    filter_upwards [hGae] with ω hω
    rw [hYval n t ω hω]
    exact (((hGgood ω hω).1 n).2.2.2 _ (min_le_right _ _)).2.1
  have hYm : ∀ n t, Measurable (Y n t) := fun n t =>
    ((hYn n).stronglyAdapted t).measurable.mono (𝒢.le t) le_rfl
  have hYL2 : ∀ n t, MemLp (Y n t) 2 P := fun n t =>
    MemLp.of_bound (hYm n t).aestronglyMeasurable (R n)
      ((hYbd n t).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hweight : ∀ n ω (q : ℝ≥0), ∫ u in (0 : ℝ)..q, stopWeight (ρ n) u ω = ((min q (ρ n ω) : ℝ≥0) : ℝ) := by
    intro n ω q
    have hi := integral_stopWeight_mul (ρ := ρ n) (ω := ω) (g := fun _ => (1 : ℝ)) (t := q)
      intervalIntegrable_const
    simp only [mul_one] at hi
    rw [hi, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hsq : ∀ n t, ∫ ω, Y n t ω ^ 2 ∂P ≤ t := by
    intro n t
    have hρ𝓔 := isStoppingTime_usualAugmentation_of_drivingFiltration hE hX (hρst n)
    obtain ⟨-, hYY⟩ := martingale_stoppedNoise (isFilteredBrownianReal_usualAugmentation hE.1)
      (fun t M hM h0 => measurableSet_usualAugmentation_of_null hM h0 t) hGm hG0
      (fun ω hω => ((hGgood ω hω).1 0).2.1) hρ𝓔
    have hE0 := hYY.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simp only [setIntegral_univ] at hE0
    have hl : ∫ ω, (Y n 0 ω ^ 2 - ∫ u in (0 : ℝ)..((0 : ℝ≥0) : ℝ), stopWeight (ρ n) u ω) ∂P = 0 := by
      refine integral_eq_zero_of_ae (hGae.mono fun ω hω => ?_)
      have hB0 := (hGgood ω hω).2.1
      simp only [Pi.zero_apply]
      rw [hYval n 0 ω hω, zero_min, hB0]
      simp
    have hIi : Integrable (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), stopWeight (ρ n) u ω) P := by
      have hm := (((hYL2 n t).aestronglyMeasurable.pow 2).sub (hYY.integrable t).aestronglyMeasurable)
      refine Integrable.of_bound (hm.congr (Eventually.of_forall fun ω => by
        simp only [Pi.sub_apply, Pi.pow_apply, hYdef]; ring)) t
        (Eventually.of_forall fun ω => ?_)
      rw [hweight, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast min_le_left _ _
    rw [hl, integral_sub (hYL2 n t).integrable_sq hIi] at hE0
    have hle : ∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), stopWeight (ρ n) u ω) ∂P ≤ t := by
      calc ∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), stopWeight (ρ n) u ω) ∂P ≤ ∫ _ω : Ω, (t : ℝ) ∂P :=
            integral_mono hIi (integrable_const _) fun ω => by
              rw [hweight]; exact_mod_cast min_le_left _ _
        _ = t := by simp
    linarith
  have hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Y n t ω) atTop (𝓝 (Yi t ω)) := by
    intro t
    filter_upwards [hGae] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(hGgood ω hω).2.2] with n hn
    simp only [hYdef, hYi, stoppedProcess_coe_apply, hn]
  have hYa : StronglyAdapted 𝒢 Yi := fun t => by
    have hSt : IsStoppingTime 𝓓 fun ω => ((min (S ω) t : ℝ≥0) : WithTop ℝ≥0) := by
      simp only [WithTop.coe_min]; exact hS.min_const t
    have hle : hSt.measurableSpace ≤ 𝒢 t :=
      (hSt.measurableSpace_mono (hS.min_const t) fun ω => by simp only [WithTop.coe_min, le_refl]).trans
        (h𝓓𝒢 t)
    exact ((measurable_stoppedNoise hκ hWa hVLa hVRa hG𝓓
      (fun ω hω => ⟨(hGp ω hω).1, ((hGgood ω hω).1 0).2.1⟩) (fun ω hω => (hGp ω hω).2.1) t hSt).mono
        hle le_rfl).stronglyMeasurable
  have hYint : ∀ t, Integrable (Yi t) P := fun t =>
    (MathFin.memLp_two_of_subseq_ae_of_sq_bound (fun n => hYL2 n t) (fun n => hYm n t)
      (fun n => hsq n t) ⟨id, hlim t⟩).integrable one_le_two
  refine ⟨Yi, Sec7.martingale_of_tendsto_of_sq_bound hYn hYL2 (fun t => ⟨t, fun n => hsq n t⟩) hlim hYa
    hYint, ?_, ρ, hρst, hρle, ?_, fun n => ?_⟩
  · filter_upwards [hGae] with ω hω t
    simp only [hYi]
    rw [stoppedProcess_coe_apply]
    simp only [noiseOn, hω, ↓reduceIte]
  · filter_upwards [hGae] with ω hω using (hGgood ω hω).2.2
  · have hR0 : 0 ≤ R n := by
      have := initBound_nonneg (xL := xL) (xR := xR)
      simp only [hR]; positivity
    have hq := martingale_stoppedNoise_sq_level hE hX hR0 hGm hG0 (fun ω hω => (hGgood ω hω).1 n) hS
      (hρst n) (hρle n) h𝓓𝒢 (hYn n)
    have e : ∀ t ω, stoppedProcess Yi (fun ω => (ρ n ω : WithTop ℝ≥0)) t ω =
        stoppedProcess (noiseOn B G) (fun ω => (ρ n ω : WithTop ℝ≥0)) t ω := fun t ω => by
      simp only [hYi, stoppedProcess_coe_apply]
      rw [min_eq_left ((min_le_right _ _).trans (hρle n ω))]
    simp only [e]
    exact hq

end Main

end WholeField

end InteractingSLE
