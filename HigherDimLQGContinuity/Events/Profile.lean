import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGContinuity.Norm.Rho
import HigherDimLQGMetric.Events.Locality
import HigherDimLQGMetric.Sec10.Lemma101
import HigherDimLQGMetric.Select.Internal
import HigherDimLQGMetric.Sharp.CountableShell
import HigherDimLQGMetric.Sharp.ScaledMetric
import LQGMetric.Meas.LocalEvent

/-!
# Locality of events of the normalized internal profiles (packet P5b)

Packet P5b, first module. Source: blueprint Part A, Lemma `a:lem-local` (steps (1), (3), (4) of its proof), with the
domain correction EB20 (Part B, `b:err-domain`); planning audit NA1, item 20, R4; NA3 N-M17; the library pattern of
HDLM's `aeEventIn_of_normInternal_shell` (`Events/EventLocal.lean`).

The proof of `a:lem-local` works under `𝐏ₛ = pinLaw d s` directly: under `𝐏ₛ` the identity is a whole-space LGF with
`g_s(0) = 0` almost surely (`isWholeSpaceLGF_pinLaw`), so the sharp-normalized internal metrics of [8]
(`IsSharpWeakExpMetric.exists_measurable_normInternal_all`, after `lemma101`) are already `fieldSigma0 id J`-measurable
for every open `J` containing the pin sphere `∂B_s` and the profile domain `V`. The transport steps (3)–(4) of the
blueprint (`aeEventIn_of_recentred` under `normLGFLaw d` and the pull-back by `pin s`) are not needed.

* `p5b_internal_rho`, `p5b_isLength_rho`, `p5b_ae_isLength_rho`: the internal metrics of `ρ^D = e^{-logMean D} D` and
  almost-sure length under `𝐏ₛ`.
* `p5b_internal_eq_of_dense`: two length metrics whose internal metrics on an open `V` agree at the pairs of a dense
  sequence of `V` agree on `V × V` (continuity of internal metrics, LM Lemma 1.1).
* `p5b_aeEventIn_of_profile` (**the locality lemma**): an event `B` that is null-measurable for `𝐏ₛ` and determined,
  on length metrics, by the `V`-internal profiles of `ρ^D_g` and `ρ^E_g` is `AEEventIn 𝐏ₛ (fieldSigma0 id J)`.
  Consumers: `local_events_aeEventIn` (this packet, `V = A`), and Part B's site events (`b:lem-refs4-prob`,
  `b:lem-siteevent`: "the argument of Lemma `a:lem-local`"), with `E := D` for one metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The normalized metric `ρ^D` -/

/-- The internal metrics of `ρ^D_g = e^{-logMean D} D_g`. -/
theorem p5b_internal_rho (D : DistRd d → ContMetric d) (g : DistRd d) (U : Set (Rd d)) (x y : Rd d) :
    (rho D g).internal U x y = ENNReal.ofReal (Real.exp (-logMean D)) * (D g).internal U x y :=
  ContMetric.internal_smul (Real.exp_pos _) (D g) U x y

/-- `ρ^D_g` is a length metric when `D_g` is. -/
theorem p5b_isLength_rho {D : DistRd d → ContMetric d} {g : DistRd d} (h : (D g).IsLength) :
    (rho D g).IsLength :=
  ContMetric.isLength_smul (Real.exp_pos (-logMean D)) h

/-- Under every pin `s > 0`, `ρ^D_g` is almost surely a length metric (axiom (I) for the input `id`). -/
theorem p5b_ae_isLength_rho (hd : 2 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s), (rho D g).IsLength := by
  have := isProbabilityMeasure_pinLaw hd s
  have hlgf := (isWholeSpaceLGF_pinLaw hd hs).1
  filter_upwards [hD.length (pinLaw d s) id hlgf.isLGFPlusCont] with g hg
  exact p5b_isLength_rho hg

/-! ## Agreement on a dense sequence -/

/-- Two length metrics whose internal metrics on an open set `V` agree at the pairs of a dense sequence of `V` have
the same internal metric on `V × V`. -/
theorem p5b_internal_eq_of_dense {G₁ G₂ : ContMetric d} (h₁ : G₁.IsLength) (h₂ : G₂.IsLength)
    {V : Set (Rd d)} (hV : IsOpen V) {q : ℕ → Rd d} (hqV : ∀ n, q n ∈ V)
    (hq : V ⊆ closure (range q))
    (he : ∀ i j, G₁.internal V (q i) (q j) = G₂.internal V (q i) (q j)) :
    ∀ u ∈ V, ∀ v ∈ V, G₁.internal V u v = G₂.internal V u v := by
  have heq : EqOn (fun p : Rd d × Rd d => G₁.internal V p.1 p.2)
      (fun p => G₂.internal V p.1 p.2) (V ×ˢ V) := by
    refine EqOn.of_subset_closure (s := range (Prod.map q q)) ?_
      (G₁.continuousOn_internal h₁ hV) (G₂.continuousOn_internal h₂ hV) ?_ ?_
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      exact he i j
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      exact ⟨hqV i, hqV j⟩
    · rw [range_prodMap, closure_prod_eq]
      exact prod_mono hq hq
  intro u hu v hv
  exact heq (show (u, v) ∈ V ×ˢ V from ⟨hu, hv⟩)

/-! ## The locality lemma -/

/-- The chain profile of the pair `(ρ^D_g, ρ^E_g)` on `V` at the pairs of a sequence `q`. -/
def p5bProfileCode (D E : DistRd d → ContMetric d) (V : Set (Rd d)) (q : ℕ → Rd d) (g : DistRd d) :
    (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) :=
  (fun p => (rho D g).chainInf V (q p.1) (q p.2), fun p => (rho E g).chainInf V (q p.1) (q p.2))

theorem p5b_measurable_profileCode {D E : DistRd d → ContMetric d} (hD : Measurable D)
    (hE : Measurable E) (V : Set (Rd d)) (q : ℕ → Rd d) :
    Measurable (p5bProfileCode D E V q) := by
  have hc (F : DistRd d → ContMetric d) (hF : Measurable F) :
      Measurable fun g => fun p : ℕ × ℕ => (F g).chainInf V (q p.1) (q p.2) := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (ContMetric.measurable_chainInf V).comp
      (hF.prodMk (measurable_const.prodMk measurable_const))
  exact (hc _ (measurable_rho hD)).prodMk (hc _ (measurable_rho hE))

/-- `(r^{ξQ} e^{ξ h_r(0)})` at a field with `h_r(0) = 0`. -/
theorem p5b_sNorm_of_sphereAvg_eq_zero {ξ Q : ℝ} {g : DistRd d} {r : ℝ}
    (h0 : sphereAvg g r 0 = 0) : sNorm ξ Q g r 0 = r ^ (ξ * Q) := by
  rw [sNorm, h0, mul_zero, Real.exp_zero, mul_one]

/-- The `fieldSigma0 id J`-measurable version of the `V`-internal profile of `ρ^D` under `𝐏ₛ`: almost surely, for all
`u, v`, `(ρ^D_g)(u, v; V)` equals a `fieldSigma0 id J`-measurable function of `g`. -/
theorem p5b_exists_measurable_internal_rho (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D) {s : ℝ} (hs : 0 < s)
    {V J : Set (Rd d)} (hV : IsOpen V) (hJ : IsOpen J) (hVJ : V ⊆ J)
    (hSJ : sphere (0 : Rd d) s ⊆ J) :
    ∃ F : DistRd d → Rd d → Rd d → ℝ≥0∞, Measurable[fieldSigma0 id J] F ∧
      ∀ᵐ g ∂(pinLaw d s), ∀ u v, F g u v = (rho D g).internal V u v := by
  have := isProbabilityMeasure_pinLaw hd s
  obtain ⟨hlgf, hpin⟩ := isWholeSpaceLGF_pinLaw hd hs
  have hDs : IsSharpWeakExpMetric d ξ Q D := lemma101 hd hξ hD
  let V' : TopologicalSpace.Opens (Rd d) := ⟨V, hV⟩
  let J' : TopologicalSpace.Opens (Rd d) := ⟨J, hJ⟩
  obtain ⟨F, hFm, hFae⟩ :=
    hDs.exists_measurable_normInternal_all (P := pinLaw d s) (h := id) hd hlgf V' J' hVJ 0 hs hSJ
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-logMean D) * s ^ (ξ * Q))
  refine ⟨fun g u v => c * F g u v, ?_, ?_⟩
  · refine @measurable_pi_iff _ _ _ (fieldSigma0 id J) _ _ |>.2 fun u => ?_
    refine @measurable_pi_iff _ _ _ (fieldSigma0 id J) _ _ |>.2 fun v => ?_
    exact measurable_const.mul ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp hFm))
  · filter_upwards [hFae, hpin] with g hg h0 u v
    have hsn : sNorm ξ Q (id g) s 0 = s ^ (ξ * Q) := p5b_sNorm_of_sphereAvg_eq_zero h0
    have hsp : 0 < s ^ (ξ * Q) := Real.rpow_pos_of_pos hs _
    change c * F g u v = (rho D g).internal V u v
    rw [hg u v, hsn, p5b_internal_rho, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      mul_assoc, mul_inv_cancel₀ hsp.ne', mul_one]
    rfl

/-- **Locality lemma** (the argument of Lemma `a:lem-local`). Let `D`, `E` be strong at positive parameters, `s > 0`,
`V ⊆ J` open with `V` nonempty and the pin sphere `∂B_s ⊆ J`. An event `B` which is null-measurable for `𝐏ₛ` and
determined, on pairs of length metrics, by the `V`-internal profiles of `ρ^D_g` and `ρ^E_g` is almost surely equal to
an event of the mean-zero pairings supported in `J`. -/
theorem p5b_aeEventIn_of_profile (hd : 2 ≤ d) {ξ η Q Q' : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D) (hE : IsStrongExpMetric d η Q' E)
    {s : ℝ} (hs : 0 < s) {V J : Set (Rd d)} (hV : IsOpen V) (hVne : V.Nonempty) (hJ : IsOpen J)
    (hVJ : V ⊆ J) (hSJ : sphere (0 : Rd d) s ⊆ J) {B : Set (DistRd d)}
    (hB : NullMeasurableSet B (pinLaw d s))
    (hsat : ∀ g₁ g₂ : DistRd d, (rho D g₁).IsLength → (rho E g₁).IsLength →
      (rho D g₂).IsLength → (rho E g₂).IsLength →
      (∀ u ∈ V, ∀ v ∈ V, (rho D g₁).internal V u v = (rho D g₂).internal V u v) →
      (∀ u ∈ V, ∀ v ∈ V, (rho E g₁).internal V u v = (rho E g₂).internal V u v) →
      g₁ ∈ B → g₂ ∈ B) :
    AEEventIn (pinLaw d s) (fieldSigma0 id J) B := by
  classical
  have := isProbabilityMeasure_pinLaw hd s
  obtain ⟨FD, hFDm, hFDae⟩ := p5b_exists_measurable_internal_rho hd hξ hD hs hV hJ hVJ hSJ
  obtain ⟨FE, hFEm, hFEae⟩ := p5b_exists_measurable_internal_rho hd hη hE hs hV hJ hVJ hSJ
  obtain ⟨q, hqV, hqd⟩ := exists_denseSeq_rd hVne
  let R : DistRd d → (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) := p5bProfileCode D E V q
  have hRm : Measurable R := p5b_measurable_profileCode hD.measurable hE.measurable V q
  let Vf : DistRd d → (ℕ × ℕ → ℝ≥0∞) × (ℕ × ℕ → ℝ≥0∞) := fun g =>
    (fun p => FD g (q p.1) (q p.2), fun p => FE g (q p.1) (q p.2))
  have hcoord (F : DistRd d → Rd d → Rd d → ℝ≥0∞) (hF : Measurable[fieldSigma0 id J] F) :
      Measurable[fieldSigma0 id J] (fun g (p : ℕ × ℕ) => F g (q p.1) (q p.2)) := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 id J) _ _ |>.2 fun p => ?_
    exact (measurable_pi_apply (q p.2)).comp ((measurable_pi_apply (q p.1)).comp hF)
  have hVfm : Measurable[fieldSigma0 id J] Vf := (hcoord FD hFDm).prodMk (hcoord FE hFEm)
  have hlenD := p5b_ae_isLength_rho hd hD hs
  have hlenE := p5b_ae_isLength_rho hd hE hs
  have hVR : ∀ᵐ g ∂(pinLaw d s), Vf g = R (id g) := by
    filter_upwards [hFDae, hFEae, hlenD, hlenE] with g hD' hE' hlD hlE
    refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
    · change FD g (q p.1) (q p.2) = (rho D g).chainInf V (q p.1) (q p.2)
      rw [hD', (rho D g).internal_eq_chainInf hlD hV]
    · change FE g (q p.1) (q p.2) = (rho E g).chainInf V (q p.1) (q p.2)
      rw [hE', (rho E g).internal_eq_chainInf hlE hV]
  -- a Borel set of full measure on which both normalized metrics are length metrics
  have hbad : pinLaw d s {g : DistRd d | ¬((rho D g).IsLength ∧ (rho E g).IsLength)} = 0 :=
    ae_iff.mp (hlenD.and hlenE)
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  have hWlen : ∀ g ∈ Nᶜ, (rho D g).IsLength ∧ (rho E g).IsLength := by
    intro g hg
    by_contra hc
    exact hg (hsub hc)
  have hWae : ∀ᵐ g ∂(pinLaw d s), id g ∈ Nᶜ := by
    rw [ae_iff]
    have hset : {a : DistRd d | ¬id a ∈ Nᶜ} = N := by
      ext a
      simp only [id, mem_compl_iff, not_not, mem_ofPred_eq]
    rw [hset]
    exact hN0
  have hRsat : ∀ g₁ ∈ Nᶜ, ∀ g₂ ∈ Nᶜ, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ he hB₁
    obtain ⟨hD₁, hE₁⟩ := hWlen g₁ hg₁
    obtain ⟨hD₂, hE₂⟩ := hWlen g₂ hg₂
    refine hsat g₁ g₂ hD₁ hE₁ hD₂ hE₂ ?_ ?_ hB₁
    · refine p5b_internal_eq_of_dense hD₁ hD₂ hV hqV hqd fun i j => ?_
      rw [(rho D g₁).internal_eq_chainInf hD₁ hV, (rho D g₂).internal_eq_chainInf hD₂ hV]
      exact congrFun (congrArg Prod.fst he) (i, j)
    · refine p5b_internal_eq_of_dense hE₁ hE₂ hV hqV hqd fun i j => ?_
      rw [(rho E g₁).internal_eq_chainInf hE₁ hV, (rho E g₂).internal_eq_chainInf hE₂ hV]
      exact congrFun (congrArg Prod.snd he) (i, j)
  have hB' : NullMeasurableSet B ((pinLaw d s).map id) := by rwa [Measure.map_id]
  exact LQGMetric.LocalEvent.aeEventIn_of_saturated measurable_id hRm hVfm hVR hNm.compl hB' hWae hRsat

/-- **Locality lemma for one metric** (`p5b_aeEventIn_of_profile` with `E := D`). -/
theorem p5b_aeEventIn_of_profile_one (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {s : ℝ} (hs : 0 < s) {V J : Set (Rd d)} (hV : IsOpen V) (hVne : V.Nonempty) (hJ : IsOpen J)
    (hVJ : V ⊆ J) (hSJ : sphere (0 : Rd d) s ⊆ J) {B : Set (DistRd d)}
    (hB : NullMeasurableSet B (pinLaw d s))
    (hsat : ∀ g₁ g₂ : DistRd d, (rho D g₁).IsLength → (rho D g₂).IsLength →
      (∀ u ∈ V, ∀ v ∈ V, (rho D g₁).internal V u v = (rho D g₂).internal V u v) →
      g₁ ∈ B → g₂ ∈ B) :
    AEEventIn (pinLaw d s) (fieldSigma0 id J) B :=
  p5b_aeEventIn_of_profile hd hξ hξ hD hD hs hV hVne hJ hVJ hSJ hB
    (fun g₁ g₂ h₁ _ h₂ _ hDeq _ hB₁ => hsat g₁ g₂ h₁ h₂ hDeq hB₁)

end HigherDimLQGContinuity
