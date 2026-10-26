import SupercriticalLFPPAS.Separating.DetSeparation
import SupercriticalLFPPAS.Separating.Locality

/-!
# Lemma 3.5′: the events, their measurability, locality and the annulus iteration

Packet P35; planning audit SB2, item 2.2 and Details D3; paper §3.2, Lemma 3.5 (l. 331–362 of
`source/almost-sure-supercritical-lfpp.txt`).

For a root `(z, r)`, a cutoff `ε`, a polylogarithmic window parameter `qp` and `η`, the events are
the one-annulus events `E^ε_{r s_k}(z + r c; C)` of [2, Lemma 3.1] (`B2.Polylog.plEventLoc`, for the
pair `(D, plLocMetric ξ qp m ε)`) at the points `c` of the lattice `p35Lattice K (η/20)` and the
scales `s_k = 4η 16^{N-k}`, `1 ≤ k ≤ N = N(η)` (`p35AnnEvent`), and the event `p35Event35` that every
lattice point has at least `N/2` good scales. This file proves:

* measurability (`p35_event35_measurable`);
* locality modulo additive constants in the root annulus `A_{r/2,3r}(z)` for an arbitrary recentring
  (`p35_event35_aeEventIn`), from `p35_plEventLoc_aeEventIn`, for `2 ρ_ε(qp) < 4ηr`;
* the annulus iteration (1.6) at one lattice point (`p35_countOcc_lt_prob`: relative radii `1/16,
  1/2` at outer radius `8 r s_k`), given the marginal bound for the one-annulus events.

The canonical form of Lemma 3.5 (`qp = uniformLocalizationExponent δ L`, root `(0, 1)`, cutoff `δ`;
the marginal bound from (1.3), (2.4) and annular tightness) is assembled in
`Separating/Lemma35Canonical.lean` and `Separating/Lemma35Final.lean`. The scale-ratio identity
`p35_kappa_ratio` (`κ_ε(r s)/κ_ε(r) = κ_{ε/r}(s)`) and its consequence `p35_kappa_root_bounds`
transport (2.6) to a root `(z, r)` (for the physical root event of §3.3).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn plEventLoc plLocMetric annAround plRad)
open LQGMetric (DistC DistOn addConst restrictTo)
open LQGMetric.Blueprint (AEEventIn fieldSigma countOcc annulus)

/-! ### Scale ratios -/

/-- `κ_ε(r s) / κ_ε(r) = κ_{ε/r}(s)` (the canonical ratio of §3.3). -/
theorem p35_kappa_ratio (ξ Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : Set.Ioi (0 : ℝ))
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Compare.kappa ξ Q m ε ⟨r * s, mul_pos hr hs⟩ / Compare.kappa ξ Q m ε ⟨r, hr⟩ =
      Compare.kappa ξ Q m ⟨(ε : ℝ) / r, div_pos ε.2 hr⟩ ⟨s, hs⟩ := by
  unfold Compare.kappa
  have hε : (0 : ℝ) < ε := ε.2
  have harg : (⟨(ε : ℝ) / (r * s), Set.mem_Ioi.mpr (div_pos ε.2 (mul_pos hr hs))⟩ :
      Set.Ioi (0 : ℝ)) = ⟨(ε : ℝ) / r / s, Set.mem_Ioi.mpr (div_pos (div_pos ε.2 hr) hs)⟩ := by
    apply Subtype.ext
    simp only
    rw [div_div]
  simp only
  rw [harg]
  set M₁ := ((m ⟨(ε : ℝ) / r / s, Set.mem_Ioi.mpr (div_pos (div_pos ε.2 hr) hs)⟩ : ℝ))
  set M₂ := ((m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.2 hr)⟩ : ℝ))
  set M₃ := ((m ε : ℝ))
  have h1 : 0 < M₁ := (m _).2
  have h2 : 0 < M₂ := (m _).2
  have h3 : 0 < M₃ := (m _).2
  have hrs : (r * s) ^ (ξ * Q) = r ^ (ξ * Q) * s ^ (ξ * Q) := Real.mul_rpow hr.le hs.le
  have hrp : 0 < r ^ (ξ * Q) := Real.rpow_pos_of_pos hr _
  have hsp : 0 < s ^ (ξ * Q) := Real.rpow_pos_of_pos hs _
  rw [hrs]
  field_simp

/-- `κ_ε(r) > 0`. -/
theorem p35_kappa_pos' (ξ Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε r : Set.Ioi (0 : ℝ)) : 0 < Compare.kappa ξ Q m ε r := by
  unfold Compare.kappa
  have hρ : (0 : ℝ) < r := r.2
  have hp := Real.rpow_pos_of_pos hρ (ξ * Q)
  have hm1 := (m ε).2
  have hm2 := (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.2 r.2)⟩).2
  simp only [Set.mem_Ioi] at hm1 hm2
  positivity

/-- (2.6) transported to the root scale: if `κ_δ(s) ∈ [C⁻¹, C]` for the canonical cutoff
`δ = ε/r`, then `κ_ε(r s) ≤ C κ_ε(r)` and `κ_ε(r s)⁻¹ ≤ C κ_ε(r)⁻¹`. -/
theorem p35_kappa_root_bounds (ξ Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : Set.Ioi (0 : ℝ)) {r s C : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hlow : C⁻¹ ≤ Compare.kappa ξ Q m ⟨(ε : ℝ) / r, div_pos ε.2 hr⟩ ⟨s, hs⟩)
    (hupp : Compare.kappa ξ Q m ⟨(ε : ℝ) / r, div_pos ε.2 hr⟩ ⟨s, hs⟩ ≤ C) :
    Compare.kappa ξ Q m ε ⟨r * s, mul_pos hr hs⟩ ≤ C * Compare.kappa ξ Q m ε ⟨r, hr⟩ ∧
      (Compare.kappa ξ Q m ε ⟨r * s, mul_pos hr hs⟩)⁻¹ ≤
        C * (Compare.kappa ξ Q m ε ⟨r, hr⟩)⁻¹ := by
  rw [← p35_kappa_ratio ξ Q m ε hr hs] at hlow hupp
  have ha : 0 < Compare.kappa ξ Q m ε ⟨r * s, mul_pos hr hs⟩ := p35_kappa_pos' ξ Q m _ _
  have hb : 0 < Compare.kappa ξ Q m ε ⟨r, hr⟩ := p35_kappa_pos' ξ Q m _ _
  set a := Compare.kappa ξ Q m ε ⟨r * s, mul_pos hr hs⟩
  set b := Compare.kappa ξ Q m ε ⟨r, hr⟩
  have hab : 0 < a / b := div_pos ha hb
  have hC : 0 < C := lt_of_lt_of_le hab hupp
  constructor
  · rwa [div_le_iff₀ hb] at hupp
  · have h1 : b / a ≤ C := by
      have := (inv_le_inv₀ hab (inv_pos.2 hC)).2 hlow
      rwa [inv_inv, inv_div] at this
    rw [div_le_iff₀ ha] at h1
    rw [inv_le_iff_one_le_mul₀ ha]
    calc (1 : ℝ) = b⁻¹ * b := (inv_mul_cancel₀ hb.ne').symm
      _ ≤ b⁻¹ * (C * a) := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hb).le
      _ = C * b⁻¹ * a := by ring

/-! ### The events -/

/-- The one-annulus events of Lemma 3.5 at the lattice point `c` of the root `(z, r)`:
`E_k = {h ∈ E^ε_{r s_k}(z + r c; C)}` for `1 ≤ k ≤ N(η)` and `E_k = Ω` otherwise, for the pair
`(D, plLocMetric ξ qp m ε)` (`qp = uniformLocalizationExponent δ L` gives `Y_{δ,L}` at `ε = δ`). -/
def p35AnnEvent (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (qp : ℝ) {Ω : Type} (h : Ω → DistC) (z : ℂ) {r : ℝ}
    (hr : 0 < r) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) (C : ℝ) (c : ℂ)
    (k : ℕ) : Set Ω :=
  if 1 ≤ k ∧ k ≤ p35ScaleCount η then
    {ω | h ω ∈ plEventLoc (ξ : ℝ) D (Compare.powScale ξ Q) m qp (z + (r : ℂ) * c) ε hε
      ⟨r * p35Scale η k, mul_pos hr (p35Scale_pos hη k)⟩ C}
  else univ

/-- **The event of Lemma 3.5 at the root `(z, r)`**: every point `c` of the lattice
`p35Lattice K (η/20)` has at least `N(η)/2` good scales among `s_1, …, s_{N(η)}`. -/
def p35Event35 (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (qp : ℝ) {Ω : Type} (h : Ω → DistC) (z : ℂ) {r : ℝ}
    (hr : 0 < r) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) (C : ℝ) (K : Set ℂ) :
    Set Ω :=
  ⋂ c ∈ p35Lattice K (η / 20), {ω | (1 / 2 : ℝ) * p35ScaleCount η ≤
    (countOcc (p35AnnEvent ξ Q D m qp h z hr ε hε hη C c) (p35ScaleCount η) ω : ℝ)}

theorem p35_plRad_one (ε : ℝ) : plRad 1 ε = ε * Real.log ε⁻¹ := by
  simp [plRad, Real.rpow_one]

/-- The carrier `A_{ρ/2,4ρ}(w)` of the one-annulus event at a lattice point near `K` and a scale
`ρ = r s_j ≤ r η^{1/2}/4` lies in the root annulus `A_{r/2,3r}(z)`. -/
theorem p35_carrier_subset_root {K : Set ℂ} (hK : ∀ k ∈ K, 3 / 4 ≤ ‖k‖ ∧ ‖k‖ ≤ 5 / 2)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) (hsmall : Real.sqrt η + η / 20 ≤ 1 / 4) {c : ℂ}
    (hc : c ∈ p35Lattice K (η / 20)) (z : ℂ) {r : ℝ} (hr : 0 < r) {j : ℕ} (hj : 1 ≤ j) :
    B2.Polylog.eventCarrier (z + (r : ℂ) * c) (r * p35Scale η j) ⊆ (annulus z (r / 2) (3 * r) : Set ℂ) := by
  obtain ⟨k, hk, hkc⟩ := p35_mem_lattice_near hc
  have hkK := hK k hk
  have hsj := p35Scale_le hη hη1 hj
  have hsjpos := p35Scale_pos hη j
  have hc1 : 3 / 4 - η / 20 ≤ ‖c‖ := by
    have := norm_sub_norm_le k c
    rw [← dist_eq_norm] at this
    linarith [hkK.1]
  have hc2 : ‖c‖ ≤ 5 / 2 + η / 20 := by
    have := norm_le_norm_add_norm_sub' c k
    have hck : ‖c - k‖ = dist k c := by rw [dist_comm, dist_eq_norm]
    linarith [hkK.2]
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hwz : ‖z + (r : ℂ) * c - z‖ = r * ‖c‖ := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hup : ‖y - z‖ ≤ ‖y - (z + (r : ℂ) * c)‖ + ‖z + (r : ℂ) * c - z‖ := by
    calc ‖y - z‖ = ‖(y - (z + (r : ℂ) * c)) + (z + (r : ℂ) * c - z)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have hlo : ‖z + (r : ℂ) * c - z‖ ≤ ‖y - (z + (r : ℂ) * c)‖ + ‖y - z‖ := by
    calc ‖z + (r : ℂ) * c - z‖ = ‖-(y - (z + (r : ℂ) * c)) + (y - z)‖ := by ring_nf
      _ ≤ ‖-(y - (z + (r : ℂ) * c))‖ + ‖y - z‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  rw [hwz] at hup hlo
  have h4 : 4 * (r * p35Scale η j) ≤ r * Real.sqrt η := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The carrier of the one-annulus event at radius `ρ = r s_k` is the open annulus of relative
radii `1/16, 1/2` at outer radius `8ρ`, the form consumed by the annulus iteration. -/
theorem p35_carrier_eq_iterAnnulus (w : ℂ) (ρ : ℝ) :
    B2.Polylog.eventCarrier w ρ ⊆ (annulus w ((1 / 16 : ℝ) * (8 * ρ)) ((1 / 2 : ℝ) * (8 * ρ)) : Set ℂ) := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · have : (1 / 16 : ℝ) * (8 * ρ) = ρ / 2 := by ring
    rw [this]
    exact hy1
  · have : (1 / 2 : ℝ) * (8 * ρ) = 4 * ρ := by ring
    rw [this]
    exact hy2

/-! ### Measurability, locality and marginal probability of the one-annulus events -/

section Events

variable (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
  (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (qp : ℝ) {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
  (z : ℂ) {r : ℝ} (hr : 0 < r) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) (C : ℝ)

theorem p35_annEvent_measurable (hDm : Measurable D) (hhm : Measurable h) (c : ℂ) (k : ℕ) :
    MeasurableSet (p35AnnEvent ξ Q D m qp h z hr ε hε hη C c k) := by
  unfold p35AnnEvent
  split_ifs
  · exact hhm (B2.Polylog.measurableSet_plEventLoc (ξ : ℝ) hDm _ m qp _ ε hε _ C)
  · exact MeasurableSet.univ

omit [MeasurableSpace Ω] in
/-- Counting events of measurable events are measurable. -/
theorem p35_countOcc_ge_measurable [MeasurableSpace Ω] (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet (E k)) (N : ℕ) (b : ℝ) :
    MeasurableSet {ω | b ≤ (countOcc E N ω : ℝ)} := by
  have hmeas : Measurable fun ω => (countOcc E N ω : ℝ) := by
    have : (fun ω => (countOcc E N ω : ℝ)) =
        fun ω => ∑ k ∈ Finset.Icc 1 N, (E k).indicator (fun _ => (1 : ℝ)) ω := by
      funext ω
      exact p35_countOcc_eq_sum E N ω
    rw [this]
    exact Finset.measurable_sum _ fun k _ => measurable_const.indicator (hE k)
  exact measurableSet_le measurable_const hmeas

/-- The event of Lemma 3.5 is measurable. -/
theorem p35_event35_measurable (hDm : Measurable D) (hhm : Measurable h) (K : Set ℂ) :
    MeasurableSet (p35Event35 ξ Q D m qp h z hr ε hε hη C K) := by
  unfold p35Event35
  refine Finset.measurableSet_biInter _ fun c _ => ?_
  exact p35_countOcc_ge_measurable _ (fun k => p35_annEvent_measurable ξ Q D m qp h z hr ε hε hη C
    hDm hhm c k) _ _

/-- Each one-annulus event of Lemma 3.5 is almost surely an event of the field in the root annulus
`A_{r/2,3r}(z)` recentred by an arbitrary `X`. -/
theorem p35_annEvent_aeEventIn_root (P : Measure Ω) [IsProbabilityMeasure P]
    (hh : IsNormalizedWholePlaneGFF h P)
    (hDw : B2.Iface.IsPfeWeakMetric ξ D (Compare.powScale ξ Q)) {K : Set ℂ}
    (hK : ∀ k ∈ K, 3 / 4 ≤ ‖k‖ ∧ ‖k‖ ≤ 5 / 2) (hη1 : η < 1)
    (hsmall : Real.sqrt η + η / 20 ≤ 1 / 4) (hloc : 2 * plRad qp ε < 4 * η * r)
    {c : ℂ} (hc : c ∈ p35Lattice K (η / 20)) (X : Ω → ℝ) (k : ℕ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-X ω)) (annulus z (r / 2) (3 * r)))
      (p35AnnEvent ξ Q D m qp h z hr ε hε hη C c k) := by
  unfold p35AnnEvent
  split_ifs with hk
  · refine p35_plEventLoc_aeEventIn P h hh hDw m qp _ ε hε _ C _
      (p35_carrier_subset_root hK hη hη1 hsmall hc z hr hk.1) ?_ X
    have := p35Scale_ge hη hk.2
    show 2 * plRad qp ε < r * p35Scale η k
    nlinarith
  · exact p35_aeEventIn_univ _ _

/-- The event of Lemma 3.5 is almost surely an event of the field in the root annulus
`A_{r/2,3r}(z)` modulo additive constants (recentred by an arbitrary `X`). -/
theorem p35_event35_aeEventIn (P : Measure Ω) [IsProbabilityMeasure P]
    (hh : IsNormalizedWholePlaneGFF h P)
    (hDw : B2.Iface.IsPfeWeakMetric ξ D (Compare.powScale ξ Q)) {K : Set ℂ}
    (hK : ∀ k ∈ K, 3 / 4 ≤ ‖k‖ ∧ ‖k‖ ≤ 5 / 2) (hη1 : η < 1)
    (hsmall : Real.sqrt η + η / 20 ≤ 1 / 4) (hloc : 2 * plRad qp ε < 4 * η * r)
    (X : Ω → ℝ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-X ω)) (annulus z (r / 2) (3 * r)))
      (p35Event35 ξ Q D m qp h z hr ε hε hη C K) := by
  unfold p35Event35
  refine p35_aeEventIn_biInter_finset _ _ fun c hc => ?_
  exact p35_aeEventIn_countOcc_ge _ _ _ _ fun k _ _ =>
    p35_annEvent_aeEventIn_root ξ Q D m qp h z hr ε hε hη C P hh hDw hK hη1 hsmall hloc hc X k

/-- **The annulus iteration at one lattice point**: fewer than `N(η)/2` good scales has
probability at most `c₀ e^{-a N(η)}`. -/
theorem p35_countOcc_lt_prob (P : Measure Ω) [IsProbabilityMeasure P]
    (hh : IsNormalizedWholePlaneGFF h P)
    (hDw : B2.Iface.IsPfeWeakMetric ξ D (Compare.powScale ξ Q)) {p c₀ a : ℝ} (hp1 : p < 1)
    (hconc : ∀ (w : ℂ) (R : ℕ → ℝ) (E : ℕ → Set Ω), (∀ k, 0 < R k) → Antitone R →
      (∀ k, R (k + 1) / R k ≤ 1 / 16) →
      (∀ k, AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) (R k) w))
        (annulus w (1 / 16 * R k) (1 / 2 * R k))) (E k)) →
      (∀ k, ENNReal.ofReal p ≤ P (E k)) →
      ∀ N : ℕ, P {ω | (countOcc E N ω : ℝ) < 1 / 2 * N} ≤ ENNReal.ofReal (c₀ * Real.exp (-a * N)))
    (c : ℂ)
    (hprobk : ∀ k, 1 ≤ k → k ≤ p35ScaleCount η → ENNReal.ofReal p ≤
      P {ω | h ω ∈ plEventLoc (ξ : ℝ) D (Compare.powScale ξ Q) m qp (z + (r : ℂ) * c) ε hε
        ⟨r * p35Scale η k, mul_pos hr (p35Scale_pos hη k)⟩ C})
    (hloc : 2 * plRad qp ε < 4 * η * r) :
    P {ω | (countOcc (p35AnnEvent ξ Q D m qp h z hr ε hε hη C c) (p35ScaleCount η) ω : ℝ) <
      1 / 2 * p35ScaleCount η} ≤ ENNReal.ofReal (c₀ * Real.exp (-a * p35ScaleCount η)) := by
  set w : ℂ := z + (r : ℂ) * c with hw
  let R : ℕ → ℝ := fun k => 8 * (r * p35Scale η k)
  have hRpos : ∀ k, 0 < R k := fun k => by
    have := p35Scale_pos hη k
    show 0 < 8 * (r * p35Scale η k)
    positivity
  have hRsucc : ∀ k, R (k + 1) = R k / 16 := fun k => by
    show 8 * (r * p35Scale η (k + 1)) = 8 * (r * p35Scale η k) / 16
    rw [p35Scale_succ]
    ring
  have hanti : Antitone R := by
    apply antitone_nat_of_succ_le
    intro k
    rw [hRsucc]
    have := hRpos k
    linarith
  have hratio : ∀ k, R (k + 1) / R k ≤ 1 / 16 := fun k => by
    rw [hRsucc]
    have hk := hRpos k
    rw [div_div, mul_comm, ← div_div, div_self hk.ne']
  refine hconc w R _ hRpos hanti hratio ?_ ?_ (p35ScaleCount η)
  · intro k
    unfold p35AnnEvent
    split_ifs with hk
    · refine p35_plEventLoc_aeEventIn P h hh hDw m qp _ ε hε _ C _
        (p35_carrier_eq_iterAnnulus w (r * p35Scale η k)) ?_ _
      have := p35Scale_ge hη hk.2
      show 2 * plRad qp ε < r * p35Scale η k
      nlinarith
    · exact p35_aeEventIn_univ _ _
  · intro k
    unfold p35AnnEvent
    split_ifs with hk
    · exact hprobk k hk.1 hk.2
    · rw [measure_univ]
      exact ENNReal.ofReal_le_one.2 hp1.le

end Events

end SupercriticalLFPPAS.Separating
