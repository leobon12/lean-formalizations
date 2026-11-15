/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71KMarked

/-!
# Lemma 7.1's pocket chart, normalized at the marked prime ends, measurably

Packet PROVE-LEMMA71K. Specification §7.1 (`source/spec/p193-240.md` L576–L606, pp. 222–224): "Let `ψ : C → ℍ` be the
conformal map sending `x₀` to `0` and `y₀` to `∞` … The outer curves determine `C`, `ψ`, and its inherited argument
branch."

For a random simply connected domain `C ω ⊆ ℍ` observed through closed balls and a continuous random right wall `R`,
this file builds, for **every** `ω`, a chart `c ω` on `C ω` (conformal, measurable forward map and lift, the lift a
continuous branch of `arg ψ′`) which is normalized along measurable approach sequences, and which on every **marked
pocket configuration** (`IsMarkedPocket`: the wall times in the closure of the Cayley image form an interval `[a, b]`,
the Cayley image is a Jordan domain) is the two-point uniformizer at the opening point `α̃ a` and the closing point
`α̃ b` (compactified picture; `α̃ b = 1` when the pocket closes at `∞`).

* `exists_index_near_disc`, `exists_measurable_approach_disc`: approach sequences in the coordinates of a measurable
  disc chart (the fallback off the good event);
* `IsMarkedPocket` (definition), `isMarkedPocket_of_mem_betweenComponents` (from `pocket_marked`);
* **`exists_markedPocketChart`**: the measurable chart (generic σ-algebra);
* **`exists_ext_of_isMarkedPocket`** (deterministic): on a marked pocket, every chart that is unique up to positive
  scaling along the approach sequences has a continuous injective boundary extension to the closure of the Cayley image
  minus the closing point, vanishing at the opening point and tending to `∞` at the closing point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71K

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

/-! ### Approach sequences in disc-chart coordinates -/

/-- Points of a dense sequence in `C` whose images under a conformal map `Φ : C → 𝔻` are close to a given point of the
unit circle. -/
theorem exists_index_near_disc {C : Set ℂ} (hCo : IsOpen C) {Φ : ℂ → ℂ} (hΦ : IsConformalBijection Φ C (ball 0 1))
    {e : ℕ → ℂ} (he : DenseRange e) {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) :
    ∃ j, e j ∈ C ∧ dist (Φ (e j)) ζ < r := by
  have hζc : ζ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right, hζ]
  obtain ⟨w, hw, hwζ⟩ := Metric.mem_closure_iff.1 hζc (r / 2) (half_pos hr)
  obtain ⟨z, hz, rfl⟩ := hΦ.2.surjOn hw
  have hc : ContinuousAt Φ z := hΦ.1.continuousOn.continuousAt (hCo.mem_nhds hz)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds (ball_mem_nhds (Φ z) (half_pos hr)))
  obtain ⟨j, hj⟩ := he.exists_mem_open (hCo.inter isOpen_ball) ⟨z, hz, mem_ball_self hδ⟩
  refine ⟨j, hj.1, ?_⟩
  have h1 : dist (Φ (e j)) (Φ z) < r / 2 := hball hj.2
  calc dist (Φ (e j)) ζ ≤ dist (Φ (e j)) (Φ z) + dist (Φ z) ζ := dist_triangle _ _ _
    _ = dist (Φ (e j)) (Φ z) + dist ζ (Φ z) := by rw [dist_comm (Φ z) ζ]
    _ < r / 2 + r / 2 := add_lt_add h1 hwζ
    _ = r := by ring

section Approach

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A measurable approach sequence in disc-chart coordinates**: for measurable disc charts `Φ ω : C ω → 𝔻` and a
point `ζ` of the unit circle, indices `N m ω` with `e (N m ω) ∈ C ω` and `Φ ω (e (N m ω)) → ζ`, for every `ω`. -/
theorem exists_measurable_approach_disc {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω}) {Φ : Ω → ℂ → ℂ}
    (hΦ : ∀ ω, IsConformalBijection (Φ ω) (C ω) (ball 0 1)) (hΦm : ∀ z, Measurable fun ω => Φ ω z) {e : ℕ → ℂ}
    (he : DenseRange e) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ N : ℕ → Ω → ℕ, (∀ m, Measurable (N m)) ∧ (∀ m ω, e (N m ω) ∈ C ω) ∧
      ∀ ω, Tendsto (fun m => Φ ω (e (N m ω))) atTop (𝓝 ζ) := by
  classical
  have hex : ∀ (m : ℕ) (ω : Ω), ∃ j, e j ∈ C ω ∧ dist (Φ ω (e j)) ζ < 1 / ((m : ℝ) + 1) := fun m ω =>
    exists_index_near_disc (hCo ω) (hΦ ω) he hζ (by positivity)
  refine ⟨fun m ω => Nat.find (hex m ω), fun m => ?_, fun m ω => (Nat.find_spec (hex m ω)).1, fun ω => ?_⟩
  · exact measurable_find (hex m) fun j =>
      (hCm (e j)).inter (measurableSet_lt ((hΦm (e j)).dist measurable_const) measurable_const)
  · refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun m => dist_nonneg) (fun m => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat)
    exact (Nat.find_spec (hex m ω)).2.le

end Approach

/-! ### Marked pockets -/

/-- **A marked pocket configuration** of a domain `C ⊆ ℍ` and a right wall `R`: the wall times `s ∈ [0, 1]` at which the
wall crosscut lies in the closure of `cayley '' C` form exactly `[a, b]` with `0 ≤ a < b ≤ 1`; the frontier of
`cayley '' C` is a Jordan curve containing the distinct marked points `α̃ a` (opening) and `α̃ b` (closing). -/
def IsMarkedPocket (R : ℝ≥0 → ℂ) (C : Set ℂ) (a b : ℝ) : Prop :=
  0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure (cayley '' C)} = Icc a b ∧
    LQGMetric.JordanMap.IsJordanCurve (frontier (cayley '' C)) ∧
    wallPt R a ∈ frontier (cayley '' C) ∧ wallPt R b ∈ frontier (cayley '' C) ∧ wallPt R a ≠ wallPt R b

/-- **Every component between two ordered simple proper curves is a marked pocket** of the right wall
(`pocket_marked`). -/
theorem isMarkedPocket_of_mem_betweenComponents {R L : ℝ≥0 → ℂ} (hR : Lemma71I.IsSimpleProper R)
    (hL : Lemma71I.IsSimpleProper L)
    (hord : Disjoint (range L) (rightSideOf (range R))) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) : ∃ a b, IsMarkedPocket R C a b := by
  rw [← Lemma71I.arcRange_realPath R, ← Lemma71I.arcRange_realPath L] at hC hord
  obtain ⟨a, b, h⟩ := pocket_marked (Lemma71I.IsSimpleProper.isProperArc hR)
    (Lemma71I.IsSimpleProper.isProperArc hL) hord hC
  exact ⟨a, b, h⟩

/-! ### The measurable chart -/

section Chart

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The measurable pocket chart, normalized at the marked prime ends.** For a random open, connected, simply
connected `C ω ⊆ ℍ` observed through closed balls, a dense sequence `e` with a measurable index `Np` of a point of
`C ω`, and a random right wall `R` (continuous for every `ω`, measurable coordinates): measurable approach sequences
`Nx`, `Ny` in `C ω` and a chart `c ω` on `C ω`, for every `ω`, conformal onto `ℍ`, with measurable domain events,
forward map and lift, the lift a continuous branch of `arg ψ′`, `ψ → 0` along `Nx` and `|ψ| → ∞` along `Ny`, unique up
to positive scaling with these properties; and on every marked pocket configuration the Cayley images of the approach
sequences tend to the opening point `α̃ a` and the closing point `α̃ b`. -/
theorem exists_markedPocketChart {C : Ω → Set ℂ}
    (hC : ∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet {ω | closedBall z r ⊆ C ω}) {e : ℕ → ℂ} (he : DenseRange e)
    {Np : Ω → ℕ} (hNp : Measurable Np) (hNpC : ∀ ω, e (Np ω) ∈ C ω)
    {R : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hRm : ∀ t, Measurable fun ω => R ω t) :
    ∃ (Nx Ny : ℕ → Ω → ℕ) (c : Ω → Chart),
      (∀ m, Measurable (Nx m)) ∧ (∀ m, Measurable (Ny m)) ∧ (∀ m ω, e (Nx m ω) ∈ C ω) ∧
      (∀ m ω, e (Ny m ω) ∈ C ω) ∧
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = C ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (C ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (L z).im) ∧
      (∀ ω, Tendsto (fun m => (c ω).1 (e (Nx m ω))) atTop (𝓝 0) ∧
        Tendsto (fun m => ‖(c ω).1 (e (Ny m ω))‖) atTop atTop) ∧
      (∀ ω (ψ₁ : ℂ → ℂ), IsConformalBijection ψ₁ (C ω) H → Tendsto (fun m => ψ₁ (e (Nx m ω))) atTop (𝓝 0) →
        Tendsto (fun m => ‖ψ₁ (e (Ny m ω))‖) atTop atTop →
        ∃ a : ℝ, 0 < a ∧ EqOn (c ω).1 (fun z => (a : ℂ) * ψ₁ z) (C ω)) ∧
      ∀ ω a b, IsMarkedPocket (R ω) (C ω) a b →
        Tendsto (fun m => cayley (e (Nx m ω))) atTop (𝓝[cayley '' C ω] (wallPt (R ω) a)) ∧
        Tendsto (fun m => cayley (e (Ny m ω))) atTop (𝓝[cayley '' C ω] (wallPt (R ω) b)) := by
  classical
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hCc : ∀ ω, IsConnected (C ω) := fun ω => (hC ω).2.1
  have hCsc : ∀ ω, IsSimplyConnected (C ω) := fun ω => (hC ω).2.2.1
  have hCH : ∀ ω, C ω ⊆ H := fun ω => (hC ω).2.2.2
  have hmem := Lemma71E.measurableSet_mem_of_closedBall hCo hCm
  -- the marked points, measurably
  have hUm : ∀ q : ℚ, MeasurableSet {ω | wallPt (R ω) q ∈ closure (cayley '' C ω)} := fun q =>
    measurableSet_mem_closure_cayley_image hCo hCH hmem he (measurable_wallPt_const hRm q)
  have hp : Measurable fun ω => wallPt (R ω) (openTime (R ω) (closure (cayley '' C ω))) :=
    measurable_wallPt hRc hRm (measurable_openTime hUm)
  have hq : Measurable fun ω => wallPt (R ω) (closeTime (R ω) (closure (cayley '' C ω))) :=
    measurable_wallPt hRc hRm (measurable_closeTime hUm)
  obtain ⟨NxG, hNxG, hNxGC, hNxGt⟩ := exists_measurable_approach_cayley hCo hCH hmem he hNp hNpC hp
  obtain ⟨NyG, hNyG, hNyGC, hNyGt⟩ := exists_measurable_approach_cayley hCo hCH hmem he hNp hNpC hq
  -- the fallback: a measurable disc chart
  obtain ⟨Φ, -, a₀, -, hΦ, -, hΦm, -, -, -⟩ := Lemma71E.exists_measurable_discPair hCo hCc hCsc hCH hCm he
  have hΦ' : ∀ ω, IsConformalBijection (Φ ω) (C ω) (ball 0 1) := fun ω => (hΦ ω).1
  obtain ⟨NxF, hNxF, hNxFC, hNxFt⟩ := exists_measurable_approach_disc hCo hmem hΦ' hΦm he
    (ζ := -1) (by rw [norm_neg, norm_one])
  obtain ⟨NyF, hNyF, hNyFC, hNyFt⟩ := exists_measurable_approach_disc hCo hmem hΦ' hΦm he
    (ζ := 1) norm_one
  -- the good event: the disc chart has distinct circle limits along the geometric sequences
  have hΦe : Measurable fun x : Ω × ℕ => Φ x.1 (e x.2) :=
    measurable_from_prod_countable_left fun j => hΦm (e j)
  have hfx : ∀ m, Measurable fun ω => Φ ω (e (NxG m ω)) := fun m => hΦe.comp (measurable_id.prodMk (hNxG m))
  have hfy : ∀ m, Measurable fun ω => Φ ω (e (NyG m ω)) := fun m => hΦe.comp (measurable_id.prodMk (hNyG m))
  set px : Ω → ℂ := fun ω => limUnder atTop fun m => Φ ω (e (NxG m ω)) with hpxdef
  set py : Ω → ℂ := fun ω => limUnder atTop fun m => Φ ω (e (NyG m ω)) with hpydef
  have hpx : Measurable px := (StronglyMeasurable.limUnder fun m => (hfx m).stronglyMeasurable).measurable
  have hpy : Measurable py := (StronglyMeasurable.limUnder fun m => (hfy m).stronglyMeasurable).measurable
  set G : Set Ω := {ω | ((∃ c, Tendsto (fun m => Φ ω (e (NxG m ω))) atTop (𝓝 c)) ∧
    (∃ c, Tendsto (fun m => Φ ω (e (NyG m ω))) atTop (𝓝 c))) ∧ ‖px ω‖ = 1 ∧ ‖py ω‖ = 1 ∧ px ω ≠ py ω}
    with hGdef
  have hG : MeasurableSet G :=
    ((StronglyMeasurable.measurableSet_exists_tendsto fun m => (hfx m).stronglyMeasurable).inter
      (StronglyMeasurable.measurableSet_exists_tendsto fun m => (hfy m).stronglyMeasurable)).inter
      ((measurableSet_eq_fun hpx.norm measurable_const).inter ((measurableSet_eq_fun hpy.norm measurable_const).inter
        (measurableSet_eq_fun hpx hpy).compl))
  set Nx : ℕ → Ω → ℕ := fun m => G.piecewise (NxG m) (NxF m) with hNxdef
  set Ny : ℕ → Ω → ℕ := fun m => G.piecewise (NyG m) (NyF m) with hNydef
  have hNx : ∀ m, Measurable (Nx m) := fun m => (hNxG m).piecewise hG (hNxF m)
  have hNy : ∀ m, Measurable (Ny m) := fun m => (hNyG m).piecewise hG (hNyF m)
  have hNxin : ∀ ω, ω ∈ G → ∀ m, Nx m ω = NxG m ω := fun ω hω m => Set.piecewise_eq_of_mem _ _ _ hω
  have hNyin : ∀ ω, ω ∈ G → ∀ m, Ny m ω = NyG m ω := fun ω hω m => Set.piecewise_eq_of_mem _ _ _ hω
  have hNxout : ∀ ω, ω ∉ G → ∀ m, Nx m ω = NxF m ω := fun ω hω m => Set.piecewise_eq_of_notMem _ _ _ hω
  have hNyout : ∀ ω, ω ∉ G → ∀ m, Ny m ω = NyF m ω := fun ω hω m => Set.piecewise_eq_of_notMem _ _ _ hω
  have hNxC : ∀ m ω, e (Nx m ω) ∈ C ω := fun m ω => by
    by_cases hω : ω ∈ G
    · rw [hNxin ω hω]; exact hNxGC m ω
    · rw [hNxout ω hω]; exact hNxFC m ω
  have hNyC : ∀ m ω, e (Ny m ω) ∈ C ω := fun m ω => by
    by_cases hω : ω ∈ G
    · rw [hNyin ω hω]; exact hNyGC m ω
    · rw [hNyout ω hω]; exact hNyFC m ω
  -- a uniformizer for every `ω`
  have hunif : ∀ (ω : Ω) (p q : ℂ) (N N' : ℕ → ℕ), ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q → (∀ m, e (N' m) ∈ C ω) →
      Tendsto (fun m => Φ ω (e (N m))) atTop (𝓝 p) → Tendsto (fun m => Φ ω (e (N' m))) atTop (𝓝 q) →
      ∃ ψ₁ : ℂ → ℂ, IsConformalBijection ψ₁ (C ω) H ∧ Tendsto (fun m => ψ₁ (e (N m))) atTop (𝓝 0) ∧
        Tendsto (fun m => ‖ψ₁ (e (N' m))‖) atTop atTop := by
    intro ω p q N N' hp1 hq1 hpq hN'C hNt hN't
    refine ⟨Lemma71E.bdryMob p q ∘ Φ ω,
      isConformalBijection_comp (Lemma71E.isConformalBijection_bdryMob (p := p) hq1) (hΦ' ω), ?_, ?_⟩
    · exact (Lemma71E.tendsto_bdryMob_left hp1 hq1 hpq).comp hNt
    · exact (Lemma71E.tendsto_norm_bdryMob_right (p := p) hq1).comp
        (tendsto_nhdsWithin_iff.2 ⟨hN't, Eventually.of_forall fun m => (hΦ' ω).2.mapsTo (hN'C m)⟩)
  have hψ₁ : ∀ ω, ∃ ψ₁ : ℂ → ℂ, IsConformalBijection ψ₁ (C ω) H ∧
      Tendsto (fun m => ψ₁ (e (Nx m ω))) atTop (𝓝 0) ∧ Tendsto (fun m => ‖ψ₁ (e (Ny m ω))‖) atTop atTop := by
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨⟨⟨cx, hcx⟩, ⟨cy, hcy⟩⟩, h1, h2, h3⟩ := hω
      have ex : px ω = cx := hcx.limUnder_eq
      have ey : py ω = cy := hcy.limUnder_eq
      rw [ex] at h1 h3
      rw [ey] at h2 h3
      have hω' : ω ∈ G := ⟨⟨⟨cx, hcx⟩, ⟨cy, hcy⟩⟩, by rw [ex]; exact h1, by rw [ey]; exact h2,
        by rw [ex, ey]; exact h3⟩
      simp only [hNxin ω hω', hNyin ω hω']
      exact hunif ω cx cy (NxG · ω) (NyG · ω) h1 h2 h3 (fun m => hNyGC m ω) hcx hcy
    · simp only [hNxout ω hω, hNyout ω hω]
      exact hunif ω (-1) 1 (NxF · ω) (NyF · ω) (by rw [norm_neg, norm_one]) norm_one
        (by norm_num) (fun m => hNyFC m ω) (hNxFt ω) (hNyFt ω)
  obtain ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, hnorm, huniq⟩ :=
    Lemma71E.exists_measurable_twoPointChart hCo hCc hCsc hCH hCm he hNx hNy hNxC hNyC hψ₁
  refine ⟨Nx, Ny, c, hNx, hNy, hNxC, hNyC, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, hnorm, huniq, ?_⟩
  -- marked pocket configurations
  intro ω a b hM
  obtain ⟨ha0, hab, hb1, hI, hJ, hpa, hpb, hpq⟩ := hM
  obtain ⟨eo, ec⟩ := openTime_closeTime_eq ha0 hab hb1 hI
  have hpt : Tendsto (fun m => cayley (e (NxG m ω))) atTop (𝓝[cayley '' C ω] (wallPt (R ω) a)) := by
    have := hNxGt ω (by rw [eo]; exact frontier_subset_closure hpa)
    rwa [eo] at this
  have hqt : Tendsto (fun m => cayley (e (NyG m ω))) atTop (𝓝[cayley '' C ω] (wallPt (R ω) b)) := by
    have := hNyGt ω (by rw [ec]; exact frontier_subset_closure hpb)
    rwa [ec] at this
  have hωG : ω ∈ G := by
    obtain ⟨ψ, hψ, ψU, hψeq, h0, hinf⟩ :=
      Lemma71F.exists_twoPoint_uniformizer_of_jordan_cayley (hCo ω) (hCc ω) (hCH ω) hJ hpa hpb hpq
    have h0' : Tendsto (fun m => ψ (e (NxG m ω))) atTop (𝓝 0) :=
      (h0.comp hpt).congr fun m => (hψeq _ (hNxGC m ω)).symm
    have hi' : Tendsto (fun m => ‖ψ (e (NyG m ω))‖) atTop atTop :=
      (hinf.comp hqt).congr fun m => by
        show ‖ψU (cayley (e (NyG m ω)))‖ = ‖ψ (e (NyG m ω))‖
        rw [hψeq _ (hNyGC m ω)]
    obtain ⟨p', q', hp', hq', hpq', hx', hy'⟩ := Lemma71E.exists_tendsto_disc_of_tendsto (hCo ω) (hΦ' ω) hψ
      (fun m => hNxGC m ω) (fun m => hNyGC m ω) h0' hi'
    have ex : px ω = p' := hx'.limUnder_eq
    have ey : py ω = q' := hy'.limUnder_eq
    exact ⟨⟨⟨p', hx'⟩, ⟨q', hy'⟩⟩, by rw [ex]; exact hp', by rw [ey]; exact hq', by rw [ex, ey]; exact hpq'⟩
  simp only [hNxin ω hωG, hNyin ω hωG]
  exact ⟨hpt, hqt⟩

end Chart

/-! ### The boundary extension on a marked pocket (deterministic) -/

/-- **The chart's boundary extension on a marked pocket.** Let `C ⊆ ℍ` be open and connected with a marked pocket
configuration `[a, b]` of the wall `R`, let `z m`, `w m` have Cayley images tending to the opening point `α̃ a` and the
closing point `α̃ b`, and let `f` be a map which equals a positive multiple of every conformal `ψ₁ : C → ℍ` with
`ψ₁ (z m) → 0` and `|ψ₁ (w m)| → ∞`. Then `f = Ψ ∘ cayley` on `C` for a map `Ψ` continuous and injective on
`closure (cayley '' C) ∖ {α̃ b}`, with values in `ℍ̄`, `Ψ (α̃ a) = 0`, and `|Ψ| → ∞` at `α̃ b`. -/
theorem exists_ext_of_isMarkedPocket {C : Set ℂ} (hCo : IsOpen C) (hCc : IsConnected C) (hCH : C ⊆ H)
    {R : ℝ≥0 → ℂ} {a b : ℝ} (hM : IsMarkedPocket R C a b) {z w : ℕ → ℂ}
    (hz : Tendsto (fun m => cayley (z m)) atTop (𝓝[cayley '' C] (wallPt R a)))
    (hw : Tendsto (fun m => cayley (w m)) atTop (𝓝[cayley '' C] (wallPt R b))) {f : ℂ → ℂ}
    (huniq : ∀ ψ₁ : ℂ → ℂ, IsConformalBijection ψ₁ C H → Tendsto (fun m => ψ₁ (z m)) atTop (𝓝 0) →
      Tendsto (fun m => ‖ψ₁ (w m)‖) atTop atTop → ∃ a : ℝ, 0 < a ∧ EqOn f (fun x => (a : ℂ) * ψ₁ x) C) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (closure (cayley '' C) \ {wallPt R b}) ∧
      InjOn Ψ (closure (cayley '' C) \ {wallPt R b}) ∧ MapsTo Ψ (closure (cayley '' C) \ {wallPt R b}) Hbar ∧
      Ψ (wallPt R a) = 0 ∧
      Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {wallPt R b}] (wallPt R b)) atTop ∧
      ∀ x ∈ C, f x = Ψ (cayley x) := by
  obtain ⟨-, -, -, -, hJ, hpa, hpb, hpq⟩ := hM
  set D := cayley '' C with hD
  have hDo : IsOpen D := Lemma71F.isOpen_cayley_image hCo hCH
  obtain ⟨Ψ, hΨ, hΨc, hΨi, hΨH, hΨ0, hΨinf⟩ := Lemma71F.exists_twoPoint_uniformizer_ext_of_jordan hDo
    (Lemma71F.isConnected_cayley_image hCc hCH) (Lemma71F.isBounded_cayley_image hCH) hJ hpa hpb hpq
  have hDsub : D ⊆ closure D \ {wallPt R b} := fun x hx =>
    ⟨subset_closure hx, fun hxq => by
      have hxb : x = wallPt R b := mem_singleton_iff.1 hxq
      have hpb' := hpb
      rw [hDo.frontier_eq] at hpb'
      exact hpb'.2 (hxb ▸ hx)⟩
  have hpmem : wallPt R a ∈ closure D \ {wallPt R b} := ⟨frontier_subset_closure hpa, hpq⟩
  have h0 : Tendsto (fun m => (Ψ ∘ cayley) (z m)) atTop (𝓝 0) := by
    rw [← hΨ0]
    exact ((hΨc _ hpmem).tendsto).comp (hz.mono_right (nhdsWithin_mono _ hDsub))
  have hinf : Tendsto (fun m => ‖(Ψ ∘ cayley) (w m)‖) atTop atTop :=
    hΨinf.comp (hw.mono_right (nhdsWithin_mono _ hDsub))
  obtain ⟨l, hl, hEq⟩ := huniq (Ψ ∘ cayley)
    (isConformalBijection_comp hΨ (Lemma71F.isConformalBijection_cayley_image hCH)) h0 hinf
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
  refine ⟨fun x => (l : ℂ) * Ψ x, continuousOn_const.mul hΨc, fun x hx y hy hxy => hΨi hx hy
    (mul_left_cancel₀ hl0 hxy), fun x hx => ?_, by simp only [hΨ0, mul_zero], ?_, fun x hx => hEq hx⟩
  · have h := hΨH hx
    show 0 ≤ ((l : ℂ) * Ψ x).im
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg hl.le h
  · refine (hΨinf.const_mul_atTop hl).congr fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]

/-! ### The canonical pocket chart, a measurable function of the outer curves -/

/-- **Wall pairs**: pairs `(L, R)` of continuous curves from `0` (left wall `L`, right wall `R`), with the σ-algebra
of their coordinates. -/
abbrev WallPair : Type := {x : (ℝ≥0 → ℂ) × (ℝ≥0 → ℂ) // Continuous x.1 ∧ Continuous x.2 ∧ x.1 0 = 0 ∧ x.2 0 = 0}

/-- The wall pair of two curves (the pair `(0, 0)` if they are not continuous curves from `0`). -/
def toWallPair (L R : ℝ≥0 → ℂ) : WallPair :=
  open Classical in
  if h : Continuous L ∧ Continuous R ∧ L 0 = 0 ∧ R 0 = 0 then ⟨(L, R), h⟩
  else ⟨(0, 0), continuous_const, continuous_const, rfl, rfl⟩

theorem toWallPair_eq {L R : ℝ≥0 → ℂ} (h : Continuous L ∧ Continuous R ∧ L 0 = 0 ∧ R 0 = 0) :
    toWallPair L R = ⟨(L, R), h⟩ := by
  classical
  simp only [toWallPair, h, and_self, ↓reduceDIte]

theorem measurable_wallPair_left (t : ℝ≥0) : Measurable fun x : WallPair => x.1.1 t :=
  ((measurable_pi_apply t).comp measurable_fst).comp measurable_subtype_coe

theorem measurable_wallPair_right (t : ℝ≥0) : Measurable fun x : WallPair => x.1.2 t :=
  ((measurable_pi_apply t).comp measurable_snd).comp measurable_subtype_coe

/-- **The wall pair of two random curves is measurable for the σ-algebra of the curves.** -/
theorem measurable_toWallPair {Ω : Type*} {L R : Ω → ℝ≥0 → ℂ}
    (h : ∀ ω, Continuous (L ω) ∧ Continuous (R ω) ∧ L ω 0 = 0 ∧ R ω 0 = 0) :
    Measurable[MeasurableSpace.comap (fun ω => (L ω, R ω)) inferInstance] fun ω => toWallPair (L ω) (R ω) := by
  have e : (fun ω => toWallPair (L ω) (R ω)) = fun ω => (⟨(L ω, R ω), h ω⟩ : WallPair) :=
    funext fun ω => toWallPair_eq (h ω)
  rw [e]
  exact @Measurable.subtype_mk _ _ (MeasurableSpace.comap (fun ω => (L ω, R ω)) inferInstance) _ _ _
    (comap_measurable _) _

/-- **The specification of the canonical pocket chart on wall pairs** `x = (L, R)`: a dense sequence `e`; the pocket
`Cw x` (through the first rational point between the walls; open, connected, simply connected, in `ℍ`) with measurable
closed-ball events and a measurable index `Np x` of a point of it; measurable approach sequences `Nx`, `Ny`; the chart
`cw x` on `Cw x`, conformal onto `ℍ`, with measurable forward map and lift, the lift a continuous branch of `arg ψ′`,
normalized along the approach sequences and unique up to positive scaling with this normalization; on every marked
pocket configuration of the right wall the Cayley images of the approach sequences tend to the marked points. -/
def IsWallPairChart (e : ℕ → ℂ) (Cw : WallPair → Set ℂ) (Np : WallPair → ℕ) (Nx Ny : ℕ → WallPair → ℕ)
    (cw : WallPair → Chart) : Prop :=
  DenseRange e ∧ Measurable Np ∧ (∀ m, Measurable (Nx m)) ∧ (∀ m, Measurable (Ny m)) ∧
    (∀ x, IsOpen (Cw x) ∧ IsConnected (Cw x) ∧ IsSimplyConnected (Cw x) ∧ Cw x ⊆ H) ∧
    (∀ (z : ℂ) (r : ℝ), MeasurableSet {x | closedBall z r ⊆ Cw x}) ∧
    (∀ x, e (Np x) ∈ Cw x) ∧ (∀ m x, e (Nx m x) ∈ Cw x) ∧ (∀ m x, e (Ny m x) ∈ Cw x) ∧
    (∀ x : WallPair, (∃ k, Lemma71Pin.IsBetweenPt (range x.1.2) (range x.1.1) (e k)) →
      Lemma71Pin.IsBetweenPt (range x.1.2) (range x.1.1) (e (Np x)) ∧
        Cw x = connectedComponentIn (H \ closure (range x.1.2 ∪ range x.1.1)) (e (Np x))) ∧
    (∀ x, (cw x).IsConformal) ∧ (∀ x, ((cw x).dom : Set ℂ) = Cw x) ∧
    (∀ x, IsConformalBijection (cw x).1 (Cw x) H) ∧
    (∀ z, Measurable ({x | z ∈ (cw x).dom}.indicator fun x => (cw x).1 z)) ∧
    (∀ z, Measurable ({x | z ∈ (cw x).dom}.indicator fun x => (cw x).2.2 z)) ∧
    (∀ x, ContinuousOn (cw x).2.2 (cw x).dom) ∧
    (∀ x, ∃ L : ℂ → ℂ, IsDerivLog (cw x).1 L (Cw x) ∧ ∀ z ∈ Cw x, (cw x).2.2 z = (L z).im) ∧
    (∀ x, Tendsto (fun m => (cw x).1 (e (Nx m x))) atTop (𝓝 0) ∧
      Tendsto (fun m => ‖(cw x).1 (e (Ny m x))‖) atTop atTop) ∧
    (∀ x (ψ₁ : ℂ → ℂ), IsConformalBijection ψ₁ (Cw x) H → Tendsto (fun m => ψ₁ (e (Nx m x))) atTop (𝓝 0) →
      Tendsto (fun m => ‖ψ₁ (e (Ny m x))‖) atTop atTop →
      ∃ a : ℝ, 0 < a ∧ EqOn (cw x).1 (fun z => (a : ℂ) * ψ₁ z) (Cw x)) ∧
    ∀ x a b, IsMarkedPocket x.1.2 (Cw x) a b →
      Tendsto (fun m => cayley (e (Nx m x))) atTop (𝓝[cayley '' Cw x] (wallPt x.1.2 a)) ∧
      Tendsto (fun m => cayley (e (Ny m x))) atTop (𝓝[cayley '' Cw x] (wallPt x.1.2 b))

/-- **The canonical pocket chart on wall pairs exists.** -/
theorem exists_isWallPairChart :
    ∃ (e : ℕ → ℂ) (Cw : WallPair → Set ℂ) (Np : WallPair → ℕ) (Nx Ny : ℕ → WallPair → ℕ) (cw : WallPair → Chart),
      IsWallPairChart e Cw Np Nx Ny cw := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  obtain ⟨Cw, Np, hNp, hC, hCm, hNpC, hbet⟩ := Lemma71Pin.exists_measurable_pocketDomain
    (R := fun x : WallPair => x.1.2) (L := fun x : WallPair => x.1.1) (fun x => x.2.2.1) (fun x => x.2.1)
    (fun x => x.2.2.2.2) (fun x => x.2.2.2.1) measurable_wallPair_right measurable_wallPair_left he
  obtain ⟨Nx, Ny, cw, hNx, hNy, hNxC, hNyC, hconf, hdom, hbij, -, hfm, hlm, hlc, hL, hnorm, huniq, hmark⟩ :=
    exists_markedPocketChart hC hCm he hNp hNpC (R := fun x : WallPair => x.1.2) (fun x => x.2.2.1)
      measurable_wallPair_right
  exact ⟨e, Cw, Np, Nx, Ny, cw, he, hNp, hNx, hNy, hC, hCm, hNpC, hNxC, hNyC, hbet, hconf, hdom, hbij, hfm, hlm,
    hlc, hL, hnorm, huniq, hmark⟩

/-! ### The pocket chart on a three-curve space -/

section Space

open Lemma71I

variable {κ θ₁ θ₂ a b : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}

/-- **The pocket chart of Lemma 7.1 on a given three-curve space, read off the outer curves.** For a canonical pocket
chart on wall pairs (`IsWallPairChart`), the pocket `C ω = Cw (β ω, α ω)` and the chart `c ω = cw (β ω, α ω)` satisfy,
on every space satisfying `Lemma72B.IsThreeCurveSpace`: `σ(β, α)`-measurable closed-ball events, forward map and lift
(`IsPocketChartData`'s clause (S1)); almost surely `C ω` is a component between the outer curves with
`∂C ∩ ℍ ⊆ β ∪ α` (S2), it is a marked pocket `[a', b']` of the right wall `α`, and the chart is `Ψ ∘ cayley` for a
boundary map `Ψ` continuous and injective on `closure (cayley '' C) ∖ {α̃ b'}` with values in `ℍ̄`, `Ψ = 0` at the
opening point `α̃ a'` and `|Ψ| → ∞` at the closing point `α̃ b'`. (The lift is the canonical one of
`Lemma71E.exists_measurable_twoPointChart`; the inherited branch is a shift by `2πn`, see the handoff.) -/
theorem pocketChart_of_isThreeCurveSpace {e : ℕ → ℂ} {Cw : WallPair → Set ℂ} {Np : WallPair → ℕ}
    {Nx Ny : ℕ → WallPair → ℕ} {cw : WallPair → Chart} (hW : IsWallPairChart e Cw Np Nx Ny cw)
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) :
    Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] (fun ω => toWallPair (β ω) (α ω)) ∧
      (∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
        {ω | closedBall z r ⊆ Cw (toWallPair (β ω) (α ω))}) ∧
      (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
        ({ω | z ∈ (cw (toWallPair (β ω) (α ω))).dom}.indicator fun ω => (cw (toWallPair (β ω) (α ω))).1 z)) ∧
      (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
        ({ω | z ∈ (cw (toWallPair (β ω) (α ω))).dom}.indicator fun ω => (cw (toWallPair (β ω) (α ω))).2.2 z)) ∧
      (∀ᵐ ω ∂P, Cw (toWallPair (β ω) (α ω)) ∈ betweenComponents (range (α ω)) (range (β ω))) ∧
      (∀ᵐ ω ∂P, frontier (Cw (toWallPair (β ω) (α ω))) ∩ H ⊆ range (β ω) ∪ range (α ω)) ∧
      ∀ᵐ ω ∂P, ∃ a' b', IsMarkedPocket (α ω) (Cw (toWallPair (β ω) (α ω))) a' b' ∧
        ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (closure (cayley '' Cw (toWallPair (β ω) (α ω))) \ {wallPt (α ω) b'}) ∧
          InjOn Ψ (closure (cayley '' Cw (toWallPair (β ω) (α ω))) \ {wallPt (α ω) b'}) ∧
          MapsTo Ψ (closure (cayley '' Cw (toWallPair (β ω) (α ω))) \ {wallPt (α ω) b'}) Hbar ∧
          Ψ (wallPt (α ω) a') = 0 ∧
          Tendsto (fun x => ‖Ψ x‖)
            (𝓝[closure (cayley '' Cw (toWallPair (β ω) (α ω))) \ {wallPt (α ω) b'}] (wallPt (α ω) b')) atTop ∧
          ∀ x ∈ Cw (toWallPair (β ω) (α ω)), (cw (toWallPair (β ω) (α ω))).1 x = Ψ (cayley x) := by
  obtain ⟨he, -, -, -, hC, hCm, hNpC, -, -, hbet, -, -, -, hfm, hlm, -, -, -, huniq, hmark⟩ := hW
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, -, hae⟩ := hS
  have hπ : ∀ ω, Continuous (β ω) ∧ Continuous (α ω) ∧ β ω 0 = 0 ∧ α ω 0 = 0 := fun ω =>
    ⟨hβ62.1 ω, hα62.1 ω, hβ62.2.1 ω, hα62.2.1 ω⟩
  have hπm := measurable_toWallPair hπ
  have hπe : ∀ ω, (toWallPair (β ω) (α ω)).1 = (β ω, α ω) := fun ω => by rw [toWallPair_eq (hπ ω)]
  refine ⟨hπm, fun z r => hπm (hCm z r), fun z => (hfm z).comp hπm, fun z => (hlm z).comp hπm, ?_⟩
  -- almost surely the selected domain is the pocket through a between point
  have hgood : ∀ᵐ ω ∂P, IsSimpleProper (α ω) ∧ IsSimpleProper (β ω) ∧
      WangWu.IsOrderedArcs (realPath (α ω)) (realPath (γ ω)) (realPath (β ω)) ∧
      Cw (toWallPair (β ω) (α ω)) =
        connectedComponentIn (H \ (range (α ω) ∪ range (β ω))) (e (Np (toWallPair (β ω) (α ω)))) ∧
      Lemma71Pin.IsBetweenPt (range (α ω)) (range (β ω)) (e (Np (toWallPair (β ω) (α ω)))) := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, -, -, -, -, -, -, hβs, hαs, hγs, hord, hγα, hγβ⟩ := hω
    obtain ⟨t, -, htB⟩ := Lemma71Pin.exists_isBetweenPt_middle hβs hαs hγs hord hγα hγβ
    have hC₀ : connectedComponentIn (H \ (range (α ω) ∪ range (β ω))) (γ ω t) ∈
        betweenComponents (range (α ω)) (range (β ω)) := by
      obtain ⟨hz, hzR, hzL⟩ := (Lemma71Pin.isBetweenPt_iff hαs hβs).1 htB
      exact ⟨γ ω t, hz, hzR, hzL, rfl⟩
    have hC₀o : IsOpen (connectedComponentIn (H \ (range (α ω) ∪ range (β ω))) (γ ω t)) :=
      (QuantumZipper.isOpen_H.sdiff ((Lemma71Pin.IsSimpleProper.isClosed_range hαs).union
        (Lemma71Pin.IsSimpleProper.isClosed_range hβs))).connectedComponentIn
    obtain ⟨k, hk⟩ := he.exists_mem_open hC₀o
      ⟨γ ω t, mem_connectedComponentIn ((Lemma71Pin.isBetweenPt_iff hαs hβs).1 htB).1⟩
    have hbetω := hbet (toWallPair (β ω) (α ω))
    rw [hπe ω] at hbetω
    obtain ⟨hB, hCω⟩ := hbetω ⟨k, Lemma71Pin.isBetweenPt_of_mem hαs hβs hC₀ hk⟩
    have hcl : closure (range (α ω) ∪ range (β ω)) = range (α ω) ∪ range (β ω) :=
      ((Lemma71Pin.IsSimpleProper.isClosed_range hαs).union (Lemma71Pin.IsSimpleProper.isClosed_range hβs)).closure_eq
    rw [hcl] at hCω
    exact ⟨hαs, hβs, hord, hCω, hB⟩
  have hbetw : ∀ᵐ ω ∂P, Cw (toWallPair (β ω) (α ω)) ∈ betweenComponents (range (α ω)) (range (β ω)) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hαs, hβs, -, hCω, hB⟩ := hω
    obtain ⟨hz, hzR, hzL⟩ := (Lemma71Pin.isBetweenPt_iff hαs hβs).1 hB
    rw [hCω]
    exact ⟨_, hz, hzR, hzL, rfl⟩
  refine ⟨hbetw, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω
    obtain ⟨hαs, hβs, -, hCω, -⟩ := hω
    rw [hCω, union_comm (range (β ω))]
    exact Lemma71Pin.frontier_connectedComponentIn_inter_H_subset
      ((Lemma71Pin.IsSimpleProper.isClosed_range hαs).union (Lemma71Pin.IsSimpleProper.isClosed_range hβs)) _
  · filter_upwards [hgood, hbetw] with ω hω hCω
    obtain ⟨hαs, hβs, hord, -, -⟩ := hω
    have hord' : Disjoint (range (β ω)) (rightSideOf (range (α ω))) := by
      have := hord.right_left
      rwa [arcRange_realPath, arcRange_realPath] at this
    obtain ⟨a', b', hM⟩ := isMarkedPocket_of_mem_betweenComponents hαs hβs hord' hCω
    have hM' : IsMarkedPocket (toWallPair (β ω) (α ω)).1.2 (Cw (toWallPair (β ω) (α ω))) a' b' := by
      rw [hπe ω]; exact hM
    obtain ⟨hx, hy⟩ := hmark _ a' b' hM'
    rw [hπe ω] at hx hy
    have hCx := hC (toWallPair (β ω) (α ω))
    exact ⟨a', b', hM, exists_ext_of_isMarkedPocket hCx.1 hCx.2.1 hCx.2.2.2 hM hx hy (huniq _)⟩

end Space

end InteractingSLE.Sec7.Lemma71K
