/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71EDisc
import InteractingSLE.GFF.Pushforward

/-!
# The measurable two-point normalized pocket chart

Packet PROVE-LEMMA71E, item (3) (PROVE-LEMMA71D's "What remains" C (ii)–(v)). Specification §7.1, setup (p. 222): "Let
`ψ : C → ℍ` be a conformal transformation which sends `x₀` to `0` and `y₀` to `∞` (the scale factor can be determined
by an arbitrary rule …)"; Lemma 7.1's consumers ask for the chart `c ω = (ψ, ψ⁻¹, lift)` with `𝓐₀`-measurable domain
events, forward map and lift (`Lemma71D.Lemma71PocketCurveConstStatement`).

**Setting.** A random open, connected, simply connected `C ω ⊆ ℍ` observed through closed balls (the events
`{closedBall c r ⊆ C ω}` are measurable), a dense sequence `e`, and the two marked boundary points given by
measurable approach sequences `e (Nx m ω) → x₀`, `e (Ny m ω) → y₀` inside `C ω`, such that **some** conformal
`ψ₁ : C ω → ℍ` tends to `0` along the first and to `∞` along the second (pathwise; for a Jordan pocket this is the
boundary correspondence).

**Construction** (`exists_measurable_twoPointChart`). `Φ ω : C ω → 𝔻` the normalized disc chart at the first point
of `e` in `C ω` (`exists_measurable_discPair`); `p ω`, `q ω` the limits of `Φ ω` along the two approach sequences
(distinct points of the circle, `exists_tendsto_disc_of_tendsto`); the forward map `ψ = M_{p,q} ∘ Φ`
(`Lemma71EMobius.lean`); the inverse `ψ⁻¹ = invFunOn ψ (C ω)`; the lift `Im (log M′_{p,q} ∘ Φ − log F′ ∘ Φ)` with
`F = Φ⁻¹` (`discLog`), the branch of `arg ψ′` fixed by `arg F′(0) = 0`.

**Conclusions.** The chart is conformal with domain `C ω`, its domain events, forward map and lift are measurable,
the lift is a continuous branch of `arg ψ′`, `ψ → 0` and `|ψ| → ∞` along the approach sequences, and every other
conformal `ψ₁ : C ω → ℍ` with this normalization is a positive multiple of `ψ` (so every boundary property of the
pathwise map `ψ₁` transfers to the measurable one). The inherited branch of the specification differs from this
branch by a constant `2πn(ω)`, with `n` measurable as soon as the inherited branch is measurable at one point
(`shiftLift`, `measurable_indicator_shiftLift`, `measurable_int_of_eq_add`).

## Main results

* **`exists_measurable_twoPointChart`**;
* `shiftLift`, `measurable_indicator_shiftLift`, `continuousOn_shiftLift`;
* `exists_int_eq_lift_add`: any continuous branch of `arg ψ′` is the chart lift plus `2πn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped ComplexOrder

namespace InteractingSLE.Sec7.Lemma71E

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The measurable two-point normalized pocket chart.** See the module docstring. -/
theorem exists_measurable_twoPointChart {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω))
    (hCc : ∀ ω, IsConnected (C ω)) (hCsc : ∀ ω, IsSimplyConnected (C ω)) (hCH : ∀ ω, C ω ⊆ H)
    (hCm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ C ω}) {e : ℕ → ℂ} (he : DenseRange e)
    {Nx Ny : ℕ → Ω → ℕ} (hNx : ∀ m, Measurable (Nx m)) (hNy : ∀ m, Measurable (Ny m))
    (hNxC : ∀ m ω, e (Nx m ω) ∈ C ω) (hNyC : ∀ m ω, e (Ny m ω) ∈ C ω)
    (hψ₁ : ∀ ω, ∃ ψ₁ : ℂ → ℂ, IsConformalBijection ψ₁ (C ω) H ∧
      Tendsto (fun m => ψ₁ (e (Nx m ω))) atTop (𝓝 0) ∧ Tendsto (fun m => ‖ψ₁ (e (Ny m ω))‖) atTop atTop) :
    ∃ c : Ω → Chart,
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
        ∃ a : ℝ, 0 < a ∧ EqOn (c ω).1 (fun z => (a : ℂ) * ψ₁ z) (C ω)) := by
  obtain ⟨Φ, F, a, -, hΦ, hΦ0, hΦm, hF, hFm, hΦF⟩ := exists_measurable_discPair hCo hCc hCsc hCH hCm he
  have hmem := measurableSet_mem_of_closedBall hCo hCm
  -- the boundary values of the disc chart
  set p : Ω → ℂ := fun ω => limUnder atTop fun m => Φ ω (e (Nx m ω)) with hpdef
  set q : Ω → ℂ := fun ω => limUnder atTop fun m => Φ ω (e (Ny m ω)) with hqdef
  have hΦe : Measurable fun x : Ω × ℕ => Φ x.1 (e x.2) :=
    measurable_from_prod_countable_left fun j => hΦm (e j)
  have hpm : Measurable p := (StronglyMeasurable.limUnder fun m =>
    (hΦe.comp (measurable_id.prodMk (hNx m))).stronglyMeasurable).measurable
  have hqm : Measurable q := (StronglyMeasurable.limUnder fun m =>
    (hΦe.comp (measurable_id.prodMk (hNy m))).stronglyMeasurable).measurable
  have hbd : ∀ ω, ‖p ω‖ = 1 ∧ ‖q ω‖ = 1 ∧ p ω ≠ q ω ∧
      Tendsto (fun m => Φ ω (e (Nx m ω))) atTop (𝓝 (p ω)) ∧
      Tendsto (fun m => Φ ω (e (Ny m ω))) atTop (𝓝 (q ω)) := by
    intro ω
    obtain ⟨ψ₁, h₁, h0, hi⟩ := hψ₁ ω
    obtain ⟨p', q', hp', hq', hpq', hx, hy⟩ := exists_tendsto_disc_of_tendsto (hCo ω) (hΦ ω).1 h₁
      (fun m => hNxC m ω) (fun m => hNyC m ω) h0 hi
    have ep : p ω = p' := hx.limUnder_eq
    have eq : q ω = q' := hy.limUnder_eq
    rw [ep, eq]
    exact ⟨hp', hq', hpq', hx, hy⟩
  -- the chart
  set fwd : Ω → ℂ → ℂ := fun ω z => bdryMob (p ω) (q ω) (Φ ω z) with hfwddef
  set lift : Ω → ℂ → ℝ := fun ω z => (bdryMobLog (q ω) (Φ ω z) - discLog (F ω) (Φ ω z)).im with hliftdef
  set c : Ω → Chart := fun ω => (fwd ω, invFunOn (fwd ω) (C ω), lift ω) with hcdef
  have hfwd : ∀ ω, IsConformalBijection (fwd ω) (C ω) H := fun ω =>
    isConformalBijection_comp (isConformalBijection_bdryMob (p := p ω) (hbd ω).2.1) (hΦ ω).1
  have hinv : ∀ ω, IsConformalBijection (invFunOn (fwd ω) (C ω)) H (C ω) := fun ω =>
    isConformalBijection_invFunOn (hCo ω) (hfwd ω)
  have hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω := by
    intro ω
    show interior (invFunOn (fwd ω) (C ω) '' H) = C ω
    rw [(hinv ω).2.image_eq, (hCo ω).interior_eq]
  have hdomset : ∀ z, {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω
    show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
    rw [hdom ω]
  have hΦball : ∀ ω z, Φ ω z ∈ ball (0 : ℂ) 1 := by
    intro ω z
    by_cases hz : z ∈ C ω
    · exact (hΦ ω).1.2.mapsTo hz
    · rw [hΦ0 ω z hz]
      exact mem_ball_self one_pos
  have hΦcont : ∀ ω, ContinuousOn (Φ ω) (C ω) := fun ω => (hΦ ω).1.1.continuousOn
  have hFlog : ∀ ω, IsDerivLog (F ω) (discLog (F ω)) (ball 0 1) := fun ω =>
    isDerivLog_discLog (hF ω).1 (hF ω).2.2
  -- the derivative lift of the forward map
  have hlog : ∀ ω, IsDerivLog (fwd ω) (fun z => bdryMobLog (q ω) (Φ ω z) + -discLog (F ω) (Φ ω z)) (C ω) := by
    intro ω
    have h1 := IsDerivLog.invFunOn isOpen_ball (hF ω).1 (hFlog ω)
    have h2 : IsDerivLog (Φ ω) (fun z => -discLog (F ω) (Φ ω z)) (C ω) :=
      IsDerivLog.congr_of_eqOn (hCo ω) h1 (hΦF ω).symm fun z hz => by
        show -discLog (F ω) (invFunOn (F ω) (ball 0 1) z) = -discLog (F ω) (Φ ω z)
        rw [hΦF ω hz]
    exact IsDerivLog.comp (hCo ω) isOpen_ball (isConformalBijection_bdryMob (p := p ω) (hbd ω).2.1).1
      (hΦ ω).1.1 (hΦ ω).1.2.mapsTo (isDerivLog_bdryMob (hbd ω).2.1) h2
  refine ⟨c, fun ω => ⟨(hinv ω).1, fun w hw => hCH ω ((hinv ω).2.mapsTo hw), fun w hw => ?_⟩, hdom, hfwd,
    fun z => ?_, fun z => ?_, fun z => ?_, fun ω => ?_, fun ω => ⟨_, hlog ω, fun z _ => ?_⟩, fun ω => ?_,
    fun ω ψ₁ h₁ h0 hi => ?_⟩
  · exact invFunOn_eq ((hfwd ω).2.surjOn hw)
  · rw [hdomset z]
    exact hmem z
  · rw [hdomset z]
    exact (measurable_bdryMob.comp (hpm.prodMk (hqm.prodMk (hΦm z)))).indicator (hmem z)
  · rw [hdomset z]
    exact (Complex.measurable_im.comp ((measurable_bdryMobLog.comp (hqm.prodMk (hΦm z))).sub
      (measurable_discLog_comp (fun ω => (hF ω).1.1) hFm (hΦm z) fun ω => hΦball ω z))).indicator (hmem z)
  · rw [show ((c ω).dom : Set ℂ) = C ω from hdom ω]
    exact Complex.continuous_im.comp_continuousOn
      (((continuousOn_bdryMobLog (hbd ω).2.1).comp (hΦcont ω) (hΦ ω).1.2.mapsTo).sub
        ((hFlog ω).1.continuousOn.comp (hΦcont ω) (hΦ ω).1.2.mapsTo))
  · show (bdryMobLog (q ω) (Φ ω z) - discLog (F ω) (Φ ω z)).im = _
    rw [sub_eq_add_neg]
  · obtain ⟨hp, hq, hpq, hx, hy⟩ := hbd ω
    refine ⟨(tendsto_bdryMob_left hp hq hpq).comp hx, (tendsto_norm_bdryMob_right (p := p ω) hq).comp ?_⟩
    exact tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall fun m => (hΦ ω).1.2.mapsTo (hNyC m ω)⟩
  · obtain ⟨hp, hq, hpq, hx, hy⟩ := hbd ω
    refine exists_pos_eqOn_mul_of_tendsto (hCo ω) h₁ (hfwd ω) (fun m => hNxC m ω) (fun m => hNyC m ω) h0
      ((tendsto_bdryMob_left hp hq hpq).comp hx) hi ((tendsto_norm_bdryMob_right (p := p ω) hq).comp ?_)
    exact tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall fun m => (hΦ ω).1.2.mapsTo (hNyC m ω)⟩

/-! ### The inherited branch: shifting the lift by `2πn` -/

/-- The chart `c` with its lift shifted by `2πn`. -/
def shiftLift (c : Chart) (n : ℤ) : Chart := (c.1, c.2.1, fun z => c.2.2 z + 2 * Real.pi * n)

omit [MeasurableSpace Ω] in
theorem shiftLift_dom (c : Chart) (n : ℤ) : (shiftLift c n).dom = c.dom := rfl

omit [MeasurableSpace Ω] in
theorem isConformal_shiftLift {c : Chart} (hc : c.IsConformal) (n : ℤ) : (shiftLift c n).IsConformal := hc

omit [MeasurableSpace Ω] in
theorem continuousOn_shiftLift {c : Chart} (hc : ContinuousOn c.2.2 c.dom) (n : ℤ) :
    ContinuousOn (shiftLift c n).2.2 (shiftLift c n).dom :=
  hc.add continuousOn_const

/-- Shifting the lift of a measurable random chart by a measurable integer keeps it measurable. -/
theorem measurable_indicator_shiftLift {c : Ω → Chart} {n : Ω → ℤ} (hn : Measurable n) (z : ℂ)
    (hdom : MeasurableSet {ω | z ∈ (c ω).dom})
    (hlift : Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) :
    Measurable ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator fun ω => (shiftLift (c ω) (n ω)).2.2 z) := by
  show Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z + 2 * Real.pi * (n ω : ℝ))
  rw [show (fun ω => (c ω).2.2 z + 2 * Real.pi * (n ω : ℝ)) =
    (fun ω => (c ω).2.2 z) + (fun ω => 2 * Real.pi * (n ω : ℝ)) from rfl, indicator_add']
  refine hlift.add (Measurable.indicator ?_ hdom)
  exact measurable_const.mul ((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp hn)

omit [MeasurableSpace Ω] in
/-- **Two continuous branches of `arg ψ′` on a connected domain differ by `2πn`.** -/
theorem exists_int_eq_lift_add {ψ L L' : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hL : IsDerivLog ψ L D) (hL' : IsDerivLog ψ L' D) :
    ∃ n : ℤ, ∀ z ∈ D, (L' z).im = (L z).im + 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := hL'.exists_int_eqOn hDo hDc hL
  refine ⟨n, fun z hz => ?_⟩
  rw [hn hz]
  simp [mul_comm, mul_left_comm]

/-- The integer by which a measurable branch differs from a measurable lift is measurable. -/
theorem measurable_int_of_eq_add {f g : Ω → ℝ} {n : Ω → ℤ} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ ω, f ω = g ω + 2 * Real.pi * n ω) : Measurable n := by
  have heq : n = fun ω => ⌊(f ω - g ω) / (2 * Real.pi)⌋ := by
    funext ω
    rw [h ω, add_sub_cancel_left, mul_div_cancel_left₀ _ (by positivity), Int.floor_intCast]
  rw [heq]
  exact Int.measurable_floor.comp ((hf.sub hg).div_const _)

end InteractingSLE.Sec7.Lemma71E
