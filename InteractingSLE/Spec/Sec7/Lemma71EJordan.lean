/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.PrimeEnd.Jordan
import InteractingSLE.Spec.Sec7.Lemma71EChart

/-!
# The two-point uniformizer of a bounded Jordan pocket

Packet PROVE-LEMMA71E, item (3) (PROVE-LEMMA71D's "What remains" C (iii): "existence of the limits from the Jordan
boundary correspondence … the pocket is a Jordan domain by Aux. 33"). Specification §7.1, setup (p. 222): "Let
`ψ : C → ℍ` be a conformal transformation which sends `x₀` to `0` and `y₀` to `∞`"; Remark 6.14 (p. 217): "Its Jordan
boundary homeomorphism".

**`exists_twoPoint_uniformizer_of_jordan`.** For a bounded domain `D` whose frontier is a Jordan curve and two distinct
frontier points `x₀ ≠ y₀`, there is a conformal map `ψ : D → ℍ` with `ψ → 0` at `x₀` and `|ψ| → ∞` at `y₀` (within `D`).
This is the pathwise hypothesis of the measurable chart (`exists_measurable_twoPointChart`) for a bounded pocket.

Proof: the closed-disc Schoenflies–Carathéodory theorem (`Foundations.Schoenflies.schoenflies_disc`) gives `φ`,
continuous and injective on the closed disc, holomorphic inside, with `φ(𝔻) = D` and `φ(∂𝔻) = ∂D`. The inverse
`G = φ⁻¹ : D → 𝔻` tends to `p = φ⁻¹(x₀)` at `x₀`: every cluster point `a` of `G` at `x₀` lies in the closed disc and
satisfies `φ(a) = x₀` (continuity of `φ`), so `a = p` (injectivity), and the closed disc is compact. Likewise at `y₀`
with `q = φ⁻¹(y₀) ≠ p`. Then `ψ = M_{p,q} ∘ G` (`Lemma71EMobius.lean`).

**`exists_measurable_jordanPocketChart`** assembles item (3)'s chart for a random bounded Jordan pocket: measurable
approach sequences of the marked points (`exists_measurable_approach`), the pathwise uniformizer above, and the
measurable two-point chart (`exists_measurable_twoPointChart`), whose forward map then tends to `0` at `x₀` and to `∞`
at `y₀` along the full filters (it is a positive multiple of the pathwise uniformizer).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.Lemma71E

/-- The inverse of a map, continuous and injective on a compact set `K`, tends to the preimage `p ∈ K` of `x`
along any filter `l` (with `l ≤ 𝓝 x`) on which it eventually takes values in `K` and inverts the map. -/
theorem tendsto_inv_of_isCompact {φ G : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (hφc : ContinuousOn φ K)
    (hφi : InjOn φ K) {l : Filter ℂ} {x p : ℂ} (hl : l ≤ 𝓝 x) (hpK : p ∈ K) (hpx : φ p = x)
    (hGK : ∀ᶠ z in l, G z ∈ K) (hφG : ∀ᶠ z in l, φ (G z) = z) : Tendsto G l (𝓝 p) := by
  refine hK.tendsto_nhds_of_unique_mapClusterPt hGK fun a haK ha => ?_
  have h1 : Tendsto φ (𝓝 a ⊓ map G l) (𝓝 (φ a)) := by
    refine (hφc a haK).tendsto.mono_left (le_inf inf_le_left ?_)
    exact inf_le_right.trans (le_principal_iff.2 (mem_map.2 hGK))
  have h2 := ha.tendsto_comp' h1
  have h3 : MapClusterPt (φ a) l id := h2.congrFun (hφG.mono fun z hz => hz)
  have h4 : ClusterPt (φ a) (𝓝 x) := (mapClusterPt_id_iff.1 h3).mono hl
  have h5 : φ a = x := eq_of_nhds_neBot h4.neBot
  exact hφi haK hpK (h5.trans hpx.symm)

/-- **The two-point uniformizer of a bounded Jordan domain.** -/
theorem exists_twoPoint_uniformizer_of_jordan {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier D)) {x₀ y₀ : ℂ}
    (hx : x₀ ∈ frontier D) (hy : y₀ ∈ frontier D) (hxy : x₀ ≠ y₀) :
    ∃ ψ : ℂ → ℂ, IsConformalBijection ψ D H ∧ Tendsto ψ (𝓝[D] x₀) (𝓝 0) ∧
      Tendsto (fun z => ‖ψ z‖) (𝓝[D] y₀) atTop := by
  obtain ⟨p₀, hp₀⟩ := hDc.nonempty
  have hDeq := connectedComponentIn_compl_frontier_eq hDo hDc hp₀
  have hp₀Γ : p₀ ∈ (frontier D)ᶜ := by
    rw [← hDeq] at hp₀
    exact connectedComponentIn_subset _ _ hp₀
  obtain ⟨φ, hφc, hφi, hφd, -, hφball, hφsph⟩ :=
    Foundations.Schoenflies.schoenflies_disc hJ hp₀Γ (by rw [hDeq]; exact hDb)
  rw [hDeq] at hφball
  -- the conformal bijection `φ : 𝔻 → D` and its inverse
  have hφbij : IsConformalBijection φ (ball 0 1) D := by
    refine ⟨hφd, ?_⟩
    rw [← hφball]
    exact (hφi.mono ball_subset_closedBall).bijOn_image
  have hG := isConformalBijection_invFunOn isOpen_ball hφbij
  set G := invFunOn φ (ball (0 : ℂ) 1) with hGdef
  have hGφ : ∀ z ∈ D, φ (G z) = z := fun z hz => invFunOn_eq (hφbij.2.surjOn hz)
  -- the preimages of the marked points
  have hpre : ∀ w ∈ frontier D, ∃ p, ‖p‖ = 1 ∧ φ p = w := fun w hw => by
    rw [← hφsph] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    exact ⟨p, mem_sphere_zero_iff_norm.1 hp, rfl⟩
  obtain ⟨p, hp, hpx⟩ := hpre x₀ hx
  obtain ⟨q, hq, hqy⟩ := hpre y₀ hy
  have hpq : p ≠ q := fun h => hxy (by rw [← hpx, ← hqy, h])
  have hK : ∀ w, ‖w‖ = 1 → w ∈ closedBall (0 : ℂ) 1 := fun w hw => mem_closedBall_zero_iff.2 hw.le
  have hGK : ∀ z ∈ D, G z ∈ closedBall (0 : ℂ) 1 := fun z hz => ball_subset_closedBall (hG.2.mapsTo hz)
  have hlim : ∀ w p, ‖p‖ = 1 → φ p = w → Tendsto G (𝓝[D] w) (𝓝 p) := fun w p hp hpw =>
    tendsto_inv_of_isCompact (isCompact_closedBall 0 1) hφc hφi nhdsWithin_le_nhds (hK p hp) hpw
      (eventually_nhdsWithin_of_forall hGK) (eventually_nhdsWithin_of_forall hGφ)
  refine ⟨bdryMob p q ∘ G, isConformalBijection_comp (isConformalBijection_bdryMob hq) hG,
    (tendsto_bdryMob_left hp hq hpq).comp (hlim x₀ p hp hpx), ?_⟩
  refine (tendsto_norm_bdryMob_right (p := p) hq).comp ?_
  exact tendsto_nhdsWithin_iff.2 ⟨hlim y₀ q hq hqy, eventually_nhdsWithin_of_forall fun z hz => hG.2.mapsTo hz⟩

/-- **The measurable chart of a random bounded Jordan pocket.** For a random bounded Jordan domain `C ω ⊆ ℍ` (open,
connected, simply connected, frontier a Jordan curve) observed through closed balls, with measurable distinct marked
frontier points `x₀ ω ≠ y₀ ω`, there is a random chart, conformal with domain `C ω`, with measurable domain events,
forward map and lift, the lift a continuous branch of `arg ψ′`, and `ψ → 0` at `x₀`, `|ψ| → ∞` at `y₀`. -/
theorem exists_measurable_jordanPocketChart {Ω : Type*} [MeasurableSpace Ω] {C : Ω → Set ℂ}
    (hCo : ∀ ω, IsOpen (C ω)) (hCc : ∀ ω, IsConnected (C ω)) (hCsc : ∀ ω, IsSimplyConnected (C ω))
    (hCH : ∀ ω, C ω ⊆ H) (hCb : ∀ ω, Bornology.IsBounded (C ω))
    (hJ : ∀ ω, LQGMetric.JordanMap.IsJordanCurve (frontier (C ω)))
    (hCm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ C ω}) {x₀ y₀ : Ω → ℂ}
    (hx : Measurable x₀) (hy : Measurable y₀) (hxC : ∀ ω, x₀ ω ∈ frontier (C ω))
    (hyC : ∀ ω, y₀ ω ∈ frontier (C ω)) (hxy : ∀ ω, x₀ ω ≠ y₀ ω) :
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = C ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (C ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (L z).im) ∧
      (∀ ω, Tendsto (c ω).1 (𝓝[C ω] (x₀ ω)) (𝓝 0) ∧ Tendsto (fun z => ‖(c ω).1 z‖) (𝓝[C ω] (y₀ ω)) atTop) := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hmem := measurableSet_mem_of_closedBall hCo hCm
  have hcl : ∀ ω w, w ∈ frontier (C ω) → w ∈ closure (C ω) := fun ω w hw => frontier_subset_closure hw
  obtain ⟨Nx, hNx, hNxC, hNxt⟩ := exists_measurable_approach hCo hmem he hx fun ω => hcl ω _ (hxC ω)
  obtain ⟨Ny, hNy, hNyC, hNyt⟩ := exists_measurable_approach hCo hmem he hy fun ω => hcl ω _ (hyC ω)
  have hψ : ∀ ω, ∃ ψ : ℂ → ℂ, IsConformalBijection ψ (C ω) H ∧ Tendsto ψ (𝓝[C ω] (x₀ ω)) (𝓝 0) ∧
      Tendsto (fun z => ‖ψ z‖) (𝓝[C ω] (y₀ ω)) atTop := fun ω =>
    exists_twoPoint_uniformizer_of_jordan (hCo ω) (hCc ω) (hCb ω) (hJ ω) (hxC ω) (hyC ω) (hxy ω)
  obtain ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, -, huniq⟩ :=
    exists_measurable_twoPointChart hCo hCc hCsc hCH hCm he hNx hNy hNxC hNyC fun ω => by
      obtain ⟨ψ, hψc, h0, hi⟩ := hψ ω
      exact ⟨ψ, hψc, h0.comp (hNxt ω), hi.comp (hNyt ω)⟩
  refine ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, fun ω => ?_⟩
  obtain ⟨ψ, hψc, h0, hi⟩ := hψ ω
  obtain ⟨a, ha, hEq⟩ := huniq ω ψ hψc (h0.comp (hNxt ω)) (hi.comp (hNyt ω))
  have hev : ∀ w, ∀ᶠ z in 𝓝[C ω] w, (c ω).1 z = (a : ℂ) * ψ z := fun w =>
    eventually_nhdsWithin_of_forall fun z hz => hEq hz
  refine ⟨?_, ?_⟩
  · have := h0.const_mul (a : ℂ)
    rw [mul_zero] at this
    exact this.congr' (EventuallyEq.symm (hev _))
  · have h1 : Tendsto (fun z => a * ‖ψ z‖) (𝓝[C ω] (y₀ ω)) atTop := hi.const_mul_atTop ha
    refine h1.congr' ((hev _).mono fun z hz => ?_)
    show a * ‖ψ z‖ = ‖(c ω).1 z‖
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

end InteractingSLE.Sec7.Lemma71E
