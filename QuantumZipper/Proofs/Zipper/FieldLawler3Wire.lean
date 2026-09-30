import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopArc
import QuantumZipper.Proofs.Zipper.FieldLawler2Max
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo
import QuantumZipper.Proofs.Thm18.LWExc3Circle
import QuantumZipper.Proofs.Thm18.LWExcUpper

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-WIRE: moving harmonic measures between `ℍ` and `H_t` (Track A wiring)

Task FL3-WIRE, towards `FieldLawler.FLImageSumBoundStmt` (`FieldLawlerSubSum.lean`).

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015)
no. 10, arXiv:1407.3314, proof of Prop. 3.4 (p. 9) and (2.1): the chain
`ℰ_ℍ(Z_t ηⱼ, ℝ∓) ≤ … = ℰ_{H_t}(ηⱼ, γ̃)` is "conformal invariance" of harmonic measure under
`Z_t : H_t → ℍ`. FL state it without proof; the argument here is the standard one (composition
of a harmonic function with a holomorphic map is harmonic, plus the maximum principle), with the
boundary correspondence given by the Carathéodory extension `F` of `Z_t⁻¹` to `ℍ̄` (Pommerenke,
*Boundary Behaviour of Conformal Maps*, Thm 2.1/2.6; in the repository `SideCtx`, built from the
hypotheses of `FLImageSumBoundStmt` by `flTop_ctx`). Own elementary argument for the implicit
step "by conformal invariance" (logged as such).

With `D = ℍ \ K_t`, `Z = fwdMap W t` and `Ω = flPull W t U = D ∩ Z⁻¹ U`:
* (W-a) `flWire_harm_comp`: `f` harmonic on `V` ⇒ `f ∘ Z` harmonic on `D ∩ Z⁻¹ V`
  (`flPull_eq_image`: this set is `Z⁻¹ '' V = fwdMapInv W t '' V` for `V ⊆ ℍ`).
* (W-b) `flWire_tendsto_zero_rough`: for `IsHarmMeas U A f`, `U ⊆ ℍ`, at a point `x₀ ∉ D` (a hull
  or real boundary point) none of whose prime-end preimages `u ∈ ℝ` (`F u = x₀`) lies in
  `closure A`, `f (Z z) → 0` as `z → x₀` in `Ω`.
* (W-c) `flWire_pullback_le`: `f ∘ Z ≤ M` on `Ω` for every harmonic `M ≥ 0` on `Ω` that tends to
  `≥ 1` at the points of `D` mapped into `closure A`; exceptional finite set `E ⊇ F(closure A ∩ ℝ)`
  (the feet of the arcs), via `fl2_harm_le_zero_off_finite`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- The pullback `D ∩ Z⁻¹ U` of an image-side set `U` to the Loewner side `D = ℍ \ K_t`. -/
def flPull (W : ℝ → ℝ) (t : ℝ) (U : Set ℂ) : Set ℂ := (H \ fwdHull W t) ∩ fwdMap W t ⁻¹' U

/-- **(W-a)** Pullback of an image-side harmonic function is harmonic. -/
theorem flWire_harm_comp (hc : SideCtx W t F) {V : Set ℂ} {f : ℂ → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f V) :
    InnerProductSpace.HarmonicOnNhd (fun z => f (fwdMap W t z)) (flPull W t V) := by
  intro z hz
  have hA : AnalyticAt ℂ (fwdMap W t) z :=
    (FwdHolo.differentiableOn_fwdMap hc.cont hc.tpos.le).analyticAt
      (hc.isOpen_dom.mem_nhds hz.1)
  exact fl_harmonicAt_comp (h := f) hA (hf _ hz.2)

/-- `‖z - Z z‖ ≤ C` on `D` (hydrodynamic normalization, from `SideCtx.bound`). -/
lemma flWire_norm_le (hc : SideCtx W t F) {C : ℝ} (hC : ∀ u ∈ H, ‖F u - u‖ ≤ C) {z : ℂ}
    (hz : z ∈ H \ fwdHull W t) : ‖fwdMap W t z‖ ≤ ‖z‖ + C ∧ ‖z‖ ≤ ‖fwdMap W t z‖ + C := by
  have h1 := hC _ (hc.mapsTo hz)
  rw [hc.F_fwdMap hz] at h1
  have e1 : ‖fwdMap W t z‖ ≤ ‖z‖ + ‖z - fwdMap W t z‖ := by
    simpa using norm_sub_le z (z - fwdMap W t z)
  have e2 : ‖z‖ ≤ ‖fwdMap W t z‖ + ‖z - fwdMap W t z‖ := by
    simpa using norm_add_le (fwdMap W t z) (z - fwdMap W t z)
  constructor <;> linarith

/-- From a limit `0` of `φ` to the `ε`–`δ` form of `fl2_harm_le_zero_off_finite` for `φ - M`,
`M ≥ 0`. -/
lemma flWire_delta {Ω : Set ℂ} {x₀ : ℂ} {φ M : ℂ → ℝ} (h : Tendsto φ (𝓝[Ω] x₀) (𝓝 0))
    (hM0 : ∀ y ∈ Ω, 0 ≤ M y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Ω, dist y x₀ < δ → φ y - M y ≤ ε := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (h.eventually (gt_mem_nhds hε))
  refine ⟨δ, hδ, fun y hy hyd => ?_⟩
  have h1 : φ y < ε := hsub ⟨mem_ball.2 hyd, hy⟩
  have h2 := hM0 y hy
  linarith

/-- The context `SideCtx` from the hypotheses of `FLImageSumBoundStmt` (`t > 0` because the tip
has norm `R > 0` while `trace W 0 = 0`). -/
theorem flWire_ctx (hW : Continuous W) (hW0 : W 0 = 0) {R : ℝ} (ht : 0 ≤ t) (hR : 0 < R)
    (h0 : trace W 0 = 0) (hcont : ContinuousOn (trace W) (Icc 0 t))
    (hinj : InjOn (trace W) (Icc 0 t)) (hH : ∀ s ∈ Ioc 0 t, trace W s ∈ H)
    (hhull : fwdHull W t = trace W '' Ioc 0 t) (htip : ‖trace W t‖ = R) :
    ∃ F : ℂ → ℂ, SideCtx W t F := by
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · rw [← h, h0, norm_zero] at htip
      linarith
  obtain ⟨F, hF, -⟩ := flTop_ctx hW hW0 htpos h0 hcont hinj hH hhull
  exact ⟨F, hF⟩

end FieldLawler
end QuantumZipper
