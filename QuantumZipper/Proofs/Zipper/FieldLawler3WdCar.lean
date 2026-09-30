import QuantumZipper.Proofs.Zipper.FieldLawler3UnifB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-WD (Car): uniformizing a bounded Jordan-type domain, one boundary point to `∞`

`fl3Wd_unif_of_car`: let `D` be a bounded simply connected domain (all complementary components
unbounded) whose frontier lies in a compact ULC set `E ⊆ Dᶜ` such that `E \ {q}` is connected for
every `q` (for a Jordan domain, `E = ∂D`). For every `p ∈ ∂D` there is `Φ`, holomorphic on `ℍ`,
mapping `ℍ` bijectively onto `D`, continuous on `ℍ̄`, mapping `ℝ` bijectively onto `∂D \ {p}`,
with `Φ(z) → p` as `z → ∞` in `ℍ̄`.

**Source.** Riemann mapping theorem (repo `RMT.riemann_mapping_of_hasHoloSqrt`) and
Carathéodory's theorem in the Jordan case (Pommerenke, *Boundary Behaviour of Conformal Maps*,
1992, Thm 2.1 and Thm 2.6, pp. 20–24; repo `CA.Car.continuousOn_extension`,
`CA.Car.isClosedEmbedding_bdryMap`), with the normalization `∞ ↦ p` (`lwHarm_car_normalize`).
The same construction as `fl3u_carHyp` / `fl3u_unif_exists` (FieldLawler3UnifA/B), without the
Möbius transport.

Why `p ↦ ∞` matters: by `fl3Wd_not_FL3Unif_of_bounded` (FieldLawler3WdBdd.lean) a bounded
domain carries no `FL3Unif`; the uniformization of a bounded domain necessarily sends one
boundary point to `∞`.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- **Carathéodory uniformization of a bounded Jordan-type domain with `∞ ↦ p`.** -/
theorem fl3Wd_unif_of_car {D E : Set ℂ} {R₀ : ℝ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hDne : D.Nonempty)
    (hcomp : ∀ a ∉ D, ¬ Bornology.IsBounded (connectedComponentIn Dᶜ a))
    (hDb : D ⊆ ball 0 R₀) (hEc : IsClosed E) (hfr : frontier D ⊆ E) (hEsub : E ⊆ Dᶜ)
    (hEb : E ⊆ closedBall 0 R₀) (hulc : Topo.ULC E) (hE : ∀ q, IsPreconnected (E \ {q}))
    {p : ℂ} (hp : p ∈ frontier D) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ H ∧ BijOn Φ H D ∧ ContinuousOn Φ Hbar ∧
      Function.Injective (fun x : ℝ => Φ x) ∧
      range (fun x : ℝ => Φ x) = frontier D \ {p} ∧
      Tendsto Φ (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 p) := by
  have hDuniv : D ≠ univ := fun h => by
    have := hDb (h ▸ mem_univ (((|R₀| + 1 : ℝ)) : ℂ))
    rw [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at this
    linarith [le_abs_self R₀]
  obtain ⟨-, -, -, ψ₀, hψb, hψd, -⟩ := RMT.riemann_mapping_of_hasHoloSqrt hDo hDc hDne
    hDuniv (RMT.hasHoloSqrt_of_unbounded_compl hDo hDc hcomp)
  have hd1 : DifferentiableOn ℂ (ψ₀ ∘ cayley) H :=
    hψd.comp (differentiableOn_cayley_Hbar.mono H_subset_Hbar) bijOn_cayley_H.mapsTo
  have hG : Car.CarHyp (ψ₀ ∘ cayley) D E R₀ :=
    ⟨hd1, hψb.comp bijOn_cayley_H, hDo, hDb, hEc, hfr, hEsub, hEb⟩
  obtain ⟨ψ₁, F₁, h1, hEq, hF, hInf⟩ := lwHarm_car_normalize hG hulc hp
  obtain ⟨hemb, hrange⟩ := Car.isClosedEmbedding_bdryMap h1 hEq hF hInf hE
  have hne : ∀ x : ℝ, F₁ x ≠ p := fun x h =>
    OnePoint.coe_ne_infty x (hemb.injective
      (show Car.bdryMap F₁ p (x : OnePoint ℝ) = Car.bdryMap F₁ p OnePoint.infty from h))
  refine ⟨F₁, h1.holo.congr fun z hz => hEq hz, h1.bij.congr fun z hz => (hEq hz).symm, hF,
    fun x y h => OnePoint.coe_injective (hemb.injective
      (show Car.bdryMap F₁ p (x : OnePoint ℝ) = Car.bdryMap F₁ p (y : OnePoint ℝ) from h)),
    ?_, fl3u_tendsto_ext_Hbar hEq hF hInf⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨?_, hne x⟩
    rw [← hrange]; exact ⟨(x : OnePoint ℝ), rfl⟩
  · rintro ⟨hz, hzp⟩
    rw [← hrange] at hz
    obtain ⟨o, ho⟩ := hz
    induction o using OnePoint.rec with
    | infty => exact absurd (ho : p = z).symm hzp
    | coe x => exact ⟨x, ho⟩

end FieldLawler
end QuantumZipper
