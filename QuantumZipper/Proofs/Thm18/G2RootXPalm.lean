import QuantumZipper.Proofs.Thm18.G2RootXCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2, `x` side, cut form: the Palm identity and the zoom at a fixed point

`G2RootXCutStmt γ μ` (`G2RootXCut.lean`) is Proposition 1.6 at the rooted point `x` with the
field outside the two regions and the cut length `ν_h[x + κ, 0]` frozen. Following Sheffield
(arXiv:1012.4797, proof of Prop. 5.5, p. 65: "once we condition on `x`, the conditional law of
`h` is that of a zero boundary GFF … plus a random harmonic function plus `−γ log|x − ·|`") and
Duplantier–Sheffield (arXiv:0808.1560, §3.3, the rooted measure), it splits into

* `G2RootXPalmIdStmt γ` — **the Palm identity** for the rooted measure of Theorem 1.2's field
  `h = 𝔥₀ + X − X(S)` (`normField`): with `ψ_x = (γ/2)(neumannH x · − k_S)` and the Palm density
  `ρ(x) = rhoNorm γ 𝔥₀ S x` (as in `PalmNorm.palm_formula_norm`),
  `E ∫_{[−δ,0]} 1_A(h, x) ν_h(dx) = ∫_{[−δ,0]} ρ(x) P(A at the shifted field X + ψ_x) dx`,
  for the events `A` of the node (with the outside field read through its coordinates, Doob–Dynkin
  `exists_outsideSigmaPalm_preimage`), together with a.e.-measurability of the right-hand
  integrand;
* `G2RootXFixStmt γ μ` — **the conditional zoom at a fixed point `x`** of the Palm-shifted field
  (D3⁺(i) at `x` with the field outside `B_κ(x)` frozen, plus the identification of the global
  canonical zoom with D3⁺'s local model, as in `Prop17PalmCAgreeStmt`).

This file holds the objects, the Doob–Dynkin step and the two statements; the assembly
(integration over `x`, uniformly in the outside event) is in `G2RootXPalmAsm.lean`.
Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-! ## The outside field as a coordinate map (Doob–Dynkin) -/

/-- The coordinates of the field outside the two regions: balanced increments `y p₁ − y p₂`. -/
def outMap (i : G3Idx) (y : FieldSample) : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ :=
  fun p => y p.1.1 - y p.1.2

theorem outsideSigma2_eq_comap {Ω : Type*} (X : Ω → FieldSample) (t₁ r₁ t₂ r₂ : ℝ) :
    outsideSigma2 X t₁ r₁ t₂ r₂ = MeasurableSpace.comap
      (fun ω (p : OutIdx2 t₁ r₁ t₂ r₂) => X ω p.1.1 - X ω p.1.2) MeasurableSpace.pi := by
  rw [outsideSigma2, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

/-- **Doob–Dynkin for the conditioning σ-algebra**: every `outsideSigmaPalm`-measurable event is
the preimage of a measurable set under `(ω, ℓ) ↦ (outside coordinates of X ω, ℓ)`. -/
theorem exists_outsideSigmaPalm_preimage (i : G3Idx) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G) :
    ∃ G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G' ∧
      G = {q | (outMap i (X₀ q.1), q.2) ∈ G'} := by
  have e : outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂ =
      MeasurableSpace.comap (fun q : Ω₀ × ℝ => (outMap i (X₀ q.1), q.2))
        (inferInstance : MeasurableSpace ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)) := by
    rw [outsideSigmaPalm, outsideSigma2_eq_comap]
    show _ = MeasurableSpace.comap _ (MeasurableSpace.comap Prod.fst MeasurableSpace.pi ⊔
      MeasurableSpace.comap Prod.snd _)
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp,
      MeasurableSpace.comap_comp]
    rfl
  rw [e] at hG
  obtain ⟨G', hG', rfl⟩ := hG
  exact ⟨G', hG', rfl⟩

/-! ## The Palm-shifted field -/

/-- The Cameron–Martin shift of the Palm field at `x`: `ψ_x = (γ/2)(neumannH x · − k_S)`
(`PalmNorm.shiftFun` without the mean). -/
def g2PalmPsi (γ x : ℝ) (u : ℂ) : ℝ := γ / 2 * (neumannH (x : ℂ) u - PalmNorm.kPot refS u)

/-- The free field shifted by `ψ_x`. -/
def xPalm (γ x : ℝ) (ω : Ω₀) : FieldSample := X₀ ω + ofFun (g2PalmPsi γ x)

/-- The Palm density of the rooted measure of `normField`: `ρ(x) = rhoNorm γ 𝔥₀ S x`. -/
def rhoX (γ x : ℝ) : ℝ := PalmNorm.rhoNorm γ (h0rev (γ ^ 2)) refS x

/-- The shifted event at a fixed point `x`: `{zoom at x ∈ s, x a margin m inside region 1,
(outside coordinates, ν_h[x+κ, 0]) ∈ G'}`, for the Palm field `h = normField (X + ψ_x)`. -/
def g3RootXPalmEv (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ)
    (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)) (x : ℝ) : Set Ω₀ :=
  {ω | zoomLaw γ i.C (normField γ (xPalm γ x) ω) x ∈ s ∧ |x - i.t₁| + m < i.r₁ ∧
    (outMap i (xPalm γ x ω),
      (qBoundaryMeasure γ (normField γ (xPalm γ x) ω) (Icc (x + κ) 0)).toReal) ∈ G'}

/-- The pulled-back outside event. -/
def outEv (i : G3Idx) (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)) : Set (Ω₀ × ℝ) :=
  {q | (outMap i (X₀ q.1), q.2) ∈ G'}

/-! ## The two nodes -/

/-- **Node P (Palm identity for the rooted measure of `normField`; Duplantier–Sheffield,
arXiv:0808.1560, §3.3; normalized form `PalmNorm.palm_formula_norm`/`palm_formula_norm_local`,
`𝔥₀ = h0rev (γ²)` being continuous on the margin window, away from `0`).** For the events of the
cut node, the rooted measure `E ∫_{[−δ,0]} · ν_h(dx)` equals `∫_{[−δ,0]} ρ(x) P(shifted event) dx`,
and the right-hand integrand is a.e.-measurable. -/
def G2RootXPalmIdStmt (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (s : Set LawD), MeasurableSet s → ∀ m κ : ℝ, 0 < m → 0 < κ →
    ∀ G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G' →
      g3RootInt γ i ((g3RootEvXc γ i s m κ (outEv i G')).indicator 1) =
        ∫⁻ x in Icc (-i.δ) 0, ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEv γ i s m κ G' x) ∧
      AEMeasurable (fun x => ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEv γ i s m κ G' x))
        (volume.restrict (Icc (-i.δ) 0))

/-- **Node F (conditional zoom at a fixed point; Sheffield, arXiv:1012.4797, Prop. 1.6 and
proof of Prop. 5.5, pp. 24–25, 65; D3⁺(i) at `x` with the field outside `B_κ(x)` frozen).**
For every fixed `x` (a margin `m > κ` inside region 1), the zoom at `x` of the Palm field
`normField (X + ψ_x)` is asymptotically independent, as `C → ∞` and uniformly in `G'`, of the
outside coordinates and the cut length `ν_h[x + κ, 0]`, with limit law `μ`. -/
def G2RootXFixStmt (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ x : ℝ, ∀ ε > 0,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G' →
        |(gffBase.P (g3RootXPalmEv γ i s m κ G' x)).toReal -
          μ.real s * (gffBase.P (g3RootXPalmEv γ i univ m κ G' x)).toReal| ≤ ε

end Thm18Asm
end QuantumZipper
