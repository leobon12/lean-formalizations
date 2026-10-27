# Harmonic functions on mated-CRT maps

**Status.** The seven frozen theorems of this formalization are proved, **conditional on a mating-of-trees input
bundle**: each is stated for every family of random objects that satisfies the frozen hypothesis
`MatedCRT.IsMatingOfTreesCoupling γ P …`, that is, for every witness of `MatedCRT.MatingOfTreesInput γ` (described
below). Each main theorem's statement is the frozen statement of the development, checked by an independent
statement audit. Its proof is machine-checked with only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) and was replayed by a fresh `leanchecker` run on 2026-10-27.

This Lean 4 project formalizes the main results of Ewain Gwynne, Jason Miller and Scott Sheffield, *Harmonic functions
on mated-CRT maps*, [arXiv:1807.07511v3](https://arxiv.org/abs/1807.07511v3) (PDF SHA-256
`068650f602eb171ddb2e26ac3716a9179c4192bbfb3f46917c121a7973e1aea4`). Line numbers "l. N" below are lines of the
plain-text extraction of that PDF produced by `pdftotext -layout`
(poppler 24.02.0; SHA-256 `83c0d9807516d273ef3eda624d5084cb7a4c103907d63e12694ec37a3c415a10`). It is not included
here, but that command reproduces it. Section, theorem and equation numbers are given as well. "The paper" below means
arXiv:1807.07511v3.

In words: fix γ ∈ (0, 2) and κ′ = 16/γ². Let h be a γ-quantum cone and η an independent whole-plane space-filling
SLE_κ′ from ∞ to ∞, parametrized by the γ-LQG area of h with η(0) = 0. For ε > 0 the cells H^ε_x = η([x − ε, x]),
x ∈ εℤ, form the ε-mated-CRT map G^ε, embedded in ℂ by x ↦ η(x). Fix ρ ∈ (0, 1), a domain D ⊂ B_ρ(0) and boundary
data f, and let f^ε be the function on the vertices whose cells meet D that equals sup_{H^ε_x ∩ ∂D} f when the cell of
x meets ∂D and is discrete harmonic otherwise. Then:
- **Theorems 3.2 and 1.3.** With probability 1 − O_ε(ε^α), the discrete Dirichlet energy of f^ε is at most A times the
  Dirichlet energy of f (plus ε^α in Theorem 3.2), for domains with bounded convexity and `area(B_r(∂D)) ≤ C r`.
- **Theorem 1.4.** With probability 1 − O_ε(ε^α), the Green's function of simple random walk on G^ε, at the root and
  stopped on exiting B_ρ(0), is at least (1/A) log ε⁻¹ times the degree of the root. For every ε > 0 the walk is
  almost surely recurrent.
- **Theorem 1.5.** With probability 1 − O_ε(ε^α), |f^ε(x) − f^ε(y)| ≤ A₀ (ε ∨ |η(x) − η(y)|)^ξ for χ-Hölder boundary
  data.
- **Corollary 1.6.** With probability tending to 1, the edges of the Tutte embedding of G^ε(D) with identity boundary
  data have length O_ε(ε^ξ′).

The SLE/LQG objects enter through one hypothesis. Every theorem is stated for every coupling of random objects that
satisfies the frozen bundle `MatingOfTreesInput γ`: a γ-quantum cone, a 0-quantum cone, an independent
imaginary-geometry field, the whole-plane space-filling SLE curve that it determines, its parametrizations, and the
boundary-length process, with 24 properties: twelve fix the laws and independence of the SLE-free data, and twelve are
properties of the SLE/LQG coupling taken from the published literature. The theorems therefore apply to the coupling
constructed in that literature, with the caveats of disclosure 3 below.

| Paper item | Lean declaration (frozen) | Status |
| --- | --- | --- |
| Theorem 3.2 (quantitative Dirichlet energy bound), as printed | `MatedCRTHarmonic.theorem3_2` | proved, conditional on the bundle |
| Theorem 1.3 (Dirichlet energy bound), with Theorem 3.2's boundary condition added | `MatedCRTHarmonic.theorem1_3` | proved, conditional on the bundle |
| Theorem 1.4 (Green's function on the diagonal; recurrence) | `MatedCRTHarmonic.theorem1_4` | proved, conditional on the bundle |
| Theorem 1.5 (Hölder continuity), for domains with connected complement | `MatedCRTHarmonic.theorem1_5` | proved, conditional on the bundle |
| Theorem 1.5, for simply connected domains, as printed | `MatedCRTHarmonic.theorem1_5_simplyConnected` | proved, conditional on the bundle |
| Corollary 1.6 (edge lengths of the Tutte embedding), for domains with connected complement | `MatedCRTHarmonic.corollary1_6` | proved, conditional on the bundle |
| Corollary 1.6, for simply connected domains, as printed | `MatedCRTHarmonic.corollary1_6_simplyConnected` | proved, conditional on the bundle |
| The hypothesis: the mating-of-trees input bundle | `MatedCRTHarmonic.MatedCRT.MatingOfTreesInput`, `MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling` | frozen definitions |
| Definitions 1.1, 1.2, (1.3), (1.6), the Tutte embedding, the Green's function at the exit time, bounded convexity | `MatedCRTHarmonic.LFMultigraph.energyOn`, `MatedCRTHarmonic.dirichletEnergy`, `MatedCRTHarmonic.MatedCRT.cell`, `MatedCRTHarmonic.LFMultigraph.IsHarmonicExtension`, `MatedCRTHarmonic.LFMultigraph.IsTutteEmbedding`, `MatedCRTHarmonic.LFMultigraph.exitGreen`, `MatedCRTHarmonic.HasBoundedConvexity` | frozen definitions |

## Exact frozen statements

The declarations below are copied from the frozen files in `MatedCRTHarmonic/Frozen/` (one declaration per file),
with their docstrings and comments omitted, and are shown together here. The statements are identical to the frozen
statements of the development up to comments and the renaming of the module root and namespace to
`MatedCRTHarmonic`; the seven theorems are also renamed after the paper's numbering. This was checked mechanically:
outside comments, each of the 76 frozen files taken from the development (the map, the multigraphs, the walk and the
bundle) has the same token stream as its development file after the renaming, and the elaborated type of each of the
seven theorems, and the elaborated type and value of each of the seven definitions of the paper above, is `==` (Lean
`Expr` equality) to that of the frozen statement text with the same renaming. The proof body of each theorem is `by exact` its provider theorem, which states the same type: the theorems
`MatedCRTHarmonic.GMSMain.MainResults.…_holds` in `GMSMain/MainResultsFinal.lean` and
`GMSMain/MainResultsWiring.lean`, which the theorem files import. The files are in `namespace MatedCRTHarmonic` and open
`MeasureTheory`, `ProbabilityTheory`, `Filter`, `Topology`, `Set` and `Metric`, with the scopes `ENNReal` and
`NNReal`.

**The definitions of the paper.**

```lean
namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

def energyOn (S : Set V) (g : V → ℝ) : ℝ≥0∞ :=
  ∑' e : {e : E // G.src e ∈ S ∧ G.tgt e ∈ S}, ENNReal.ofReal ((g (G.src e.1) - g (G.tgt e.1)) ^ 2)

def IsHarmonicExtension (H : V → Set ℂ) (D : Set ℂ) (f : ℂ → ℝ) (g : V → ℝ) : Prop :=
  ∀ x ∈ verticesMeeting H D,
    (x ∈ verticesMeeting H (frontier D) → IsLUB (f '' (H x ∩ frontier D)) (g x)) ∧
      (x ∉ verticesMeeting H (frontier D) → ∑ d ∈ G.outDarts x, (g x - g (G.dtgt d)) = 0)

def IsTutteEmbedding (H : V → Set ℂ) (D : Set ℂ) (Φ : V → ℂ) : Prop :=
  G.IsHarmonicExtension H D (fun z => z.re) (fun x => (Φ x).re) ∧
    G.IsHarmonicExtension H D (fun z => z.im) (fun x => (Φ x).im)

def exitGreen (U : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' n : ℕ, G.walkLaw x {ω | G.vertexPath ω n = y ∧ (n : ℕ∞) < Markov.hitTime Uᶜ (G.vertexPath ω)}

end LFMultigraph

def dirichletEnergy (f : ℂ → ℝ) (D : Set ℂ) (_hD : IsOpen D) (_hf : DifferentiableOn ℝ f D) : ℝ≥0∞ :=
  ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)

def HasBoundedConvexity (C : ℝ) (D : Set ℂ) : Prop :=
  ∀ z ∈ D, ∀ w ∈ D, ∃ c : ℝ → ℂ, ContinuousOn c (Icc 0 1) ∧ c 0 = z ∧ c 1 = w ∧
    MapsTo c (Icc 0 1) D ∧ eVariationOn c (Icc 0 1) ≤ ENNReal.ofReal (C * dist z w)

namespace MatedCRT

def cell (ε : ℝ) (η : C(ℝ, ℂ)) (x : ℤ) : Set ℂ := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

end MatedCRT
```

**The map and the multigraphs.**

```lean
structure LFMultigraph (V E : Type*) where
  src : E → V
  tgt : E → V
  finite_inc : ∀ x : V, {e : E | src e = x ∨ tgt e = x}.Finite
  exists_inc : ∀ x : V, ∃ e : E, src e = x ∨ tgt e = x

variable {V : Type*} in
def verticesMeeting (J : V → Set ℂ) (D : Set ℂ) : Set V := {x | (J x ∩ D).Nonempty}

namespace MatedCRT

def intervalInf (X : ℝ → ℝ) (a b : ℝ) : ℝ := sInf (X '' Icc a b)

def SideCond (ε : ℝ) (X : ℝ → ℝ) (x y : ℤ) : Prop :=
  max (intervalInf X (ε * ((x : ℝ) - 1)) (ε * x)) (intervalInf X (ε * ((y : ℝ) - 1)) (ε * y)) ≤
    intervalInf X (ε * x) (ε * ((y : ℝ) - 1))

def IsEdge (ε : ℝ) (ω : Path2) (e : ℤ × ℤ × Bool) : Prop :=
  e.1 < e.2.1 ∧
    ((e.2.1 = e.1 + 1 ∧ e.2.2 = false) ∨
      (e.2.1 ≠ e.1 + 1 ∧ SideCond ε (fun t => if e.2.2 then (ω t).2 else (ω t).1) e.1 e.2.1))

abbrev Edge (ε : ℝ) (ω : Path2) : Type := {e : ℤ × ℤ × Bool // IsEdge ε ω e}

def IsLocallyFinite (ε : ℝ) (ω : Path2) : Prop :=
  ∀ x : ℤ, {e : Edge ε ω | e.1.1 = x ∨ e.1.2.1 = x}.Finite

def graph (ε : ℝ) (ω : Path2) (h : IsLocallyFinite ε ω) : LFMultigraph ℤ (Edge ε ω) where
  src e := e.1.1
  tgt e := e.1.2.1
  finite_inc := h
  exists_inc x := ⟨⟨(x, x + 1, false), lt_add_one x, Or.inl ⟨rfl, rfl⟩⟩, Or.inl rfl⟩

end MatedCRT
```

`SideCond ε X x y` is (1.1) for the coordinate `X` and the vertices `εx < εy` (l. 89–97).

- `energyOn G S g` is Definition 1.1 on the sub-graph `G(S)` of (1.5) (l. 413–417, 456–462): parallel edges count with
  their multiplicity, a loop contributes 0, and the value is in `[0, ∞]`.
- `IsHarmonicExtension G H D f g` is (1.6) (l. 446–453): at a vertex whose cell meets `∂D`, `g` is the supremum of `f`
  over the cell's points on `∂D` (stated with `IsLUB`); at the other vertices whose cells meet `D`, `g` is discrete
  harmonic for simple random walk on `G`.
- `IsTutteEmbedding` is the Tutte embedding with identity boundary data (l. 538–541): its real and imaginary parts are
  the functions of (1.6) for `f = Re` and `f = Im`.
- `exitGreen G U x y` is the Green's function of l. 495–497 at the exit time from `U` (l. 499–505): the expected number
  of visits to `y` before the first time outside `U`, time 0 included, under the quenched walk law.
- `dirichletEnergy f D hD hf` is Definition 1.2 (l. 464–468) for an open `D` and `f` differentiable on `D`.
- `HasBoundedConvexity C D` is C-bounded convexity (l. 1227–1228): any two points of `D` are joined by a path in `D`
  of length at most `C` times their distance.
- `MatedCRT.cell ε η x` is the cell `H^ε_{εx} = η([ε(x − 1), εx])` of (1.3) (l. 407).

**Theorem 3.2** (l. 1218–1245), as printed.

```lean
theorem theorem3_2 :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
          ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            ∀ D : Set ℂ, ∀ hD : IsOpen D, D ⊆ ball (0 : ℂ) ρ →
            (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
            HasBoundedConvexity C D →
            ∀ f : ℂ → ℝ, ∀ hf : DifferentiableOn ℝ f D,
              (∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
              (∀ z ∈ D, |f z| ≤ ε ^ (-β)) → (∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
              ContinuousOn f (closure D) →
                P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
                  (∃ g : ℤ → ℝ,
                    (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g) ∧
                  ∀ g : ℤ → ℝ,
                    (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g →
                    (MatedCRT.graph ε (bm ω) h).energyOn (verticesMeeting (MatedCRT.cell ε (η ω)) D) g ≤
                      ENNReal.ofReal A * dirichletEnergy f D hD hf + ENNReal.ofReal (ε ^ α)} ≤
                  ENNReal.ofReal (Cr * ε ^ α) :=
```

**Theorem 1.3** (l. 470–484), with Theorem 3.2's condition `area(B_r(∂D)) ≤ C r` added and `A` uniform in `f`
(see disclosure 7 and correction 1).

```lean
theorem theorem1_3 :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C → ∃ A : ℝ, 0 < A ∧
          ∀ D : Set ℂ, ∀ hD : IsOpen D, D ⊆ ball (0 : ℂ) ρ → HasBoundedConvexity C D →
          (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
          ∀ f : ℂ → ℝ, ∀ hf : DifferentiableOn ℝ f D, ContinuousOn (fderiv ℝ f) D →
            (∃ L : ℝ≥0, LipschitzOnWith L (fderiv ℝ f) D) → ContinuousOn f (closure D) →
            ∃ Cf : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
              P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
                (∃ g : ℤ → ℝ,
                  (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g) ∧
                ∀ g : ℤ → ℝ,
                  (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g →
                  (MatedCRT.graph ε (bm ω) h).energyOn (verticesMeeting (MatedCRT.cell ε (η ω)) D) g ≤
                    ENNReal.ofReal A * dirichletEnergy f D hD hf} ≤
                ENNReal.ofReal (Cf * ε ^ α) :=
```

**Theorem 1.4** (l. 499–508).

```lean
theorem theorem1_4 :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        (∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ,
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              ENNReal.ofReal (1 / A * Real.log ε⁻¹) ≤
                (MatedCRT.graph ε (bm ω) h).exitGreen
                    (verticesMeeting (MatedCRT.cell ε (η ω)) (ball (0 : ℂ) ρ)) 0 0 /
                  ((MatedCRT.graph ε (bm ω) h).deg 0 : ℝ≥0∞)} ≤
              ENNReal.ofReal (C * ε ^ α)) ∧
        ∀ ε : ℝ, 0 < ε →
          ∀ᵐ ω ∂P, ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), (MatedCRT.graph ε (bm ω) h).Recurrent :=
```

**Theorem 1.5** (l. 517–524), for domains with connected complement and, as printed, for simply connected domains.

```lean
theorem theorem1_5 :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
          ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
          ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ g : ℤ → ℝ,
                (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g) ∧
              ∀ g : ℤ → ℝ,
                (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g →
                ∀ x ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D,
                  ∀ y ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D,
                    |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
              ENNReal.ofReal (C * ε ^ α) :=
```

```lean
theorem theorem1_5_simplyConnected :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace D →
          ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
          ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ g : ℤ → ℝ,
                (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g) ∧
              ∀ g : ℤ → ℝ,
                (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g →
                ∀ x ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D,
                  ∀ y ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D,
                    |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
              ENNReal.ofReal (C * ε ^ α) :=
```

**Corollary 1.6** (l. 538–551), for domains with connected complement and, as printed, for simply connected domains.

```lean
theorem corollary1_6 :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
          ∃ C : ℝ, Tendsto (fun ε : ℝ =>
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ Φ : ℤ → ℂ,
                (MatedCRT.graph ε (bm ω) h).IsTutteEmbedding (MatedCRT.cell ε (η ω)) D Φ) ∧
              ∀ Φ : ℤ → ℂ,
                (MatedCRT.graph ε (bm ω) h).IsTutteEmbedding (MatedCRT.cell ε (η ω)) D Φ →
                ∀ e : MatedCRT.Edge ε (bm ω),
                  (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D →
                  (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D →
                    ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                      C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
```

```lean
theorem corollary1_6_simplyConnected :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace D →
          ∃ C : ℝ, Tendsto (fun ε : ℝ =>
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ Φ : ℤ → ℂ,
                (MatedCRT.graph ε (bm ω) h).IsTutteEmbedding (MatedCRT.cell ε (η ω)) D Φ) ∧
              ∀ Φ : ℤ → ℂ,
                (MatedCRT.graph ε (bm ω) h).IsTutteEmbedding (MatedCRT.cell ε (η ω)) D Φ →
                ∀ e : MatedCRT.Edge ε (bm ω),
                  (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D →
                  (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D →
                    ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                      C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
```

**The hypothesis: the mating-of-trees input bundle.**

```lean
namespace MatedCRT

structure IsMatingOfTreesCoupling (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  gff : LQGMetric.IsWholePlaneGFF X P
  gff₀ : LQGMetric.IsWholePlaneGFF X₀ P
  bm_B : IsBrownianReal B P
  bm_B' : IsBrownianReal B' P
  bm_B₀ : IsBrownianReal B₀ P
  bm_B₀' : IsBrownianReal B₀' P
  indep_cone : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P
  indep_cone₀ : IndepFun X₀ (fun ω => ((fun t => B₀ t ω), (fun t => B₀' t ω))) P ∧
    IndepFun (fun ω t => B₀ t ω) (fun ω t => B₀' t ω) P
  igField : LQGMetric.IsNormalizedWPGFF hIG₀ P ∧ P.map U = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)] ∧
    IndepFun hIG₀ U P
  indep_curve : IndepFun (fun ω => (hIG₀ ω, U ω))
    (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω, (fun t => B₀ t ω), (fun t => B₀' t ω))) P
  measurable_curves : Measurable ηL ∧ Measurable η ∧ Measurable η₀ ∧ Measurable bm
  igMap : ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
    (∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K') ∧
    (∀ᵐ ω ∂P, ηL ω = Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) ∧
    (∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (igPullback γ z₀ s φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) =
        affineReroot z₀ s φ (ηL ω)) ∧
    (∀ (V : Set ℂ), IsOpen V → Bornology.IsBounded V → ∀ δ : ℝ, 0 < δ →
      ∃ g : (ℝ → ℂ → ℝ) → (ℚ × ℚ → ℝ → ℂ), Measurable g ∧ ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ,
        ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ V →
          excursionSegment (ηL ω) V ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) =
            g (restrictCircles (thickening δ V)
              (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) q)
  spaceFilling : ∀ᵐ ω ∂P, Function.Surjective (ηL ω) ∧
    Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) ∧ ηL ω 0 = 0 ∧
    ∀ s t : ℝ, s ≤ t → volume (ηL ω '' Icc s t) = ENNReal.ofReal (t - s)
  areaParam : ∀ᵐ ω ∂P,
    (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, η ω t = ηL ω (φ t)) ∧
      ∀ μ : Measure ℂ,
        IsVagueLimitC (lqgAreaApprox γ (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))) μ →
          ∀ s t : ℝ, s ≤ t → μ (η ω '' Icc s t) = ENNReal.ofReal (t - s)
  areaParam₀ : ∀ᵐ ω ∂P,
    (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, η₀ ω t = ηL ω (φ t)) ∧
      ∀ μ : Measure ℂ,
        IsVagueLimitC (lqgAreaApprox γ (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))) μ →
          ∀ s t : ℝ, s ≤ t → μ (η₀ ω '' Icc s t) = ENNReal.ofReal (t - s)
  segmentsContainBalls : ∀ R : ℝ, 0 < R → ∀ r ∈ Ioo (0 : ℝ) 1, ∀ N : ℕ, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
    P {ω | ¬ SegmentsContainBalls (ηL ω) R r ε} ≤ ENNReal.ofReal (C * ε ^ N)
  coverage : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ M : ℝ, 1 < M →
    P {ω | ¬ ball (0 : ℂ) 1 ⊆ η ω '' Icc (-M) M} ≤ ENNReal.ofReal (C * M ^ (-c))
  cellMoments :
    (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, diamAreaSup (η₀ ω) ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∫⁻ ω, ((degInner (η₀ ω) : ℝ≥0∞)) ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ((degOuter (η₀ ω) : ℝ≥0∞)) ^ p ∂P < ⊤)
  boundaryLawBM : IsCorrelatedBM2 γ (P.map bm)
  boundaryLength : ∃ BL : Field × C(ℝ, ℂ) → Path2, Measurable BL ∧
    (∀ᵐ ω ∂P, bm ω = BL (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)), η ω)) ∧
    ∀ b₀ : ℝ, 0 < b₀ → ∀ᵐ ω ∂P,
      BL (coneRescaleField γ (coneScale γ γ (fun u => B u ω) (fun u => B' u ω) b₀) b₀
            (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))),
          coneRescaleCurve (coneScale γ γ (fun u => B u ω) (fun u => B' u ω) b₀) b₀ (η ω)) =
        brownRescale b₀ (bm ω)
  merge : ∀ᵐ ω ∂P, ∀ s t : ℝ,
    (DirectRel (fun u => lrCoord 0 u (bm ω)) s t ∨ DirectRel (fun u => lrCoord 1 u (bm ω)) s t) →
      η ω s = η ω t
  onlyMerge : ∀ᵐ ω ∂P, ∀ s t : ℝ, η ω s = η ω t →
    Relation.EqvGen (fun a c => DirectRel (fun u => lrCoord 0 u (bm ω)) a c ∨
      DirectRel (fun u => lrCoord 1 u (bm ω)) a c) s t
  visitBound : ∃ k : ℕ, ∀ᵐ ω ∂P, ∀ z : ℂ, ((ηL ω) ⁻¹' {z}).encard ≤ k

def MatingOfTreesInput (γ : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
    (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2),
    IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm

end MatedCRT
```

**The objects.**
- `MatedCRT.Field` is the type of distributions on ℂ of the released `LQGMetric` library (`LQGMetric.DistC`), and
  `MatedCRT.Path2` is `C(ℝ, ℝ × ℝ)`, the type of the boundary-length pair `(L, R)`.
- `MatedCRT.graph ε w h` is the ε-mated-CRT map (1.1) of the pair `w` (l. 89–97). The vertex `x : ℤ` stands for `εx`.
  Consecutive vertices are joined by one edge; non-consecutive `x < y` are joined by one edge for each coordinate
  (`L` or `R`) for which (1.1) holds, so a pair that satisfies both gets two edges. `h : MatedCRT.IsLocallyFinite ε w`
  says that every vertex has finitely many edges; it holds almost surely.
- `verticesMeeting J D` is `{x | J x ∩ D ≠ ∅}`, the vertex set `V_{G^ε}(D)` of (1.5).
- `LFMultigraph V E` is a locally finite multigraph with no isolated vertex. Its simple random walk moves along darts
  (a loop gives two darts), `walkLaw x` is the law of the walk from `x`, `vertexPath` its vertex sequence, `outDarts`,
  `dtgt` and `deg` are the darts at a vertex, their heads and the degree, and `Markov.hitTime A` is the first time in
  `A`. `Recurrent` says that from every vertex the walk hits every vertex almost surely.
- In the bundle:
  - `LQGMetric.IsWholePlaneGFF` is the whole-plane Gaussian free field (as a random distribution, modulo additive
    constants), `LQGMetric.IsNormalizedWPGFF` adds the normalization `h_1(0) = 0`, and `LQGMetric.circleAvg h r z` is the
    circle average of `h` on `∂B_r(z)`.
  - `IsBrownianReal` is Mathlib's standard real Brownian motion.
  - `coneField X (coneRadial γ α B B')` is the α-quantum cone of Duplantier–Miller–Sheffield (Definition 4.10 of
    arXiv:1409.7055): the lateral part of `X` plus the radial process built from `B` and `B'`, with `α = γ` for the
    γ-quantum cone and `α = 0` for the 0-quantum cone.
  - `lqgAreaApprox γ h k` is the measure `e^{γ h_r(z)} r^{γ²/2} dz` at the dyadic radius `r = 2^{−k}`, and
    `IsVagueLimitC` is vague convergence on ℂ.
  - `igChi γ` is χ = 2/γ − γ/2. `igPullback` and `affineReroot` express the imaginary-geometry coordinate change under
    `w ↦ z₀ + s e^{iφ} w`, the curve being re-rooted at its first visit to `z₀`. `excursionSegment c V z` is the segment of
    `c` in `V` around its first visit to `z`, and `restrictCircles` keeps the circle averages on circles inside a set.
  - `SegmentsContainBalls c R r ε` is the event of the cited estimate: for every `δ ∈ (0, ε]`, every segment
    `c([a, b]) ⊂ B_R(0)` of diameter at least `δ^{1−r}` contains a ball of radius `δ`. `diamAreaSup c` is the supremum
    over `s ∈ [0, 1]` of diameter²/area of `c([s − 1, s])`, and `degInner c`, `degOuter c` are the inner and outer
    degrees of GMS-T Definition 4.5 of the root cell `c([−1, 1])`; the bundle applies them to the 0-cone's curve `η₀`.
  - `IsCorrelatedBM2 γ μ` says that `μ` is the law of a centred Gaussian pair of two-sided Brownian motions with
    variance 1 and correlation `−cos(πγ²/4)`. `DirectRel X s t` is a direct identification of the times `s < t` by the
    coordinate `X` (`X s = X t < X u` for `s < u < t`), and `lrCoord i` selects a coordinate.
  - `coneScale`, `coneRescaleField`, `coneRescaleCurve` and `brownRescale` implement the scaling of the γ-quantum cone
    by a factor `b`: the rescaled field `h_b`, the rescaled curve `η^b`, and the pair `b^{−1/2} w(b ·)`.

## Statement scope and disclosures

These points are part of the approved statements and matter when the Lean statements are compared with the paper.

1. **Conditional on the bundle.** Every theorem has the form: for every γ ∈ (0, 2), every standard Borel probability
   space `(Ω, P)` and every family `X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm` satisfying
   `IsMatingOfTreesCoupling γ P …`, the paper's statement holds for the mated-CRT map of that family. These families
   are exactly the witnesses of `MatingOfTreesInput γ`. The bundle collects published results of the mating-of-trees,
   SLE and LQG literature as hypotheses; none of them is proved here. If no family satisfies the bundle, the theorems
   are vacuous. That one does (the coupling constructed in the literature) rests on the cited papers, not on Lean.
   Every SLE-free ingredient and every lemma of the paper that the proofs use is proved (see "Cited inputs").
2. **The 24 fields.** The first twelve fix the laws of the SLE-free data, their independence and measurability; the
   other twelve are properties of the SLE/LQG coupling from the published literature; item 3 lists those that are
   not separately numbered theorems or whose published proofs are sketched or incomplete. Keys: DMS =
   Duplantier–Miller–Sheffield, arXiv:1409.7055v4; GHMS = Gwynne–Holden–Miller–Sun, arXiv:1510.04687v2; GHM =
   Gwynne–Holden–Miller, arXiv:1512.01223v5;
   GHS = Gwynne–Holden–Sun, arXiv:1606.01214v4; GMS-T = Gwynne–Miller–Sheffield, arXiv:1705.11161v5 (cited in the paper
   as [GMS17]); IG I and IG IV = Miller–Sheffield, arXiv:1201.1496v2 and arXiv:1302.4738v2.

   | Field | Content | Source |
   | --- | --- | --- |
   | `isProbabilityMeasure` | `P` is a probability measure. | — |
   | `gff`, `gff₀` | `X` and `X₀` are whole-plane GFFs, whose lateral parts are those of the γ-cone and of the 0-cone. | DMS Definition 4.10 |
   | `bm_B`, `bm_B'`, `bm_B₀`, `bm_B₀'` | Standard real Brownian motions driving the radial parts of the two cones. | DMS Definition 4.10 |
   | `indep_cone`, `indep_cone₀` | Within each cone, the field and the two Brownian motions are independent. | DMS Definition 4.10 |
   | `igField` | `hIG₀` is a whole-plane GFF with `h_1(0) = 0`, `U` is uniform on `[0, 2πχ)` and independent of it; `hIG₀ + U` is the imaginary-geometry field. | IG IV (convention for the whole-plane field); paper l. 856–864 |
   | `indep_curve` | `(hIG₀, U)` is independent of both cones. | paper l. 288–289 and 400–402 |
   | `measurable_curves` | `ηL`, `η`, `η₀` and `bm` are random variables. | — |
   | `igMap` | `ηL` is a measurable function `Φ` of the circle averages of `hIG₀ + U`; `Φ` ignores radii `≤ 0`, satisfies the coordinate change for every map `w ↦ z₀ + s e^{iφ} w`, and is local: the excursion segments in a bounded open set are measurable functions of the field near that set. | IG I (1.4) and IG IV (1.2) (coordinate change); IG IV Theorems 1.1, 1.2 and 1.16; DMS footnote 4; paper Lemma 2.4 |
   | `spaceFilling` | `ηL` is surjective and transient, `ηL(0) = 0`, and `area(ηL([s, t])) = t − s`. | DMS Lemma 8.11; paper l. 883–885 |
   | `areaParam`, `areaParam₀` | `η` (resp. `η₀`) is `ηL` reparametrized by γ-LQG area of the γ-cone (resp. the 0-cone): `μ(η([s, t])) = t − s` for every vague limit `μ` of the area approximations, with `η(0) = 0`. | DMS, setting of Theorem 1.9; GMS-T for the 0-cone |
   | `segmentsContainBalls` | Superpolynomially small probability in `ε` that, for some `δ ≤ ε`, a segment of `ηL` inside `B_R(0)` of diameter at least `δ^{1−r}` contains no ball of radius `δ`. | GHM Proposition 3.4 and Remark 3.9 |
   | `coverage` | `P[B_1(0) ⊄ η([−M, M])] ≤ C M^{−c}`. | GHS Lemma A.4 |
   | `cellMoments` | Moments for the 0-cone: of `sup_{s ∈ [0,1]} diam(η₀([s−1, s]))²/area(η₀([s−1, s]))` for every `p ≥ 1`, of the inner degree (GMS-T Definition 4.5) for `1 ≤ p < 4/γ²`, and of the outer degree for every `p ≥ 1`. | GMS-T Propositions 4.4 and 4.6 |
   | `boundaryLawBM` | `bm` is a correlated two-sided Brownian motion with variance 1 and correlation `−cos(πγ²/4)`. | DMS Theorem 1.9 (Theorem 8.1) for κ′ ≤ 8; GHMS Theorem 1.1 for κ′ > 8 |
   | `boundaryLength` | `bm` is a measurable functional of `(h, η)` (the normalized boundary-length process), and under the cone's scaling by `b` it becomes `b^{−1/2} bm(b ·)`. | DMS §1 (quantum length: coordinate change and constant shift); see disclosure 3 |
   | `merge` | Times directly identified by `L` or by `R` are mapped by `η` to the same point. | DMS Lemma 8.8 |
   | `onlyMerge` | Times mapped by `η` to the same point are related by the equivalence relation generated by direct identifications. | DMS Lemmas 8.9 and 8.14 |
   | `visitBound` | For a deterministic `k`, almost surely `ηL` visits every point at most `k` times. | DMS Lemma 8.13 with (8.9) |

   Theorem 1.4 uses all 24 fields. The other six theorems use 23 of them: all except `boundaryLength`.
3. **Caveats on the bundle's sources.**
   - **γ = √2 (κ′ = 8).** At γ = √2, `boundaryLawBM` says that `L` and `R` are uncorrelated. DMS state this
     (Theorem 1.9), but the key step of their Lemma 8.7, which treats κ′ = 8, is asserted without proof. What their
     argument establishes there is a two-sided planar Brownian motion with equal variances (Lemma 8.2 and the symmetry
     of the construction), with nonpositive covariance derived in one sentence from the absence of local cut points of
     SLE₈, and GHMS cover γ < √2 only. So at γ = √2 all seven theorems rest on a published claim whose proof is
     incomplete.
   - **`onlyMerge` and `visitBound`.** DMS Lemma 8.14 relies on the part of the proof of Lemma 8.13 that is only
     sketched, and Lemma 8.13 also gives the visit bound. The relation printed "R_s = L_t" in condition 2 of the
     statement of Lemma 8.14 is read as "R_s = R_t". The visit bound counts distinct times and does not depend on the
     time parametrization.
   - **`boundaryLength`.** The pathwise behaviour of the boundary-length process under the cone's random scaling
     follows from the coordinate-change rule for quantum length and the rule for adding a constant to the field. It is
     not a separately numbered theorem, and the coordinate-change rule is stated almost surely for each fixed map, while
     here it is applied at the random scaling map; that use rests on the construction of quantum length along the
     curve. Only Theorem 1.4 uses this field.
   - **Whole-plane determination (`igMap`).** IG IV Theorem 1.16 proves that the field determines the curve for
     chordal space-filling SLE. The whole-plane statement used here is deduced from it in the paper only as a sketch
     ("can be proven using the same argument or deduced from the chordal case and [DMS14, Footnote 4]", l. 896–899);
     the locality clause is the paper's Lemma 2.4 (l. 901–908).
   - **The imaginary-geometry convention.** The bundle uses the convention of IG IV (§2.2) and DMS (§1.4.1): the
     whole-plane field viewed modulo `2πχℤ` is a whole-plane GFF normalized by `h_1(0) = 0` plus an independent
     constant `U`, uniform on `[0, 2πχ)`. The paper (l. 856–864) says that it follows IG IV §2.2 but omits `U`. Read
     literally, this changes the law of the curve: the IG IV curve is the literal one rotated about 0 by an independent
     uniform angle (IG IV (1.2)), and the two laws differ because the curve determines the field modulo `2πχ`
     (IG IV Theorem 1.10). The paper's arguments use DMS Theorem 1.9 for the curve of the IG IV convention (l. 329), so
     the bundle follows that convention; the literal reading is not treated here. That `Φ` ignores circle averages of
     nonpositive radius is a clause of the hypothesis, not a separately numbered theorem; it rests on two facts: the
     field is determined by its circle averages at positive radii, and the curve by the field.
   - **The range of DMS §8.** §8.1 of DMS is written for κ′ ∈ (4, 8]; the lemmas of §8.2 used for the curve (8.8 and
     8.11–8.14) do not use that restriction: Lemma 8.11 is stated for every κ′ > 4, and the arguments of 8.12–8.13 treat
     κ′ ≥ 8 and κ < 2 explicitly.
   - **Properties, not definitions.** The bundle lists properties of the coupling; it does not construct SLE or LQG
     objects in Lean. Any family with these properties is admissible, and a theorem proved for every such family holds
     in particular for the coupling of the literature.
4. **The map.** `G^ε` is `MatedCRT.graph ε (bm ω) h`, the ε-mated-CRT map of the bundle's boundary-length pair. Its
   cells are `MatedCRT.cell ε (η ω) x = η([ε(x − 1), εx])` ((1.3)), and the vertex `x` sits at `η(εx)` (l. 342–344).
   The paper defines `G^ε` by boundary-arc adjacency of cells (l. 402–405) and, for the γ-cone, identifies it with the
   mated-CRT map of the boundary-length process (l. 329–342, citing DMS Theorem 1.9 and §8.2). The bundle carries that
   identification through `boundaryLawBM`, `boundaryLength`, `merge` and `onlyMerge`; no separate notion of boundary
   arcs is formalized.
5. **Every real ε.** As printed, every statement is for every real ε ∈ (0, 1) (for example l. 1234–1236 and
   1618–1619), not only for dyadic ε.
6. **Constants after the coupling.** The paper has one model for each γ, so its constants depend on γ only
   (α = α(γ), A = A(ρ, γ), …). In the Lean statements every constant is chosen after the coupling, and before every
   parameter on which the paper says it does not depend (item 13).
   - The bundle does not determine the joint law of `(η, bm)`: exchanging the two coordinates of `bm` turns a coupling
     into another coupling, which for the coupling of the literature has a different joint law of `(η, bm)` (the map
     `G^ε` itself is unchanged).
   - On a standard Borel space, the outer probability of any event of `(η, bm)` equals its outer probability under the
     law of `(η, bm)` (by disintegration). So the constants depend on the coupling only through the law of `(η, bm)`,
     which for the coupling of the literature is determined by γ. This identity and the swap were checked in Lean during
     the development; those lemmas are not part of this library.
   - Uniformity over all couplings that satisfy the bundle is not claimed. It would say more than the paper, and the
     constants of the proofs depend on quantities that the bundle controls only coupling by coupling, for example the
     visit bound `k` of `visitBound` and the exponent `c` of `coverage`.
7. **Theorem 1.3 in repaired form.** As printed, Theorem 1.3 is false (correction 1). The Lean statement adds Theorem
   3.2's condition `area(B_r(∂D)) ≤ C r` for `r ∈ (0, 1)`, uses one constant `C` for this condition and for the
   bounded convexity, and takes `A` independent of `f`. This implies the printed dependence `A(D, γ, Lip f, Lip ∇f)`
   on domains that satisfy the condition. Theorem 3.2 is stated as printed.
8. **"Simply connected".** The proofs use only that `ℂ ∖ D` is connected (l. 1725). Theorem 1.5 and Corollary 1.6
   therefore have two forms each: for open connected `D ⊂ B_ρ(0)` with `ℂ ∖ D` connected, and, as printed, for open
   simply connected `D ⊂ B_ρ(0)`. The second form follows from the first by a planar-topology theorem proved in the
   library, `MatedCRTHarmonic.isConnected_compl_of_simplyConnected`: a bounded, simply connected, open `D ⊂ ℂ` has
   connected complement. Discs satisfy both sets of hypotheses.
9. **Boundary data.** (1.6) evaluates `f` on `∂D`. So in Theorems 1.3 and 3.2, `f` is a real function that is
   continuous on the closure of `D` (`ContinuousOn f (closure D)`). The paper writes "f : D → ℂ continuous" (l. 447),
   but `f^ε` is real-valued and (1.6) needs the boundary values. In Theorem 1.5 only the restriction of `f` to `∂D`
   enters, as a χ-Hölder function on `∂D`. The functions `f^ε` and `Φ^ε` are not defined as objects: each good event
   says that a function with the defining properties exists and that every such function satisfies the bound.
   Existence and uniqueness on `V(D)` hold almost surely and are proved.
10. **Definition 1.2.** `dirichletEnergy f D hD hf = ∫_D |∇f(z)|² dz` takes the openness of `D` and the
    differentiability of `f` on `D` as arguments. On an open set, `fderiv ℝ f z` is then the pointwise gradient at every
    point of `D`; without openness, Lean's `fderiv` could take its default value at points where `f` is only
    differentiable within `D`. In both uses `∇f` is continuous on `D`, where the distributional gradient of Definition
    1.2 is the pointwise one, and the operator norm `‖fderiv ℝ f z‖` is the Euclidean `|∇f(z)|`.
11. **Probabilities.** "With probability at least 1 − O_ε(ε^α)" is `∃ C, ∀ ε ∈ (0, 1), P(bad) ≤ C ε^α`, where
    `P(bad)` is the outer measure of the bad event, so no measurability of the event is assumed. Every bad event
    contains the null set on which `G^ε` is not locally finite. "With probability tending to 1" (Corollary 1.6) is
    `Tendsto (fun ε => P(bad)) (𝓝[>] 0) (𝓝 0)`.
12. **Graph conventions.** Discrete harmonicity is taken in the whole `G^ε` at the vertices of `V(D) ∖ V(∂D)`; this
    agrees with harmonicity in `G^ε(D)` almost surely. The Green's function counts visits before the exit time from
    `V(B_ρ(0))`, and `deg(0; G^ε)` is the degree in `G^ε`.
13. **Order of quantifiers.** All constants come after the coupling (item 6).

    | Theorem | Printed dependence | Lean order |
    | --- | --- | --- |
    | 3.2 | α(γ), β(γ); A(C, ρ, γ); rate depending on (C, ρ, γ) | `∃ α, ∃ β, ∀ ρ, ∀ C ≥ 1, ∃ A, ∃ Cr, ∀ ε, ∀ D, ∀ f` |
    | 1.3 | α(γ); A(D, γ, Lip f, Lip ∇f); here A = A(C, ρ, γ), uniform in `f` and in the domains `D ⊂ B_ρ(0)` with constant `C` | `∃ α, ∀ ρ, ∀ C ≥ 1, ∃ A, ∀ D, ∀ f, ∃ C_f, ∀ ε` |
    | 1.4 | α(γ); A(ρ, γ) | `(∃ α, ∀ ρ, ∃ A, ∃ C, ∀ ε) ∧ ∀ ε > 0, almost surely recurrent` |
    | 1.5 | α(γ); ξ(ρ, χ, γ); A₀(f, D, γ) | `∃ α, ∀ ρ, ∀ χ, ∃ ξ, ∀ D, ∀ f, ∃ A₀, ∃ C, ∀ ε` |
    | 1.6 | ξ′(ρ, γ); the O_ε-constant | `∀ ρ, ∃ ξ′, ∀ D, ∃ C, Tendsto …` |

14. **Statement audit.** Before the statements were frozen, an independent statement audit compared every binder with
    the paper. It found no hypothesis beyond the paper's and the bundle, and required one change: the openness argument
    of `dirichletEnergy` (item 10). Independent transcriptions of Theorem 1.5 and Corollary 1.6 were proved equivalent in
    Lean to the frozen statements, and the simply connected forms were checked to follow from the main forms.

## What is not claimed

- **The bundle.** Its fields (the mating-of-trees theorem, whole-plane space-filling SLE and its properties, the LQG
  parametrizations, the cited estimates) are hypotheses, and the existence of a coupling satisfying them is not proved
  in Lean.
- **Theorem 1.3 as printed.** It is false (correction 1).
- **Theorem 3.9 as printed.** Its boundary estimate (3.31), with (3.38), is false without a floor `ε^β`
  (correction 2). The interior estimate (3.30) as printed, its claims at boundary vertices and the exponent of (3.33)
  are not proved (correction 3). Only a corrected version is proved, inside the library.
- **The paper's lemmas and propositions as public results.** They are formalized inside the library, several in
  corrected or modified form: for example Lemma 4.6 only with a larger polylogarithmic exponent (correction 9), and the
  moment claim after (4.16) only for some moment of order `p > 1` (correction 10). Only the seven frozen statements are
  claimed.
- **Uniform constants.** No constant is claimed to be uniform over the couplings that satisfy the bundle
  (disclosure 6).
- **Other fields.** The statements for the whole-plane GFF and the 0-quantum cone in the paper's §4 are used inside the
  proofs but are not claimed as results.

## Corrections to the printed text

Formalizing the proofs required the corrections and completions below. They are listed so that readers can compare the
Lean statements with the paper. Of the main results, only Theorem 1.3 is affected as stated; Theorems 3.2, 1.4 and 1.5
and Corollary 1.6 are proved here as printed (conditional on the bundle, with the readings of disclosures 5, 8 and 9),
and the paper's arguments go through after these repairs.

**Main statements and Section 3.**

1. **Theorem 1.3 (l. 470–484) omits a hypothesis.** Its proof says that it follows from Theorem 3.2 (l. 1314–1316),
   but Theorem 3.2's class also requires `area(B_r(∂D)) ≤ C r` (condition 1, l. 1223), which Theorem 1.3 drops.
   Without it the statement is false.
   - *Why.* Energies are 2-homogeneous and the boundary data (1.6) are positively homogeneous. So, applied to `c·g` for
     small `c`, a constant `A(D, γ, Lip f, Lip ∇f)` would bound the ratio of discrete to continuum energy for every
     `C^{1,1}` function `g`: a bound depending on `D` alone.
   - *Counterexample.* Let `F ⊂ [0, 1]` be a fat Cantor set (closed, nowhere dense, of positive length) and `Q` an open
     square with closure in `B_ρ(0)` containing a scaled copy of `K = F × F`; set `D = Q ∖ K`. Then `D` is open,
     connected and has 2-bounded convexity (join points by a horizontal and a vertical segment at coordinates outside
     `F`), but `∂D ⊇ K` has positive area. Take `g_w(z) = w² Ψ((z − p)/w)` at a Lebesgue density point `p` of `K`, with
     `Ψ` smooth, supported in the unit disc and `∇Ψ = e₁` near 0. The Lipschitz constants of `g_w` and `∇g_w` stay
     bounded, and `Energy(g_w; D) = o(w⁴)` as `w → 0`. For fixed `w`, with probability `1 − O(ε^α)` the discrete energy
     is at least `c w⁴`: cells meeting `K` are boundary vertices, boundary values at the two ends of horizontal segments
     at heights in `F` near `p` differ by at least `w²/4`, and the argument of Lemma 3.7 with Lemma 3.1 turns these
     increments into energy. So the ratio is unbounded.
   - *Repair.* Add `area(B_r(∂D)) ≤ C r`. Then Theorem 1.3 follows from Theorem 3.2 with `A = A(C, ρ, γ) + 1`,
     uniformly in `f`: for small ε the term `ε^α` is at most `Energy(f; D)` when that is positive, and when it is 0, `f`
     is constant and so is `f^ε`.
2. **(3.31) and (3.38) need a floor `ε^β` (l. 1628–1636, 1724–1739).** Lemma 3.11 is available only at radii
   `r ≥ ε^β`, so the scales in (3.38) must stop at `ε^β`. Without the floor, (3.31) is false.
   - *Counterexample.* In any realization, take a vertex `x` and `t > 0`, and let `D` be `B_ρ(0)` minus a slit along
     a simple arc from `∂B_ρ(0)` whose tip approaches `η(x)` inside the neighbouring cell `H_{x+ε}` without meeting
     `H_x`; `D` is simply
     connected. Take boundary data 0 on the vertices whose cells meet `∂D ∩ B_t(η(x))` and 1 elsewhere. As the tip
     moves, the vertex sets and the data do not change, so `f^ε(x)` stays at a fixed positive value (the walk from `x`
     reaches the far boundary with positive probability), while the bound `0 + A‖f^ε‖_∞ (t/dist(η(x), ∂D))^{−ξ}` of
     (3.31) tends to 0.
   - *Repair.* Replace `dist(η(x), ∂D)` by `dist(η(x), ∂D) ∨ ε^β` in (3.31) and (3.38). With the floor, the estimate
     holds for every vertex of `V(D)`, boundary vertices included, and every `t > 0`.
   - *Also in this step.* "Since `ℂ ∖ D` is connected" (l. 1725–1726) needs the cells meeting the connected set
     `ℂ ∖ D` to form a connected subgraph; this cell-topology fact is not stated in the paper and is proved here from
     the identification of the map with the curve. `B_{r/2}(0)` at l. 1726 should be `B_{r/2}(η(x))`. Near
     `∂B_ρ(0)`, Lemma 3.11 is needed on a slightly larger ball `B_{ρ′}(0)`.
3. **The interior estimate (3.30) and (3.33) (l. 1696–1751).**
   - "We have absorbed β into ξ" (l. 1717–1718) is not valid in the ratio form: the scales stop at `ε^β`, so the proof
     gives (3.30) with `ε^β ∨ |η(x) − η(y)|` in place of `ε ∨ |η(x) − η(y)|`. When `|η(x) − η(y)| ≤ ε` and
     `dist(η(x), ∂D) = ε^β`, no scale is available and the middle term of (3.37) is negative, while its right-hand side
     `1 − A ε^{(1−β)ξ}` is positive for small ε. No counterexample to (3.30) itself is known.
   - (3.30) and (3.31) are claimed for all `x, y ∈ V(D)` (l. 1625, 1635), but Lemma 3.10 needs `x, y ∉ V(∂D)`, where
     the boundary data are arbitrary; at boundary vertices (3.30) is not proved by this argument.
   - In (3.39) the boundary vertices compared lie within `2t + |η(x) − η(y)| + 2 ε^q` of each other, where `ε^q`
     bounds the cell diameters; the term `ε^q` is dropped. With `t = (ε ∨ |η(x) − η(y)|)^{1/4}` it dominates when
     `q < 1/4`, which happens for γ > 2√2 − 2, so the exponent `(ξ ∧ χ)/4` of (3.33) is not supported. The proved
     exponent includes a term `qχ`.
   - At l. 1741 the first "≤" should be "≥".
   - None of this affects Theorem 1.5, whose exponent is existential; it is proved with interior vertices, the floor
     `ε^β`, and the boundary estimate of correction 2.
4. **Typos and ranges in (3.37) and (3.38) (l. 1705–1714, 1727–1736).**
   - `1 − p^N` should be `1 − (1 − p)^N`: `p` is a success probability, and all `N` attempts fail with probability at
     most `(1 − p)^N`.
   - The exponent of (3.38) is printed as `t/dist(η(x), ∂D) − 2`; as in (3.37), it should be the number of scales,
     about `log(t/dist(η(x), ∂D))` (verified in the PDF, p. 32: (3.37) prints the log and (3.38) does not).
   - The range of scales in (3.37) starts at a radius comparable to `dist(η(x), ∂D)`, so `B_{2r}(η(x))` need not lie in
     `D`; in (3.38) the largest radius is close to `t`, so the exit point need not lie in `B_t(η(x))`. A bounded number
     of scales must be dropped at each end, which changes only the constant `A`.
5. **Lemma 3.11 (l. 1666–1693).** The statement is true, and both its uses need graph disconnection: the walk's trace
   must meet every path in the graph from `y` to the target set. The proof does not deliver that.
   - "It is easily seen from Proposition 3.6 … three appropriately chosen arcs" (l. 1679–1682) does not give (3.36).
     The walk stays near the arcs but can leave the annulus before disconnecting. Coming close to each target point is
     not the same as closing a loop: the trace can spiral and form an arc. And a closed chain of visited cells can still
     be crossed by a graph path through two unvisited cells that touch the chain at a single point, since cells can
     meet at points without being adjacent.
   - The union bound (l. 1691–1693) also needs a grid approximation of an arbitrary annulus by a grid annulus, with
     margins for the cell size and the grid spacing (this uses β below the grid exponent), and a strong-Markov reduction
     to the first hit of the grid circle, not of `∂B_r(z)`, which is not a grid circle.
   - *Repair.* An itinerary estimate along a scaled and rotated polar template, from Lemma 3.8 and the chaining of
     Proposition 3.6, makes the walk cross the annulus radially and then make a full lap. A planar separation argument
     for the cells shows that such a trace disconnects the inner circle from the outer one in the graph. Then the grid
     approximation and the strong Markov property give (3.35) for every annulus, at every real ε.
6. **Other points in Sections 2–3.**
   - Lemma 3.8 (l. 1497–1589): Lemma 3.7's error term forces `β ≤ α₁/4` (not `β = α₁/2`, l. 1586), and the maximum
     principle uses connectivity of the cells along circles and segments; axis-parallel squares and segments reduce this
     to connectivity along lines, which holds for these cells.
   - Proposition 3.6 (l. 1387–1405, 1590–1613): in (3.29) the walk is confined to `B_{r+r₀}(P)`, not `B_r(P)`, and the
     proof needs `r − r̃ ≥ ε^β`, which the statement omits. Only an itinerary version is used here.
   - Lemma 3.7 (l. 1439–1490): the endpoints `t = sr` must be excluded so that the paths are compact subsets of `D`, and
     the radial family must not wrap around; angles in `[0, π]` suffice.
   - Lemma 3.4 (l. 1322–1350): (3.15) should read `A/log(ε⁻¹ ∧ s⁻¹)`; with `∨` it fails at `s = ρ/2` and at `s = 0`.
   - Lemma 3.1 (l. 1152–1158): `Σ_{x ∈ V(∂D)} diam(H_x)² ≤ area(B_{ε^q}(∂D))` does not follow, since a squared
     diameter is not bounded by an area; Proposition 2.10 applied to a smoothed indicator of a neighbourhood of `∂D`
     repairs it.
   - Theorem 1.4 (l. 1352–1376): the equality in the Dirichlet-principle step is an inequality "≥".
   - Definition 2.3 (l. 813–819): the drift should be `B_t + αt` for `t ≥ 0`, as in DMS Definitions 4.5 and 4.10.
   - Lemma 2.5 (l. 925–941): the "positive conditional probability" is not uniform (it depends on
     `L_τ − inf_{[−1,0]} L`); a stopping-time argument with independent blocks gives the stated tail.
   - Lemmas 2.7 and 2.8 (l. 982–1049): "mass ≥ ε" against "cell mass = ε" needs a strict sub-segment; the constant in
     the `δ/2` grid is absorbed by shrinking `p`; the cited GHM Lemma 3.12 has the form `δ ε^{2+γ²/2} e^{γ h_ε}`.

**Section 4 and Appendix A (the proof of Proposition 2.10).**

7. **Lemma 4.3 (l. 1931–1939): locality and measurability.** The localized quantities are defined at the first visit
   time `τ_z` ((4.2), l. 1790), and Lemma 4.3 is stated for each fixed `z`. The proofs of Propositions 4.8 and 4.10 use
   it inside spatial integrals, and at points that the curve visits several times the first-visit quantities are not
   local in the required sense. The formalization uses the corresponding quantities over all visits, which dominate the
   first-visit ones and have the same spatial integrals almost surely, because the set of multiply visited points has
   zero area. The probabilities of the events described by Lemma 4.3 also presuppose measurability; it is proved for the
   test data actually used (open or Borel domains, continuous or almost everywhere measurable test functions).
8. **Proposition 4.5 (l. 1983–2006): the order of α and ρ.** The statement introduces ρ before "There exists
   α = α(γ, q, ζ)", and only the annotation says that α does not depend on ρ. The proof does choose α before ρ, and
   Propositions 4.1, 4.10 and 2.10 (α = α(γ), l. 1076, 1770) need this. The formalization states Proposition 4.5 with
   α chosen first.
9. **Lemma 4.6 (l. 1903–1906, 2015–2069): the adjacency step.** `deg^ε_in` counts segments whose images merely
   intersect the root segment, but the proof (l. 2057–2066) treats the intersection as a non-trivial connected set and
   concludes that each segment meets a cell equal or adjacent to a root cell. Point contacts are not accounted for:
   cells can touch at a single point without sharing a boundary arc, and for γ ∈ (√(8/3), 2) (κ′ ∈ (4, 6)) the curve
   has a positive-dimensional set of points visited four times (GHM Corollary 6.5 with m = 4), at which cells can meet
   without being adjacent. The formalization uses the finite-visit property `visitBound` to join
   touching cells by short chains of adjacent cells. This gives a polylogarithmic bound with a larger fixed exponent,
   `2k(1+ζ) + 1` for the visit bound `k`, which suffices for Proposition 4.5. The printed exponent `1+ζ` is not proved.
10. **(4.16) (l. 2082–2116): a random normalization constant.** The Radon–Nikodym derivative between the
    `R`-circle-average embedding and the unit-normalized field is written as a deterministic Cameron–Martin shift with
    moments of all orders (l. 2091–2101). The two normalizations differ by a random Gaussian constant correlated with
    the harmonic part of the local field, so the displayed shift is not the density, and the all-orders claim does not
    follow. A Markov decomposition with a random-shift density gives a density in `L^p` for some `p > 1`, which suffices
    for the Hölder step. (The cited IG I Proposition 3.4 is also a statement on a domain.)
11. **Proposition 4.10, Case 3 (l. 2484–2518): the random mesh.** After subtracting `a = h²_{1/2}(z)`, the bound of
    Case 2 is applied "with `e^{γa}ε` in place of ε". A fixed-mesh bound integrated over a random mesh gives only an
    average over meshes, not the pointwise bound at mesh ε. The formalization avoids the random mesh: for the
    whole-plane GFF normalized by `h_1(0) = 0`, the field translated by `z` has the same law on `B_r(0)` whenever
    `|z| + r ≤ 1`, jointly with the re-rooted imaginary-geometry data, so the translated field has the cone's law at the
    same mesh. Separately, `S = e^{γ h²_{1/2}(z)}` in (4.41) should be `e^{−γ h²_{1/2}(z)}`, and correspondingly the
    mesh in the display after it should be `e^{γa}ε`, as the text says.
12. **Proposition 4.10, Case 4, (4.42) (l. 2519–2538).** From `h⁴(u) = h³(u/2 + z)`, the inverse change of coordinates
    is `u = 2(w − z)`, not `2(w + z)`; in the coordinate-change formula just before (4.42) (l. 2526–2532) the mesh should
    be `2^{γQ}ε`, i.e. `u^{3,ε}_*(·) = u^{4,2^{γQ}ε}_*(2(· − z))`, which makes the `c = 2^{−γQ}` of (4.42) correct; and
    the Jacobian of the change of variables is 4, not ½. (The formal proof translates at scale one, as in correction
    11.)
13. **Lemma 4.9 (l. 2229–2281): subtracting `(a₁, a₂)`.** Subtracting the constant `a₂` from the imaginary-geometry
    field (l. 2256–2258) rotates the flow-line angles by `a₂/χ`, so the curve of the recentred field is not `(η − z)/δ`
    and "in the same manner" fails for the curve. The localized quantities are invariant under this rotation, because
    whole-plane space-filling SLE is rotation invariant, so the conditional moments are unchanged; the argument also has
    to keep track of the uniform additive constant of the field.
14. **Proposition 4.8, (4.30) and (4.36) (l. 2307–2316, 2378–2387).** The first equality in (4.36) moves the indicator
    of the global event `E^ε` through a conditional expectation given `(h, h^IG)` outside `B_{ε^{q−4ζ}}(z)`; `E^ε` is not
    measurable with respect to that σ-algebra. The second moment is computed without the indicator, keeping the local
    events `F^ε(z)` inside the fluctuation: the near pairs contribute `O(ε^{2q−10ζ}‖f‖²_∞)` and the far pairs
    `O(ε^ζ‖f‖²_∞)`, and
    the bound with the indicator follows by monotonicity. The formal proof conditions on the circle averages of both
    fields and on the uniform constant of the imaginary-geometry field separately; this gives the same conditional mean
    almost surely. As stated in (4.22) and after (4.28) (l. 2195–2198, 2296–2298), the local quantity depends on the
    fields near `z` and on the two circle averages; the formal local factorization keeps both circle averages.
15. **Other points in Section 4 and Appendix A.**
    - (4.18) in Lemma 4.7 (l. 2121–2134): the lower bound on `diam(η([τ_z − ε, τ_z + ε]))` needs an upper bound on the
      LQG mass of small balls (for example GHS Lemma A.3 with a union bound); Lemma 2.8 gives a lower bound.
    - (4.27) (l. 2285–2289): `h^IG_{ε^{q−ζ}}(z)` should be `h^IG_{ε^{q−4ζ}}(z)`, the radius of (4.24), (4.25) and
      (4.28) (verified in the PDF, pp. 40–42; (4.27) is introduced "By (4.25)").
    - Several intermediate lemmas are formalized almost surely, for measurable versions, or with guards that exclude
      degenerate parameters. None of these reformulations occurs in a frozen statement or as a hypothesis.

**Citations.**

16. Theorem 4.4 (l. 1953–1954): the degree moments are GMS-T Proposition 4.6, not "4.5". Proposition 4.5's condition 2
    (l. 2152) needs [MS16b] Proposition 2.4, not Corollary 2.5. Lemma 2.6 (l. 946–959) cites [HS18, Proposition 6.2],
    which is for the Lebesgue parametrization; the LQG-parametrized statement is GHS Lemma A.4. Lemma A.4 cites
    [MS16d, Lemma 6.4], a local-set statement for a GFF on a domain; the needed whole-plane variance has a short direct
    proof. ([MS16b] = Miller–Sheffield, arXiv:1605.03563; [MS16d] = IG I; [HS18] = Holden–Sun, arXiv:1610.05272.)

## Cited inputs

No literature result is assumed beyond the bundle. Its SLE/LQG fields are the paper's setting (§1.4–§1.5, §2.1); every
other input is proved here or in an already released library.

| Input | Treatment |
| --- | --- |
| The boundary-length process is a correlated Brownian motion (DMS Theorem 1.9; GHMS Theorem 1.1 for κ′ > 8) | bundle field `boundaryLawBM` |
| Identification of times with the same point of the curve (DMS Lemmas 8.8, 8.9, 8.14) and finite visits (DMS Lemma 8.13) | bundle fields `merge`, `onlyMerge`, `visitBound` |
| Space-filling SLE as a measurable, local function of the imaginary-geometry field, and its coordinate change (IG I, IG IV, paper Lemma 2.4) | bundle field `igMap` |
| Space-filling and the Lebesgue parametrization (paper l. 883–885), transience (DMS Lemma 8.11); the parametrization by LQG area | bundle fields `spaceFilling`, `areaParam`, `areaParam₀` |
| The boundary-length process as a functional of `(h, η)` and its scaling | bundle field `boundaryLength` |
| GHM Proposition 3.4; GHS Lemma A.4; GMS-T Propositions 4.4 and 4.6 | bundle fields `segmentsContainBalls`, `coverage`, `cellMoments` |
| The laws of the GFFs, Brownian motions and imaginary-geometry field, and their independence | the bundle's data fields |
| SLE-free facts: the whole-plane GFF and its circle averages, LQG area measures and their moments, quantum cones and their scaling (DMS Proposition 4.13(i)), the rooting identity of DMS Lemma A.10, the circle-average bound of Miller–Sheffield, arXiv:1605.03563 ([MS16b]), Proposition 2.4, Brownian and Markov-chain facts, planar topology | proved in this library or in the released `LQGMetric`, `QuantumZipper` and `LQGDimension` libraries |
| Every lemma and proposition of the paper used by the proofs | proved here, several in corrected form (see above) |
| Lemma 3.10 (cited from arXiv:1807.07515, Lemma 3.12, proved there by Wilson's algorithm) | not taken as an input: the estimates it serves are proved here by maximum-principle arguments |
| The recurrence criterion of Gurel-Gurevich and Nachmias | not used: recurrence is proved from the energy estimates, as in the paper |

Theorem 1.16 of the companion paper arXiv:1807.07515 is formalized, in an interpolated-path formulation, in
[`results/gwynne-miller-sheffield`](../gwynne-miller-sheffield/README.md); the present library does not use it.

## How it was checked

The project follows Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills)
workflow.

1. **Planning.** Refute-first audits of §§2–4 and Appendix A of the paper, and of the proofs of the main results,
   before any statement was frozen. The defects they found are listed under "Corrections to the printed text".
2. **Statement.** The seven theorems, the definitions they use (the seven above and the earlier frozen definitions of
   the map, the multigraphs and the walk) and the bundle were frozen one declaration per file, pinned
   by a hash manifest (the bytes around each proof body and the elaborated types), after the independent statement
   audit of disclosure 14.
3. **Proof.** Each frozen theorem has a provider theorem with exactly its type; the frozen body is `by exact` the
   provider.
4. **Two-key seal.** A theorem is `PROVED` only after both keys.
   - Key 1: the frozen-anchor checker, the build, unchanged elaborated types and statement-closure fingerprint, and
     `#print axioms` with standard axioms only.
   - Key 2: an independent seal audit by auditors who did not write the statements or the proofs. It checked fidelity
     to the paper, that no proof step is smuggled in as a hypothesis, the provider chains, the use and meaning of every
     bundle field, the axioms, and a fresh kernel replay.
5. **Release checks.** On the release tree (the library staged onto the public `main`): all 752 modules
   of `MatedCRTHarmonic` were compiled from empty project artifacts against 3,346 released upstream modules
   whose compiled files are trace-linked to the public source bytes, with no error and no `sorry`; the statement
   comparison above was run on the compiled library; `Check.lean` reports only `propext`, `Classical.choice` and
   `Quot.sound` for each of the seven theorems; and the public source scan passes.

## What is in the library

The library `MatedCRTHarmonic` ships 752 Lean files: the import closure of the library root, which
imports the seven theorem files and the bundle. *Lines* are physical
lines; *code lines* are neither blank nor entirely inside comments.

| Part | Directories | Modules | Lines | Code lines |
| --- | --- | ---: | ---: | ---: |
| Graphs, random walk, harmonic functions, the discrete Dirichlet problem, Green's functions | `Markov`, `Harmonic`, `HarmonicInfinity`, `GoodScales`, `Growth`, `WalkSteps` | 18 | 4,298 | 2,994 |
| Mated-CRT maps, cells, cellular embeddings, planar topology and graph separation | `MatedCRT`, `CellularFacts`, `Infinite`, `Implementation`, `Core`, `Topology`, `Planar`, `RouteM`, `CellFamily`, `MesoGrid` | 78 | 20,278 | 16,444 |
| Gaussian free field, quantum cones, LQG area measures and their scaling | `MoTPort`, `GMCFacts`, `GMCUpper`, `ConeLemmaA10`, `ConeScaling`, `LQGCone`, `LQGCoord`, `IGLaw`, `Brownian` | 151 | 29,393 | 22,848 |
| Consequences of the bundle: the cell model and the identification of the map | `MoTInput`, `MesoModel`, `GMSCM` | 48 | 7,565 | 6,080 |
| §2 of the paper: degrees and cell diameters | `GMSLemma27`, `CellScaling` | 32 | 5,715 | 4,260 |
| §3: energy bounds, Green's function, recurrence, Hölder continuity, the Tutte embedding | `GMS3`, `GMSMain`, `Lemma38Source` | 77 | 20,228 | 15,531 |
| §4 and Appendix A: localized estimates and Propositions 2.10 and 4.1–4.10 | `GMS4`, `GMS4b`, `GMS4c`, `GMS4cM`, `GMS4cO`, `GMS4cP`, `GMS4cQ`, `GMS4cS`, `GMS4F`, `GMS4FO`, `GMS4O`, `GMSAppA`, `GMSCase`, `GMSCase1`, `BundleSec4`, `Canon` | 257 | 51,398 | 40,409 |
| **Proof modules** | | **661** | **138,875** | **108,566** |
| Frozen statements (the definitions, the bundle, the 7 theorems) | `Frozen` | 90 | 3,377 | 1,744 |
| Library root (imports the seven theorems and the bundle) | `MatedCRTHarmonic.lean` | 1 | 16 | 8 |
| **Total shipped** | | **752** | **142,268** | **110,318** |

The import closure of the shipped files also contains 3,346 modules of already released libraries,
unchanged: `QuantumZipper` (2,186), `LQGMetric` (1,030), `LQGDimension` (107) and `BouRabeeGwynne` (23).
Their results are proved in their libraries, not assumed. The proofs use declarations of the first three; the
`BouRabeeGwynne` modules are imported by one module of the library, and none of their results is used by the seven
theorems.

## About the source files

All files are derived from the development commit recorded in `source-manifest.json` (`source_commit`), with
these changes: the module root and namespace are renamed to `MatedCRTHarmonic`, and folders and declarations with
internal working names are renamed to descriptive names; the seven main theorems are named after the paper's
numbering; declarations that lie outside the scope of this release (those depending on development material that is
not shipped) are removed from the shipped modules; and comments and docstrings that referred to the development were
shortened or removed. Each module's manifest row records its SHA-256 and `release_transform`, and, for modules taken
from a development file, the SHA-256 of that file (`development_sha256`). Outside comments, the frozen files taken from
the development are identical to their development versions after the renaming (equal comment-free token streams,
checked mechanically). Named propositions inside the library are internal interfaces between proof steps: each one that the
proofs consume is the conclusion of a proved theorem, and none occurs in a frozen statement.

## Reproduce the checks

The toolchain is `leanprover/lean4:v4.34.0-rc2` and Mathlib is `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`; the included
`lake-manifest.json` pins the other dependencies. From the root of `leobon12/lean-formalizations`, with elan, Lake and
Python 3:

```sh
lake exe cache get
lake build MatedCRTHarmonic
lake env lean results/harmonic-functions-mated-crt-maps/Check.lean
python3 -I scripts/verify.py --scan-only
```

`Check.lean` runs `assert_no_sorry` and `#print axioms` on each of the seven theorems; every reported axiom must be one
of `propext`, `Classical.choice` and `Quot.sound`. `scripts/verify.py --scan-only` checks the selected module closure,
the source hashes, the import closure and forbidden proof tokens. `lake build MatedCRTHarmonic` compiles the library root,
which imports the seven theorem files and the bundle; `lake env leanchecker --fresh MatedCRTHarmonic` replays its
whole closure in a fresh kernel.

## Credits

The mathematics is due to Ewain Gwynne, Jason Miller and Scott Sheffield, *Harmonic functions on mated-CRT maps*,
arXiv:1807.07511. The inputs collected in the bundle are results of Duplantier, Miller and Sheffield; Gwynne, Holden,
Miller and Sun; Gwynne, Holden and Miller; Gwynne, Holden and Sun; Gwynne, Miller and Sheffield; and Miller and
Sheffield, cited above. Cite the Lean source snapshot by repository URL and release commit. The statements were frozen
and audited following Scott Armstrong's LeanAutoformalizationSkills workflow.

[All released formalizations](../../README.md)
