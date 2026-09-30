import QuantumZipper.Proofs.Thm18.G2FixMixRoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2, `x` side: Sheffield's smoothing step (cut length `ν_h[x + κ, 0]`)

`G2FixMixRootXStmt γ μ` (`G2FixMixRoot.lean`) conditions the zoom at the rooted point `x` on the
field outside the two regions **and the length `ν_h[x, 0]`**. That length depends on the field
arbitrarily close to `x`, so D3⁺(i) (conditioning on the field outside a small ball `B_κ(x)`)
does not apply to it directly. Sheffield (arXiv:1012.4797, proof of Proposition 5.5, pp. 65–66)
handles this in two steps, which we follow:

1. **Cut length** (`G2RootXCutStmt`; `κ` is Sheffield's `ε̄`): replace `ν_h[x, 0]` by `ν_h[x + κ, 0]`, a function of the
   field outside `B_κ(x)`. With this conditioning the statement is Proposition 1.6 at a rooted
   point with the field outside `B_κ(x)` frozen, i.e. D3⁺(i) after the Palm identity
   (Duplantier–Sheffield, arXiv:0808.1560, §3.3: given `x`, `h` is a GFF plus
   `−γ log|x − ·|` plus a harmonic function).
2. **Smoothing** (`G2RootXLenSmoothStmt`, Sheffield p. 66): writing `h = α₁ φ₁ + h₀` for a bump
   `φ₁` supported in region 1 between `x + κ` and the region's right end, given `h₀` the cut
   length is a smooth strictly increasing function of the Gaussian `α₁`, hence has a smooth
   density; the difference `ν_h[x, x + κ)` is a function of `h₀` tending to `0` in probability as
   `κ → 0`; and for large `C` the zoom only reads `h₀` near `x`. Hence the two conditionings
   differ in total variation by `o(1)` as `κ → 0`, eventually in `C`.

`g2FixMixRootXStmt_of_cut : G2RootXLenSmoothStmt γ → G2RootXCutStmt γ μ → G2FixMixRootXStmt γ μ`
is the triangle inequality
`|R(A∩E) − μ(s)R(E)| ≤ |R(A∩E) − R(A∩E_κ)| + |R(A∩E_κ) − μ(s)R(E_κ)| + μ(s)|R(E_κ) − R(E)|`
(own elementary bookkeeping; the two nodes are Sheffield's two steps).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The **cut length** `ν_h[x + κ, 0]` (a function of the field outside `B_κ(x)`). -/
def g3CutLen (γ κ : ℝ) (ω : Ω₀) (x : ℝ) : ℝ := (g3Hν γ ω (Icc (x + κ) 0)).toReal

/-- The rooted event `{zoom at x ∈ s, x a margin m inside region 1, (h, ν_h[x+κ,0]) ∈ G}`. -/
def g3RootEvXc (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, g3CutLen γ κ q.1 q.2.2) ∈ G}

/-- The rooted event `{x a margin m inside region 1, (h, ν_h[x+κ,0]) ∈ G}`. -/
def g3RootEvXc0 (γ : ℝ) (i : G3Idx) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) : Set (Ω₀ × ℝ × ℝ) :=
  {q | |q.2.2 - i.t₁| + m < i.r₁ ∧ (q.1, g3CutLen γ κ q.1 q.2.2) ∈ G}

theorem g3RootEvX_univ (γ : ℝ) (i : G3Idx) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvX γ i univ m G = g3RootEvX0 i m G := by
  ext q; simp [g3RootEvX, g3RootEvX0]

theorem g3RootEvXc_univ (γ : ℝ) (i : G3Idx) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvXc γ i univ m κ G = g3RootEvXc0 γ i m κ G := by
  ext q; simp [g3RootEvXc, g3RootEvXc0]

/-- **Node 1 (cut length; Proposition 1.6 at a rooted point with the field outside `B_κ(x)`
frozen).** For every `0 < κ < m`: under the rooted measure, the zoom at `x` (a margin `m` inside
region 1) is asymptotically independent, as `C → ∞` and uniformly in `G`, of the field outside
the two regions together with the cut length `ν_h[x + κ, 0]`, with limit law `μ`
(Sheffield, arXiv:1012.4797, Prop. 1.6, p. 24, and proof of Prop. 5.5, p. 65; D3⁺(i) after the
Palm identity of Duplantier–Sheffield, arXiv:0808.1560, §3.3). -/
def G2RootXCutStmt (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ),
    ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvXc γ i s m κ G).indicator 1)).toReal -
        μ.real s * (g3RootInt γ i ((g3RootEvXc0 γ i m κ G).indicator 1)).toReal| ≤ ε

/-- **Node 2 (smoothing of the length coordinate; Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66).** Replacing the length `ν_h[x, 0]` by the cut length `ν_h[x + κ, 0]` in the
conditioning changes the rooted measure of `{zoom ∈ s} ∩ {margin} ∩ {(h, length) ∈ G}` by at most
`ε`, uniformly in `G`, for all small `κ`, eventually in `C`. -/
def G2RootXLenSmoothStmt (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ε₀ > 0, ∀ κ ∈ Ioo 0 ε₀,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvX γ i s m G).indicator 1)).toReal -
        (g3RootInt γ i ((g3RootEvXc γ i s m κ G).indicator 1)).toReal| ≤ ε

/-- The real triangle inequality behind the assembly. -/
theorem abs_sub_mul_le_of_three {a a' b b' c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h1 : |a - a'| ≤ ε / 3) (h2 : |a' - c * b'| ≤ ε / 3) (h3 : |b - b'| ≤ ε / 3) :
    |a - c * b| ≤ ε := by
  have e : a - c * b = (a - a') + (a' - c * b') + c * (b' - b) := by ring
  rw [e]
  have h3' : |c * (b' - b)| ≤ ε / 3 := by
    rw [abs_mul, abs_of_nonneg hc0, abs_sub_comm]
    calc c * |b - b'| ≤ 1 * |b - b'| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      _ ≤ ε / 3 := by rw [one_mul]; exact h3
  calc |(a - a') + (a' - c * b') + c * (b' - b)|
      ≤ |(a - a') + (a' - c * b')| + |c * (b' - b)| := abs_add_le _ _
    _ ≤ |a - a'| + |a' - c * b'| + |c * (b' - b)| := by gcongr; exact abs_add_le _ _
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-- **`G2FixMixRootXStmt` from Sheffield's two steps** (cut length + smoothing). -/
theorem g2FixMixRootXStmt_of_cut {γ : ℝ} {μ : Measure LawD} [IsProbabilityMeasure μ]
    (hS : G2RootXLenSmoothStmt γ) (hC : G2RootXCutStmt γ μ) : G2FixMixRootXStmt γ μ := by
  intro s hs δ η m hm ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨ε₁, hε₁, h₁⟩ := hS s hs δ η m hm (ε / 3) hε3
  obtain ⟨ε₂, hε₂, h₂⟩ := hS univ univ_mem_lawCyl δ η m hm (ε / 3) hε3
  set κ : ℝ := min (min ε₁ ε₂) m / 2 with hκ
  have hmin : 0 < min (min ε₁ ε₂) m := lt_min (lt_min hε₁ hε₂) hm
  have hκ0 : 0 < κ := by positivity
  have hκlt : κ < min (min ε₁ ε₂) m := by rw [hκ]; linarith
  have hκ1 : κ < ε₁ := hκlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hκ2 : κ < ε₂ := hκlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hκm : κ < m := hκlt.trans_le (min_le_right _ _)
  filter_upwards [h₁ κ ⟨hκ0, hκ1⟩, h₂ κ ⟨hκ0, hκ2⟩, hC s hs δ η m κ hκ0 hκm (ε / 3) hε3]
    with C hC₁ hC₂ hC₃ i hi G hG
  have a1 := hC₁ i hi G hG
  have a2 := hC₃ i hi G hG
  have a3 := hC₂ i hi G hG
  rw [g3RootEvX_univ, g3RootEvXc_univ] at a3
  exact abs_sub_mul_le_of_three measureReal_nonneg measureReal_le_one a1 a2 a3

end Thm18Asm
end QuantumZipper
