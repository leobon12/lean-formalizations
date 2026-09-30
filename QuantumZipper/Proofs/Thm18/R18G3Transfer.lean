import QuantumZipper.Proofs.Thm18.R18G3Defs
import QuantumZipper.Proofs.Thm18.R18G3Free

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5: the core from the free-field two-point limit and a transfer node

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71 (Proposition 5.5 at `x` and at `R(x)`
in the upper picture of Figure 1.7, and the GFF Markov property). The independence content is
proved for the free boundary GFF with a Palm point sampled from quantum length and its length
partner (`R18.g3FreeTwoPoint_holds`, the old G3 scheme without `G3TransferFullStmt`). What
remains is to compare the two Palm zoom schemes: `G3WedgeFreeTransferStmt` says that whatever
joint cylinder limit the free-field scheme has, the wedge scheme of step 5 (the
`(γ−2/γ)`-wedge `Y`, Palm point by quantum length within `U` of the root, zooms through the local
maps of the independent curve) has the same limit, up to `ε`, for all small windows.

Why it holds (plan for its proof, handoff/R18-PLAN.md §5): `Y` is the canonical (unit-area)
rescaling of the circle-average embedded wedge, which on the unit half-disc is the normalized free
field plus `(γ−2/γ)(−log|·|)`; the random dilation only shifts zoom levels by an a.s. finite amount;
small windows keep `x, R(x)` inside that half-disc; the smooth term and the local conformal maps change a zoom only by a level
shift and a dilation, which the canonical description and the limit `L → ∞` absorb (G0,
`g2ZoomLocStmt_holds`); the curve is independent of `Y` (Fubini).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Transfer node (step 5T).** Joint cylinder limits of the free-field Palm zoom scheme
(`g3PalmLaw`, `g3Uf`, `g3Vf`, `g3Filter`) carry over to the wedge Palm zoom scheme
(`g3zWedgePalmCyl`) for all small windows and all large zoom levels. -/
def G3WedgeFreeTransferStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ s ∈ lawCyl, ∀ t ∈ lawCyl, ∀ c : ℝ,
      Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ g3Vf γ i ⁻¹' t)) g3Filter
        (𝓝 c) →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ U : ℝ, 0 < U → U ≤ U₀ → ∀ᶠ L in atTop,
        (ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L s t ≤ ENNReal.ofReal c + ε ∧
          ENNReal.ofReal c ≤ (ENNReal.ofReal U)⁻¹ * g3zWedgePalmCyl γ P B Y U L s t + ε

/-- Arithmetic of step 5 from the transfer node: if `a ≈ x y`, `b' ≈ x`, `d' ≈ y` within `e`,
with `x, y ≤ 1`, `e ≤ 1`, `4 e ≤ ε`, then `a ≈ b' d'` within `ε`. Own elementary proof. -/
theorem g3_dec_arith {a b' d' x y e ε : ℝ≥0∞} (hx : x ≤ 1) (hy : y ≤ 1) (he : e ≤ 1)
    (hε : 4 * e ≤ ε) (h1 : a ≤ x * y + e) (h2 : x * y ≤ a + e) (h3 : b' ≤ x + e)
    (h4 : x ≤ b' + e) (h5 : d' ≤ y + e) (h6 : y ≤ d' + e) :
    a ≤ b' * d' + ε ∧ b' * d' ≤ a + ε := by
  have hb2 : b' * e ≤ 2 * e := by
    calc b' * e ≤ (x + e) * e := by gcongr
      _ ≤ (1 + 1) * e := by gcongr
      _ = 2 * e := by rw [one_add_one_eq_two]
  constructor
  · calc a ≤ x * y + e := h1
      _ ≤ (b' + e) * y + e := by gcongr
      _ = b' * y + e * y + e := by ring
      _ ≤ b' * (d' + e) + e * 1 + e := by gcongr
      _ = b' * d' + b' * e + e + e := by ring
      _ ≤ b' * d' + 2 * e + e + e := by gcongr
      _ = b' * d' + 4 * e := by ring
      _ ≤ b' * d' + ε := by gcongr
  · calc b' * d' ≤ (x + e) * (y + e) := by gcongr
      _ = x * y + x * e + e * y + e * e := by ring
      _ ≤ (a + e) + 1 * e + e * 1 + e * 1 := by gcongr
      _ = a + 4 * e := by ring
      _ ≤ a + ε := by gcongr

/-- **Step 5 from the transfer node** and the free-field two-point limit
(`R18.g3FreeTwoPoint_holds`): the transfer node is applied to `(s, t)`, `(s, univ)` and
`(univ, t)`, and the three approximations are combined by `g3_dec_arith`. -/
theorem g3WedgePalmDecStmt_of_transfer (hT : G3WedgeFreeTransferStmt) : G3WedgePalmDecStmt := by
  intro γ Ω _ P _ B Y hS hIn s hs t ht ε hε
  obtain ⟨μ, ν, hμ, hν, hlim⟩ := g3FreeTwoPoint_holds hS.1 hS.2.1
  set e : ℝ≥0∞ := min (ε / 4) 1 with he_def
  have he0 : 0 < e := lt_min (ENNReal.div_pos hε.ne' (by norm_num)) one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have he4 : 4 * e ≤ ε := by
    calc 4 * e ≤ 4 * (ε / 4) := by gcongr; exact min_le_left _ _
      _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  obtain ⟨hJ, -, -⟩ := hlim s hs t ht
  obtain ⟨hJs, -, -⟩ := hlim s hs univ univ_mem_lawCyl
  obtain ⟨hJt, -, -⟩ := hlim univ univ_mem_lawCyl t ht
  obtain ⟨U₁, hU₁, H₁⟩ := hT γ P B Y hS hIn s hs t ht _ hJ e he0
  obtain ⟨U₂, hU₂, H₂⟩ := hT γ P B Y hS hIn s hs univ univ_mem_lawCyl _ hJs e he0
  obtain ⟨U₃, hU₃, H₃⟩ := hT γ P B Y hS hIn univ univ_mem_lawCyl t ht _ hJt e he0
  have hpos : 0 < min U₁ (min U₂ U₃) := lt_min hU₁ (lt_min hU₂ hU₃)
  refine ⟨min U₁ (min U₂ U₃), hpos, ?_⟩
  filter_upwards [H₁ _ hpos (min_le_left _ _),
    H₂ _ hpos ((min_le_right _ _).trans (min_le_left _ _)),
    H₃ _ hpos ((min_le_right _ _).trans (min_le_right _ _))] with L h1 h2 h3
  have hx : ENNReal.ofReal (μ.real s * ν.real univ) ≤ 1 := by
    rw [probReal_univ, mul_one]
    exact ENNReal.ofReal_le_one.2 measureReal_le_one
  have hy : ENNReal.ofReal (μ.real univ * ν.real t) ≤ 1 := by
    rw [probReal_univ, one_mul]
    exact ENNReal.ofReal_le_one.2 measureReal_le_one
  have hxy : ENNReal.ofReal (μ.real s * ν.real t) =
      ENNReal.ofReal (μ.real s * ν.real univ) * ENNReal.ofReal (μ.real univ * ν.real t) := by
    rw [probReal_univ, probReal_univ, mul_one, one_mul]
    exact ENNReal.ofReal_mul measureReal_nonneg
  rw [hxy] at h1
  exact g3_dec_arith hx hy he1 he4 h1.1 h1.2 h2.1 h2.2 h3.1 h3.2

end R18
end QuantumZipper
