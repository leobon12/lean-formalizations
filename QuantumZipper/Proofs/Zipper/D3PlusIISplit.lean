import QuantumZipper.Proofs.Zipper.D3PlusStmt

/-!
# D3⁺(ii) (LSC): splitting into a constant level shift and a correction vanishing at `0`

Task D3P-II (decision D23; statement `D3Plus.D3PlusIIStmt`, `D3PlusStmt.lean`). Blueprint
`E_BRANCH_BLUEPRINT.md` §3 (D3⁺(ii): "LSC follows from asymptotic independence of `canonical` and
`log scaleParam` (spread `≍ √L`, hitting time of a BM with drift)"), decision D24 (a harmonic
perturbation near `0` has Dirichlet energy on `B(0, aR)` tending to `0` as `a → 0`, so its TV cost
tends to `0` by Cameron–Martin: Berestycki–Powell, *GFF and LQG*, arXiv:2004.04720, Lemmas 3.12,
3.14, p. 79). Paper: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25: near the marked point
the smooth part is "approximately constant").

Everything is stated for a general local reading `rd : ℕ → FieldSample → E` of the canonical
field (`zoomGen rd`, `LSCGen rd`); `rd = TV.locField` is D23's `D3PlusIIStmt`
(`lscGen_locField_iff`), `rd = locFieldFull` is D25's `D3PlusIIStmtRich` (`D3PlusIIRich.lean`).
Two corrections `g, g'` with `|g − g'| ≤ K` are compared through the intermediate correction
`g'' = g + (g'(0) − g(0))`:

* `g ↦ g''` adds the `condSigma`-measurable constant `c = g'(0) − g(0)`, `|c| ≤ K`; by
  `zoomGen_add_const` this is the **level shift** `L ↦ L + γ c` (`LSCConstGen`: the
  `√L`-spread / hitting-time part);
* `g'' ↦ g'` is a perturbation **vanishing at `0`** with `|g'' − g'| ≤ 2K`
  (`LSCZeroGen`: the Cameron–Martin part).

`lscGen_of_const_zero : LSCConstGen rd → LSCZeroGen rd → LSCGen rd` (triangle inequality for the
two-sided bounds; own elementary argument). Both parts are special cases of `LSCGen rd`
(`lscConstGen_of_lscGen`, `lscZeroGen_of_lscGen`), so the split loses nothing.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The level-shift identity -/

/-- Adding a constant `c` to the correction is the level shift `L ↦ L + γ c`. -/
theorem zoomModel_add_const {γ : ℝ} (hγ : γ ≠ 0) (α L : ℝ) (ρ₀ : Measure ℂ) (x : FieldSample)
    (g : ℂ → ℝ) (c : ℝ) :
    zoomModel γ α L ρ₀ x (fun z => g z + c) = zoomModel γ α (L + γ * c) ρ₀ x g := by
  unfold zoomModel
  congr 2
  funext z
  field_simp
  ring

/-- **The zoomed pair for a general local reading** `rd R : FieldSample → E` of the canonical
field: `(rd R (canonicalOn γ Y_L (halfDisc r)), log (scaleParamOn γ Y_L (halfDisc r)))`.
`zoomPair` is the case `rd = TV.locField` (`zoomPair_eq_zoomGen`); D25's `zoomPairRich` is the
case `rd = locFieldFull` (`D3PlusIIRich.lean`). -/
def zoomGen {E : Type} (rd : ℕ → FieldSample → E) (γ α L r : ℝ) (R : ℕ) (ρ₀ : Measure ℂ)
    (x : FieldSample) (g : ℂ → ℝ) : E × ℝ :=
  (rd R (canonicalOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r)),
    Real.log (scaleParamOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r)))

theorem zoomGen_add_const {E : Type} (rd : ℕ → FieldSample → E) {γ : ℝ} (hγ : γ ≠ 0)
    (α L r : ℝ) (R : ℕ) (ρ₀ : Measure ℂ) (x : FieldSample) (g : ℂ → ℝ) (c : ℝ) :
    zoomGen rd γ α L r R ρ₀ x (fun z => g z + c) = zoomGen rd γ α (L + γ * c) r R ρ₀ x g := by
  simp only [zoomGen, zoomModel_add_const hγ]

/-- `Setup` is stable under adding a `condSigma`-measurable random constant to the correction. -/
theorem Setup.add_const {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E'] {Ξ : Ω → E'}
    {g : Ω → ℂ → ℝ} (hS : Setup γ α r ρ₀ P X Ξ g) {c : Ω → ℝ}
    (hc : Measurable[condSigma Ξ X r] c) :
    Setup γ α r ρ₀ P X Ξ (fun ω z => g ω z + c ω) where
  hγ := hS.hγ
  hγ2 := hS.hγ2
  hα := hS.hα
  hr := hS.hr
  hX := hS.hX
  hΞ := hS.hΞ
  hind := hS.hind
  hρ := hS.hρ
  hρ1 := hS.hρ1
  hρB := hS.hρB
  harm := fun ω => (hS.harm ω).add (InnerProductSpace.harmonicOnNhd_const (c ω))
  gmeas := fun z => Measurable.add (m := condSigma Ξ X r) (hS.gmeas z) hc

/-! ## The generic LSC statement and its two special cases -/

/-- **D3⁺(ii) for a general local reading `rd`** (`D3PlusIIStmt` with `zoomPair` replaced by
`zoomGen rd`; `lscGen_locField_iff`: for `rd = TV.locField` it is `D3PlusIIStmt`). -/
def LSCGen {E : Type} [MeasurableSpace E] (rd : ℕ → FieldSample → E) : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g g' : Ω → ℂ → ℝ) (K : ℝ),
    Setup γ α r ρ₀ P X Ξ g → Setup γ α r ρ₀ P X Ξ g' →
    (∀ ω, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g ω z - g' ω z| ≤ K) →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × (E × ℝ) → ℝ≥0∞, Measurable[(condSigma Ξ X r).prod inferInstance] Φ →
        (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, zoomGen rd γ α L r R ρ₀ (X ω) (g ω)) ∂P
        let rhs := ∫⁻ ω, Φ (ω, zoomGen rd γ α L r R ρ₀ (X ω) (g' ω)) ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

/-- **Constant part (level-shift continuity)** for a reading `rd`: under `Setup` for `g` and a
`condSigma`-measurable random constant `c` with `|c| ≤ K`, the conditional laws of `zoomGen rd` at
the levels `L` and `L + γ c` are TV-close as `L → ∞`, uniformly over `condSigma ⊗ Borel`-measurable
`Φ ∈ [0,1]`. (By `zoomGen_add_const`, this is `LSCGen rd` for `g' = g + c`.) -/
def LSCConstGen {E : Type} [MeasurableSpace E] (rd : ℕ → FieldSample → E) : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g : Ω → ℂ → ℝ) (c : Ω → ℝ) (K : ℝ),
    Setup γ α r ρ₀ P X Ξ g → Measurable[condSigma Ξ X r] c → (∀ ω, |c ω| ≤ K) →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × (E × ℝ) → ℝ≥0∞, Measurable[(condSigma Ξ X r).prod inferInstance] Φ →
        (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, zoomGen rd γ α L r R ρ₀ (X ω) (g ω)) ∂P
        let rhs := ∫⁻ ω, Φ (ω, zoomGen rd γ α (L + γ * c ω) r R ρ₀ (X ω) (g ω)) ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

/-- **Part vanishing at `0` (Cameron–Martin part)** for a reading `rd`: `LSCGen rd` under the
extra hypothesis `g ω 0 = g' ω 0` for every `ω`. -/
def LSCZeroGen {E : Type} [MeasurableSpace E] (rd : ℕ → FieldSample → E) : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g g' : Ω → ℂ → ℝ) (K : ℝ),
    Setup γ α r ρ₀ P X Ξ g → Setup γ α r ρ₀ P X Ξ g' →
    (∀ ω, g ω 0 = g' ω 0) →
    (∀ ω, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g ω z - g' ω z| ≤ K) →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × (E × ℝ) → ℝ≥0∞, Measurable[(condSigma Ξ X r).prod inferInstance] Φ →
        (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, zoomGen rd γ α L r R ρ₀ (X ω) (g ω)) ∂P
        let rhs := ∫⁻ ω, Φ (ω, zoomGen rd γ α L r R ρ₀ (X ω) (g' ω)) ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

section Gen

variable {E : Type} [MeasurableSpace E] {rd : ℕ → FieldSample → E}

theorem two_sided_trans {a b c η : ℝ≥0∞} (h1 : a ≤ b + η / 2 ∧ b ≤ a + η / 2)
    (h2 : b ≤ c + η / 2 ∧ c ≤ b + η / 2) : a ≤ c + η ∧ c ≤ a + η := by
  constructor
  · calc a ≤ b + η / 2 := h1.1
      _ ≤ c + η / 2 + η / 2 := by gcongr; exact h2.1
      _ = c + η := by rw [add_assoc, ENNReal.add_halves]
  · calc c ≤ b + η / 2 := h2.2
      _ ≤ a + η / 2 + η / 2 := by gcongr; exact h1.2
      _ = a + η := by rw [add_assoc, ENNReal.add_halves]

/-- **LSC from its constant part and its part vanishing at `0`** (own elementary argument: the
intermediate correction `g + (g'(0) − g(0))` and the triangle inequality). -/
theorem lscGen_of_const_zero (hC : LSCConstGen rd) (hZ : LSCZeroGen rd) : LSCGen rd := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g g' K hS hS' hK R η hη
  have hγ : γ ≠ 0 := hS.hγ.ne'
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r ∩ Hbar :=
    ⟨Metric.mem_ball_self hS.hr, show (0 : ℝ) ≤ (0 : ℂ).im by simp⟩
  set c : Ω → ℝ := fun ω => g' ω 0 - g ω 0 with hc_def
  have hcm : Measurable[condSigma Ξ X r] c :=
    Measurable.sub (m := condSigma Ξ X r) (hS'.gmeas 0) (hS.gmeas 0)
  have hcK : ∀ ω, |c ω| ≤ K := fun ω => by
    rw [hc_def, abs_sub_comm]; exact hK ω 0 h0
  set g'' : Ω → ℂ → ℝ := fun ω z => g ω z + c ω with hg''
  have hS'' : Setup γ α r ρ₀ P X Ξ g'' := hS.add_const hcm
  have h0'' : ∀ ω, g'' ω 0 = g' ω 0 := fun ω => by simp [hg'', hc_def]
  have hK'' : ∀ ω, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g'' ω z - g' ω z| ≤ K + K :=
    fun ω z hz => by
      have e : g'' ω z - g' ω z = (g ω z - g' ω z) + c ω := by simp only [hg'']; ring
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add (hK ω z hz) (hcK ω))
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hA := hC γ α r ρ₀ P X Ξ g c K hS hcm hcK R (η / 2) hη2
  have hB := hZ γ α r ρ₀ P X Ξ g'' g' (K + K) hS'' hS' h0'' hK'' R (η / 2) hη2
  filter_upwards [hA, hB] with L hLA hLB Φ hΦ h1
  have eA : ∀ ω, zoomGen rd γ α (L + γ * c ω) r R ρ₀ (X ω) (g ω) =
      zoomGen rd γ α L r R ρ₀ (X ω) (g'' ω) := fun ω =>
    (zoomGen_add_const rd hγ α L r R ρ₀ (X ω) (g ω) (c ω)).symm
  have hA' := hLA Φ hΦ h1
  simp only [eA] at hA'
  exact two_sided_trans hA' (hLB Φ hΦ h1)

end Gen

end D3Plus
end QuantumZipper
