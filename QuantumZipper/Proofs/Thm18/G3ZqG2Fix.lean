import QuantumZipper.Proofs.Thm18.G2RootRCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 engine with an abstract zoom: fixed regions, length root, rooted form, cut nodes

Generalized copy (D92) of `G2FullMixGeo.lean` (only `G2FixMixStmt`), `G2FixMixLen.lean`,
`G2FixMixRoot.lean`, `G2FixMixRootR.lean`, `G2RootXCut.lean` and `G2RootRCut.lean`, in which the
plain zoom `zoomLaw γ C` is replaced by abstract zooms `Z` (at `x`) and `Z'` (at `R(x)`),
`Z C h y : LawD` for level `C`, field `h` and point `y`. The plain engine is the instance
`Z = Z' = zoomLaw γ`. The only property of the zoom the proofs use is the joint measurability
`Measurable fun q : FieldSample × ℝ => Z C q.1 q.2` (where the originals use
`measurable_zoomLaw`). All zoom-free lemmas (length-rooted measure, change of variables, rooted
measures, zoom-free events, triangle inequalities) are reused from the originals.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66 (and proof of Thm. 1.8, p. 71).
Own elementary bookkeeping (AGENT_GUIDE cost rule), copied from the committed originals.

* `G2FixMixStmtZ`, `G2FixMixLenXStmtZ`, `G2FixMixLenRStmtZ`, `g2FixMixStmtZ_of_len`;
* `g3RootEvXZ`, `G2FixMixRootXStmtZ`, `g2FixMixLenXZ_of_root` and the `R` side;
  `g2FixMixStmtZ_of_root`;
* `g3RootEvXcZ`, `G2RootXCutStmtZ`, `G2RootXLenSmoothStmtZ`, `g2FixMixRootXStmtZ_of_cut` and the
  `R` side; headline `g2FixMixStmtZ_of_cutNodes`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

section ZoomAbs

variable (Z Z' : ℝ → FieldSample → ℝ → LawD)

/-- The abstract zoom of the full field at the Palm point `x`. -/
def g3UfZ (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : LawD :=
  Z i.C (normField γ gffBase.X p.1) (g3X γ i p)

/-- The abstract zoom of the full field at the length partner `R(x)`. -/
def g3VfZ (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : LawD :=
  Z i.C (normField γ gffBase.X p.1) (g3R γ i p)

/-! ## Fixed regions (copy of `G2FixMixStmt`, `G2FullMixGeo.lean`) -/

/-! ## Length-rooted form (copy of `G2FixMixLen.lean`) -/

/-- `G2FixMixLenXStmt` with the abstract zoom `Z`. -/
def G2FixMixLenXStmtZ (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3LenRoot γ i).real (g3UfZ Z γ i ⁻¹' s ∩ {p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G) -
        μ.real s * (g3LenRoot γ i).real ({p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G)| ≤ ε

/-- `G2FixMixLenRStmt` with the abstract zoom `Z'`. -/
def G2FixMixLenRStmtZ (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3LenRoot γ i).real (g3VfZ Z' γ i ⁻¹' t ∩ {p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G) -
        ν.real t * (g3LenRoot γ i).real ({p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G)| ≤ ε

variable {Z Z'}

variable (Z Z')

/-! ## Rooted form (copy of `G2FixMixRoot.lean`, `G2FixMixRootR.lean`) -/

/-- `g3RootEvX` with the abstract zoom `Z`. -/
def g3RootEvXZ (γ : ℝ) (i : G3Idx) (s : Set LawD) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, q.2.1) ∈ G}

/-- `G2FixMixRootXStmt` with the abstract zoom `Z`. -/
def G2FixMixRootXStmtZ (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvXZ Z γ i s m G).indicator 1)).toReal -
        μ.real s * (g3RootInt γ i ((g3RootEvX0 i m G).indicator 1)).toReal| ≤ ε

/-- `g3RootEvR` with the abstract zoom `Z'`. -/
def g3RootEvRZ (γ : ℝ) (i : G3Idx) (t : Set LawD) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z' i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, q.2.1) ∈ G}

/-- `G2FixMixRootRStmt` with the abstract zoom `Z'`. -/
def G2FixMixRootRStmtZ (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvRZ Z' γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
        ν.real t * (g3RootIntR γ i ((g3RootEvR0 i m G ∩ g3TM γ i).indicator 1)).toReal| ≤ ε

variable {Z Z'}

theorem measurableSet_g3RootEvXZ (hZ : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) : MeasurableSet (g3RootEvXZ Z γ i s m G) :=
  ((hZ i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) hs).inter (measurableSet_g3RootEvX0 i m hG)

theorem measurableSet_g3RootEvRZ (hZ : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) : MeasurableSet (g3RootEvRZ Z' γ i t m G) :=
  ((hZ i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) ht).inter (measurableSet_g3RootEvR0 i m hG)

/-- **The `x`-side length-rooted node from the rooted node** (abstract zoom). -/
theorem g2FixMixLenXZ_of_root (hZ : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Measure LawD}
    (h : G2FixMixRootXStmtZ Z γ μ) : G2FixMixLenXStmtZ Z γ μ := by
  intro s hs δ η m hm ε hε
  filter_upwards [h s hs δ η m hm ε hε] with C hC i hi G hG
  have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
  have e1 : g3UfZ Z γ i ⁻¹' s ∩ {p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G =
      {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvXZ Z γ i s m G} := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, g3RootEvXZ, g3UfZ, Prod.mk.eta]
    tauto
  have e2 : {p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G =
      {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvX0 i m G} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, g3RootEvX0, Prod.mk.eta]
  have r1 : (g3LenRoot γ i).real {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvXZ Z γ i s m G} =
      (g3RootInt γ i ((g3RootEvXZ Z γ i s m G).indicator 1)).toReal := by
    rw [measureReal_def, g3LenRoot_rooted hγ hγ2 i
      (measurableSet_g3RootEvXZ hZ γ i (measurableSet_lawCyl hs) m hGm)]
  have r2 : (g3LenRoot γ i).real {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvX0 i m G} =
      (g3RootInt γ i ((g3RootEvX0 i m G).indicator 1)).toReal := by
    rw [measureReal_def, g3LenRoot_rooted hγ hγ2 i (measurableSet_g3RootEvX0 i m hGm)]
  rw [e1, e2, r1, r2]
  exact hC i hi G hG

/-- **The `R`-side length-rooted node from the rooted node** (abstract zoom). -/
theorem g2FixMixLenRZ_of_root (hZ : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ν : Measure LawD}
    (h : G2FixMixRootRStmtZ Z' γ ν) : G2FixMixLenRStmtZ Z' γ ν := by
  intro t ht δ η m hm ε hε
  filter_upwards [h t ht δ η m hm ε hε] with C hC i hi G hG
  have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
  by_cases hmr : m < i.r₂
  · have ha : 0 < i.t₂ - i.r₂ + m := by rw [i.t₂_sub_r₂]; linarith [i.hη]
    have hb0 : 0 < i.t₂ + i.r₂ - m := by linarith [i.t₂_add_r₂, i.hη]
    have hb : i.t₂ + i.r₂ - m < i.t₂ + i.r₂ := by linarith
    have e1 : g3VfZ Z' γ i ⁻¹' t ∩ {p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G =
        {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvRZ Z' γ i t m G} := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, g3RootEvRZ, g3VfZ, Prod.mk.eta]
      tauto
    have e2 : {p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G =
        {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvR0 i m G} := by
      ext p
      simp only [mem_inter_iff, mem_ofPred_eq, g3RootEvR0, Prod.mk.eta]
    have r1 : (g3LenRoot γ i).real {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvRZ Z' γ i t m G} =
        (g3RootIntR γ i ((g3RootEvRZ Z' γ i t m G ∩ g3TM γ i).indicator 1)).toReal := by
      rw [measureReal_def, g3LenRoot_rootedR hγ hγ2 i
        (measurableSet_g3RootEvRZ hZ γ i (measurableSet_lawCyl ht) m hGm) ha hb0 hb
        (fun q hq => g3RootEvR0_sub i m G q hq.2)]
    have r2 : (g3LenRoot γ i).real {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvR0 i m G} =
        (g3RootIntR γ i ((g3RootEvR0 i m G ∩ g3TM γ i).indicator 1)).toReal := by
      rw [measureReal_def, g3LenRoot_rootedR hγ hγ2 i (measurableSet_g3RootEvR0 i m hGm) ha hb0 hb
        (g3RootEvR0_sub i m G)]
    rw [e1, e2, r1, r2]
    exact hC i hi G hG
  · have hE : {p : Ω₀ × ℝ | |g3R γ i p - i.t₂| + m < i.r₂} = ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      linarith [abs_nonneg (g3R γ i p - i.t₂), not_lt.1 hmr]
    rw [hE, inter_empty, empty_inter]
    simp only [measureReal_empty, mul_zero, sub_zero, abs_zero]
    exact hε.le

variable (Z Z')

/-! ## Cut nodes (copy of `G2RootXCut.lean`, `G2RootRCut.lean`) -/

/-- `g3RootEvXc` with the abstract zoom `Z`. -/
def g3RootEvXcZ (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, g3CutLen γ κ q.1 q.2.2) ∈ G}

/-- `g3RootEvRc` with the abstract zoom `Z'`. -/
def g3RootEvRcZ (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z' i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, g3CutLenR γ κ q.1 q.2.2) ∈ G ∧ ENNReal.ofReal (g3CutLenR γ κ q.1 q.2.2) ≤ g3Mass γ i q.1}

theorem g3RootEvXZ_univ (γ : ℝ) (i : G3Idx) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvXZ Z γ i univ m G = g3RootEvX0 i m G := by
  ext q; simp [g3RootEvXZ, g3RootEvX0]

theorem g3RootEvXcZ_univ (γ : ℝ) (i : G3Idx) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvXcZ Z γ i univ m κ G = g3RootEvXc0 γ i m κ G := by
  ext q; simp [g3RootEvXcZ, g3RootEvXc0]

theorem g3RootEvRZ_univ (γ : ℝ) (i : G3Idx) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvRZ Z' γ i univ m G = g3RootEvR0 i m G := by
  ext q; simp [g3RootEvRZ, g3RootEvR0]

theorem g3RootEvRcZ_univ (γ : ℝ) (i : G3Idx) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvRcZ Z' γ i univ m κ G = g3RootEvRc0 γ i m κ G := by
  ext q; simp [g3RootEvRcZ, g3RootEvRc0]

/-- `G2RootXCutStmt` (node 1, cut length) with the abstract zoom `Z`. -/
def G2RootXCutStmtZ (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ),
    ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvXcZ Z γ i s m κ G).indicator 1)).toReal -
        μ.real s * (g3RootInt γ i ((g3RootEvXc0 γ i m κ G).indicator 1)).toReal| ≤ ε

/-- `G2RootXLenSmoothStmt` (node 2, smoothing) with the abstract zoom `Z`. -/
def G2RootXLenSmoothStmtZ (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ε₀ > 0, ∀ κ ∈ Ioo 0 ε₀,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvXZ Z γ i s m G).indicator 1)).toReal -
        (g3RootInt γ i ((g3RootEvXcZ Z γ i s m κ G).indicator 1)).toReal| ≤ ε

/-- `G2RootRCutStmt` (node 1, `R` side) with the abstract zoom `Z'`. -/
def G2RootRCutStmtZ (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ),
    ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvRcZ Z' γ i t m κ G).indicator 1)).toReal -
        ν.real t * (g3RootIntR γ i ((g3RootEvRc0 γ i m κ G).indicator 1)).toReal| ≤ ε

/-- `G2RootRLenSmoothStmt` (node 2, `R` side) with the abstract zoom `Z'`. -/
def G2RootRLenSmoothStmtZ (γ : ℝ) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ε₀ > 0, ∀ κ ∈ Ioo 0 ε₀,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvRZ Z' γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
        (g3RootIntR γ i ((g3RootEvRcZ Z' γ i t m κ G).indicator 1)).toReal| ≤ ε

variable {Z Z'}

/-- **`G2FixMixRootXStmtZ` from Sheffield's two steps** (cut length + smoothing). -/
theorem g2FixMixRootXStmtZ_of_cut {γ : ℝ} {μ : Measure LawD} [IsProbabilityMeasure μ]
    (hS : G2RootXLenSmoothStmtZ Z γ) (hC : G2RootXCutStmtZ Z γ μ) :
    G2FixMixRootXStmtZ Z γ μ := by
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
  rw [g3RootEvXZ_univ, g3RootEvXcZ_univ] at a3
  exact abs_sub_mul_le_of_three measureReal_nonneg measureReal_le_one a1 a2 a3

/-- **`G2FixMixRootRStmtZ` from Sheffield's two steps** (cut length + smoothing). -/
theorem g2FixMixRootRStmtZ_of_cut {γ : ℝ} {ν : Measure LawD} [IsProbabilityMeasure ν]
    (hS : G2RootRLenSmoothStmtZ Z' γ) (hC : G2RootRCutStmtZ Z' γ ν) :
    G2FixMixRootRStmtZ Z' γ ν := by
  intro t ht δ η m hm ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨ε₁, hε₁, h₁⟩ := hS t ht δ η m hm (ε / 3) hε3
  obtain ⟨ε₂, hε₂, h₂⟩ := hS univ univ_mem_lawCyl δ η m hm (ε / 3) hε3
  set κ : ℝ := min (min ε₁ ε₂) m / 2 with hκ
  have hmin : 0 < min (min ε₁ ε₂) m := lt_min (lt_min hε₁ hε₂) hm
  have hκ0 : 0 < κ := by positivity
  have hκlt : κ < min (min ε₁ ε₂) m := by rw [hκ]; linarith
  have hκ1 : κ < ε₁ := hκlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hκ2 : κ < ε₂ := hκlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hκm : κ < m := hκlt.trans_le (min_le_right _ _)
  filter_upwards [h₁ κ ⟨hκ0, hκ1⟩, h₂ κ ⟨hκ0, hκ2⟩, hC t ht δ η m κ hκ0 hκm (ε / 3) hε3]
    with C hC₁ hC₂ hC₃ i hi G hG
  have a1 := hC₁ i hi G hG
  have a2 := hC₃ i hi G hG
  have a3 := hC₂ i hi G hG
  rw [g3RootEvRZ_univ, g3RootEvRcZ_univ] at a3
  exact abs_sub_mul_le_of_three measureReal_nonneg measureReal_le_one a1 a2 a3

end ZoomAbs

end Thm18Asm
end QuantumZipper
