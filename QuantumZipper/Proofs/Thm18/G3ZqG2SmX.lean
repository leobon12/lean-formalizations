import QuantumZipper.Proofs.Thm18.G3ZqG2Fix
import QuantumZipper.Proofs.Thm18.G2ClipReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 engine with an abstract zoom: smoothing via clipping, and the disintegration nodes

Generalized copy (D92) of `G2LenSmoothX.lean`, `G2LenSmoothRNode.lean` and `G2ClipReduce.lean`,
with the plain zoom `zoomLaw γ C` replaced by an abstract zoom `Z C h y` (the plain engine is
`Z = zoomLaw γ`). The only property of the zoom used here is the joint measurability `hZm`
(where the originals use `measurable_zoomLaw`). Zoom-free lemmas (gap events, cut-length
versions `g3RootInt_cut_eq`, `g3GapX_small`, `g3GapR_small`, `g2clip_frozen`, triangle
inequalities) are reused from the originals.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66 (smoothing by the Gaussian bump
decomposition, p. 66). Own elementary bookkeeping copied from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

variable {Z : ℝ → FieldSample → ℝ → LawD}

/-- The rooted event conditioned on the **clipped length** `max(ν_h[x+κ, 0], ν_h[x, 0] − ρ)`. -/
def g3RootEvXclipZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, max (g3CutLen γ κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G}

/-- **Node (smooth conditional density of the length; Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66, the Gaussian bump decomposition `h = α₁ φ₁ + h₀`).** Shifting the length
`ν_h[x, 0]` down by `min(ν_h[x, x + κ), ρ)` (an amount in `[0, ρ]` independent of the bump
coefficient `α₁`) changes the rooted measure of `{zoom ∈ s} ∩ {margin} ∩ {(h, length) ∈ G}` by at
most `ε`, uniformly in `G`, for small `ρ`, all `κ < ρ`, eventually in `C`. -/
def G2RootXClipSmoothStmtZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ρ > 0, ∀ κ ∈ Ioo 0 ρ,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvXZ Z γ i s m G).indicator 1)).toReal -
        (g3RootInt γ i ((g3RootEvXclipZ Z γ i s m κ ρ G).indicator 1)).toReal| ≤ ε

/-- Measurable versions (through `g3CutLenM`). -/
def g3RootEvXclipMZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, max (g3CutLenM γ i κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G}

def g3RootEvXcMZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, g3CutLenM γ i κ q.1 q.2.2) ∈ G}

theorem measurableSet_g3zoomMarginZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m : ℝ) : MeasurableSet {q : Ω₀ × ℝ × ℝ |
      Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s} ∧
    MeasurableSet {q : Ω₀ × ℝ × ℝ | |q.2.2 - i.t₁| + m < i.r₁} := by
  have hf : Measurable fun q : Ω₀ × ℝ × ℝ => |q.2.2 - i.t₁| + m := by fun_prop
  exact ⟨(hZm i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) hs, measurableSet_lt hf measurable_const⟩

theorem measurableSet_g3RootEvXclipMZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m κ ρ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvXclipMZ Z γ i s m κ ρ G) := by
  obtain ⟨h1, h2⟩ := measurableSet_g3zoomMarginZ hZm γ i hs m
  have h3 : Measurable fun q : Ω₀ × ℝ × ℝ =>
      ((q.1, max (g3CutLenM γ i κ q.1 q.2.2) (q.2.1 - ρ)) : Ω₀ × ℝ) :=
    measurable_fst.prodMk ((measurable_g3CutLenM γ i κ).max
      ((measurable_fst.comp measurable_snd).sub_const ρ))
  exact h1.inter (h2.inter (h3 hG))

theorem measurableSet_g3RootEvXcMZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m κ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvXcMZ Z γ i s m κ G) := by
  obtain ⟨h1, h2⟩ := measurableSet_g3zoomMarginZ hZm γ i hs m
  have h3 : Measurable fun q : Ω₀ × ℝ × ℝ => ((q.1, g3CutLenM γ i κ q.1 q.2.2) : Ω₀ × ℝ) :=
    measurable_fst.prodMk (measurable_g3CutLenM γ i κ)
  exact h1.inter (h2.inter (h3 hG))

/-- Off the gap event, clipping does nothing. -/
theorem g3RootEvXclipM_subsetZ (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvXclipMZ Z γ i s m κ ρ G ⊆ g3RootEvXcMZ Z γ i s m κ G ∪ g3GapEvXM γ i κ ρ := by
  intro q hq
  by_cases hd : q ∈ g3GapEvXM γ i κ ρ
  · exact Or.inr hd
  · left
    simp only [g3GapEvXM, mem_setOf_eq, not_lt] at hd
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨h1, h2, ?_⟩
    rwa [max_eq_left (by linarith)] at h3

theorem g3RootEvXcM_subsetZ (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvXcMZ Z γ i s m κ G ⊆ g3RootEvXclipMZ Z γ i s m κ ρ G ∪ g3GapEvXM γ i κ ρ := by
  intro q hq
  by_cases hd : q ∈ g3GapEvXM γ i κ ρ
  · exact Or.inr hd
  · left
    simp only [g3GapEvXM, mem_setOf_eq, not_lt] at hd
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨h1, h2, ?_⟩
    rwa [max_eq_left (by linarith)]

/-- **Clipped versus cut conditioning differ only on the gap event.** -/
theorem g3RootXclip_compZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {s : Set LawD}
    (hs : MeasurableSet s) (m : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (ρ : ℝ) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet G) :
    |(g3RootInt γ i ((g3RootEvXclipZ Z γ i s m κ ρ G).indicator 1)).toReal -
      (g3RootInt γ i ((g3RootEvXcZ Z γ i s m κ G).indicator 1)).toReal| ≤
      (g3RootInt γ i ((g3GapEvX γ κ ρ).indicator 1)).toReal := by
  have eA : g3RootInt γ i ((g3RootEvXclipZ Z γ i s m κ ρ G).indicator 1) =
      g3RootInt γ i ((g3RootEvXclipMZ Z γ i s m κ ρ G).indicator 1) :=
    g3RootInt_cut_eq hγ hγ2 i hκ (fun q c => Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧
      |q.2.2 - i.t₁| + m < i.r₁ ∧ (q.1, max c (q.2.1 - ρ)) ∈ G)
  have eB : g3RootInt γ i ((g3RootEvXcZ Z γ i s m κ G).indicator 1) =
      g3RootInt γ i ((g3RootEvXcMZ Z γ i s m κ G).indicator 1) :=
    g3RootInt_cut_eq hγ hγ2 i hκ (fun q c => Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧
      |q.2.2 - i.t₁| + m < i.r₁ ∧ (q.1, c) ∈ G)
  have eD : g3RootInt γ i ((g3GapEvX γ κ ρ).indicator 1) =
      g3RootInt γ i ((g3GapEvXM γ i κ ρ).indicator 1) :=
    g3RootInt_cut_eq hγ hγ2 i hκ (fun q c => ρ < q.2.1 - c)
  have hA := measurableSet_g3RootEvXclipMZ hZm γ i hs m κ ρ hG
  have hB := measurableSet_g3RootEvXcMZ hZm γ i hs m κ hG
  have hD := measurableSet_g3GapEvXM γ i κ ρ
  rw [eA, eB, eD, ← g3LenRoot_rooted hγ hγ2 i hA, ← g3LenRoot_rooted hγ hγ2 i hB,
    ← g3LenRoot_rooted hγ hγ2 i hD]
  have hZ := g3Z_pos_lt_top hγ hγ2 i
  have := isFiniteMeasure_g3LenRoot γ i hZ.2
  set f : Ω₀ × ℝ → Ω₀ × ℝ × ℝ := fun p => (p.1, p.2, g3X γ i p) with hf
  change |(g3LenRoot γ i (f ⁻¹' _)).toReal - (g3LenRoot γ i (f ⁻¹' _)).toReal| ≤
    (g3LenRoot γ i (f ⁻¹' _)).toReal
  refine abs_toReal_sub_le_of_le_add (measure_ne_top _ _) (measure_ne_top _ _)
    (measure_ne_top _ _) ?_ ?_
  · refine (measure_mono ?_).trans (measure_union_le _ _)
    rw [← preimage_union]
    exact preimage_mono (g3RootEvXclipM_subsetZ γ i s m κ ρ G)
  · refine (measure_mono ?_).trans (measure_union_le _ _)
    rw [← preimage_union]
    exact preimage_mono (g3RootEvXcM_subsetZ γ i s m κ ρ G)

/-- **`G2RootXLenSmoothStmtZ` from the clipped-shift node** (Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66): the gap part is proved (`g3GapX_small`). -/
theorem g2RootXLenSmoothStmt_of_clipZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : G2RootXClipSmoothStmtZ Z γ) : G2RootXLenSmoothStmtZ Z γ := by
  intro s hs δ η m hm ε hε
  obtain ⟨ρ, hρ, hclip⟩ := h s hs δ η m hm (ε / 2) (by positivity)
  by_cases hex : ∃ i₀ : G3Idx, i₀.δ = δ
  · obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨ε₁, hε₁, hgap⟩ := g3GapX_small hγ hγ2 i₀ hρ (ε := ε / 2) (by positivity)
    refine ⟨min ρ ε₁, lt_min hρ hε₁, fun κ hκ => ?_⟩
    filter_upwards [hclip κ ⟨hκ.1, hκ.2.trans_le (min_le_left _ _)⟩] with C hC i hi G hG
    have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
    have a1 := hC i hi G hG
    have a2 := g3RootXclip_compZ hZm hγ hγ2 i (measurableSet_lawCyl hs) m hκ.1.le ρ hGm
    have hδi : i.δ = δ := by unfold G3Idx.δ; rw [hi]
    have a3 := hgap κ ⟨hκ.1, hκ.2.trans_le (min_le_right _ _)⟩
    rw [g3RootInt_eq_of_δ (hi₀.trans hδi.symm)] at a3
    calc _ ≤ _ := abs_sub_le _
          (g3RootInt γ i ((g3RootEvXclipZ Z γ i s m κ ρ G).indicator 1)).toReal _
      _ ≤ ε / 2 + ε / 2 := add_le_add a1 (a2.trans a3)
      _ = ε := by ring
  · refine ⟨1, one_pos, fun κ _ => Eventually.of_forall fun C i hi => ?_⟩
    exact absurd ⟨i, by unfold G3Idx.δ; rw [hi]⟩ hex

/-- The rooted event at `y` conditioned on the **clipped length**
`max(ν_h[0, y − κ], ν_h[0, y] − ρ)` (outside event and truncation). -/
def g3RootEvRclipZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, max (g3CutLenR γ κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G ∧
    ENNReal.ofReal (max (g3CutLenR γ κ q.1 q.2.2) (q.2.1 - ρ)) ≤ g3Mass γ i q.1}

/-- **Node, `R` side (smooth conditional density of the length; Sheffield, arXiv:1012.4797,
proof of Prop. 5.5, p. 66, bump `φ₂` in region 2 between `0` and `y − κ`; proof of Thm. 1.8,
p. 71).** Shifting the length `ν_h[0, y]` down by `min(ν_h(y − κ, y], ρ)` (in the outside event
and in the truncation `≤ M`) changes the rooted measure by at most `ε`, uniformly in `G`, for
small `ρ`, all `κ < ρ`, eventually in `C`. -/
def G2RootRClipSmoothStmtZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ρ > 0, ∀ κ ∈ Ioo 0 ρ,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvRZ Z γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
        (g3RootIntR γ i ((g3RootEvRclipZ Z γ i t m κ ρ G).indicator 1)).toReal| ≤ ε

def g3RootEvRclipMZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, max (g3CutLenRM γ i κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G ∧
    ENNReal.ofReal (max (g3CutLenRM γ i κ q.1 q.2.2) (q.2.1 - ρ)) ≤ g3Mass γ i q.1}

def g3RootEvRcMZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, g3CutLenRM γ i κ q.1 q.2.2) ∈ G ∧
    ENNReal.ofReal (g3CutLenRM γ i κ q.1 q.2.2) ≤ g3Mass γ i q.1}

theorem measurableSet_g3zoom₂Z (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t) :
    MeasurableSet {q : Ω₀ × ℝ × ℝ | Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ t} :=
  (hZm i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) ht

theorem measurableSet_g3RootEvRclipMZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m κ ρ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvRclipMZ Z γ i t m κ ρ G) :=
  (measurableSet_g3zoom₂Z hZm γ i ht).inter ((measurableSet_margin₂ i m).inter
    (measurableSet_g3len_tail γ i hG ((measurable_g3CutLenRM γ i κ).max
      ((measurable_fst.comp measurable_snd).sub_const ρ))))

theorem measurableSet_g3RootEvRcMZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m κ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvRcMZ Z γ i t m κ G) :=
  (measurableSet_g3zoom₂Z hZm γ i ht).inter ((measurableSet_margin₂ i m).inter
    (measurableSet_g3len_tail γ i hG (measurable_g3CutLenRM γ i κ)))

theorem g3RootEvRclipM_subsetZ (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvRclipMZ Z γ i t m κ ρ G ⊆ g3RootEvRcMZ Z γ i t m κ G ∪ g3GapEvRM γ i m κ ρ := by
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  by_cases hd : ρ < q.2.1 - g3CutLenRM γ i κ q.1 q.2.2
  · exact Or.inr ⟨h2, hd⟩
  · left
    rw [max_eq_left (by linarith)] at h3 h4
    exact ⟨h1, h2, h3, h4⟩

theorem g3RootEvRcM_subsetZ (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvRcMZ Z γ i t m κ G ⊆ g3RootEvRclipMZ Z γ i t m κ ρ G ∪ g3GapEvRM γ i m κ ρ := by
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  by_cases hd : ρ < q.2.1 - g3CutLenRM γ i κ q.1 q.2.2
  · exact Or.inr ⟨h2, hd⟩
  · left
    have e : max (g3CutLenRM γ i κ q.1 q.2.2) (q.2.1 - ρ) = g3CutLenRM γ i κ q.1 q.2.2 :=
      max_eq_left (by linarith)
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [e]; exact h3
    · rw [e]; exact h4

/-- **Clipped versus cut conditioning at `R` differ only on the gap event.** -/
theorem g3RootRclip_compZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {t : Set LawD}
    (ht : MeasurableSet t) {m : ℝ} (hm : 0 < m) {κ : ℝ} (hκ : 0 ≤ κ) (ρ : ℝ)
    {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    |(g3RootIntR γ i ((g3RootEvRclipZ Z γ i t m κ ρ G).indicator 1)).toReal -
      (g3RootIntR γ i ((g3RootEvRcZ Z γ i t m κ G).indicator 1)).toReal| ≤
      (g3RootIntR γ i ((g3GapEvR γ i.t₂ i.r₂ m κ ρ).indicator 1)).toReal := by
  have eA : g3RootIntR γ i ((g3RootEvRclipZ Z γ i t m κ ρ G).indicator 1) =
      g3RootIntR γ i ((g3RootEvRclipMZ Z γ i t m κ ρ G).indicator 1) :=
    g3RootIntR_cut_eq hγ hγ2 i hκ hm.le (fun q c =>
      Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
        (q.1, max c (q.2.1 - ρ)) ∈ G ∧ ENNReal.ofReal (max c (q.2.1 - ρ)) ≤ g3Mass γ i q.1)
      (fun q c h => h.2.1)
  have eB : g3RootIntR γ i ((g3RootEvRcZ Z γ i t m κ G).indicator 1) =
      g3RootIntR γ i ((g3RootEvRcMZ Z γ i t m κ G).indicator 1) :=
    g3RootIntR_cut_eq hγ hγ2 i hκ hm.le (fun q c =>
      Z i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
        (q.1, c) ∈ G ∧ ENNReal.ofReal c ≤ g3Mass γ i q.1)
      (fun q c h => h.2.1)
  have eD : g3RootIntR γ i ((g3GapEvR γ i.t₂ i.r₂ m κ ρ).indicator 1) =
      g3RootIntR γ i ((g3GapEvRM γ i m κ ρ).indicator 1) :=
    g3RootIntR_cut_eq hγ hγ2 i hκ hm.le
      (fun q c => |q.2.2 - i.t₂| + m < i.r₂ ∧ ρ < q.2.1 - c) (fun q c h => h.1)
  obtain ⟨ha0, hb0, hbt, hsub⟩ := g3bR_props i hm
  have hA := measurableSet_g3RootEvRclipMZ hZm γ i ht m κ ρ hG
  have hB := measurableSet_g3RootEvRcMZ hZm γ i ht m κ hG
  have hD := measurableSet_g3GapEvRM γ i m κ ρ
  have fin : ∀ T : Set (Ω₀ × ℝ × ℝ), g3RootIntR γ i (T.indicator 1) ≠ ⊤ := fun T =>
    (g3RootIntR_indicator_lt_top hγ hγ2 i T).ne
  rw [eA, eB, eD, ← g3RootR_apply_eq hγ hγ2 i hA ha0 hb0 hbt (fun q hq => hsub _ hq.2.1),
    ← g3RootR_apply_eq hγ hγ2 i hB ha0 hb0 hbt (fun q hq => hsub _ hq.2.1),
    ← g3RootR_apply_eq hγ hγ2 i hD ha0 hb0 hbt (fun q hq => hsub _ hq.1)]
  have fA := fin (g3RootEvRclipMZ Z γ i t m κ ρ G)
  have fB := fin (g3RootEvRcMZ Z γ i t m κ G)
  have fD := fin (g3GapEvRM γ i m κ ρ)
  rw [← g3RootR_apply_eq hγ hγ2 i hA ha0 hb0 hbt (fun q hq => hsub _ hq.2.1)] at fA
  rw [← g3RootR_apply_eq hγ hγ2 i hB ha0 hb0 hbt (fun q hq => hsub _ hq.2.1)] at fB
  rw [← g3RootR_apply_eq hγ hγ2 i hD ha0 hb0 hbt (fun q hq => hsub _ hq.1)] at fD
  refine abs_toReal_sub_le_of_le_add fA fB fD ?_ ?_
  · exact (measure_mono (g3RootEvRclipM_subsetZ γ i t m κ ρ G)).trans (measure_union_le _ _)
  · exact (measure_mono (g3RootEvRcM_subsetZ γ i t m κ ρ G)).trans (measure_union_le _ _)

/-- **`G2RootRLenSmoothStmtZ` from the clipped-shift node** (the gap part is proved,
`g3GapR_small`). -/
theorem g2RootRLenSmoothStmt_of_clipZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : G2RootRClipSmoothStmtZ Z γ) : G2RootRLenSmoothStmtZ Z γ := by
  intro t ht δ η m hm ε hε
  obtain ⟨ρ, hρ, hclip⟩ := h t ht δ η m hm (ε / 2) (by positivity)
  by_cases hex : ∃ i₀ : G3Idx, i₀.η = η
  · obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨ε₁, hε₁, hgap⟩ := g3GapR_small hγ hγ2 i₀ hm hρ (ε := ε / 2) (by positivity)
    refine ⟨min ρ ε₁, lt_min hρ hε₁, fun κ hκ => ?_⟩
    filter_upwards [hclip κ ⟨hκ.1, hκ.2.trans_le (min_le_left _ _)⟩] with C hC i hi G hG
    have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
    have a1 := hC i hi G hG
    have a2 := g3RootRclip_compZ hZm hγ hγ2 i (measurableSet_lawCyl ht) hm hκ.1.le ρ hGm
    have hηi : i.η = i₀.η := by rw [hi₀]; unfold G3Idx.η; rw [hi]
    have ht₂ : i₀.t₂ = i.t₂ := by unfold G3Idx.t₂; rw [hηi]
    have hr₂ : i₀.r₂ = i.r₂ := by unfold G3Idx.r₂; rw [hηi]
    have a3 := hgap κ ⟨hκ.1, hκ.2.trans_le (min_le_right _ _)⟩
    rw [g3RootIntR_eq_of_idx (i' := i) (by rw [ht₂, hr₂]), ht₂, hr₂] at a3
    calc _ ≤ _ := abs_sub_le _
          (g3RootIntR γ i ((g3RootEvRclipZ Z γ i t m κ ρ G).indicator 1)).toReal _
      _ ≤ ε / 2 + ε / 2 := add_le_add a1 (a2.trans a3)
      _ = ε := by ring
  · refine ⟨1, one_pos, fun κ _ => Eventually.of_forall fun C i hi => ?_⟩
    exact absurd ⟨i, by unfold G3Idx.η; rw [hi]⟩ hex

/-- **Node (rooted bump disintegration, `x` side; Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66).** See the module docstring. -/
def G2RootXDisintStmtZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∃ ρ₀ > 0, ∀ ε > 0,
    ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (Q : Measure Ξ) (_ : IsFiniteMeasure Q)
      (N : Measure ℝ) (_ : IsProbabilityMeasure N) (f : Ξ → ℝ → ℝ),
      N ≪ volume ∧ Measurable (Function.uncurry f) ∧ (∀ ξ, Differentiable ℝ (f ξ)) ∧
      (∀ ξ a, 0 < deriv (f ξ) a) ∧
      ∀ κ ∈ Ioo 0 ρ₀, ∃ gap : Ξ → ℝ, Measurable gap ∧ (∀ ξ, 0 ≤ gap ξ) ∧
        ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
          ∀ G : Set (gffBase.Ω × ℝ),
          MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
          ∃ S : Set (Ξ × ℝ), MeasurableSet S ∧
            |(g3RootInt γ i ((g3RootEvXZ Z γ i s m G).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2) ∈ S}| ≤ ε ∧
            ∀ ρ > 0, |(g3RootInt γ i ((g3RootEvXclipZ Z γ i s m κ ρ G).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2 - min (gap p.1) ρ) ∈ S}| ≤ ε

/-- **Node (rooted bump disintegration, `R` side; bump in region 2 between `0` and `y − κ`;
Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 66, and of Thm. 1.8, p. 71).** -/
def G2RootRDisintStmtZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∃ ρ₀ > 0, ∀ ε > 0,
    ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (Q : Measure Ξ) (_ : IsFiniteMeasure Q)
      (N : Measure ℝ) (_ : IsProbabilityMeasure N) (f : Ξ → ℝ → ℝ),
      N ≪ volume ∧ Measurable (Function.uncurry f) ∧ (∀ ξ, Differentiable ℝ (f ξ)) ∧
      (∀ ξ a, 0 < deriv (f ξ) a) ∧
      ∀ κ ∈ Ioo 0 ρ₀, ∃ gap : Ξ → ℝ, Measurable gap ∧ (∀ ξ, 0 ≤ gap ξ) ∧
        ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
          ∀ G : Set (gffBase.Ω × ℝ),
          MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
          ∃ S : Set (Ξ × ℝ), MeasurableSet S ∧
            |(g3RootIntR γ i ((g3RootEvRZ Z γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2) ∈ S}| ≤ ε ∧
            ∀ ρ > 0, |(g3RootIntR γ i ((g3RootEvRclipZ Z γ i t m κ ρ G).indicator 1)).toReal -
              (Q.prod N).real {p | (p.1, f p.1 p.2 - min (gap p.1) ρ) ∈ S}| ≤ ε

/-- **`G2RootXClipSmoothStmtZ` from the rooted bump disintegration** and the proved
frozen-coefficient estimate `g2clip_frozen`. -/
theorem g2RootXClipSmoothStmt_of_disintZ {γ : ℝ} (hX : G2RootXDisintStmtZ Z γ) :
    G2RootXClipSmoothStmtZ Z γ := by
  intro s hs δ η m hm ε hε
  obtain ⟨ρ₀, hρ₀, hD⟩ := hX s hs δ η m hm
  obtain ⟨Ξ, _, Q, _, N, _, f, hN, hfm, hf, hpos, hK⟩ := hD (ε / 3) (by positivity)
  obtain ⟨ρ₁, hρ₁, hfr⟩ := g2clip_frozen Q hN f hfm hf hpos (ε := ε / 3) (by positivity)
  have hmin : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
  refine ⟨min ρ₀ ρ₁ / 2, by positivity, fun κ hκ => ?_⟩
  have hκ0 : κ ∈ Ioo 0 ρ₀ := ⟨hκ.1, hκ.2.trans_le (by linarith [min_le_left ρ₀ ρ₁])⟩
  obtain ⟨gap, hgm, hg0, hev⟩ := hK κ hκ0
  filter_upwards [hev] with C hC i hi G hG
  obtain ⟨S, hS, h1, h2⟩ := hC i hi G hG
  have h2' := h2 (min ρ₀ ρ₁ / 2) (by positivity)
  have h3 := hfr S hS (fun ξ => -min (gap ξ) (min ρ₀ ρ₁ / 2)) (hgm.min measurable_const).neg
    (fun ξ => g2clip_shift_bound (hg0 ξ) (by positivity)
      (by linarith [min_le_right ρ₀ ρ₁]))
  simp only [← sub_eq_add_neg] at h3
  exact g2clip_three h1 h3 h2'

/-- **`G2RootRClipSmoothStmtZ` from the rooted bump disintegration** (`R` side). -/
theorem g2RootRClipSmoothStmt_of_disintZ {γ : ℝ} (hR : G2RootRDisintStmtZ Z γ) :
    G2RootRClipSmoothStmtZ Z γ := by
  intro t ht δ η m hm ε hε
  obtain ⟨ρ₀, hρ₀, hD⟩ := hR t ht δ η m hm
  obtain ⟨Ξ, _, Q, _, N, _, f, hN, hfm, hf, hpos, hK⟩ := hD (ε / 3) (by positivity)
  obtain ⟨ρ₁, hρ₁, hfr⟩ := g2clip_frozen Q hN f hfm hf hpos (ε := ε / 3) (by positivity)
  have hmin : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
  refine ⟨min ρ₀ ρ₁ / 2, by positivity, fun κ hκ => ?_⟩
  have hκ0 : κ ∈ Ioo 0 ρ₀ := ⟨hκ.1, hκ.2.trans_le (by linarith [min_le_left ρ₀ ρ₁])⟩
  obtain ⟨gap, hgm, hg0, hev⟩ := hK κ hκ0
  filter_upwards [hev] with C hC i hi G hG
  obtain ⟨S, hS, h1, h2⟩ := hC i hi G hG
  have h2' := h2 (min ρ₀ ρ₁ / 2) (by positivity)
  have h3 := hfr S hS (fun ξ => -min (gap ξ) (min ρ₀ ρ₁ / 2)) (hgm.min measurable_const).neg
    (fun ξ => g2clip_shift_bound (hg0 ξ) (by positivity)
      (by linarith [min_le_right ρ₀ ρ₁]))
  simp only [← sub_eq_add_neg] at h3
  exact g2clip_three h1 h3 h2'

end Thm18Asm
end QuantumZipper
