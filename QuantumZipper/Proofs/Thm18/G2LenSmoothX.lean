import QuantumZipper.Proofs.Thm18.G2LenSmoothGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 smoothing, `x` side: `G2RootXLenSmoothStmt` from the clipped-shift node

Sheffield (arXiv:1012.4797, proof of Proposition 5.5, pp. 65–66) proves that conditioning on the
length `L = ν_h[x, 0]` or on its value after resampling the field near `x` gives the same zoom
law up to `o(1)` in total variation, from two facts:

1. the resampling changes `L` by an amount tending to `0` in probability (here: the gap
   `L − ν_h[x + κ, 0] = ν_h[x, x + κ)`; **proved**, `g3GapX_small`, `G2LenSmoothGap.lean`);
2. given everything except the Gaussian coefficient `α₁` of a bump `φ₁` (supported in region 1
   to the right of the margin, so away from `x`, `x + κ` and the zoom window), `L` is a smooth
   strictly increasing function of `α₁` (`ν_h = e^{γ α₁ φ₁ / 2} ν_{h₀}` on `supp φ₁`), hence has a
   smooth conditional density, and a shift of `L` by an `α₁`-independent amount in `[0, ρ]`
   changes the conditional law by `o(1)` in total variation as `ρ → 0`.

Fact 2 is the node `G2RootXClipSmoothStmt` below: it compares conditioning on `L` with
conditioning on the **clipped** length `max(ν_h[x + κ, 0], L − ρ) = L − min(gap, ρ)`, a shift of
`L` by the `α₁`-independent amount `min(ν_h[x, x+κ), ρ) ∈ [0, ρ]`.

`g2RootXLenSmoothStmt_of_clip` assembles the two: the clipped event and the cut event
`g3RootEvXc` differ only on `{gap > ρ}` (`g3RootXclip_comp`), whose rooted measure is small by
fact 1. Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The rooted event conditioned on the **clipped length** `max(ν_h[x+κ, 0], ν_h[x, 0] − ρ)`. -/
def g3RootEvXclip (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, max (g3CutLen γ κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G}

/-- **Node (smooth conditional density of the length; Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66, the Gaussian bump decomposition `h = α₁ φ₁ + h₀`).** Shifting the length
`ν_h[x, 0]` down by `min(ν_h[x, x + κ), ρ)` (an amount in `[0, ρ]` independent of the bump
coefficient `α₁`) changes the rooted measure of `{zoom ∈ s} ∩ {margin} ∩ {(h, length) ∈ G}` by at
most `ε`, uniformly in `G`, for small `ρ`, all `κ < ρ`, eventually in `C`. -/
def G2RootXClipSmoothStmt (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ρ > 0, ∀ κ ∈ Ioo 0 ρ,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvX γ i s m G).indicator 1)).toReal -
        (g3RootInt γ i ((g3RootEvXclip γ i s m κ ρ G).indicator 1)).toReal| ≤ ε

/-- Measurable versions (through `g3CutLenM`). -/
def g3RootEvXclipM (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, max (g3CutLenM γ i κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G}

def g3RootEvXcM (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, g3CutLenM γ i κ q.1 q.2.2) ∈ G}

theorem measurableSet_g3zoomMargin (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m : ℝ) : MeasurableSet {q : Ω₀ × ℝ × ℝ |
      zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s} ∧
    MeasurableSet {q : Ω₀ × ℝ × ℝ | |q.2.2 - i.t₁| + m < i.r₁} := by
  have hf : Measurable fun q : Ω₀ × ℝ × ℝ => |q.2.2 - i.t₁| + m := by fun_prop
  exact ⟨(measurable_zoomLaw γ i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) hs, measurableSet_lt hf measurable_const⟩

theorem measurableSet_g3RootEvXclipM (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m κ ρ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvXclipM γ i s m κ ρ G) := by
  obtain ⟨h1, h2⟩ := measurableSet_g3zoomMargin γ i hs m
  have h3 : Measurable fun q : Ω₀ × ℝ × ℝ =>
      ((q.1, max (g3CutLenM γ i κ q.1 q.2.2) (q.2.1 - ρ)) : Ω₀ × ℝ) :=
    measurable_fst.prodMk ((measurable_g3CutLenM γ i κ).max
      ((measurable_fst.comp measurable_snd).sub_const ρ))
  exact h1.inter (h2.inter (h3 hG))

theorem measurableSet_g3RootEvXcM (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m κ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvXcM γ i s m κ G) := by
  obtain ⟨h1, h2⟩ := measurableSet_g3zoomMargin γ i hs m
  have h3 : Measurable fun q : Ω₀ × ℝ × ℝ => ((q.1, g3CutLenM γ i κ q.1 q.2.2) : Ω₀ × ℝ) :=
    measurable_fst.prodMk (measurable_g3CutLenM γ i κ)
  exact h1.inter (h2.inter (h3 hG))

/-- Off the gap event, clipping does nothing. -/
theorem g3RootEvXclipM_subset (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvXclipM γ i s m κ ρ G ⊆ g3RootEvXcM γ i s m κ G ∪ g3GapEvXM γ i κ ρ := by
  intro q hq
  by_cases hd : q ∈ g3GapEvXM γ i κ ρ
  · exact Or.inr hd
  · left
    simp only [g3GapEvXM, mem_setOf_eq, not_lt] at hd
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨h1, h2, ?_⟩
    rwa [max_eq_left (by linarith)] at h3

theorem g3RootEvXcM_subset (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvXcM γ i s m κ G ⊆ g3RootEvXclipM γ i s m κ ρ G ∪ g3GapEvXM γ i κ ρ := by
  intro q hq
  by_cases hd : q ∈ g3GapEvXM γ i κ ρ
  · exact Or.inr hd
  · left
    simp only [g3GapEvXM, mem_setOf_eq, not_lt] at hd
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨h1, h2, ?_⟩
    rwa [max_eq_left (by linarith)]

theorem abs_toReal_sub_le_of_le_add {a b c : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (h1 : a ≤ b + c) (h2 : b ≤ a + c) : |a.toReal - b.toReal| ≤ c.toReal := by
  have e1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hb, hc⟩) h1
  have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha, hc⟩) h2
  rw [ENNReal.toReal_add hb hc] at e1
  rw [ENNReal.toReal_add ha hc] at e2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **Clipped versus cut conditioning differ only on the gap event.** -/
theorem g3RootXclip_comp {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {s : Set LawD}
    (hs : MeasurableSet s) (m : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (ρ : ℝ) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet G) :
    |(g3RootInt γ i ((g3RootEvXclip γ i s m κ ρ G).indicator 1)).toReal -
      (g3RootInt γ i ((g3RootEvXc γ i s m κ G).indicator 1)).toReal| ≤
      (g3RootInt γ i ((g3GapEvX γ κ ρ).indicator 1)).toReal := by
  have eA : g3RootInt γ i ((g3RootEvXclip γ i s m κ ρ G).indicator 1) =
      g3RootInt γ i ((g3RootEvXclipM γ i s m κ ρ G).indicator 1) :=
    g3RootInt_cut_eq hγ hγ2 i hκ (fun q c => zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧
      |q.2.2 - i.t₁| + m < i.r₁ ∧ (q.1, max c (q.2.1 - ρ)) ∈ G)
  have eB : g3RootInt γ i ((g3RootEvXc γ i s m κ G).indicator 1) =
      g3RootInt γ i ((g3RootEvXcM γ i s m κ G).indicator 1) :=
    g3RootInt_cut_eq hγ hγ2 i hκ (fun q c => zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧
      |q.2.2 - i.t₁| + m < i.r₁ ∧ (q.1, c) ∈ G)
  have eD : g3RootInt γ i ((g3GapEvX γ κ ρ).indicator 1) =
      g3RootInt γ i ((g3GapEvXM γ i κ ρ).indicator 1) :=
    g3RootInt_cut_eq hγ hγ2 i hκ (fun q c => ρ < q.2.1 - c)
  have hA := measurableSet_g3RootEvXclipM γ i hs m κ ρ hG
  have hB := measurableSet_g3RootEvXcM γ i hs m κ hG
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
    exact preimage_mono (g3RootEvXclipM_subset γ i s m κ ρ G)
  · refine (measure_mono ?_).trans (measure_union_le _ _)
    rw [← preimage_union]
    exact preimage_mono (g3RootEvXcM_subset γ i s m κ ρ G)

/-- **`G2RootXLenSmoothStmt` from the clipped-shift node** (Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66): the gap part is proved (`g3GapX_small`). -/
theorem g2RootXLenSmoothStmt_of_clip {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : G2RootXClipSmoothStmt γ) : G2RootXLenSmoothStmt γ := by
  intro s hs δ η m hm ε hε
  obtain ⟨ρ, hρ, hclip⟩ := h s hs δ η m hm (ε / 2) (by positivity)
  by_cases hex : ∃ i₀ : G3Idx, i₀.δ = δ
  · obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨ε₁, hε₁, hgap⟩ := g3GapX_small hγ hγ2 i₀ hρ (ε := ε / 2) (by positivity)
    refine ⟨min ρ ε₁, lt_min hρ hε₁, fun κ hκ => ?_⟩
    filter_upwards [hclip κ ⟨hκ.1, hκ.2.trans_le (min_le_left _ _)⟩] with C hC i hi G hG
    have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
    have a1 := hC i hi G hG
    have a2 := g3RootXclip_comp hγ hγ2 i (measurableSet_lawCyl hs) m hκ.1.le ρ hGm
    have hδi : i.δ = δ := by unfold G3Idx.δ; rw [hi]
    have a3 := hgap κ ⟨hκ.1, hκ.2.trans_le (min_le_right _ _)⟩
    rw [g3RootInt_eq_of_δ (hi₀.trans hδi.symm)] at a3
    calc _ ≤ _ := abs_sub_le _
          (g3RootInt γ i ((g3RootEvXclip γ i s m κ ρ G).indicator 1)).toReal _
      _ ≤ ε / 2 + ε / 2 := add_le_add a1 (a2.trans a3)
      _ = ε := by ring
  · refine ⟨1, one_pos, fun κ _ => Eventually.of_forall fun C i hi => ?_⟩
    exact absurd ⟨i, by unfold G3Idx.δ; rw [hi]⟩ hex

end Thm18Asm
end QuantumZipper
