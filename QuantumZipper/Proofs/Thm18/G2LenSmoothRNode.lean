import QuantumZipper.Proofs.Thm18.G2LenSmoothR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 smoothing, `R` side: the clipped-shift node and the assembly

See `G2LenSmoothR.lean` for the plan. The clipped length `max(ν_h[0, y − κ], L − ρ)` enters both
the outside event and the truncation `≤ M`, as the cut length does in `g3RootEvRc`; off the gap
event `{L − ν_h[0, y − κ] > ρ}` the clipped and the cut events coincide (`g3RootRclip_comp`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The rooted event at `y` conditioned on the **clipped length**
`max(ν_h[0, y − κ], ν_h[0, y] − ρ)` (outside event and truncation). -/
def g3RootEvRclip (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, max (g3CutLenR γ κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G ∧
    ENNReal.ofReal (max (g3CutLenR γ κ q.1 q.2.2) (q.2.1 - ρ)) ≤ g3Mass γ i q.1}

/-- **Node, `R` side (smooth conditional density of the length; Sheffield, arXiv:1012.4797,
proof of Prop. 5.5, p. 66, bump `φ₂` in region 2 between `0` and `y − κ`; proof of Thm. 1.8,
p. 71).** Shifting the length `ν_h[0, y]` down by `min(ν_h(y − κ, y], ρ)` (in the outside event
and in the truncation `≤ M`) changes the rooted measure by at most `ε`, uniformly in `G`, for
small `ρ`, all `κ < ρ`, eventually in `C`. -/
def G2RootRClipSmoothStmt (γ : ℝ) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ρ > 0, ∀ κ ∈ Ioo 0 ρ,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvR γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
        (g3RootIntR γ i ((g3RootEvRclip γ i t m κ ρ G).indicator 1)).toReal| ≤ ε

def g3RootEvRclipM (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, max (g3CutLenRM γ i κ q.1 q.2.2) (q.2.1 - ρ)) ∈ G ∧
    ENNReal.ofReal (max (g3CutLenRM γ i κ q.1 q.2.2) (q.2.1 - ρ)) ≤ g3Mass γ i q.1}

def g3RootEvRcM (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, g3CutLenRM γ i κ q.1 q.2.2) ∈ G ∧
    ENNReal.ofReal (g3CutLenRM γ i κ q.1 q.2.2) ≤ g3Mass γ i q.1}

theorem measurableSet_g3len_tail (γ : ℝ) (i : G3Idx) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G)
    {f : Ω₀ × ℝ × ℝ → ℝ} (hf : Measurable f) :
    MeasurableSet {q : Ω₀ × ℝ × ℝ | (q.1, f q) ∈ G ∧ ENNReal.ofReal (f q) ≤ g3Mass γ i q.1} :=
  ((measurable_fst.prodMk hf) hG).inter (measurableSet_le (ENNReal.measurable_ofReal.comp hf)
    ((measurable_g3Mass γ i).comp measurable_fst))

theorem measurableSet_g3zoom₂ (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t) :
    MeasurableSet {q : Ω₀ × ℝ × ℝ | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t} :=
  (measurable_zoomLaw γ i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) ht

theorem measurableSet_g3RootEvRclipM (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m κ ρ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvRclipM γ i t m κ ρ G) :=
  (measurableSet_g3zoom₂ γ i ht).inter ((measurableSet_margin₂ i m).inter
    (measurableSet_g3len_tail γ i hG ((measurable_g3CutLenRM γ i κ).max
      ((measurable_fst.comp measurable_snd).sub_const ρ))))

theorem measurableSet_g3RootEvRcM (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m κ : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    MeasurableSet (g3RootEvRcM γ i t m κ G) :=
  (measurableSet_g3zoom₂ γ i ht).inter ((measurableSet_margin₂ i m).inter
    (measurableSet_g3len_tail γ i hG (measurable_g3CutLenRM γ i κ)))

theorem g3RootEvRclipM_subset (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvRclipM γ i t m κ ρ G ⊆ g3RootEvRcM γ i t m κ G ∪ g3GapEvRM γ i m κ ρ := by
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  by_cases hd : ρ < q.2.1 - g3CutLenRM γ i κ q.1 q.2.2
  · exact Or.inr ⟨h2, hd⟩
  · left
    rw [max_eq_left (by linarith)] at h3 h4
    exact ⟨h1, h2, h3, h4⟩

theorem g3RootEvRcM_subset (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ ρ : ℝ)
    (G : Set (Ω₀ × ℝ)) :
    g3RootEvRcM γ i t m κ G ⊆ g3RootEvRclipM γ i t m κ ρ G ∪ g3GapEvRM γ i m κ ρ := by
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
theorem g3RootRclip_comp {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {t : Set LawD}
    (ht : MeasurableSet t) {m : ℝ} (hm : 0 < m) {κ : ℝ} (hκ : 0 ≤ κ) (ρ : ℝ)
    {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) :
    |(g3RootIntR γ i ((g3RootEvRclip γ i t m κ ρ G).indicator 1)).toReal -
      (g3RootIntR γ i ((g3RootEvRc γ i t m κ G).indicator 1)).toReal| ≤
      (g3RootIntR γ i ((g3GapEvR γ i.t₂ i.r₂ m κ ρ).indicator 1)).toReal := by
  have eA : g3RootIntR γ i ((g3RootEvRclip γ i t m κ ρ G).indicator 1) =
      g3RootIntR γ i ((g3RootEvRclipM γ i t m κ ρ G).indicator 1) :=
    g3RootIntR_cut_eq hγ hγ2 i hκ hm.le (fun q c =>
      zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
        (q.1, max c (q.2.1 - ρ)) ∈ G ∧ ENNReal.ofReal (max c (q.2.1 - ρ)) ≤ g3Mass γ i q.1)
      (fun q c h => h.2.1)
  have eB : g3RootIntR γ i ((g3RootEvRc γ i t m κ G).indicator 1) =
      g3RootIntR γ i ((g3RootEvRcM γ i t m κ G).indicator 1) :=
    g3RootIntR_cut_eq hγ hγ2 i hκ hm.le (fun q c =>
      zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
        (q.1, c) ∈ G ∧ ENNReal.ofReal c ≤ g3Mass γ i q.1)
      (fun q c h => h.2.1)
  have eD : g3RootIntR γ i ((g3GapEvR γ i.t₂ i.r₂ m κ ρ).indicator 1) =
      g3RootIntR γ i ((g3GapEvRM γ i m κ ρ).indicator 1) :=
    g3RootIntR_cut_eq hγ hγ2 i hκ hm.le
      (fun q c => |q.2.2 - i.t₂| + m < i.r₂ ∧ ρ < q.2.1 - c) (fun q c h => h.1)
  obtain ⟨ha0, hb0, hbt, hsub⟩ := g3bR_props i hm
  have hA := measurableSet_g3RootEvRclipM γ i ht m κ ρ hG
  have hB := measurableSet_g3RootEvRcM γ i ht m κ hG
  have hD := measurableSet_g3GapEvRM γ i m κ ρ
  have fin : ∀ T : Set (Ω₀ × ℝ × ℝ), g3RootIntR γ i (T.indicator 1) ≠ ⊤ := fun T =>
    (g3RootIntR_indicator_lt_top hγ hγ2 i T).ne
  rw [eA, eB, eD, ← g3RootR_apply_eq hγ hγ2 i hA ha0 hb0 hbt (fun q hq => hsub _ hq.2.1),
    ← g3RootR_apply_eq hγ hγ2 i hB ha0 hb0 hbt (fun q hq => hsub _ hq.2.1),
    ← g3RootR_apply_eq hγ hγ2 i hD ha0 hb0 hbt (fun q hq => hsub _ hq.1)]
  have fA := fin (g3RootEvRclipM γ i t m κ ρ G)
  have fB := fin (g3RootEvRcM γ i t m κ G)
  have fD := fin (g3GapEvRM γ i m κ ρ)
  rw [← g3RootR_apply_eq hγ hγ2 i hA ha0 hb0 hbt (fun q hq => hsub _ hq.2.1)] at fA
  rw [← g3RootR_apply_eq hγ hγ2 i hB ha0 hb0 hbt (fun q hq => hsub _ hq.2.1)] at fB
  rw [← g3RootR_apply_eq hγ hγ2 i hD ha0 hb0 hbt (fun q hq => hsub _ hq.1)] at fD
  refine abs_toReal_sub_le_of_le_add fA fB fD ?_ ?_
  · exact (measure_mono (g3RootEvRclipM_subset γ i t m κ ρ G)).trans (measure_union_le _ _)
  · exact (measure_mono (g3RootEvRcM_subset γ i t m κ ρ G)).trans (measure_union_le _ _)

/-- **`G2RootRLenSmoothStmt` from the clipped-shift node** (the gap part is proved,
`g3GapR_small`). -/
theorem g2RootRLenSmoothStmt_of_clip {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : G2RootRClipSmoothStmt γ) : G2RootRLenSmoothStmt γ := by
  intro t ht δ η m hm ε hε
  obtain ⟨ρ, hρ, hclip⟩ := h t ht δ η m hm (ε / 2) (by positivity)
  by_cases hex : ∃ i₀ : G3Idx, i₀.η = η
  · obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨ε₁, hε₁, hgap⟩ := g3GapR_small hγ hγ2 i₀ hm hρ (ε := ε / 2) (by positivity)
    refine ⟨min ρ ε₁, lt_min hρ hε₁, fun κ hκ => ?_⟩
    filter_upwards [hclip κ ⟨hκ.1, hκ.2.trans_le (min_le_left _ _)⟩] with C hC i hi G hG
    have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
    have a1 := hC i hi G hG
    have a2 := g3RootRclip_comp hγ hγ2 i (measurableSet_lawCyl ht) hm hκ.1.le ρ hGm
    have hηi : i.η = i₀.η := by rw [hi₀]; unfold G3Idx.η; rw [hi]
    have ht₂ : i₀.t₂ = i.t₂ := by unfold G3Idx.t₂; rw [hηi]
    have hr₂ : i₀.r₂ = i.r₂ := by unfold G3Idx.r₂; rw [hηi]
    have a3 := hgap κ ⟨hκ.1, hκ.2.trans_le (min_le_right _ _)⟩
    rw [g3RootIntR_eq_of_idx (i' := i) (by rw [ht₂, hr₂]), ht₂, hr₂] at a3
    calc _ ≤ _ := abs_sub_le _
          (g3RootIntR γ i ((g3RootEvRclip γ i t m κ ρ G).indicator 1)).toReal _
      _ ≤ ε / 2 + ε / 2 := add_le_add a1 (a2.trans a3)
      _ = ε := by ring
  · refine ⟨1, one_pos, fun κ _ => Eventually.of_forall fun C i hi => ?_⟩
    exact absurd ⟨i, by unfold G3Idx.η; rw [hi]⟩ hex

/-- **Both smoothing nodes of G2** (`g2FixMixStmt_of_agreeNodes`) from the two clipped-shift
nodes. -/
theorem g2RootLenSmooth_of_clip {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : G2RootXClipSmoothStmt γ) (hR : G2RootRClipSmoothStmt γ) :
    G2RootXLenSmoothStmt γ ∧ G2RootRLenSmoothStmt γ :=
  ⟨g2RootXLenSmoothStmt_of_clip hγ hγ2 hX, g2RootRLenSmoothStmt_of_clip hγ hγ2 hR⟩

end Thm18Asm
end QuantumZipper
