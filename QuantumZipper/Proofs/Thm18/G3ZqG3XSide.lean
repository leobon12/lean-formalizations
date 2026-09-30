import QuantumZipper.Proofs.Thm18.G3ZqG3CM
import QuantumZipper.Proofs.Thm18.R18G3TXSide4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the step `B → C` (x side proved, R side open)

Generalized copy (D92) of `xside_index_bound` and `g3TCutToProfXStmt_holds`
(`R18G3TXSide4.lean`), with the plain zoom replaced by an abstract zoom `Z`. The original uses,
besides measurability, the locality of `zoomLaw` on the margin event: the region zoom and the
full zoom agree outside the area-failure events (`g3p_symmDiff_subset_area₁` with
`G3TCutAreaStmt`, `G3TProfAreaStmt`). For an abstract zoom this is the explicit hypothesis
`G3pRegLocXZ` (region locality at `x`, for the cut-off profiles `g3wCut γ η` of scheme `B` and the
profile `g3wProf γ` of scheme `C`); the failure events are then the symmetric differences
themselves. The Palm change of variables `g3Φ`, `g3pPalm_cv` and all zoom-free lemmas are reused.

The `R(x)` side `G3TCutToProfRStmtZ` is left open (it is open for the plain zoom as well,
`G3TCutToProfRStmt`).

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, p. 71. Own bookkeeping copied from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- **Per-index bound** for the `x`-side of `B → C`. -/
theorem xside_index_boundZ {Z : ℝ → FieldSample → ℝ → LawD}
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {s : Set LawD}
    (hs : s ∈ lawCyl) {m : ℝ} (hm : 0 < m)
    {failB failC : Set (Ω₀ × ℝ)}
    (hlocB : (g3pUZ Z γ (g3wCut γ i.η) i ⁻¹' s ∩
          {p | |g3pX γ (g3wCut γ i.η) i p - i.t₁| + m < i.r₁}) ∆
        (g3pUfZ Z γ (g3wCut γ i.η) i ⁻¹' s ∩
          {p | |g3pX γ (g3wCut γ i.η) i p - i.t₁| + m < i.r₁}) ⊆ failB)
    (hlocC : (g3pUZ Z γ (g3wProf γ) i ⁻¹' s ∩ {p | |g3pX γ (g3wProf γ) i p - i.t₁| + m < i.r₁}) ∆
        (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩ {p | |g3pX γ (g3wProf γ) i p - i.t₁| + m < i.r₁}) ⊆
          failC)
    {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G)
    {a e₁ e₂ : ℝ}
    (hbody : |(g3pPalmLaw γ (g3wCut γ i.η) i).real (g3pUfZ Z γ (g3wCut γ i.η) i ⁻¹' s ∩
        {p | |g3pX γ (g3wCut γ i.η) i p - i.t₁| + m < i.r₁} ∩ g3Φ γ i ⁻¹' G) -
      a * (g3pPalmLaw γ (g3wCut γ i.η) i).real
        ({p | |g3pX γ (g3wCut γ i.η) i p - i.t₁| + m < i.r₁} ∩ g3Φ γ i ⁻¹' G)| ≤ e₁)
    (hfB : (g3pPalmLaw γ (g3wCut γ i.η) i).real failB ≤ e₂)
    (hfC : (g3pPalmLaw γ (g3wProf γ) i).real failC ≤ e₂) :
    |(g3pPalmLaw γ (g3wProf γ) i).real (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩
        {p | |g3pX γ (g3wProf γ) i p - i.t₁| + m < i.r₁} ∩ G) -
      a * (g3pPalmLaw γ (g3wProf γ) i).real
        ({p | |g3pX γ (g3wProf γ) i p - i.t₁| + m < i.r₁} ∩ G)| ≤
      ((g3pZ γ (g3wProf γ) i)⁻¹ * g3pZ γ (g3wCut γ i.η) i).toReal * (e₁ + e₂) + e₂ := by
  set gB := g3wCut γ i.η
  set gC := g3wProf γ
  set PB := g3pPalmLaw γ gB i
  set PC := g3pPalmLaw γ gC i
  set EB : Set (Ω₀ × ℝ) := {p | |g3pX γ gB i p - i.t₁| + m < i.r₁} with hEBdef
  set EC : Set (Ω₀ × ℝ) := {p | |g3pX γ gC i p - i.t₁| + m < i.r₁} with hECdef
  set RB := g3pX γ gB i ⁻¹' reg1 i
  set r := ((g3pZ γ gC i)⁻¹ * g3pZ γ gB i).toReal with hr
  have hZB := g3pBZ_pos_lt_top hγ hγ2 i
  have hZC := g3pZ_pos_lt_top hγ hγ2 i
  have hr0 : 0 < r := ENNReal.toReal_pos
    (mul_ne_zero (ENNReal.inv_ne_zero.2 hZC.2.ne) hZB.1.ne')
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZC.1.ne') hZB.2.ne)
  have hXB : Measurable (g3pX γ gB i) := (measurable_g3pX γ gB i).mono (sig_le_g3 i _ _) le_rfl
  have hXC : Measurable (g3pX γ gC i) := (measurable_g3pX γ gC i).mono (sig_le_g3 i _ _) le_rfl
  have mEB : MeasurableSet EB := measurableSet_lt (by fun_prop) measurable_const
  have mEC : MeasurableSet EC := measurableSet_lt (by fun_prop) measurable_const
  have mG : MeasurableSet G := outsideSigmaPalm_le_g3 i _ hG
  have mUfC := measurable_g3pUfZ hZm γ gC i (measurableSet_lawCyl hs)
  have mUfB := measurable_g3pUfZ hZm γ gB i (measurableSet_lawCyl hs)
  have mΦG : MeasurableSet (g3Φ γ i ⁻¹' G) := measurable_g3Φ γ i mG
  have hsub : ∀ x : ℝ, |x - i.t₁| + m < i.r₁ → x ∈ reg1 i := fun x hx => by
    have := (abs_lt.1 (show |x - i.t₁| < i.r₁ by linarith))
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hEsubB : EB ⊆ RB := fun p hp => hsub _ hp
  have hEsubC : EC ⊆ g3pX γ gC i ⁻¹' reg1 i := fun p hp => hsub _ hp
  -- the change of variables, real form
  have cvr : ∀ K, MeasurableSet K → K ⊆ g3pX γ gC i ⁻¹' reg1 i →
      PC.real K = r * PB.real (g3Φ γ i ⁻¹' K ∩ RB) := fun K hK hKE => by
    have h := g3pPalm_cv hγ hγ2 i hK hKE
    have e : PC K = (g3pZ γ gC i)⁻¹ * g3pZ γ gB i * PB (g3Φ γ i ⁻¹' K ∩ RB) := by
      rw [mul_assoc, h, ← mul_assoc, ENNReal.inv_mul_cancel hZC.1.ne' hZC.2.ne, one_mul]
    simp only [measureReal_def]
    rw [e, ENNReal.toReal_mul]
  have hgood : ∀ᵐ p ∂PB, g3pν₀ γ gB i p.1 (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0 ∧
      g3pν₀ γ gC i p.1 (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0 ∧
      g3pν₁ γ gC i p.1 (Icc (i.t₁ + i.r₁) 0) = 0 :=
    ae_palm_of_ae γ gB i ((ae_gap_null hγ hγ2).mono fun ω h => h i)
  -- (i) the margin events correspond
  have hK2 : (g3Φ γ i ⁻¹' (EC ∩ G) ∩ RB : Set (Ω₀ × ℝ)) =ᵐ[PB] (EB ∩ g3Φ γ i ⁻¹' G : Set _) := by
    refine Filter.eventuallyEqSet_iff.2 (hgood.mono fun p hp => ?_)
    constructor
    · rintro ⟨⟨hEC, hGp⟩, hR⟩
      have e := g3pX_Φ hp.1 hp.2.1 hp.2.2 hR
      refine ⟨?_, hGp⟩
      show |g3pX γ gB i p - i.t₁| + m < i.r₁
      rw [← e]; exact hEC
    · rintro ⟨hEB, hGp⟩
      have e := g3pX_Φ hp.1 hp.2.1 hp.2.2 (hEsubB hEB)
      refine ⟨⟨?_, hGp⟩, hEsubB hEB⟩
      show |g3pX γ gC i (g3Φ γ i p) - i.t₁| + m < i.r₁
      rw [e]; exact hEB
  -- (ii) the zoom events correspond off the failure events
  set T : Set (Ω₀ × ℝ) := EC ∩ toMeasurable PC failC with hT
  have mT : MeasurableSet T := mEC.inter (measurableSet_toMeasurable _ _)
  set K1 : Set (Ω₀ × ℝ) := g3Φ γ i ⁻¹' (g3pUfZ Z γ gC i ⁻¹' s ∩ EC ∩ G) ∩ RB
  set Oth : Set (Ω₀ × ℝ) := g3pUfZ Z γ gB i ⁻¹' s ∩ EB ∩ g3Φ γ i ⁻¹' G
  have hincl : ∀ᵐ p ∂PB, p ∈ K1 ∆ Oth → p ∈ failB ∪ (g3Φ γ i ⁻¹' T ∩ RB) := by
    filter_upwards [hgood] with p hp hmem
    by_contra hno
    simp only [mem_union, not_or] at hno
    obtain ⟨hnB, hnT⟩ := hno
    -- common facts
    have hcommon : p ∈ EB ∧ g3Φ γ i p ∈ EC := by
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · have hR : p ∈ RB := h1.2
        have e := g3pX_Φ hp.1 hp.2.1 hp.2.2 hR
        refine ⟨?_, h1.1.1.2⟩
        show |g3pX γ gB i p - i.t₁| + m < i.r₁
        rw [← e]; exact h1.1.1.2
      · have e := g3pX_Φ hp.1 hp.2.1 hp.2.2 (hEsubB h1.1.2)
        refine ⟨h1.1.2, ?_⟩
        show |g3pX γ gC i (g3Φ γ i p) - i.t₁| + m < i.r₁
        rw [e]; exact h1.1.2
    obtain ⟨hEB, hEC⟩ := hcommon
    have hnC : g3Φ γ i p ∉ failC := fun h =>
      hnT ⟨⟨hEC, subset_toMeasurable _ _ h⟩, hEsubB hEB⟩
    have locB := zoom_iff_of_not_fail (R := 0) hlocB hEB hnB
    have locC := zoom_iff_of_not_fail (R := 0) hlocC hEC hnC
    have eU : g3pUZ Z γ gB i p = g3pUZ Z γ gC i (g3Φ γ i p) := by
      unfold g3pUZ
      rw [g3pX_Φ hp.1 hp.2.1 hp.2.2 (hEsubB hEB)]
      rw [restrictField_circIn_g3pField_congr γ (g₂ := gC)
        (by simpa using g3wCut_eqOn_ball γ i true) p.1]
      rfl
    have hiff : g3pUfZ Z γ gB i p ∈ s ↔ g3pUfZ Z γ gC i (g3Φ γ i p) ∈ s := by
      rw [← locB, eU, locC]
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 ⟨⟨hiff.2 h1.1.1.1, hEB⟩, h1.1.2⟩
    · exact h2 ⟨⟨⟨hiff.1 h1.1.1, hEC⟩, h1.2⟩, hEsubB hEB⟩
  have mK1 : MeasurableSet K1 :=
    (measurable_g3Φ γ i ((mUfC.inter mEC).inter mG)).inter (hXB measurableSet_Ioo)
  have mOth : MeasurableSet Oth := (mUfB.inter mEB).inter mΦG
  have hd : |PB.real K1 - PB.real Oth| ≤ PB.real failB + PB.real (g3Φ γ i ⁻¹' T ∩ RB) := by
    refine (abs_measureReal_sub_le_measureReal_symmDiff mK1.nullMeasurableSet
      mOth.nullMeasurableSet).trans ?_
    refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hincl)).trans ?_
    exact measureReal_union_le _ _
  have hTr : PC.real T = r * PB.real (g3Φ γ i ⁻¹' T ∩ RB) :=
    cvr T mT (inter_subset_left.trans hEsubC)
  have hTle : PC.real T ≤ e₂ := by
    refine le_trans ?_ hfC
    refine (measureReal_mono inter_subset_right).trans (le_of_eq ?_)
    simp only [measureReal_def, measure_toMeasurable]
  have h1 := cvr _ ((mUfC.inter mEC).inter mG)
    ((inter_subset_left.trans inter_subset_right).trans hEsubC)
  have h2 := cvr _ (mEC.inter mG) (inter_subset_left.trans hEsubC)
  rw [measureReal_congr hK2] at h2
  rw [h1, h2]
  have hb : |PB.real Oth - a * PB.real (EB ∩ g3Φ γ i ⁻¹' G)| ≤ e₁ := hbody
  calc |r * PB.real K1 - a * (r * PB.real (EB ∩ g3Φ γ i ⁻¹' G))|
      = r * |PB.real K1 - a * PB.real (EB ∩ g3Φ γ i ⁻¹' G)| := by
        rw [← abs_of_pos hr0, ← abs_mul, abs_of_pos hr0]; ring_nf
    _ ≤ r * (|PB.real K1 - PB.real Oth| + |PB.real Oth - a * PB.real (EB ∩ g3Φ γ i ⁻¹' G)|) :=
        mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) hr0.le
    _ ≤ r * (PB.real failB + PB.real (g3Φ γ i ⁻¹' T ∩ RB) + e₁) :=
        mul_le_mul_of_nonneg_left (add_le_add hd hb) hr0.le
    _ = r * (PB.real failB + e₁) + PC.real T := by rw [hTr]; ring
    _ ≤ r * (e₂ + e₁) + e₂ := by gcongr
    _ = r * (e₁ + e₂) + e₂ := by ring

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- **Region locality at `x` for a family of profiles `gf η`** (hypothesis): on the margin event,
the region zoom and the full zoom of `Z` differ on each cylinder only on a set of small Palm
probability, for large `C`. -/
def G3pRegLocXZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (gf : ℝ → ℂ → ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) →
    (g3pPalmLaw γ (gf i.η) i).real
      ((g3pUZ Z γ (gf i.η) i ⁻¹' s ∩ {p | |g3pX γ (gf i.η) i p - i.t₁| + m < i.r₁}) ∆
        (g3pUfZ Z γ (gf i.η) i ⁻¹' s ∩ {p | |g3pX γ (gf i.η) i p - i.t₁| + m < i.r₁})) ≤ ε

/-- The `x`-half of the mixing body of scheme `C` for an abstract zoom. -/
def G3BodyCXZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3pPalmLaw γ (g3wProf γ) i).real (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩
          {p | |g3pX γ (g3wProf γ) i p - i.t₁| + m < i.r₁} ∩ G) -
        μ.real s * (g3pPalmLaw γ (g3wProf γ) i).real
          ({p | |g3pX γ (g3wProf γ) i p - i.t₁| + m < i.r₁} ∩ G)| ≤ ε

/-- The `R(x)`-half of the mixing body of scheme `C` for an abstract zoom. -/
def G3BodyCRZ (Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3pPalmLaw γ (g3wProf γ) i).real (g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
          {p | |g3pR γ (g3wProf γ) i p - i.t₂| + m < i.r₂} ∩ G) -
        ν.real t * (g3pPalmLaw γ (g3wProf γ) i).real
          ({p | |g3pR γ (g3wProf γ) i p - i.t₂| + m < i.r₂} ∩ G)| ≤ ε

/-- **(R-b) `x` side of `B → C` for an abstract zoom** (copy of `g3TCutToProfXStmt_holds`). -/
theorem g3TCutToProfXZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hLB : G3pRegLocXZ Z γ (g3wCut γ)) (hLC : G3pRegLocXZ Z γ (fun _ => g3wProf γ))
    {μ ν : Measure LawD} (hB : G3BodyBZ Z Z' γ μ ν) : G3BodyCXZ Z γ μ := by
  intro s hs δ η m hm ε hε
  by_cases hcon : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4
  · obtain ⟨hη, hηδ, hδ4⟩ := hcon
    set i₀ : G3Idx := ⟨(δ, η, 0), hη, hηδ, hδ4⟩ with hi₀
    set r₀ : ℝ := ((g3pZ γ (g3wProf γ) i₀)⁻¹ * g3pZ γ (g3wCut γ η) i₀).toReal with hr₀
    have hr₀0 : 0 ≤ r₀ := ENNReal.toReal_nonneg
    set e : ℝ := ε / (2 * (r₀ + 1)) with he
    have he0 : 0 < e := by positivity
    filter_upwards [hB.1 s hs δ η m hm e he0, hLB s hs δ η m hm e he0,
      hLC s hs δ η m hm e he0] with C h1 h2 h3 i hi G hG
    have h₁ : i.1.1 = i₀.1.1 := by rw [hi]
    have h₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi]
    have hiη : i.η = η := by show i.1.2.1 = η; rw [hi]
    have hr : ((g3pZ γ (g3wProf γ) i)⁻¹ * g3pZ γ (g3wCut γ i.η) i).toReal = r₀ := by
      rw [hr₀, hiη, g3pZ_congr (g := g3wProf γ) h₁ h₂, g3pZ_congr (g := g3wCut γ η) h₁ h₂]
    have hb := xside_index_boundZ hZm hγ hγ2 i hs hm subset_rfl subset_rfl hG
      (h1 i hi (g3Φ γ i ⁻¹' G) (measurableSet_g3Φ_preimage γ i hG)) (h2 i hi) (h3 i hi)
    rw [hr] at hb
    refine hb.trans ?_
    rw [he]
    have hpos : 0 < 2 * (r₀ + 1) := by positivity
    rw [show r₀ * (ε / (2 * (r₀ + 1)) + ε / (2 * (r₀ + 1))) + ε / (2 * (r₀ + 1)) =
      ε * ((2 * r₀ + 1) / (2 * (r₀ + 1))) by field_simp; ring]
    exact mul_le_of_le_one_right hε.le ((div_le_one hpos).2 (by linarith))
  · filter_upwards with C
    intro i hi
    have h2 : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4 := by
      have := i.2
      rwa [hi] at this
    exact absurd h2 hcon

/-- **(R-c) `R(x)` side of `B → C` for abstract zooms** (open; open for the plain zoom too). -/
def G3TCutToProfRStmtZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ μ ν : Measure LawD, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    G3BodyBZ Z Z' γ μ ν → G3BodyCRZ Z' γ ν

/-- **`B → C` from its `x` side (proved from region locality) and its `R(x)` side.** -/
theorem g3TCutToProfStmtZ_of (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hLB : G3pRegLocXZ Z γ (g3wCut γ)) (hLC : G3pRegLocXZ Z γ (fun _ => g3wProf γ))
    (hR : G3TCutToProfRStmtZ Z Z' γ) : G3TCutToProfStmtZ Z Z' γ :=
  fun μ ν hμ hν hB => ⟨g3TCutToProfXZ hZm hγ hγ2 hLB hLC hB, hR μ ν hμ hν hB⟩

end R18
end QuantumZipper
