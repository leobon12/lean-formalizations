import QuantumZipper.Proofs.Thm18.G2RootXPalm
import QuantumZipper.Proofs.Zipper.D3PlusIRich

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2, `x` side, cut form: assembly over the rooted point

`g2RootXCutStmt_of_palm : G2RootXPalmIdStmt γ → G2RootXFixStmt γ μ → G2RootXCutStmt γ μ`.

By the Palm identity both rooted quantities are `∫ ρ(x) a(x) dx` and `∫ ρ(x) b(x) dx` with
`a(x), b(x) ∈ [0, 1]` the probabilities of the shifted events at `x`, supported on the margin
window. For every `x`, eventually in `C` and uniformly in the outside event,
`|a(x) − μ(s) b(x)| ≤ ε'` (node F); the bad set `{x : not yet}` is not known to be measurable, so
its `ρ dx`-mass is controlled with the lower-integral dominated convergence
`D3Plus.tendsto_lintegral_of_ae_tendsto_nonmeas`. The total mass `∫_{margin} ρ` is finite since it
is a rooted quantity, bounded by `E ν_h[−δ, 0] = g3Z < ∞`.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The rooted measure is bounded by `E ν_h[−δ, 0] = g3Z`. -/
theorem g3RootInt_indicator_le_g3Z {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    (T : Set (Ω₀ × ℝ × ℝ)) : g3RootInt γ i (T.indicator 1) ≤ g3Z γ i := by
  have h1 : g3RootInt γ i (T.indicator 1) ≤ g3RootInt γ i ((univ : Set (Ω₀ × ℝ × ℝ)).indicator 1) :=
    lintegral_mono fun ω => lintegral_mono fun x =>
      indicator_le_indicator_of_subset (subset_univ _) (fun _ => bot_le) _
  have h2 := g3LenRoot_rooted hγ hγ2 i (T := univ) MeasurableSet.univ
  rw [show {p : Ω₀ × ℝ | (p.1, p.2, g3X γ i p) ∈ (univ : Set (Ω₀ × ℝ × ℝ))} = univ from rfl,
    g3LenRoot_univ] at h2
  exact h1.trans h2.symm.le

/-- Two-sided `ℝ≥0∞` bounds give a real bound. -/
theorem abs_toReal_sub_le_of_two_sided {A B E : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (hA : A ≠ ⊤)
    (hB : B ≠ ⊤) (hE : E ≠ ⊤) (h1 : A ≤ ENNReal.ofReal c * B + E)
    (h2 : ENNReal.ofReal c * B ≤ A + E) : |A.toReal - c * B.toReal| ≤ E.toReal := by
  have hcB : ENNReal.ofReal c * B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  have e : (ENNReal.ofReal c * B).toReal = c * B.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  have t1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hcB, hE⟩) h1
  have t2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA, hE⟩) h2
  rw [ENNReal.toReal_add hcB hE, e] at t1
  rw [ENNReal.toReal_add hA hE, e] at t2
  rw [abs_le]; constructor <;> linarith

/-- The shifted event only depends on the region geometry through the margin. -/
theorem g3RootXPalmEv_univ_univ (γ : ℝ) (i : G3Idx) (m κ x : ℝ) :
    g3RootXPalmEv γ i univ m κ univ x = {_ω | |x - i.t₁| + m < i.r₁} := by
  ext _ω; simp [g3RootXPalmEv]

theorem G3Idx.t₁_r₁_congr {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    i.t₁ = i'.t₁ ∧ i.r₁ = i'.r₁ := by
  unfold G3Idx.t₁ G3Idx.r₁ G3Idx.δ G3Idx.η
  rw [h₁, h₂]; exact ⟨rfl, rfl⟩

/-- Pointwise two-sided bound at a good or bad point. -/
theorem palm_pointwise {a b : ℝ≥0∞} {c ε' : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε' : 0 ≤ ε')
    (ha : a ≤ 1) (hb : b ≤ 1) (bad : ℝ≥0∞)
    (hgood : bad ≠ 1 → |a.toReal - c * b.toReal| ≤ ε') (hbad : bad = 0 ∨ bad = 1) :
    a ≤ ENNReal.ofReal c * b + (ENNReal.ofReal ε' + bad) ∧
      ENNReal.ofReal c * b ≤ a + (ENNReal.ofReal ε' + bad) := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb
  rcases hbad with h0 | h1
  · have hg := hgood (by rw [h0]; exact zero_ne_one)
    rw [abs_le] at hg
    rw [h0, add_zero]
    constructor
    · calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha').symm
        _ ≤ ENNReal.ofReal (c * b.toReal + ε') := ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal c * b + ENNReal.ofReal ε' := by
          rw [ENNReal.ofReal_add (mul_nonneg hc0 ENNReal.toReal_nonneg) hε',
            ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hb']
    · calc ENNReal.ofReal c * b = ENNReal.ofReal (c * b.toReal) := by
            rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hb']
        _ ≤ ENNReal.ofReal (a.toReal + ε') := ENNReal.ofReal_le_ofReal (by linarith)
        _ = a + ENNReal.ofReal ε' := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε', ENNReal.ofReal_toReal ha']
  · rw [h1]
    have hcb : ENNReal.ofReal c * b ≤ 1 :=
      (mul_le_mul' (ENNReal.ofReal_le_one.2 hc1) hb).trans_eq (one_mul 1)
    exact ⟨ha.trans (le_add_left le_add_self), hcb.trans (le_add_left le_add_self)⟩

/-- **The cut node from the Palm identity and the fixed-point zoom.** -/
theorem g2RootXCutStmt_of_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Measure LawD}
    [IsProbabilityMeasure μ] (hP : G2RootXPalmIdStmt γ) (hF : G2RootXFixStmt γ μ) :
    G2RootXCutStmt γ μ := by
  classical
  intro s hs δ η m κ hκ hκm ε hε
  have hsm : MeasurableSet s := measurableSet_lawCyl hs
  have hm : 0 < m := hκ.trans hκm
  by_cases h0 : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η
  swap
  · exact Eventually.of_forall fun C i hi => absurd ⟨i, by rw [hi], by rw [hi]⟩ h0
  obtain ⟨i₀, hδ₀, hη₀⟩ := h0
  set c : ℝ := μ.real s with hc
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c ≤ 1 := measureReal_le_one
  -- the reference density on the margin window, and its finite mass
  set ρ₀ : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEv γ i₀ univ m κ univ x) with hρ₀
  obtain ⟨hP₀, hρ₀m⟩ := hP i₀ univ MeasurableSet.univ m κ hm hκ univ MeasurableSet.univ
  set M : Measure ℝ := (volume.restrict (Icc (-i₀.δ) 0)).withDensity ρ₀ with hM
  have hMu : M univ = ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x := by
    rw [hM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hMfin : M univ ≠ ⊤ := by
    rw [hMu, ← hP₀]
    exact ((g3RootInt_indicator_le_g3Z hγ hγ2 i₀ _).trans_lt (g3Z_pos_lt_top hγ hγ2 i₀).2).ne
  have : IsFiniteMeasure M := ⟨lt_top_iff_ne_top.2 hMfin⟩
  set Z : ℝ := (M univ).toReal with hZ
  have hZ0 : 0 ≤ Z := ENNReal.toReal_nonneg
  set ε' : ℝ := ε / (2 * (Z + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'Z : ε' * Z ≤ ε / 2 := by
    have e : ε' * (Z + 1) = ε / 2 := by rw [hε']; field_simp
    nlinarith
  -- the bad set of points (not known to be measurable)
  set bad : ℝ → ℝ → ℝ≥0∞ := fun C x => if (∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G' →
        |(gffBase.P (g3RootXPalmEv γ i s m κ G' x)).toReal -
          c * (gffBase.P (g3RootXPalmEv γ i univ m κ G' x)).toReal| ≤ ε') then 0 else 1 with hbad
  have hbad01 : ∀ C x, bad C x = 0 ∨ bad C x = 1 := fun C x => by
    simp only [hbad]; split_ifs <;> simp
  have hbad1 : ∀ C x, bad C x ≤ 1 := fun C x => by
    rcases hbad01 C x with h | h <;> rw [h]; exact zero_le_one
  have hlim : Tendsto (fun C => ∫⁻ x, bad C x ∂M) atTop (𝓝 0) :=
    D3Plus.tendsto_lintegral_of_ae_tendsto_nonmeas bad hbad1 (ae_of_all _ fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hF s hs δ η m κ hκ hκm x ε' hε'0] with C hC
      simp only [hbad]; rw [ite_eq_left_iff.2 fun h => absurd hC h])
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by positivity)
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with C hC i hi G hG
  obtain ⟨G', hG', hGe⟩ := exists_outsideSigmaPalm_preimage i hG
  have hGe' : G = outEv i G' := hGe
  subst hGe'
  have hi₁ : i.1.1 = i₀.1.1 := by rw [hi, hδ₀]
  have hi₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi, hη₀]
  obtain ⟨ht, hr⟩ := G3Idx.t₁_r₁_congr hi₁ hi₂
  have hiδ : i.δ = i₀.δ := hi₁
  obtain ⟨hPa, hma⟩ := hP i s hsm m κ hm hκ G' hG'
  obtain ⟨hPb, hmb⟩ := hP i univ MeasurableSet.univ m κ hm hκ G' hG'
  rw [hiδ] at hma hmb
  rw [← g3RootEvXc_univ, hPa, hPb, hiδ]
  set a : ℝ → ℝ≥0∞ := fun x => gffBase.P (g3RootXPalmEv γ i s m κ G' x) with ha
  set b : ℝ → ℝ≥0∞ := fun x => gffBase.P (g3RootXPalmEv γ i univ m κ G' x) with hb
  set ρ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (rhoX γ x) with hρ
  have hma' : AEMeasurable (fun x => ρ x * a x) (volume.restrict (Icc (-i₀.δ) 0)) := hma
  have hmb' : AEMeasurable (fun x => ρ x * b x) (volume.restrict (Icc (-i₀.δ) 0)) := hmb
  have hpt : ∀ x, (ρ x * a x ≤ ENNReal.ofReal c * (ρ x * b x) +
      ρ₀ x * (ENNReal.ofReal ε' + bad C x) ∧
      ENNReal.ofReal c * (ρ x * b x) ≤ ρ x * a x + ρ₀ x * (ENNReal.ofReal ε' + bad C x)) ∧
      ρ x * a x ≤ ρ₀ x ∧ ρ x * b x ≤ ρ₀ x := by
    intro x
    by_cases hx : |x - i.t₁| + m < i.r₁
    · have hset : {_ω : Ω₀ | |x - i₀.t₁| + m < i₀.r₁} = univ :=
        eq_univ_of_forall fun _ => by rw [← ht, ← hr]; exact hx
      have hρ₀x : ρ₀ x = ρ x := by
        simp only [hρ₀, hρ, g3RootXPalmEv_univ_univ, hset, measure_univ, mul_one]
      have hax : a x ≤ 1 := prob_le_one
      have hbx : b x ≤ 1 := prob_le_one
      have hgood : bad C x ≠ 1 → |(a x).toReal - c * (b x).toReal| ≤ ε' := fun h => by
        simp only [hbad] at h
        split_ifs at h with hcond
        · exact hcond i hi G' hG'
        · exact absurd rfl h
      obtain ⟨p1, p2⟩ := palm_pointwise hc0 hc1 hε'0.le hax hbx (bad C x) hgood (hbad01 C x)
      rw [hρ₀x]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · calc ρ x * a x ≤ ρ x * (ENNReal.ofReal c * b x + (ENNReal.ofReal ε' + bad C x)) :=
              by gcongr
          _ = _ := by rw [mul_add, mul_left_comm]
      · calc ENNReal.ofReal c * (ρ x * b x) = ρ x * (ENNReal.ofReal c * b x) := mul_left_comm _ _ _
          _ ≤ ρ x * (a x + (ENNReal.ofReal ε' + bad C x)) := by gcongr
          _ = _ := by rw [mul_add]
      · exact (show ρ x * a x ≤ ρ x * 1 by gcongr).trans_eq (mul_one _)
      · exact (show ρ x * b x ≤ ρ x * 1 by gcongr).trans_eq (mul_one _)
    · have hempty : ∀ s' : Set LawD, g3RootXPalmEv γ i s' m κ G' x = ∅ := fun s' =>
        eq_empty_of_forall_notMem fun ω hω => hx hω.2.1
      have ha0 : a x = 0 := by simp only [ha, hempty, measure_empty]
      have hb0 : b x = 0 := by simp only [hb, hempty, measure_empty]
      simp only [ha0, hb0, mul_zero, zero_add, zero_le, and_self]
  have hfin₀ : ∀ᵐ x ∂(volume.restrict (Icc (-i₀.δ) 0)), ρ₀ x < ⊤ := ae_of_all _ fun x =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (prob_le_one.trans_lt ENNReal.one_lt_top)
  have hWD : ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x * (ENNReal.ofReal ε' + bad C x) =
      ENNReal.ofReal ε' * M univ + ∫⁻ x, bad C x ∂M := by
    rw [← lintegral_const, ← lintegral_add_left measurable_const]
    exact (lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hρ₀m hfin₀ _).symm
  set E : ℝ≥0∞ := ENNReal.ofReal ε' * M univ + ∫⁻ x, bad C x ∂M with hE
  have hI1 : ∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x ≤
      ENNReal.ofReal c * (∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x) + E := by
    calc ∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x
        ≤ ∫⁻ x in Icc (-i₀.δ) 0, (ENNReal.ofReal c * (ρ x * b x) +
            ρ₀ x * (ENNReal.ofReal ε' + bad C x)) := lintegral_mono fun x => (hpt x).1.1
      _ = (∫⁻ x in Icc (-i₀.δ) 0, ENNReal.ofReal c * (ρ x * b x)) +
            ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x * (ENNReal.ofReal ε' + bad C x) :=
          lintegral_add_left' (hmb'.const_mul _) _
      _ = _ := by rw [hWD]; congr 1; exact lintegral_const_mul'' _ hmb'
  have hI2 : ENNReal.ofReal c * ∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x ≤
      (∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x) + E := by
    calc ENNReal.ofReal c * ∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x
        = ∫⁻ x in Icc (-i₀.δ) 0, ENNReal.ofReal c * (ρ x * b x) :=
          (lintegral_const_mul'' _ hmb').symm
      _ ≤ ∫⁻ x in Icc (-i₀.δ) 0, (ρ x * a x + ρ₀ x * (ENNReal.ofReal ε' + bad C x)) :=
          lintegral_mono fun x => (hpt x).1.2
      _ = (∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x) +
            ∫⁻ x in Icc (-i₀.δ) 0, ρ₀ x * (ENNReal.ofReal ε' + bad C x) :=
          lintegral_add_left' hma' _
      _ = _ := by rw [hWD]
  have hA : ∫⁻ x in Icc (-i₀.δ) 0, ρ x * a x ≠ ⊤ :=
    ne_top_of_le_ne_top (hMu ▸ hMfin) (lintegral_mono fun x => (hpt x).2.1)
  have hB : ∫⁻ x in Icc (-i₀.δ) 0, ρ x * b x ≠ ⊤ :=
    ne_top_of_le_ne_top (hMu ▸ hMfin) (lintegral_mono fun x => (hpt x).2.2)
  have hbadfin : ∫⁻ x, bad C x ∂M ≠ ⊤ := (hC.trans ENNReal.ofReal_lt_top).ne
  have hEfin : E ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin, hbadfin⟩
  have hEle : E.toReal ≤ ε := by
    rw [hE, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin) hbadfin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hε'0.le, ← hZ]
    have h2 : (∫⁻ x, bad C x ∂M).toReal ≤ ε / 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hC.le
    linarith
  exact (abs_toReal_sub_le_of_two_sided hc0 hA hB hEfin hI1 hI2).trans hEle

end Thm18Asm
end QuantumZipper
