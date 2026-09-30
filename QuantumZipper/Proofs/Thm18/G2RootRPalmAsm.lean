import QuantumZipper.Proofs.Thm18.G2RootRPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2, `R(x)` side, cut form: assembly over the rooted point

`g2RootRCutStmt_of_palm : G2RootRPalmIdStmt γ → G2RootRFixStmt γ ν → G2RootRCutStmt γ ν`, the
twin of `g2RootXCutStmt_of_palm` (`G2RootXPalmAsm.lean`): Palm identity, pointwise bounds from the
fixed-point node, and the lower-integral dominated convergence
`D3Plus.tendsto_lintegral_of_ae_tendsto_nonmeas` for the (not necessarily measurable) set of
points where the fixed-point bound does not yet hold. The Palm mass of the window is finite by
`lintegral_rhoX_Icc_lt_top`. Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- **The cut node from the Palm identity and the fixed-point zoom.** -/
theorem g2RootRCutStmt_of_palm {γ : ℝ} (hγ : 0 < γ) {μ : Measure LawD}
    [IsProbabilityMeasure μ] (hP : G2RootRPalmIdStmt γ) (hF : G2RootRFixStmt γ μ) :
    G2RootRCutStmt γ μ := by
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
  set b₀ : ℝ := i₀.t₂ + i₀.r₂ with hb₀
  set ρ₀ : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (rhoX γ x) * gffBase.P (g3PalmEvR γ i₀ univ m κ univ x) with hρ₀
  obtain ⟨-, hρ₀m⟩ := hP i₀ univ MeasurableSet.univ m κ hm hκ univ MeasurableSet.univ
  set M : Measure ℝ := (volume.restrict (Icc 0 b₀)).withDensity ρ₀ with hM
  have hMu : M univ = ∫⁻ x in Icc 0 b₀, ρ₀ x := by
    rw [hM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hMfin : M univ ≠ ⊤ := by
    rw [hMu]
    refine (lt_of_le_of_lt (lintegral_mono fun x => ?_) (lintegral_rhoX_Icc_lt_top hγ b₀)).ne
    exact (show ρ₀ x ≤ ENNReal.ofReal (rhoX γ x) * 1 by
      simp only [hρ₀]; gcongr; exact prob_le_one).trans_eq (mul_one _)
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
      ∀ G' : Set (CondR i), MeasurableSet G' →
        |(gffBase.P (g3PalmEvR γ i s m κ G' x)).toReal -
          c * (gffBase.P (g3PalmEvR γ i univ m κ G' x)).toReal| ≤ ε') then 0 else 1 with hbad
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
  obtain ⟨ht, hr⟩ := G3Idx.t₂_r₂_congr hi₂
  have hib : i.t₂ + i.r₂ = b₀ := by rw [hb₀, ht, hr]
  have hT := measurableSet_truncSet i hG'
  obtain ⟨hPa, hma⟩ := hP i s hsm m κ hm hκ (truncSet i G') hT
  obtain ⟨hPb, hmb⟩ := hP i univ MeasurableSet.univ m κ hm hκ (truncSet i G') hT
  rw [hib] at hma hmb
  rw [← g3RootEvRc_univ, g3RootEvRc_eq, g3RootEvRc_eq, hPa, hPb, hib]
  set a : ℝ → ℝ≥0∞ := fun x => gffBase.P (g3PalmEvR γ i s m κ (truncSet i G') x) with ha
  set b : ℝ → ℝ≥0∞ := fun x => gffBase.P (g3PalmEvR γ i univ m κ (truncSet i G') x) with hb
  set ρ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (rhoX γ x) with hρ
  have hma' : AEMeasurable (fun x => ρ x * a x) (volume.restrict (Icc 0 b₀)) := hma
  have hmb' : AEMeasurable (fun x => ρ x * b x) (volume.restrict (Icc 0 b₀)) := hmb
  have hpt : ∀ x, (ρ x * a x ≤ ENNReal.ofReal c * (ρ x * b x) +
      ρ₀ x * (ENNReal.ofReal ε' + bad C x) ∧
      ENNReal.ofReal c * (ρ x * b x) ≤ ρ x * a x + ρ₀ x * (ENNReal.ofReal ε' + bad C x)) ∧
      ρ x * a x ≤ ρ₀ x ∧ ρ x * b x ≤ ρ₀ x := by
    intro x
    by_cases hx : |x - i.t₂| + m < i.r₂
    · have hset : {_ω : Ω₀ | |x - i₀.t₂| + m < i₀.r₂} = univ :=
        eq_univ_of_forall fun _ => by rw [← ht, ← hr]; exact hx
      have hρ₀x : ρ₀ x = ρ x := by
        simp only [hρ₀, hρ, g3PalmEvR_univ_univ, hset, measure_univ, mul_one]
      have hax : a x ≤ 1 := prob_le_one
      have hbx : b x ≤ 1 := prob_le_one
      have hgood : bad C x ≠ 1 → |(a x).toReal - c * (b x).toReal| ≤ ε' := fun h => by
        simp only [hbad] at h
        split_ifs at h with hcond
        · exact hcond i hi (truncSet i G') hT
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
    · have hempty : ∀ s' : Set LawD, g3PalmEvR γ i s' m κ (truncSet i G') x = ∅ := fun s' =>
        eq_empty_of_forall_notMem fun ω hω => hx hω.2.1
      have ha0 : a x = 0 := by simp only [ha, hempty, measure_empty]
      have hb0 : b x = 0 := by simp only [hb, hempty, measure_empty]
      simp only [ha0, hb0, mul_zero, zero_add, zero_le, and_self]
  have hfin₀ : ∀ᵐ x ∂(volume.restrict (Icc 0 b₀)), ρ₀ x < ⊤ := ae_of_all _ fun x =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (prob_le_one.trans_lt ENNReal.one_lt_top)
  have hWD : ∫⁻ x in Icc 0 b₀, ρ₀ x * (ENNReal.ofReal ε' + bad C x) =
      ENNReal.ofReal ε' * M univ + ∫⁻ x, bad C x ∂M := by
    rw [← lintegral_const, ← lintegral_add_left measurable_const]
    exact (lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hρ₀m hfin₀ _).symm
  set E : ℝ≥0∞ := ENNReal.ofReal ε' * M univ + ∫⁻ x, bad C x ∂M with hE
  have hI1 : ∫⁻ x in Icc 0 b₀, ρ x * a x ≤
      ENNReal.ofReal c * (∫⁻ x in Icc 0 b₀, ρ x * b x) + E := by
    calc ∫⁻ x in Icc 0 b₀, ρ x * a x
        ≤ ∫⁻ x in Icc 0 b₀, (ENNReal.ofReal c * (ρ x * b x) +
            ρ₀ x * (ENNReal.ofReal ε' + bad C x)) := lintegral_mono fun x => (hpt x).1.1
      _ = (∫⁻ x in Icc 0 b₀, ENNReal.ofReal c * (ρ x * b x)) +
            ∫⁻ x in Icc 0 b₀, ρ₀ x * (ENNReal.ofReal ε' + bad C x) :=
          lintegral_add_left' (hmb'.const_mul _) _
      _ = _ := by rw [hWD]; congr 1; exact lintegral_const_mul'' _ hmb'
  have hI2 : ENNReal.ofReal c * ∫⁻ x in Icc 0 b₀, ρ x * b x ≤
      (∫⁻ x in Icc 0 b₀, ρ x * a x) + E := by
    calc ENNReal.ofReal c * ∫⁻ x in Icc 0 b₀, ρ x * b x
        = ∫⁻ x in Icc 0 b₀, ENNReal.ofReal c * (ρ x * b x) :=
          (lintegral_const_mul'' _ hmb').symm
      _ ≤ ∫⁻ x in Icc 0 b₀, (ρ x * a x + ρ₀ x * (ENNReal.ofReal ε' + bad C x)) :=
          lintegral_mono fun x => (hpt x).1.2
      _ = (∫⁻ x in Icc 0 b₀, ρ x * a x) +
            ∫⁻ x in Icc 0 b₀, ρ₀ x * (ENNReal.ofReal ε' + bad C x) :=
          lintegral_add_left' hma' _
      _ = _ := by rw [hWD]
  have hA : ∫⁻ x in Icc 0 b₀, ρ x * a x ≠ ⊤ :=
    ne_top_of_le_ne_top (hMu ▸ hMfin) (lintegral_mono fun x => (hpt x).2.1)
  have hB : ∫⁻ x in Icc 0 b₀, ρ x * b x ≠ ⊤ :=
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
