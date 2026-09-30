import QuantumZipper.Proofs.Thm18.ASepGoodPar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (good parameters, part 2): `ParGood` from the A-sep separation hypothesis at `τ' = 0`

`parGood_of_backSep`: if the folded circle `fc(d, r)` gives no mass to a `δ`-neighbourhood of the
reverse hull at `p = (τ, a)` and the flow from every nonzero real point survives for all time,
then `p` is a good parameter (`ParGood`): the flow from `a w` survives until `τ + δ'` for every
`w` in a closed `δ'`-neighbourhood of the folded sphere in the closed upper half-plane.

* `local_lower_upto`: the continuation lower bound of `local_lower_of_isForwardSol` with constants
  uniform over the sub-intervals `[0, s] ⊆ [0, S]`;
* `survive_near`: points of `ℍ` near a point surviving until `S` survive until `S`
  (continuation by `CoreArc.exists_isForwardSol_beyond`);
* `survive_margin`: a uniform time margin near a point of `ℍ̄` that is nonzero and, if in `ℍ`,
  not swallowed by time `τ`;
* compactness of the closed neighbourhood of the folded sphere.

Own elementary argument (continuous dependence and continuation for the Loewner ODE, Lawler,
*Conformally invariant processes in the plane*, §4.1).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- **Continuation lower bound, uniform over sub-intervals.** -/
theorem local_lower_upto {W : ℝ → ℝ} {z : ℂ} {S : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z S u) (hS : 0 ≤ S) :
    ∃ μ > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) S, ∀ z' : ℂ, ∀ v : ℝ → ℂ, IsForwardSol W z' s v →
      ‖z' - z‖ < δ → ∀ r ∈ Icc (0 : ℝ) s, μ ≤ ‖v r‖ := by
  obtain ⟨a, ha, hua⟩ := exists_pos_lower_of_isForwardSol hu hS
  have ha2 : 0 < a / 2 := by positivity
  set K : ℝ := 2 / (a * (a / 2)) with hK
  refine ⟨a / 2, ha2, a / 2 / Real.exp (K * S), by positivity, ?_⟩
  intro s hs z' v hv hzz
  have hus : IsForwardSol W z s u := isForwardSol_restrict hu hs.1 hs.2
  have hua' : ∀ r ∈ Icc (0 : ℝ) s, a ≤ ‖u r‖ := fun r hr => hua r ⟨hr.1, hr.2.trans hs.2⟩
  have claim : ∀ r ∈ Icc (0 : ℝ) s, ‖u r - v r‖ < a / 2 := by
    by_contra hcon
    push_neg at hcon
    set St : Set ℝ := Icc (0 : ℝ) s ∩ (fun r => ‖u r - v r‖) ⁻¹' Ici (a / 2) with hSt
    have hSc : IsClosed St :=
      (continuous_norm.comp_continuousOn (hus.1.sub hv.1)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Ici
    obtain ⟨r0, hr0, hr0'⟩ := hcon
    have hSne : St.Nonempty := ⟨r0, hr0, hr0'⟩
    have hSb : BddBelow St := ⟨0, fun x hx => hx.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set t := sInf St with ht
    have hbefore : ∀ r ∈ Ico (0 : ℝ) t, a ≤ ‖u r‖ ∧ a / 2 ≤ ‖v r‖ := by
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) s := ⟨hr.1, (hr.2.le).trans hmem.1.2⟩
      have hrS : r ∉ St := fun h => absurd (csInf_le hSb h) (not_le.mpr hr.2)
      have hlt : ‖u r - v r‖ < a / 2 := by
        by_contra h'
        exact hrS ⟨hrT, not_lt.mp h'⟩
      have hur := hua' r hrT
      have := norm_sub_norm_le (u r) (u r - v r)
      rw [sub_sub_cancel] at this
      exact ⟨hur, by linarith⟩
    have hg := norm_sol_sub_le_gronwall hus hv hmem.1 ha ha2 hbefore
    have hexp : Real.exp (2 / (a * (a / 2)) * t) ≤ Real.exp (K * S) := by
      apply Real.exp_le_exp.mpr
      rw [hK]
      exact mul_le_mul_of_nonneg_left (hmem.1.2.trans hs.2) (by positivity)
    have hEpos : 0 < Real.exp (K * S) := Real.exp_pos _
    have hlt : ‖z - z'‖ * Real.exp (K * S) < a / 2 := by
      rw [norm_sub_rev]
      calc ‖z' - z‖ * Real.exp (K * S) < a / 2 / Real.exp (K * S) * Real.exp (K * S) :=
            mul_lt_mul_of_pos_right hzz hEpos
        _ = a / 2 := div_mul_cancel₀ _ hEpos.ne'
    have hge : a / 2 ≤ ‖u t - v t‖ := hmem.2
    have := hg.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg _))
    linarith
  intro r hr
  have h1 := claim r hr
  have h2 := hua' r hr
  have := norm_sub_norm_le (u r) (u r - v r)
  rw [sub_sub_cancel] at this
  linarith

/-- **Survival is open in `ℍ`** (near any point, real or not, that survives until `S`). -/
theorem survive_near {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} {S : ℝ} (hS : 0 < S)
    {u : ℝ → ℂ} (hu : IsForwardSol W z S u) :
    ∃ η > 0, ∀ z' : ℂ, 0 < z'.im → ‖z' - z‖ < η → ∃ v, IsForwardSol W z' S v := by
  obtain ⟨μ, hμ, δ, hδ, hlow⟩ := local_lower_upto hu hS.le
  refine ⟨δ, hδ, fun z' hz' hzz => ?_⟩
  by_contra hno
  set I : Set ℝ := {s | s ∈ Icc (0 : ℝ) S ∧ ∃ v, IsForwardSol W z' s v} with hI
  obtain ⟨T0, hT0, v0, hv0⟩ := exists_isForwardSol_small hW hz'
  have hm0 : min T0 S ∈ I :=
    ⟨⟨le_min hT0.le hS.le, min_le_right _ _⟩, v0,
      isForwardSol_restrict hv0 (le_min hT0.le hS.le) (min_le_left _ _)⟩
  have hbdd : BddAbove I := ⟨S, fun s hs => hs.1.2⟩
  set s₀ := sSup I with hs₀
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le (lt_min hT0 hS) (le_csSup hbdd hm0)
  have hs₀S : s₀ ≤ S := csSup_le ⟨_, hm0⟩ fun s hs => hs.1.2
  have hex : ∀ s ∈ Ico (0 : ℝ) s₀, ∃ v, IsForwardSol W z' s v := by
    intro s hs
    obtain ⟨s', hs'I, hss'⟩ := exists_lt_of_lt_csSup ⟨_, hm0⟩ hs.2
    obtain ⟨v, hv⟩ := hs'I.2
    exact ⟨v, isForwardSol_restrict hv hs.1 hss'.le⟩
  have hbd : ∀ s ∈ Ico (0 : ℝ) s₀, μ ≤ ‖fwdMap W s z'‖ := by
    intro s hs
    obtain ⟨v, hv⟩ := hex s hs
    have hsS : s ∈ Icc (0 : ℝ) S := ⟨hs.1, hs.2.le.trans hs₀S⟩
    rw [fwdMap_eq hW hz' hv ⟨hs.1, le_rfl⟩]
    exact hlow s hsS z' v hv hzz s ⟨hs.1, le_rfl⟩
  obtain ⟨S', hS', v, hv⟩ := CoreArc.exists_isForwardSol_beyond hW hz' hs₀pos hμ hex hbd
  rcases le_or_gt S S' with h | h
  · exact hno ⟨v, isForwardSol_restrict hv hS.le h⟩
  · have hmem : S' ∈ I := ⟨⟨hs₀pos.le.trans hS'.le, h.le⟩, v, hv⟩
    exact absurd (le_csSup hbdd hmem) (not_le.2 hS')

/-- **Uniform time margin near a surviving point of `ℍ̄`.** -/
theorem survive_margin {W : ℝ → ℝ} (hW : Continuous W)
    (hreal : ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol W (x : ℂ) T v)
    {τ : ℝ} (hτ : 0 < τ) {z : ℂ} (hz : 0 ≤ z.im) (hz0 : z ≠ 0)
    (hH : 0 < z.im → z ∈ H \ fwdHull W τ) :
    ∃ ε > 0, ∃ η > 0, ∀ z' : ℂ, 0 ≤ z'.im → ‖z' - z‖ < η →
      ∃ v, IsForwardSol W z' (τ + ε) v := by
  have him : ∀ z' : ℂ, |z'.im - z.im| ≤ ‖z' - z‖ := fun z' => by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rcases hz.lt_or_eq with hpos | hzero
  · obtain ⟨-, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff hτ.le).1 (hH hpos)
    obtain ⟨η, hη, hnear⟩ := survive_near hW (hτ.trans hT') hu
    refine ⟨T' - τ, by linarith, min η z.im, lt_min hη hpos, fun z' hz' hzz => ?_⟩
    have h1 := him z'
    have hz'pos : 0 < z'.im := by
      have := abs_le.1 h1; linarith [min_le_right η z.im, this.1]
    rw [show τ + (T' - τ) = T' by ring]
    exact hnear z' hz'pos (hzz.trans_le (min_le_left _ _))
  · have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
    have hre0 : z.re ≠ 0 := fun h => hz0 (by rw [hzr, h, Complex.ofReal_zero])
    obtain ⟨u, hu⟩ := hreal z.re hre0 (τ + 1) (by linarith)
    obtain ⟨η, hη, hnear⟩ := survive_near hW (by linarith : (0 : ℝ) < τ + 1) hu
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    refine ⟨1, one_pos, min η ‖z‖, lt_min hη hzn, fun z' hz' hzz => ?_⟩
    rcases hz'.lt_or_eq with hp' | hz'0
    · exact hnear z' hp' (by rw [← hzr]; exact hzz.trans_le (min_le_left _ _))
    · have hz'r : z' = ((z'.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hz'0])
      have hne : z'.re ≠ 0 := by
        intro h
        have h0 : z' = 0 := by rw [hz'r, h, Complex.ofReal_zero]
        rw [h0, zero_sub, norm_neg] at hzz
        exact absurd (hzz.trans_le (min_le_right _ _)) (lt_irrefl _)
      rw [hz'r]
      exact hreal z'.re hne (τ + 1) (by linarith)

/-- **`ParGood` from the A-sep separation hypothesis at `τ' = 0`.** -/
theorem parGood_of_backSep {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hreal : ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol W (x : ℂ) T v)
    {d : ℂ} {r : ℝ} (hr : 0 < r) {p : Fin 2 → ℝ} (hτ : 0 < p 0) (ha : 0 < p 1)
    (hsep : ∃ δ : ℝ, 0 < δ ∧ foldedCircle d r
      (Metric.thickening δ (revHull (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) = 0) :
    ParGood W (foldSph d r) p := by
  obtain ⟨δ, hδ, hnull⟩ := hsep
  have sp := sep_pointwise hW hW0 hτ ha hδ hnull
  set a := p 1 with hadef
  set τ := p 0 with hτdef
  set C : Set ℂ := cthickening (δ / 2) (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im} with hC
  have hCc : IsCompact C :=
    ((isCompact_foldSph d r).cthickening).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  have hm : ∀ w : C, ∃ ε > 0, ∃ η > 0, ∀ z' : ℂ, 0 ≤ z'.im →
      ‖z' - (a : ℂ) * w‖ < η → ∃ v, IsForwardSol W z' (τ + ε) v := by
    rintro ⟨w, hw⟩
    obtain ⟨hw0, hwH⟩ := sp w hw
    refine survive_margin hW hreal hτ ?_ ?_ ?_
    · show 0 ≤ ((a : ℂ) * w).im
      have : 0 ≤ w.im := hw.2
      simpa using mul_nonneg ha.le this
    · exact mul_ne_zero (by exact_mod_cast ha.ne') hw0
    · intro hpos
      refine hwH ?_
      have : 0 < ((a : ℂ) * w).im := hpos
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero] at this
      exact pos_of_mul_pos_right this ha.le
  choose εf hεf ηf hηf hsol using hm
  obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun w : C => ball (w : ℂ) (ηf w / a))
    (fun _ => isOpen_ball) (fun w hw => mem_iUnion.2 ⟨⟨w, hw⟩, mem_ball_self (by
      have := hηf ⟨w, hw⟩; positivity)⟩)
  obtain ⟨ε0, hε0, hε0le⟩ : ∃ ε0 > 0, ∀ i ∈ t, ε0 ≤ εf i := by
    rcases t.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨t.inf' h εf, (Finset.lt_inf'_iff h).2 fun i _ => hεf i,
        fun i hi => Finset.inf'_le _ hi⟩
  refine ⟨hτ, ha, min (δ / 2) ε0, lt_min (by positivity) hε0, fun w hw => ?_⟩
  have hwC : w ∈ C := ⟨cthickening_mono (min_le_left _ _) _ hw.1, hw.2⟩
  obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.1 (ht hwC)
  have hdist : ‖(a : ℂ) * w - (a : ℂ) * i‖ < ηf i := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le, ← dist_eq_norm]
    have := mem_ball.1 hwi
    rw [lt_div_iff₀ ha] at this
    linarith
  have hwim : 0 ≤ ((a : ℂ) * w).im := by
    have : 0 ≤ w.im := hw.2
    simpa using mul_nonneg ha.le this
  obtain ⟨v, hv⟩ := hsol i _ hwim hdist
  exact ⟨v, isForwardSol_restrict hv (by
    have := lt_min (half_pos hδ) hε0; rw [← hτdef]; linarith)
    (by linarith [min_le_right (δ / 2) ε0, hε0le i hi])⟩

end ASep
end QuantumZipper
