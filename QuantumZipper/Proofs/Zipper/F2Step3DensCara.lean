import QuantumZipper.Proofs.Zipper.F2Step3DensSign
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.ReverseFlow
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Proofs.Complex.CaraBdry
import QuantumZipper.Proofs.Thm12.Semigroup
import QuantumZipper.Proofs.Zipper.UnzipInvariance
import QuantumZipper.Proofs.Zipper.F2Step2b

/-!
# F2 step (3), input (i): the boundary extension of `f_t⁻¹` near `(O⁻_t, O⁺_t)`

`Step3BdryExtStmt` holds (`step3BdryExt_holds`). For `t > 0` and `V' = vrev W t` (the
time-reversed driver), `f_t⁻¹ = revMap V' t` on `ℍ` (`UnzipInvariance.fwdMapInv_eq_revMap_timeRev`)
and `revMap V' t` has a Carathéodory extension `F` to `ℍ̄` (Pommerenke, *Boundary Behaviour of
Conformal Maps*, 1992, Thm 2.6; proved as `CaraR.revMapCaratheodory`, for the simple arc
`revHull V' t = η(0,t]`, Rohde–Schramm via `RS.rohdeSchrammSimple`). Then:

* `extInv W t = F` on `ℍ̄` (on `ℝ`, `invBdry W t x = lim_{ℍ ∋ w → x} F w = F x`);
* `O⁻_t = 0₋(V')` (`B5.sideImages_fst_eq_zeroMinus_vrev`) and `O⁺_t = 0₊(V')`: by the reflection
  `W ↦ −W`, `O⁺_t(W) = −O⁻_t(−W) = −0₋(−V') = 0₊(V')`, where `0₋(−V') = −0₊(V')` follows from the
  reflection `revMap (−V') t (−z̄) = −\overline{revMap V' t z}` (`LoewnerAlgebra.revMap_reflect`)
  passed to the boundary values (`revMapBdry_neg_eq`);
* on `V = {0₋ < Re z < 0₊}`, `F` is nonvanishing on `ℍ̄`: `F(ℍ) ⊆ ℍ`, and `F x ∉ ℝ` for real
  `x ∈ (0₋, 0₊)` (`IsCaratheodoryRevExt`).

The identification `O⁺_t = 0₊` via reflection and the bookkeeping are our own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace F2

section Det

variable {V : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ}

theorem im_vert (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

theorem tendsto_revMap_vertical (hF : Blueprint.IsCaratheodoryRevExt V T F) (x : ℝ) :
    Tendsto (fun y : ℝ => revMap V T ((x : ℂ) + (y : ℂ) * I)) (𝓝[>] 0) (𝓝 (F x)) := by
  have hFc : ContinuousWithinAt F Hbar (x : ℂ) := hF.2.1 _ (by simp [Hbar])
  have hp : Tendsto (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
    · have hc : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) := by fun_prop
      have := hc.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · show (0 : ℝ) ≤ ((x : ℂ) + (y : ℂ) * I).im
      rw [im_vert]
      exact le_of_lt hy
  refine (hFc.tendsto.comp hp).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  refine hF.1 ?_
  show 0 < ((x : ℂ) + (y : ℂ) * I).im
  rw [im_vert]
  exact hy

theorem revMapBdry_eq_of_cara (hF : Blueprint.IsCaratheodoryRevExt V T F) (x : ℝ) :
    revMapBdry V T x = F x :=
  (tendsto_revMap_vertical hF x).limUnder_eq

theorem revMapBdry_neg_eq (hV : Continuous V) (hT : 0 ≤ T) (hF : Blueprint.IsCaratheodoryRevExt V T F)
    (x : ℝ) : revMapBdry (-V) T x = -conj (F ((-x : ℝ) : ℂ)) := by
  unfold revMapBdry
  refine Tendsto.limUnder_eq ?_
  have hc : Continuous fun w : ℂ => -conj w := continuous_conj.neg
  refine ((hc.tendsto _).comp (tendsto_revMap_vertical hF (-x))).congr'
    (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hz : 0 < (((-x : ℝ) : ℂ) + (y : ℂ) * I).im := by
    rw [im_vert]
    exact hy
  have := LoewnerAlgebra.revMap_reflect V hV hT hz
  have e : -conj (((-x : ℝ) : ℂ) + (y : ℂ) * I) = (x : ℂ) + (y : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [e] at this
  exact this.symm

theorem zeroMinus_neg_eq (hV : Continuous V) (hT : 0 ≤ T) (hF : Blueprint.IsCaratheodoryRevExt V T F) :
    zeroMinus (-V) T = -zeroPlus V T := by
  unfold zeroMinus zeroPlus
  rw [← Real.sSup_neg]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_neg]
  rw [revMapBdry_neg_eq hV hT hF, revMapBdry_eq_of_cara hF, neg_pos]
  simp

end Det

/-- **Deterministic core of input (i).** -/
theorem exists_extInv_good {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t)
    (hK : IsSimpleCurveHull (revHull (B2.vrev W t) t))
    (hK' : IsSimpleCurveHull (revHull (B2.vrev (-W) t) t))
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol W (x : ℂ) t v)
    (halive' : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol (-W) (x : ℂ) t v) :
    ∃ V : Set ℂ, IsOpen V ∧
      (∀ s ∈ Ioo (sideImages W t).1 (sideImages W t).2, (s : ℂ) ∈ V) ∧
      ContinuousOn (extInv W t) (V ∩ Hbar) ∧ ∀ z ∈ V ∩ Hbar, extInv W t z ≠ 0 := by
  set V' := B2.vrev W t with hV'
  have hV'c : Continuous V' := B2.continuous_vrev hW t
  have hV'0 : V' 0 = 0 := B2.vrev_zero ht.le
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory V' hV'c hV'0 t ht hK
  have ha : (sideImages W t).1 = zeroMinus V' t :=
    B5.sideImages_fst_eq_zeroMinus_vrev hW hW0 ht hK halive
  have hb : (sideImages W t).2 = zeroPlus V' t := by
    obtain ⟨a, b, hL, hR⟩ := F1.exists_tendsto_sideImages_of_alive ht.le halive
    have h1 := F1.sideImages_reflect_swap ht.le hL hR
    have h2 := B5.sideImages_fst_eq_zeroMinus_vrev hW.neg (by simp [hW0]) ht hK' halive'
    have hvneg : B2.vrev (-W) t = -V' := by
      funext s; simp only [B2.vrev, Pi.neg_apply, hV']; ring
    rw [h1, hvneg, zeroMinus_neg_eq hV'c ht.le hF] at h2
    exact neg_inj.1 h2
  have hH : ∀ w ∈ H, fwdMapInv W t w = F w := by
    intro w hw
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht.le hw,
      ReverseFlow.revMap_congr_drive w (W' := V') fun s hs => (B2.vrev_of_mem hs).symm]
    exact (hF.1 hw).symm
  have hEq : ∀ z ∈ Hbar, extInv W t z = F z := by
    intro z hz
    by_cases hpos : 0 < z.im
    · simp only [extInv, hpos, ↓reduceIte]
      exact hH z hpos
    · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hpos) hz
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
      simp only [extInv, hpos, ↓reduceIte, invBdry]
      have hmem : (z.re : ℂ) ∈ closure H := by
        rw [CA.Car.closure_H_eq_Hbar]; simp [Hbar]
      have := mem_closure_iff_nhdsWithin_neBot.1 hmem
      rw [hzr]
      simp only [ofReal_re]
      refine Tendsto.limUnder_eq ?_
      refine (((hF.2.1 _ (by simp [Hbar])).mono fun w (hw : 0 < w.im) =>
        (le_of_lt hw : 0 ≤ w.im)).tendsto).congr' ?_
      exact eventually_nhdsWithin_of_forall fun w hw => (hH w hw).symm
  refine ⟨{z : ℂ | zeroMinus V' t < z.re ∧ z.re < zeroPlus V' t},
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const),
    fun s hs => ?_, (hF.2.1.mono inter_subset_right).congr fun z hz => hEq z hz.2,
    fun z hz => ?_⟩
  · rw [ha, hb] at hs
    simpa using hs
  · rw [hEq z hz.2]
    by_cases hpos : 0 < z.im
    · intro h0
      have := Semigroup.mem_H_revMap hV'c ht.le hpos
      rw [← hF.1 hpos, h0] at this
      simp [H] at this
    · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hpos) hz.2
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
      intro h0
      have him : (F (z.re : ℂ)).im = 0 := by rw [← hzr, h0]; simp
      rcases (hF.2.2.2.2.2.1 z.re).1 him with h | h
      · exact absurd h (not_le.2 hz.1.1)
      · exact absurd h (not_le.2 hz.1.2)

/-- **`Step3BdryExtStmt` holds.** -/
theorem step3BdryExt_holds : Step3BdryExtStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB _ _
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ
      hκ4.le P B hB,
    RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le P (-B) hB.neg,
    hB.cont, hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4.le,
    RS.ae_real_alive hB.neg hκ hκ4.le] with ω hK hK' hc h0 hal hal' t ht
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hdr : drive κ (-B) ω = -drive κ B ω := by
    funext s; simp [drive]
  rcases ht.eq_or_lt with rfl | ht'
  · refine ⟨∅, isOpen_empty, fun s hs => ?_, by simp, by simp⟩
    rw [B5.sideImages_fst_zero_time hW0, F2.sideImages_snd_zero_time hW0] at hs
    exact absurd hs (by simp)
  have hK1 : IsSimpleCurveHull (revHull (B2.vrev (-drive κ B ω) t) t) := by
    rw [← hdr]; exact hK' t ht'
  refine exists_extInv_good hWc hW0 ht' (hK t ht') hK1 (fun x hx => hal x hx t ht)
    fun x hx => ?_
  rw [← hdr]
  exact hal' x hx t ht

end F2
end QuantumZipper
