import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Zipper.E1CoordChange2
import QuantumZipper.Proofs.Zipper.F1Side

/-!
# B5-V endpoints (2): the left side image is `0₋` of the time-reversed driver

Task B5V-FIX (`handoff/B5.md`, R1 (d)). For a continuous driver `W` with `W 0 = 0`, `s > 0`,
every real `x ≠ 0` alive at time `s` under the forward flow, and a simple reverse hull of
`V' = vrev W s` at time `s`:
`(sideImages W s).1 = zeroMinus (vrev W s) s` (**`sideImages_fst_eq_zeroMinus_vrev`**), i.e.
`O⁻_s = 0₋^{V'}(s)`.

* `isRealRevSol_vrev_of_isForwardSol`: a forward solution from a real point, read backwards in
  time, is a real reverse solution for `vrev W s` (time reversal of the Loewner ODE);
* the identity: the values `f_s(y)`, `y < 0`, are exactly the points of `(−∞, 0₋^{V'}(s))` alive
  through time `s` under the reverse flow of `V'`, and `O⁻_s` is their supremum.

Own elementary proof (time reversal of an ODE and uniqueness of real solutions; the identity
`g_t = h_t^{-1}` for the reversed driver is Lawler, *Conformally invariant processes in the
plane*, §4.1, stated there for the complex maps).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace B5

open B2

/-- Solutions of the forward flow started at a real point take real values (conjugation and
uniqueness). -/
theorem im_eq_zero_of_isForwardSol_real {W : ℝ → ℝ} {T x : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) {t : ℝ} (ht : t ∈ Icc 0 T) : (u t).im = 0 := by
  have huc : IsForwardSol W (x : ℂ) T fun s => (starRingEnd ℂ) (u s) := by
    simpa using F1.isForwardSol_conj hu
  have h : (starRingEnd ℂ) (u t) = u t := F1.isForwardSol_unique_gronwall huc hu ht
  have h2 : -(u t).im = (u t).im := by simpa using congrArg Complex.im h
  linarith

/-- **Time reversal.** A forward solution from a real point `y`, read backwards, is a real
reverse solution for `vrev W s` from `(f s).re`. -/
theorem isRealRevSol_vrev_of_isForwardSol {W : ℝ → ℝ} {s y : ℝ} {f : ℝ → ℂ} (hs : 0 ≤ s)
    (hf : IsForwardSol W (y : ℂ) s f) :
    IsRealRevSol (vrev W s) (f s).re s (fun r => (f (s - r)).re) := by
  set φ : ℝ → ℝ := fun q => (f q).re with hφ
  have him : ∀ q ∈ Icc 0 s, f q = (φ q : ℂ) := fun q hq => by
    apply Complex.ext
    · simp [φ]
    · simp [φ, im_eq_zero_of_isForwardSol_real hf hq]
  have hφne : ∀ q ∈ Icc 0 s, φ q ≠ 0 := fun q hq h =>
    (hf.2 q hq).1 (by rw [him q hq, h, Complex.ofReal_zero])
  have hφc : ContinuousOn φ (Icc 0 s) := Complex.continuous_re.comp_continuousOn hf.1
  have hc : ContinuousOn (fun q => 2 / φ q) (Icc 0 s) := continuousOn_const.div hφc hφne
  have heq : ∀ q ∈ Icc 0 s, φ q = y - W q + ∫ p in (0 : ℝ)..q, 2 / φ p := by
    intro q hq
    have h := (hf.2 q hq).2
    have hI : ∫ p in (0 : ℝ)..q, 2 / f p = ((∫ p in (0 : ℝ)..q, 2 / φ p : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun p hp => ?_
      rw [uIcc_of_le hq.1] at hp
      simp only [him p ⟨hp.1, hp.2.trans hq.2⟩, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [hI] at h
    have h2 := congrArg Complex.re h
    simpa [φ] using h2
  have hmaps : MapsTo (fun r => s - r) (Icc 0 s) (Icc 0 s) := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine ⟨hφc.comp (continuous_const.sub continuous_id).continuousOn hmaps, fun r hr => ?_⟩
  have hsr := hmaps hr
  refine ⟨hφne _ hsr, ?_⟩
  have e1 := heq _ hsr
  have e2 := heq s ⟨hs, le_rfl⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, hs⟩ hsr)).intervalIntegrable (μ := volume))
    ((hc.mono (uIcc_subset_Icc hsr ⟨hs, le_rfl⟩)).intervalIntegrable (μ := volume))
  have hsub : ∫ q in (0 : ℝ)..r, 2 / φ (s - q) = ∫ p in s - r..s, 2 / φ p := by
    rw [intervalIntegral.integral_comp_sub_left (fun p => 2 / φ p) s, sub_zero]
  rw [vrev_of_mem hr]
  show φ (s - r) = φ s - (W (s - r) - W s) - ∫ q in (0 : ℝ)..r, 2 / φ (s - q)
  rw [hsub]
  linarith

/-- **`O⁻_s = 0₋^{V'}(s)`** for `V' = vrev W s`. -/
theorem sideImages_fst_eq_zeroMinus_vrev {W : ℝ → ℝ} {s : ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hs : 0 < s) (hK : IsSimpleCurveHull (revHull (vrev W s) s))
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol W (x : ℂ) s v) :
    (sideImages W s).1 = zeroMinus (vrev W s) s := by
  set V' := vrev W s with hV'
  have hV'c : Continuous V' := continuous_vrev hW s
  have hV'0 : V' 0 = 0 := vrev_zero hs.le
  set fS : ℝ → ℝ := fun y => (fwdMap W s y).re with hfS
  have hval : ∀ y : ℝ, y < 0 → fS y < 0 ∧ ∃ g, IsRealRevSol V' (fS y) s g ∧ g s = y := by
    intro y hy
    obtain ⟨f, hf⟩ := halive y hy.ne
    have hR := isRealRevSol_vrev_of_isForwardSol hs.le hf
    have hf0 : f 0 = y := by rw [F1.isForwardSol_zero hf hs.le, hW0]; simp
    have hgs : (fun r => (f (s - r)).re) s = y := by simp [hf0]
    simp only [hfS]
    rw [F1.fwdMap_eq_of_isForwardSol hf ⟨hs.le, le_rfl⟩]
    refine ⟨?_, _, hR, hgs⟩
    by_contra hz
    push Not at hz
    obtain ⟨p, hp, hp0⟩ := intermediate_value_Icc' hs.le hR.1
      (⟨by simp only [sub_self, hf0, Complex.ofReal_re]; exact hy.le,
        by simp only [sub_zero]; exact hz⟩ : (0 : ℝ) ∈ Icc _ _)
    exact (hR.2 p hp).1 hp0
  have hmono : ∀ y y' : ℝ, y < y' → y' < 0 → fS y < fS y' := by
    intro y y' h h'
    obtain ⟨-, g, hg, hgs⟩ := hval y (h.trans h')
    obtain ⟨-, g', hg', hg's⟩ := hval y' h'
    rcases lt_trichotomy (fS y) (fS y') with hlt | heq | hgt
    · exact hlt
    · rw [heq] at hg
      have := RealLine.isRealRevSol_unique hV'c hs.le hg hg' ⟨hs.le, le_rfl⟩
      rw [hgs, hg's] at this
      exact absurd this h.ne
    · have := RealLine.isRealRevSol_lt hV'c hs.le hg' hg hgt
      rw [hgs, hg's] at this
      exact absurd h (not_lt.2 this.le)
  have hle : ∀ y : ℝ, y < 0 → fS y ≤ zeroMinus V' s := by
    intro y hy
    obtain ⟨hz0, g, hg, -⟩ := hval y hy
    by_contra hlt
    push Not at hlt
    have := (realHitTime_lt_iff hV'c hV'0 hs hK hz0.le).2 hlt
    exact absurd (RealLine.ofReal_le_realHitTime hs.le hg) (not_le.2 this)
  have hex : ∀ z, z < zeroMinus V' s → ∃ y, y < 0 ∧ fS y = z := by
    intro z hz2
    have hτ := ofReal_lt_realHitTime hV'c hV'0 hs hK hs le_rfl hz2
    obtain ⟨v, hv⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime hτ
    have hz0 : z < 0 := hz2.trans (zeroMinus_neg_of_le hV'c hV'0 hs hK hs le_rfl)
    have hy : v s < 0 := by
      have := E1.realRevMap_neg hV'c hV'0 hs.le hz0 hτ
      rwa [RealLine.realRevMap_eq hV'c hv hs.le le_rfl] at this
    obtain ⟨-, g, hg, hgs⟩ := hval (v s) hy
    exact ⟨v s, hy, RealLine.eq_of_isRealRevSol_eq hV'c hs.le hg hv hgs⟩
  have hlim : Tendsto fS (𝓝[<] 0) (𝓝 (zeroMinus V' s)) := by
    refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
    · obtain ⟨z, hz1, hz2⟩ := exists_between hl
      obtain ⟨y₀, hy₀, hfy₀⟩ := hex z hz2
      filter_upwards [Ioo_mem_nhdsLT hy₀] with y hy
      exact hz1.trans (hfy₀ ▸ hmono _ _ hy.1 hy.2)
    · filter_upwards [self_mem_nhdsWithin] with y (hy : y < 0)
      exact (hle y hy).trans_lt hu
  exact hlim.limUnder_eq

end B5
end QuantumZipper
