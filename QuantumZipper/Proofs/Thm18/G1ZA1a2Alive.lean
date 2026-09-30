import QuantumZipper.Proofs.Thm18.G1ZA1aBdry
import QuantumZipper.Proofs.Zipper.UnifClSide
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Thm14.WeldingData

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a2: real points stay alive for a good driver

`real_alive_of_good`: for a good driver `W` (`G1zDrvGood`), every real `y ≠ 0` has a solution of
the forward Loewner equation on `[0,T]` for every `T ≥ 0` (it is never swallowed). This removes
the `halive` hypotheses of the side-image lemmas for good drivers.

Route (own argument on top of proved project facts):
* `y < 0`: with `V = trev W T` (so `f_T⁻¹ = revMap V T`), `revHull V T = K_T` is a simple-curve hull,
  the reverse swallowed set is `[0⁻, b]` (`B5.swallowedSet_eq_Icc_zeroMinus`), and on `(−∞, 0⁻)`
  the Carathéodory extension `F` of `revMap V T` (Pommerenke, *Boundary Behaviour of Conformal
  Maps*, Thm 2.6; `CaraR.revMapCaratheodory`) is the real reverse flow map, which tends to `−∞` at
  `−∞` (`CaraR.tendsto_realRevMap_atBot`) and to `F(0⁻) = 0` at `0⁻`. By the intermediate value
  theorem `y = F x` for some `x < 0⁻`, and the time reversal of the real reverse solution from `x`
  is a forward solution from `y` (`RegUnif.isForwardSol_of_isRealRevSol_rev`).
* `y > 0`: reflect, `z ↦ −z̄`, `W ↦ −W` (`F1.isForwardSol_conj`, `RS.isForwardSol_neg`).
-/

noncomputable section

open Filter Set Complex Function
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

open QuantumZipper.CA QuantumZipper.CA.Uniformizer

/-- Reflection of forward solutions: `W ↦ −W`, `z ↦ −z̄`. -/
theorem isForwardSol_refl {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W z T u) :
    IsForwardSol (fun t => -W t) (refl z) T (fun t => refl (u t)) := by
  have h := RS.isForwardSol_neg (F1.isForwardSol_conj hu)
  simpa [CA.Uniformizer.refl] using h

theorem mem_fwdHull_neg_iff {W : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    z ∈ fwdHull (fun t => -W t) T ↔ refl z ∈ fwdHull W T := by
  have hsol : ∀ (V : ℝ → ℝ) (w : ℂ) (S : ℝ), (∃ u, IsForwardSol (fun t => -V t) w S u) →
      ∃ u, IsForwardSol V (refl w) S u := fun V w S ⟨u, hu⟩ => by
    have h := isForwardSol_refl hu
    simp only [neg_neg] at h
    exact ⟨_, h⟩
  rw [LoewnerAlgebra.mem_fwdHull_iff hT, LoewnerAlgebra.mem_fwdHull_iff hT, refl_mem_H_iff]
  refine and_congr_right fun _ => ⟨fun h S hS hex => h S hS ?_, fun h S hS hex => h S hS ?_⟩
  · obtain ⟨u, hu⟩ := hex
    have := hsol (fun t => -W t) (refl z) S ⟨u, by simpa using hu⟩
    simpa [refl_refl] using this
  · exact hsol W z S hex

theorem isSimpleCurveHull_fwdHull_neg {W : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hK : IsSimpleCurveHull (fwdHull W T)) : IsSimpleCurveHull (fwdHull (fun t => -W t) T) := by
  obtain ⟨γ, hc, hi, h0, hH, hKγ⟩ := hK
  refine ⟨fun s => refl (γ s), continuous_refl.comp_continuousOn hc,
    fun x hx y hy hxy => hi hx hy (refl_injective hxy), by simpa using h0,
    fun s hs => refl_mem_H_iff.2 (hH s hs), ?_⟩
  ext z
  rw [mem_fwdHull_neg_iff hT, hKγ]
  constructor
  · rintro ⟨s, hs, hsz⟩
    exact ⟨s, hs, by show refl (γ s) = z; rw [hsz, refl_refl]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, (refl_refl _).symm⟩

/-- **Negative real points are alive** when `K_T` is a simple-curve hull. -/
theorem alive_neg_of_hull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (hK : IsSimpleCurveHull (fwdHull W T)) {y : ℝ} (hy : y < 0) :
    ∃ v, IsForwardSol W (y : ℂ) T v := by
  set V := ArcDriver.trev W T with hVdef
  have hVc : Continuous V := ArcDriver.continuous_trev hW T
  have hV0 : V 0 = 0 := ArcDriver.trev_zero W T
  have hK' : IsSimpleCurveHull (revHull V T) := by
    rw [hVdef, ArcDriver.revHull_trev hW hW0 hT]; exact hK
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory V hVc hV0 T hT hK'
  obtain ⟨hzm, b, hb, hS⟩ := B5.swallowedSet_eq_Icc_zeroMinus hVc hV0 hT hK'
  set zm := zeroMinus V T with hzmdef
  have hsol : ∀ x : ℝ, x < zm → ∃ u, IsRealRevSol V x T u := fun x hx =>
    CaraR.not_mem_swallowedSet_iff.1 (by rw [hS]; exact fun h => absurd h.1 (not_le.2 hx))
  have hFx : ∀ x : ℝ, x < zm → F x = (realRevMap V T x : ℂ) := fun x hx => by
    obtain ⟨u, hu⟩ := hsol x hx
    rw [RealLine.realRevMap_eq hVc hu hT.le le_rfl]
    exact tendsto_nhds_unique (Thm14WeldingData.tendsto_revMap_of_car hF x)
      (RealLine.tendsto_revMap_of_isRealRevSol hVc hu ⟨hT.le, le_rfl⟩)
  set G : ℝ → ℝ := fun x => (F x).re with hG
  have hGc : Continuous G := by
    have h1 : ContinuousOn F Hbar := hF.2.1
    have h2 : Continuous fun x : ℝ => F x :=
      h1.comp_continuous Complex.continuous_ofReal fun x => by simp [Hbar]
    exact Complex.continuous_re.comp h2
  have hGzm : G zm = 0 := by
    show (F zm).re = 0
    rw [hF.2.2.2.1]; simp
  have hGx : ∀ x : ℝ, x < zm → G x = realRevMap V T x := fun x hx => by
    show (F x).re = _
    rw [hFx x hx]; simp
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, x₁ < zm ∧ realRevMap V T x₁ < y := by
    have h := (CaraR.tendsto_realRevMap_atBot hVc hT.le).eventually (eventually_lt_atBot y)
    obtain ⟨x, hx⟩ := (h.and (eventually_lt_atBot zm)).exists
    exact ⟨x, hx.2, hx.1⟩
  have hivt := intermediate_value_Icc hx₁.1.le hGc.continuousOn
  have hyI : y ∈ Icc (G x₁) (G zm) :=
    ⟨by rw [hGx x₁ hx₁.1]; exact hx₁.2.le, by rw [hGzm]; exact hy.le⟩
  obtain ⟨x, hxI, hxy⟩ := hivt hyI
  have hxzm : x < zm := by
    rcases eq_or_lt_of_le hxI.2 with h | h
    · rw [h, hGzm] at hxy; exact absurd hxy.symm hy.ne
    · exact h
  obtain ⟨u, hu⟩ := hsol x hxzm
  have huT : u T = y := by
    rw [← RealLine.realRevMap_eq hVc hu hT.le le_rfl, ← hGx x hxzm]; exact hxy
  have h := RegUnif.isForwardSol_of_isRealRevSol_rev hT.le hW0 (fun r _ => rfl) hu
  rw [huT] at h
  exact ⟨_, h⟩

/-- **Real points are alive for a good driver.** -/
theorem real_alive_of_good {W : ℝ → ℝ} (hG : G1zDrvGood W) {T : ℝ} (hT : 0 ≤ T) {y : ℝ}
    (hy : y ≠ 0) : ∃ v, IsForwardSol W (y : ℂ) T v := by
  have hW := hG.1
  have hW0 := hG.2.1
  rcases hT.eq_or_lt with h0 | hT
  · subst h0
    refine ⟨fun _ => (y : ℂ) - W 0, continuousOn_const, fun s hs => ?_⟩
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    refine ⟨by rw [hW0]; simpa using hy, by simp⟩
  have hK : IsSimpleCurveHull (fwdHull W T) := by
    have h := isSimpleCurveHull_fwdHull_shift hW hW0 hG.2.2.2.1 hG.2.2.2.2 le_rfl hT
    have e : (fun s => W (0 + s) - W 0) = W := by funext s; simp [hW0]
    rwa [e, sub_zero] at h
  rcases hy.lt_or_gt with hneg | hpos
  · exact alive_neg_of_hull hW hW0 hT hK hneg
  · have hWn : Continuous fun t => -W t := hW.neg
    obtain ⟨v, hv⟩ := alive_neg_of_hull hWn (by simp [hW0]) hT
      (isSimpleCurveHull_fwdHull_neg hT.le hK) (neg_lt_zero.2 hpos)
    have h := RS.isForwardSol_neg hv
    simp only [neg_neg, Complex.ofReal_neg] at h
    exact ⟨_, h⟩

end G1ZA1a
end Thm18Asm
end QuantumZipper
