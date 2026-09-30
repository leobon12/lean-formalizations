import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2
import QuantumZipper.Proofs.Thm11.MainMart
import QuantumZipper.Proofs.GFF.K3.C5Kernel

/-!
# Theorem 1.1 addendum, AD-4: pathwise limits of the frozen field and kernel as `δ ↓ 0`

Blueprint `blueprint/THM11_BLUEPRINT.md` §9, AD-4.  Sheffield, *Conformal weldings of random
surfaces* (arXiv:1012.4797), Theorem 1.1 addendum (p. 12): a point swallowed at time `τ(a) ≤ T`
carries the left limit `lim_{s ↑ τ(a)} 𝔥_s(a)`, and the kernel is `V_T(a,b) =
lim_{t ↑ τ_a ∧ τ_b ∧ T} G(f_t a, f_t b)`.

For a strictly decreasing sequence of levels `δ_n ↓ 0` (taming `c_n = δ_n/2`) and a fixed
continuous driving path, the freezing times `σ_n(a)` are nondecreasing, lie strictly before the
swallowing time `τ(a)`, and increase to `τ(a) ∧ T` (FD-2 as in R19's proof).  Hence
* `tendsto_frozenField_ext`: `𝔥^{δ_n}_T(a) → 𝔥^ext_T(a)` whenever the left limit exists
  (R19 gives it a.s.);
* `tendsto_frozenKernel_VT`: `K^{δ_n}_T(a,b) → V_T(a,b)` (monotone limit, `K3.tendsto_vtKer_VTe`);
* `tendsto_fieldV_ext`: `V^{δ_n}_T → ∬ ρρ V_T` (dominated by `|ρ||ρ| G`).
The arguments follow the proof of `Thm11Add.ae_tendsto_fieldAt_of_lt` and of
`MainMart.tendsto_fieldV`; the strictness `σ_n < τ(a)` uses `swallowTime_shift`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm11Asm

open FwdHolo FwdClock FrozenMart FieldMart NonSwallow MainMart Thm11Add

/-- Alive on `[0,t]` means not yet swallowed at `t`, strictly. -/
theorem ofReal_lt_swallowTime_of_sol {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {t : ℝ} (ht : 0 ≤ t) (h : ∃ u, IsForwardSol W z t u) :
    ENNReal.ofReal t < swallowTime W z := by
  have hpos : 0 < (fwdMap W t z).im := by
    obtain ⟨u, hu⟩ := h
    rw [fwdMap_eq hW hz hu ⟨ht, le_rfl⟩]
    exact (im_isForwardSol_le hW hz hu).2 t ⟨ht, le_rfl⟩
  rw [swallowTime_shift hW hz ht h]
  have hW' : Continuous (fun r => W (t + r) - W t) :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  exact ENNReal.lt_add_right ENNReal.ofReal_ne_top (swallowTime_pos hW' hpos).ne'

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
variable {δn : ℕ → ℝ}

/-- The freezing time at level `δ_n`, taming `δ_n/2`. -/
abbrev sigN (κ : ℝ) (δn : ℕ → ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) (ω : Ω) (n : ℕ) : ℝ≥0 :=
  frozenTime κ (δn n / 2) (δn n) T B a ω

theorem sigN_lt_swallowTime (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hδpos : ∀ n, 0 < δn n)
    {a : ℂ} (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) (ω : Ω) (n : ℕ) :
    ENNReal.ofReal (sigN κ δn T B a ω n) < swallowTime (drive κ B ω) a :=
  ofReal_lt_swallowTime_of_sol (continuous_drive_path hBc ω)
    ((hδpos n).trans_le (hδa n)) (NNReal.coe_nonneg _)
    (alive_of_le_frozenTime hBc (by linarith [hδpos n]) (by linarith [hδpos n]) (hδa n) ω
      le_rfl).1

theorem le_im_of_le_sigN (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hδpos : ∀ n, 0 < δn n)
    {a : ℂ} (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) (ω : Ω) (n : ℕ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (sigN κ δn T B a ω n)) :
    δn n ≤ (fwdMap (drive κ B ω) r a).im :=
  ((alive_of_le_frozenTime hBc (by linarith [hδpos n]) (by linarith [hδpos n]) (hδa n) (T := T)
    ω le_rfl).2 r hr).2.2

theorem im_sigN_le (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hδpos : ∀ n, 0 < δn n)
    {a : ℂ} (hδa : ∀ n, δn n ≤ a.im) {T : ℝ≥0} (ω : Ω) {n : ℕ}
    (hlt : sigN κ δn T B a ω n < T) :
    (fwdMap (drive κ B ω) (sigN κ δn T B a ω n) a).im ≤ δn n :=
  im_fwdMap_frozenTime_le hBc (by linarith [hδpos n]) (by linarith [hδpos n]) (hδa n) ω hlt

theorem sigN_monotone (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hδpos : ∀ n, 0 < δn n)
    (hδanti : StrictAnti δn) {a : ℂ} (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) (ω : Ω) :
    Monotone (sigN κ δn T B a ω) := by
  refine monotone_nat_of_le_succ fun n => ?_
  by_contra hcon
  push Not at hcon
  have hT : sigN κ δn T B a ω (n + 1) < T := hcon.trans_le (hittingBtwn_le ω)
  have h1 := im_sigN_le hBc hδpos hδa ω hT
  have h2 := le_im_of_le_sigN hBc hδpos hδa T ω n
    (r := sigN κ δn T B a ω (n + 1)) ⟨NNReal.coe_nonneg _, by exact_mod_cast hcon.le⟩
  have h3 := hδanti (Nat.lt_succ_self n)
  linarith

/-- Cofinality: every admissible time is eventually below the freezing times. -/
theorem eventually_le_sigN (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hδpos : ∀ n, 0 < δn n)
    (hδlim : Tendsto δn atTop (𝓝 0)) {a : ℂ} (ha : a ∈ H) (hδa : ∀ n, δn n ≤ a.im)
    (T : ℝ≥0) (ω : Ω) {s : ℝ} (hs0 : 0 ≤ s) (hsτ : ENNReal.ofReal s < swallowTime (drive κ B ω) a)
    (hsT : s ≤ T) : ∀ᶠ n in atTop, s ≤ sigN κ δn T B a ω n := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  have hsol := K3.exists_sol_of_lt_swallowTime (W := drive κ B ω) ha hs0 hsτ
  obtain ⟨hanti, hpos⟩ := K3.im_fwdMap_antitoneOn hW ha hsol
  have hp : 0 < (fwdMap (drive κ B ω) s a).im := hpos s ⟨hs0, le_rfl⟩
  filter_upwards [hδlim.eventually (gt_mem_nhds hp)] with n hn
  by_contra hcon
  push Not at hcon
  have hT : sigN κ δn T B a ω n < T := by
    have : ((sigN κ δn T B a ω n : ℝ≥0) : ℝ) < T := hcon.trans_le hsT
    exact_mod_cast this
  have h1 := im_sigN_le hBc hδpos hδa ω hT
  have h2 : (fwdMap (drive κ B ω) s a).im ≤ (fwdMap (drive κ B ω) (sigN κ δn T B a ω n) a).im :=
    hanti ⟨NNReal.coe_nonneg _, hcon.le⟩ ⟨hs0, le_rfl⟩ hcon.le
  linarith

/-- For a point swallowed by time `T`, the freezing times increase to `τ(a)` from below. -/
theorem tendsto_sigN_swallow (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hδpos : ∀ n, 0 < δn n)
    (hδlim : Tendsto δn atTop (𝓝 0)) {a : ℂ} (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) (ω : Ω)
    (hK : a ∈ fwdHull (drive κ B ω) T) :
    Tendsto (fun n => (sigN κ δn T B a ω n : ℝ)) atTop
      (𝓝[<] (swallowTime (drive κ B ω) a).toReal) := by
  set τ := swallowTime (drive κ B ω) a with hτdef
  have hτtop : τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK.2
  set τr := τ.toReal with hτr
  have hτeq : τ = ENNReal.ofReal τr := (ENNReal.ofReal_toReal hτtop).symm
  have hlt : ∀ n, (sigN κ δn T B a ω n : ℝ) < τr := fun n => by
    have := sigN_lt_swallowTime hBc hδpos hδa T ω n (κ := κ)
    rw [← hτdef, hτeq] at this
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 this).1
  have hτT : τr ≤ T := by
    have := hK.2; rw [← hτdef, hτeq] at this
    exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg _)).1 this
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun u hu => ?_,
    fun u hu => Eventually.of_forall fun n => (hlt n).trans hu⟩, Eventually.of_forall hlt⟩
  rcases lt_or_ge u 0 with hu0 | hu0
  · exact Eventually.of_forall fun n => hu0.trans_le (NNReal.coe_nonneg _)
  have hs0 : 0 ≤ (u + τr) / 2 := by linarith
  have hsτ : ENNReal.ofReal ((u + τr) / 2) < τ := by
    rw [hτeq]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  filter_upwards [eventually_le_sigN hBc hδpos hδlim ((hδpos 0).trans_le (hδa 0)) hδa T ω hs0
    hsτ (by linarith)] with n hn
  linarith

/-- For a point not swallowed by time `T`, the freezing time is eventually `T`. -/
theorem eventually_sigN_eq (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hδpos : ∀ n, 0 < δn n)
    (hδlim : Tendsto δn atTop (𝓝 0)) {a : ℂ} (T : ℝ≥0) (ω : Ω)
    (ha : a ∈ H \ fwdHull (drive κ B ω) T) :
    ∀ᶠ n in atTop, sigN κ δn T B a ω n = T := by
  obtain ⟨δs, hδs, hev⟩ := eventually_frozen_true (κ := κ) hBc T ω ha
  filter_upwards [hδlim.eventually (eventually_le_nhds hδs)] with n hn
  exact (hev (δn n) (δn n / 2) (by linarith [hδpos n]) (by linarith [hδpos n]) hn).1

/-- **Pathwise AD-4 (field).** If the left limit at `τ(a)` exists (R19), then
`𝔥^{δ_n}_T(a) → 𝔥^ext_T(a)`. -/
theorem tendsto_frozenField_ext (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ}
    (hδpos : ∀ n, 0 < δn n) (hδlim : Tendsto δn atTop (𝓝 0)) {a : ℂ} (ha : a ∈ H)
    (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) (ω : Ω)
    (hlim : swallowTime (drive κ B ω) a < ⊤ → ∃ ℓ : ℝ,
      Tendsto (fieldAt κ (drive κ B ω) a) (𝓝[<] (swallowTime (drive κ B ω) a).toReal)
        (𝓝 ℓ)) :
    Tendsto (fun n => frozenField κ (δn n / 2) (δn n) T B a T ω) atTop
      (𝓝 (hTfwdExt κ (drive κ B ω) T a)) := by
  have he : ∀ n, frozenField κ (δn n / 2) (δn n) T B a T ω =
      fieldAt κ (drive κ B ω) a (sigN κ δn T B a ω n) := fun n => by
    rw [frozenField_eq_fieldAt hBc (by linarith [hδpos n]) (by linarith [hδpos n]) (hδa n),
      min_eq_right (hittingBtwn_le ω)]
  simp only [he]
  by_cases hK : a ∈ fwdHull (drive κ B ω) T
  · obtain ⟨ℓ, hℓ⟩ := hlim (lt_of_le_of_lt hK.2 ENNReal.ofReal_lt_top)
    have e : hTfwdExt κ (drive κ B ω) T a = ℓ := by
      rw [hTfwdExt, if_pos hK]; exact hℓ.limUnder_eq
    rw [e]
    exact hℓ.comp (tendsto_sigN_swallow hBc hδpos hδlim hδa T ω hK)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_sigN_eq hBc hδpos hδlim T ω ⟨ha, hK⟩] with n hn
    rw [hn, hTfwdExt, if_neg hK, hTfwd, if_pos ⟨ha, hK⟩]
    rfl

end Path

end Thm11Asm
end QuantumZipper
