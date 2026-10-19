import GaussianLQG.Uniform.Holder.Assembly
import GaussianLQG.Uniform.InterfacesCons

/-!
# U12: uniform LFPP-level moments of the `1/2`-Hölder constant

Phase B, packet PB-U12 (B-8). Ledger `blueprint/phaseB/uniform-ledger.tex`, statement U12
(`holder_moment_unif`), Finding `fd:U12` (changes (i)–(vii), exponent bookkeeping `1 − 4ξ − 2/q`),
row U12 of §`subsec:ledger-cons`; audit B-0b, findings S-2 (general boxes) and M-1 (the constant of
`prop2_expMoment_int`). Inputs: the interfaces `IfaceMomentsLambdaU` (U10) and `IfaceScaleU` (U11)
of `GaussianLQG/Uniform/InterfacesCons.lean`, and nothing else unproved.

For `q ≥ 1` let `ξ_q = min(1/32, 1/max(q,16))` and `p = ⌈max(q,16)⌉₊`. Then for every `R > 0`
there is `C < ∞`, chosen before the probability space, such that for every white noise, every
`ξ ∈ (0, ξ_q]` and every `n`,
`E[ A_{V'_R}(λ_n^{-1} D_n(·,·; V_R))^q ] ≤ C`, where `D_n(·,·; V_R)` is the LFPP distance of
`e^{ξ φ_{0,n}}` internal to `V_R = boxOut R = [-R-1, R+1]²` and `A_{V'_R}` the `1/2`-Hölder constant
over pairs in `V'_R = boxIn R = [-R, R]²` (`holder_moment_unif`, `holder_moment_box`).

Proof (ledger Finding `fd:U12`): dyadic chaining in the half-integer offset unit squares
`c + [0,1]² ⊆ [-N, N]²`, `N = ⌈R⌉₊` (`Holder/Geom.lean`, `Holder/Chain.lean`; audit S-2), down to
level `n − 1`, with straight segments below the cutoff; at each level a union bound in `L^p` over
`≤ 4|A| 4^K` crossings, independence of `φ_{0,K}` and `φ_{K,n}`, the coarse field through
DDDF (2.11) and Jensen (`Holder/Moments.lean`; audit M-1), U10 for the crossings and U11(a) for
`λ_{n−K}` (`Holder/Level.lean`); Minkowski over the levels (`Holder/Lp.lean`); `x^q ≤ 1 + x^p`
(`Holder/Assembly.lean`). The Hölder constant is bounded a.s. by a measurable majorant, so its own
measurability (ledger change (vii)) is never needed.

`holder_moment_unit` is the unit-square form (ledger U12a of audit S-2, internal distance and pairs
in `[0,1]²`); `ifaceHolderMomentU` gives the orchestrator's interface `IfaceHolderMomentU`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise Holder

/-- **U12 on a covered domain, with the explicit exponent `ξ_q = min(1/32, 1/max(q,16))`**: for
covering data `ChainGeom A Q T P` and a domain `S ⊇ Q`, the `q`-th moment of the `1/2`-Hölder
constant over `T` of `λ_n^{-1} D_n(·,·; S)` is bounded uniformly in the white noise, in
`ξ ∈ (0, ξ_q]` and in `n`. -/
theorem holder_moment_gen (hmom : IfaceMomentsLambdaU) (hscale : IfaceScaleU) {q : ℝ}
    (hq : 1 ≤ q) {A : Finset ℂ} {Q T : Set ℂ} {Pn : ℕ} (G : ChainGeom A Q T Pn)
    (hne : Q.Nonempty) {S : Set ℂ} (hQS : Q ⊆ S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) (min (1 / 32) (1 / max q 16)), ∀ n : ℕ,
          ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
            (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) S z.1 z.2).toReal) T ^ q ∂P ≤ C := by
  -- the order of the moments: `p = ⌈max(q,16)⌉₊`
  set q' := max q 16 with hq'
  have hq'16 : (16 : ℝ) ≤ q' := le_max_right _ _
  have hqq' : q ≤ q' := le_max_left _ _
  set p : ℕ := ⌈q'⌉₊ with hp_def
  have hp1 : q' ≤ p := Nat.le_ceil _
  have hp2 : (p : ℝ) < q' + 1 := Nat.ceil_lt_add_one (by linarith)
  have hp16 : 16 ≤ p := by
    have : (16 : ℝ) ≤ p := hq'16.trans hp1
    exact_mod_cast this
  -- the constants, chosen before the probability space
  obtain ⟨C10, hC10⟩ := hmom (p : ℝ) (by linarith)
  obtain ⟨Cs, hCs, hsc⟩ := hscale
  obtain ⟨K₀, hK₀, hexp⟩ := lintegral_exp_supQ_le
  refine ⟨1 + ENNReal.ofReal ((48 * Pn * holderB A.card p K₀ (max C10 0) Cs) ^ p) +
    ENNReal.ofReal ((Real.exp (Cs + 4 * Real.log 2) * √(Pn : ℝ)) ^ q *
      (A.card * (4 : ℝ) ^ (1 + K₀))),
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩, ?_⟩
  intro Ω _ P W hW ξ hξ n
  obtain ⟨hξ0, hξq⟩ := hξ
  have hξ1 : ξ ≤ 1 / 32 := hξq.trans (min_le_left _ _)
  have hξ2 : ξ ≤ 1 / q' := hξq.trans (min_le_right _ _)
  have hq'0 : 0 < q' := by linarith
  have hpξ : (p : ℝ) * ξ ≤ 3 / 2 := by
    calc (p : ℝ) * ξ ≤ (q' + 1) * ξ := mul_le_mul_of_nonneg_right hp2.le hξ0.le
      _ ≤ (q' + 1) * (1 / q') := mul_le_mul_of_nonneg_left hξ2 (by positivity)
      _ = 1 + 1 / q' := by field_simp
      _ ≤ 3 / 2 := by
          have : 1 / q' ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hq'16
          linarith
  have hqξ : q * ξ ≤ 1 := by
    calc q * ξ ≤ q' * (1 / q') := mul_le_mul hqq' hξ2 hξ0.le hq'0.le
      _ = 1 := by field_simp
  have hξ8 : ξ ∈ Set.Ioc (0 : ℝ) (1 / 8) := ⟨hξ0, by linarith⟩
  -- the interfaces at this noise and this `ξ`
  have hlam : ∀ m, 0 < lambdaN ξ W P m :=
    fun m => lt_of_lt_of_le (Real.exp_pos _) (hsc hW ξ hξ8 m).2.2.2.1
  have hmom' : ∀ m : ℕ, ∫⁻ ω, rectLen ξ (fun x => phiMN W P 0 m x ω) (rectAB 2 1) ^ p ∂P ≤
      ENNReal.ofReal (max C10 0 * lambdaN ξ W P m ^ p) := fun m =>
    lintegral_rectLen_pow_le hW (hlam m)
      (hC10 hW ξ hξ8 m 2 1 (by simp [shapeSet])).1
  have hexp' := fun K γ (h0 : 0 ≤ γ) (h1 : γ ≤ 3 / 2) => hexp hW G hne K γ h0 h1
  rcases le_or_gt n 1 with hn | hn
  · refine (lintegral_holder_small hW hξ0 hξ1 (by linarith) hqξ G hQS hK₀ hexp' hCs hn (hlam n)
      (hsc hW ξ hξ8 n).2.2.2.1).trans ?_
    exact le_add_self
  · refine (lintegral_holder_large hW hξ0 hξ1 hq (p := p) hp16 (hqq'.trans hp1) hpξ G hne hQS
      hexp' (le_max_right _ _) hmom' hCs hlam (n := n) (by omega) (hsc hW ξ hξ8 n).1
      (hsc hW ξ hξ8 n).2.2.2.1).trans ?_
    exact le_self_add

/-- **U12 on the boxes, with the explicit exponent** `ξ_q = min(1/32, 1/max(q,16))`:
pairs in `V'_R = boxIn R = [-R,R]²`, distance internal to `V_R = boxOut R = [-R-1,R+1]²`. -/
theorem holder_moment_box (hmom : IfaceMomentsLambdaU) (hscale : IfaceScaleU) {q : ℝ}
    (hq : 1 ≤ q) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) (min (1 / 32) (1 / max q 16)), ∀ n : ℕ,
          ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
            (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) (boxOut R) z.1 z.2).toReal)
            (boxIn R) ^ q ∂P ≤ C := by
  have hN : 1 ≤ ⌈R⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hR).ne'
  refine holder_moment_gen hmom hscale hq (chainGeom_box hN (Nat.le_ceil R)) ⟨0, ?_⟩
    (boxIn_sub_boxOut R (Nat.ceil_lt_add_one hR.le).le)
  simp only [boxIn, mem_ofPred_eq, Complex.zero_re, Complex.zero_im, abs_zero, Nat.cast_nonneg,
    and_self]

/-- **U12** (ledger `holder_moment_unif`, exactly): uniform `q`-th moments of the `1/2`-Hölder
constant over `V'_R = [-R,R]²` of the LFPP distance internal to `V_R = [-R-1,R+1]²`, normalized by
`λ_n`; the exponent `ξ_q = min(1/32, 1/max(q,16))` is chosen before the box. -/
theorem holder_moment_unif (hmom : IfaceMomentsLambdaU) (hscale : IfaceScaleU) (q : ℝ)
    (hq : 1 ≤ q) : ∃ ξq : ℝ, 0 < ξq ∧ ∀ R : ℝ, 0 < R → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) ξq, ∀ n : ℕ,
          ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
            (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) (boxOut R) z.1 z.2).toReal)
            (boxIn R) ^ q ∂P ≤ C :=
  ⟨min (1 / 32) (1 / max q 16), lt_min (by norm_num) (by positivity),
    fun _ hR => holder_moment_box hmom hscale hq hR⟩

/-- **U12a** (audit B-0b, S-2 (i)): the unit-square form, internal distance and pairs in
`[0,1]²`. -/
theorem holder_moment_unit (hmom : IfaceMomentsLambdaU) (hscale : IfaceScaleU) (q : ℝ)
    (hq : 1 ≤ q) : ∃ ξq : ℝ, 0 < ξq ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) ξq, ∀ n : ℕ,
          ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
            (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) Blueprint.closedUnitSquare z.1 z.2).toReal)
            Blueprint.closedUnitSquare ^ q ∂P ≤ C :=
  ⟨min (1 / 32) (1 / max q 16), lt_min (by norm_num) (by positivity),
    holder_moment_gen hmom hscale hq chainGeom_unit ⟨0, by
      simp only [Blueprint.closedUnitSquare, mem_ofPred_eq, Complex.zero_re, Complex.zero_im,
        le_refl, zero_le_one, and_self]⟩ subset_rfl⟩

/-- **The interface `IfaceHolderMomentU`** (`GaussianLQG/Uniform/InterfacesLFPP.lean`) from U10 and
U11. -/
theorem ifaceHolderMomentU (hmom : IfaceMomentsLambdaU) (hscale : IfaceScaleU) :
    IfaceHolderMomentU :=
  fun q hq => holder_moment_unif hmom hscale q hq

end Uniform
end GaussianLQG
