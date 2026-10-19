import GaussianLQG.Uniform.InverseMoments.Strip
import GaussianLQG.Uniform.InterfacesCons

/-!
# Uniform inverse separated-distance moments (Route U, item U13)

Phase B, packet PB-U13 (ledger packet B-9). Mathematical source: the uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statement U13 and its ledger row (§`subsec:ledger-cons`),
in the corrected form of the audit `planning/audits/B0b-ledger-audit.md` (S-1: the infimum is
taken in `ℝ≥0∞`, since the ledger's real-valued `⨅ R ∈ stripFam K₀ δ, (…).toReal` is junk `0`;
M-4: `δ ≤ 1`). The planar part U13 (a) is in `InverseMoments/Planar.lean`.

**Statement** (`inv_moment_unif`, given the interfaces `IfaceMomentsLambdaU` (U10) and
`IfaceScaleU` (U11) of `GaussianLQG/Uniform/InterfacesCons.lean`): for `q ≥ 1` and
`ξq' = min (1/8) (1/q)`, for every compact `K₀` and `δ ∈ (0, 1]` there is `C < ∞`, chosen before
the probability space and before `ξ`, with
`E[(λ_n / min_{strips R} L_n(R))^q] ≤ C` for every white noise, `ξ ∈ (0, ξq']` and `n`, where
the strips are `T20D.RS (k δ) j`, `j ∈ T20D.shortJ (k δ) b`, `b ∈ blockSet K₀ (k δ)`,
`k δ = ⌈log₂(4/δ)⌉₊` (`kDelta`), crossed the short way.

**Proof** (ledger row `inv_moment_unif`; audit §3). Union bound over the finitely many strips
(`div_biInf_rpow_le_sum`, `blockSet_finite`). For one strip, with `k = k(δ) ≥ 2`,
`h = 2^{-k}`:
* motion invariance moves the strip to `h R_{1,3} ⊆ [0,1]²` (`lintegral_stripLen_eq`);
* `n ≥ k`: `φ_{0,n} = φ_{0,k} + φ_{k,n}` a.s. (`ae_phiMN_add`), so
  `L_n ≥ e^{-ξ M_k} L(φ_{k,n})` with `M_k = sup_{[0,1]²}|φ_{0,k}|`; Young's inequality
  `e^u v ≤ e^{3u/2} + v³` and `qξ ≤ 1` give
  `(λ_n/L_n)^q ≤ e^{(3/2) M_k} + (λ_n/L(φ_{k,n}))^{3q}`. Then `E e^{(3/2) M_k} ≤ 4^{(3/2)k + K√k}`
  (DDDF (2.11)), `L(φ_{k,n}) =ᵈ h L_{n-k}(R_{1,3})` (DDDF (2.30), `dddf_eq230`),
  `λ_n ≤ e^{C k} λ_{n-k}` (U11 (b) iterated) and `E[(λ_{n-k}/L_{n-k}(R_{1,3}))^{3q}] ≤ C₃`
  (U10 at order `3q`);
* `n < k`: `L_n ≥ e^{-ξ M_n} h` (`rectLen_ge`) and `λ_n ≤ 3 e^{ξ² n log 2/2} ≤ 3 e^k`
  (U11 (d)), so `(λ_n/L_n)^q ≤ (3e^k/h)^q e^{(3/2) M_n}`.
The constants depend on `(q, K₀, δ)` only. Helpers (and the one-strip bound
`lintegral_originStrip_le`) are in the namespace `GaussianLQG.Uniform.InvMom`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace InvMom

/-! ### Real inequalities -/

/-- Young's inequality in the form `e^u v ≤ e^{3u/2} + v³` (`v ≥ 0`) -/
lemma exp_mul_le_young (u : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    Real.exp u * v ≤ Real.exp (3 / 2 * u) + v ^ 3 := by
  set s := Real.exp (u / 2) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hss : Real.exp u = s * s := by rw [hs, ← Real.exp_add]; congr 1; ring
  have hs3 : Real.exp (3 / 2 * u) = s * s * s := by
    rw [hs, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hss, hs3]
  rcases le_or_gt v s with h | h
  · have : s * s * v ≤ s * s * s := mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith [pow_nonneg hv 3]
  · have h2 : s * s ≤ v * v := mul_self_le_mul_self hs0.le h.le
    have : s * s * v ≤ v * v * v := mul_le_mul_of_nonneg_right h2 hv
    nlinarith [mul_pos (mul_pos hs0 hs0) hs0]

/-- the pointwise bound of the regime `n ≥ k`: if `ℓ' ≤ e^{ξ M} ℓ` and `qξ ≤ 1`, then
`(λ/ℓ)^q ≤ e^{(3/2) M} + (λ/ℓ')^{3q}` -/
lemma ratio_rpow_le_of_cmp {lam ℓ ℓ' M ξ q : ℝ} (hlam : 0 ≤ lam) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hqξ : q * ξ ≤ 1)
    (hcmp : ℓ' ≤ Real.exp (ξ * M) * ℓ) :
    (lam / ℓ) ^ q ≤ Real.exp (3 / 2 * M) + (lam / ℓ') ^ (3 * q) := by
  set e := Real.exp (ξ * M) with he
  have he0 : 0 < e := Real.exp_pos _
  have h1 : lam / ℓ ≤ e * (lam / ℓ') := by
    calc lam / ℓ = e * lam / (e * ℓ) := (mul_div_mul_left lam ℓ he0.ne').symm
      _ ≤ e * lam / ℓ' := div_le_div_of_nonneg_left (by positivity) hℓ' hcmp
      _ = e * (lam / ℓ') := mul_div_assoc _ _ _
  have hv : 0 ≤ (lam / ℓ') ^ q := Real.rpow_nonneg (div_nonneg hlam hℓ'.le) q
  have h2 : (lam / ℓ) ^ q ≤ Real.exp (ξ * M * q) * (lam / ℓ') ^ q := by
    calc (lam / ℓ) ^ q ≤ (e * (lam / ℓ')) ^ q :=
          Real.rpow_le_rpow (div_nonneg hlam hℓ.le) h1 hq
      _ = e ^ q * (lam / ℓ') ^ q := Real.mul_rpow he0.le (div_nonneg hlam hℓ'.le)
      _ = Real.exp (ξ * M * q) * (lam / ℓ') ^ q := by rw [he, ← Real.exp_mul]
  have h3 := exp_mul_le_young (ξ * M * q) hv
  have h4 : Real.exp (3 / 2 * (ξ * M * q)) ≤ Real.exp (3 / 2 * M) := by
    refine Real.exp_le_exp.2 ?_
    have : ξ * M * q ≤ M := by nlinarith
    linarith
  have h5 : ((lam / ℓ') ^ q) ^ 3 = (lam / ℓ') ^ (3 * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hlam hℓ'.le)]
    norm_num [mul_comm]
  linarith

/-- the pointwise bound of the regime `n < k`: if `λ ≤ A` and `ℓ ≥ e^{-ξ M} h`, then
`(λ/ℓ)^q ≤ (A/h)^q e^{(3/2) M}` -/
lemma ratio_rpow_le_of_lower {lam ℓ M ξ q h A : ℝ} (hlam : 0 ≤ lam) (hlamA : lam ≤ A) (hh : 0 < h)
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hqξ : q * ξ ≤ 1)
    (hℓ : Real.exp (-(ξ * M)) * h ≤ ℓ) :
    (lam / ℓ) ^ q ≤ (A / h) ^ q * Real.exp (3 / 2 * M) := by
  have hA : 0 ≤ A := hlam.trans hlamA
  have hl0 : 0 < Real.exp (-(ξ * M)) * h := by positivity
  have hℓ0 : 0 < ℓ := hl0.trans_le hℓ
  have h1 : lam / ℓ ≤ A / h * Real.exp (ξ * M) := by
    calc lam / ℓ ≤ lam / (Real.exp (-(ξ * M)) * h) := div_le_div_of_nonneg_left hlam hl0 hℓ
      _ ≤ A / (Real.exp (-(ξ * M)) * h) := div_le_div_of_nonneg_right hlamA hl0.le
      _ = A / h * Real.exp (ξ * M) := by
          rw [Real.exp_neg]; field_simp
  calc (lam / ℓ) ^ q ≤ (A / h * Real.exp (ξ * M)) ^ q :=
        Real.rpow_le_rpow (div_nonneg hlam hℓ0.le) h1 hq
    _ = (A / h) ^ q * Real.exp (ξ * M * q) := by
        rw [Real.mul_rpow (div_nonneg hA hh.le) (Real.exp_pos _).le, ← Real.exp_mul]
    _ ≤ (A / h) ^ q * Real.exp (3 / 2 * M) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
          (Real.rpow_nonneg (div_nonneg hA hh.le) q)
        nlinarith

/-- `λ / (h L) ≤ (c/h)(λ'/L)` when `λ ≤ c λ'` (with junk `x/0 = 0`) -/
lemma ratio_scale_le {lam lam' h L c : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (hc : lam ≤ c * lam') :
    lam / (h * L) ≤ c / h * (lam' / L) := by
  calc lam / (h * L) = lam / h / L := by rw [div_mul_eq_div_div]
    _ ≤ c * lam' / h / L := by gcongr
    _ = c / h * (lam' / L) := by ring

/-- iterating `a_{m+1} ≤ e^C a_m` -/
lemma le_exp_mul_of_succ_le {a : ℕ → ℝ} {C : ℝ} (h : ∀ m, a (m + 1) ≤ Real.exp C * a m)
    (m i : ℕ) : a (m + i) ≤ Real.exp (C * i) * a m := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc a (m + (i + 1)) = a (m + i + 1) := rfl
      _ ≤ Real.exp C * a (m + i) := h _
      _ ≤ Real.exp C * (Real.exp (C * i) * a m) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = Real.exp (C * ((i + 1 : ℕ) : ℝ)) * a m := by
          rw [← mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring

/-- `(ofReal λ / L)^q = ofReal ((λ / L.toReal)^q)` for `0 < L.toReal` -/
lemma ofReal_div_rpow_eq {lam : ℝ} (hlam : 0 ≤ lam) {L : ℝ≥0∞} (hL : 0 < L.toReal) {q : ℝ}
    (hq : 0 ≤ q) : (ENNReal.ofReal lam / L) ^ q = ENNReal.ofReal ((lam / L.toReal) ^ q) := by
  have hLt : L ≠ ⊤ := fun h => by simp [h] at hL
  conv_lhs => rw [← ENNReal.ofReal_toReal hLt]
  rw [← ENNReal.ofReal_div_of_pos hL, ENNReal.ofReal_rpow_of_nonneg (div_nonneg hlam hL.le) hq]

/-- the union bound for a minimum: `(a / min_{i ∈ s} f_i)^q ≤ Σ_{i ∈ s} (a / f_i)^q` in `ℝ≥0∞`
(an empty minimum is `⊤`) -/
lemma div_biInf_rpow_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (a : ℝ≥0∞) {q : ℝ}
    (hq : 0 < q) : (a / ⨅ i ∈ s, f i) ^ q ≤ ∑ i ∈ s, (a / f i) ^ q := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [ENNReal.zero_rpow_of_pos hq]
  · obtain ⟨i, hi, hmin⟩ := s.exists_min_image f hs
    have e : ⨅ i ∈ s, f i = f i := le_antisymm (iInf₂_le i hi) (le_iInf₂ fun j hj => hmin j hj)
    rw [e]
    exact Finset.single_le_sum (f := fun i => (a / f i) ^ q) (fun _ _ => zero_le) hi

/-! ### One strip -/

/-- **The moment bound for one strip at the origin** (ledger row `inv_moment_unif`, audit §3):
for `k ≥ 2`, `ξ ∈ (0, min(1/8, 1/q)]` and every `n`,
`E[(λ_n / L_n(2^{-k} R_{1,3}))^q] ≤ B k`, with `B k < ∞` chosen before the probability space and
before `ξ`. -/
theorem lintegral_originStrip_le (hM : IfaceMomentsLambdaU) (hS : IfaceScaleU) {q : ℝ}
    (hq : 1 ≤ q) :
    ∃ B : ℕ → ℝ≥0∞, (∀ k, B k ≠ ⊤) ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) (min (1 / 8) (1 / q)), ∀ n : ℕ,
        ∫⁻ ω, (ENNReal.ofReal (lambdaN ξ W P n) / rectLen ξ (fun x => phiMN W P 0 n x ω)
          (rectAB ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k * 3))) ^ q ∂P ≤ B k := by
  obtain ⟨K, hK⟩ := lintegral_exp_supPhi_le.{0}
  obtain ⟨C₃, hC₃⟩ := hM (3 * q) (by linarith)
  obtain ⟨Cs, -, hCs⟩ := hS
  -- the constants of one level
  set E : ℕ → ℝ := fun k => (4 : ℝ) ^ (3 / 2 * (k : ℝ) + |K| * Real.sqrt k) with hE
  set A : ℕ → ℝ := fun k => (3 * Real.exp k / (2 : ℝ)⁻¹ ^ k) ^ q with hA
  set D : ℕ → ℝ := fun k => (Real.exp (Cs * k) / (2 : ℝ)⁻¹ ^ k) ^ (3 * q) * C₃ with hD
  refine ⟨fun k => ENNReal.ofReal (A k) * ENNReal.ofReal (E k) + ENNReal.ofReal (E k) +
      ENNReal.ofReal (D k), fun k => ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
        ENNReal.ofReal_ne_top⟩, ?_⟩
  intro k hk Ω _ P W hW ξ hξ n
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hξ8 : ξ ≤ 1 / 8 := hξ1.trans (min_le_left _ _)
  have hq0 : 0 < q := by linarith
  have hqξ : q * ξ ≤ 1 := by
    have := hξ1.trans (min_le_right _ _)
    rw [le_div_iff₀ hq0] at this; linarith
  have hξI : ξ ∈ Set.Ioc (0 : ℝ) (1 / 8) := ⟨hξ0, hξ8⟩
  set h : ℝ := (2 : ℝ)⁻¹ ^ k with hh_def
  have hh : 0 < h := by positivity
  set R := rectAB h (h * 3) with hR_def
  have hRsub : R.toSet ⊆ ferniqueBox (0 : ℂ) 1 := rectAB_strip_subset hk
  -- `E` is monotone in the level
  have hEle : ∀ m : ℕ, m ≤ k → (4 : ℝ) ^ (3 / 2 * (m : ℝ) + K * Real.sqrt m) ≤ E k := by
    intro m hm
    have hm' : (m : ℝ) ≤ k := by exact_mod_cast hm
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : K * Real.sqrt m ≤ |K| * Real.sqrt m :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.sqrt_nonneg _)
    have h2 : |K| * Real.sqrt m ≤ |K| * Real.sqrt k :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm') (abs_nonneg K)
    linarith
  -- facts about `λ`
  have hlam := hCs hW ξ hξI n
  have hlam0 : 0 ≤ lambdaN ξ W P n := (Real.exp_pos _).le.trans hlam.2.2.2.1
  set lam := lambdaN ξ W P n with hlam_def
  rcases lt_or_ge n k with hnk | hkn
  · -- the regime `n < k`: Euclidean lower bound and U11 (d)
    have hlamA : lam ≤ 3 * Real.exp k := by
      refine hlam.2.2.2.2.trans ?_
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
        linarith
      have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk.le
      have hξ2 : ξ ^ 2 ≤ 1 := by nlinarith
      have : ξ ^ 2 * n * Real.log 2 / 2 ≤ k := by
        have h1 : ξ ^ 2 * n * Real.log 2 ≤ 1 * n * 1 := by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have := mul_le_mul hξ2 (le_refl (n : ℝ)) hn0 zero_le_one
          nlinarith
        linarith
      gcongr
    have hpt : ∀ ω, (ENNReal.ofReal lam / rectLen ξ (fun x => phiMN W P 0 n x ω) R) ^ q ≤
        ENNReal.ofReal (A k) * ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P n ω)) := by
      intro ω
      have hb : ∀ x ∈ R.toSet, |phiMN W P 0 n x ω| ≤ supPhi W P n ω := fun x hx =>
        abs_le_supPhi hW n ω (hRsub hx)
      obtain ⟨-, hge⟩ := toReal_rectLen_ge (ξ := ξ)
        ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω) hh.le (by positivity) hb
      rw [abs_of_pos hξ0] at hge
      have hpos : 0 < (rectLen ξ (fun x => phiMN W P 0 n x ω) R).toReal :=
        lt_of_lt_of_le (by positivity) hge
      rw [ofReal_div_rpow_eq hlam0 hpos hq0.le, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (ratio_rpow_le_of_lower hlam0 hlamA hh
        (supPhi_nonneg W P n ω) hq0.le hqξ hge)
    calc ∫⁻ ω, (ENNReal.ofReal lam / rectLen ξ (fun x => phiMN W P 0 n x ω) R) ^ q ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (A k) * ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P n ω)) ∂P :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (A k) * ∫⁻ ω, ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P n ω)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (A k) * ENNReal.ofReal (E k) := by
          gcongr
          exact (hK hW n).trans (ENNReal.ofReal_le_ofReal (hEle n hnk.le))
      _ ≤ ENNReal.ofReal (A k) * ENNReal.ofReal (E k) + ENNReal.ofReal (E k) +
            ENNReal.ofReal (D k) := le_add_right le_self_add
  · -- the regime `k ≤ n`: coarse field, scaling, U11 (b) and U10
    have hφn := isPhiVersion_phiMN hW (Nat.zero_le n)
    have hφkn := isPhiVersion_phiMN hW hkn
    have hpt : ∀ᵐ ω ∂P, (ENNReal.ofReal lam / rectLen ξ (fun x => phiMN W P 0 n x ω) R) ^ q ≤
        ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P k ω)) +
          ENNReal.ofReal ((lam / lenMN ξ W P h (h * 3) k n ω) ^ (3 * q)) := by
      filter_upwards [ae_phiMN_add hW hkn] with ω hadd
      have hbn : ∀ x ∈ R.toSet, |phiMN W P 0 n x ω| ≤ supPhi W P n ω := fun x hx =>
        abs_le_supPhi hW n ω (hRsub hx)
      have hbk : ∀ x ∈ R.toSet, |phiMN W P 0 k x ω| ≤ supPhi W P k ω := fun x hx =>
        abs_le_supPhi hW k ω (hRsub hx)
      have hbkn : ∀ x ∈ R.toSet, |phiMN W P k n x ω| ≤ supPhi W P n ω + supPhi W P k ω :=
        fun x hx => by
          have e : phiMN W P k n x ω = phiMN W P 0 n x ω - phiMN W P 0 k x ω := by
            rw [hadd x]; ring
          rw [e]; exact (abs_sub _ _).trans (add_le_add (hbn x hx) (hbk x hx))
      have hdiff : ∀ x ∈ R.toSet, |phiMN W P k n x ω - phiMN W P 0 n x ω| ≤ supPhi W P k ω :=
        fun x hx => by
          have e : phiMN W P k n x ω - phiMN W P 0 n x ω = -phiMN W P 0 k x ω := by
            rw [hadd x]; ring
          rw [e, abs_neg]; exact hbk x hx
      obtain ⟨hne, hge⟩ := toReal_rectLen_ge (ξ := ξ) (hφn.cont ω)
        hh.le (by positivity) hbn
      obtain ⟨-, hge'⟩ := toReal_rectLen_ge (ξ := ξ) (hφkn.cont ω)
        hh.le (by positivity) hbkn
      have hpos : 0 < (rectLen ξ (fun x => phiMN W P 0 n x ω) R).toReal :=
        lt_of_lt_of_le (by positivity) hge
      have hpos' : 0 < (rectLen ξ (fun x => phiMN W P k n x ω) R).toReal :=
        lt_of_lt_of_le (by positivity) hge'
      have hcmp : rectLen ξ (fun x => phiMN W P k n x ω) R ≤
          ENNReal.ofReal (Real.exp (|ξ| * supPhi W P k ω)) *
            rectLen ξ (fun x => phiMN W P 0 n x ω) R :=
        crossLenIn_le_of_abs_sub_le hdiff
      have hcmp' : (rectLen ξ (fun x => phiMN W P k n x ω) R).toReal ≤
          Real.exp (ξ * supPhi W P k ω) * (rectLen ξ (fun x => phiMN W P 0 n x ω) R).toReal := by
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne) hcmp
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, abs_of_pos hξ0]
          at this
      rw [ofReal_div_rpow_eq hlam0 hpos hq0.le,
        ← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
      exact ENNReal.ofReal_le_ofReal (ratio_rpow_le_of_cmp hlam0 hpos hpos'
        (supPhi_nonneg W P k ω) hq0.le hqξ hcmp')
    have hmeas : Measurable fun ω =>
        ENNReal.ofReal ((lam / lenMN ξ W P h (h * 3) k n ω) ^ (3 * q)) :=
      ((measurable_const.div (measurable_lenMN hW _ _ hkn)).pow_const _).ennreal_ofReal
    -- the coarse field
    have hfirst : ∫⁻ ω, ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P k ω)) ∂P ≤
        ENNReal.ofReal (E k) :=
      (hK hW k).trans (ENNReal.ofReal_le_ofReal (hEle k le_rfl))
    -- scaling, U11 (b) iterated and U10
    have hsecond : ∫⁻ ω, ENNReal.ofReal ((lam / lenMN ξ W P h (h * 3) k n ω) ^ (3 * q)) ∂P
        ≤ ENNReal.ofReal (D k) := by
      have e1 : (2 : ℝ) ^ k * h = 1 := by
        rw [hh_def, ← mul_pow]; norm_num
      have e3 : (2 : ℝ) ^ k * (h * 3) = 3 := by
        rw [hh_def, ← mul_assoc, ← mul_pow]; norm_num
      have hg : Measurable fun t : ℝ => ENNReal.ofReal ((lam / t) ^ (3 * q)) :=
        ((measurable_const.div measurable_id).pow_const _).ennreal_ofReal
      have hlaw := lintegral_comp_eq_of_measure_eq (P := P)
        (measurable_lenMN (ξ := ξ) hW h (h * 3) hkn)
        ((measurable_lenMN (ξ := ξ) hW 1 3 (Nat.zero_le (n - k))).const_mul h)
        (fun S hS => by
          have := dddf_eq230 (ξ := ξ) hW h (h * 3) hkn hS
          rwa [e1, e3] at this) hg
      rw [hlaw]
      have hstep : ∀ m, lambdaN ξ W P (m + 1) ≤ Real.exp Cs * lambdaN ξ W P m := fun m =>
        (hCs hW ξ hξI m).2.2.1
      have hlamk : lam ≤ Real.exp (Cs * k) * lambdaN ξ W P (n - k) := by
        have := le_exp_mul_of_succ_le (a := fun m => lambdaN ξ W P m) hstep (n - k) k
        rwa [Nat.sub_add_cancel hkn] at this
      have hlamk0 : 0 ≤ lambdaN ξ W P (n - k) :=
        (Real.exp_pos _).le.trans (hCs hW ξ hξI (n - k)).2.2.2.1
      calc ∫⁻ ω, ENNReal.ofReal ((lam / (h * lenMN ξ W P 1 3 0 (n - k) ω)) ^ (3 * q)) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal ((Real.exp (Cs * k) / h) ^ (3 * q)) *
              ENNReal.ofReal ((lambdaN ξ W P (n - k) /
                lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω) ^ (3 * q)) ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hL0 : 0 ≤ lenMN ξ W P 1 3 0 (n - k) ω := ENNReal.toReal_nonneg
            have hr := ratio_scale_le hh hL0 hlamk
            calc (lam / (h * lenMN ξ W P 1 3 0 (n - k) ω)) ^ (3 * q)
                ≤ (Real.exp (Cs * k) / h *
                    (lambdaN ξ W P (n - k) / lenMN ξ W P 1 3 0 (n - k) ω)) ^ (3 * q) :=
                  Real.rpow_le_rpow (div_nonneg hlam0 (by positivity)) hr (by positivity)
              _ = (Real.exp (Cs * k) / h) ^ (3 * q) * (lambdaN ξ W P (n - k) /
                    lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω) ^ (3 * q) :=
                  Real.mul_rpow (by positivity) (div_nonneg hlamk0 hL0)
        _ = ENNReal.ofReal ((Real.exp (Cs * k) / h) ^ (3 * q)) *
              ∫⁻ ω, ENNReal.ofReal ((lambdaN ξ W P (n - k) /
                lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω) ^ (3 * q)) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal ((Real.exp (Cs * k) / h) ^ (3 * q)) * ENNReal.ofReal C₃ := by
            gcongr
            exact (hC₃ hW ξ hξI (n - k) 1 3 (by simp [shapeSet])).2
        _ = ENNReal.ofReal (D k) := by rw [← ENNReal.ofReal_mul (by positivity)]
    calc ∫⁻ ω, (ENNReal.ofReal lam / rectLen ξ (fun x => phiMN W P 0 n x ω) R) ^ q ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P k ω)) +
            ENNReal.ofReal ((lam / lenMN ξ W P h (h * 3) k n ω) ^ (3 * q))) ∂P :=
          lintegral_mono_ae hpt
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P k ω)) ∂P +
            ∫⁻ ω, ENNReal.ofReal ((lam / lenMN ξ W P h (h * 3) k n ω) ^ (3 * q)) ∂P :=
          lintegral_add_right _ hmeas
      _ ≤ ENNReal.ofReal (E k) + ENNReal.ofReal (D k) := add_le_add hfirst hsecond
      _ ≤ ENNReal.ofReal (A k) * ENNReal.ofReal (E k) + ENNReal.ofReal (E k) +
            ENNReal.ofReal (D k) := by
          gcongr; exact le_add_self

end InvMom

open InvMom

/-! ### The family of strips -/

/-- **U13 with explicit `ξ`-range** (ledger U13 (b), corrected by audit S-1/M-4): for `q ≥ 1`,
compact `K₀` and `δ ∈ (0, 1]` there is `C < ∞` (chosen before the probability space and before
`ξ`) bounding the `q`-th moment of `λ_n` over the `ℝ≥0∞`-minimum of the short-way crossing lengths
of the strips of level `k(δ)` around the blocks meeting `K₀`, for every `ξ ∈ (0, min(1/8, 1/q)]`
and every `n`. -/
theorem inv_moment_unif_le (hM : IfaceMomentsLambdaU) (hS : IfaceScaleU) (q : ℝ) (hq : 1 ≤ q)
    (K₀ : Set ℂ) (hK₀ : IsCompact K₀) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) (min (1 / 8) (1 / q)), ∀ n : ℕ,
        ∫⁻ ω, (ENNReal.ofReal (lambdaN ξ W P n) /
            ⨅ b ∈ blockSet K₀ (kDelta δ), ⨅ j ∈ T20D.shortJ (kDelta δ) b,
              crossLenIn ξ (fun x => phiMN W P 0 n x ω) (T20D.RS (kDelta δ) j)
                (T20D.RS₁ (kDelta δ) j) (T20D.RS₂ (kDelta δ) j)) ^ q ∂P ≤ C := by
  obtain ⟨B, hBfin, hB⟩ := lintegral_originStrip_le hM hS hq
  set k := kDelta δ with hk_def
  have hk : 2 ≤ k := two_le_kDelta hδ hδ1
  have hfin := blockSet_finite hK₀.isBounded k
  set Bf := hfin.toFinset with hBf
  refine ⟨∑ b ∈ Bf, ∑ j ∈ T20D.shortJ k b, B k,
    ENNReal.sum_ne_top.2 fun b _ => ENNReal.sum_ne_top.2 fun j _ => hBfin k, ?_⟩
  intro Ω _ P W hW ξ hξ n
  have hq0 : 0 < q := by linarith
  set a := ENNReal.ofReal (lambdaN ξ W P n) with ha
  set F : Circle × ℂ → Ω → ℝ≥0∞ := fun j ω => crossLenIn ξ (fun x => phiMN W P 0 n x ω)
    (T20D.RS k j) (T20D.RS₁ k j) (T20D.RS₂ k j) with hF
  have hpt : ∀ ω, (a / ⨅ b ∈ blockSet K₀ k, ⨅ j ∈ T20D.shortJ k b, F j ω) ^ q ≤
      ∑ b ∈ Bf, ∑ j ∈ T20D.shortJ k b, (a / F j ω) ^ q := by
    intro ω
    have e : (⨅ b ∈ blockSet K₀ k, ⨅ j ∈ T20D.shortJ k b, F j ω) =
        ⨅ b ∈ Bf, ⨅ j ∈ T20D.shortJ k b, F j ω := by
      simp only [hBf, Set.Finite.mem_toFinset]
    rw [e]
    exact (div_biInf_rpow_le_sum Bf _ a hq0).trans
      (Finset.sum_le_sum fun b _ => div_biInf_rpow_le_sum _ _ a hq0)
  have hgm : Measurable fun x : ℝ≥0∞ => (a / x) ^ q :=
    (measurable_const.div measurable_id).pow_const q
  have hmeas : ∀ j, Measurable fun ω => (a / F j ω) ^ q := fun j =>
    hgm.comp (measurable_stripLen hW (Nat.zero_le n) k j)
  calc ∫⁻ ω, (a / ⨅ b ∈ blockSet K₀ k, ⨅ j ∈ T20D.shortJ k b, F j ω) ^ q ∂P
      ≤ ∫⁻ ω, ∑ b ∈ Bf, ∑ j ∈ T20D.shortJ k b, (a / F j ω) ^ q ∂P := lintegral_mono hpt
    _ = ∑ b ∈ Bf, ∑ j ∈ T20D.shortJ k b, ∫⁻ ω, (a / F j ω) ^ q ∂P := by
        rw [lintegral_finsetSum _ fun b _ => Finset.measurable_sum _ fun j _ => hmeas j]
        exact Finset.sum_congr rfl fun b _ => lintegral_finsetSum _ fun j _ => hmeas j
    _ ≤ ∑ b ∈ Bf, ∑ j ∈ T20D.shortJ k b, B k := by
        gcongr with b hb j hj
        rw [hF, lintegral_stripLen_eq hW n k j hgm]
        exact hB k hk hW ξ hξ n

/-- **Ledger U13 (b), `inv_moment_unif`** (in the `ℝ≥0∞` form of audit S-1, with `δ ≤ 1`,
audit M-4), given the interfaces U10 and U11: witness `ξq' = min (1/8) (1/q)`. -/
theorem inv_moment_unif (hM : IfaceMomentsLambdaU) (hS : IfaceScaleU) (q : ℝ) (hq : 1 ≤ q) :
    ∃ ξq' : ℝ, 0 < ξq' ∧ ∀ K₀ : Set ℂ, IsCompact K₀ → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
          IsWhiteNoise P W → ∀ ξ ∈ Set.Ioc (0 : ℝ) ξq', ∀ n : ℕ,
            ∫⁻ ω, (ENNReal.ofReal (lambdaN ξ W P n) /
                ⨅ b ∈ blockSet K₀ (kDelta δ), ⨅ j ∈ T20D.shortJ (kDelta δ) b,
                  crossLenIn ξ (fun x => phiMN W P 0 n x ω) (T20D.RS (kDelta δ) j)
                    (T20D.RS₁ (kDelta δ) j) (T20D.RS₂ (kDelta δ) j)) ^ q ∂P ≤ C :=
  ⟨min (1 / 8) (1 / q), lt_min (by norm_num) (by positivity), fun K₀ hK₀ δ hδ hδ1 =>
    inv_moment_unif_le hM hS q hq K₀ hK₀ δ hδ hδ1⟩

end Uniform
end GaussianLQG
