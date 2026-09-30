import QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# RS BP1: generator identities for the base-point estimates (κ < 4 and κ = 4)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §4, nodes BP1-a and BP1-4.

State `v = (X, O, L) : ℝ × ℝ × ℝ` with `X = f_t(x)`, `O = f_t(y)` (`0 < y < x`, `f_t = g_t − W_t`
the centered forward Loewner flow) and `L = log f_t'(x)`. The forward flow
`dX = 2/X dt − √κ dB`, `dO = 2/O dt − √κ dB`, `dL = −2/X² dt` has the (tamed) drift
`bpDrift c v = (2/max X c, 2/max O c, −2/(max X c)²)` and noise vector
`bpNoise κ = (−√κ, −√κ, 0)`; the taming is inactive on `{c ≤ O < X}`.
Write `Υ = (X − O) e^{−L}` (`bpUps`), `ρ = O/X`, `s = (X − O)/O`.

* **BP1-a** (`dynkinGen_bp1_le`, κ < 4): `bp1Test κ v = Υ^{−p} (2 − ρ)`,
  `p = min (1/2) ((4 − κ)/2)`, has generator
  `Υ^{−p} (X − O)/(X² O) · [2p(2 − ρ) − 2(1 + ρ) + κρ] ≤ 0` (`dynkinGen_bp1Test_eq`); this is
  the EXT_RS formula `X^{−2}(1−ρ)[2p(2−ρ) − 2(1+ρ) + κρ]/ρ · Υ^{−p}`. Own argument (EXT_RS §9;
  RS's κ = 4 Koebe mechanism with a power supersolution).
* **BP1-4** (`dynkinGen_bp14_eq`, κ = 4): `bp4Test = log Υ + G(s)` has zero generator; it is
  `−(Q − G(s))` (`bp4Test_eq_neg_bp4Q`), Rohde–Schramm's local martingale `Q − G(s)` (`bp4Q`,
  `dynkinGen_bp4Q_eq`),
  `Q = log f_t'(x) − log (X − O) = −log Υ`, with `G' (s) = log (s/(1+s))/(1+s)`
  (`bp4Gd`), i.e. RS's `G(s) = log s log(1+s) − ½ log²(1+s) + Li₂(−s)` up to an additive
  constant. Here `G = bp4G s = ∫₁ˢ G'`, and `bp4G_le_two : bp4G s ≤ 2` for `s > 0`
  (RS: "`sup {G(x) : x > 0} < ∞`").
  **Sign note.** TASKS/EXT_RS BP1-4 sign corrected per RS Lemma 7.2 (`Q = −log Υ`):
  TASKS.md R8 wrote the test as `log Υ − G(s)`, whose generator is
  `−4s/((1+s)² O²) ≠ 0` (fidelity audit AUDIT5 N1 found the same). The correct test is
  `log Υ + G(s) = −(Q − G(s))`.

Also: `bpDrift` is bounded and Lipschitz, and both tests are `C³` on the open set
`bpDom = {0 < O < X}` (the inputs of `RS.integral_localDynkin_stopped_le`).

Literature: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Lemma 7.2
and its proof, pp. 32–33 (κ = 4: `∂_t Q = −2X⁻² + 2X⁻¹O⁻¹`, `G`, `s(1+s)²G'' + s(1+s)G' = 1`,
"`Q(t) − G_t` is a local martingale", `sup G < ∞`); G. Lawler, *Conformally Invariant Processes
in the Plane*, AMS 2005, Prop. 6.12, pp. 128–129. RS use Itô's formula; here the generator is
computed by hand for the project's Itô-free Dynkin formula. The bound `bp4G ≤ 2` is an own
elementary proof (monotonicity).
-/

noncomputable section

set_option linter.unusedSimpArgs false

open Set Filter Topology

namespace QuantumZipper
namespace RS

open FrozenMart

/-! ### Definitions -/

/-- The (tamed) drift of `(X, O, L) = (f_t x, f_t y, log f_t' x)`. -/
def bpDrift (c : ℝ) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (2 / max v.1 c, 2 / max v.2.1 c, -2 / (max v.1 c) ^ 2)

/-- The noise vector `(−√κ, −√κ, 0)`. -/
def bpNoise (κ : ℝ) : ℝ × ℝ × ℝ := (-Real.sqrt κ, -Real.sqrt κ, 0)

/-- `Υ = (X − O) e^{−L} = (f_t x − f_t y)/f_t'(x)`. -/
def bpUps (v : ℝ × ℝ × ℝ) : ℝ := (v.1 - v.2.1) * Real.exp (-v.2.2)

/-- The exponent `p = min (1/2) ((4 − κ)/2)`. -/
def bp1Exp (κ : ℝ) : ℝ := min (1 / 2) ((4 - κ) / 2)

/-- The BP1-a supersolution `Υ^{−p} (2 − O/X)`. -/
def bp1Test (κ : ℝ) (v : ℝ × ℝ × ℝ) : ℝ := bpUps v ^ (-bp1Exp κ) * (2 - v.2.1 / v.1)

/-- `G'(s) = log (s/(1+s))/(1+s)` (Rohde–Schramm, Lemma 7.2). -/
def bp4Gd (u : ℝ) : ℝ := Real.log (u / (1 + u)) / (1 + u)

/-- `G(s) = ∫₁ˢ G'`. -/
def bp4G (s : ℝ) : ℝ := ∫ u in (1 : ℝ)..s, bp4Gd u

/-- Rohde–Schramm's local martingale `Q − G(s) = L − log (X − O) − G((X − O)/O)`
(Lemma 7.2, `Q = log g_t'(x) − log (g_t(x) − g_t(y)) = −log Υ`). -/
def bp4Q (v : ℝ × ℝ × ℝ) : ℝ :=
  v.2.2 - Real.log (v.1 - v.2.1) - bp4G ((v.1 - v.2.1) / v.2.1)

/-- The BP1-4 test `log Υ + G(s) = log (X − O) − L + G((X − O)/O)` (sign-corrected; equals
`−bp4Q`). -/
def bp4Test (v : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (v.1 - v.2.1) - v.2.2 + bp4G ((v.1 - v.2.1) / v.2.1)

/-- The open domain `{0 < O < X}`. -/
def bpDom : Set (ℝ × ℝ × ℝ) := {v | 0 < v.2.1 ∧ v.2.1 < v.1}

theorem isOpen_bpDom : IsOpen bpDom :=
  (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
    (isOpen_lt (continuous_fst.comp continuous_snd) continuous_fst)

theorem bpDrift_of_le {c : ℝ} {v : ℝ × ℝ × ℝ} (hv : c ≤ v.2.1 ∧ v.2.1 < v.1) :
    bpDrift c v = (2 / v.1, 2 / v.2.1, -2 / v.1 ^ 2) := by
  have h1 : max v.1 c = v.1 := max_eq_left (hv.1.trans hv.2.le)
  have h2 : max v.2.1 c = v.2.1 := max_eq_left hv.1
  simp only [bpDrift, h1, h2]

/-! ### The drift is bounded and Lipschitz -/

theorem abs_two_div_sub_le_bp {c A B : ℝ} (hc : 0 < c) (hA : c ≤ A) (hB : c ≤ B) :
    |2 / A - 2 / B| ≤ 2 / c ^ 2 * |A - B| := by
  have hA0 : 0 < A := hc.trans_le hA
  have hB0 : 0 < B := hc.trans_le hB
  have e : 2 / A - 2 / B = 2 * (B - A) / (A * B) := by field_simp
  have hAB : c ^ 2 ≤ A * B := by nlinarith
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hA0 hB0), abs_two, abs_sub_comm B A,
    div_le_iff₀ (mul_pos hA0 hB0)]
  calc 2 * |A - B| = 2 / c ^ 2 * |A - B| * c ^ 2 := by field_simp
    _ ≤ 2 / c ^ 2 * |A - B| * (A * B) := by gcongr

theorem abs_two_div_sq_sub_le_bp {c A B : ℝ} (hc : 0 < c) (hA : c ≤ A) (hB : c ≤ B) :
    |2 / A ^ 2 - 2 / B ^ 2| ≤ 4 / c ^ 3 * |A - B| := by
  have hA0 : 0 < A := hc.trans_le hA
  have hB0 : 0 < B := hc.trans_le hB
  have e : 2 / A ^ 2 - 2 / B ^ 2 = (2 / A - 2 / B) * (1 / A + 1 / B) := by field_simp; ring
  have h2 : |1 / A + 1 / B| ≤ 2 / c := by
    rw [abs_of_pos (by positivity)]
    have : 1 / A ≤ 1 / c := one_div_le_one_div_of_le hc hA
    have : 1 / B ≤ 1 / c := one_div_le_one_div_of_le hc hB
    have : 2 / c = 1 / c + 1 / c := by ring
    linarith
  rw [e, abs_mul]
  calc |2 / A - 2 / B| * |1 / A + 1 / B| ≤ (2 / c ^ 2 * |A - B|) * (2 / c) :=
        mul_le_mul (abs_two_div_sub_le_bp hc hA hB) h2 (abs_nonneg _) (by positivity)
    _ = 4 / c ^ 3 * |A - B| := by field_simp; ring

theorem lipschitz_bpDrift {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (2 / c ^ 2 + 4 / c ^ 3)) (bpDrift c) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  have hd : 0 ≤ dist v w := dist_nonneg
  have hX : |max v.1 c - max w.1 c| ≤ dist v w := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← Real.dist_eq]
    exact (le_max_left _ _).trans (le_of_eq Prod.dist_eq.symm)
  have hO : |max v.2.1 c - max w.2.1 c| ≤ dist v w := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← Real.dist_eq]
    calc dist v.2.1 w.2.1 ≤ dist v.2 w.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ dist v w := (le_max_right _ _).trans (le_of_eq Prod.dist_eq.symm)
  have h2 : 0 ≤ 2 / c ^ 2 := by positivity
  have h4 : 0 ≤ 4 / c ^ 3 := by positivity
  rw [Prod.dist_eq, Prod.dist_eq]
  refine max_le ?_ (max_le ?_ ?_)
  · rw [Real.dist_eq]
    refine (abs_two_div_sub_le_bp hc (le_max_right _ _) (le_max_right _ _)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hX h2, mul_nonneg h4 hd]
  · rw [Real.dist_eq]
    refine (abs_two_div_sub_le_bp hc (le_max_right _ _) (le_max_right _ _)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hO h2, mul_nonneg h4 hd]
  · rw [Real.dist_eq]
    simp only [bpDrift]
    rw [show -2 / max v.1 c ^ 2 - -2 / max w.1 c ^ 2 = -(2 / max v.1 c ^ 2 - 2 / max w.1 c ^ 2)
      by ring, abs_neg]
    refine (abs_two_div_sq_sub_le_bp hc (le_max_right _ _) (le_max_right _ _)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hX h4, mul_nonneg h2 hd]

theorem norm_bpDrift_le {c : ℝ} (hc : 0 < c) (v : ℝ × ℝ × ℝ) :
    ‖bpDrift c v‖ ≤ 2 / c + 2 / c ^ 2 := by
  have k1 : ∀ A : ℝ, c ≤ A → |2 / A| ≤ 2 / c := fun A hA => by
    rw [abs_of_pos (by have := hc.trans_le hA; positivity)]
    exact div_le_div_of_nonneg_left (by norm_num) hc hA
  have k2 : ∀ A : ℝ, c ≤ A → |-2 / A ^ 2| ≤ 2 / c ^ 2 := fun A hA => by
    rw [neg_div, abs_neg, abs_of_pos (by have := hc.trans_le hA; positivity)]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ hc.le hA 2)
  have p1 : 0 ≤ 2 / c := by positivity
  have p2 : 0 ≤ 2 / c ^ 2 := by positivity
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · rw [Real.norm_eq_abs]; have := k1 _ (le_max_right v.1 c); simp only [bpDrift]; linarith
  · rw [Real.norm_eq_abs]; have := k1 _ (le_max_right v.2.1 c); simp only [bpDrift]; linarith
  · rw [Real.norm_eq_abs]; have := k2 _ (le_max_right v.1 c); simp only [bpDrift]; linarith

/-! ### Smoothness -/

theorem contDiff_bpUps : ContDiff ℝ 3 bpUps := by
  unfold bpUps
  exact (contDiff_fst.sub (contDiff_fst.comp contDiff_snd)).mul
    (Real.contDiff_exp.comp (contDiff_snd.comp contDiff_snd).neg)

theorem bpUps_pos {v : ℝ × ℝ × ℝ} (hv : v ∈ bpDom) : 0 < bpUps v :=
  mul_pos (sub_pos.2 hv.2) (Real.exp_pos _)

theorem contDiffOn_bp1Test (κ : ℝ) : ContDiffOn ℝ 3 (bp1Test κ) bpDom := by
  have h1 : ContDiffOn ℝ 3 (fun v => bpUps v ^ (-bp1Exp κ)) bpDom :=
    contDiff_bpUps.contDiffOn.rpow_const_of_ne fun v hv => (bpUps_pos hv).ne'
  have h2 : ContDiffOn ℝ 3 (fun v : ℝ × ℝ × ℝ => 2 - v.2.1 / v.1) bpDom :=
    contDiffOn_const.sub ((contDiff_fst.comp contDiff_snd).contDiffOn.div contDiff_fst.contDiffOn
      fun v hv => (hv.1.trans hv.2).ne')
  exact h1.mul h2

theorem continuousOn_bp4Gd : ContinuousOn bp4Gd (Ioi 0) := by
  intro u hu
  have hu : (0 : ℝ) < u := hu
  refine ContinuousAt.continuousWithinAt ?_
  unfold bp4Gd
  have h1 : (1 : ℝ) + u ≠ 0 := by positivity
  have h2 : u / (1 + u) ≠ 0 := by positivity
  exact ((continuousAt_id.div (continuousAt_const.add continuousAt_id) h1).log h2).div
    (continuousAt_const.add continuousAt_id) h1

theorem hasDerivAt_bp4G {u : ℝ} (hu : 0 < u) : HasDerivAt bp4G (bp4Gd u) u := by
  have hsub : uIcc 1 u ⊆ Ioi 0 := fun x hx => by
    rcases le_total 1 u with h | h
    · rw [uIcc_of_le h] at hx; exact lt_of_lt_of_le one_pos hx.1
    · rw [uIcc_of_ge h] at hx; exact lt_of_lt_of_le hu hx.1
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuousOn_bp4Gd.mono hsub).intervalIntegrable)
    (continuousOn_bp4Gd.stronglyMeasurableAtFilter isOpen_Ioi u hu)
    (continuousOn_bp4Gd.continuousAt (Ioi_mem_nhds hu))

/-- `G''(u) = 1/(u(1+u)²) − log (u/(1+u))/(1+u)²`. -/
def bp4Gdd (u : ℝ) : ℝ := 1 / (u * (1 + u) ^ 2) - Real.log (u / (1 + u)) / (1 + u) ^ 2

theorem hasDerivAt_bp4Gd {u : ℝ} (hu : 0 < u) : HasDerivAt bp4Gd (bp4Gdd u) u := by
  have h1 : (1 : ℝ) + u ≠ 0 := by positivity
  have h2 : u / (1 + u) ≠ 0 := by positivity
  have hd := ((((hasDerivAt_id' u).div ((hasDerivAt_id' u).const_add 1) h1).log h2).div
    ((hasDerivAt_id' u).const_add 1) h1)
  refine (hd : HasDerivAt (fun x => Real.log (x / (1 + x)) / (1 + x)) _ u).congr_deriv ?_
  unfold bp4Gdd
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
  field_simp
  ring

theorem contDiffOn_bp4G : ContDiffOn ℝ 3 bp4G (Ioi 0) := by
  have hGd : ContDiffOn ℝ 2 bp4Gd (Ioi 0) := by
    intro u hu
    have hu : (0 : ℝ) < u := hu
    refine ContDiffAt.contDiffWithinAt ?_
    unfold bp4Gd
    have h1 : (1 : ℝ) + u ≠ 0 := by positivity
    have h2 : u / (1 + u) ≠ 0 := by positivity
    exact ((contDiffAt_id.div (contDiffAt_const.add contDiffAt_id) h1).log h2).div
      (contDiffAt_const.add contDiffAt_id) h1
  rw [show (3 : WithTop ℕ∞) = 2 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun u hu => (hasDerivAt_bp4G hu).differentiableAt.differentiableWithinAt,
    by simp, hGd.congr fun u hu => (hasDerivAt_bp4G hu).deriv⟩

theorem contDiffOn_bp4Q : ContDiffOn ℝ 3 bp4Q bpDom := by
  have hD : ContDiff ℝ 3 (fun v : ℝ × ℝ × ℝ => v.1 - v.2.1) :=
    contDiff_fst.sub (contDiff_fst.comp contDiff_snd)
  have h1 : ContDiffOn ℝ 3 (fun v : ℝ × ℝ × ℝ => Real.log (v.1 - v.2.1)) bpDom :=
    hD.contDiffOn.log fun v hv => (sub_pos.2 hv.2).ne'
  have hs : ContDiffOn ℝ 3 (fun v : ℝ × ℝ × ℝ => (v.1 - v.2.1) / v.2.1) bpDom :=
    hD.contDiffOn.div (contDiff_fst.comp contDiff_snd).contDiffOn fun v hv => hv.1.ne'
  have h2 : ContDiffOn ℝ 3 (fun v : ℝ × ℝ × ℝ => bp4G ((v.1 - v.2.1) / v.2.1)) bpDom :=
    contDiffOn_bp4G.comp hs fun v hv => div_pos (sub_pos.2 hv.2) hv.1
  exact ((contDiff_snd.comp contDiff_snd).contDiffOn.sub h1).sub h2

/-! ### `G` is bounded above -/

theorem bp4Gd_nonpos {u : ℝ} (hu : 0 < u) : bp4Gd u ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg
    (Real.log_nonpos (by positivity) ((div_le_one (by positivity)).2 (by linarith)))
    (by positivity)

theorem continuousOn_bp4G : ContinuousOn bp4G (Ioi 0) := fun u hu =>
  (hasDerivAt_bp4G hu).continuousAt.continuousWithinAt

/-- **`G` is bounded above** (Rohde–Schramm, Lemma 7.2: `sup {G(x) : x > 0} < ∞`). -/
theorem bp4G_le_two {s : ℝ} (hs : 0 < s) : bp4G s ≤ 2 := by
  have hG1 : bp4G 1 = 0 := intervalIntegral.integral_same
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  rcases le_total 1 s with h1 | h1
  · -- `G` is antitone on `[1, ∞)`
    have hanti : AntitoneOn bp4G (Ici 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
        (continuousOn_bp4G.mono fun x (hx : 1 ≤ x) => show (0 : ℝ) < x from one_pos.trans_le hx) (f' := bp4Gd) ?_ ?_
      · intro x hx
        rw [interior_Ici] at hx
        exact (hasDerivAt_bp4G (one_pos.trans hx)).hasDerivWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        exact bp4Gd_nonpos (one_pos.trans hx)
    have := hanti (Set.mem_Ici.2 (le_refl (1 : ℝ))) h1 h1
    linarith
  · -- `ψ = G − (s log s − s) + s log 2` is monotone on `(0, 1]`
    set ψ : ℝ → ℝ := fun x => bp4G x - (x * Real.log x - x) + x * Real.log 2 with hψ
    have hmono : MonotoneOn ψ (Ioc 0 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1) ?_
        (f' := fun x => bp4Gd x - Real.log x + Real.log 2) ?_ ?_
      · intro x hx
        have hx0 : 0 < x := hx.1
        refine ContinuousAt.continuousWithinAt ?_
        have := (hasDerivAt_bp4G hx0).continuousAt
        exact (this.sub ((continuousAt_id.mul (Real.continuousAt_log hx0.ne')).sub
          continuousAt_id)).add (continuousAt_id.mul continuousAt_const)
      · intro x hx
        rw [interior_Ioc] at hx
        have hx0 : 0 < x := hx.1
        have hd := ((hasDerivAt_bp4G hx0).sub (((hasDerivAt_id' x).mul
          (Real.hasDerivAt_log hx0.ne')).sub (hasDerivAt_id' x))).add
          ((hasDerivAt_id' x).mul_const (Real.log 2))
        refine HasDerivAt.hasDerivWithinAt ?_
        refine (hd : HasDerivAt (fun x => bp4G x - (x * Real.log x - x) + x * Real.log 2) _ x
          ).congr_deriv ?_
        try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
        field_simp
        ring
      · intro x hx
        rw [interior_Ioc] at hx
        have hx0 : 0 < x := hx.1
        have hl : Real.log (x / (1 + x)) = Real.log x - Real.log (1 + x) :=
          Real.log_div hx0.ne' (by positivity)
        have hl2 : Real.log (1 + x) ≤ Real.log 2 :=
          Real.log_le_log (by positivity) (by linarith [hx.2])
        have hneg : Real.log (x / (1 + x)) ≤ 0 :=
          Real.log_nonpos (by positivity) ((div_le_one (by positivity)).2 (by linarith))
        have hge : Real.log (x / (1 + x)) ≤ bp4Gd x := by
          unfold bp4Gd
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        show 0 ≤ bp4Gd x - Real.log x + Real.log 2
        linarith
    have hψs := hmono ⟨hs, h1⟩ ⟨one_pos, le_rfl⟩ h1
    simp only [hψ, hG1, Real.log_one, mul_zero] at hψs
    have hsl : s * Real.log s ≤ 0 := by
      have := Real.log_nonpos hs.le h1; nlinarith
    have : 0 ≤ s * Real.log 2 := by positivity
    linarith

/-! ### Derivatives along lines -/

theorem deriv_deriv_eq_of_eventually_bp {f g : ℝ → ℝ} {g' : ℝ}
    (hf : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt f (g s) s) (hg : HasDerivAt g g' 0) :
    deriv (deriv f) 0 = g' := by
  have : deriv f =ᶠ[𝓝 0] g := hf.mono fun s hs => hs.deriv
  rw [this.deriv_eq, hg.deriv]

theorem bp1Test_line (κ : ℝ) (v w : ℝ × ℝ × ℝ) (s : ℝ) :
    bp1Test κ (v + s • w) = (((v.1 + s * w.1) - (v.2.1 + s * w.2.1)) *
      Real.exp (-(v.2.2 + s * w.2.2))) ^ (-bp1Exp κ) *
      (2 - (v.2.1 + s * w.2.1) / (v.1 + s * w.1)) := by
  simp only [bp1Test, bpUps, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]

theorem bp1Test_noise_line (κ k : ℝ) (v : ℝ × ℝ × ℝ) (s : ℝ) :
    bp1Test κ (v + s • ((-k, -k, 0) : ℝ × ℝ × ℝ)) =
      bpUps v ^ (-bp1Exp κ) * (2 - (v.2.1 - s * k) / (v.1 - s * k)) := by
  rw [bp1Test_line]
  simp only [bpUps, mul_zero, add_zero]
  rw [show v.1 + s * -k - (v.2.1 + s * -k) = v.1 - v.2.1 by ring,
    show v.2.1 + s * -k = v.2.1 - s * k by ring, show v.1 + s * -k = v.1 - s * k by ring]

theorem hasDerivAt_bp1Aux (q X O L a b m : ℝ) (hD : 0 < X - O) (hX : X ≠ 0) :
    HasDerivAt (fun s : ℝ => (((X + s * a) - (O + s * b)) * Real.exp (-(L + s * m))) ^ q *
        (2 - (O + s * b) / (X + s * a)))
      (((X - O) * Real.exp (-L)) ^ q *
        (q * ((a - b) / (X - O) - m) * (2 - O / X) - (b * X - O * a) / X ^ 2)) 0 := by
  have h1 := (((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X).sub
    (((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add O)
  have h2 := (((hasDerivAt_id' (0 : ℝ)).mul_const m).const_add L).neg.exp
  have hv : (X + 0 * a - (O + 0 * b)) * Real.exp (-(L + 0 * m)) = (X - O) * Real.exp (-L) := by
    simp
  have hY : 0 < (X - O) * Real.exp (-L) := mul_pos hD (Real.exp_pos _)
  have h3 := (h1.mul h2).rpow_const (p := q) (Or.inl (by
    show (X + 0 * a - (O + 0 * b)) * Real.exp (-(L + 0 * m)) ≠ 0
    rw [hv]; exact hY.ne'))
  have hX0 : X + 0 * a ≠ 0 := by simpa using hX
  have h4 := ((((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add O).div
    (((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X) hX0).const_sub 2
  refine ((h3.mul h4 : HasDerivAt (fun s : ℝ => (((X + s * a) - (O + s * b)) *
    Real.exp (-(L + s * m))) ^ q * (2 - (O + s * b) / (X + s * a))) _ 0)).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, zero_mul, add_zero, one_mul, mul_zero, neg_zero, mul_neg, neg_mul]
  rw [Real.rpow_sub_one hY.ne']
  have hD' : X - O ≠ 0 := hD.ne'
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
  field_simp
  ring

theorem deriv_deriv_bp1Noise (A X O k : ℝ) (hX : X ≠ 0) :
    deriv (deriv (fun s : ℝ => A * (2 - (O - s * k) / (X - s * k)))) 0 =
      A * (2 * k ^ 2 * (X - O) / X ^ 3) := by
  have hc : ContinuousAt (fun s : ℝ => X - s * k) 0 := by fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), X - s * k ≠ 0 := hc.eventually_ne (by simpa using hX)
  refine deriv_deriv_eq_of_eventually_bp (g := fun s => A * k * (X - O) / (X - s * k) ^ 2)
    (hev.mono fun s hs => ?_) ?_
  · have hd := (((((hasDerivAt_id' s).mul_const k).const_sub O).div
      (((hasDerivAt_id' s).mul_const k).const_sub X) hs).const_sub 2).const_mul A
    refine (hd : HasDerivAt (fun s : ℝ => A * (2 - (O - s * k) / (X - s * k))) _ s
      ).congr_deriv ?_
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
    field_simp
    ring
  · have hX0 : (X - 0 * k) ^ 2 ≠ 0 := by simpa using hX
    have hd := (hasDerivAt_const (0 : ℝ) (A * k * (X - O))).div
      ((((hasDerivAt_id' (0 : ℝ)).mul_const k).const_sub X).pow 2) hX0
    refine (hd : HasDerivAt (fun s : ℝ => A * k * (X - O) / (X - s * k) ^ 2) _ 0
      ).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply, zero_mul, sub_zero, one_mul]
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
    field_simp
    ring

/-- **The BP1-a generator** (where the taming is inactive). -/
theorem dynkinGen_bp1Test_eq {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} {v : ℝ × ℝ × ℝ} (hc : 0 < c)
    (hv : c ≤ v.2.1 ∧ v.2.1 < v.1) :
    dynkinGen (bpDrift c) (bpNoise κ) (bp1Test κ) v =
      bpUps v ^ (-bp1Exp κ) * ((v.1 - v.2.1) / (v.1 ^ 2 * v.2.1) *
        (2 * bp1Exp κ * (2 - v.2.1 / v.1) - 2 * (1 + v.2.1 / v.1) + κ * (v.2.1 / v.1))) := by
  have hO : 0 < v.2.1 := hc.trans_le hv.1
  have hX : 0 < v.1 := hO.trans hv.2
  have hmem : v ∈ bpDom := ⟨hO, hv.2⟩
  have hF : ContDiffAt ℝ 3 (bp1Test κ) v :=
    (contDiffOn_bp1Test κ).contDiffAt (isOpen_bpDom.mem_nhds hmem)
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line (hF.of_le (by norm_num))]
  have e1 : (fun s : ℝ => bp1Test κ (v + s • bpDrift c v)) = fun s =>
      (((v.1 + s * (bpDrift c v).1) - (v.2.1 + s * (bpDrift c v).2.1)) *
      Real.exp (-(v.2.2 + s * (bpDrift c v).2.2))) ^ (-bp1Exp κ) *
      (2 - (v.2.1 + s * (bpDrift c v).2.1) / (v.1 + s * (bpDrift c v).1)) :=
    funext fun s => bp1Test_line κ v _ s
  have e2 : (fun s : ℝ => bp1Test κ (v + s • bpNoise κ)) = fun s =>
      bpUps v ^ (-bp1Exp κ) * (2 - (v.2.1 - s * Real.sqrt κ) / (v.1 - s * Real.sqrt κ)) :=
    funext fun s => bp1Test_noise_line κ (Real.sqrt κ) v s
  rw [e1, e2, (hasDerivAt_bp1Aux _ _ _ _ _ _ _ (sub_pos.2 hv.2) hX.ne').deriv,
    deriv_deriv_bp1Noise _ _ _ _ hX.ne', bpDrift_of_le hv]
  simp only [bpUps]
  rw [Real.sq_sqrt hκ]
  have hD : v.1 - v.2.1 ≠ 0 := (sub_pos.2 hv.2).ne'
  have hX' := hX.ne'
  have hO' := hO.ne'
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
  field_simp
  ring

/-- **BP1-a (κ < 4): `Υ^{−p}(2 − ρ)` is a supersolution** where the taming is inactive. -/
theorem dynkinGen_bp1_le {κ : ℝ} (hκ : 0 < κ) (_hκ4 : κ < 4) {c : ℝ} (hc : 0 < c)
    {v : ℝ × ℝ × ℝ} (hv : c ≤ v.2.1 ∧ v.2.1 < v.1) :
    dynkinGen (bpDrift c) (bpNoise κ) (bp1Test κ) v ≤ 0 := by
  have hO : 0 < v.2.1 := hc.trans_le hv.1
  have hX : 0 < v.1 := hO.trans hv.2
  rw [dynkinGen_bp1Test_eq hκ.le hc hv]
  have hY : 0 < bpUps v ^ (-bp1Exp κ) := Real.rpow_pos_of_pos (bpUps_pos ⟨hO, hv.2⟩) _
  have hQ : 0 ≤ (v.1 - v.2.1) / (v.1 ^ 2 * v.2.1) :=
    div_nonneg (sub_pos.2 hv.2).le (by positivity)
  set ρ := v.2.1 / v.1 with hρ
  have hρ0 : 0 ≤ ρ := (div_pos hO hX).le
  have hρ1 : ρ ≤ 1 := (div_le_one hX).2 hv.2.le
  have hp1 : 4 * bp1Exp κ - 2 ≤ 0 := by
    have := min_le_left (1 / 2 : ℝ) ((4 - κ) / 2); unfold bp1Exp; linarith
  have hp2 : 2 * bp1Exp κ - 4 + κ ≤ 0 := by
    have := min_le_right (1 / 2 : ℝ) ((4 - κ) / 2); unfold bp1Exp; linarith
  have hlin : 2 * bp1Exp κ * (2 - ρ) - 2 * (1 + ρ) + κ * ρ =
      (1 - ρ) * (4 * bp1Exp κ - 2) + ρ * (2 * bp1Exp κ - 4 + κ) := by ring
  have hneg : 2 * bp1Exp κ * (2 - ρ) - 2 * (1 + ρ) + κ * ρ ≤ 0 := by
    rw [hlin]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) hp1)
      (mul_nonpos_of_nonneg_of_nonpos hρ0 hp2)
  exact mul_nonpos_of_nonneg_of_nonpos hY.le (mul_nonpos_of_nonneg_of_nonpos hQ hneg)

/-! ### BP1-4 (κ = 4) -/

theorem bp4Q_line (v w : ℝ × ℝ × ℝ) (s : ℝ) :
    bp4Q (v + s • w) = (v.2.2 + s * w.2.2) - Real.log ((v.1 + s * w.1) - (v.2.1 + s * w.2.1)) -
      bp4G (((v.1 + s * w.1) - (v.2.1 + s * w.2.1)) / (v.2.1 + s * w.2.1)) := by
  simp only [bp4Q, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

theorem bp4Q_noise_line (k : ℝ) (v : ℝ × ℝ × ℝ) (s : ℝ) :
    bp4Q (v + s • ((-k, -k, 0) : ℝ × ℝ × ℝ)) =
      (v.2.2 - Real.log (v.1 - v.2.1)) - bp4G ((v.1 - v.2.1) / (v.2.1 - s * k)) := by
  rw [bp4Q_line]
  simp only [mul_zero, add_zero]
  rw [show v.1 + s * -k - (v.2.1 + s * -k) = v.1 - v.2.1 by ring,
    show v.2.1 + s * -k = v.2.1 - s * k by ring]

theorem hasDerivAt_bp4Aux (X O L a b m : ℝ) (hO : 0 < O) (hD : 0 < X - O) :
    HasDerivAt (fun s : ℝ => (L + s * m) - Real.log ((X + s * a) - (O + s * b)) -
        bp4G (((X + s * a) - (O + s * b)) / (O + s * b)))
      (m - (a - b) / (X - O) - bp4Gd ((X - O) / O) * (((a - b) * O - (X - O) * b) / O ^ 2)) 0 := by
  have hL := ((hasDerivAt_id' (0 : ℝ)).mul_const m).const_add L
  have h1 := (((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X).sub
    (((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add O)
  have hD0 : X + 0 * a - (O + 0 * b) ≠ 0 := by simpa using hD.ne'
  have hO0 : O + 0 * b ≠ 0 := by simpa using hO.ne'
  have hlog := h1.log hD0
  have hu := h1.div (((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add O) hO0
  have hG := (hasDerivAt_bp4G (div_pos hD hO)).comp_of_eq 0 hu (by simp)
  refine ((hL.sub hlog).sub hG : HasDerivAt (fun s : ℝ => (L + s * m) -
    Real.log ((X + s * a) - (O + s * b)) -
    bp4G (((X + s * a) - (O + s * b)) / (O + s * b))) _ 0).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.div_apply, zero_mul, add_zero, one_mul]

theorem deriv_deriv_bp4Noise (C X O k : ℝ) (hO : 0 < O) (hD : 0 < X - O) :
    deriv (deriv (fun s : ℝ => C - bp4G ((X - O) / (O - s * k)))) 0 =
      -(bp4Gdd ((X - O) / O) * ((X - O) * k / O ^ 2) * ((X - O) * k / O ^ 2) +
        bp4Gd ((X - O) / O) * (2 * (X - O) * k ^ 2 / O ^ 3)) := by
  have hc : ContinuousAt (fun s : ℝ => O - s * k) 0 := by fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < O - s * k :=
    hc.eventually (lt_mem_nhds (by simpa using hO))
  refine deriv_deriv_eq_of_eventually_bp
    (g := fun s => -(bp4Gd ((X - O) / (O - s * k)) * ((X - O) * k / (O - s * k) ^ 2)))
    (hev.mono fun s hs => ?_) ?_
  · have hu := (hasDerivAt_const s (X - O)).div
      (((hasDerivAt_id' s).mul_const k).const_sub O) hs.ne'
    have hG := ((hasDerivAt_bp4G (div_pos hD hs)).comp s hu).const_sub C
    refine (hG : HasDerivAt (fun s : ℝ => C - bp4G ((X - O) / (O - s * k))) _ s).congr_deriv ?_
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
    field_simp
    ring
  · have hO0 : O - 0 * k ≠ 0 := by simpa using hO.ne'
    have hu := (hasDerivAt_const (0 : ℝ) (X - O)).div
      (((hasDerivAt_id' (0 : ℝ)).mul_const k).const_sub O) hO0
    have hGd := (hasDerivAt_bp4Gd (div_pos hD hO)).comp_of_eq 0 hu (by simp)
    have hO2 : (O - 0 * k) ^ 2 ≠ 0 := by simpa using hO.ne'
    have hq := (hasDerivAt_const (0 : ℝ) ((X - O) * k)).div
      ((((hasDerivAt_id' (0 : ℝ)).mul_const k).const_sub O).pow 2) hO2
    refine ((hGd.mul hq).neg : HasDerivAt (fun s : ℝ =>
      -(bp4Gd ((X - O) / (O - s * k)) * ((X - O) * k / (O - s * k) ^ 2))) _ 0).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, zero_mul, sub_zero, one_mul, Function.comp]
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
    field_simp
    ring

/-- **Rohde–Schramm's `Q − G(s)` has zero generator** (κ = 4) where the taming is
inactive (Rohde–Schramm, Lemma 7.2, pp. 32–33). -/
theorem dynkinGen_bp4Q_eq {c : ℝ} (hc : 0 < c) {v : ℝ × ℝ × ℝ}
    (hv : c ≤ v.2.1 ∧ v.2.1 < v.1) :
    dynkinGen (bpDrift c) (bpNoise 4) bp4Q v = 0 := by
  have hO : 0 < v.2.1 := hc.trans_le hv.1
  have hX : 0 < v.1 := hO.trans hv.2
  have hDp : 0 < v.1 - v.2.1 := sub_pos.2 hv.2
  have hmem : v ∈ bpDom := ⟨hO, hv.2⟩
  have hF : ContDiffAt ℝ 3 bp4Q v :=
    contDiffOn_bp4Q.contDiffAt (isOpen_bpDom.mem_nhds hmem)
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line (hF.of_le (by norm_num))]
  have e1 : (fun s : ℝ => bp4Q (v + s • bpDrift c v)) = fun s =>
      (v.2.2 + s * (bpDrift c v).2.2) -
      Real.log ((v.1 + s * (bpDrift c v).1) - (v.2.1 + s * (bpDrift c v).2.1)) -
      bp4G (((v.1 + s * (bpDrift c v).1) - (v.2.1 + s * (bpDrift c v).2.1)) /
        (v.2.1 + s * (bpDrift c v).2.1)) :=
    funext fun s => bp4Q_line v _ s
  have e2 : (fun s : ℝ => bp4Q (v + s • bpNoise 4)) = fun s =>
      (v.2.2 - Real.log (v.1 - v.2.1)) - bp4G ((v.1 - v.2.1) / (v.2.1 - s * Real.sqrt 4)) :=
    funext fun s => bp4Q_noise_line (Real.sqrt 4) v s
  rw [e1, e2, (hasDerivAt_bp4Aux _ _ _ _ _ _ hO hDp).deriv,
    deriv_deriv_bp4Noise _ _ _ _ hO hDp, bpDrift_of_le hv]
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  simp only [bp4Gd, bp4Gdd]
  generalize Real.log ((v.1 - v.2.1) / v.2.1 / (1 + (v.1 - v.2.1) / v.2.1)) = ℓ
  have hD := hDp.ne'
  have hX' := hX.ne'
  have hO' := hO.ne'
  have h1 : 1 + (v.1 - v.2.1) / v.2.1 ≠ 0 := by positivity
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply] at *
  field_simp
  ring

theorem bp4Test_eq_neg_bp4Q : bp4Test = -bp4Q := by
  funext v; simp only [bp4Test, bp4Q, Pi.neg_apply]; ring

/-- On `bpDom`, `bp4Test v = log Υ + G((X − O)/O)`. -/
theorem bp4Test_eq_log_bpUps {v : ℝ × ℝ × ℝ} (hv : v ∈ bpDom) :
    bp4Test v = Real.log (bpUps v) + bp4G ((v.1 - v.2.1) / v.2.1) := by
  unfold bp4Test bpUps
  rw [Real.log_mul (sub_pos.2 hv.2).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem contDiffOn_bp4Test : ContDiffOn ℝ 3 bp4Test bpDom := by
  rw [bp4Test_eq_neg_bp4Q]; exact contDiffOn_bp4Q.neg

theorem dynkinGen_neg_bp {b : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} {e : ℝ × ℝ × ℝ} {F : ℝ × ℝ × ℝ → ℝ}
    (x : ℝ × ℝ × ℝ) : dynkinGen b e (-F) x = -dynkinGen b e F x := by
  unfold dynkinGen
  rw [fderiv_neg, iteratedFDeriv_neg_apply]
  change -(fderiv ℝ F x (b x)) + 1 / 2 * -(iteratedFDeriv ℝ 2 F x ![e, e]) = _
  ring

/-- **BP1-4 (κ = 4): `log Υ + G(s)` has zero generator** where the taming is inactive
(Rohde–Schramm, Lemma 7.2, pp. 32–33: `Q − G_t` is a local martingale, `Q = −log Υ`).
TASKS/EXT_RS BP1-4 sign corrected per RS Lemma 7.2 (`Q = −log Υ`). -/
theorem dynkinGen_bp14_eq {c : ℝ} (hc : 0 < c) {v : ℝ × ℝ × ℝ}
    (hv : c ≤ v.2.1 ∧ v.2.1 < v.1) :
    dynkinGen (bpDrift c) (bpNoise 4) bp4Test v = 0 := by
  rw [bp4Test_eq_neg_bp4Q, dynkinGen_neg_bp, dynkinGen_bp4Q_eq hc hv, neg_zero]

end RS
end QuantumZipper
