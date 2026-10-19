import GaussianLQG.Uniform.InverseMoments.Planar
import LQGMetric.Papers.DDDF.T20BRect
import LQGMetric.Papers.DDDF.S6P21Max

/-!
# Inverse separated-distance moments: tools for one strip (Route U, item U13 (b))

Phase B, packet PB-U13 (ledger packet B-9); helpers in the namespace `GaussianLQG.Uniform.InvMom`.
Source: `blueprint/phaseB/uniform-ledger.tex`, U13 (b)
and its ledger row, with the audit `planning/audits/B0b-ledger-audit.md` (S-1, M-4, §3: "move each
strip to the origin with the full field"). The tools are:

* `lintegral_comp_eq_of_measure_eq`: two random variables with the same law have the same
  integrals of measurable functions;
* `lintegral_stripLen_eq`: the short-way crossing length of the strip `T20D.RS k j` for the field
  `φ_{0,n}` has the law of the crossing of `2^{-k} R_{1,3}` (the strip moved to the origin):
  motion invariance `measure_crossLenIn_phiMN_motion` (DDDF (2.30) without scaling);
* `toReal_rectLen_ge`: `L_f(R_{a,b}) < ∞` and `L_f(R_{a,b}) ≥ e^{-|ξ| M} a` when `|f| ≤ M` on
  `R_{a,b}` (`rectLen_ge`, `rectLen_ne_top`);
* `supPhi W P m ω = sup_{[0,1]²} |φ_{0,m}(·, ω)|` and its exponential moment
  `E e^{(3/2) supPhi} ≤ 4^{(3/2) m + K √m}` with `K` chosen before the probability space
  (`lintegral_exp_supPhi_le`, from DDDF (2.11), `prop2_expMoment_int` at `γ' = 3/2 < 2`);
* `rectAB_strip_subset`: for `k ≥ 2` the strip `2^{-k} R_{1,3}` at the origin lies in `[0,1]²`.
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

/-! ### Law transfer of integrals -/

/-- two measurable random variables whose laws agree on measurable sets have the same integrals of
measurable nonnegative functions -/
lemma lintegral_comp_eq_of_measure_eq {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {X Y : Ω → α} (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ S : Set α, MeasurableSet S → P {ω | X ω ∈ S} = P {ω | Y ω ∈ S})
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (X ω) ∂P = ∫⁻ ω, g (Y ω) ∂P := by
  have hmap : P.map X = P.map Y := Measure.ext fun S hS => by
    rw [Measure.map_apply hX hS, Measure.map_apply hY hS]; exact h S hS
  rw [← lintegral_map hg hX, hmap, lintegral_map hg hY]

/-! ### The strips moved to the origin -/

/-- the strip `RS k j` as the image of `2^{-k} R_{1,3}` under `x ↦ u x + c` -/
lemma RS_eq_image (k : ℕ) (j : Circle × ℂ) :
    T20D.RS k j = (fun x => (j.1 : ℂ) * x + j.2) ''
      (rectAB ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k * 3)).toSet := by
  rw [T20D.RS, T20B.mot_image, image_mul_rectAB_toSet (by positivity), mul_one]

lemma RS₁_eq_image (k : ℕ) (j : Circle × ℂ) :
    T20D.RS₁ k j = (fun x => (j.1 : ℂ) * x + j.2) ''
      (rectAB ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k * 3)).side₁ := by
  rw [T20D.RS₁, T20B.mot_image, image_mul_rectAB_side₁ (by positivity), mul_one]

lemma RS₂_eq_image (k : ℕ) (j : Circle × ℂ) :
    T20D.RS₂ k j = (fun x => (j.1 : ℂ) * x + j.2) ''
      (rectAB ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k * 3)).side₂ := by
  rw [T20D.RS₂, T20B.mot_image, image_mul_rectAB_side₂ (by positivity), mul_one]

lemma isCompact_RS (k : ℕ) (j : Circle × ℂ) : IsCompact (T20D.RS k j) := by
  rw [RS_eq_image]
  exact (MarkedRect.isCompact_toSet _).image ((continuous_const.mul continuous_id).add
    continuous_const)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the crossing length of a strip is measurable -/
lemma measurable_stripLen (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n) (k : ℕ)
    (j : Circle × ℂ) :
    Measurable fun ω => crossLenIn ξ (fun x => phiMN W P m n x ω) (T20D.RS k j)
      (T20D.RS₁ k j) (T20D.RS₂ k j) :=
  measurable_crossLenIn (isCompact_RS k j) (isPhiVersion_phiMN hW hmn).cont
    (isPhiVersion_phiMN hW hmn).meas

/-- **Motion invariance for the strips**: the crossing length of `RS k j` for `φ_{0,n}` has the
law of the crossing of the strip `2^{-k} R_{1,3}` at the origin
(`measure_crossLenIn_phiMN_motion`). -/
lemma lintegral_stripLen_eq (hW : IsWhiteNoise P W) (n k : ℕ) (j : Circle × ℂ)
    {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (crossLenIn ξ (fun x => phiMN W P 0 n x ω) (T20D.RS k j) (T20D.RS₁ k j)
        (T20D.RS₂ k j)) ∂P =
      ∫⁻ ω, g (rectLen ξ (fun x => phiMN W P 0 n x ω)
        (rectAB ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k * 3))) ∂P := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  set R := rectAB ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k * 3)
  refine lintegral_comp_eq_of_measure_eq (measurable_stripLen hW (Nat.zero_le n) k j)
    (measurable_crossLenIn R.isCompact_toSet hφ.cont hφ.meas) (fun S hS => ?_) hg
  rw [RS_eq_image, RS₁_eq_image, RS₂_eq_image]
  exact measure_crossLenIn_phiMN_motion hW (Nat.zero_le n) j.1 j.2 R.isCompact_toSet hS

/-! ### Elementary bounds for the crossing of a rectangle -/

lemma crossWidth_rectAB' (a b : ℝ) : (rectAB a b).crossWidth = a := by
  simp [MarkedRect.crossWidth, rectAB]

/-- `L_f(R_{a,b})` is finite and at least `e^{-|ξ| M} a` when `|f| ≤ M` on `R_{a,b}` -/
lemma toReal_rectLen_ge {f : ℂ → ℝ} (hf : Continuous f) {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : ∀ x ∈ (rectAB a b).toSet, |f x| ≤ M) :
    rectLen ξ f (rectAB a b) ≠ ⊤ ∧
      Real.exp (-(|ξ| * M)) * a ≤ (rectLen ξ f (rectAB a b)).toReal := by
  have hne : rectLen ξ f (rectAB a b) ≠ ⊤ := rectLen_ne_top (rectAB a b) ha hb hf
  refine ⟨hne, ?_⟩
  have hge := rectLen_ge (ξ := ξ) (rectAB a b) hM
  rw [crossWidth_rectAB'] at hge
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hge

/-! ### The coarse field on the unit square -/

/-- `sup_{[0,1]²} |φ_{0,m}(·, ω)|` -/
def supPhi (W : WNSpace → Ω → ℝ) (P : Measure Ω) (m : ℕ) (ω : Ω) : ℝ :=
  ⨆ z : ferniqueBox (0 : ℂ) 1, |phiMN W P 0 m z ω|

lemma supPhi_nonneg (W : WNSpace → Ω → ℝ) (P : Measure Ω) (m : ℕ) (ω : Ω) :
    0 ≤ supPhi W P m ω :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma abs_le_supPhi (hW : IsWhiteNoise P W) (m : ℕ) (ω : Ω) {x : ℂ}
    (hx : x ∈ ferniqueBox (0 : ℂ) 1) : |phiMN W P 0 m x ω| ≤ supPhi W P m ω := by
  have hc := (isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω
  have hcpt : IsCompact (ferniqueBox (0 : ℂ) 1) := isCompact_ferniqueBox 0 1
  have := isCompact_iff_compactSpace.1 hcpt
  have hbdd : BddAbove (range fun z : ferniqueBox (0 : ℂ) 1 => |phiMN W P 0 m z ω|) :=
    (isCompact_range ((continuous_abs.comp hc).comp continuous_subtype_val)).bddAbove
  exact le_ciSup hbdd (⟨x, hx⟩ : ferniqueBox (0 : ℂ) 1)

/-- **DDDF (2.11) at `γ' = 3/2`, constant before the probability space**:
`E e^{(3/2) sup_{[0,1]²}|φ_{0,m}|} ≤ 4^{(3/2) m + K √m}` (`prop2_expMoment_int`). -/
theorem lintegral_exp_supPhi_le : ∃ K : ℝ,
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ m : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (3 / 2 * supPhi W P m ω)) ∂P ≤
        ENNReal.ofReal ((4 : ℝ) ^ (3 / 2 * (m : ℝ) + K * Real.sqrt m)) := by
  obtain ⟨K, hK⟩ := prop2_expMoment_int (γ := 3 / 2) (by norm_num) (by norm_num)
  refine ⟨K, fun {Ω} _ {P} {W} hW m => ?_⟩
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hY : ∀ x, (fun ω => phiMN W P 0 m x ω) =ᵐ[P] phi W ((2 : ℝ) ^ m)⁻¹ 1 x := by
    intro x
    have e : phi W ((2 : ℝ)⁻¹ ^ m) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ m)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    rw [← e]; exact hφ.ae_eq x
  obtain ⟨hint, hle⟩ := hK hW m (phiMN W P 0 m) hY hφ.cont
  simp only [supPhi]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal hle

/-- for `k ≥ 2` the strip `2^{-k} R_{1,3}` at the origin lies in `[0,1]²` (audit M-4) -/
lemma rectAB_strip_subset {k : ℕ} (hk : 2 ≤ k) :
    (rectAB ((2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k * 3)).toSet ⊆ ferniqueBox (0 : ℂ) 1 := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ k := by positivity
  have h4 : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have h4' : (2 : ℝ)⁻¹ ^ k ≤ 1 / 4 := by norm_num at h4 ⊢; exact h4
  intro x hx
  rw [mem_rectAB_toSet] at hx
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hx
  simp only [ferniqueBox, Complex.zero_re, Complex.zero_im, zero_add, Complex.mem_reProdIm,
    mem_Icc]
  exact ⟨⟨a1, by linarith⟩, b1, by linarith⟩

end InvMom

end Uniform
end GaussianLQG
