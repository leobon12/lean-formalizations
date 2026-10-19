import LQGMetric.Papers.DDDF.P10Law
import LQGMetric.Papers.DDDF.T20CMom
import LQGMetric.Papers.DDDF.C8

/-!
# Law invariance of `X_{a,b}` and the Prop 5 constants before the probability space

Phase B, packet PB-RSW (Route U, items U1 and U4 of `planning/audits/B1-S6-feasibility.md`;
uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`, U1, Recipe B).

The ledger states every uniform node with its constants chosen before `ξ` and before the
probability space `(Ω, P, W)`. In `LQGMetric` the constants of DDDF Prop 5 (`dddf_prop5_XAB`,
`exists_tail_XAB_unif`) and of the exponential moments of `X_{a,b}`
(`T20C.expMoment_XAB_shift`) are stated after `hW : IsWhiteNoise P W`. They only depend on the
law of `X_{a,b}`, and this law is the same for every white noise on every probability space. This
file proves that, and moves the constants before `Ω`:

* `map_restrict_wn_eq`, `map_wn_eq`: the law of `(W (F i))_{i ∈ ι}` on `ι → ℝ` does not depend on
  the white noise (finite-dimensional laws by characteristic functionals, then
  `IsProjectiveLimit.unique`; the argument of `map_phi_eq`, `LQGMetric/Papers/DDDF/P10Law.lean`);
* `ae_XAB_shift_eq_xabFun`: `X_{a,b}` on the translated box `c₁ + [0,a] × [0,b]` is a.s. a
  measurable function of countably many values `W (xabKer Q c₁ i)` (continuity of the fields
  reduces the supremum to a countable dense set);
* `map_XAB_shift_eq`, `measure_XAB_shift_eq`, `lintegral_XAB_shift_eq`: the law of `X_{a,b}`
  does not depend on the white noise;
* `dddf_prop5_XAB_W`, `exists_tail_XAB_unif_W`, `expMoment_XAB_shift_W`: the three templates
  with their constants before `Ω`, taken at a reference white noise on `(ℕ → ℝ, stdP)`
  (`exists_isWhiteNoise`).

Standard measure theory; no published source needed (own routine step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-! ### The law of a white noise applied to a family of vectors -/

section WNLaw

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {P : Measure Ω}
  {P₂ : Measure Ω₂}

/-- the law of a linear functional of `(W (F i))_{i ∈ I}` -/
lemma map_dual_restrict_wn {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ι : Type}
    [DecidableEq ι] (F : ι → WNSpace) (I : Finset ι) (L : StrongDual ℝ (I → ℝ)) :
    P.map (fun ω => L (I.restrict fun i => W (F i) ω)) =
      gaussianReal 0 (‖∑ i : I, L (Pitt.unitVec i) • F i‖ ^ 2).toNNReal := by
  refine ((hW.hasLaw (fun i : I => F i) (fun i => L (Pitt.unitVec i))).congr
    (Filter.Eventually.of_forall fun ω => ?_)).map_eq
  rw [Pitt.dual_apply_eq_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- equal finite-dimensional laws of `(W (F i))_i` for two white noises -/
lemma map_restrict_wn_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ} (hW : IsWhiteNoise P W)
    (hV : IsWhiteNoise P₂ V) {ι : Type} (F : ι → WNSpace) (I : Finset ι) :
    P.map (fun ω => I.restrict fun i => W (F i) ω) =
      P₂.map (fun ω => I.restrict fun i => V (F i) ω) := by
  classical
  have := hW.isProbabilityMeasure
  have := hV.isProbabilityMeasure
  have hm : Measurable (fun ω => I.restrict fun i => W (F i) ω) :=
    measurable_pi_iff.2 fun i => hW.measurable _
  have hm₂ : Measurable (fun ω => I.restrict fun i => V (F i) ω) :=
    measurable_pi_iff.2 fun i => hV.measurable _
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.continuous.measurable hm, Measure.map_map L.continuous.measurable hm₂]
  congr 1
  exact (map_dual_restrict_wn hW F I L).trans (map_dual_restrict_wn hV F I L).symm

/-- **The law of `(W (F i))_{i ∈ ι}` on `ι → ℝ` does not depend on the white noise.** -/
theorem map_wn_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ} (hW : IsWhiteNoise P W)
    (hV : IsWhiteNoise P₂ V) {ι : Type} (F : ι → WNSpace) :
    P.map (fun ω i => W (F i) ω) = P₂.map (fun ω i => V (F i) ω) := by
  have := hW.isProbabilityMeasure
  have := hV.isProbabilityMeasure
  have h1 := isProjectiveLimit_map (P := P) (X := fun i ω => W (F i) ω)
    (measurable_pi_iff.2 fun i => hW.measurable (F i)).aemeasurable
  have h2 := isProjectiveLimit_map (P := P₂) (X := fun i ω => V (F i) ω)
    (measurable_pi_iff.2 fun i => hV.measurable (F i)).aemeasurable
  have e : (fun I : Finset ι => P.map (fun ω => I.restrict fun i => W (F i) ω)) =
      fun I => P₂.map (fun ω => I.restrict fun i => V (F i) ω) :=
    funext fun I => map_restrict_wn_eq hW hV F I
  rw [e] at h1
  exact h1.unique h2

end WNLaw

/-! ### `X_{a,b}` as a function of countably many values of the white noise -/

/-- the kernels of `φ_{0,n}(y + c₁)` (`true`) and `ψ_{0,n}(y + c₁)` (`false`) -/
def xabKer (Q : PsiParams) (c₁ : ℂ) : ℕ × ℂ × Bool → WNSpace
  | (n, y, true) => phiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (y + c₁)
  | (n, y, false) => Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (y + c₁)

/-- `sup_n sup_{d ∈ D} |√π z(n,d,true) − √π z(n,d,false)|` -/
def xabFun {S : Set ℂ} (D : Set S) (z : ℕ × ℂ × Bool → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ d : D, ENNReal.ofReal |Real.sqrt Real.pi * z (n, ((d : S) : ℂ), true) -
    Real.sqrt Real.pi * z (n, ((d : S) : ℂ), false)|

lemma measurable_xabFun {S : Set ℂ} {D : Set S} (hD : D.Countable) : Measurable (xabFun D) := by
  have := hD.to_subtype
  refine Measurable.iSup fun n => Measurable.iSup fun d => ?_
  refine ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp ?_)
  exact ((measurable_pi_apply _).const_mul _).sub ((measurable_pi_apply _).const_mul _)

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {P : Measure Ω}
  {P₂ : Measure Ω₂}

/-- `X_{a,b}` on `c₁ + [0,a] × [0,b]` is a.s. `xabFun D` of the values `W (xabKer Q c₁ i)` -/
lemma ae_XAB_shift_eq_xabFun {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams)
    (c₁ : ℂ) (a b : ℝ) {D : Set (rectAB a b).toSet} (hDc : D.Countable) (hDd : Dense D) :
    (fun ω => XAB (fun n y => phiMN W P 0 n (y + c₁) ω) (fun n y => psiMN Q W P 0 n (y + c₁) ω)
      a b) =ᵐ[P] fun ω => xabFun D (fun i => W (xabKer Q c₁ i) ω) := by
  have := hDc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ (n : ℕ) (d : D),
      phiMN W P 0 n (((d : (rectAB a b).toSet) : ℂ) + c₁) ω =
        Real.sqrt Real.pi * W (xabKer Q c₁ (n, ((d : (rectAB a b).toSet) : ℂ), true)) ω ∧
      psiMN Q W P 0 n (((d : (rectAB a b).toSet) : ℂ) + c₁) ω =
        Real.sqrt Real.pi * W (xabKer Q c₁ (n, ((d : (rectAB a b).toSet) : ℂ), false)) ω := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro d
    filter_upwards [(isPhiVersion_phiMN hW (Nat.zero_le n)).ae_eq
        (((d : (rectAB a b).toSet) : ℂ) + c₁),
      (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).ae_eq
        (((d : (rectAB a b).toSet) : ℂ) + c₁)] with ω h1 h2
    exact ⟨h1.trans rfl, h2.trans rfl⟩
  filter_upwards [hall] with ω hω
  unfold XAB xabFun
  refine iSup_congr fun n => ?_
  have hc : Continuous fun y : ℂ =>
      ENNReal.ofReal |phiMN W P 0 n (y + c₁) ω - psiMN Q W P 0 n (y + c₁) ω| := by
    have h1 := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω
    have h2 := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont ω
    exact ENNReal.continuous_ofReal.comp (continuous_abs.comp
      ((h1.comp (continuous_id.add continuous_const)).sub
        (h2.comp (continuous_id.add continuous_const))))
  rw [T20B.biSup_eq_iSup_dense hDd hc]
  refine iSup_congr fun d => ?_
  rw [(hω n d).1, (hω n d).2]

/-- `X_{a,b}` on `c₁ + [0,a] × [0,b]` is a.e. measurable -/
lemma aemeasurable_XAB_shift {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams)
    (c₁ : ℂ) (a b : ℝ) :
    AEMeasurable (fun ω => XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
      (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (rectAB a b).toSet
  have hZ : Measurable (fun ω (i : ℕ × ℂ × Bool) => W (xabKer Q c₁ i) ω) :=
    measurable_pi_iff.2 fun i => hW.measurable _
  exact ((measurable_xabFun hDc).comp hZ).aemeasurable.congr
    (ae_XAB_shift_eq_xabFun hW Q c₁ a b hDc hDd).symm

/-- **The law of `X_{a,b}` on `c₁ + [0,a] × [0,b]` does not depend on the white noise.** -/
theorem map_XAB_shift_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ} (hW : IsWhiteNoise P W)
    (hV : IsWhiteNoise P₂ V) (Q : PsiParams) (c₁ : ℂ) (a b : ℝ) :
    P.map (fun ω => XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
        (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b) =
      P₂.map (fun ω => XAB (fun n y => phiMN V P₂ 0 n (y + c₁) ω)
        (fun n y => psiMN Q V P₂ 0 n (y + c₁) ω) a b) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (rectAB a b).toSet
  have hG := measurable_xabFun hDc
  have hZ : Measurable (fun ω (i : ℕ × ℂ × Bool) => W (xabKer Q c₁ i) ω) :=
    measurable_pi_iff.2 fun i => hW.measurable _
  have hZ₂ : Measurable (fun ω (i : ℕ × ℂ × Bool) => V (xabKer Q c₁ i) ω) :=
    measurable_pi_iff.2 fun i => hV.measurable _
  rw [Measure.map_congr (ae_XAB_shift_eq_xabFun hW Q c₁ a b hDc hDd),
    Measure.map_congr (ae_XAB_shift_eq_xabFun hV Q c₁ a b hDc hDd)]
  calc P.map (fun ω => xabFun D (fun i => W (xabKer Q c₁ i) ω))
      = (P.map (fun ω (i : ℕ × ℂ × Bool) => W (xabKer Q c₁ i) ω)).map (xabFun D) :=
        (Measure.map_map hG hZ).symm
    _ = (P₂.map (fun ω (i : ℕ × ℂ × Bool) => V (xabKer Q c₁ i) ω)).map (xabFun D) := by
        rw [map_wn_eq hW hV (xabKer Q c₁)]
    _ = P₂.map (fun ω => xabFun D (fun i => V (xabKer Q c₁ i) ω)) := Measure.map_map hG hZ₂

/-- probabilities of `X_{a,b}`-events do not depend on the white noise -/
theorem measure_XAB_shift_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (Q : PsiParams) (c₁ : ℂ) (a b : ℝ)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | XAB (fun n y => phiMN W P 0 n (y + c₁) ω) (fun n y => psiMN Q W P 0 n (y + c₁) ω)
        a b ∈ S} =
      P₂ {ω | XAB (fun n y => phiMN V P₂ 0 n (y + c₁) ω)
        (fun n y => psiMN Q V P₂ 0 n (y + c₁) ω) a b ∈ S} := by
  have h := congrArg (fun μ : Measure ℝ≥0∞ => μ S) (map_XAB_shift_eq hW hV Q c₁ a b)
  rwa [Measure.map_apply_of_aemeasurable (aemeasurable_XAB_shift hW Q c₁ a b) hS,
    Measure.map_apply_of_aemeasurable (aemeasurable_XAB_shift hV Q c₁ a b) hS] at h

/-- integrals of functions of `X_{a,b}` do not depend on the white noise -/
theorem lintegral_XAB_shift_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (Q : PsiParams) (c₁ : ℂ) (a b : ℝ)
    {g : ℝ≥0∞ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
        (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b) ∂P =
      ∫⁻ ω, g (XAB (fun n y => phiMN V P₂ 0 n (y + c₁) ω)
        (fun n y => psiMN Q V P₂ 0 n (y + c₁) ω) a b) ∂P₂ := by
  rw [← lintegral_map' hg.aemeasurable (aemeasurable_XAB_shift hW Q c₁ a b),
    ← lintegral_map' hg.aemeasurable (aemeasurable_XAB_shift hV Q c₁ a b),
    map_XAB_shift_eq hW hV Q c₁ a b]

/-! ### The templates with their constants before `Ω` -/

/-- **DDDF Proposition 5 for `X_{a,b}`** (`dddf_prop5_XAB`) with the constants before the
probability space (ledger U1, Recipe B). -/
theorem dddf_prop5_XAB_W (Q : PsiParams) (a b : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ x : ℝ, 0 < x →
      P {ω | ENNReal.ofReal x ≤
          XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤
        ENNReal.ofReal (C * Real.exp (-(c * x ^ 2))) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  obtain ⟨C, c, hC, hc, h⟩ := dddf_prop5_XAB hW₀ Q a b
  refine ⟨C, c, hC, hc, fun {Ω} _ {P} {W} hW x hx => ?_⟩
  have e := measure_XAB_shift_eq hW hW₀ Q 0 a b (S := Ici (ENNReal.ofReal x)) measurableSet_Ici
  simp only [add_zero, mem_Ici] at e
  rw [e]
  exact h x hx

/-- the Prop 5 tail of `X_{a,b}`, uniformly over `a, b ≤ B` (`exists_tail_XAB_unif`), with the
constants before the probability space -/
theorem exists_tail_XAB_unif_W (Q : PsiParams) (B : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ a b : ℝ, a ≤ B → b ≤ B → ∀ η : ℝ, 0 < η →
      P {ω | ENNReal.ofReal (√(max 1 (Real.log (C / η)) / c)) <
        XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤
        ENNReal.ofReal η := by
  obtain ⟨C, c, hC, hc, htail⟩ := dddf_prop5_XAB_W Q B B
  refine ⟨C, c, hC, hc, fun {Ω} _ {P} {W} hW a b ha hb η hη => ?_⟩
  set M : ℝ := √(max 1 (Real.log (C / η)) / c)
  have hM0 : 0 < M := Real.sqrt_pos.mpr (by positivity)
  have hM2 : M ^ 2 = max 1 (Real.log (C / η)) / c := Real.sq_sqrt (by positivity)
  refine (measure_mono fun ω (hω : ENNReal.ofReal M < _) =>
    (show ENNReal.ofReal M ≤ _ from hω.le.trans (XAB_mono _ _ ha hb))).trans
    ((htail hW M hM0).trans (ENNReal.ofReal_le_ofReal ?_))
  have hlog : Real.log (C / η) ≤ c * M ^ 2 := by
    rw [hM2, mul_div_cancel₀ _ hc.ne']; exact le_max_right _ _
  have h1 : C * Real.exp (-(c * M ^ 2)) ≤ C * Real.exp (-Real.log (C / η)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
  have e : Real.exp (-Real.log (C / η)) = (C / η)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (div_pos hC hη)]
  rw [e] at h1
  calc C * Real.exp (-(c * M ^ 2)) ≤ C * (C / η)⁻¹ := h1
    _ = η := by field_simp

/-- exponential moments of `X_{a,b}` on `c₁ + [0,a] × [0,b]` (`T20C.expMoment_XAB_shift`) with
the bound before the probability space -/
theorem expMoment_XAB_shift_W (Q : PsiParams) (c₁ : ℂ) (a b : ℝ) {l : ℝ} (hl : 0 < l) :
    ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
      IsWhiteNoise P W →
      AEMeasurable (fun ω => (XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
        (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b).toReal) P ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
        (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b).toReal)) ∂P ≤ ENNReal.ofReal M := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  obtain ⟨-, M, hM⟩ := T20C.expMoment_XAB_shift hW₀ Q c₁ a b hl
  refine ⟨M, fun {Ω} _ {P} {W} hW => ⟨(T20C.expMoment_XAB_shift hW Q c₁ a b hl).1, ?_⟩⟩
  have hg : Measurable fun x : ℝ≥0∞ => ENNReal.ofReal (Real.exp (l * x.toReal)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul ENNReal.measurable_toReal))
  rw [lintegral_XAB_shift_eq hW hW₀ Q c₁ a b hg]
  exact hM

end Uniform
end GaussianLQG
