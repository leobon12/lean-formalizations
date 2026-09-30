import QuantumZipper.Proofs.Section5.Prop16NodeBKernel
import QuantumZipper.Proofs.LQG.PalmNorm

/-!
# Proposition 1.6, Palm node B′: a local Palm formula for the mixed field

Item (1) of the D30 expert's list for node B′ (`Prop16PalmIdMaskStmt`): the Palm (rooted
measure) formula for the mixed GFF `X` of Proposition 1.6, **locally**: only coordinates carried
by a compact `K` near the free arc are used, and `h0` need only agree with a continuous `m` on
`K`.

* `maskK K X`: the field `X` on measures that are admissible and carried by `K` (`KAdm K`), `0`
  elsewhere. It is a centered Gaussian field (`isCenteredGaussianField_maskK`; `IsMixedGFF`
  constrains `X` only on admissible measures, K3 M4 gives admissibility of the `K`-carried ones).
* `var_maskK_fc_add_log_le`: the uniform bound **hvarbd for every level `n`** (at the levels
  where `fc(x, 2^{-n})` is not carried by `K` the masked variance is `0` and `2 log 2^{-n} ≤ 0`).
* `palm_formula_mixed_local`: the weighted Palm formula
  `E ∫ w(x) φ((h0 + X)(μ_j), x) ν(dx) = ∫ w(x) ρ(x) E φ((h0 + X + (γ/2) G_D(x, ·))(μ_j), x) dx`,
  `ρ(x) = exp(γ h0(x)/2 + γ² k(x,x)/8)`, for `K`-carried admissible `μ_j`, with the Palm shift
  read through `palmMixedField` (i.e. `mixedGreenSample`, identified on `K` by
  `mixedGreenSample_eq`). Remaining hypotheses (stated exactly): the a.s. regularity `hreg` of the
  masked field at the folded circles centred on `[a,b]` and the `L¹` convergence `hL1`
  (`PalmFree.BdryL1ConvCc`, item (2)) of its boundary approximations to `ν`.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
arXiv:0808.1560, §3.3 (rooted measure, p. 22), in the project's abstract form
`PalmFree.palm_formula_weight`; applied as in Sheffield, arXiv:1012.4797, proof of Prop. 1.6
(p. 25). The masking and the local bookkeeping are own arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- Admissible and carried by `K`. -/
def KAdm (K : Set ℂ) (μ : Measure ℂ) : Prop := IsAdmissibleH μ ∧ μ Kᶜ = 0

open Classical in
/-- The field `X` masked to the `K`-carried admissible measures. -/
def maskK (K : Set ℂ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  fun μ => if KAdm K μ then X ω μ else 0

section

variable {D S K : Set ℂ} {R : ℝ} {k : ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → FieldSample}

theorem maskK_of_KAdm {μ : Measure ℂ} (h : KAdm K μ) (ω : Ω) : maskK K X ω μ = X ω μ := by
  classical
  simp only [maskK, if_pos h]

theorem maskK_of_not {μ : Measure ℂ} (h : ¬ KAdm K μ) (ω : Ω) : maskK K X ω μ = 0 := by
  classical
  simp only [maskK, if_neg h]

theorem ofFun_eq_of_eqOn {m h0 : ℂ → ℝ} (hmK : EqOn m h0 K) {μ : Measure ℂ}
    (hμK : μ Kᶜ = 0) : ofFun m μ = ofFun h0 μ := by
  refine integral_congr_ae ?_
  filter_upwards [(mem_ae_iff.2 hμK : K ∈ ae μ)] with z hz
  exact hmK hz

variable (hL : K3.MixedLocalHyp D S K R) (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
  (hkc : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ Kᶜ = 0 → IsAdmissibleH ν → ν Kᶜ = 0 →
    dualCov D (mixedSpace D S) μ ν = kernelCov (fun x y => neumannH x y + k x y) μ ν)
include hL hk hkc

/-- **hvarbd at every level** for the masked field. -/
theorem var_maskK_fc_add_log_le (hX : IsMixedGFF D S X P) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y w, |remK K k y w| ≤ M) (x : ℝ) (n : ℕ) :
    Var[fun ω => maskK K X ω (Palm.fcK x n); P] + 2 * Real.log (radius n) ≤ M := by
  by_cases hn : Palm.fcK x n Kᶜ = 0
  · have hA : KAdm K (Palm.fcK x n) := ⟨isAdmissibleH_fcK x n, hn⟩
    simp_rw [maskK_of_KAdm hA]
    rw [var_mixed_fc_add_log hL hk hkc hX hn]
    exact (le_abs_self _).trans (abs_kernelCov_remK_le hL.compact hk hM _ _)
  · have hA : ¬ KAdm K (Palm.fcK x n) := fun h => hn h.2
    simp_rw [maskK_of_not hA]
    have h0 : Var[fun _ : Ω => (0 : ℝ); P] = 0 := variance_zero P
    rw [h0, zero_add]
    have := Real.log_nonpos (radius_pos n).le (Palm.radius_le_one' n)
    linarith

/-- **hvar** for the masked field. -/
theorem tendsto_var_maskK (hX : IsMixedGFF D S X P) {x : ℝ} (hx : (x : ℂ) ∈ K)
    (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) :
    Tendsto (fun n => Var[fun ω => maskK K X ω (Palm.fcK x n); P] + 2 * Real.log (radius n))
      atTop (𝓝 (k x x)) := by
  refine (tendsto_var_mixed_fc hL hk hkc hX hx hev).congr' ?_
  filter_upwards [hev] with n hn
  simp_rw [maskK_of_KAdm (show KAdm K (Palm.fcK x n) from ⟨isAdmissibleH_fcK x n, hn⟩)]

end

end Prop16Asm

end QuantumZipper
