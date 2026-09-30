import QuantumZipper.Proofs.Zipper.UnifAWDet

/-!
# UNIF-AW: `AnchorWindowStmt` from the time-continuous transported limits

Task UNIF-AW (decision D26). `RegUnif.AnchorWindowStmt` (AW) is reduced to

* `AnchorConvStmt` (**AC**, the analytic input, open): for a rational anchor `q`, a rational
  window `(u,v)` of the fully unzipped picture live at time `q`, and every continuous test
  function `f` with compact support in `(u,v)`, a.s. the integrals of `f ∘ F_s⁻¹`
  (`F_s = realRevMap V (T − s)`, `awTest`) against the approximations `bdryApprox γ h⁰_s k`
  converge as `k → ∞` for **every** `s ∈ [q,T]`, to a limit that is continuous in `s`.
  This is the conformal coordinate-change rule of the boundary measure for the field `h⁰_q` and
  the continuous family of independent maps given by the driver after `q` (`b2_markov`),
  uniformly in the parameter: Sheffield–Wang, *Field-measure correspondence in Liouville quantum
  gravity almost surely commutes with all conformal maps simultaneously*, arXiv:1605.06171
  (Trans. AMS 2020), Thm 4.3 (boundary measures, all conformal maps at once; proof of Thm 1.4,
  §3.3, uniform convergence (3.5)). Note: Sheffield–Wang regularize `h ∘ φ` by mollifiers;
  AC uses the semicircle averages of `bdryApprox` (the project's definition of `ν`).
* `UnifGlobalStmt` (UG, agent UNIF-UG), used only at rational times and at `T`.

Main result: **`anchorWindowStmt_of_conv`**: AC + UG ⇒ AW. At rational times `r ∈ [q,T]` the
limits are identified by the fixed-time window identities (`ae_windows_rat`) and a π-system
argument (`restrict_eq_map_symm`); by continuity in `s` they are the same at every `s`
(`eq_const_of_rat`), which identifies the local vague limit on `F_s(u,v)` as the image of
`ν_{h⁰_T}|_{(u,v)}` (`det_anchor`). This reduction is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

variable {Ω : Type} [MeasurableSpace Ω]

/-- **AC (anchored convergence, uniform in time)**: see the module docstring. -/
def AnchorConvStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ q : ℚ, (0 : ℝ) < q → (q : ℝ) ≤ T → ∀ u v : ℚ, ∀ᵐ ω ∂P,
    zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∃ L : ℝ → ℝ, ContinuousOn L (Icc (q : ℝ) T) ∧ ∀ s ∈ Icc (q : ℝ) T,
        Tendsto (fun k => ∫ x, awTest (realRevMap (Vr κ T B ω) (T - s)) u v f x
          ∂bdryApprox (Real.sqrt κ) (h0f κ s B X ω) k) atTop (𝓝 (L s))

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- The transported test integral `∫ (f ∘ F_s⁻¹) d(bdryApprox γ h⁰_s k)` of AC. -/
def awInt (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (u v : ℝ) (f : ℝ → ℝ)
    (s : ℝ) (k : ℕ) : ℝ :=
  ∫ x, awTest (realRevMap (Vr κ T B ω) (T - s)) u v f x ∂bdryApprox (Real.sqrt κ) (h0f κ s B X ω) k

/-- **AC-cont** (soft half of AC, open): at each fixed scale `k`, the transported test integral
is continuous in `s ∈ [q,T]` (expected from the joint continuous modification of the unzipped
circle averages, `RegUnif.jointModStmt_holds`, and the joint continuity of the reverse flow). -/
def AnchorApproxContStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ q : ℚ, (0 : ℝ) < q → (q : ℝ) ≤ T → ∀ u v : ℚ, ∀ᵐ ω ∂P,
    zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∀ k : ℕ, ContinuousOn (fun s => awInt κ T B X ω u v f s k) (Icc (q : ℝ) T)

/-- **AC-unif** (analytic half of AC, open): the transported test integrals are uniformly Cauchy
in `s ∈ [q,T]` as `k → ∞` (Sheffield–Wang, arXiv:1605.06171, uniform convergence (3.5) in the
proof of Thm 1.4 and its boundary analogue Thm 4.3, for the one-parameter family `F_s`). -/
def AnchorUnifCauchyStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ q : ℚ, (0 : ℝ) < q → (q : ℝ) ≤ T → ∀ u v : ℚ, ∀ᵐ ω ∂P,
    zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      UniformCauchySeqOn (fun k s => awInt κ T B X ω u v f s k) atTop (Icc (q : ℝ) T)

omit [IsProbabilityMeasure P] in
/-- **AC from AC-cont and AC-unif** (uniform limit of continuous functions). -/
theorem anchorConvStmt_of_unif (hA : AnchorApproxContStmt κ T P B X)
    (hU : AnchorUnifCauchyStmt κ T P B X) : AnchorConvStmt κ T P B X := by
  intro q hq hqT u v
  filter_upwards [hA q hq hqT u v, hU q hq hqT u v] with ω hA' hU' hu huv hv f hf hfc hfs
  have hUf := hU' hu huv hv f hf hfc hfs
  have hlim : ∀ s ∈ Icc (q : ℝ) T, Tendsto (fun k => awInt κ T B X ω u v f s k) atTop
      (𝓝 (limUnder atTop fun k => awInt κ T B X ω u v f s k)) := fun s hs =>
    (hUf.cauchySeq hs).tendsto_limUnder
  refine ⟨fun s => limUnder atTop fun k => awInt κ T B X ω u v f s k, ?_, hlim⟩
  exact (hUf.tendstoUniformlyOn_of_tendsto hlim).continuousOn
    (Frequently.of_forall fun k => hA' hu huv hv f hf hfc hfs k)

end RegUnif
end QuantumZipper
