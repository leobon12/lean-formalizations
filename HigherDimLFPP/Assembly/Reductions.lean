import HigherDimLFPP.Var.Theorem11
import HigherDimLFPP.Exist.Exponent
import HigherDimLFPP.Upper.UpperAssembly
import HigherDimLFPP.Lower.LowerAssembly

/-!
# Assembly of Theorem 1.1 from its four parts

`theorem11_of_inputs` derives the statement of the frozen `theorem11`
(`HigherDimLFPP/Frozen/MainTheorem.lean`) from

* the variational part `theorem11_variational` (§2; `Var/Theorem11.lean`);
* the existence of the exponent `theorem11_exponent_exists` (DGZ Prop. 1.1 and App. A.1;
  `Exist/Exponent.lean`);
* the existence-free upper comparison `Upper.upperComparison_limsup` (§4), which is proved from the
  good-record mean bound `Upper.GoodRecordMeanBound` (Lemma 4.3);
* the existence-free lower comparison `Lower.lowerComparison_liminf` (§5), which is proved from
  `Lower.Lemma53Holds` (Lemma 5.3).

The two remaining inputs are explicit hypotheses here. The provider `Assembly/Main.lean` discharges them
with the proofs of Lemma 4.3 and Lemma 5.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- Squeeze: if `k - η ≤ f ≤ k + η` eventually for every `η > 0`, then `f → k`. -/
theorem tendsto_of_eventually_le_add_sub {f : ℝ → ℝ} {l : Filter ℝ} {k : ℝ}
    (h₁ : ∀ η > 0, ∀ᶠ ζ in l, k - η ≤ f ζ) (h₂ : ∀ η > 0, ∀ᶠ ζ in l, f ζ ≤ k + η) :
    Tendsto f l (𝓝 k) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [h₁ ((k - a) / 2) (by linarith)] with ζ hζ
    linarith
  · filter_upwards [h₂ ((b - k) / 2) (by linarith)] with ζ hζ
    linarith

/-- Theorem 1.1 (the statement of the frozen `theorem11`), given Lemma 4.3 and Lemma 5.3. -/
theorem theorem11_of_inputs
    (hU : ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ → Upper.GoodRecordMeanBound d κ)
    (hL : ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ → Lower.Lemma53Holds d κ) :
    ∀ d : ℕ, 2 ≤ d →
    (∀ n : ℕ, A n d ≠ ⊥ ∧ A n d ≠ ⊤) ∧
    (∀ n r : ℕ, A (n + r) d ≤ A n d + A r d) ∧
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) ∧
    0 < kappa d ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∃ lam : ℝ, IsLFPPExponent H P ζ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) →
        Tendsto (fun ζ => lam ζ / ζ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa d)) := by
  intro d hd
  obtain ⟨h1, h2, h3, h4⟩ := theorem11_variational d hd
  refine ⟨h1, h2, h3, h4, fun κ hκ Ω _ P W hW H hH => ⟨?_, fun lam hlam => ?_⟩⟩
  · exact theorem11_exponent_exists d hd κ hκ Ω P W hW H hH
  · exact tendsto_of_eventually_le_add_sub
      (fun η hη => Lower.lowerComparison_liminf hd hκ (hL d hd κ hκ) hW hH hlam hη)
      (fun η hη => Upper.upperComparison_limsup hd (hU d hd) hκ hW hH hlam hη)

end HigherDimLFPP
