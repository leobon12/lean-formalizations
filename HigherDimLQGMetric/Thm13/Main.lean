import HigherDimLQGMetric.Thm13.TightContinuous
import HigherDimLQGMetric.Thm13.LocalGood
import HigherDimLQGMetric.Thm13.L6cInputs
import HigherDimLQGMetric.Thm13.AssemblyBridge

/-! Theorem 1.3 assembly from the B3 interfaces. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_thm13_of
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (hL6f : ∀ d ξ κ, L6f_tightScales d ξ κ)
    (hL7f : ∀ d ξ κ, L7f_determined d ξ κ) :
    ∀ d ξ κ, L8_thm13 d ξ κ := by
  intro d ξ κ hB2 hMarkov hShell εs hεs hεt
  obtain ⟨Q, hQ, hAdapter⟩ := hB2
  have hd : 2 ≤ d := hQ.dim
  have hκ : HigherDimLFPP.IsLFPPKernel κ := hQ.kernel
  have hB2' : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q :=
    ⟨Q, hQ, hAdapter⟩
  obtain ⟨φ, hφ, hN⟩ := l8_exists_normalized_good'
    hL6a l8_length_limit_input hL7f l8_lemma36_trunc_input
    hd ξ κ hκ hB2' hMarkov hShell εs hεs hεt
  let ε' : ℕ → ℝ := εs ∘ φ
  have hε' (n : ℕ) : 0 < ε' n := hεs (φ n)
  have hε't : Tendsto ε' atTop (𝓝 0) :=
    hεt.comp hφ.tendsto_atTop
  obtain ⟨c, hc, hcan⟩ := l8_canonical_scales_of_good
    hL6f hd κ hκ ξ hB2' ε' hε' hε't hN
  let D : DistRd d → ContMetric d :=
    l8_patch hd hκ ξ ε' hε'
  refine ⟨φ, D, c, hφ, ?_, ?_⟩
  · refine {
      measurable := l8_measurable_patch hd hκ ξ ε' hε'
      length := ?_
      locality := ?_
      weyl := ?_
      translation := ?_
      c_pos := hc
      tight := ?_
      tight_bdd := ?_ }
    · intro Ω _ P _ h hh
      exact (l8_length_weyl_of_normalized hd ξ D
        (l8_normalizedWeyl_of_good hd hκ ξ ε' hε' hN)
        P h hh).1
    · intro Ω _ P _ h hh U
      exact l8_locality_of_normalized_good l8_lemma36_trunc_input
        hd κ hκ ξ ε' hε' hε't hN P h hh U
    · intro Ω _ P _ h hh
      exact (l8_length_weyl_of_normalized hd ξ D
        (l8_normalizedWeyl_of_good hd hκ ξ ε' hε' hN)
        P h hh).2
    · intro Ω _ P _ h hh z
      exact l8_translation_of_normalized_good
        l8_translate_prelimit_input hd κ hκ ξ ε' hε'
        hN P h hh z
    · intro Ω _ P _ h hh R hR
      exact l8_tight_cont_of_normalized hd ξ hQ.xi_pos.le D
        (l8_measurable_patch hd hκ ξ ε' hε')
        (l8_normalizedWeyl_of_good hd hκ ξ ε' hε' hN)
        c hc hcan P h hh R hR
    · intro Ω _ P _ h hh
      exact l8_tight_bdd_of_normalized hd ξ hQ.xi_pos.le D
        (l8_measurable_patch hd hκ ξ ε' hε')
        (l8_normalizedWeyl_of_good hd hκ ξ ε' hε' hN)
        c hc hcan P h hh
  · intro Ω _ P _ h hh
    exact l8_prob_bdd_raw_of_normalized_good
      l8_lemma36_full_input hd κ hκ ξ ε' hε' hε't hN
      P h hh

theorem b3Goal_of
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (hL6f : ∀ d ξ κ, L6f_tightScales d ξ κ)
    (hL7f : ∀ d ξ κ, L7f_determined d ξ κ) : B3Goal :=
  b3Goal_of_universal (l8_thm13_of hL6a hL6f hL7f)

end HigherDimLQGMetric
