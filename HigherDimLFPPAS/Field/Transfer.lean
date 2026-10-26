import HigherDimLFPPAS.Field.Prelim

/-!
# Transfer of Lemma 2.3(ii)–(iii) to the localized field

This is the deterministic implication P7.  It applies to the actual pathwise fields by taking `f ε x` to be
`convMollify κ ε (h ω) x` and `g ε x` to be `locField κ ε (h ω) x`; its closeness premise is the pathwise conclusion
of Lemma 2.3(i).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric

namespace HigherDimLFPPAS.Field

/-- If two fields converge uniformly on a fixed ball as `ε ↓ 0`, then the logarithmic bound and shrinking-window
oscillation conclusions of Lemma 2.3 transfer from the first field to the second. -/
theorem transfer_lemma23_ii_iii_F1 {d : ℕ} {R : ℝ} (_hR : 0 < R)
    (f g : ℝ → Rd d → ℝ)
    (hclose : ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ x ∈ closedBall (0 : Rd d) R,
        |g ε x - f ε x| ≤ η)
    (hii : ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ x ∈ closedBall (0 : Rd d) R,
        |f ε x| ≤ (Real.sqrt (2 * (d : ℝ)) + η) * Real.log ε⁻¹)
    (hiii : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ ε : ℝ, ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)) →
        ∀ δ : ℝ, δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)) →
        ∀ x ∈ closedBall (0 : Rd d) R, |f ε x - f δ x| ≤ η) :
    (∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ x ∈ closedBall (0 : Rd d) R,
        |g ε x| ≤ (Real.sqrt (2 * (d : ℝ)) + η) * Real.log ε⁻¹) ∧
    (∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ ε : ℝ, ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)) →
        ∀ δ : ℝ, δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)) →
        ∀ x ∈ closedBall (0 : Rd d) R, |g ε x - g δ x| ≤ η) := by
  constructor
  · intro η hη
    obtain ⟨εc, hεc, hcl⟩ := hclose (η / 2) (by linarith)
    obtain ⟨εf, hεf, hf⟩ := hii (η / 2) (by linarith)
    let ε₀ := min εc (min εf (Real.exp (-1)))
    have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε hε hεbound x hx
    have hεc' : ε ≤ εc := hεbound.trans (min_le_left _ _)
    have hεf' : ε ≤ εf := hεbound.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hexp : ε ≤ Real.exp (-1) := hεbound.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hlogε : Real.log ε ≤ -1 := by
      calc Real.log ε ≤ Real.log (Real.exp (-1)) := Real.log_le_log hε hexp
        _ = -1 := by rw [Real.log_exp]
    have hlog : 1 ≤ Real.log ε⁻¹ := by
      rw [Real.log_inv]
      linarith
    have htri : |g ε x| ≤ |f ε x| + |g ε x - f ε x| := by
      calc |g ε x| = |f ε x + (g ε x - f ε x)| := by congr 1; ring
        _ ≤ |f ε x| + |g ε x - f ε x| := abs_add_le _ _
    have hfc := hf ε hε hεf' x hx
    have hcc := hcl ε hε hεc' x hx
    calc |g ε x|
        ≤ |f ε x| + |g ε x - f ε x| := htri
      _ ≤ (Real.sqrt (2 * (d : ℝ)) + η / 2) * Real.log ε⁻¹ + η / 2 :=
          add_le_add hfc hcc
      _ ≤ (Real.sqrt (2 * (d : ℝ)) + η) * Real.log ε⁻¹ := by
          nlinarith [Real.sqrt_nonneg (2 * (d : ℝ)), mul_nonneg (by linarith : 0 ≤ η / 2)
            (by linarith : 0 ≤ Real.log ε⁻¹ - 1)]
  · intro a ha η hη
    obtain ⟨εc, hεc, hcl⟩ := hclose (η / 3) (by linarith)
    obtain ⟨Nf, hf⟩ := hiii a ha (η / 3) (by linarith)
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-a) < εc :=
      hpow.eventually (Iio_mem_nhds hεc)
    obtain ⟨Np, hNp⟩ := eventually_atTop.1 hev
    let N := max 1 (max Nf Np)
    refine ⟨N, ?_⟩
    intro n hn ε hεI δ hδI x hx
    have hn1 : 0 < n := by dsimp [N] at hn; omega
    have hnNf : Nf ≤ n := by dsimp [N] at hn; omega
    have hnNp : Np ≤ n := by dsimp [N] at hn; omega
    have hupper : (n : ℝ) ^ (-a) < εc := hNp n hnNp
    have hlowerPos : 0 < ((n : ℝ) + 1) ^ (-a) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hεpos : 0 < ε := hlowerPos.trans_le hεI.1
    have hδpos : 0 < δ := hlowerPos.trans_le hδI.1
    have hεsmall : ε ≤ εc := hεI.2.trans hupper.le
    have hδsmall : δ ≤ εc := hδI.2.trans hupper.le
    have hεclose := hcl ε hεpos hεsmall x hx
    have hδclose := hcl δ hδpos hδsmall x hx
    have hδclose' : |f δ x - g δ x| ≤ η / 3 := by
      simpa only [abs_sub_comm] using hδclose
    have hfosc := hf n hnNf ε hεI δ hδI x hx
    have heq : g ε x - g δ x = (g ε x - f ε x) + (f ε x - f δ x) +
        (f δ x - g δ x) := by ring
    rw [heq]
    calc |(g ε x - f ε x) + (f ε x - f δ x) + (f δ x - g δ x)|
        ≤ |g ε x - f ε x| + |f ε x - f δ x| + |f δ x - g δ x| := by
          calc |(g ε x - f ε x) + (f ε x - f δ x) + (f δ x - g δ x)|
              ≤ |(g ε x - f ε x) + (f ε x - f δ x)| + |f δ x - g δ x| := abs_add_le _ _
            _ ≤ |g ε x - f ε x| + |f ε x - f δ x| + |f δ x - g δ x| := by
                gcongr
                exact abs_add_le _ _
      _ ≤ η := by linarith

end HigherDimLFPPAS.Field
