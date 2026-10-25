import SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedApprox

 

















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 
lemma crossLenIn_eq_iInf_lfppDOn (ξ : ℝ) (f : ℂ → ℝ) (U A B : Set ℂ) :
    DDDF.crossLenIn ξ f U A B = ⨅ z ∈ A, ⨅ w ∈ B, lfppDOn ξ f U z w := rfl

 

theorem lfppDOn_compare_of_abs_sub_le {ξ : ℝ} {φ φ' : ℂ → ℝ} {S : Set ℂ} {δ : ℝ}
    (hδ : ∀ x ∈ S, |φ x - φ' x| ≤ δ) (z w : ℂ) :
    lfppDOn ξ φ' S z w ≤ ENNReal.ofReal (Real.exp (|ξ| * δ)) * lfppDOn ξ φ S z w ∧
      lfppDOn ξ φ S z w ≤ ENNReal.ofReal (Real.exp (|ξ| * δ)) * lfppDOn ξ φ' S z w :=
  ⟨lfppDOn_le_of_abs_sub_le (fun x hx => by rw [abs_sub_comm]; exact hδ x hx) z w,
    lfppDOn_le_of_abs_sub_le hδ z w⟩

 
theorem crossLenIn_le_of_abs_sub_le {ξ : ℝ} {φ φ' : ℂ → ℝ} {U : Set ℂ} {δ : ℝ}
    (hδ : ∀ x ∈ U, |φ' x - φ x| ≤ δ) (A B : Set ℂ) :
    DDDF.crossLenIn ξ φ' U A B ≤
      ENNReal.ofReal (Real.exp (|ξ| * δ)) * DDDF.crossLenIn ξ φ U A B := by
  rw [crossLenIn_eq_iInf_lfppDOn, crossLenIn_eq_iInf_lfppDOn,
    ENNReal.mul_iInf_of_ne (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top]
  refine iInf_mono fun z => ?_
  rw [ENNReal.mul_iInf_of_ne (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top]
  refine iInf_mono fun _ => ?_
  rw [ENNReal.mul_iInf_of_ne (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top]
  refine iInf_mono fun w => ?_
  rw [ENNReal.mul_iInf_of_ne (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top]
  exact iInf_mono fun _ => lfppDOn_le_of_abs_sub_le hδ z w

 
lemma exp_mul_log_div_le (ξ : ℝ) {c : ℝ} (hc : 1 < c) :
    Real.exp (|ξ| * (Real.log c / (|ξ| + 1))) ≤ c := by
  have hlc : 0 < Real.log c := Real.log_pos hc
  have : |ξ| * (Real.log c / (|ξ| + 1)) ≤ Real.log c := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg ξ]
  calc Real.exp (|ξ| * (Real.log c / (|ξ| + 1))) ≤ Real.exp (Real.log c) := Real.exp_le_exp.2 this
    _ = c := Real.exp_log (by linarith)

 






theorem lem_localized_approx.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {q : ℝ} (hq : 0 < q) {U : Set ℂ}
    (hU : Bornology.IsBounded U) (ξ : ℝ) :
    (∀ ω, ContinuousOn (fun p : ℝ × ℂ =>
        if hp : p.1 ∈ Ioo (0 : ℝ) 1 then plMollify q p.1 hp (g ω) p.2 else 0)
        (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
    ∀ᵐ ω ∂P,
      (∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1, ∀ z ∈ closure U,
        (∃ L : ℝ, Tendsto (fun n : ℕ => g ω (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
        |heatMollify ε (g ω) z - plMollify q ε hε (g ω) z| ≤ δ) ∧
      ∀ c : ℝ, 1 < c → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
        (∀ z w : ℂ,
          plLocOn ξ q ε hε (g ω) U z w ≤
              ENNReal.ofReal c * lfppDOn ξ (heatMollify ε (g ω)) U z w ∧
            lfppDOn ξ (heatMollify ε (g ω)) U z w ≤
              ENNReal.ofReal c * plLocOn ξ q ε hε (g ω) U z w) ∧
        ∀ A B : Set ℂ,
          DDDF.crossLenIn ξ (plMollify q ε hε (g ω)) U A B ≤
              ENNReal.ofReal c * DDDF.crossLenIn ξ (heatMollify ε (g ω)) U A B ∧
            DDDF.crossLenIn ξ (heatMollify ε (g ω)) U A B ≤
              ENNReal.ofReal c * DDDF.crossLenIn ξ (plMollify q ε hε (g ω)) U A B := by
  refine ⟨fun ω => plMollify_continuousOn q (g ω), ?_⟩
  filter_upwards [lem_localized_approx_sup hg hq hU] with ω hω
  refine ⟨hω, fun c hc => ?_⟩
  set δ : ℝ := Real.log c / (|ξ| + 1)
  have hδ : 0 < δ := div_pos (Real.log_pos hc) (by positivity)
  have hm : ENNReal.ofReal (Real.exp (|ξ| * δ)) ≤ ENNReal.ofReal c :=
    ENNReal.ofReal_le_ofReal (exp_mul_log_div_le ξ hc)
  filter_upwards [hω δ hδ] with ε hε0 hε
  have hU' : ∀ x ∈ U, |heatMollify ε (g ω) x - plMollify q ε hε (g ω) x| ≤ δ :=
    fun x hx => (hε0 hε x (subset_closure hx)).2
  have hU'' : ∀ x ∈ U, |plMollify q ε hε (g ω) x - heatMollify ε (g ω) x| ≤ δ :=
    fun x hx => by rw [abs_sub_comm]; exact hU' x hx
  refine ⟨fun z w => ?_, fun A B => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := lfppDOn_compare_of_abs_sub_le (ξ := ξ) hU' z w
    exact ⟨h1.trans (mul_le_mul_left hm _), h2.trans (mul_le_mul_left hm _)⟩
  · exact (crossLenIn_le_of_abs_sub_le hU'' A B).trans (mul_le_mul_left hm _)
  · exact (crossLenIn_le_of_abs_sub_le hU' A B).trans (mul_le_mul_left hm _)

end SupercriticalLQGUniqueness.B2.Polylog
