import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XUpperTarget
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3WeylMetric

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

theorem weyl_all_bounded_of_countable_upper
    (ξ : ℝ) (hξ : 0 ≤ ξ)
    (a : ℕ → Set.Ioi (0 : ℝ)) (φ : ℕ → C(ℂ, ℝ)) (D : LSCMetric)
    (hG : Tendsto (fun n => normalizedLFPPMetric ξ (a n) (φ n)) atTop (𝓝 D))
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ≠ 0) (hε0 : Tendsto ε atTop (𝓝 0))
    (hCount : ∀ j : ℕ, ∃ E : LSCMetric,
      (∀ p, E p = weylScale ξ (upperShiftFamily j) D p) ∧
      Tendsto (fun n => normalizedLFPPMetric ξ (a n)
        (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n)
          (upperShiftFamily j) (upperShiftBound j)
          (upperShiftFamily_bound j))) atTop (𝓝 E)) :
    ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M),
      ∃ E : LSCMetric, (∀ p, E p = weylScale ξ f D p) ∧
        Tendsto (fun n => normalizedLFPPMetric ξ (a n)
          (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM))
          atTop (𝓝 E) := by
  intro f M hM
  let G : ℕ → LSCMetric := fun n => normalizedLFPPMetric ξ (a n) (φ n)
  let fn : ℕ → C(ℂ, ℝ) := fun n =>
    LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM
  let W : ℕ → LSCMetric := fun n => normalizedLFPPMetric ξ (a n) (φ n + fn n)
  have hfn : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, ∀ z ∈ K, |fn n z - f z| < η :=
    mollCont_fixed_tendsto_compact hε hε0 f M hM
  have hfnM : ∀ n z, |fn n z| ≤ M := fun n z =>
    abs_mollCont_le (hε n) f M hM z
  have hforget : ∀ n, Continuous (euclidForget (G n)) := fun n =>
    PfeAxioms.continuous_euclidForget_normalizedLFPPMetric ξ (a n) (φ n)
  have hlow : ∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
      weylScale ξ f D q ≤ liminf (fun n => W n (p n)) atTop := by
    intro p q hp
    simp only [W, fn, normalizedLFPPMetric_add_eq_weylScale]
    exact weyl_gamma_liminf hG ξ hξ f fn hfn M hfnM hforget hDlen hDforget
      hacross hp
  obtain ⟨E, hE⟩ := exists_weyl_lscMetric hDlen hDforget hacross ξ hξ f M hM
  refine ⟨E, hE, LSCMetric.tendsto_iff.2 ⟨?_, ?_⟩⟩
  · intro p q hp
    rw [hE]
    exact hlow p q hp
  · intro q
    by_cases htop : weylScale ξ f D q = ⊤
    · refine ⟨fun _ => q, tendsto_const_nhds, ?_⟩
      rw [hE, htop]
      have hl := hlow (fun _ => q) q tendsto_const_nhds
      rw [htop] at hl
      exact tendsto_of_le_liminf_of_limsup_le
        (by simpa only [W, fn] using hl) le_top
    · let e : ℝ≥0∞ := weylScale ξ f D q
      have happrox : ∀ η : ℝ, 0 < η →
          ∃ p : ℕ → ℂ × ℂ, Tendsto p atTop (𝓝 q) ∧
            ∀ᶠ n in atTop, W n (p n) ≤ e + ENNReal.ofReal η := by
        intro η hη
        obtain ⟨j, hdom, hclose⟩ :=
          exists_upperShiftFamily_weyl_close D hDforget ξ hξ f M hM q htop η hη
        obtain ⟨Ej, hEj, hEjconv⟩ := hCount j
        obtain ⟨p, hp, hpEj⟩ := (LSCMetric.tendsto_iff.1 hEjconv).2 q
        have hlt : Ej q < e + ENNReal.ofReal η := by
          rw [hEj]
          exact hclose
        have hev : ∀ᶠ n in atTop,
            normalizedLFPPMetric ξ (a n)
              (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n)
                (upperShiftFamily j) (upperShiftBound j)
                (upperShiftFamily_bound j)) (p n) <
              e + ENNReal.ofReal η :=
          hpEj.eventually_lt tendsto_const_nhds hlt
        refine ⟨p, hp, ?_⟩
        filter_upwards [hev] with n hn
        exact (normalizedLFPPMetric_shift_mono_x hξ (a n) (φ n)
          (hε n) hM (upperShiftFamily_bound j) hdom (p n)).trans hn.le
      obtain ⟨p, hp, hpF⟩ := exists_diagonal_upper (fun n p => W n p) q e happrox
      refine ⟨p, hp, ?_⟩
      rw [hE]
      refine tendsto_of_le_liminf_of_limsup_le (hlow p q hp) ?_
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      have h := hpF η (by exact_mod_cast hη)
      simp only [ENNReal.ofReal_coe_nnreal] at h
      exact limsup_le_of_le (by isBoundedDefault) h

end SupercriticalLQGUniqueness.B2.PfeWeyl
