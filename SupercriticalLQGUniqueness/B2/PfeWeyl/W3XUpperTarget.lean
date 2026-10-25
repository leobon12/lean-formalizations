import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XMonotone

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

theorem exists_upperShiftFamily_weyl_close
    (D : LSCMetric) (hDforget : Continuous (euclidForget D))
    (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (q : ℂ × ℂ) (hfin : weylScale ξ f D q ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ i : ℕ, (∀ z, f z ≤ upperShiftFamily i z) ∧
      weylScale ξ (upperShiftFamily i) D q <
        weylScale ξ f D q + ENNReal.ofReal ε := by
  obtain ⟨i, hi, hloc⟩ := exists_upperShiftFamily_approximants f M hM
  let g : ℕ → C(ℂ, ℝ) := fun n => upperShiftFamily (i n)
  have hgloc : ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, ∀ z ∈ K, g n z ≤ f z + δ := hloc
  let e₀ : ℝ := (weylScale ξ f D q).toReal
  have he : weylScale ξ f D q = ENNReal.ofReal e₀ :=
    (ENNReal.ofReal_toReal hfin).symm
  have he0 : 0 ≤ e₀ := ENNReal.toReal_nonneg
  let F : ℝ → ℝ := fun t => Real.exp (ξ * t) * (e₀ + t)
  have hFc : Continuous F := by fun_prop
  have hF0 : F 0 = e₀ := by simp [F]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), F t < e₀ + ε :=
    hFc.continuousAt.eventually_lt continuousAt_const (by rw [hF0]; linarith)
  obtain ⟨t, htF, ht⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and
      self_mem_nhdsWithin).exists
  have htop : weylScale ξ f D (q.1, q.2) ≠ ⊤ := by simpa only [Prod.mk.eta] using hfin
  obtain ⟨n, hn⟩ := (eventually_weylScale_le_of_local_upper D hDforget ξ hξ f g
    hgloc htop ht ht).exists
  refine ⟨i n, hi n, ?_⟩
  have hres : weylScale ξ (upperShiftFamily (i n)) D q ≤
      ENNReal.ofReal (Real.exp (ξ * t)) *
        (weylScale ξ f D q + ENNReal.ofReal t) := by
    simpa only [g, Prod.mk.eta] using hn
  have hcast : ENNReal.ofReal (Real.exp (ξ * t)) *
      (weylScale ξ f D q + ENNReal.ofReal t) =
      ENNReal.ofReal (F t) := by
    rw [he, ← ENNReal.ofReal_add he0 ht.le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hcast] at hres
  rw [he, ← ENNReal.ofReal_add he0 hε.le]
  exact hres.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htF)

end SupercriticalLQGUniqueness.B2.PfeWeyl
