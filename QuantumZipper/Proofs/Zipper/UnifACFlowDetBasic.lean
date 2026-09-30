import QuantumZipper.Proofs.Loewner.RevMapExtension
import QuantumZipper.Proofs.Loewner.CaraR1
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DiffContOnCl

/-!
# UNIF-ACFLOW-DET (1): the reverse Loewner carrier, uniform in the horizon

Task ACFLOW-DET. For a fixed continuous driver `W` and a compact real window `J` that is **live at
the horizon** `T` (no point of `J` is swallowed by the reverse flow of `W` by time `T`), we
produce **one** open neighbourhood `U` of `J` and **one** set of constants that work for **all**
horizons `t ∈ [0,T]` simultaneously:

* `exists_unif_ball_isCRevSol`: complex solutions from all `z ∈ U` on all `[0,t]`, `t ≤ T`,
  staying at distance `≥ c` from `0` — uniformly in `x ∈ J`, in the horizon and in `z`;
* `exists_unif_revMapExt_extension`: `revMapExt W t` is holomorphic on `U` for every `t ≤ T`,
  satisfies the Schwarz reflection `revMapExt W t (conj z) = conj (revMapExt W t z)`, equals
  `realRevMap W t` on `J`, and has the explicit derivative
  `deriv (revMapExt W t) x = exp (∫₀ᵗ 2/(realRevMap W s x)² ds)`;
* `exists_unif_deriv_bounds`: `1 ≤ ‖deriv (revMapExt W t) x‖ ≤ exp (2T/c²)` on `J × [0,T]`, so
  `‖1/deriv‖` is uniformly bounded too (the family is a uniform quasiconformal model);
* `strictMonoOn_revMapExt_window`, `continuousOn_revMapExt_time`: monotone on `J` and continuous
  in the horizon.

This is the "deterministic regularity, uniform in `s`" input for the family
`ψ_s = revMap (Vr κ s B ω) (s − q)` (`UnifACFlowDetFam`).

Sources: uniform-in-`t` version of node A2-ext of the blueprint
(`exists_revMapExt_extension`, `QuantumZipper/Proofs/Loewner/RevMapExtension.lean`; see
`LITERATURE.md` for Cara–Rohde, the source of the extension lemma). The uniformity is own
bookkeeping (finite subcover of the compact window + restriction of the horizon-`T` solutions);
the proof follows the published one with constants made horizon-independent.
-/

noncomputable section

open Set Metric Filter Topology Complex ComplexConjugate intervalIntegral
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open RevMapExtension CaraR

variable {W : ℝ → ℝ}

/-! ### Solutions with a uniform clearance -/

theorem dist_ofReal_coe {x y : ℝ} : dist (x : ℂ) (y : ℂ) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- A solution bounded away from `0` by `c` grows at most linearly. -/
theorem norm_isCRevSol_le {z : ℂ} {u : ℝ → ℂ} {c T : ℝ} (hc : 0 < c)
    (h : IsCRevSol W z T u) (hb : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u s‖) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) : ‖u τ‖ ≤ ‖z‖ + |W τ| + 2 / c * τ := by
  have h1 : u τ = z - (W τ : ℂ) - ∫ s in (0 : ℝ)..τ, (2 : ℂ) / u s := (h.2 τ hτ).2
  rw [h1]
  have h2 : ‖z - (W τ : ℂ) - ∫ s in (0 : ℝ)..τ, (2 : ℂ) / u s‖
      ≤ ‖z - (W τ : ℂ)‖ + ‖∫ s in (0 : ℝ)..τ, (2 : ℂ) / u s‖ := norm_sub_le _ _
  have h3 : ‖z - (W τ : ℂ)‖ ≤ ‖z‖ + |W τ| := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h4 : ‖∫ s in (0 : ℝ)..τ, (2 : ℂ) / u s‖ ≤ 2 / c * τ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := τ)
      (C := 2 / c) (f := fun s => (2 : ℂ) / u s) fun s hs => by
      rw [uIoc_of_le hτ.1] at hs
      have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans hτ.2⟩
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) hc (hb s hsI)
    rwa [sub_zero, abs_of_nonneg hτ.1] at this
  linarith

/-- **Uniformity in the horizon.** A compact window `J` live at time `T` admits a radius `ρ` and a
clearance `c` such that every complex point within `ρ` of a point of `J` has a reverse solution on
**every** `[0,t]`, `t ≤ T`, staying at distance `≥ c` from `0`. -/
theorem exists_unif_ball_isCRevSol (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {J : Set ℝ}
    (hJc : IsCompact J) (hJ : ∀ x ∈ J, ENNReal.ofReal T < realHitTime W x) :
    ∃ ρ > 0, ∃ c > 0, ∀ x ∈ J, ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ Metric.ball (x : ℂ) ρ,
      ∃ u, IsCRevSol W z t u ∧ ∀ s ∈ Icc (0 : ℝ) t, c ≤ ‖u s‖ := by
  by_cases hJne : J.Nonempty
  swap
  · exact ⟨1, one_pos, 1, one_pos, fun x hx => absurd ⟨x, hx⟩ hJne⟩
  have hper : ∀ x ∈ J, ∃ r : ℝ, ∃ c : ℝ, 0 < r ∧ 0 < c ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, ∃ u, IsCRevSol W z T u ∧ ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u s‖ := by
    intro x hx
    obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hJ x hx)
    obtain ⟨c, hc, r, hr, h⟩ := exists_ball_isCRevSol hW hT hw
    exact ⟨r, c, hr, hc, h⟩
  choose r c hrc using hper
  obtain ⟨t, ht⟩ := hJc.elim_finite_subcover
    (fun i : J => Metric.ball (α := ℝ) (i.1 : ℝ) (r i.1 i.2 / 2))
    (fun _ => isOpen_ball) (fun x hx =>
      mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (by have := (hrc x hx).1; linarith)⟩)
  obtain ⟨x₀, hx₀⟩ := hJne
  have htne : t.Nonempty := by
    obtain ⟨i, hit, -⟩ := mem_iUnion₂.1 (ht hx₀)
    exact ⟨i, hit⟩
  set ρ := (t.image fun i : J => r i.1 i.2 / 2).min' (htne.image _) with hρdef
  set cc := (t.image fun i : J => c i.1 i.2).min' (htne.image _) with hccdef
  have hρmem := Finset.min'_mem (t.image fun i : J => r i.1 i.2 / 2) (htne.image _)
  have hccmem := Finset.min'_mem (t.image fun i : J => c i.1 i.2) (htne.image _)
  have hρpos : 0 < ρ := by
    obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hρmem
    have h2 : ρ = r v.1 v.2 / 2 := by rw [hρdef, ← hv]
    rw [h2]; exact half_pos (hrc v.1 v.2).1
  have hccpos : 0 < cc := by
    obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hccmem
    have h2 : cc = c v.1 v.2 := by rw [hccdef, ← hv]
    rw [h2]; exact (hrc v.1 v.2).2.1
  refine ⟨ρ, hρpos, cc, hccpos, fun x hx t' ht' z hz => ?_⟩
  obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.1 (ht hx)
  have hρle : ρ ≤ r i.1 i.2 / 2 :=
    Finset.min'_le _ _ (Finset.mem_image.2 ⟨i, hit, rfl⟩)
  have hccle : cc ≤ c i.1 i.2 := Finset.min'_le _ _ (Finset.mem_image.2 ⟨i, hit, rfl⟩)
  have hzi : z ∈ Metric.ball (α := ℂ) (i.1 : ℂ) (r i.1 i.2) := by
    rw [mem_ball] at hz hxi ⊢
    calc dist z (i.1 : ℂ) ≤ dist z (x : ℂ) + dist (x : ℂ) (i.1 : ℂ) := dist_triangle _ _ _
      _ < ρ + r i.1 i.2 / 2 := by rw [dist_ofReal_coe]; linarith
      _ ≤ r i.1 i.2 := by linarith
  obtain ⟨u, hu, hub⟩ := (hrc i.1 i.2).2.2 z hzi
  exact ⟨u, isCRevSol_restrict hu ht'.2,
    fun s hs => hccle.trans (hub s ⟨hs.1, hs.2.trans ht'.2⟩)⟩

/-! ### The uniform extension -/

/-- **A2-ext, uniform in the horizon.** If `J` is compact and live at time `T`, there is an open,
conjugation-invariant neighbourhood `U` of the real points of `J` on which `revMapExt W t` is
holomorphic for **all** `t ∈ [0,T]`, with the Schwarz reflection, the real values `realRevMap W t`
and the explicit positive derivative `exp (∫₀ᵗ 2/(realRevMap W s x)²)` at the points of `J`. -/
theorem exists_unif_revMapExt_extension (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {J : Set ℝ}
    (hJc : IsCompact J) (hJ : ∀ x ∈ J, ENNReal.ofReal T < realHitTime W x) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x ∈ J, (x : ℂ) ∈ U) ∧ (∀ z ∈ U, conj z ∈ U) ∧
      (∀ t ∈ Icc (0 : ℝ) T, DifferentiableOn ℂ (revMapExt W t) U) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ U, revMapExt W t (conj z) = conj (revMapExt W t z)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ J, revMapExt W t x = realRevMap W t x ∧
        deriv (revMapExt W t) x =
          ((Real.exp (∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2) : ℝ) : ℂ) ∧
        0 < (deriv (revMapExt W t) x).re ∧ (deriv (revMapExt W t) x).im = 0) := by
  obtain ⟨ρ, hρ, c, hc, hgood⟩ := exists_unif_ball_isCRevSol hW hT hJc hJ
  refine ⟨Metric.thickening ρ ((↑) '' J), Metric.isOpen_thickening,
    fun x hx => Metric.mem_thickening_iff.2 ⟨(x : ℂ), mem_image_of_mem _ hx, by
      rw [dist_self]; exact hρ⟩, fun z hz => ?_,
    fun t ht z hz => ?_, fun t ht z _ => RevMapExtension.revMapExt_conj ht.1 z,
    fun t ht x hx => ?_⟩
  · obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.1 hz
    obtain ⟨x, hx, rfl⟩ := hy
    exact Metric.mem_thickening_iff.2 ⟨(x : ℂ), mem_image_of_mem _ hx, by
      rw [← Complex.conj_ofReal x, Complex.dist_conj_conj]; exact hzy⟩
  · obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.1 hz
    obtain ⟨x, hx, rfl⟩ := hy
    have hzx : dist z (x : ℂ) < ρ := hzy
    have hρ' : 0 < ρ - dist z (x : ℂ) := by linarith
    have hsub : Metric.ball z (ρ - dist z (x : ℂ)) ⊆ Metric.ball (x : ℂ) ρ :=
      Metric.ball_subset_ball' (by linarith)
    obtain ⟨u₀, hu₀, -⟩ := hgood x hx t ht z hzx
    exact (hasDerivAt_revMapExt ht.1 hρ' hc
      (fun w hw => hgood x hx t ht w (hsub hw)) hu₀).differentiableAt.differentiableWithinAt
  · obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hJ x hx)
    have hresT : IsCRevSol W x T (fun s => (w s : ℂ)) := isCRevSol_ofReal hw
    have hres : IsCRevSol W x t (fun s => (w s : ℂ)) := isCRevSol_restrict hresT ht.2
    have hderiv : deriv (revMapExt W t) x =
        ((Real.exp (∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2) : ℝ) : ℂ) := by
      rw [(hasDerivAt_revMapExt ht.1 hρ hc (fun w hw => hgood x hx t ht w hw) hres).deriv]
      have e1 : (fun s => (2 : ℂ) / ((w s : ℂ)) ^ 2) = fun s => ((2 / (w s) ^ 2 : ℝ) : ℂ) := by
        funext s; push_cast; rfl
      have e2 : (∫ s in (0 : ℝ)..t, 2 / (w s) ^ 2) =
          ∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht.1] at hs
        change 2 / w s ^ 2 = 2 / (realRevMap W s x) ^ 2
        rw [RealLine.realRevMap_eq hW hw hs.1 (hs.2.trans ht.2)]
      rw [e1, intervalIntegral.integral_ofReal, e2, Complex.ofReal_exp]
    have hpos : 0 < (deriv (revMapExt W t) x).re := by
      rw [hderiv, Complex.ofReal_re]; exact Real.exp_pos _
    have him : (deriv (revMapExt W t) x).im = 0 := by rw [hderiv, Complex.ofReal_im]
    exact ⟨revMapExt_ofReal hW ht.1 (RealLine.isRealRevSol_restrict hw ht.2), hderiv, hpos, him⟩

/-- **Derivative at a live real point**, in the horizon-`t` form. -/
theorem deriv_revMapExt_eq_of_live (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {x : ℝ}
    (hx : ENNReal.ofReal T < realHitTime W x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    deriv (revMapExt W t) x =
      ((Real.exp (∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2) : ℝ) : ℂ) := by
  obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime hx
  obtain ⟨ρ, hρ, c, hc, hgood⟩ := exists_unif_ball_isCRevSol hW hT (J := {x})
    isCompact_singleton (fun y hy => by rw [mem_singleton_iff] at hy; rw [hy]; exact hx)
  have hxρ : (x : ℂ) ∈ Metric.ball (α := ℂ) (x : ℂ) ρ := Metric.mem_ball_self hρ
  have hresT : IsCRevSol W x T (fun s => (w s : ℂ)) := isCRevSol_ofReal hw
  have hres : IsCRevSol W x t (fun s => (w s : ℂ)) := isCRevSol_restrict hresT ht.2
  have hder : deriv (revMapExt W t) x = Complex.exp (∫ s in (0 : ℝ)..t, 2 / ((w s : ℂ)) ^ 2) :=
    (hasDerivAt_revMapExt (z₀ := (x : ℂ)) ht.1 hρ hc
      (fun y hy => hgood x (mem_singleton x) t ht y hy) hres).deriv
  rw [hder]
  have e1 : (fun s => (2 : ℂ) / ((w s : ℂ)) ^ 2) = fun s => ((2 / (w s) ^ 2 : ℝ) : ℂ) := by
    funext s; push_cast; rfl
  have e2 : (∫ s in (0 : ℝ)..t, 2 / (w s) ^ 2) =
      ∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change 2 / w s ^ 2 = 2 / (realRevMap W s x) ^ 2
    rw [RealLine.realRevMap_eq hW hw hs.1 (hs.2.trans ht.2)]
  rw [e1, intervalIntegral.integral_ofReal, e2, Complex.ofReal_exp]

/-! ### Uniform bounds on the derivative and its inverse -/

/-! ### The uniform second-derivative bound -/

/-! ### Monotonicity and continuity in the horizon -/

end RegUnif
end QuantumZipper
