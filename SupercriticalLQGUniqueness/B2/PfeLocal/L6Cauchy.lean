import SupercriticalLQGUniqueness.B2.PfeLocal.L6Lusin
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3WeylMetric
import SupercriticalLQGUniqueness.B2.PfeAxioms.AnnulusWeylTransfer

 
















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum Uniqueness.Toolkit.PathInfimum PfeWeyl

 
theorem l6_sandwich {W : ℕ → LSCMetric} {E : LSCMetric} (hW : Tendsto W atTop (𝓝 E))
    (hLen : ∀ n, (W n).IsLengthSpace)
    (hPath : ∀ n, PfeAxioms.FinitePathsEuclideanContinuous (W n))
    (hforget : ∀ n, Continuous (euclidForget (W n)))
    (hsmall : ∀ k : ℕ, SmallAnnulusCosts W E (closedBall 0 k) (ball 0 ((k : ℝ) + 1)))
    (c : L5Code) {m m' : ℕ} (h : m < m') :
    limsup (fun n => l5Obs (W n) (l6Enlarge c m)) atTop ≤ l5Obs E (l6Enlarge c m') ∧
      l5Obs E (l6Enlarge c m') ≤ liminf (fun n => l5Obs (W n) (l6Enlarge c m')) atTop := by
  obtain ⟨h1, h2, h3⟩ := l6_enlarge_margin c h
  have hpos : (0 : ℝ) < (l6δ m : ℝ) - l6δ m' := by
    have := l6δ_anti h; rw [sub_pos]; exact_mod_cast this
  exact ⟨l6_limsup_le hW hLen hPath hforget hsmall (l5Rect_isCompact _) hpos h1 h2 h3,
    compactPathInf_seq_liminf hW (l5Rect_isCompact _) (l5Ball_isCompact _) (l5Ball_isCompact _)⟩

 
theorem l6_cauchy {W : ℕ → LSCMetric} {E : LSCMetric} (hW : Tendsto W atTop (𝓝 E))
    (hLen : ∀ n, (W n).IsLengthSpace)
    (hPath : ∀ n, PfeAxioms.FinitePathsEuclideanContinuous (W n))
    (hforget : ∀ n, Continuous (euclidForget (W n)))
    (hsmall : ∀ k : ℕ, SmallAnnulusCosts W E (closedBall 0 k) (ball 0 ((k : ℝ) + 1)))
    (c : L5Code) {m m' : ℕ} (h : m < m') :
    limsup (fun n => l5Obs (W n) (l6Enlarge c m)) atTop ≤
      liminf (fun n => l5Obs (W n) (l6Enlarge c m')) atTop :=
  let h := l6_sandwich hW hLen hPath hforget hsmall c h
  h.1.trans h.2

 
theorem l6_weyl_cauchy {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace) (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (M : ℝ) (hfM : ∀ z, |f z| ≤ M) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D)
    (W : ℕ → LSCMetric) (hW : ∀ n x y, W n (x, y) = weylScale ξ (fn n) (G n) (x, y))
    (hWlen : ∀ n, (W n).IsLengthSpace)
    (hWpath : ∀ n, PfeAxioms.FinitePathsEuclideanContinuous (W n))
    (hWforget : ∀ n, Continuous (euclidForget (W n)))
    (hsmall : ∀ k : ℕ, SmallAnnulusCosts G D (closedBall 0 k) (ball 0 ((k : ℝ) + 1)))
    (c : L5Code) {m m' : ℕ} (h : m < m') :
    limsup (fun n => l5Obs (W n) (l6Enlarge c m)) atTop ≤
      liminf (fun n => l5Obs (W n) (l6Enlarge c m')) atTop := by
  obtain ⟨E, hE, hWE⟩ := weyl_tendsto_lscMetric hG hGlen hGforget ξ hξ f fn hfn M hfM hfnM
    hDlen hDforget hacross W hW hWforget hsmall
  have hsmallW : ∀ k : ℕ, SmallAnnulusCosts W E (closedBall 0 k) (ball 0 ((k : ℝ) + 1)) :=
    fun k => PfeAxioms.smallAnnulusCosts_of_bounded_weyl ξ hξ G W D E f fn hDforget hE
      (fun n p => hW n p.1 p.2) M (fun z => (abs_le.1 (hfM z)).1)
      (fun n z _ => (abs_le.1 (hfnM n z)).2) (hsmall k)
  exact l6_cauchy hWE hWlen hWpath hWforget hsmallW c h

end SupercriticalLQGUniqueness.B2.PfeLocal
