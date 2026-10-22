import HigherDimLQGMetric.Sec8b.Prop86EventBridge
import HigherDimLQGMetric.Sec8b.FavorableCM

/-! Cameron--Martin and Hölder bound for one fixed scale, bin and colour. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_cm_class_bound
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs R : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hcs : 0 ≤ cs) (hCs : 0 < Cs)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hR : 0 < R) (x y : Rd d)
    (j i : ℤ) (colour : Fin d → ℤ)
    (hrR : 3 * (64 : ℝ) ^ j ≤ R)
    (k : ℕ) (hk : 1 ≤ k)
    (S : Finset (Finset (Rd d × ℕ)))
    (hS : ∀ Z ∈ S,
      IsSec8LabeledSet d T.J ((64 : ℝ) ^ j) R x y colour Z ∧
        Z.card ≤ k)
    {M0 : ℝ} (hM0 : 0 ≤ M0)
    (hcm : ∀ label < T.J, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      IsCMBounded (bumpAt (T.f label) r z) M0)
    {pH : ℝ} (hpH : 1 < pH) :
    ∑ Z ∈ S, P.real {ω | h ω ∈
      FavEventBorel D Dt ξ Q Cs ((2 : ℝ) ^ i) R ((64 : ℝ) ^ j)
        T.b T.J T.N T.V T.f x y Z} ≤
      Real.exp ((pH - 1) / 2 * (k * M0) ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ *
        (((2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
          ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k : ℕ) : ℝ) ^ (1 - pH⁻¹) := by
  classical
  let r : ℝ := (64 : ℝ) ^ j
  let q : ℝ := (2 : ℝ) ^ i
  have hr : 0 < r := by dsimp [r]; positivity
  have h85 := lemma85 P h hh.1 hd hξ hQ hcs hCs hD hDt
    hcomp T hR x y
  have hbridge : ∀ᵐ ω ∂P, ∀ Z ∈ S,
      shiftNorm (h ω) (F_Z T.f r Z) ∈
        FavEventBorel D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z ↔
      addFun (h ω) (F_Z T.f r Z) ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z := by
    refine (Filter.eventually_all_finset S).2 fun Z hZS => ?_
    exact s7b_shiftNorm_fav_equiv_ae P h hh.1 hd hξ hQ hR hr
      hD hDt T x y colour Z (hS Z hZS).1
  have hcount : ∀ᵐ ω ∂P,
      ((S.filter fun Z => shiftNorm (h ω) (F_Z T.f r Z) ∈
        FavEventBorel D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z).card : ℝ) ≤
      (((2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
        ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k : ℕ) : ℝ) := by
    filter_upwards [h85, hbridge] with ω hω hbr
    have hraw := hω j i colour k hk hrR S hS
    have heq : (S.filter fun Z => shiftNorm (h ω) (F_Z T.f r Z) ∈
        FavEventBorel D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z) =
        (S.filter fun Z => addFun (h ω) (F_Z T.f r Z) ∈
          FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z) := by
      apply Finset.filter_congr
      intro Z hZS
      exact hbr Z hZS
    simpa only [heq, r, q] using (show
      ((S.filter fun Z => addFun (h ω) (F_Z T.f r Z) ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z).card : ℝ) ≤
        (((2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
          ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k : ℕ) : ℝ) from
      (by exact_mod_cast hraw))
  have hSJ : ∀ Z ∈ S, (∀ site ∈ Z, site.2 < T.J) ∧ Z.card ≤ k := by
    intro Z hZS
    refine ⟨?_, (hS Z hZS).2⟩
    intro site hs
    obtain ⟨_, _, _, _, _, _, hj⟩ := (hS Z hZS).1.1 site hs
    exact hj
  exact s7b_cm_favorable (by omega : 2 ≤ d)
    hD.measurable hDt.measurable T hM0 hcm hh Cs q R r hr x y S
    hSJ hpH (by positivity) hcount

end HigherDimLQGMetric
