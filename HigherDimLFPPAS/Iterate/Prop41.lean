import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Improve.Prop41
import HigherDimLQGMetric.Sharp.GridCount
import HigherDimLQGMetric.Sharp.GridNear

/-!
# Proposition 4.1 interface adapter

This module specializes the deterministic covering theorem to the shared core interfaces.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Metric

namespace HigherDimLFPPAS.Iterate

open HigherDimLQGMetric HigherDimLFPPAS.Core HigherDimLFPPAS.Improve
open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem setDistIn_anti (G : ContMetric d) {U V : Set (Rd d)} (hUV : U ⊆ V)
    (A B : Set (Rd d)) :
    setDistIn G V A B ≤ setDistIn G U A B := by
  unfold setDistIn
  exact iInf₂_mono fun u _ => iInf₂_mono fun v _ => G.internal_anti hUV u v

/-- The shared Borel good-annulus event implies D4's deterministic good-annulus condition. -/
theorem goodAnnulus_imp_d4GoodAt {G G' : ContMetric d} {A η c b r : ℝ} {z : Rd d}
    (hr : 0 < r) (hc : 0 < c) (hη : 0 < η) (hA : 1 ≤ A) (hb : 0 < b)
    (hE : Core.GoodAnnulus G G' A η c b z r) : Improve.d4GoodAt G G' z r c η A b := by
  obtain ⟨h1, h2, h3⟩ := hE
  have hFV : Improve.d4F z r ⊆ ann z (r / 2) (3 * r / 2) := by
    intro x hx
    simp only [Improve.d4F, annCl, ann, mem_ofPred_eq] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hFU : Improve.d4F z r ⊆ Improve.d4U z r := by
    intro x hx
    simp only [Improve.d4F, Improve.d4U, annCl, ann, mem_ofPred_eq] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hδG := setDistIn_anti G hFU (sphere z (3 * r / 4)) (sphere z r)
  have hδG' := setDistIn_anti G' hFU (sphere z (3 * r / 4)) (sphere z r)
  refine ⟨hr, hc, hη, hA, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact (h1 x hx y hy).1.trans (by gcongr; exact G.internal_anti hFV x y)
  · intro x hx y hy
    exact (h1 x hx y hy).2.trans (by gcongr; exact G'.internal_anti hFV x y)
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    exact (h2 x hx y hy).1.trans (by gcongr; exact hδG)
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    exact (h2 x hx y hy).2.trans (by gcongr; exact hδG')
  · intro x hx w hw
    exact (h3 x hx w hw).1.trans (by gcongr; exact hδG)
  · intro x hx w hw
    exact (h3 x hx w hw).2.trans (by gcongr; exact hδG')

/-- Proposition 4.1 in the shared interface form. -/
theorem prop41_holds (d : ℕ) : Core.Prop41Stmt d := by
  intro hd u q₀ η A hu huq hq₀ hη hA
  let εbase := Improve.d4_prop41_epsilon0 hu huq hq₀
  have hbase : 0 < εbase ∧ ∀ ε ∈ Ioo (0 : ℝ) εbase,
      8 * ε ^ q₀ ≤ 6 * ε ^ (u / 2) ∧ ε ^ u / 100 + 2 * ε ^ (u / 2) < 1 := by
    simpa only [εbase, Improve.d4_prop41_epsilon0] using
      Classical.choose_spec (Improve.d4_prop41_small_epsilon hu huq hq₀)
  let ε₀ : ℝ := min εbase 1
  have hε₀ : 0 < ε₀ := lt_min hbase.1 (by norm_num)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε R hR G G' Rε c m C hRε hgood hcomp
  have hεbase : ε < εbase := hε.2.trans_le (min_le_left _ _)
  have hε1 : ε < 1 := hε.2.trans_le (min_le_right _ _)
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  let s : ℝ := ε ^ u / (100 * (d : ℝ))
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (Real.rpow_pos_of_pos hε.1 u) (mul_pos (by norm_num) hdpos)
  let box : Finset (Rd d) := HigherDimLQGMetric.shellGridBox d
    (⌈(R + 1) / s⌉₊ + 1) s
  have hmeshSub : Core.mesh d ε u R ⊆ (box : Set (Rd d)) := by
    intro z hz
    have hz' : z ∈ HigherDimLQGMetric.gridPts s ∩ Metric.ball (0 : Rd d) (R + 1) := by
      simpa [Core.mesh, s] using hz
    exact HigherDimLQGMetric.grid_ball_subset_shellGridBox hs (by linarith) hz'
  have hmeshFinite : (Core.mesh d ε u R).Finite := box.finite_toSet.subset hmeshSub
  let mesh : Finset (Rd d) := hmeshFinite.toFinset
  have hmeshMem (z : Rd d) : z ∈ mesh ↔ z ∈ Core.mesh d ε u R := by
    simpa only [mesh] using hmeshFinite.mem_toFinset (a := z)
  have hpow : ε ^ u ≤ 1 := by
    calc
      ε ^ u ≤ ε ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hε.1 hε1.le (le_of_lt hu)
      _ = 1 := by simp
  have hmeshCover : ∀ x ∈ Metric.ball (0 : Rd d) R,
      ∃ z ∈ mesh, dist x z ≤ ε ^ u / 100 := by
    intro x hx
    obtain ⟨z, hzgrid, hnear⟩ := HigherDimLQGMetric.exists_gridPt_near hs x
    have hdist : dist x z ≤ ε ^ u / 100 := by
      rw [dist_eq_norm]
      calc
        ‖x - z‖ ≤ (d : ℝ) * s := hnear
        _ = ε ^ u / 100 := by
          dsimp [s]
          field_simp [ne_of_gt hdpos]
    have hxnorm : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hztri : ‖z‖ ≤ ‖x‖ + dist x z := by
      have hrepr : z = x + (z - x) := by abel
      calc
        ‖z‖ = ‖x + (z - x)‖ := by rw [← hrepr]
        _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
        _ = ‖x‖ + dist x z := by rw [dist_eq_norm]; simp [norm_sub_rev]
    have hsmall : ε ^ u / 100 < 1 := by nlinarith
    have hzball : z ∈ Metric.ball (0 : Rd d) (R + 1) := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hzcore : z ∈ Core.mesh d ε u R := by
      rw [Core.mesh]
      exact ⟨by simpa [s] using hzgrid, hzball⟩
    exact ⟨z, (hmeshMem z).2 hzcore, hdist⟩
  have hcover : Improve.d4Covering G G' R (ε ^ u) (ε ^ (u / 2)) η A
      (8 * ε ^ q₀) mesh Rε c := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨z, hz, hdist⟩ := hmeshCover x hx
      exact ⟨z, hz, hdist⟩
    · intro z hz
      have hzcore := (hmeshMem z).1 hz
      have hzcore' : z ∈ HigherDimLQGMetric.gridPts s ∩ Metric.ball (0 : Rd d) (R + 1) := by
        simpa [Core.mesh, s] using hzcore
      exact hzcore'.2
    · intro z hz
      have hzcore := (hmeshMem z).1 hz
      obtain ⟨r, hrRε, hEr⟩ := hgood z hzcore
      obtain ⟨hwindow, hc, hcm⟩ := hRε r hrRε
      rcases hwindow with ⟨k, hk, rfl⟩
      have hrmin : ε ^ u ≤ (256 : ℝ) ^ (-k) := hk.1
      have hrmax : (256 : ℝ) ^ (-k) ≤ ε ^ (u / 2) := hk.2
      have hgoodD4 : Improve.d4GoodAt G G' z ((256 : ℝ) ^ (-k))
          (c ((256 : ℝ) ^ (-k))) η A (8 * ε ^ q₀) := by
        apply goodAnnulus_imp_d4GoodAt
        · exact lt_of_lt_of_le (Real.rpow_pos_of_pos hε.1 u) hrmin
        · exact hc
        · exact hη
        · exact hA
        · exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hε.1 q₀)
        · exact hEr
      exact ⟨(256 : ℝ) ^ (-k), hrRε, hrmin, hrmax, hgoodD4⟩
  have hcompare : Improve.d4Comparison G G' R ε q₀ C := hcomp
  have hεsmall : ε < Improve.d4_prop41_epsilon0 hu huq hq₀ := hεbase
  have hresult := Improve.d4_prop41_forward_full hu huq hq₀ hη hA hR hε.1 hε1 hεsmall
    G G' mesh Rε c (fun r hr => (hRε r hr).2.2) hcover hcompare
  exact hresult

end HigherDimLFPPAS.Iterate

end
