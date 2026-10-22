import HigherDimLQGMetric.Events.AnnulusGeometry
import HigherDimLQGMetric.Weak.DetInternalTight

/-!
# The two configuration domains

The configuration coordinates are continuous functions on the pair spaces of the
outer and inner annuli.  Both annuli are connected when `d ≥ 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The outer configuration annulus. -/
def configOuter (d : ℕ) : Set (Rd d) := ann 0 (1 / 2) 5

/-- The inner configuration annulus. -/
def configInner (d : ℕ) : Set (Rd d) := ann 0 (3 / 4) (7 / 2)

theorem configInner_subset_outer : configInner d ⊆ configOuter d := by
  intro x hx
  dsimp [configInner, configOuter, ann] at hx ⊢
  constructor <;> linarith

/-- Open Euclidean annuli are connected in dimension at least two. -/
theorem config_isConnected_ann (hd : 2 ≤ d) (z : Rd d) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) : IsConnected (ann z a b) := by
  let S : Set (Rd d) := sphere 0 1
  let I : Set ℝ := Ioo a b
  have himage : ann z a b =
      (fun p : ℝ × Rd d => p.1 • p.2 + z) '' (I ×ˢ S) := by
    ext x
    constructor
    · intro hx
      have hn : 0 < ‖x - z‖ := ha.trans hx.1
      let v : Rd d := ‖x - z‖⁻¹ • (x - z)
      have hv : v ∈ S := by
        rw [mem_sphere, dist_eq_norm, sub_zero]
        dsimp [v]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
        exact inv_mul_cancel₀ hn.ne'
      refine ⟨(‖x - z‖, v), ⟨hx, hv⟩, ?_⟩
      dsimp [v]
      simp [smul_smul, hn.ne']
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      have htpos : 0 < t := ha.trans ht.1
      have hvnorm : ‖v‖ = 1 := by
        simpa only [S, mem_sphere, dist_eq_norm, sub_zero] using hv
      change a < ‖t • v + z - z‖ ∧ ‖t • v + z - z‖ < b
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hvnorm, mul_one]
      exact ht
  rw [himage]
  exact ((isConnected_Ioo hab).prod (isConnected_unit_sphere hd)).image _
    (by fun_prop : ContinuousOn (fun p : ℝ × Rd d => p.1 • p.2 + z) (I ×ˢ S))

theorem configOuter_isOpen : IsOpen (configOuter d) := isOpen_ann _ _ _
theorem configInner_isOpen : IsOpen (configInner d) := isOpen_ann _ _ _

instance configOuter_locallyCompactSpace : LocallyCompactSpace (configOuter d) :=
  configOuter_isOpen.locallyCompactSpace

instance configInner_locallyCompactSpace : LocallyCompactSpace (configInner d) :=
  configInner_isOpen.locallyCompactSpace

theorem configOuter_isPreconnected (hd : 2 ≤ d) : IsPreconnected (configOuter d) :=
  (config_isConnected_ann hd 0 (by norm_num) (by norm_num)).isPreconnected

theorem configInner_isPreconnected (hd : 2 ≤ d) : IsPreconnected (configInner d) :=
  (config_isConnected_ann hd 0 (by norm_num) (by norm_num)).isPreconnected

end HigherDimLQGMetric
