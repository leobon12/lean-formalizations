import HigherDimLQGMetric.Config.Geometry
import HigherDimLQGMetric.Events.Defs
import HigherDimLQGMetric.Sharp.ScaledMetric
import HigherDimLQGMetric.Events.ScaledEvent

/-!
# Continuous real configuration coordinates

For length metrics in dimension at least two, the four normalized internal
metrics are finite continuous functions on their annular pair domains.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- MA1's configuration space with the compact-open topology. -/
abbrev ConfigC (d : ℕ) : Type :=
  C(configOuter d × configOuter d, ℝ) × C(configOuter d × configOuter d, ℝ) ×
    C(configInner d × configInner d, ℝ) × C(configInner d × configInner d, ℝ)

/-- The normalized metric before restricting to either annulus. -/
def configScaledMetric (D : ContMetric d) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (z : Rd d) : ContMetric d :=
  (D.affine r hr.ne' z).smul s⁻¹ (inv_pos.mpr hs)

theorem configScaledMetric_one (D : ContMetric d) :
    configScaledMetric D (s := 1) (r := 1) (by norm_num) (by norm_num) 0 = D := by
  apply Subtype.ext
  ext p
  simp only [configScaledMetric, ContMetric.smul_apply, ContMetric.affine_apply]
  simp

theorem configScaledMetric_isLength (D : ContMetric d) (hD : D.IsLength)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d) :
    (configScaledMetric D hs hr z).IsLength :=
  ContMetric.isLength_smul (inv_pos.mpr hs)
    (ContMetric.isLength_affine hr.ne' z hD)

/-- Continuous version of the four internal-metric coordinates. -/
def configC (hd : 2 ≤ d) (D Dt : ContMetric d) (hD : D.IsLength)
    (hDt : Dt.IsLength) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d) :
    ConfigC d :=
  let E := configScaledMetric D hs hr z
  let Et := configScaledMetric Dt hs hr z
  (internalC E (configScaledMetric_isLength D hD hs hr z)
      configOuter_isOpen (configOuter_isPreconnected hd),
   internalC Et (configScaledMetric_isLength Dt hDt hs hr z)
      configOuter_isOpen (configOuter_isPreconnected hd),
   internalC E (configScaledMetric_isLength D hD hs hr z)
      configInner_isOpen (configInner_isPreconnected hd),
   internalC Et (configScaledMetric_isLength Dt hDt hs hr z)
      configInner_isOpen (configInner_isPreconnected hd))

theorem configScaledMetric_internal (D : ContMetric d) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (z : Rd d)
    (V : Set (Rd d)) (u v : Rd d) :
    (configScaledMetric D hs hr z).internal V u v =
      ENNReal.ofReal s⁻¹ * D.internal ((fun x => r • x + z) '' V)
        (r • u + z) (r • v + z) := by
  unfold configScaledMetric
  rw [ContMetric.internal_smul, ContMetric.internal_affine hr.ne' z D]

/-- The real coordinate is exactly the finite extended internal distance. -/
theorem configScaledMetric_internalC_ofReal (D : ContMetric d) (hD : D.IsLength)
    (hd : 2 ≤ d) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d)
    (u v : configOuter d) :
    ENNReal.ofReal
      (internalC (configScaledMetric D hs hr z)
        (configScaledMetric_isLength D hD hs hr z)
        configOuter_isOpen (configOuter_isPreconnected hd) (u, v)) =
      ENNReal.ofReal s⁻¹ *
        D.internal (ann z (r / 2) (5 * r)) (r • u.1 + z) (r • v.1 + z) := by
  have hfin := (configScaledMetric D hs hr z).internal_ne_top_of_isPreconnected
    (configScaledMetric_isLength D hD hs hr z)
    configOuter_isOpen (configOuter_isPreconnected hd) u.2 v.2
  change ENNReal.ofReal ((configScaledMetric D hs hr z).internal
    (configOuter d) u.1 v.1).toReal = _
  rw [ENNReal.ofReal_toReal hfin, configScaledMetric_internal]
  simp only [configOuter, image_ann_affine hr z (1 / 2) 5]
  congr 2
  ring_nf

theorem configC_bridge_outer (hd : 2 ≤ d) (D Dt : ContMetric d)
    (hD : D.IsLength) (hDt : Dt.IsLength) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (z : Rd d) (u v : configOuter d) :
    ENNReal.ofReal ((configC hd D Dt hD hDt hs hr z).1 (u, v)) =
      (config D Dt s r z).1 u.1 v.1 := by
  exact configScaledMetric_internalC_ofReal D hD hd hs hr z u v

theorem configScaledMetric_internalC_inner_ofReal (D : ContMetric d) (hD : D.IsLength)
    (hd : 2 ≤ d) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d)
    (u v : configInner d) :
    ENNReal.ofReal
      (internalC (configScaledMetric D hs hr z)
        (configScaledMetric_isLength D hD hs hr z)
        configInner_isOpen (configInner_isPreconnected hd) (u, v)) =
      ENNReal.ofReal s⁻¹ *
        D.internal (ann z (3 * r / 4) (7 * r / 2))
          (r • u.1 + z) (r • v.1 + z) := by
  have hfin := (configScaledMetric D hs hr z).internal_ne_top_of_isPreconnected
    (configScaledMetric_isLength D hD hs hr z)
    configInner_isOpen (configInner_isPreconnected hd) u.2 v.2
  change ENNReal.ofReal ((configScaledMetric D hs hr z).internal
    (configInner d) u.1 v.1).toReal = _
  rw [ENNReal.ofReal_toReal hfin, configScaledMetric_internal]
  simp only [configInner, image_ann_affine hr z (3 / 4) (7 / 2)]
  congr 2
  ring_nf

theorem configC_bridge_outer_tilde (hd : 2 ≤ d) (D Dt : ContMetric d)
    (hD : D.IsLength) (hDt : Dt.IsLength) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (z : Rd d) (u v : configOuter d) :
    ENNReal.ofReal ((configC hd D Dt hD hDt hs hr z).2.1 (u, v)) =
      (config D Dt s r z).2.1 u.1 v.1 := by
  exact configScaledMetric_internalC_ofReal Dt hDt hd hs hr z u v

theorem configC_bridge_inner (hd : 2 ≤ d) (D Dt : ContMetric d)
    (hD : D.IsLength) (hDt : Dt.IsLength) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (z : Rd d) (u v : configInner d) :
    ENNReal.ofReal ((configC hd D Dt hD hDt hs hr z).2.2.1 (u, v)) =
      (config D Dt s r z).2.2.1 u.1 v.1 := by
  exact configScaledMetric_internalC_inner_ofReal D hD hd hs hr z u v

theorem configC_bridge_inner_tilde (hd : 2 ≤ d) (D Dt : ContMetric d)
    (hD : D.IsLength) (hDt : Dt.IsLength) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (z : Rd d) (u v : configInner d) :
    ENNReal.ofReal ((configC hd D Dt hD hDt hs hr z).2.2.2 (u, v)) =
      (config D Dt s r z).2.2.2 u.1 v.1 := by
  exact configScaledMetric_internalC_inner_ofReal Dt hDt hd hs hr z u v

end HigherDimLQGMetric
