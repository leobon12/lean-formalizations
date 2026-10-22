import HigherDimLQGMetric.DGZ.NiceBoxMeas

/-!
# Locality of the across distance on the closed shell (packet L4a1)

Source: planning audit MA7 D-5.3, Remark 5.4′ ("the across term lives on the shell around `x`"),
blueprint Lemma `r2:lem:54`(iii).

L3b1's `measurable_acrossDist_comap` gives measurability for the field on the whole box
`B̄_{r₁}(c)`; the independence of `𝒞(x,z)` from the fine fields near `z` (DGZ Remark 5.4(2), Lemma
5.7) needs measurability for the field on the **closed shell** `B̄_{r₁}(c) \ B_{r₂}(c)` only. The
shell is not a retract of `ℝ^d`, so the clamping trick of L3b1 does not apply; instead:

* `linfDist c z = |z - c|_∞` (the sup norm of `z - c` as a function on `Fin d`);
* `shellExt c r₁ r₂ φ`: for `|z - c|_∞ ≥ r₂` the value `φ(clamp_{B̄_{r₁}(c)} z)`, and inside the
  hole the radial projection to `∂B_{r₂}(c)` damped linearly to `0` at `c`: `(|z - c|_∞ / r₂) φ(c +
  (r₂/|z - c|_∞)(z - c))`. It is continuous for continuous `φ` (`continuous_shellExt`), agrees with
  `φ` on the closed shell (`shellExt_eq_of_mem`), and each value only uses `φ` at one point of the
  closed shell (or is `0`).
* `measurable_acrossDist_comap_shell`: the across distance is measurable for the σ-algebra of the
  field on the closed shell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox clampBox clampBox_apply
  continuous_clampBox clampBox_mem clampBox_of_mem)

variable {d : ℕ}

/-! ## The `ℓ^∞` distance -/

/-- The `ℓ^∞` distance `|z - c|_∞`. -/
def linfDist (c z : Rd d) : ℝ := ‖(WithLp.ofLp (z - c) : Fin d → ℝ)‖

theorem continuous_linfDist (c : Rd d) : Continuous (linfDist c) :=
  continuous_norm.comp ((PiLp.continuous_ofLp 2 _).comp (continuous_id.sub continuous_const))

theorem linfDist_nonneg (c z : Rd d) : 0 ≤ linfDist c z := norm_nonneg _

theorem abs_sub_le_linfDist (c z : Rd d) (i : Fin d) : |z i - c i| ≤ linfDist c z := by
  have h := norm_le_pi_norm (WithLp.ofLp (z - c) : Fin d → ℝ) i
  rwa [PiLp.sub_apply, Real.norm_eq_abs] at h

theorem linfDist_le_iff {c z : Rd d} {r : ℝ} (hr : 0 ≤ r) : linfDist c z ≤ r ↔ z ∈ cbox c r := by
  unfold linfDist
  rw [pi_norm_le_iff_of_nonneg hr]
  refine forall_congr' fun i => ?_
  rw [PiLp.sub_apply, Real.norm_eq_abs]

theorem linfDist_lt_iff {c z : Rd d} {r : ℝ} (hr : 0 < r) : linfDist c z < r ↔ z ∈ obox c r := by
  unfold linfDist
  rw [pi_norm_lt_iff hr]
  refine forall_congr' fun i => ?_
  rw [PiLp.sub_apply, Real.norm_eq_abs]

theorem linfDist_self (c : Rd d) : linfDist c c = 0 := by simp [linfDist]

theorem eq_of_linfDist_eq_zero {c z : Rd d} (h : linfDist c z = 0) : z = c := by
  unfold linfDist at h
  rw [norm_eq_zero] at h
  have h' : WithLp.ofLp (z - c) = WithLp.ofLp (0 : Rd d) := by rw [h]; rfl
  exact sub_eq_zero.1 (WithLp.ofLp_injective 2 h')

theorem linfDist_add_smul_sub (c z : Rd d) (t : ℝ) :
    linfDist c (c + t • (z - c)) = |t| * linfDist c z := by
  unfold linfDist
  rw [add_sub_cancel_left, WithLp.ofLp_smul, norm_smul, Real.norm_eq_abs]

/-! ## The extension from the closed shell -/

/-- **Extension of a field from the closed shell** `B̄_{r₁}(c) \ B_{r₂}(c)`: `φ ∘ clamp` outside the
hole, and inside it the radial projection to `∂B_{r₂}(c)` damped linearly to `0` at `c`. -/
def shellExt (c : Rd d) (r₁ r₂ : ℝ) (φ : Rd d → ℝ) (z : Rd d) : ℝ :=
  if r₂ ≤ linfDist c z then φ (clampBox c r₁ z)
  else linfDist c z / r₂ * φ (c + (r₂ / linfDist c z) • (z - c))

/-- The radial part of `shellExt`. -/
def radialExt (c : Rd d) (r₂ : ℝ) (φ : Rd d → ℝ) (z : Rd d) : ℝ :=
  linfDist c z / r₂ * φ (c + (r₂ / linfDist c z) • (z - c))

theorem radial_mem_lsph {c z : Rd d} {r₂ : ℝ} (hr₂ : 0 < r₂) (hz : z ≠ c) :
    c + (r₂ / linfDist c z) • (z - c) ∈ lsph c r₂ := by
  have hN : 0 < linfDist c z := lt_of_le_of_ne (linfDist_nonneg c z)
    (fun h => hz (eq_of_linfDist_eq_zero h.symm))
  have e : linfDist c (c + (r₂ / linfDist c z) • (z - c)) = r₂ := by
    rw [linfDist_add_smul_sub, abs_of_pos (div_pos hr₂ hN), div_mul_cancel₀ _ hN.ne']
  refine ⟨(linfDist_le_iff hr₂.le).1 e.le, fun h => ?_⟩
  have := (linfDist_lt_iff hr₂).2 h
  rw [e] at this
  exact lt_irrefl _ this

theorem continuous_radialExt {c : Rd d} {r₂ : ℝ} (hr₂ : 0 < r₂) {φ : Rd d → ℝ}
    (hφ : Continuous φ) : Continuous (radialExt c r₂ φ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = c
  · subst hz
    -- squeeze: `|radialExt z| ≤ (linfDist / r₂) M` with `M` a bound of `|φ|` on `∂B_{r₂}(c) ∪ {c}`
    have hK : IsCompact (insert z (lsph z r₂)) :=
      ((isCompact_cbox z r₂).of_isClosed_subset (isClosed_lsph z r₂)
        (lsph_subset_cbox z r₂)).insert z
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
    have h0 : radialExt z r₂ φ z = 0 := by simp [radialExt, linfDist_self]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z (mem_insert z _))
    have ht : Tendsto (radialExt z r₂ φ) (𝓝 z) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun w => linfDist z w / r₂ * M) (Eventually.of_forall
        fun w => ?_) ?_
      · have hpt : z + (r₂ / linfDist z w) • (w - z) ∈ insert z (lsph z r₂) := by
          by_cases hw : w = z
          · subst hw
            simp [linfDist_self]
          · exact mem_insert_of_mem _ (radial_mem_lsph hr₂ hw)
        rw [radialExt, norm_mul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (linfDist_nonneg _ _)
          hr₂.le)]
        exact mul_le_mul_of_nonneg_left (hM _ hpt) (div_nonneg (linfDist_nonneg _ _) hr₂.le)
      · have h1 : Tendsto (fun w => linfDist z w / r₂ * M) (𝓝 z)
            (𝓝 (linfDist z z / r₂ * M)) :=
          (((continuous_linfDist z).div_const r₂).mul continuous_const).tendsto z
        rwa [linfDist_self, zero_div, zero_mul] at h1
    rw [ContinuousAt, h0]
    exact ht
  · have hN : linfDist c z ≠ 0 := fun h => hz (eq_of_linfDist_eq_zero h)
    have h1 : ContinuousAt (fun w => r₂ / linfDist c w) z :=
      continuousAt_const.div (continuous_linfDist c).continuousAt hN
    have h2 : ContinuousAt (fun w => c + (r₂ / linfDist c w) • (w - c)) z :=
      continuousAt_const.add (h1.smul (continuousAt_id.sub continuousAt_const))
    exact (((continuous_linfDist c).div_const r₂).continuousAt).mul
      (hφ.continuousAt.comp h2)

/-- **The extension is continuous** (`0 < r₂ ≤ r₁`, `φ` continuous). -/
theorem continuous_shellExt {c : Rd d} {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ ≤ r₁)
    {φ : Rd d → ℝ} (hφ : Continuous φ) : Continuous (shellExt c r₁ r₂ φ) := by
  have h := continuous_if_le (f := fun _ : Rd d => r₂) (g := linfDist c)
    (f' := fun z => φ (clampBox c r₁ z)) (g' := radialExt c r₂ φ) continuous_const
    (continuous_linfDist c) (hφ.comp (continuous_clampBox c r₁)).continuousOn
    (continuous_radialExt hr₂ hφ).continuousOn fun z hz => ?_
  · exact h
  · have hzb : z ∈ cbox c r₁ := (linfDist_le_iff (hr₂.le.trans hr)).1 (hz ▸ hr)
    rw [clampBox_of_mem hzb, radialExt, ← hz, div_self hr₂.ne', one_smul, one_mul,
      add_sub_cancel]

/-- The extension agrees with `φ` on the closed shell. -/
theorem shellExt_eq_of_mem {c : Rd d} {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) {φ : Rd d → ℝ} {z : Rd d}
    (hz : z ∈ cbox c r₁ \ obox c r₂) : shellExt c r₁ r₂ φ z = φ z := by
  have h : r₂ ≤ linfDist c z := not_lt.1 fun h => hz.2 ((linfDist_lt_iff hr₂).1 h)
  rw [shellExt, ite_eq_left h, clampBox_of_mem hz.1]

/-- Clamping a point with `|z - c|_∞ ≥ r₂` to `B̄_{r₁}(c)` lands in the closed shell (`r₂ ≤ r₁`). -/
theorem clampBox_mem_shell {c z : Rd d} {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ ≤ r₁)
    (hz : r₂ ≤ linfDist c z) : clampBox c r₁ z ∈ cbox c r₁ \ obox c r₂ := by
  refine ⟨clampBox_mem c (hr₂.le.trans hr) z, fun h => ?_⟩
  have hz' : z ∉ obox c r₂ := fun h' => (not_lt.2 hz) ((linfDist_lt_iff hr₂).2 h')
  apply hz'
  intro i
  have hi : |clampBox c r₁ z i - c i| < r₂ := h i
  rw [clampBox_apply] at hi
  rw [abs_lt] at hi ⊢
  constructor
  · by_contra hlt
    push Not at hlt
    have : min (c i + r₁) (z i) = z i := min_eq_right (by linarith)
    rw [this] at hi
    have := le_max_left (c i - r₁) (z i)
    have := le_max_right (c i - r₁) (z i)
    by_cases hm : c i - r₁ ≤ z i
    · rw [max_eq_right hm] at hi
      linarith [hi.1]
    · rw [max_eq_left (le_of_not_ge hm)] at hi
      linarith [hi.1]
  · by_contra hlt
    push Not at hlt
    have h1 : c i + r₂ ≤ min (c i + r₁) (z i) := le_min (by linarith) (by linarith)
    have h2 : min (c i + r₁) (z i) ≤ max (c i - r₁) (min (c i + r₁) (z i)) := le_max_right _ _
    linarith [hi.2]

/-- The inner sphere `∂B_{r₂}(c)` lies in the closed shell (`r₂ ≤ r₁`). -/
theorem lsph_subset_shell {c : Rd d} {r₁ r₂ : ℝ} (hr : r₂ ≤ r₁) :
    lsph c r₂ ⊆ cbox c r₁ \ obox c r₂ :=
  fun _ hz => ⟨fun i => (hz.1 i).trans hr, hz.2⟩

/-! ## Locality of the across distance on the closed shell -/

/-- **The across distance is measurable for the field on the closed shell** `B̄_{r₁}(c) \ B_{r₂}(c)`
(`0 < r₂ < r₁`). -/
theorem measurable_acrossDist_comap_shell {Ω : Type*} {H : Rd d → Ω → ℝ}
    (hc : ∀ ω, Continuous fun z => H z ω) (ξ : ℝ) (c : Rd d) {r₁ r₂ : ℝ} (hr₂ : 0 < r₂)
    (hr : r₂ < r₁) :
    Measurable[MeasurableSpace.comap
        (fun ω (z : (cbox c r₁ \ obox c r₂ : Set (Rd d))) => H z ω) MeasurableSpace.pi]
      fun ω => acrossDist ξ (fun z => H z ω) c r₁ r₂ := by
  set Y : Ω → (cbox c r₁ \ obox c r₂ : Set (Rd d)) → ℝ := fun ω z => H z ω with hY
  let mΩ : MeasurableSpace Ω := MeasurableSpace.comap Y MeasurableSpace.pi
  have hev : ∀ z (hz : z ∈ cbox c r₁ \ obox c r₂), Measurable fun ω => H z ω := fun z hz =>
    (measurable_pi_apply (⟨z, hz⟩ : (cbox c r₁ \ obox c r₂ : Set (Rd d)))).comp
      (comap_measurable Y)
  set Ht : Rd d → Ω → ℝ := fun z ω => shellExt c r₁ r₂ (fun y => H y ω) z with hHt
  have hct : ∀ ω, Continuous fun z => Ht z ω := fun ω =>
    continuous_shellExt hr₂ hr.le (hc ω)
  have hmt : ∀ z, Measurable (Ht z) := by
    intro z
    by_cases hz : r₂ ≤ linfDist c z
    · have e : Ht z = fun ω => H (clampBox c r₁ z) ω := by
        funext ω
        simp only [hHt, shellExt, ite_eq_left hz]
      rw [e]
      exact hev _ (clampBox_mem_shell hr₂ hr.le hz)
    · by_cases hzc : z = c
      · have e : Ht z = fun _ => 0 := by
          funext ω
          rw [hHt]
          dsimp only
          rw [shellExt, ite_eq_right hz, hzc, linfDist_self, zero_div, zero_mul]
        rw [e]
        exact measurable_const
      · have e : Ht z = fun ω =>
            linfDist c z / r₂ * H (c + (r₂ / linfDist c z) • (z - c)) ω := by
          funext ω
          simp only [hHt, shellExt, ite_eq_right hz]
        rw [e]
        exact (hev _ (lsph_subset_shell hr.le (radial_mem_lsph hr₂ hzc))).const_mul _
  have heq : (fun ω => acrossDist ξ (fun z => H z ω) c r₁ r₂) =
      fun ω => acrossDist ξ (fun z => Ht z ω) c r₁ r₂ := by
    funext ω
    exact acrossDist_congr (hc ω) (hct ω) hr fun z hz =>
      (shellExt_eq_of_mem (φ := fun y => H y ω) hr₂ hz).symm
  rw [heq]
  exact measurable_acrossDist hct hmt ξ c r₁ r₂

end DGZ

end HigherDimLQGMetric
