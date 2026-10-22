import HigherDimLQGMetric.Sec6.Geometry
import HigherDimLQGMetric.Metric.WeylBridge
import HigherDimLQGMetric.Metric.Lemma21

/-!
# [S] §6: configuration coordinates versus Weyl-scaled metrics at `(z, r)`

Packet S6a. The configuration `config D₀ D̃₀ s r z` stores, on the unit-scale carrier `U = A_{1/2,5}`, the
normalized internal metrics `s⁻¹ D(z + ru, z + rv; z + rU)`. This file transfers lengths between the two
pictures (MA3 D-6.2, *Proof of (T)*, first paragraph: "the `U`-internal metrics of `D', D̃'` at `(z, r)` are
`s ×` the weighted configuration metrics"):

* `curveLengthWith_cfg`: for a curve `Q` in `U` and `E u v = s⁻¹ D₁(z+ru, z+rv; W)` (`W = A_{r/2,5r}(z)`),
  `len(Q; E) = s⁻¹ len(z + rQ; D₁)`;
* `weightedLengthWith_cfg`: if `D' = e^{ξ g}·D₁` and the weight `w` of `U` matches `e^{ξ g}` along the
  realized curve, then `∫_Q w ds_E = s⁻¹ len(z + rQ; D')` (no hypothesis on `D₁`; [S] Lemma 2.1(c) through
  M1's `curveLength_eq_weightedLength_of_weyl`);
* `internal_le_weylDistOnWith`: `D'(z+rx, z+ry; A_{r,3r}(z)) ≤ s · (w·E)(x, y; A_{1,3})`;
* `exists_cfg_lift`, `len_affine_reparam`: a curve of `A_{r,3r}(z)` on `[σ₁, σ₂]` as a configuration curve on
  `[0, 1]`, and the affine reparametrization of lengths.

All helpers live in the namespace `HigherDimLQGMetric.S6a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

namespace S6a

open Set Metric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-! ### `ℝ≥0∞` normalizations -/

theorem ofReal_mul_ofReal_inv_mul {s : ℝ} (hs : 0 < s) (X : ℝ≥0∞) :
    ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * X) = X := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul]

theorem ofReal_inv_mul_ofReal_mul {s : ℝ} (hs : 0 < s) (X : ℝ≥0∞) :
    ENNReal.ofReal s⁻¹ * (ENNReal.ofReal s * X) = X := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le), inv_mul_cancel₀ hs.ne',
    ENNReal.ofReal_one, one_mul]

/-- `ofReal (a s) = ofReal s * ofReal a` for `s > 0`. -/
theorem ofReal_mul_scale {s : ℝ} (hs : 0 < s) (a : ℝ) :
    ENNReal.ofReal (a * s) = ENNReal.ofReal s * ENNReal.ofReal a := by
  rw [mul_comm a s, ENNReal.ofReal_mul hs.le]

/-! ### Realized curves -/

theorem continuousOn_realize {r : ℝ} {z : Rd d} {Q : ℝ → ↥(ann (0 : Rd d) (1 / 2) 5)}
    {S : Set ℝ} (hQ : ContinuousOn Q S) : ContinuousOn (fun t => r • (Q t : Rd d) + z) S :=
  ((continuous_subtype_val.comp_continuousOn hQ).const_smul r).add continuousOn_const

/-- **Unweighted transfer.** `len(Q; E) = s⁻¹ len(z + rQ; D₁)` for the configuration coordinate `E` of
`D₁`. -/
theorem curveLengthWith_cfg {D₁ : ContMetric d} {s r : ℝ} (hr : 0 < r) {z : Rd d}
    {E : ↥(ann (0 : Rd d) (1 / 2) 5) → ↥(ann (0 : Rd d) (1 / 2) 5) → ℝ≥0∞}
    (hE : ∀ u v, E u v = ENNReal.ofReal s⁻¹ *
      D₁.internal (ann z (r / 2) (5 * r)) (r • (u : Rd d) + z) (r • (v : Rd d) + z))
    {Q : ℝ → ↥(ann (0 : Rd d) (1 / 2) 5)} {α β : ℝ} (hQ : ContinuousOn Q (Icc α β)) :
    curveLengthWith E Q α β =
      ENNReal.ofReal s⁻¹ * D₁.len (fun t => r • (Q t : Rd d) + z) α β := by
  have h1 : curveLengthWith E Q α β = curveLengthWith (fun x y => ENNReal.ofReal s⁻¹ *
      D₁.internal (ann z (r / 2) (5 * r)) x y) (fun t => r • (Q t : Rd d) + z) α β := by
    unfold curveLengthWith
    congr 1
    funext u v
    exact hE _ _
  rw [h1, curveLengthWith_const_mul, D₁.curveLengthWith_internal (continuousOn_realize hQ)
    (fun t _ => affine_mem_cfg hr z (Q t).2)]

/-- **Weighted transfer** ([S] Lemma 2.1(c) at `(z, r)`). If `D' = e^{ξ g}·D₁` and `w(Q t) = e^{ξ g(z + r Q t)}`
along the curve, then `∫_Q w ds_E = s⁻¹ len(z + rQ; D')`. -/
theorem weightedLengthWith_cfg {D₁ D' : ContMetric d} {ξ : ℝ} {g : C(Rd d, ℝ)}
    (hD' : IsWeylOf ξ g D₁ D') {s r : ℝ} (hr : 0 < r) {z : Rd d}
    {E : ↥(ann (0 : Rd d) (1 / 2) 5) → ↥(ann (0 : Rd d) (1 / 2) 5) → ℝ≥0∞}
    (hE : ∀ u v, E u v = ENNReal.ofReal s⁻¹ *
      D₁.internal (ann z (r / 2) (5 * r)) (r • (u : Rd d) + z) (r • (v : Rd d) + z))
    {w : ↥(ann (0 : Rd d) (1 / 2) 5) → ℝ} {Q : ℝ → ↥(ann (0 : Rd d) (1 / 2) 5)} {α β : ℝ}
    (hQ : ContinuousOn Q (Icc α β))
    (hw : ∀ t ∈ Icc α β, w (Q t) = Real.exp (ξ * g (r • (Q t : Rd d) + z))) :
    weightedLengthWith E w Q α β =
      ENNReal.ofReal s⁻¹ * D'.len (fun t => r • (Q t : Rd d) + z) α β := by
  have hPc : ContinuousOn (fun t => r • (Q t : Rd d) + z) (Icc α β) := continuousOn_realize hQ
  rw [ContMetric.len_def, curveLength_eq_weightedLength_of_weyl hD' hPc, weightedLength,
    ← partitionSup_const_mul, weightedLengthWith]
  refine partitionSup_congr fun u v hu _ hv => ?_
  have hsub : Icc u v ⊆ Icc α β := Icc_subset_Icc hu hv
  rw [curveLengthWith_cfg hr hE (hQ.mono hsub)]
  have hinf : infAlong w Q u v =
      infAlong (D₁.weylWeight ξ g) (D₁.pt ∘ fun t => r • (Q t : Rd d) + z) u v := by
    unfold infAlong
    refine iInf_congr fun t => iInf_congr fun ht => ?_
    rw [hw t (hsub ht)]
    rfl
  rw [hinf, ContMetric.len_def, mul_left_comm]

/-- **(T2) transfer.** The internal distance in `A_{r,3r}(z)` of `D' = e^{ξ g}·D₁` is at most `s` times
the weighted configuration distance confined to `A_{1,3}`, if `w = e^{ξ g(z + r·)}` on `A_{1,3}`. -/
theorem internal_le_weylDistOnWith {D₁ D' : ContMetric d} {ξ : ℝ} {g : C(Rd d, ℝ)}
    (hD' : IsWeylOf ξ g D₁ D') {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z : Rd d}
    {E : ↥(ann (0 : Rd d) (1 / 2) 5) → ↥(ann (0 : Rd d) (1 / 2) 5) → ℝ≥0∞}
    (hE : ∀ u v, E u v = ENNReal.ofReal s⁻¹ *
      D₁.internal (ann z (r / 2) (5 * r)) (r • (u : Rd d) + z) (r • (v : Rd d) + z))
    {w : ↥(ann (0 : Rd d) (1 / 2) 5) → ℝ}
    (hw : ∀ u : ↥(ann (0 : Rd d) (1 / 2) 5), (u : Rd d) ∈ ann (0 : Rd d) 1 3 →
      w u = Real.exp (ξ * g (r • (u : Rd d) + z)))
    (x y : ↥(ann (0 : Rd d) (1 / 2) 5)) :
    D'.internal (ann z r (3 * r)) (r • (x : Rd d) + z) (r • (y : Rd d) + z) ≤
      ENNReal.ofReal s * weylDistOnWith E w {u | (u : Rd d) ∈ ann (0 : Rd d) 1 3} x y := by
  have key : ENNReal.ofReal s⁻¹ *
      D'.internal (ann z r (3 * r)) (r • (x : Rd d) + z) (r • (y : Rd d) + z) ≤
      weylDistOnWith E w {u | (u : Rd d) ∈ ann (0 : Rd d) 1 3} x y := by
    unfold weylDistOnWith
    refine le_iInf fun Q => le_iInf fun hQc => le_iInf fun hQ0 => le_iInf fun hQ1 =>
      le_iInf fun hQS => ?_
    rw [weightedLengthWith_cfg hD' hr hE hQc (fun t ht => hw (Q t) (hQS ht))]
    refine mul_le_mul' le_rfl ?_
    have h := D'.internal_le_len (U := ann z r (3 * r)) zero_le_one (continuousOn_realize hQc)
      (fun t ht => affine_mem_ann13 hr z (hQS ht))
    simpa only [hQ0, hQ1] using h
  calc D'.internal (ann z r (3 * r)) (r • (x : Rd d) + z) (r • (y : Rd d) + z)
      = ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ *
          D'.internal (ann z r (3 * r)) (r • (x : Rd d) + z) (r • (y : Rd d) + z)) :=
        (ofReal_mul_ofReal_inv_mul hs _).symm
    _ ≤ ENNReal.ofReal s * weylDistOnWith E w {u | (u : Rd d) ∈ ann (0 : Rd d) 1 3} x y :=
        mul_le_mul' le_rfl key

/-! ### Lifting curves of `A_{r,3r}(z)` to configuration curves -/

/-- A curve of `A_{r,3r}(z)` on `[σ₁, σ₂]` is the realization `z + rQ` of a continuous configuration curve
`Q` on `[0, 1]` (affinely reparametrized), with values in `A_{1,3}`. -/
theorem exists_cfg_lift {P : ℝ → Rd d} {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (hP : ContinuousOn P (Icc σ₁ σ₂)) {r : ℝ} (hr : 0 < r) {z : Rd d}
    (hPA : ∀ t ∈ Icc σ₁ σ₂, P t ∈ ann z r (3 * r)) :
    ∃ Q : ℝ → ↥(ann (0 : Rd d) (1 / 2) 5), Continuous Q ∧
      (∀ t ∈ Icc (0 : ℝ) 1, r • (Q t : Rd d) + z = P (σ₁ + t * (σ₂ - σ₁))) ∧
      (∀ t, (Q t : Rd d) ∈ ann (0 : Rd d) 1 3) := by
  let φ : ℝ → ℝ := fun t => σ₁ + (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) * (σ₂ - σ₁)
  have hφc : Continuous φ :=
    continuous_const.add ((continuous_subtype_val.comp continuous_projIcc).mul continuous_const)
  have hφmem : ∀ t, φ t ∈ Icc σ₁ σ₂ := by
    intro t
    have h0 : (0 : ℝ) ≤ (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) :=
      (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.1
    have h1 : (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) ≤ 1 :=
      (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.2
    have hd : 0 ≤ σ₂ - σ₁ := sub_nonneg.2 hσ
    have hm1 : 0 ≤ (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) * (σ₂ - σ₁) := mul_nonneg h0 hd
    have hm2 : (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) * (σ₂ - σ₁) ≤ σ₂ - σ₁ :=
      mul_le_of_le_one_left hd h1
    exact ⟨by simp only [φ]; linarith, by simp only [φ]; linarith⟩
  have hA : ∀ t, r⁻¹ • (P (φ t) - z) ∈ ann (0 : Rd d) 1 3 := fun t =>
    pull_mem_ann13 hr z (hPA _ (hφmem t))
  refine ⟨fun t => ⟨r⁻¹ • (P (φ t) - z), ann13_subset_cfg (hA t)⟩, ?_, ?_, fun t => hA t⟩
  · have hPφ : Continuous fun t => P (φ t) := hP.comp_continuous hφc hφmem
    exact Continuous.subtype_mk ((hPφ.sub continuous_const).const_smul r⁻¹) _
  · intro t ht
    change r • (r⁻¹ • (P (φ t) - z)) + z = P (σ₁ + t * (σ₂ - σ₁))
    rw [affine_pull hr.ne']
    simp only [φ, Set.projIcc_of_mem zero_le_one ht]

/-- Affine reparametrization of lengths: `len(P(σ₁ + ·(σ₂ − σ₁)); [u, v]) = len(P; [φ u, φ v])`. -/
theorem len_affine_reparam (D : ContMetric d) (P : ℝ → Rd d) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    {u v : ℝ} (huv : u ≤ v) :
    D.len (fun t => P (σ₁ + t * (σ₂ - σ₁))) u v =
      D.len P (σ₁ + u * (σ₂ - σ₁)) (σ₁ + v * (σ₂ - σ₁)) := by
  have hmono : MonotoneOn (fun t : ℝ => σ₁ + t * (σ₂ - σ₁)) (Icc u v) := by
    intro a _ b _ hab
    have hd : 0 ≤ σ₂ - σ₁ := sub_nonneg.2 hσ
    simp only
    nlinarith
  have hcont : ContinuousOn (fun t : ℝ => σ₁ + t * (σ₂ - σ₁)) (Icc u v) := by fun_prop
  rw [ContMetric.len_def, ContMetric.len_def]
  exact curveLength_comp_of_continuousOn_monotoneOn (D.pt ∘ P) huv hcont hmono

end S6a

end HigherDimLQGMetric
