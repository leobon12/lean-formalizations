import QuantumZipper.Proofs.Section5.Prop16PalmABMeas
import QuantumZipper.Proofs.Zipper.D3PlusN2Bridge

/-!
# Proposition 1.6, Palm zoom: masked zoom coordinates (decision D30, part 1)

Node B of `Prop16PalmZoom.lean` (`Prop16PalmIdStmt`) compares the laws of the *full* coordinate
vectors `coords (canonicalOn …)`, which read the field at dyadic folded circles anywhere in the
plane. Pulled back by the canonical rescaling and the translation, most of them leave `closure D`,
where `IsMixedGFF` leaves the field unconstrained and `mixedGreenSample` is a `limUnder` junk
value; node B is false as stated (P16-PALM-AB counterexample). Decision D30: mask them.

A coordinate `i` (folded circle of centre `cᵢ`, radius `rᵢ`, reach `‖cᵢ‖ + rᵢ`) of the canonical
zoom at the point `t` with scale `s` is kept iff `0 < s` and the half-disc of radius
`2 s (‖cᵢ‖ + rᵢ)` about `t` stays away from `Hbar \ (D ∪ (a,b))`
(`2 s (‖cᵢ‖ + rᵢ) < infDist t (Hbar \ (D ∪ (a,b)))`); otherwise it is replaced by `0`. The factor
`2` leaves room for the regularization (`evalReg`) of the translated/rescaled readings.

Main result: `tendsto_tvDist_palmMask` — under `prop16Q`, the laws of the unmasked and masked
local coordinates `locCoords R` are at total variation distance `→ 0` as `C → ∞`. Indeed they
agree unless `¬(0 < s_C ∧ 2 s_C R < infDist t K)`; the local scale `s_C → 0` in probability
(`prop16_hsc0`), and `infDist t K > 0` for `t ∈ (a,b)` by the half-disc hypothesis of
Prop. 1.6 (`K3.Prop16Geometry`), so the bad event has vanishing `Q`-measure (continuity from above
in the threshold `δ`).

Source: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25), which zooms in at a boundary
point and never reads the field outside `D`. The masking and this estimate are own elementary
bookkeeping (no published counterpart; the paper works with the continuum field directly).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization

/-! ## 1. The mask -/

/-- The part of the closed upper half-plane outside `D ∪ (a,b)`: where the field is not read. -/
def palmOutside (D : Set ℂ) (a b : ℝ) : Set ℂ := Hbar \ (D ∪ realSet (Ioo a b))

/-- The distance from the boundary point `t` to `Hbar \ (D ∪ (a,b))`. -/
def palmGap (D : Set ℂ) (a b t : ℝ) : ℝ := infDist (t : ℂ) (palmOutside D a b)

/-- The reach `‖cᵢ‖ + rᵢ` of the `i`-th dyadic folded circle (so `inBall R i ↔ reach ≤ R`). -/
def coordReach (i : ℕ) : ℝ := ‖(dyadicIndex i).1‖ + radius (dyadicIndex i).2

/-- Coordinate `i` of the canonical zoom at `t` with scale `s` is kept. -/
def PalmKeep (D : Set ℂ) (a b s t : ℝ) (i : ℕ) : Prop :=
  0 < s ∧ 2 * s * coordReach i < palmGap D a b t

open Classical in
/-- The masked coordinate vector: coordinates whose rescaled circle may leave `D ∪ (a,b)` are
replaced by `0`. -/
def maskCoords (D : Set ℂ) (a b s t : ℝ) (y : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if PalmKeep D a b s t i then y i else 0

/-- The local scale of the canonical zoom at `p = (ω, t)`. -/
def palmScale (γ C : ℝ) (D : Set ℂ) (h0 : ℂ → ℝ) {Ω : Type} (X : Ω → FieldSample)
    (p : Ω × ℝ) : ℝ :=
  scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)

/-- The masked canonical zoom coordinates at `p = (ω, t)`. -/
def palmCanonMask (γ C : ℝ) (D : Set ℂ) (a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type}
    (X : Ω → FieldSample) (p : Ω × ℝ) : ℕ → ℝ :=
  maskCoords D a b (palmScale γ C D h0 X p) p.2 (palmCanonCoords γ C D h0 X p)

/-- The masked canonical zoom coordinates at the fixed point `x` of the Palm-shifted mixed field
`X + (γ/2) G_D(x, ·)`. -/
def palmFixedMask (γ C : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type}
    (X : Ω → FieldSample) (x : ℝ) (ω : Ω) : ℕ → ℝ :=
  palmCanonMask γ C D a b h0 (palmMixedField γ D (realSet (Icc c d)) X x) (ω, x)

theorem measurable_maskCoords (D : Set ℂ) (a b : ℝ) :
    Measurable fun q : ℝ × ℝ × (ℕ → ℝ) => maskCoords D a b q.1 q.2.1 q.2.2 := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  have hg : Measurable fun q : ℝ × ℝ × (ℕ → ℝ) => palmGap D a b q.2.1 :=
    (continuous_infDist_pt _).measurable.comp
      (Complex.continuous_ofReal.measurable.comp (measurable_fst.comp measurable_snd))
  have hS : MeasurableSet {q : ℝ × ℝ × (ℕ → ℝ) | PalmKeep D a b q.1 q.2.1 i} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt ((measurable_const.mul measurable_fst).mul measurable_const) hg)
  exact Measurable.ite hS ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
    measurable_const

theorem aemeasurable_maskCoords {α : Type*} [MeasurableSpace α] {μ : Measure α} (D : Set ℂ)
    (a b : ℝ) {s t : α → ℝ} {y : α → ℕ → ℝ} (hs : AEMeasurable s μ) (ht : AEMeasurable t μ)
    (hy : AEMeasurable y μ) : AEMeasurable (fun p => maskCoords D a b (s p) (t p) (y p)) μ :=
  (measurable_maskCoords D a b).comp_aemeasurable (hs.prodMk (ht.prodMk hy))

/-- The mask does not change the local coordinates on the event `0 < s ∧ 2 s R < gap`. -/
theorem locCoords_maskCoords {D : Set ℂ} {a b s t : ℝ} {R : ℕ} (hs : 0 < s)
    (hR : 2 * s * R < palmGap D a b t) (y : ℕ → ℝ) :
    locCoords R (maskCoords D a b s t y) = locCoords R y := by
  classical
  funext i
  by_cases hi : inBall R i
  · have hk : PalmKeep D a b s t i := by
      refine ⟨hs, lt_of_le_of_lt ?_ hR⟩
      have : coordReach i ≤ R := hi
      have h2s : 0 ≤ 2 * s := by positivity
      exact mul_le_mul_of_nonneg_left this h2s
    simp only [locCoords, hi, ite_true, maskCoords, hk]
  · simp only [locCoords, hi, ite_false]

/-- The gap is positive at every point of `(a,b)` (half-disc hypothesis of Prop. 1.6). -/
theorem palmGap_pos {D : Set ℂ} {c d a b t : ℝ} (hDH : D ⊆ H)
    (hhd : ∀ t ∈ Ioo c d, ∃ r > 0, ball (t : ℂ) r ∩ H ⊆ D) (hca : c ≤ a) (hbd : b ≤ d)
    (ht : t ∈ Ioo a b) : 0 < palmGap D a b t := by
  obtain ⟨r, hr, hrD⟩ := hhd t ⟨lt_of_le_of_lt hca ht.1, lt_of_lt_of_le ht.2 hbd⟩
  have hne : (palmOutside D a b).Nonempty := by
    refine ⟨(b : ℂ), ?_, ?_⟩
    · show (0 : ℝ) ≤ (b : ℂ).im; simp
    · rintro (h | ⟨u, hu, hub⟩)
      · have : 0 < ((b : ℂ)).im := hDH h
        simp at this
      · have : u = b := Complex.ofReal_injective hub
        exact (lt_irrefl b) (this ▸ hu.2)
  set r' := min r (min (t - a) (b - t)) with hr'
  have hr'0 : 0 < r' := lt_min hr (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  refine lt_of_lt_of_le hr'0 ((le_infDist hne).2 fun z hz => ?_)
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨hzH, hzU⟩ := hz
  have hzb : z ∈ ball (t : ℂ) r := by
    rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hlt (min_le_left _ _)
  rcases (show (0 : ℝ) ≤ z.im from hzH).lt_or_eq with him | him
  · exact hzU (Or.inl (hrD ⟨hzb, him⟩))
  · refine hzU (Or.inr ⟨z.re, ?_, ?_⟩)
    · have hd : |t - z.re| < min (t - a) (b - t) := by
        have e : dist (t : ℂ) z = |t - z.re| := by
          rw [Complex.dist_eq, ← Complex.re_add_im z, ← him]
          simp only [add_zero, zero_mul, Complex.ofReal_zero]
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
        rw [← e]; exact lt_of_lt_of_le hlt (min_le_right _ _)
      rw [abs_lt] at hd
      constructor <;> linarith [min_le_left (t - a) (b - t), min_le_right (t - a) (b - t)]
    · apply Complex.ext <;> simp [him.symm]

/-! ## 2. Total variation cost of the mask -/

/-- Laws of the unmasked and masked local coordinates differ by at most the probability that
the mask is active inside `closedBall 0 R`. -/
theorem tvDist_locCoords_mask_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : Set ℂ)
    (a b : ℝ) {s t : α → ℝ} {y : α → ℕ → ℝ} (hs : AEMeasurable s μ) (ht : AEMeasurable t μ)
    (hy : AEMeasurable y μ) (R : ℕ) :
    tvDist (μ.map fun p => locCoords R (y p))
      (μ.map fun p => locCoords R (maskCoords D a b (s p) (t p) (y p))) ≤
      μ {p | ¬ (0 < s p ∧ 2 * s p * R < palmGap D a b (t p))} := by
  refine D3Plus.tvDist_map_le_of_ae_eq_off ((measurable_locCoords R).comp_aemeasurable hy)
    ((measurable_locCoords R).comp_aemeasurable (aemeasurable_maskCoords D a b hs ht hy)) _
    (ae_of_all _ fun p hp => ?_)
  simp only [mem_ofPred_eq, not_not] at hp
  exact (locCoords_maskCoords hp.1 hp.2 (y p)).symm

end Prop16Asm

end QuantumZipper
