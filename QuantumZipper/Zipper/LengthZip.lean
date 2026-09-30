import QuantumZipper.Zipper.Maps

/-!
# The constructive length zipper `Z^LEN_ℓ`

Sheffield, *Conformal weldings of random surfaces*, Theorem 1.8; `STATEMENT_SPEC.md` A13;
audit AUDIT-1 §3 (`audits/2026-09-26-statements/README.md`).

`Zipper/Maps.lean` defines the unzipping map `Z^LEN_{−ℓ}` (`zipLenDown`). An earlier
choice-based `zipLenUp` (a choice among *all* preimages, not pinned down) was removed
(AUDIT-1 §3.1). This file
defines `Z^LEN_ℓ`, `ℓ ≥ 0`, **constructively**, in the same way as `zipCapUp` defines
`Z^CAP_t`:

1. `lenWeldPoint γ x ℓ` is the point `x₋ ≤ 0` with `ν_x[x₋,0] = ℓ` (`ν_x = qBoundaryMeasure γ x`).
2. A *length-welding driver* (`IsLenWeldingDriver`) is a pair `(T, W')`: a reverse Loewner
   driver `W'` and a capacity time `T` whose reverse hull is a simple curve, whose negative base
   preimage is `0₋ = x₋`, and whose welding homeomorphism is `R_x` on `[x₋,0]`. It welds the
   boundary arc `[x₋,0]` to `[0,x₊]` (`x₊ = R_x(x₋)`, so `ν_x[0,x₊] = ℓ` as well) by quantum
   length. `lenWeldDriver` chooses one (Theorem 1.8 (1) asserts that one exists a.s. and that
   `T` and `W'|[0,T]` are a.s. unique; only these are used, `zipWeldUp_congr`).
3. `zipWeldUp γ T W' c` zips the configuration `c` up along `(T, W')` without rescaling. It is
   literally `zipCapUp` with the given driver in place of `weldDriver` (`zipCapUp_eq_zipWeldUp`).
4. `canonConfig γ` rescales a configuration by (1.8) to unit quantum area in `B₁(0)` and
   transforms its driver by Brownian scaling.
5. `zipLenUpC γ ℓ := canonConfig γ ∘ zipWeldUp γ T W'` with `(T, W') = lenWeldDriver`, and
   `zipLenC γ ℓ` is `zipLenUpC γ ℓ` for `ℓ ≥ 0` and `zipLenDown γ (−ℓ)` for `ℓ < 0`.

## Rescaling convention (verification)

`rescale x Q a = x(a·) + Q log a`, so a point `w` of the old picture is the point `w/a` of the
new one, and the new curve is (old curve)`/a`. Since `hcap(K/a) = hcap(K)/a²`, the Loewner
maps satisfy `g^{η/a}_s(ζ) = g^η_{a²s}(aζ)/a`, so the driver becomes `s ↦ V(a²s)/a`. This is
`canonConfig`. `zipLenDown γ ℓ c` is `canonConfig γ (zipCapDown γ t' c)`, with `t'` the
unzipping time (`zipLenDown_eq_canonConfig`, proved below), so both directions of `Z^LEN` use
the same convention.

Round trip `Z^LEN_{−ℓ} ∘ Z^LEN_ℓ` (by hand). Let `c = (Y, W)` with `Y` canonical, `(T, W')` the
true length-welding driver, `f = revMap W' T`, `V` the concatenated driver of `zipWeldUp`, and
`b = scaleParam γ (Y ∘ f⁻¹ + Q log|(f⁻¹)'|)`. Then `zipLenUpC` has driver `W₁ s = V(b²s)/b`. Its
curve begins with `K_T/b`, of capacity time `T/b²`. Unzipping it returns the field
`Y(b·) + Q log b`, whose `ν`-length of `[0₋/b, 0]` is `ν_Y[x₋,0] = ℓ`. Hence the unzipping time
is `t' = T/b²` and the unzipped scale is `a = scaleParam γ (Y(b·) + Q log b) = 1/b`. The
resulting driver is
`(W₁(t' + a²s) − W₁(t'))/a = V(T + s) − V(T) = (W s − W' T) − (W' 0 − W' T) = W s`.

Round trip `Z^LEN_ℓ ∘ Z^LEN_{−ℓ}` (by hand). Let `t'` be the unzipping time, `x'` the unzipped
field, `a = scaleParam γ x'`, and `W₂ s = (W(t' + a²s) − W t')/a`. The length-welding driver of
`canonical γ x'` is `T = t'/a²` with `W' s = (W(t' − a²s) − W t')/a`: it zips `η[0,t']/a`, and
`f⁻¹ = f_{t'}(a·)/a`. The zipped field is `Y(a·) + Q log a`, so `b = 1/a`. For `s ≤ t'` the
driver is `a·V(s/a²) = a·(W'(T − s/a²) − W' T) = W s`. For `s > t'` it is
`a·(W₂(s/a² − T) − W' T) = W s`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

/-- Canonicalization of a configuration `c = (x, V)` (Sheffield (1.8) together with Brownian
scaling): with `a = scaleParam γ x`, the field becomes `canonical γ x = x(a·) + Q log a`, which
gives `B₁(0) ∩ ℍ` unit quantum area, and the curve becomes (old curve)`/a`. Its driver is
`s ↦ V(a² s)/a`, normalized to `V 0 / a` for `s ≤ 0` (this is `0` for the drivers produced by
`zipWeldUp` and `zipCapDown`). -/
def canonConfig (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) : FieldSample × (ℝ → ℝ) :=
  (canonical γ c.1, fun s => c.2 (scaleParam γ c.1 ^ 2 * max s 0) / scaleParam γ c.1)

/-- Sanity check of the rescaling convention: the unzipping map `Z^LEN_{−ℓ}` of `Maps.lean` is
the canonicalization (`canonConfig`) of the capacity unzipping `zipCapDown` at the first
capacity time `t'` at which the quantum length seen from `D₁` reaches `ℓ`. -/
theorem zipLenDown_eq_canonConfig (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    zipLenDown γ ℓ c = canonConfig γ
      (zipCapDown γ (sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengths γ c s).1}) c) := by
  simp only [zipLenDown, canonConfig, zipCapDown, canonical]
  refine Prod.ext rfl ?_
  funext s
  simp only
  rw [max_eq_left (mul_nonneg (sq_nonneg _) (le_max_right s 0))]

/-- The left welding point for quantum length `ℓ`: `sup {s ≤ 0 : ℓ ≤ ν_x[s,0]}`, where
`ν_x = qBoundaryMeasure γ x`. When `ν_x` is atomless, charges every nondegenerate interval and
has infinite mass on `(−∞,0]` (a.s. the case for the fields of Theorem 1.8), this is the unique
`x₋ ≤ 0` with `ν_x[x₋,0] = ℓ`. For `ℓ ≤ 0` it is `0` (`lenWeldPoint_of_nonpos`). If no such point
exists the set is empty and the value is the junk `sSup ∅ = 0`. -/
def lenWeldPoint (γ : ℝ) (x : FieldSample) (ℓ : ℝ) : ℝ :=
  sSup {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ qBoundaryMeasure γ x (Icc s 0)}

/-- `p = (T, W')` is a **length-welding driver** of the field `x` for quantum length `ℓ`: `T ≥ 0`,
`W'` is continuous with `W' 0 = 0`, the reverse hull `revHull W' T` is the hull of a simple curve
(or `T = 0`, where nothing is zipped; see `IsWeldingDriver`), its negative base preimage
`0₋ = zeroMinus W' T` is the left welding point `lenWeldPoint γ x ℓ`, and its welding
homeomorphism agrees with `R_x = weldHomR γ x` on `[0₋,0]`. So the reverse flow `revMap W' T`
welds `[x₋,0]` to `[0,R_x(x₋)]` by quantum length, and each side has quantum length `ℓ`. Only
`T` and `W'|[0,T]` matter (`zipWeldUp_congr`). This is `IsWeldingDriver` with the time chosen
by quantum length instead of capacity (`isLenWeldingDriver_iff`). -/
def IsLenWeldingDriver (γ : ℝ) (x : FieldSample) (ℓ : ℝ) (p : ℝ × (ℝ → ℝ)) : Prop :=
  0 ≤ p.1 ∧ Continuous p.2 ∧ p.2 0 = 0 ∧ (p.1 = 0 ∨ IsSimpleCurveHull (revHull p.2 p.1)) ∧
    zeroMinus p.2 p.1 = lenWeldPoint γ x ℓ ∧
    ∀ s ∈ Icc (zeroMinus p.2 p.1) 0, weldingHom p.2 p.1 s = weldHomR γ x s

/-- A length-welding driver is a capacity-welding driver (`IsWeldingDriver`) at a nonnegative
time whose negative base preimage is the length-`ℓ` welding point. -/
theorem isLenWeldingDriver_iff {γ : ℝ} {x : FieldSample} {ℓ : ℝ} {p : ℝ × (ℝ → ℝ)} :
    IsLenWeldingDriver γ x ℓ p ↔
      0 ≤ p.1 ∧ IsWeldingDriver γ x p.1 p.2 ∧ zeroMinus p.2 p.1 = lenWeldPoint γ x ℓ := by
  unfold IsLenWeldingDriver IsWeldingDriver
  tauto

/-- The length-welding driver of `x` for quantum length `ℓ`, chosen by `Classical.epsilon`
among the `IsLenWeldingDriver γ x ℓ` pairs (junk if there is none). In the setting of Theorem 1.8
it exists a.s., and `T` and `W'|[0,T]` are a.s. unique (Theorem 1.8 (1)); nothing else about the
choice is used. -/
def lenWeldDriver (γ : ℝ) (x : FieldSample) (ℓ : ℝ) : ℝ × (ℝ → ℝ) :=
  Classical.epsilon (IsLenWeldingDriver γ x ℓ)

theorem lenWeldDriver_spec {γ : ℝ} {x : FieldSample} {ℓ : ℝ}
    (h : ∃ p, IsLenWeldingDriver γ x ℓ p) : IsLenWeldingDriver γ x ℓ (lenWeldDriver γ x ℓ) :=
  Classical.epsilon_spec h

/-- Zipping the configuration `c = (x, W)` up along the reverse flow `f = revMap W' T`, without
rescaling. The field is `h ∘ f⁻¹ + Q log|(f⁻¹)'|` (`Q = Qc γ`). The driver traces the zipped
curve `K_T` from `0` with the time-reversed driver `W'(T − s) − W' T` for `s ∈ [0,T]`, then the
image `f(η)` of the old curve with driver `W (s − T) − W' T` for `s ≥ T`. It is normalized to
`0` on `(−∞,0]`. This is the formula of `zipCapUp` (see the sign verification in
`Zipper/Maps.lean`) with an arbitrary driver in place of `weldDriver`. -/
def zipWeldUp (γ T : ℝ) (W' : ℝ → ℝ) (c : FieldSample × (ℝ → ℝ)) : FieldSample × (ℝ → ℝ) :=
  (coordChange c.1 (revMapInv W' T) (Qc γ),
    fun s => if s ≤ T then W' (T - max s 0) - W' T else c.2 (s - T) - W' T)

/-- `zipCapUp` is `zipWeldUp` along the capacity welding driver `weldDriver`. -/
theorem zipCapUp_eq_zipWeldUp (γ t : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    zipCapUp γ t c = zipWeldUp γ t (weldDriver γ c.1 t) c := rfl

/-- The length quantum zipper `Z^LEN_ℓ`, `ℓ ≥ 0` (Theorem 1.8), defined constructively: zip up
along the length-welding driver `(T, W') = lenWeldDriver γ c.1 ℓ` (`zipWeldUp`), then
canonicalize by (1.8) with Brownian scaling of the driver (`canonConfig`). With
`b = scaleParam γ (h ∘ f⁻¹ + Q log|(f⁻¹)'|)`, the field is
`canonical γ (coordChange c.1 (revMapInv W' T) Q)` and the driver is `s ↦ V(b² s)/b`, where
`V` is the concatenated driver of `zipWeldUp`. -/
def zipLenUpC (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : FieldSample × (ℝ → ℝ) :=
  canonConfig γ (zipWeldUp γ (lenWeldDriver γ c.1 ℓ).1 (lenWeldDriver γ c.1 ℓ).2 c)

/-- The length quantum zipper `Z^LEN_ℓ` of Theorem 1.8, constructive version: zip up by quantum
length `ℓ` (`zipLenUpC`) for `ℓ ≥ 0`, and unzip (`zipLenDown`) by `−ℓ` for `ℓ < 0`. -/
def zipLenC (γ ℓ : ℝ) : FieldSample × (ℝ → ℝ) → FieldSample × (ℝ → ℝ) :=
  if 0 ≤ ℓ then zipLenUpC γ ℓ else zipLenDown γ (-ℓ)

theorem zipLenC_of_nonneg {γ ℓ : ℝ} (hℓ : 0 ≤ ℓ) : zipLenC γ ℓ = zipLenUpC γ ℓ := by
  simp only [zipLenC, hℓ, ↓reduceIte]

theorem zipLenC_of_neg {γ ℓ : ℝ} (hℓ : ℓ < 0) : zipLenC γ ℓ = zipLenDown γ (-ℓ) := by
  simp only [zipLenC, not_le.mpr hℓ, ↓reduceIte]

/-- For `ℓ ≤ 0` the left welding point is `0`. -/
theorem lenWeldPoint_of_nonpos {γ : ℝ} {x : FieldSample} {ℓ : ℝ} (hℓ : ℓ ≤ 0) :
    lenWeldPoint γ x ℓ = 0 := by
  have : {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ qBoundaryMeasure γ x (Icc s 0)} = Iic 0 := by
    ext s
    simp [ENNReal.ofReal_eq_zero.2 hℓ]
  rw [lenWeldPoint, this, csSup_Iic]

/-- `revMap W T` depends only on `W|[0,T]`. -/
theorem revMap_congr_lenZip {W W' : ℝ → ℝ} {T : ℝ} (h : EqOn W W' (Icc 0 T)) :
    revMap W T = revMap W' T := by
  funext z
  have hP : IsReverseSol W z T = IsReverseSol W' z T := by
    funext u
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun t ht => by rw [← h ht]; exact h2 t ht⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun t ht => by rw [h ht]; exact h2 t ht⟩
  unfold revMap
  rw [hP]

/-- The zipped configuration depends on the driver only through `W'|[0,T]`. -/
theorem zipWeldUp_congr {γ T : ℝ} {W₁ W₂ : ℝ → ℝ} (hT : 0 ≤ T) (h : EqOn W₁ W₂ (Icc 0 T))
    (c : FieldSample × (ℝ → ℝ)) : zipWeldUp γ T W₁ c = zipWeldUp γ T W₂ c := by
  have hinv : revMapInv W₁ T = revMapInv W₂ T := by
    unfold revMapInv
    rw [revMap_congr_lenZip h]
  have hTT : W₁ T = W₂ T := h ⟨hT, le_rfl⟩
  simp only [zipWeldUp, hinv, hTT]
  refine Prod.ext rfl ?_
  funext s
  simp only
  split_ifs with hs
  · rw [h ⟨by simp [hs, hT], by simp⟩]
  · rfl

/-- If the length-welding driver is unique in the sense of Theorem 1.8 (1) (same time `T`, same
driver on `[0,T]`), then `Z^LEN_ℓ` is computed by any length-welding driver: the choice made by
`lenWeldDriver` is irrelevant. -/
theorem zipLenUpC_eq_of_unique {γ ℓ : ℝ} {c : FieldSample × (ℝ → ℝ)} {p : ℝ × (ℝ → ℝ)}
    (hp : IsLenWeldingDriver γ c.1 ℓ p)
    (huniq : ∀ q q', IsLenWeldingDriver γ c.1 ℓ q → IsLenWeldingDriver γ c.1 ℓ q' →
      q.1 = q'.1 ∧ EqOn q.2 q'.2 (Icc 0 q.1)) :
    zipLenUpC γ ℓ c = canonConfig γ (zipWeldUp γ p.1 p.2 c) := by
  have hs := lenWeldDriver_spec ⟨p, hp⟩
  obtain ⟨h1, h2⟩ := huniq _ _ hs hp
  unfold zipLenUpC
  rw [h1] at h2 ⊢
  rw [zipWeldUp_congr hp.1 h2]

end QuantumZipper
