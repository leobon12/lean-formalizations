/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Real
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Spec.Sec2.TerminalPath
import InteractingSLE.Spec.Supplement.LPProbReflect

/-!
# Aux. lemma 25: the pathwise argument before the lifetime

Packet PROVE-AUX25. Specification, proof of Aux. lemma 25 (`source/spec/p097-144.md`, pp. 125–127). For one
path of an integrated `SLE_κ(ρ)` evolution with a continuous generating trace `η`, two times `s < t` before
the lifetime with `η(s) = η(t)` are bracketed by a rational interior time `q`. In the chart at `q`
(`Aux25Real.lean`):

* if every force gap is nonzero at `t`, the localized comparison of Aux. lemma 24 puts the relative tip in
  `ℍ`, so `η(t) ∉ η([0, q])`;
* if a right force coordinate meets the driver at `t`, the relative tip is a real point at or right of that
  coordinate's position at `q` (`IsLoewnerTraceLT.not_mem_image_or_endpoint_right`), and `η(t) ∈ η([0, q])`
  forces the **endpoint case**: the coordinate was swallowed by `q` and hits the driver again exactly at its
  own position, with every real point to its right still alive;
* left collisions are the reflection.

The endpoint case is excluded by the probabilistic input `NoRightEndpoint` (the source's "independent
one-force first-swallow law (B1) in Aux. lemma 99"), which the deterministic part reduces to a rational
restart time `r` after which the other force gaps stay at least `1/(m+1)` up to the first collision `σ`.

## Main definitions

* `Aux25.AliveFrom w r σ y`: the real point `y` (centred at the driver at time `r`) is not swallowed on
  `[r, σ]`;
* `Aux25.NoRightEndpoint w vL vR ζ`: the endpoint case does not happen at any rational restart time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace Aux25

/-! ### Definitions -/

/-- The real point `y`, centred at the driver at time `r`, is **alive on `[r, σ]`**: the centred real
Loewner flow `X(s) = y − (w(s) − w(r)) + ∫ᵣˢ 2/X` has a positive continuous solution on `[r, σ]`. -/
def AliveFrom (w : ℝ≥0 → ℝ) (r σ : ℝ≥0) (y : ℝ) : Prop :=
  ∃ X : ℝ → ℝ, ContinuousOn X (Icc (r : ℝ) σ) ∧ (∀ s ∈ Icc (r : ℝ) σ, 0 < X s) ∧
    ∀ s ∈ Icc (r : ℝ) σ, X s = y - (w s.toNNReal - w r) + ∫ τ in (r : ℝ)..s, 2 / X τ

/-- The rational restart time `q⁺ ∈ ℝ≥0`. -/
def ratTime (q : ℚ) : ℝ≥0 := (q : ℝ).toNNReal

/-- **No right endpoint case** (pathwise form of the source's "first-swallow law (B1)" applied after a
rational restart): for every rational time `r = q⁺`, right mark `k` that is leftmost among the right marks at
`r` and has a positive gap there, and first later collision time `σ` of `k` with the driver before the
lifetime, if every other force gap (right marks not at `k`'s position at `r`, and all left marks) stays at
least `1/(m+1)` on `[r, σ]`, then not every real point to the right of `k` (in the chart at `r`) is alive up
to `σ`; that is, the trace does not hit `k`'s own position at `σ`. -/
def NoRightEndpoint {nL nR : ℕ} (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (ζ : ℝ≥0∞) : Prop :=
  ∀ (q : ℚ) (k : Fin nR) (m : ℕ) (σ : ℝ≥0), (ratTime q) < σ → (σ : ℝ≥0∞) < ζ →
    w (ratTime q) < vR k (ratTime q) → (∀ s : ℝ≥0, (ratTime q) ≤ s → s < σ → w s < vR k s) →
    vR k σ = w σ → (∀ j, vR k (ratTime q) ≤ vR j (ratTime q)) →
    (∀ s : ℝ≥0, (ratTime q) ≤ s → s ≤ σ → ∀ j, vR j (ratTime q) ≠ vR k (ratTime q) →
      1 / ((m : ℝ) + 1) ≤ vR j s - w s) →
    (∀ s : ℝ≥0, (ratTime q) ≤ s → s ≤ σ → ∀ i, 1 / ((m : ℝ) + 1) ≤ w s - vL i s) →
    ¬ ∀ y : ℝ, vR k (ratTime q) - w (ratTime q) < y → AliveFrom w (ratTime q) σ y

/-! ### Force coordinates of a frozen path as centred solutions -/

/-- The centred coordinate `s ↦ v(s⁺) − W(s)` of a mark `v` for an `ℝ`-indexed driver `W`. -/
def centred (v : ℝ≥0 → ℝ) (W : ℝ → ℝ) (s : ℝ) : ℝ := v s.toNNReal - W s

section Frozen

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem toNNReal_lt_of_le {t₂ : ℝ} (ht₂ζ : ENNReal.ofReal t₂ < ζ) {s : ℝ} (hs : s ≤ t₂) :
    ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ :=
  show ENNReal.ofReal s < ζ from lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs) ht₂ζ

/-- **A mark of a frozen path is a centred solution.** If `v = x + ∫ 2/(v − w)` before `ζ` (integrable
reciprocal gap, null collision set) and `t₂ < ζ`, then `centred v (frozenDrive w t₂)` solves the centred
real Loewner equation of `frozenDrive w t₂` on `[0, T]` for every `T ≤ t₂`. -/
theorem centred_eq_of_frozen {v : ℝ≥0 → ℝ} {x : ℝ}
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hv : ContinuousOn v {s | (s : ℝ≥0∞) < ζ})
    (hint : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 s)
    (heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ →
      v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal))
    (hnull : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = v s.toNNReal} = 0)
    {t₂ : ℝ} (ht₂ζ : ENNReal.ofReal t₂ < ζ) {T : ℝ} (hT0 : 0 ≤ T) (hTt₂ : T ≤ t₂) :
    ContinuousOn (centred v (frozenDrive w t₂)) (Icc 0 T) ∧
      (∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
        centred v (frozenDrive w t₂) s₂ - centred v (frozenDrive w t₂) s₁ =
          -(frozenDrive w t₂ s₂ - frozenDrive w t₂ s₁) +
            ∫ s in s₁..s₂, 2 / centred v (frozenDrive w t₂) s) ∧
      IntervalIntegrable (fun s => 2 / centred v (frozenDrive w t₂) s) volume 0 T ∧
      volume {s | s ∈ Icc (0 : ℝ) T ∧ centred v (frozenDrive w t₂) s = 0} = 0 := by
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂ζ
  have hlt : ∀ s ∈ Icc (0 : ℝ) T, ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun s hs =>
    toNNReal_lt_of_le ht₂ζ (hs.2.trans hTt₂)
  have hWeq : ∀ s ∈ Icc (0 : ℝ) T, frozenDrive w t₂ s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans hTt₂⟩
  set u := centred v (frozenDrive w t₂) with hu
  have hu_eq : ∀ s ∈ Icc (0 : ℝ) T, u s = v s.toNNReal - w s.toNNReal := fun s hs => by
    simp only [hu, centred, hWeq s hs]
  have huc : ContinuousOn u (Icc 0 T) :=
    (hv.comp continuous_real_toNNReal.continuousOn fun s hs => hlt s hs).sub hW.continuousOn
  have hint' : ∀ s ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 s := by
    intro s hs
    have h := hint s.toNNReal (hlt s hs)
    rw [Real.coe_toNNReal _ hs.1] at h
    have e : (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) =
        fun r => (-2) * (w r.toNNReal - v r.toNNReal)⁻¹ := by
      funext r
      rw [div_eq_mul_inv, ← neg_sub, inv_neg]
      ring
    rw [e]
    exact h.const_mul _
  have heq' : ∀ s ∈ Icc (0 : ℝ) T,
      v s.toNNReal = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) := by
    intro s hs
    have h := heq s.toNNReal (hlt s hs)
    rwa [Real.coe_toNNReal _ hs.1] at h
  have hcongr : ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T,
      (∫ r in s₁..s₂, 2 / (v r.toNNReal - w r.toNNReal)) = ∫ r in s₁..s₂, 2 / u r := by
    intro s₁ hs₁ s₂ hs₂
    refine intervalIntegral.integral_congr fun r hr => ?_
    simp only [hu_eq r (uIcc_subset_Icc hs₁ hs₂ hr)]
  refine ⟨huc, ?_, ?_, ?_⟩
  · intro s₁ hs₁ s₂ hs₂ _
    rw [← hcongr s₁ hs₁ s₂ hs₂,
      ← intervalIntegral.integral_interval_sub_left (hint' s₂ hs₂) (hint' s₁ hs₁)]
    have e1 := heq' s₁ hs₁
    have e2 := heq' s₂ hs₂
    simp only [hu, centred]
    linarith
  · have h := hint' T ⟨hT0, le_rfl⟩
    rw [intervalIntegrable_iff] at h ⊢
    refine h.congr_fun (fun r hr => ?_) measurableSet_uIoc
    rw [uIoc_of_le hT0] at hr
    simp only [hu_eq r ⟨hr.1.le, hr.2⟩]
  · refine measure_mono_null (fun s hs => ?_) hnull
    refine ⟨hs.1.1, hlt s hs.1, ?_⟩
    have h := hs.2
    rw [hu_eq s hs.1] at h
    linarith

end Frozen

/-! ### Helpers -/

section Helpers

/-- The four properties of a centred force coordinate restrict to subintervals. -/
theorem centred_restrict {W u : ℝ → ℝ} {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (h : ContinuousOn u (Icc 0 T) ∧
      (∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
        u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s) ∧
      IntervalIntegrable (fun s => 2 / u s) volume 0 T ∧
      volume {s | s ∈ Icc (0 : ℝ) T ∧ u s = 0} = 0) :
    ContinuousOn u (Icc a b) ∧
      (∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, s₁ ≤ s₂ →
        u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s) ∧
      IntervalIntegrable (fun s => 2 / u s) volume a b ∧
      volume {s | s ∈ Icc a b ∧ u s = 0} = 0 := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hbT
  obtain ⟨hc, he, hi, hn⟩ := h
  refine ⟨hc.mono hsub, fun s₁ hs₁ s₂ hs₂ h12 => he s₁ (hsub hs₁) s₂ (hsub hs₂) h12,
    hi.mono_set (by rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hbT))]; exact hsub),
    measure_mono_null (fun s (hs : s ∈ {s | s ∈ Icc a b ∧ u s = 0}) =>
      (⟨hsub hs.1, hs.2⟩ : s ∈ {s | s ∈ Icc (0 : ℝ) T ∧ u s = 0})) hn⟩

/-- A uniform positive lower bound for finitely many positive reals. -/
theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

/-- **From a forward solution in the chart at `r` to `AliveFrom`.** -/
theorem aliveFrom_of_isForwardSol {w : ℝ≥0 → ℝ} {t₂ : ℝ} (hW : Continuous (frozenDrive w t₂))
    {r σ : ℝ} (hr : 0 ≤ r) (hrσ : r ≤ σ) (hσt₂ : σ ≤ t₂) {y : ℝ} (hy : 0 < y) {v : ℝ → ℂ}
    (hv : IsForwardSol (shiftDrive (frozenDrive w t₂) r) (y : ℂ) (σ - r) v) :
    AliveFrom w r.toNNReal σ.toNNReal y := by
  have hσ0 : 0 ≤ σ - r := sub_nonneg.2 hrσ
  obtain ⟨X₀, hXc, hXv, hX0, hXeq, -⟩ :=
    exists_real_of_isForwardSol (QuantumZipper.RS.continuous_shiftDrive hW r) hσ0 hv
  rw [QuantumZipper.RS.shiftDrive_zero, sub_zero] at hX0
  have hXpos := pos_of_ne_zero_of_pos hXc (fun s hs => (hXv s hs).1) (by rw [hX0]; exact hy)
  have hrN : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr
  have hσN : ((σ.toNNReal : ℝ≥0) : ℝ) = σ := Real.coe_toNNReal _ (hr.trans hrσ)
  have hmem : ∀ x ∈ Icc r σ, x - r ∈ Icc (0 : ℝ) (σ - r) := fun x hx =>
    ⟨sub_nonneg.2 hx.1, by linarith [hx.2]⟩
  refine ⟨fun x => X₀ (x - r), ?_, ?_, ?_⟩
  · rw [hrN, hσN]
    exact hXc.comp (continuous_id.sub continuous_const).continuousOn hmem
  · rw [hrN, hσN]
    exact fun x hx => hXpos _ (hmem x hx)
  · rw [hrN, hσN]
    intro x hx
    have h1 := hXeq 0 ⟨le_rfl, hσ0⟩ (x - r) (hmem x hx) (hmem x hx).1
    rw [hX0] at h1
    have h2 : shiftDrive (frozenDrive w t₂) r (x - r) - shiftDrive (frozenDrive w t₂) r 0 =
        w x.toNNReal - w r.toNNReal := by
      simp only [shiftDrive, add_zero, sub_self, sub_zero, add_sub_cancel]
      rw [frozenDrive_eq ⟨hr.trans hx.1, hx.2.trans hσt₂⟩,
        frozenDrive_eq ⟨hr, hrσ.trans hσt₂⟩]
    have h3 : (∫ τ in (0 : ℝ)..(x - r), 2 / X₀ τ) = ∫ τ in r..x, 2 / X₀ (τ - r) := by
      rw [intervalIntegral.integral_comp_sub_right (fun τ => 2 / X₀ τ) r, sub_self]
    rw [h2, h3] at h1
    linarith

end Helpers

/-! ### The right collision case -/

section Right

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **No return at a right collision.** Let `η` be a continuous generating trace of an integrated path
without the endpoint case, `s < q < t < ζ` with `q` rational, `η(q) ∈ ℍ`, and let a right force coordinate
meet the driver at `t`. Then `η(t) ≠ η(s)`. -/
theorem false_of_eq_of_collision_right (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) (hend : NoRightEndpoint w vL vR ζ)
    {s t : ℝ≥0} {q : ℚ} (hsq : (s : ℝ) < q) (hqt : (q : ℝ) < t) (htζ : (t : ℝ≥0∞) < ζ)
    (hηq : η (ratTime q) ∈ H) (hst : η s = η t) {k : Fin nR} (hk : vR k t = w t) : False := by
  have hp' := hp
  obtain ⟨hw0, -, -, hwc, hvLc, hvRc, -, hvLw, hwvR, -, hgapL, hgapR, -, hvLeq, hvReq, hcolL,
    hcolR, -⟩ := hp'
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := exists_real_btwn_of_lt htζ
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hwc ht₂ζ
  have hW0 : W 0 = 0 := by rw [hWdef, frozenDrive_zero ht₂, hw0]
  have hL := hη.isLoewnerTraceLT ht₂ζ
  set T : ℝ := (t : ℝ) with hTdef
  have hT0 : 0 ≤ T := t.coe_nonneg
  have hTt₂ : T ≤ t₂ := htt₂.le
  set r : ℝ := (q : ℝ) with hrdef
  have hr0 : 0 ≤ r := (NNReal.coe_nonneg s).trans hsq.le
  have hrT : r < T := hqt
  have hrN : ((ratTime q : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0
  have hlt : ∀ x ∈ Icc (0 : ℝ) T, ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun x hx =>
    toNNReal_lt_of_le ht₂ζ (hx.2.trans hTt₂)
  have hWeq : ∀ x ∈ Icc (0 : ℝ) T, W x = w x.toNNReal := fun x hx =>
    frozenDrive_eq ⟨hx.1, hx.2.trans hTt₂⟩
  -- the right and left force coordinates
  set u : Fin nR → ℝ → ℝ := fun j => centred (vR j) W with hudef
  set uL : Fin nL → ℝ → ℝ := fun i => centred (vL i) W with huLdef
  have hmR : ∀ j, _ := fun j => centred_eq_of_frozen hwc (hvRc j) (fun s hs => hgapR s hs j)
    (fun s hs => hvReq s hs j) (hcolR j) ht₂ζ hT0 hTt₂
  have hmL : ∀ i, _ := fun i => centred_eq_of_frozen hwc (hvLc i) (fun s hs => hgapL s hs i)
    (fun s hs => hvLeq s hs i) (hcolL i) ht₂ζ hT0 hTt₂
  have hu_eq : ∀ j, ∀ x ∈ Icc (0 : ℝ) T, u j x = vR j x.toNNReal - w x.toNNReal := fun j x hx => by
    simp only [hudef, centred, hWeq x hx]
  have huL_eq : ∀ i, ∀ x ∈ Icc (0 : ℝ) T, uL i x = vL i x.toNNReal - w x.toNNReal :=
    fun i x hx => by simp only [huLdef, centred, hWeq x hx]
  have hu0 : ∀ j, ∀ x ∈ Icc (0 : ℝ) T, 0 ≤ u j x := fun j x hx => by
    rw [hu_eq j x hx]; linarith [hwvR _ (hlt x hx) j]
  have huL0 : ∀ i, ∀ x ∈ Icc (0 : ℝ) T, uL i x ≤ 0 := fun i x hx => by
    rw [huL_eq i x hx]; linarith [hvLw _ (hlt x hx) i]
  have hrI : r ∈ Icc (0 : ℝ) T := ⟨hr0, hrT.le⟩
  -- gaps at `r`
  have hrζ : ((ratTime q : ℝ≥0) : ℝ≥0∞) < ζ := by
    have := hlt r hrI
    rwa [show (ratTime q : ℝ≥0) = r.toNNReal from rfl]
  obtain ⟨hgL, hgR⟩ := hp.forall_ne_of_mem_H hη hrζ hηq
  have hur : ∀ j, 0 < u j r := fun j => by
    have h1 := hu0 j r hrI
    have h2 : u j r ≠ 0 := by
      rw [hu_eq j r hrI]; exact sub_ne_zero.2 (hgR j).symm
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have huLr : ∀ i, uL i r < 0 := fun i => by
    have h1 := huL0 i r hrI
    have h2 : uL i r ≠ 0 := by
      rw [huL_eq i r hrI]; exact sub_ne_zero.2 (hgL i).symm
    exact lt_of_le_of_ne h1 h2
  -- the trace point `η(t)` is on the prefix through `r`
  have hmem : (fun x : ℝ => η x.toNNReal) T ∈ (fun x : ℝ => η x.toNNReal) '' Icc 0 r :=
    ⟨s, ⟨s.coe_nonneg, hsq.le⟩, by simp only [hTdef, Real.toNNReal_coe, hst]⟩
  have hukT : u k T = 0 := by
    rw [hu_eq k T ⟨hT0, le_rfl⟩, hTdef, Real.toNNReal_coe, hk, sub_self]
  -- the dichotomy in the chart at `r`
  rcases hL.not_mem_image_or_endpoint_right hW hW0 hr0 hrT (lt_of_le_of_lt le_rfl htt₂) (hmR k).1
    (hu0 k) (hmR k).2.1 (hmR k).2.2.1 (hmR k).2.2.2 hukT with hnot | ⟨hz, halive⟩
  · exact hnot hmem
  -- the first collision `σ` of `k` after `r`
  obtain ⟨σ, hσ, huσ₀, hukne⟩ := exists_first_zero hrT.le
    ((hmR k).1.mono (Icc_subset_Icc_left hr0)) (hur k).ne' hukT
  have huσ : u k σ = 0 := huσ₀
  have hrσ : r < σ := hσ.1
  have hσT : σ ≤ T := hσ.2
  have hσ0 : 0 ≤ σ := hr0.trans hrσ.le
  have hσI : σ ∈ Icc (0 : ℝ) T := ⟨hσ0, hσT⟩
  -- comparison of two right coordinates on `[a', b'] ⊆ [0, T]`
  have hcmp : ∀ j j' : Fin nR, ∀ a' b' : ℝ, 0 ≤ a' → a' ≤ b' → b' ≤ T →
      ∀ x ∈ Icc a' b', u j' x - u j x ≤ max (u j' a' - u j a') 0 := by
    intro j j' a' b' ha' hab' hb'
    have hRj := centred_restrict ha' hab' hb' (hmR j)
    have hRj' := centred_restrict ha' hab' hb' (hmR j')
    exact sub_le_max_of_centredEq hRj.1 (fun x hx => hu0 j x ⟨ha'.trans hx.1, hx.2.trans hb'⟩)
      hRj.2.1 hRj.2.2.1 hRj.2.2.2 hRj'.1 hRj'.2.1 hRj'.2.2.1
  -- `k` is leftmost among the right marks at `r` (it was swallowed by `r`)
  obtain ⟨s', hs', hus'₀⟩ := hz
  have hus' : u k s' = 0 := hus'₀
  have hleft : ∀ j, u k r ≤ u j r := by
    intro j
    rcases le_total (u k 0) (u j 0) with h | h
    · have := hcmp j k 0 r le_rfl hr0 hrT.le r ⟨hr0, le_rfl⟩
      rw [max_eq_right (by linarith)] at this
      linarith
    · have h1 := hcmp k j 0 s' le_rfl hs'.1 (hs'.2.trans hrT.le) s' ⟨hs'.1, le_rfl⟩
      rw [max_eq_right (by linarith)] at h1
      have hujs' : u j s' = 0 :=
        le_antisymm (by linarith) (hu0 j s' ⟨hs'.1, hs'.2.trans hrT.le⟩)
      have h2 := hcmp j k s' r hs'.1 hs'.2 hrT.le r ⟨hs'.2, le_rfl⟩
      rw [hus', hujs', sub_self, max_self] at h2
      linarith
  -- the shifted coordinates in the chart at `r`
  have hsR : ∀ j, _ := fun j => centredEq_shift hr0 hrT.le (hmR j).1 (hmR j).2.1 (hmR j).2.2.1
    (hmR j).2.2.2
  have hsL : ∀ i, _ := fun i => centredEq_shift hr0 hrT.le (hmL i).1 (hmL i).2.1 (hmL i).2.2.1
    (hmL i).2.2.2
  have hσr : σ - r ≤ T - r := by linarith
  have hσr0 : 0 ≤ σ - r := by linarith
  have hshmem : ∀ x ∈ Icc (0 : ℝ) (T - r), r + x ∈ Icc (0 : ℝ) T := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hSc := QuantumZipper.RS.continuous_shiftDrive hW r
  -- lower bounds for the right marks not at `k`'s position
  have hlow : ∀ j, ∃ δ > 0, u j r ≠ u k r → ∀ x ∈ Icc r σ, δ ≤ u j x := by
    intro j
    by_cases hj : u j r = u k r
    · exact ⟨1, one_pos, fun h => absurd hj h⟩
    · have hlt' : u k r < u j r := lt_of_le_of_ne (hleft j) (Ne.symm hj)
      set y := (u k r + u j r) / 2 with hydef
      obtain ⟨v, hv⟩ := halive y (by rw [hydef]; linarith)
      have hv' := isForwardSol_mono hv hσr
      obtain ⟨X, hXc, hXv, hX0, hXeq, hXint⟩ := exists_real_of_isForwardSol hSc hσr0 hv'
      rw [QuantumZipper.RS.shiftDrive_zero, sub_zero] at hX0
      have hXpos := pos_of_ne_zero_of_pos hXc (fun x hx => (hXv x hx).1)
        (by rw [hX0, hydef]; linarith [hur k])
      have hRj := centred_restrict le_rfl hσr0 hσr (hsR j)
      have hcm := sub_le_max_of_centredEq hRj.1
        (fun x hx => hu0 j _ (hshmem x ⟨hx.1, hx.2.trans hσr⟩)) hRj.2.1 hRj.2.2.1 hRj.2.2.2 hXc
        hXeq hXint
      obtain ⟨τ₀, hτ₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hσr0) hXc
      refine ⟨X τ₀, hXpos τ₀ hτ₀, fun _ x hx => ?_⟩
      have hxm : x - r ∈ Icc (0 : ℝ) (σ - r) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have h1 := hcm (x - r) hxm
      rw [hX0, add_zero, max_eq_right (by rw [hydef]; linarith)] at h1
      have h2 : X τ₀ ≤ X (x - r) := hmin hxm
      rw [show r + (x - r) = x by ring] at h1
      linarith
  choose δf hδf hδfle using hlow
  obtain ⟨δR, hδR, hδRle⟩ := exists_pos_le_of_finite δf hδf
  -- no left mark meets the driver at `σ`
  obtain ⟨hγ, -⟩ := hL.isLoewnerTraceLT_shift hW hW0 hr0
  have hσt₂ : σ - r < t₂ - r := by linarith
  have hLσ : ∀ i, uL i σ ≠ 0 := by
    intro i hi0
    have hRk := centred_restrict le_rfl hσr0 hσr (hsR k)
    have hRi := centred_restrict le_rfl hσr0 hσr (hsL i)
    obtain ⟨xR, hxR, hxRu, -⟩ := hγ.exists_tip_real_of_collision_right hSc
      (QuantumZipper.RS.shiftDrive_zero W r) hσr0 hσt₂ hRk.1
      (fun x hx => hu0 k _ (hshmem x ⟨hx.1, hx.2.trans hσr⟩)) hRk.2.1 hRk.2.2.1 hRk.2.2.2
      (by rw [show r + (σ - r) = σ by ring]; exact huσ)
    obtain ⟨xL', hxL, hxLu, -⟩ := hγ.exists_tip_real_of_collision_left hSc
      (QuantumZipper.RS.shiftDrive_zero W r) hσr0 hσt₂ hRi.1
      (fun x hx => huL0 i _ (hshmem x ⟨hx.1, hx.2.trans hσr⟩)) hRi.2.1 hRi.2.2.1 hRi.2.2.2
      (by rw [show r + (σ - r) = σ by ring]; exact hi0)
    rw [hxR] at hxL
    have hxx : xR = xL' := Complex.ofReal_injective hxL
    rw [add_zero] at hxRu hxLu
    linarith [hur k, huLr i]
  -- the left gaps stay away from `0` near `σ`
  have hLσneg : ∀ i, uL i σ < 0 := fun i => lt_of_le_of_ne (huL0 i σ hσI) (hLσ i)
  have hnear : ∀ i, ∃ ε > 0, ∀ x ∈ Icc (0 : ℝ) T, dist x σ < ε → -uL i σ / 2 ≤ -uL i x := by
    intro i
    obtain ⟨ε, hε, hball⟩ := Metric.continuousWithinAt_iff.1 ((hmL i).1 σ hσI) (-uL i σ / 2)
      (by linarith [hLσneg i])
    refine ⟨ε, hε, fun x hx hxσ => ?_⟩
    have h := hball hx hxσ
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  choose εf hεf hεfle using hnear
  obtain ⟨εL, hεL, hεLle⟩ := exists_pos_le_of_finite εf hεf
  obtain ⟨δL, hδL, hδLle⟩ := exists_pos_le_of_finite (fun i => -uL i σ / 2)
    (fun i => by linarith [hLσneg i])
  -- the rational restart time `r' ∈ (r, σ)` close to `σ`, and the level `1/(m+1)`
  obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (max_lt hrσ (by linarith : σ - εL < σ))
  set r' : ℝ := (q' : ℝ) with hr'def
  have hr'r : r < r' := lt_of_le_of_lt (le_max_left _ _) hq'1
  have hr'ε : σ - εL < r' := lt_of_le_of_lt (le_max_right _ _) hq'1
  have hr'σ : r' < σ := hq'2
  have hr'0 : 0 ≤ r' := hr0.trans hr'r.le
  have hr'N : ((ratTime q' : ℝ≥0) : ℝ) = r' := Real.coe_toNNReal _ hr'0
  have hσN : ((σ.toNNReal : ℝ≥0) : ℝ) = σ := Real.coe_toNNReal _ hσ0
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min hδR hδL)
  have hmR' : 1 / ((m : ℝ) + 1) ≤ δR := (hm.trans_le (min_le_left _ _)).le
  have hmL' : 1 / ((m : ℝ) + 1) ≤ δL := (hm.trans_le (min_le_right _ _)).le
  -- values at times of `ℝ≥0`
  have hval : ∀ j, ∀ x : ℝ≥0, (x : ℝ) ∈ Icc (0 : ℝ) T → u j x = vR j x - w x := fun j x hx => by
    rw [hu_eq j x hx, Real.toNNReal_coe]
  have hvalL : ∀ i, ∀ x : ℝ≥0, (x : ℝ) ∈ Icc (0 : ℝ) T → uL i x = vL i x - w x := fun i x hx => by
    rw [huL_eq i x hx, Real.toNNReal_coe]
  have hmemI : ∀ x : ℝ≥0, ratTime q' ≤ x → x ≤ σ.toNNReal → (x : ℝ) ∈ Icc r' σ := fun x h1 h2 =>
    ⟨by rw [← hr'N]; exact_mod_cast h1, by rw [← hσN]; exact_mod_cast h2⟩
  have hIT : ∀ x : ℝ, x ∈ Icc r' σ → x ∈ Icc (0 : ℝ) T := fun x hx =>
    ⟨hr'0.trans hx.1, hx.2.trans hσT⟩
  have hr'I : ((ratTime q' : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) T := by rw [hr'N]; exact hIT r' ⟨le_rfl, hr'σ.le⟩
  have hσI' : ((σ.toNNReal : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) T := by rw [hσN]; exact hσI
  -- `k` stays leftmost, and the marks at `k`'s position move with `k`
  have hleft' : ∀ j, u k r' ≤ u j r' := fun j => by
    have := hcmp j k r r' hr0 hr'r.le (hr'σ.le.trans hσT) r' ⟨hr'r.le, le_rfl⟩
    rw [max_eq_right (by linarith [hleft j])] at this
    linarith
  have hsame : ∀ j, u j r = u k r → u j r' = u k r' := fun j hj => by
    have h1 := hcmp j k r r' hr0 hr'r.le (hr'σ.le.trans hσT) r' ⟨hr'r.le, le_rfl⟩
    have h2 := hcmp k j r r' hr0 hr'r.le (hr'σ.le.trans hσT) r' ⟨hr'r.le, le_rfl⟩
    rw [hj, sub_self, max_self] at h1 h2
    linarith
  refine hend q' k m σ.toNNReal ?_ (hlt σ hσI) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← NNReal.coe_lt_coe, hr'N, hσN]; exact hr'σ
  · rw [← sub_pos, ← hval k _ hr'I, hr'N]
    exact lt_of_le_of_ne (hu0 k r' (hIT r' ⟨le_rfl, hr'σ.le⟩))
      (Ne.symm (hukne r' ⟨hr'r.le, hr'σ⟩))
  · intro x hx1 hx2
    have hxI := hmemI x hx1 hx2.le
    have hxσ : (x : ℝ) < σ := by rw [← hσN]; exact_mod_cast hx2
    rw [← sub_pos, ← hval k x (hIT _ hxI)]
    exact lt_of_le_of_ne (hu0 k x (hIT _ hxI)) (Ne.symm (hukne x ⟨hr'r.le.trans hxI.1, hxσ⟩))
  · have h := hval k _ hσI'
    rw [hσN, huσ] at h
    linarith
  · intro j
    have h1 := hval k _ hr'I
    have h2 := hval j _ hr'I
    rw [hr'N] at h1 h2
    linarith [hleft' j]
  · intro x hx1 hx2 j hj
    have hxI := hmemI x hx1 hx2
    have hjr : u j r ≠ u k r := fun h => by
      have h3 := hsame j h
      have h1 := hval k _ hr'I
      have h2 := hval j _ hr'I
      rw [hr'N] at h1 h2
      exact hj (by linarith)
    have h4 := hδfle j hjr x ⟨hr'r.le.trans hxI.1, hxI.2⟩
    rw [hval j x (hIT _ hxI)] at h4
    linarith [hδRle j]
  · intro x hx1 hx2 i
    have hxI := hmemI x hx1 hx2
    have hdist : dist (x : ℝ) σ < εf i := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hεLle i, hxI.1, hxI.2]
    have h4 := hεfle i x (hIT _ hxI) hdist
    rw [hvalL i x (hIT _ hxI)] at h4
    linarith [hδLle i]
  · intro y' hy'
    have hkr' := hval k _ hr'I
    rw [hr'N] at hkr'
    rw [← hkr'] at hy'
    have hRk := centred_restrict le_rfl hσr0 hσr (hsR k)
    have halive' : ∀ y : ℝ, (fun x => u k (r + x)) 0 < y →
        ∃ v, IsForwardSol (shiftDrive W r) (y : ℂ) (σ - r) v := fun y hy => by
      obtain ⟨v, hv⟩ := halive y (by simpa only [add_zero] using hy)
      exact ⟨v, isForwardSol_mono hv hσr⟩
    obtain ⟨v, hv⟩ := alive_shift_of_alive hSc (QuantumZipper.RS.shiftDrive_zero W r)
      (sub_nonneg.2 hr'r.le) (by linarith : r' - r ≤ σ - r) hRk.1
      (fun x hx => hu0 k _ (hshmem x ⟨hx.1, hx.2.trans hσr⟩)) hRk.2.1 hRk.2.2.1 hRk.2.2.2
      halive' y' (by simpa only [show r + (r' - r) = r' by ring] using hy')
    rw [shiftDrive_shiftDrive, show σ - r - (r' - r) = σ - r' by ring] at hv
    have hy'pos : 0 < y' := lt_of_le_of_lt (hu0 k r' (hIT r' ⟨le_rfl, hr'σ.le⟩)) hy'
    exact aliveFrom_of_isForwardSol hW hr'0 hr'σ.le (hσT.trans hTt₂) hy'pos hv

end Right

/-! ### Injectivity before the lifetime -/

section Inj

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The localization of Aux. lemma 24 along one path (the pathwise conclusion of
`IsIntegratedSLEEvolution.ae_exists_localization`): at a time with all force gaps nonzero, the future after
some time `a` just before it agrees with a driver whose trace is continuous and interior. -/
def HasLocalization {nL nR : ℕ} (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (ζ : ℝ≥0∞) : Prop :=
  ∀ t₁ : ℝ≥0, (t₁ : ℝ≥0∞) < ζ → (∀ i, w t₁ ≠ vL i t₁) → (∀ i, w t₁ ≠ vR i t₁) →
    ∀ b : ℝ≥0, b < t₁ → ∃ a : ℝ≥0, b < a ∧ a < t₁ ∧
      ∃ f : ℝ → ℝ, Continuous f ∧ f 0 = 0 ∧
        (∀ u : ℝ, 0 ≤ u → Tendsto (fun y : ℝ => fwdMapInv f u (y * Complex.I)) (𝓝[>] 0)
          (𝓝 (QuantumZipper.trace f u))) ∧
        ContinuousOn (QuantumZipper.trace f) (Ici 0) ∧
        (∀ u : ℝ, 0 < u → QuantumZipper.trace f u ∈ H) ∧
        ∀ s : ℝ≥0, a + s ≤ t₁ → w (a + s) - w a = f s

/-- Between two times before the lifetime there is a rational interior time. -/
theorem exists_rat_mem_H_btwn {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {s t : ℝ≥0} (hst : s < t)
    (htζ : (t : ℝ≥0∞) < ζ) : ∃ q : ℚ, (s : ℝ) < q ∧ (q : ℝ) < t ∧ η (ratTime q) ∈ H := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := exists_real_btwn_of_lt htζ
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  have hW := continuous_frozenDrive_of_lt hwc ht₂ζ
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have hL := hη.isLoewnerTraceLT ht₂ζ
  have hst' : (s : ℝ) < t := hst
  set m : ℝ := ((s : ℝ) + t) / 2 with hmdef
  have hm1 : (s : ℝ) < m := by rw [hmdef]; linarith
  have hm2 : m < t := by rw [hmdef]; linarith
  obtain ⟨u, hu, huK⟩ := hL.exists_mem_diff (t := (s : ℝ)) (t' := m) hW hW0 s.coe_nonneg hm1
    (by linarith)
  have huH : η u.toNNReal ∈ H := by
    have h1 := huK.1
    rw [hL.2.2 m (by linarith [s.coe_nonneg]) (by linarith)] at h1
    exact fillH_subset_H _ h1
  have hu0 : 0 ≤ u := (NNReal.coe_nonneg s).trans hu.1.le
  have hcont : ContinuousWithinAt (fun x : ℝ => η x.toNNReal) (Ico 0 t₂) u :=
    hL.2.1 u ⟨hu0, by linarith [hu.2]⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    (hcont.preimage_mem_nhdsWithin (QuantumZipper.isOpen_H.mem_nhds huH))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (s : ℝ) (u - ε) < min (t : ℝ) (u + ε) from
    max_lt (lt_min (by linarith [hu.1]) (by linarith [hu.1])) (lt_min (by linarith [hu.2]) (by linarith)))
  have hqs : (s : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hqt : (q : ℝ) < t := lt_of_lt_of_le hq2 (min_le_left _ _)
  refine ⟨q, hqs, hqt, ?_⟩
  have hmem : (q : ℝ) ∈ Metric.ball u ε ∩ Ico 0 t₂ := by
    refine ⟨?_, ⟨(NNReal.coe_nonneg s).trans hqs.le, by linarith⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_right (s : ℝ) (u - ε)]
    · linarith [min_le_right (t : ℝ) (u + ε)]
  exact hball hmem

/-- **Aux. lemma 25 before the lifetime, pathwise.** A continuous generating trace of an integrated path
with the Aux. 24 localization and without right or (reflected) left endpoint cases is injective on
`{t | t < ζ}`. -/
theorem injOn_lt_of_noEndpoint (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) (hloc : HasLocalization w vL vR ζ)
    (hendR : NoRightEndpoint w vL vR ζ)
    (hendL : NoRightEndpoint (-w) (fun i => -vR i) (fun i => -vL i) ζ) :
    InjOn η {t | (t : ℝ≥0∞) < ζ} := by
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ} := hp.2.2.2.1
  have hw0 : w 0 = 0 := hp.1
  -- the case `s < t`
  have key : ∀ s t : ℝ≥0, s < t → (t : ℝ≥0∞) < ζ → η s = η t → False := by
    intro s t hst htζ hηst
    obtain ⟨q, hsq, hqt, hηq⟩ := exists_rat_mem_H_btwn hη hwc hw0 hst htζ
    by_cases hR : ∃ k, vR k t = w t
    · obtain ⟨k, hk⟩ := hR
      exact false_of_eq_of_collision_right hp hη hendR hsq hqt htζ hηq hηst hk
    by_cases hLc : ∃ i, vL i t = w t
    · obtain ⟨i, hi⟩ := hLc
      refine false_of_eq_of_collision_right hp.reflect (LP.isGeneratingTrace_reflect hη) hendL hsq
        hqt htζ (LP.reflectC_mem_H_iff.2 hηq) (by simp only [hηst]) (k := i) ?_
      show -vL i t = -w t
      rw [hi]
    -- all gaps nonzero at `t`: the localization of Aux. lemma 24
    push Not at hR hLc
    have hr0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg s).trans hsq.le
    have hrt : ratTime q < t := by
      rw [← NNReal.coe_lt_coe, ratTime, Real.coe_toNNReal _ hr0]; exact hqt
    obtain ⟨A, hA1, hA2, f, hf, hf0, hflim, -, hfH, hfid⟩ :=
      hloc t htζ (fun i h => hLc i h.symm) (fun i h => hR i h.symm) (ratTime q) hrt
    obtain ⟨t₂, htt₂, ht₂ζ⟩ := exists_real_btwn_of_lt htζ
    have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
    have hW := continuous_frozenDrive_of_lt hwc ht₂ζ
    have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
    have hL := hη.isLoewnerTraceLT ht₂ζ
    have hrN : ((ratTime q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hr0
    have hqA : (q : ℝ) ≤ A := by rw [← hrN]; exact_mod_cast hA1.le
    have hAt : (A : ℝ) ≤ t := by exact_mod_cast hA2.le
    have hEq : EqOn (shiftDrive (frozenDrive w t₂) A) f (Icc 0 ((t : ℝ) - A)) := by
      intro τ hτ
      have hτ0 : 0 ≤ τ := hτ.1
      have hle : A + τ.toNNReal ≤ t := by
        rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hτ0]; linarith [hτ.2]
      simp only [shiftDrive]
      rw [frozenDrive_eq ⟨by positivity, by linarith [hτ.2]⟩,
        frozenDrive_eq ⟨A.coe_nonneg, by linarith⟩, Real.toNNReal_coe,
        show ((A : ℝ) + τ).toNNReal = A + τ.toNNReal by
          rw [Real.toNNReal_add A.coe_nonneg hτ0, Real.toNNReal_coe],
        hfid _ hle, Real.coe_toNNReal _ hτ0]
    have hnot := hL.not_mem_image_of_shiftDrive_eqOn hW hW0 hr0 hqA hAt htt₂ hf hf0 hEq
      (hflim _ (sub_nonneg.2 hAt)) (hfH _ (sub_pos.2 (by exact_mod_cast hA2)))
    refine hnot ⟨s, ⟨s.coe_nonneg, hsq.le⟩, ?_⟩
    simp only [Real.toNNReal_coe, hηst]
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key s t h ht hst
  · exact key t s h hs hst.symm

end Inj

end Aux25

end InteractingSLE
