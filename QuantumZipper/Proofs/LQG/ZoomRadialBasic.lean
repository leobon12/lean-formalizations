import QuantumZipper.Proofs.LQG.WedgeTranslation

/-!
# The radial process at a zoom (blueprint `SECTION5_BLUEPRINT.md` node D3, TASKS.md R6)

Definitions and deterministic facts for the zoom radial process of the D3 zoom lemma. Setting
(Sheffield, arXiv:1012.4797, §1.6 and the proof of Prop. 1.6; Williams (1974); Rogers–Pitman
(1981) Thm 1; Revuz–Yor VII.4): `Xc c b ω t = c + √2 b t + (α − Q) t` is the drifted Brownian
radial path started at `c > 0` (drift `α − Q < 0`), `Tc` is its first hitting time of `0`, and
`zoomRadial α Q b c ω s = Xc (Tc + s)` is the radially normalized process read at the zoom
scale. `Rw` is the *re-centring of the wedge path* at its hitting time of `−c` (the object of
`WedgeTranslation.wedge_translation`, i.e. blueprint node B4(c) from L14).

The deterministic core of the D3 radial comparison is `trunc_Rw_eq`: as soon as `Tc ≥ S` (so
that the window `[−S, 0]` lies before the hitting time), truncating both paths at time `−S`
identifies the re-centred wedge path with the zoom radial path. This is the mirror of
`translation_good` on the `Xc` side: the two paths agree wherever they are read at a
nonnegative time of the drifted path, and the truncation removes exactly the region where the
two disagree (`Tc < S`), which is the event controlled by the wedge branch in R6.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace ZoomRadial

variable {Ω : Type*}

/-- The drifted Brownian path whose first hitting time of `0` is the zoom time:
`Xc c b ω t = c + √2 * b t.toNNReal ω + (α − Q) * t`. -/
def Xc (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  c + √2 * b t.toNNReal ω + (α - Q) * t

/-- The first time `t ≥ 0` at which the radial path `Xc` is `≤ 0`. -/
def Tc (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  sInf {t | 0 ≤ t ∧ Xc α Q c b ω t ≤ 0}

/-- The radial process at the zoom: `Xc` re-centred at `Tc` (junk `Xc (Tc + s)` for `s < −Tc`). -/
def zoomRadial (α Q : ℝ) (b : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  Xc α Q c b ω (Tc α Q c b ω + s)

/-- Truncation of a path at time `−S` (constant extension to the left). -/
def trunc (S : ℝ) (p : ℝ → ℝ) : ℝ → ℝ := fun s => p (max s (-S))

theorem measurable_trunc (S : ℝ) : Measurable (trunc S) :=
  measurable_pi_iff.2 fun s => measurable_pi_apply (max s (-S))

theorem trunc_apply (S : ℝ) (p : ℝ → ℝ) (s : ℝ) : trunc S p s = p (max s (-S)) := rfl

/-- `Xc` is `c` plus the zero-start drifted path used in `WilliamsDriftDecomposition`. -/
theorem Xc_eq (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) :
    Xc α Q c b ω t = c + (√2 * b t.toNNReal ω - (Q - α) * t) := by
  simp only [Xc]; ring

/-- The level set defining `Tc` is the one used in L14 (`X ≤ −c` for the zero-start path). -/
theorem Tc_set_eq (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    {t | 0 ≤ t ∧ Xc α Q c b ω t ≤ 0} =
      {t | 0 ≤ t ∧ √2 * b t.toNNReal ω - (Q - α) * t ≤ -c} := by
  ext t
  rw [mem_setOf_eq, mem_setOf_eq, Xc_eq]
  constructor
  · rintro ⟨h0, h⟩; exact ⟨h0, by linarith⟩
  · rintro ⟨h0, h⟩; exact ⟨h0, by linarith⟩

theorem Tc_nonneg (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) : 0 ≤ Tc α Q c b ω := by
  rw [Tc]
  by_cases h : ({t | 0 ≤ t ∧ Xc α Q c b ω t ≤ 0} : Set ℝ).Nonempty
  · exact le_csInf h fun t ht => ht.1
  · rw [not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty]

/-- On `t ≥ 0` the wedge path is the drifted Brownian path `√2 b t − (Q − α) t`. -/
theorem wA_eq {α Q : ℝ} {b b' : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ} (ht : 0 ≤ t) :
    WedgeTrans.wA α Q b b' t ω = √2 * b t.toNNReal ω - (Q - α) * t := by
  simp only [WedgeTrans.wA, wedgePath, if_pos ht]
  ring

/-- The hitting time of `−c` by the wedge path is `Tc`: on `t ≥ 0` the wedge path agrees with
the drifted Brownian path, and for `t < 0` it does not matter (`Tc ≥ 0`). -/
theorem hitTime_eq_Tc (α Q c : ℝ) (b b' : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (sInf {t | 0 ≤ t ∧ WedgeTrans.wA α Q b b' t ω ≤ -c}) = Tc α Q c b ω := by
  rw [Tc]
  congr 1
  ext t
  constructor
  · rintro ⟨h0, h⟩
    have hw := wA_eq (α := α) (Q := Q) (b := b) (b' := b') (ω := ω) h0
    exact ⟨h0, by rw [Xc_eq]; rw [hw] at h; linarith⟩
  · rintro ⟨h0, h⟩
    have hw := wA_eq (α := α) (Q := Q) (b := b) (b' := b') (ω := ω) h0
    exact ⟨h0, by rw [Xc_eq] at h; rw [hw]; linarith⟩

/-- The wedge path re-centred at its hitting time of `−c` and shifted by `c`
(the map whose law is computed by `WedgeTranslation.wedge_translation`). -/
def Rw (α Q : ℝ) (b b' : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => WedgeTrans.wA α Q b b' (sInf {s | 0 ≤ s ∧ WedgeTrans.wA α Q b b' s ω ≤ -c} + t) ω + c

/-- **Deterministic core of D3 (steps (1)–(3))**: if `Tc ≥ S`, truncating at `−S` makes the
re-centred wedge path equal to the radially normalized zoom process. Below the hitting time the
two read the drifted path at nonnegative times; the truncation cuts off the branch `t < −Tc`,
which is exactly where they differ. -/
theorem trunc_Rw_eq {α Q c S : ℝ} {b b' : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hTc : S ≤ Tc α Q c b ω) :
    trunc S (Rw α Q b b' c ω) =
      fun s => Xc α Q c b ω (Tc α Q c b ω + max s (-S)) := by
  have hkey : ∀ t : ℝ, -S ≤ t → Rw α Q b b' c ω t = Xc α Q c b ω (Tc α Q c b ω + t) := by
    intro t ht
    have h1 : 0 ≤ Tc α Q c b ω + t := by linarith
    rw [Rw, hitTime_eq_Tc]
    show WedgeTrans.wA α Q b b' (Tc α Q c b ω + t) ω + c = _
    rw [wA_eq (α := α) (Q := Q) (b := b) (b' := b') (ω := ω) h1, Xc]
    ring
  funext s
  rw [trunc_apply, hkey (max s (-S)) (le_max_right s (-S))]

/-- The `s ↦ Xc (Tc + s)` path (untruncated re-centred radial path); its truncation
`trunc S (Vpath ω)` is the integrand on the left of R6. -/
def Vpath (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun s => Xc α Q c b ω (Tc α Q c b ω + s)

/-- `Xc` of a continuous path is continuous. -/
theorem continuous_Xc {α Q c : ℝ} {b : ℝ≥0 → Ω → ℝ} {ω : Ω} (hb : Continuous fun s => b s ω) :
    Continuous fun t => Xc α Q c b ω t := by
  have h1 : Continuous fun t : ℝ => √2 * b t.toNNReal ω :=
    continuous_const.mul (hb.comp continuous_real_toNNReal)
  have h2 : Continuous fun t : ℝ => (α - Q) * t := continuous_const.mul continuous_id
  have h3 : Continuous fun t : ℝ => c + (√2 * b t.toNNReal ω + (α - Q) * t) :=
    continuous_const.add (h1.add h2)
  simpa only [Xc, add_assoc] using h3

end ZoomRadial
end QuantumZipper
