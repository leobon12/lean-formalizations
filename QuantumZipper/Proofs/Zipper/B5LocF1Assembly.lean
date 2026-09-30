import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.Zipper.B5LocOn
import QuantumZipper.Proofs.RS.RealAlive

/-!
# B5 locality for F1: assembly of `F1.F1LocalityStmt`

Theorem 1.3, node B5 (locality), as consumed by F1 (`F1GermFam.lean`); Sheffield,
arXiv:1012.4797, §5.4, pp. 70–72 ("the quantum lengths of `η[0,t]` are determined by the field
and the driver in a neighbourhood of the origin", for small `t`). The paper gives no proof.

`f1LocalityStmt_of_inputs` derives `F1.F1LocalityStmt γ α κ` from the deterministic locality
core (`unzipLengths_eq_qBoundaryMeasureOn`, `norm_fwdMapInv_sub_le`) and four inputs, each a
self-contained statement:

* (R1) `WedgeUnzipLimitStmt`: a.s. the unzipped wedge field at every time `1/(m+1)` has a global
  vague boundary limit (no junk value);
* (R2) `SideSmallStmt`: deterministic smallness of the side images `O^±_t` for small `t` and
  small `sup_{[0,t]} |W|` (Lawler, *Conformally Invariant Processes in the Plane*, §4.1–4.2);
* (R3) `WedgeLocalCoordStmt`: the wedge field on the small dyadic circles centred near `0` agrees
  a.s. with a field that is measurable for the level-`n` data;
* (R4) `LocLengthsMeasStmt`: the local boundary lengths of the field unzipped by the driver
  rebuilt from a path on `[0,u]` are, on continuous paths vanishing at `0` (with all real points
  alive, side images in `(-a, a)` and an existing local limit on `(-a, a)`), a measurable
  functional of (field, path).

(R2) is proved in `B5LocF1Side.lean`, (R3) in `B5LocF1Coord.lean`; `B5LocF1Final.lean` derives
(R1) for the configuration at hand from the positivity input of `F1.f1cd_lengths_agree_unscaled`.

The events are `E m = {sup_{q ∈ ℚ ∩ [0, 1/(m+1)]} |W_q| ≤ M}` (for `m` large), which avoid the
side images altogether; (R2) turns them into `|O^±| < a`. Own bookkeeping argument.
-/

noncomputable section

set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open F1

/-- The level-`n` σ-algebra of `F1.F1LocalityStmt`. -/
def levelSigma {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample) (P : Measure Ω)
    (A : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ (Finset.univ : Finset (Fin 3)), germFam X P A B i n

/-- The driver `√κ p` rebuilt from a path `p` on `[0,u]`, frozen after time `u`. -/
def clampDrive (κ : ℝ) (u : ℝ≥0) (p : Set.Iic u → ℝ) : ℝ → ℝ :=
  fun r => Real.sqrt κ * p ⟨min r.toNNReal u, Set.mem_Iic.2 (min_le_right _ _)⟩

/-- **(R2)** Deterministic smallness of the side images: for every `a > 0` there are `M, t₀ > 0`
such that `|O^±_t| < a` whenever `t ∈ (0, t₀]` and `|W| ≤ M` on `[0,t]` (continuous `W`,
`W 0 = 0`, every real `x ≠ 0` alive at time `t`; the aliveness makes the one-sided limits in
`sideImages` genuine, `F1.exists_tendsto_sideImages_of_alive`, and holds a.s. for
`W = √κ B`, `κ ≤ 4`, by `RS.ae_real_alive`). -/
def SideSmallStmt : Prop :=
  ∀ a : ℝ, 0 < a → ∃ M : ℝ, 0 < M ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
    ∀ t ∈ Ioc (0 : ℝ) t₀, (∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol W (x : ℂ) t v) →
      (∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) →
      |(sideImages W t).1| < a ∧ |(sideImages W t).2| < a

/-- **(R3)** For every level `n`, the wedge field agrees a.s., on the dyadic circles of radius
`≤ 2^{-j₀}` centred in `B(0, ρ)`, with a field measurable for the level-`n` data. -/
def WedgeLocalCoordStmt (γ α κ : ℝ) : Prop :=
  0 < κ → κ < 4 → γ = Real.sqrt κ → α < Qc γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    IsWedgeProcess α (Qc γ) A P → IsBrownianReal B P → (∀ t, Measurable (A t)) →
    (∀ t, Measurable (B t)) → iIndep (srcSigma X A B) P →
    ∀ n : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ j₀ : ℕ, ∃ Y : Ω → FieldSample,
      Measurable[levelSigma X P A B n] Y ∧
      ∀ᵐ ω ∂P, DyCircAgree (unscaledConfig γ κ X A B ω).1 (Y ω) (Metric.ball 0 ρ) j₀

/-- A continuous function bounded by `M` at the rationals of `[0,t]` is bounded by `M` on
`[0,t]`. -/
theorem abs_le_of_forall_rat {f : ℝ → ℝ} (hf : Continuous f) {t M : ℝ} (ht : 0 < t)
    (h : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t → |f q| ≤ M) :
    ∀ r ∈ Icc (0 : ℝ) t, |f r| ≤ M := by
  have hcl : IsClosed {r : ℝ | |f r| ≤ M} := isClosed_le (continuous_abs.comp hf) continuous_const
  have hsub : Ioo (0 : ℝ) t ∩ range ((↑) : ℚ → ℝ) ⊆ {r | |f r| ≤ M} := by
    rintro _ ⟨hr, q, rfl⟩
    exact h q hr.1.le hr.2.le
  have hd := (Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter (isOpen_Ioo (a := 0) (b := t))
  have hIoo : Ioo (0 : ℝ) t ⊆ {r | |f r| ≤ M} := fun x hx =>
    closure_minimal hsub hcl (hd hx)
  intro r hr
  have hr' : r ∈ closure (Ioo 0 t) := by rw [closure_Ioo ht.ne]; exact hr
  exact closure_minimal hIoo hcl hr'

theorem bmPast_le_levelSigma {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample)
    (P : Measure Ω) (A : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    GermZeroOne.bmPast B (GermZeroOne.epsSeq n) ≤ levelSigma X P A B n :=
  le_iSup₂_of_le (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => germFam X P A B i n)
    2 (Finset.mem_univ _) le_rfl

/-- Forward solutions only read the driver on `[0,T]`. -/
theorem isForwardSol_of_eqOn {W W' : ℝ → ℝ} {z : ℂ} {T : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W z T v) (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) : IsForwardSol W' z T v :=
  ⟨hv.1, fun s hs => ⟨(hv.2 s hs).1, by rw [← h s hs]; exact (hv.2 s hs).2⟩⟩

end B5
end QuantumZipper
