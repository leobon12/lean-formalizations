import QuantumZipper.Proofs.Thm11.FrozenMartingales
import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# THM11-AD3: the frozen fields and the true field (pathwise consistency)

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Theorem 1.1 addendum
(§1, p. 12). For the left limit of `𝔥_s(a) = h0fwd κ (f_s(a)) − χ Im log f_s'(a)` at the
swallowing time of `a` (κ ∈ (4,8)) we work with the frozen fields of `FrozenMartingales`
(tamed flow at level `c`, frozen when `Im` first reaches `δ ≥ c`). This file proves, pathwise:

* up to the freezing time the tamed state is the true state `(f_t(a), Im log f_t'(a))`, so the
  frozen field is the true field stopped at the freezing time (`frozenField_eq_fieldAt`);
* the freezing time does not depend on the taming level `c ≤ δ` (`frozenTime_congr`);
* the true path is alive up to the freezing time, and when the freezing time is `< T` the level
  `δ` is reached (`ofReal_frozenTime_le_swallowTime`, `im_fwdMap_frozenTime_le`).

Own elementary proofs (the agreement lemmas `fwdMap_eq_tamedZ`, `im_logDerivFwd_eq_tamedA` of
`ForwardTamed` do the analytic work).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm11Add

open FrozenMart

/-- The true one-point field `𝔥_t(a) = h0fwd κ (f_t(a)) − χ Im log f_t'(a)`. -/
def fieldAt (κ : ℝ) (W : ℝ → ℝ) (a : ℂ) (t : ℝ) : ℝ :=
  h0fwd κ (fwdMap W t a) - chiC κ * (logDerivFwd W t a).im

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

theorem fzZ_im_ge (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) {a : ℂ}
    (hδa : δ ≤ a.im) {T : ℝ≥0} (ω : Ω) {t : ℝ≥0} (ht : t ≤ frozenTime κ c δ T B a ω) :
    δ ≤ (fzZ κ c B a t ω).im := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  refine mem_of_forall_lt_of_isClosed (p := fun s => fzZ κ c B a s ω)
    (continuous_fzZ hBc hc a ω) (isClosed_le continuous_const Complex.continuous_im) ?_ ?_
  · show δ ≤ (tamedZ (drive κ B ω) c a ((0 : ℝ≥0) : ℝ)).im
    rw [NNReal.coe_zero, im_tamedZ_zero hW hc]; exact hδa
  · intro s hs
    have := notMem_of_lt_hittingBtwn (u := fzZ κ c B a) (s := {z : ℂ | z.im ≤ δ}) (n := 0)
      (m := T) (ω := ω) (hs.trans_le ht) zero_le
    simp only [Set.mem_ofPred_eq, not_le] at this
    exact this.le

/-- Up to the freezing time the tamed state is the true state. -/
theorem alive_of_le_frozenTime (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) {T : ℝ≥0} (ω : Ω) {t : ℝ≥0}
    (ht : t ≤ frozenTime κ c δ T B a ω) :
    (∃ u, IsForwardSol (drive κ B ω) a t u) ∧ ∀ r ∈ Icc (0 : ℝ) t,
      fwdMap (drive κ B ω) r a = tamedZ (drive κ B ω) c a r ∧
      (logDerivFwd (drive κ B ω) r a).im = tamedA (drive κ B ω) c a r ∧
      δ ≤ (fwdMap (drive κ B ω) r a).im := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  have ha : 0 < a.im := (hc.trans_le hcδ).trans_le hδa
  have hge : ∀ r ∈ Icc (0 : ℝ) t, δ ≤ (tamedZ (drive κ B ω) c a r).im := by
    intro r hr
    have h1 : r.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
    have := fzZ_im_ge hBc hc hδa ω (h1.trans ht)
    simpa [fzZ, Real.coe_toNNReal _ hr.1] using this
  have him : ∀ r ∈ Icc (0 : ℝ) t, c ≤ (tamedZ (drive κ B ω) c a r).im :=
    fun r hr => hcδ.trans (hge r hr)
  obtain ⟨hsol, heq⟩ := fwdMap_eq_tamedZ hW hc t.coe_nonneg ha him
  have hA := im_logDerivFwd_eq_tamedA hW hc t.coe_nonneg ha him
  exact ⟨hsol, fun r hr => ⟨heq r hr, hA r hr, (heq r hr) ▸ hge r hr⟩⟩

theorem fzU_eq_true (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) {T : ℝ≥0} (ω : Ω) {t : ℝ≥0}
    (ht : t ≤ frozenTime κ c δ T B a ω) :
    fzU κ c B a t ω = (fwdMap (drive κ B ω) t a, (logDerivFwd (drive κ B ω) t a).im) := by
  obtain ⟨-, h⟩ := alive_of_le_frozenTime hBc hc hcδ hδa ω ht
  obtain ⟨h1, h2, -⟩ := h t ⟨t.coe_nonneg, le_rfl⟩
  simp only [fzU, fzZ, fzA, h1, h2]

theorem fzPhi_fzU_eq (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) {T : ℝ≥0} (ω : Ω) {t : ℝ≥0}
    (ht : t ≤ frozenTime κ c δ T B a ω) :
    fzPhi κ (fzU κ c B a t ω) = fieldAt κ (drive κ B ω) a t := by
  rw [fzU_eq_true hBc hc hcδ hδa ω ht]; rfl

/-- The frozen field is the true field stopped at the freezing time. -/
theorem frozenField_eq_fieldAt (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    frozenField κ c δ T B a t ω =
      fieldAt κ (drive κ B ω) a (min t (frozenTime κ c δ T B a ω) : ℝ≥0) :=
  fzPhi_fzU_eq hBc hc hcδ hδa ω (min_le_right _ _)

/-- If the freezing time is `< T`, the level `δ` is reached there. -/
theorem fzZ_frozenTime_mem (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) {a : ℂ}
    {T : ℝ≥0} (ω : Ω) (hlt : frozenTime κ c δ T B a ω < T) :
    (fzZ κ c B a (frozenTime κ c δ T B a ω) ω).im ≤ δ := by
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) T, fzZ κ c B a j ω ∈ {z : ℂ | z.im ≤ δ} := by
    obtain ⟨j, hj, hjS⟩ := (hittingBtwn_lt_iff (u := fzZ κ c B a) (s := {z : ℂ | z.im ≤ δ})
      (n := 0) (ω := ω) T le_rfl).1 hlt
    exact ⟨j, Ico_subset_Icc_self hj, hjS⟩
  exact NonSwallow.hittingBtwn_mem_of_isClosed (X := fzZ κ c B a)
    (isClosed_le Complex.continuous_im continuous_const) (continuous_fzZ hBc hc a ω) hex

theorem frozenTime_le_of (hBc : ∀ ω, Continuous (B · ω)) {κ c c' δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) (hc' : 0 < c') (hc'δ : c' ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) (ω : Ω) :
    frozenTime κ c' δ T B a ω ≤ frozenTime κ c δ T B a ω := by
  by_contra hcon
  push Not at hcon
  set σ := frozenTime κ c δ T B a ω
  have hlt : σ < T := hcon.trans_le (hittingBtwn_le ω)
  have hmem := fzZ_frozenTime_mem hBc hc ω hlt
  have e1 := fzU_eq_true hBc hc hcδ hδa (T := T) ω (le_refl σ)
  have e2 := fzU_eq_true hBc hc' hc'δ hδa (T := T) ω hcon.le
  have e : fzZ κ c' B a σ ω = fzZ κ c B a σ ω := by
    have := congrArg Prod.fst (e2.trans e1.symm); simpa [fzU] using this
  have : frozenTime κ c' δ T B a ω ≤ σ :=
    hittingBtwn_le_of_mem (u := fzZ κ c' B a) (s := {z : ℂ | z.im ≤ δ}) zero_le
      (hittingBtwn_le ω) (by show (fzZ κ c' B a σ ω).im ≤ δ; rw [e]; exact hmem)
  exact absurd hcon (not_lt.2 this)

/-- The freezing time does not depend on the taming level. -/
theorem frozenTime_congr (hBc : ∀ ω, Continuous (B · ω)) {κ c c' δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) (hc' : 0 < c') (hc'δ : c' ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) (ω : Ω) :
    frozenTime κ c δ T B a ω = frozenTime κ c' δ T B a ω :=
  le_antisymm (frozenTime_le_of hBc hc' hc'δ hc hcδ hδa T ω)
    (frozenTime_le_of hBc hc hcδ hc' hc'δ hδa T ω)

/-- The point is alive up to the freezing time. -/
theorem ofReal_frozenTime_le_swallowTime (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ}
    (hc : 0 < c) (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (frozenTime κ c δ T B a ω) ≤ swallowTime (drive κ B ω) a :=
  ofReal_le_swallowTime (frozenTime κ c δ T B a ω).coe_nonneg
    (alive_of_le_frozenTime hBc hc hcδ hδa ω le_rfl).1

/-- The true path at the freezing time, when it is `< T`. -/
theorem im_fwdMap_frozenTime_le (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) {T : ℝ≥0} (ω : Ω)
    (hlt : frozenTime κ c δ T B a ω < T) :
    (fwdMap (drive κ B ω) (frozenTime κ c δ T B a ω) a).im ≤ δ := by
  have h := fzU_eq_true hBc hc hcδ hδa ω (le_refl (frozenTime κ c δ T B a ω))
  have e := congrArg Prod.fst h
  simp only [fzU] at e
  rw [← e]; exact fzZ_frozenTime_mem hBc hc ω hlt

end Thm11Add
end QuantumZipper
