import QuantumZipper.Proofs.Zipper.UnifClAnchor

/-!
# UNIF-AW, deterministic part: from time-continuous window limits to anchored windows

Task UNIF-AW (decision D26, `handoff/REG-UNIF.md`, UNIF-CLUSTER). This file is purely
deterministic (one sample `ω`, abstract measures).

Setting: `νT` a locally finite measure (the boundary measure of the fully unzipped field `h⁰_T`),
`A s k` measures on `ℝ` (the approximations `bdryApprox γ h⁰_s k`), `ν r` measures (the boundary
measures of `h⁰_r` at rational times `r`), `F s` real maps (`F_s = realRevMap V (T − s)`) which
agree on a window `[u,v]` with order isomorphisms of `ℝ`.

* `awTest F u v f`: the test function `f` (supported in `(u,v)`, the fully unzipped picture)
  transported to the time-`s` picture, `f ∘ F⁻¹` on `F(u,v)` and `0` elsewhere.
* `restrict_eq_map_symm`: if `νT (a,b) = ν_r (F a, F b)` for all rational subwindows, then
  `νT|_{(u,v)} = (F⁻¹)_* (ν_r|_{F(u,v)})` (π-system of rational open intervals).
* **`det_anchor`**: if (i) at rational times `r` the approximations converge vaguely to `ν r` and
  the window identities hold, and (ii) for every test function `f` the transported integrals
  `∫ awTest (F s) u v f d(A s k)` converge as `k → ∞` for **every** `s ∈ [q,T]` to a limit that
  is continuous in `s`, then for every `s ∈ [q,T]` the approximations `A s` have a local vague
  limit on `F_s(u,v)` of mass `νT (u,v)`.

The reduction is own bookkeeping (a density argument in `s`); the analytic input (ii) is the
uniform-in-time coordinate change (Sheffield–Wang, arXiv:1605.06171, Thm 4.3; Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 2.1 / §6 for one fixed map).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace RegUnif

/-- The test function `f` transported by `F`: `f (F⁻¹ x)` for `x ∈ F(u,v)`, else `0`. -/
def awTest (F : ℝ → ℝ) (u v : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  open Classical in if h : ∃ y ∈ Ioo u v, F y = x then f h.choose else 0

theorem awTest_eq {F : ℝ → ℝ} {u v : ℝ} {Φ : ℝ ≃o ℝ} (hΦ : ∀ y ∈ Icc u v, Φ y = F y)
    {f : ℝ → ℝ} (hf : tsupport f ⊆ Ioo u v) : awTest F u v f = f ∘ Φ.symm := by
  funext x
  simp only [awTest, Function.comp]
  split_ifs with h
  · obtain ⟨hy, hFy⟩ := h.choose_spec
    congr 1
    apply Φ.injective
    rw [OrderIso.apply_symm_apply, hΦ _ (Ioo_subset_Icc_self hy), hFy]
  · symm
    by_contra hne
    have hmem : Φ.symm x ∈ Ioo u v := hf (subset_tsupport f (Function.mem_support.2 hne))
    exact h ⟨Φ.symm x, hmem, by
      rw [← hΦ _ (Ioo_subset_Icc_self hmem), OrderIso.apply_symm_apply]⟩

theorem tsupport_comp_subset_preimage' {f g : ℝ → ℝ} (hg : Continuous g) :
    tsupport (f ∘ g) ⊆ g ⁻¹' tsupport f :=
  closure_minimal (fun x hx => subset_tsupport f hx) ((isClosed_tsupport f).preimage hg)

theorem hasCompactSupport_comp_orderIso {f : ℝ → ℝ} (hf : HasCompactSupport f) (Φ : ℝ ≃o ℝ) :
    HasCompactSupport (f ∘ Φ) := by
  have := hf.comp_isClosedEmbedding Φ.toHomeomorph.isClosedEmbedding
  rwa [OrderIso.coe_toHomeomorph] at this

/-- Integral of a function vanishing off `S` against `μ` equals that against `μ|_S`. -/
theorem integral_eq_restrict_of_support {μ : Measure ℝ} {S : Set ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, x ∉ S → f x = 0) : ∫ x, f x ∂μ = ∫ x, f x ∂(μ.restrict S) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

/-- **Window identities ⇒ pushforward identity.** -/
theorem restrict_eq_map_symm {νT νs : Measure ℝ} {F : ℝ → ℝ} {u v : ℚ} (huv : (u : ℝ) < v)
    {Φ : ℝ ≃o ℝ} (hΦ : ∀ y ∈ Icc (u : ℝ) v, Φ y = F y) (hfin : νT (Ioo (u : ℝ) v) < ∞)
    (hwin : ∀ a b : ℚ, (u : ℝ) ≤ a → (a : ℝ) < b → (b : ℝ) ≤ v →
      νT (Ioo a b) = νs (Ioo (F a) (F b))) :
    νT.restrict (Ioo (u : ℝ) v) = (νs.restrict (Ioo (F u) (F v))).map Φ.symm := by
  have hFu : F u = Φ u := (hΦ u ⟨le_rfl, huv.le⟩).symm
  have hFv : F v = Φ v := (hΦ v ⟨huv.le, le_rfl⟩).symm
  have : IsFiniteMeasure (νT.restrict (Ioo (u : ℝ) v)) := isFiniteMeasure_restrict.2 hfin.ne
  have hm : Measurable Φ.symm := Φ.symm.continuous.measurable
  refine ext_of_generate_finite _ (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Ioo_rat)
    Real.isPiSystem_Ioo_rat ?_ ?_
  · intro S hS
    simp only [mem_iUnion, mem_singleton_iff] at hS
    obtain ⟨a, b, -, rfl⟩ := hS
    rw [Measure.restrict_apply measurableSet_Ioo, Measure.map_apply hm measurableSet_Ioo,
      Measure.restrict_apply (hm measurableSet_Ioo), OrderIso.preimage_Ioo, OrderIso.symm_symm,
      hFu, hFv, Ioo_inter_Ioo, Ioo_inter_Ioo, ← Φ.map_sup, ← Φ.map_inf]
    have ha' : (((max a u : ℚ)) : ℝ) = (a : ℝ) ⊔ u := by push_cast; rfl
    have hb' : (((min b v : ℚ)) : ℝ) = (b : ℝ) ⊓ v := by push_cast; rfl
    rw [← ha', ← hb']
    by_cases hlt : (((max a u : ℚ)) : ℝ) < ((min b v : ℚ) : ℝ)
    · have hu' : (u : ℝ) ≤ ((max a u : ℚ) : ℝ) := by rw [ha']; exact le_sup_right
      have hv' : (((min b v : ℚ)) : ℝ) ≤ v := by rw [hb']; exact inf_le_right
      rw [hΦ _ ⟨hu', (hlt.trans_le hv').le⟩, hΦ _ ⟨hu'.trans hlt.le, hv'⟩]
      exact hwin _ _ hu' hlt hv'
    · rw [Ioo_eq_empty hlt, Ioo_eq_empty (fun h => hlt (Φ.lt_iff_lt.1 h))]
      simp
  · rw [Measure.restrict_apply_univ, Measure.map_apply hm MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    exact hwin u v le_rfl huv le_rfl

/-- `∫ f dνT = ∫ f ∘ Φ⁻¹ dνs` at a time where the window identities hold. -/
theorem integral_eq_of_windows {νT νs : Measure ℝ} {F : ℝ → ℝ} {u v : ℚ} (huv : (u : ℝ) < v)
    {Φ : ℝ ≃o ℝ} (hΦ : ∀ y ∈ Icc (u : ℝ) v, Φ y = F y) (hfin : νT (Ioo (u : ℝ) v) < ∞)
    (hwin : ∀ a b : ℚ, (u : ℝ) ≤ a → (a : ℝ) < b → (b : ℝ) ≤ v →
      νT (Ioo a b) = νs (Ioo (F a) (F b)))
    {f : ℝ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ Ioo (u : ℝ) v) :
    ∫ x, f x ∂νT = ∫ x, (f ∘ Φ.symm) x ∂νs := by
  have hFu : F u = Φ u := (hΦ u ⟨le_rfl, huv.le⟩).symm
  have hFv : F v = Φ v := (hΦ v ⟨huv.le, le_rfl⟩).symm
  have h0 : ∀ x, x ∉ Ioo (u : ℝ) v → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hfs h))
  rw [integral_eq_restrict_of_support h0, restrict_eq_map_symm huv hΦ hfin hwin,
    integral_map Φ.symm.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  refine (integral_eq_restrict_of_support (f := f ∘ Φ.symm) fun x hx => h0 _ fun h => hx ?_).symm
  rw [hFu, hFv]
  exact ⟨by simpa using Φ.strictMono h.1, by simpa using Φ.strictMono h.2⟩

/-- A function continuous on `[q,T]` (`q` rational) and equal to `c` at the rational points is
`c` on `[q,T]`. -/
theorem eq_const_of_rat {q : ℚ} {T : ℝ} {L : ℝ → ℝ} {c : ℝ} (hL : ContinuousOn L (Icc (q : ℝ) T))
    (hr : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → L r = c) : ∀ s ∈ Icc (q : ℝ) T, L s = c := by
  intro s hs
  rcases hs.1.eq_or_lt with h | h
  · rw [← h]; exact hr q ⟨le_rfl, h.le.trans hs.2⟩
  · refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨δ, hδ, hδL⟩ := Metric.continuousWithinAt_iff.1 (hL s hs) ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt h (sub_lt_self s hδ))
    have hrm : (r : ℝ) ∈ Icc (q : ℝ) T := ⟨(le_max_left _ _).trans hr1.le, hr2.le.trans hs.2⟩
    have hd : dist (r : ℝ) s < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right (q : ℝ) (s - δ)]
    have := hδL hrm hd
    rw [hr r hrm, dist_comm] at this
    exact this.le

/-- **Deterministic core of AW.** Rational-time identities plus time-continuous limits of the
transported test integrals give, at every `s ∈ [q,T]`, a local vague limit on `F_s(u,v)` with
the mass `νT (u,v)`. -/
theorem det_anchor {q : ℚ} {T : ℝ} {u v : ℚ} (huv : (u : ℝ) < v) {A : ℝ → ℕ → Measure ℝ}
    {ν : ℝ → Measure ℝ} {νT : Measure ℝ} (hfin : νT (Ioo (u : ℝ) v) < ∞) {F : ℝ → ℝ → ℝ}
    (hΦ : ∀ s ∈ Icc (q : ℝ) T, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc (u : ℝ) v, Φ y = F s y)
    (hlim : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → IsVagueLimitR (A r) (ν r))
    (hwin : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → ∀ a b : ℚ, (u : ℝ) ≤ a → (a : ℝ) < b →
      (b : ℝ) ≤ v → νT (Ioo a b) = ν r (Ioo (F r a) (F r b)))
    (hconv : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∃ L : ℝ → ℝ, ContinuousOn L (Icc (q : ℝ) T) ∧ ∀ s ∈ Icc (q : ℝ) T,
        Tendsto (fun k => ∫ x, awTest (F s) u v f x ∂A s k) atTop (𝓝 (L s))) :
    ∀ s ∈ Icc (q : ℝ) T, ∃ μ : Measure ℝ, IsVagueLimitOnR (Ioo (F s u) (F s v)) (A s) μ ∧
      μ (Ioo (F s u) (F s v)) = νT (Ioo (u : ℝ) v) := by
  -- step 1: the limits are the constant `∫ f dνT`
  have hconst : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∀ s ∈ Icc (q : ℝ) T, Tendsto (fun k => ∫ x, awTest (F s) u v f x ∂A s k) atTop
        (𝓝 (∫ x, f x ∂νT)) := by
    intro f hf hfc hfs
    obtain ⟨L, hLc, hLt⟩ := hconv f hf hfc hfs
    have hr : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → L r = ∫ x, f x ∂νT := by
      intro r hr
      obtain ⟨Φ, hΦr⟩ := hΦ r hr
      have hg := awTest_eq hΦr hfs
      have hlimr := (hlim r hr).2 (awTest (F r) u v f) (by rw [hg]; exact hf.comp Φ.symm.continuous)
        (by rw [hg]; exact hasCompactSupport_comp_orderIso hfc Φ.symm)
      refine (tendsto_nhds_unique (hLt r hr) hlimr).trans ?_
      rw [hg]
      exact (integral_eq_of_windows huv hΦr hfin (hwin r hr) hf hfs).symm
    intro s hs
    rw [← eq_const_of_rat hLc hr s hs]
    exact hLt s hs
  -- step 2: the pushforward of `νT|_{(u,v)}` is the local limit
  intro s hs
  obtain ⟨Φ, hΦs⟩ := hΦ s hs
  have hFu : F s u = Φ u := (hΦs u ⟨le_rfl, huv.le⟩).symm
  have hFv : F s v = Φ v := (hΦs v ⟨huv.le, le_rfl⟩).symm
  have hm : Measurable Φ := Φ.continuous.measurable
  have hpre : Φ ⁻¹' Ioo (F s u) (F s v) = Ioo (u : ℝ) v := by
    rw [hFu, hFv, OrderIso.preimage_Ioo, OrderIso.symm_apply_apply, OrderIso.symm_apply_apply]
  set μ := (νT.restrict (Ioo (u : ℝ) v)).map Φ with hμ
  have hμW : μ (Ioo (F s u) (F s v)) = νT (Ioo (u : ℝ) v) := by
    rw [hμ, Measure.map_apply hm measurableSet_Ioo, hpre, Measure.restrict_apply measurableSet_Ioo,
      inter_self]
  refine ⟨μ, ⟨?_, fun K _ _ => ?_, fun g hg hgc hgs => ?_⟩, hμW⟩
  · rw [hμ, Measure.map_apply hm measurableSet_Ioo.compl, preimage_compl, hpre,
      Measure.restrict_apply measurableSet_Ioo.compl]
    simp
  · calc μ K ≤ μ univ := measure_mono (subset_univ _)
      _ < ∞ := by
        rw [hμ, Measure.map_apply hm MeasurableSet.univ, preimage_univ,
          Measure.restrict_apply_univ]
        exact hfin
  · set f := g ∘ Φ with hfdef
    have hfc : Continuous f := hg.comp Φ.continuous
    have hfcs : HasCompactSupport f := hasCompactSupport_comp_orderIso hgc Φ
    have hfs : tsupport f ⊆ Ioo (u : ℝ) v :=
      (tsupport_comp_subset_preimage' Φ.continuous).trans (by rw [← hpre]; exact preimage_mono hgs)
    have hg' : awTest (F s) u v f = g := by
      rw [awTest_eq hΦs hfs]
      funext x
      simp [f]
    have hint : ∫ t, g t ∂μ = ∫ x, f x ∂νT := by
      rw [hμ, integral_map hm.aemeasurable hg.aestronglyMeasurable]
      exact (integral_eq_restrict_of_support fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => hx (hfs h)).symm
    have := hconst f hfc hfcs hfs s hs
    rw [hg'] at this
    rw [hint]
    exact this

end RegUnif
end QuantumZipper
