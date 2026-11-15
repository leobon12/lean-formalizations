/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafRun
import InteractingSLE.Spec.Supplement.GW1PieceSimpleProof

/-!
# GB6's first contacts at rational times, as a measurable event (pathwise part)

Packet PROVE-T14-GW4REG. GW1 (p. 619): "Apply GB6, within the independently established complete conditional pair in
item 2, to every available interior-tip prefix of `β_j`. It lies in `η[0, T_{w_j}]` in reverse first-visit order."
GB6 holds under the regular conditional law at the launch; to bring it back to `P` it must be a measurable event
(ruling R51, as for `GW1Z.PieceVisitEvent`). Here, for a piece `α` (chart coordinates, rational values `A`) and the
conditional counterflow trace `γ` (rational values `G`, physical points `−1/γ`):

* `FCAt A G S`: at every rational `q ∈ (0, S)` with an interior tip and every rational `r`, if `α(q)` keeps a
  positive distance from the counterflow points at rational times `≤ r`, so does `α([0, q])` (at rational times);
* `measurable_fcAt`;
* `fcAt_of_firstContact`: GB6's first-contact assertion at the rational interior-tip times gives `FCAt`;
* `firstVisit_le_of_fcAt`: conversely `FCAt` (and a visit of `α(q)`) gives the first-contact minimality
  `T(α(q)) ≤ T(α(v))`, `v ≤ q`, in terms of `GB11.firstVisit`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW1Z

/-- **First contacts at rational times**: at every rational interior-tip time `q ∈ (0, S)` and rational `r`, if `A(q)`
keeps a positive distance from the points `−1/G(u)`, `u ≤ r` rational, then so do all `A(v)`, `v ≤ q` rational. -/
def FCAt (A G : ℝ≥0 → ℂ) (S : ℝ≥0∞) : Prop :=
  ∀ q r : ℚ, 0 < rt q → (rt q : ℝ≥0∞) < S → 0 < (A (rt q)).im →
    (∃ n : ℕ, ∀ u : ℚ, rt u ≤ rt r → G (rt u) ≠ 0 → 1 / ((n : ℝ) + 1) ≤ ‖A (rt q) + (G (rt u))⁻¹‖) →
      ∃ n : ℕ, ∀ u v : ℚ, rt u ≤ rt r → rt v ≤ rt q → G (rt u) ≠ 0 →
        1 / ((n : ℝ) + 1) ≤ ‖A (rt v) + (G (rt u))⁻¹‖

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_fcAt {A G : ℝ≥0 → Ω → ℂ} (hA : ∀ t, Measurable (A t)) (hG : ∀ t, Measurable (G t))
    {S : Ω → ℝ≥0∞} (hS : Measurable S) :
    Measurable fun ω => FCAt (fun t => A t ω) (fun t => G t ω) (S ω) := by
  unfold FCAt
  refine Measurable.forall fun q => Measurable.forall fun r => Measurable.imp measurable_const
    (Measurable.imp ?_ (Measurable.imp ?_ (Measurable.imp ?_ ?_)))
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hS)
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const (Complex.measurable_im.comp (hA _)))
  · refine Measurable.exists fun n => Measurable.forall fun u => Measurable.imp measurable_const
      (Measurable.imp ?_ ?_)
    · exact (measurableSet_setOfPred.1 (measurableSet_eq_fun (hG _) measurable_const)).not
    · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const ((hA _).add (hG _).inv).norm)
  · refine Measurable.exists fun n => Measurable.forall fun u => Measurable.forall fun v =>
      Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp ?_ ?_))
    · exact (measurableSet_setOfPred.1 (measurableSet_eq_fun (hG _) measurable_const)).not
    · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const ((hA _).add (hG _).inv).norm)

end Meas

/-! ### A compactness bound -/

/-- `‖a + 1/g‖ ≥ ‖a g + 1‖ / M` when `‖g‖ ≤ M`. -/
theorem div_le_norm_add_inv {a g : ℂ} (hg : g ≠ 0) {M : ℝ} (hM : 0 < M) (hgM : ‖g‖ ≤ M) :
    ‖a * g + 1‖ / M ≤ ‖a + g⁻¹‖ := by
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have h1 : a * g + 1 = (a + g⁻¹) * g := by field_simp
  rw [h1, norm_mul, div_le_iff₀ hM]
  exact mul_le_mul_of_nonneg_left hgM (norm_nonneg _)

/-- **A uniform positive distance on a compact time window.** If `α` is continuous on `[0, b]`, `γ` is continuous,
and no `−1/γ(u)` with `u ≤ a` equals any `α(v)` with `v ≤ b`, then the distances `‖α(v) + γ(u)⁻¹‖` (`γ(u) ≠ 0`) are
bounded below by `1/(n+1)` for some `n`. -/
theorem exists_uniform_sep {α γ : ℝ≥0 → ℂ} {a b : ℝ≥0} (hα : ContinuousOn α (Icc 0 b)) (hγ : Continuous γ)
    (hsep : ∀ u ≤ a, ∀ v ≤ b, γ u ≠ 0 → -(γ u)⁻¹ ≠ α v) :
    ∃ n : ℕ, ∀ u ≤ a, ∀ v ≤ b, γ u ≠ 0 → 1 / ((n : ℝ) + 1) ≤ ‖α v + (γ u)⁻¹‖ := by
  set K : Set (ℝ≥0 × ℝ≥0) := Icc 0 a ×ˢ Icc 0 b with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := ⟨(0, 0), ⟨zero_le, zero_le⟩, ⟨zero_le, zero_le⟩⟩
  set F : ℝ≥0 × ℝ≥0 → ℝ := fun x => ‖α x.2 * γ x.1 + 1‖ with hF
  have hFc : ContinuousOn F K := by
    refine (((hα.comp continuousOn_snd fun x hx => hx.2).mul
      (hγ.comp continuous_fst).continuousOn).add continuousOn_const).norm
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hKc.exists_isMinOn hKne hFc
  have hm : 0 < F x₀ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have hγ0 : γ x₀.1 ≠ 0 := by
      intro hz
      rw [hz, mul_zero, zero_add] at h0
      exact one_ne_zero h0
    apply hsep x₀.1 hx₀K.1.2 x₀.2 hx₀K.2.2 hγ0
    have : α x₀.2 = -(γ x₀.1)⁻¹ := by
      field_simp
      linear_combination h0
    exact this.symm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).exists_bound_of_continuousOn
    hγ.continuousOn
  set M' : ℝ := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hm hM'pos)
  refine ⟨n, fun u hu v hv hγu => ?_⟩
  have hmin : F x₀ ≤ F (u, v) := hx₀min ⟨⟨zero_le, hu⟩, ⟨zero_le, hv⟩⟩
  have hgM : ‖γ u‖ ≤ M' := (hM u ⟨zero_le, hu⟩).trans (le_max_left _ _)
  calc 1 / ((n : ℝ) + 1) ≤ F x₀ / M' := hn.le
    _ ≤ F (u, v) / M' := div_le_div_of_nonneg_right hmin hM'pos.le
    _ ≤ ‖α v + (γ u)⁻¹‖ := div_le_norm_add_inv hγu hM'pos hgM

/-! ### From GB6's first contacts to the event -/

theorem neg_inv_ne_of_firstContact {α γ : ℝ≥0 → ℂ} {s T : ℝ≥0}
    (hfirst : ∀ t < T, Supp8.GB6.sphereInv (γ t : OnePoint ℂ) ∉ (fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    {u v : ℝ≥0} (hu : u < T) (hv : v ≤ s) (hγu : γ u ≠ 0) : -(γ u)⁻¹ ≠ α v := by
  intro heq
  apply hfirst u hu
  refine ⟨v, ⟨zero_le, hv⟩, ?_⟩
  show ((α v : ℂ) : OnePoint ℂ) = Supp8.GB6.sphereInv (γ u : OnePoint ℂ)
  simp only [Supp8.GB6.sphereInv_coe, hγu, ↓reduceIte, heq]

/-- **GB6's first contacts give the event `FCAt`.** -/
theorem fcAt_of_firstContact {α γ A G : ℝ≥0 → ℂ} {S : ℝ≥0∞}
    (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ S}) (hγ : Continuous γ)
    (hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < S → A (rt q) = α (rt q)) (hG : ∀ r : ℚ, G (rt r) = γ (rt r))
    (hfc : ∀ q : ℚ, 0 < rt q → (rt q : ℝ≥0∞) < S → α (rt q) ∈ H →
      Supp8.GB6.IsFirstContactAtTip (fun t => Supp8.GB6.sphereInv (γ t : OnePoint ℂ)) (fun t => (α t : OnePoint ℂ))
        (rt q)) :
    FCAt A G S := by
  intro q r hq hqS hqH hn
  rw [hA q hqS] at hqH hn
  obtain ⟨T, hTη, hTfirst⟩ := hfc q hq hqS hqH
  obtain ⟨hγT, hαq⟩ := sphereInv_eq_coe hTη
  have hrT : rt r < T := by
    by_contra hle
    push Not at hle
    obtain ⟨n, hn⟩ := hn
    have hcont : ContinuousAt (fun u => ‖α (rt q) + (γ u)⁻¹‖) T :=
      (continuousAt_const.add (hγ.continuousAt.inv₀ hγT)).norm
    have h0 : ‖α (rt q) + (γ T)⁻¹‖ = 0 := by rw [hαq]; simp
    have hev : ∀ᶠ u in 𝓝 T, ‖α (rt q) + (γ u)⁻¹‖ < 1 / ((n : ℝ) + 1) ∧ γ u ≠ 0 := by
      refine (hcont.eventually (gt_mem_nhds (by show ‖α (rt q) + (γ T)⁻¹‖ < _; rw [h0]; positivity))).and ?_
      exact hγ.continuousAt.eventually_ne hγT
    have hgood : ∃ u : ℚ, rt u ≤ rt r ∧ ‖α (rt q) + (γ (rt u))⁻¹‖ < 1 / ((n : ℝ) + 1) ∧ γ (rt u) ≠ 0 := by
      rcases hle.lt_or_eq with hlt | heq
      · obtain ⟨w, hTw, hsub⟩ := exists_Ico_subset_of_mem_nhds hev ⟨rt r, hlt⟩
        obtain ⟨u, hu1, hu2⟩ := exists_rt_btwn (lt_min hTw hlt)
        exact ⟨u, (hu2.trans_le (min_le_right _ _)).le,
          hsub ⟨hu1.le, hu2.trans_le (min_le_left _ _)⟩⟩
      · exact ⟨r, le_rfl, heq ▸ hev.self_of_nhds⟩
    obtain ⟨u, hur, hlt, hγu⟩ := hgood
    have := hn u hur (by rw [hG u]; exact hγu)
    rw [hG u] at this
    linarith
  have hαc : ContinuousOn α (Icc 0 (rt q)) := hα.mono fun t ht =>
    (show (t : ℝ≥0∞) ≤ S from le_trans (ENNReal.coe_le_coe.2 ht.2) hqS.le)
  obtain ⟨n, hn'⟩ := exists_uniform_sep (a := rt r) hαc hγ fun u hu v hv hγu =>
    neg_inv_ne_of_firstContact hTfirst (lt_of_le_of_lt hu hrT) hv hγu
  refine ⟨n, fun u v hu hv hGu => ?_⟩
  rw [hG u] at hGu ⊢
  rw [hA v (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv) hqS)]
  exact hn' _ hu _ hv hGu

/-! ### From the event to first-contact minimality -/

/-- Rational own times `≤ b` converging to `v ≤ b`. -/
theorem exists_seq_rt_le {v : ℝ≥0} {b : ℚ} (hv : v ≤ rt b) :
    ∃ w : ℕ → ℚ, (∀ n, rt (w n) ≤ rt b) ∧ Tendsto (fun n => rt (w n)) atTop (𝓝 v) := by
  rcases hv.lt_or_eq with hlt | heq
  · obtain ⟨w, hw, hwt⟩ := exists_seq_rt_right hlt
    exact ⟨w, fun n => (hw n).2.le, hwt⟩
  · exact ⟨fun _ => b, fun _ => le_rfl, by rw [heq]; exact tendsto_const_nhds⟩

/-- **`FCAt` gives first-contact minimality**: at a rational interior-tip time `q < S` whose point is visited, every
earlier point of the piece is first visited no earlier. -/
theorem firstVisit_le_of_fcAt {α γ A G : ℝ≥0 → ℂ} {S : ℝ≥0∞}
    (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ S}) (hγ : Continuous γ)
    (hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < S → A (rt q) = α (rt q)) (hG : ∀ r : ℚ, G (rt r) = γ (rt r))
    (hfc : FCAt A G S) {q : ℚ} (hq : 0 < rt q) (hqS : (rt q : ℝ≥0∞) < S) (hqH : α (rt q) ∈ H)
    (hvis : GB11.firstVisit γ (α (rt q)) < ⊤) {v : ℝ≥0} (hv : v ≤ rt q) :
    GB11.firstVisit γ (α (rt q)) ≤ GB11.firstVisit γ (α v) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t₀, ht₀, hγt₀, hγv⟩ := GW4Reg.exists_eq_firstVisit hγ (hlt.trans hvis)
  obtain ⟨T₀, hT₀, -, -⟩ := GW4Reg.exists_eq_firstVisit hγ hvis
  have ht₀T₀ : t₀ < T₀ := by
    have : (t₀ : ℝ≥0∞) < T₀ := by rw [ht₀, hT₀]; exact hlt
    exact_mod_cast this
  obtain ⟨r, hr1, hr2⟩ := exists_rt_btwn ht₀T₀
  -- `α(q)` keeps a positive distance from the counterflow up to `r`
  have hsepq : ∀ u ≤ rt r, ∀ w ≤ (0 : ℝ≥0), γ u ≠ 0 → -(γ u)⁻¹ ≠ (fun _ : ℝ≥0 => α (rt q)) w := by
    intro u hu _ _ hγu heq
    have h1 : GB11.firstVisit γ (α (rt q)) ≤ u := by
      have := GB11.firstVisit_le hγu
      rwa [heq] at this
    rw [← hT₀] at h1
    exact absurd (lt_of_le_of_lt hu hr2) (not_lt.2 (by exact_mod_cast h1))
  obtain ⟨n₀, hn₀⟩ := exists_uniform_sep (a := rt r) (b := 0) continuousOn_const hγ hsepq
  obtain ⟨n, hn⟩ := hfc q r hq hqS (by rw [hA q hqS]; exact hqH) ⟨n₀, fun u hu hGu => by
    rw [hA q hqS, hG u]
    rw [hG u] at hGu
    exact hn₀ _ hu 0 le_rfl hGu⟩
  -- rational times approaching `(t₀, v)`
  obtain ⟨useq, hu, hut⟩ := exists_seq_rt_right hr1
  obtain ⟨vseq, hvle, hvt⟩ := exists_seq_rt_le hv
  have hvS : (v : ℝ≥0∞) ≤ S := le_trans (ENNReal.coe_le_coe.2 hv) hqS.le
  have hαt : Tendsto (fun k => α (rt (vseq k))) atTop (𝓝 (α v)) := by
    refine (hα v hvS).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hvt, Eventually.of_forall fun k => ?_⟩)
    exact (show (rt (vseq k) : ℝ≥0∞) ≤ S from le_trans (ENNReal.coe_le_coe.2 (hvle k)) hqS.le)
  have hγt : Tendsto (fun k => (γ (rt (useq k)))⁻¹) atTop (𝓝 (γ t₀)⁻¹) :=
    ((hγ.tendsto t₀).comp hut).inv₀ hγt₀
  have hlim : Tendsto (fun k => ‖α (rt (vseq k)) + (γ (rt (useq k)))⁻¹‖) atTop (𝓝 0) := by
    have h0 : α v + (γ t₀)⁻¹ = 0 := by rw [← hγv]; ring
    have := (hαt.add hγt).norm
    rwa [h0, norm_zero] at this
  have hev : ∀ᶠ k in atTop, γ (rt (useq k)) ≠ 0 :=
    ((hγ.tendsto t₀).comp hut).eventually (isOpen_ne.mem_nhds hγt₀)
  have hge : ∀ᶠ k in atTop, 1 / ((n : ℝ) + 1) ≤ ‖α (rt (vseq k)) + (γ (rt (useq k)))⁻¹‖ := by
    filter_upwards [hev] with k hk
    have := hn (useq k) (vseq k) (hu k).2.le (hvle k) (by rw [hG]; exact hk)
    rwa [hG, hA _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hvle k)) hqS)] at this
  have := ge_of_tendsto hlim hge
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

end GW4Leaf

end Theorem14

end InteractingSLE
