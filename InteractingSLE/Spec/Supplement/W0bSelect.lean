/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.W0bChart
import InteractingSLE.Spec.Supplement.S7Interior
import InteractingSLE.Spec.Supplement.S9Contacts
import InteractingSLE.Spec.Supplement.S9Completion
import InteractingSLE.Spec.Sec7.Lemma77RealTip

/-!
# Lemma W0b, the deterministic selection: rational stops inside a cooriented common arc

Packet PROVE-G12D (specification supplement §9, Lemma W0b, p. 529, `source/spec/p529-576.md#id-W0b-proof`: "The
contact-order theorem for the proper completions makes any common arc cooriented. Choose a compact subarc in its
interior which lies in `ℍ`, and choose rational original own stopping times for both paths strictly after that
compact subarc but still within the common open arc. This is possible because a nontrivial real subarc would have
zero capacity. Injectivity and compactness give positive physical clearance between the chosen compact subarc and
every portion of either retained history outside the common open arc").

Deterministic. Two simple traces `α` from `x₁` and `β` from `x₂ ≤ x₁` (`Restart.IsPathGood`), prefixes `α([0, a])`,
`β([0, c])` strictly before the lifetimes with ordered proper completions (`HasOrderedProperCompletions`) and a common
open subarc (`Supp9.HasCommonOpenSubarc`). `exists_coorientedStops` produces:

* rational stops `q₁ ≤ a`, `q₂ ≤ c` and a common point `p = α(s) = β(t)`, `s < q₁`, `t < q₂`, with `α([l, q₁]) ⊆ ℍ`
  for some `l < s` and `β(q₂) ∈ ℍ` (an interior point exists because a good path is not real on an interval,
  `IsPathGood.exists_mem_H`);
* **the physical clearance**: near `p` the stopped ranges `α([0, q₁])`, `β([0, q₂])` coincide;
* ordered proper completions `α''`, `β''` of these stopped prefixes whose **tails `α''((q₁, ∞))`, `β''((q₂, ∞))` lie
  in `ℍ`** (Lemma G10, `Supp7.exists_interiorized_completions`: every real point of the completions is a real point
  of the prefixes; such a point on a tail would be a contact inside the common arc, which lies in `ℍ`, by the contact
  order `Supp9B.contact_order`).

The common arc is cooriented: the `β`-time `g(u)` of `α(u)` is strictly increasing (contact order) and continuous
(`continuousOn_of_comp_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp9

namespace W0b

open Sec7 Sec7.ReverseArc HalfPlaneSep Supp9B Restart

/-! ### Helpers -/

section Helpers

/-- A compact set avoiding `p` misses a ball about `p`. -/
theorem exists_ball_notMem {S : Set ℂ} (hS : IsCompact S) {p : ℂ} (hp : p ∉ S) :
    ∃ d > 0, ∀ z ∈ S, z ∉ ball p d := by
  obtain ⟨d, hd, h⟩ := Metric.isOpen_iff.1 hS.isClosed.isOpen_compl p hp
  exact ⟨d, hd, fun z hz hzb => h hzb hz⟩

/-- **The inverse of an injective curve on a compact interval is continuous along a continuous curve in its image**
(a continuous injective map of a compact space into a Hausdorff space is an embedding). -/
theorem continuousOn_of_comp_eq {a b T : ℝ≥0} {α β : ℝ≥0 → ℂ} (hα : ContinuousOn α (Icc a b))
    (hβ : ContinuousOn β (Icc 0 T)) (hβi : InjOn β (Icc 0 T)) {g : ℝ≥0 → ℝ≥0}
    (hg : ∀ u ∈ Icc a b, g u ∈ Icc 0 T) (hgeq : ∀ u ∈ Icc a b, β (g u) = α u) : ContinuousOn g (Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  set f : Icc (0 : ℝ≥0) T → ℂ := (Icc 0 T).domRestrict β with hf
  have hfc : Continuous f := hβ.domRestrict
  have hfi : Function.Injective f := fun x y hxy => Subtype.ext (hβi x.2 y.2 hxy)
  have hemb := (hfc.isClosedEmbedding hfi).isEmbedding
  set g' : Icc a b → Icc (0 : ℝ≥0) T := fun u => ⟨g u, hg u u.2⟩ with hg'
  have hg'c : Continuous g' := by
    rw [hemb.continuous_iff]
    have : f ∘ g' = (Icc a b).domRestrict α := funext fun u => hgeq u u.2
    rw [this]
    exact hα.domRestrict
  exact continuous_subtype_val.comp hg'c

/-- A rational number strictly between two nonnegative reals, read in `ℝ≥0`. -/
theorem exists_rat_btwn_nnreal {a b : ℝ≥0} (hab : a < b) :
    ∃ r : ℚ, a < (r : ℝ).toNNReal ∧ (r : ℝ).toNNReal < b := by
  obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
  have hr : (0 : ℝ) ≤ r := (NNReal.coe_nonneg a).trans h1.le
  refine ⟨r, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr]; exact h1
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr]; exact h2

theorem not_mem_H_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z ∉ H := fun hz => by
  have : (0 : ℝ) < z.im := hz
  linarith

theorem im_eq_zero_of_not_mem_H {z : ℂ} (h0 : 0 ≤ z.im) (h : z ∉ H) : z.im = 0 :=
  le_antisymm (not_lt.1 fun hp => h hp) h0

end Helpers

/-! ### The selection -/

section Select

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **The rational stops inside a cooriented common arc, with interiorized completions** (proof of Lemma W0b,
p. 529). -/
theorem exists_coorientedStops (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ ≤ x₁)
    {a c : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ₁) (hc : (c : ℝ≥0∞) < ζ₂)
    (hord : HasOrderedProperCompletions α a β c) (hcom : HasCommonOpenSubarc α a β c) :
    ∃ (r₁ r₂ : ℚ) (l s t : ℝ≥0), (r₁ : ℝ).toNNReal ≤ a ∧ (r₂ : ℝ).toNNReal ≤ c ∧ l < s ∧
      s < (r₁ : ℝ).toNNReal ∧ t < (r₂ : ℝ).toNNReal ∧ β t = α s ∧ α '' Icc l (r₁ : ℝ).toNNReal ⊆ H ∧
      β (r₂ : ℝ).toNNReal ∈ H ∧
      (∃ ρ > 0, α '' Icc 0 (r₁ : ℝ).toNNReal ∩ ball (α s) ρ = β '' Icc 0 (r₂ : ℝ).toNNReal ∩ ball (α s) ρ) ∧
      ∃ α'' β'' : ℝ≥0 → ℂ, IsProperCurve α'' ∧ IsProperCurve β'' ∧ (∀ u ≤ (r₁ : ℝ).toNNReal, α'' u = α u) ∧
        (∀ v ≤ (r₂ : ℝ).toNNReal, β'' v = β v) ∧ range β'' ⊆ closedLeftSide α'' ∧
        (∀ u, (r₁ : ℝ).toNNReal < u → α'' u ∈ H) ∧ (∀ v, (r₂ : ℝ).toNNReal < v → β'' v ∈ H) := by
  classical
  obtain ⟨α', β', hα', hβ', hord'⟩ := hord
  obtain ⟨u₁, u₂, hu₁₂, hu₂a, hsub⟩ := hcom
  have hα0 : α 0 = x₁ := IsPathGood.zero hp₁
  have hβ0 : β 0 = x₂ := IsPathGood.zero hp₂
  have hpc₁ := isProperCurve_of_isProperCompletion hα'
  have hpc₂ := isProperCurve_of_isProperCompletion hβ'
  have hα'0 : α' 0 = x₁ := by rw [hα'.2.2.2.2 0 zero_le, hα0]
  have hβ'0 : β' 0 = x₂ := by rw [hβ'.2.2.2.2 0 zero_le, hβ0]
  have hco : ∀ {s s' t t' : ℝ≥0}, α' s = β' t → α' s' = β' t' → s < s' → t < t' := fun hst hst' hss' =>
    contact_order hpc₁ hpc₂ (by rw [hα'0]; simp) (by rw [hβ'0]; simp) (by rw [hα'0, hβ'0]; simpa using hx) hord'
      hst hst' hss'
  -- an interior point of the common arc, and an interval about it in `ℍ`
  have hu₂ζ : (u₂ : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hu₂a).trans ha.le
  obtain ⟨u₀, hu₀, hu₀H⟩ := IsPathGood.exists_mem_H hp₁ hu₁₂ hu₂ζ
  have hu₀pos : 0 < u₀ := lt_of_le_of_lt zero_le hu₀.1
  have hcont : ContinuousAt α u₀ :=
    (IsPathGood.continuousOn_Icc hp₁ hu₂ζ).continuousAt (Icc_mem_nhds hu₀pos hu₀.2)
  have hnhd : α ⁻¹' H ∩ Ioo u₁ u₂ ∈ 𝓝 u₀ :=
    inter_mem (hcont.preimage_mem_nhds (QuantumZipper.isOpen_H.mem_nhds hu₀H)) (isOpen_Ioo.mem_nhds hu₀)
  obtain ⟨lo, hi, ⟨hlo, hhi⟩, hIoo⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨0, hu₀pos⟩ ⟨u₀ + 1, lt_add_one u₀⟩).1 hnhd
  obtain ⟨l, hlol, hlu₀⟩ := exists_between hlo
  obtain ⟨r, hu₀r, hrhi⟩ := exists_between hhi
  have hIcc : ∀ u ∈ Icc l r, α u ∈ H ∧ u ∈ Ioo u₁ u₂ := fun u hu => hIoo ⟨hlol.trans_le hu.1, hu.2.trans_lt hrhi⟩
  have hlr : l ≤ r := (hlu₀.trans hu₀r).le
  have hra : r ≤ a := ((hIcc r ⟨hlr, le_rfl⟩).2.2.le).trans hu₂a
  have hrζ : (r : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hra).trans ha.le
  have hcζ : (c : ℝ≥0∞) ≤ ζ₂ := hc.le
  -- the `β`-times of the common arc
  have hgex : ∀ u, ∃ v : ℝ≥0, u ∈ Icc l r → v ∈ Icc 0 c ∧ β v = α u := by
    intro u
    by_cases hu : u ∈ Icc l r
    · obtain ⟨v, hv, hve⟩ := hsub ⟨u, (hIcc u hu).2, rfl⟩
      exact ⟨v, fun _ => ⟨hv, hve⟩⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose g hg using hgex
  have hua : ∀ u ∈ Icc l r, u ≤ a := fun u hu => hu.2.trans hra
  have hgα : ∀ u ∈ Icc l r, α' u = β' (g u) := fun u hu => by
    rw [hα'.2.2.2.2 u (hua u hu), hβ'.2.2.2.2 _ (hg u hu).1.2, (hg u hu).2]
  have hmono : StrictMonoOn g (Icc l r) := fun u hu v hv huv => hco (hgα u hu) (hgα v hv) huv
  have hgc : ContinuousOn g (Icc l r) :=
    continuousOn_of_comp_eq (IsPathGood.continuousOn_Icc hp₁ hrζ |>.mono (Icc_subset_Icc_left zero_le))
      (IsPathGood.continuousOn_Icc hp₂ hcζ) (IsPathGood.injOn_Icc hp₂ hcζ) (fun u hu => (hg u hu).1)
      fun u hu => (hg u hu).2
  have hgH : ∀ u ∈ Icc l r, β (g u) ∈ H := fun u hu => (hg u hu).2 ▸ (hIcc u hu).1
  -- the image of a subinterval contains the interval between the end values
  have hivt : ∀ {u v : ℝ≥0}, u ∈ Icc l r → v ∈ Icc l r → u ≤ v → Icc (g u) (g v) ⊆ g '' Icc u v :=
    fun {u v} hu hv huv => intermediate_value_Icc huv (hgc.mono (Icc_subset_Icc hu.1 hv.2))
  -- the stops
  have hu₀I : u₀ ∈ Icc l r := ⟨hlu₀.le, hu₀r.le⟩
  obtain ⟨r₁, hq₁a, hq₁b⟩ := exists_rat_btwn_nnreal hu₀r
  set q₁ := (r₁ : ℝ).toNNReal with hq₁
  have hq₁I : q₁ ∈ Icc l r := ⟨hlu₀.le.trans hq₁a.le, hq₁b.le⟩
  set t := g u₀ with ht
  have htq : t < g q₁ := hmono hu₀I hq₁I hq₁a
  obtain ⟨r₂, hq₂a, hq₂b⟩ := exists_rat_btwn_nnreal htq
  set q₂ := (r₂ : ℝ).toNNReal with hq₂
  obtain ⟨w, hwI, hgw⟩ := hivt hu₀I hq₁I hq₁a.le ⟨hq₂a.le, hq₂b.le⟩
  have hwu₀ : u₀ < w := lt_of_le_of_ne hwI.1 fun h => by rw [← h] at hgw; exact absurd hgw (ne_of_lt hq₂a)
  have hwq₁ : w < q₁ := lt_of_le_of_ne hwI.2 fun h => by rw [h] at hgw; exact absurd hgw (ne_of_gt hq₂b)
  have hwI' : w ∈ Icc l r := ⟨hu₀I.1.trans hwu₀.le, hwq₁.le.trans hq₁I.2⟩
  have hq₂c : q₂ ≤ c := hq₂b.le.trans (hg q₁ hq₁I).1.2
  have hq₁ζ : (q₁ : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hq₁I.2).trans hrζ
  have hq₂ζ : (q₂ : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hq₂c).trans hcζ
  have hβt : β t = α u₀ := (hg u₀ hu₀I).2
  have hβq₂ : β q₂ ∈ H := hgw ▸ hgH w hwI'
  -- the times of `β` in `(t, q₂]` are on the arc `α([u₀, w])`
  have harc : ∀ v, t ≤ v → v ≤ q₂ → ∃ u ∈ Icc u₀ w, β v = α u := fun v h1 h2 => by
    obtain ⟨u, hu, hgu⟩ := hivt hu₀I hwI' hwu₀.le ⟨h1, hgw ▸ h2⟩
    exact ⟨u, hu, by rw [← hgu]; exact (hg u ⟨hu₀I.1.trans hu.1, hu.2.trans hwI'.2⟩).2⟩
  -- the physical clearance
  have hclear : ∃ ρ > 0, α '' Icc 0 q₁ ∩ ball (α u₀) ρ = β '' Icc 0 q₂ ∩ ball (α u₀) ρ := by
    have hlI : l ∈ Icc l r := ⟨le_rfl, hlr⟩
    set S₁ := α '' (Icc 0 q₁ \ Ioo l w) with hS₁
    set S₂ := β '' (Icc 0 q₂ \ Ioo (g l) q₂) with hS₂
    have hS₁c : IsCompact S₁ :=
      (isCompact_Icc.diff isOpen_Ioo).image_of_continuousOn
        ((IsPathGood.continuousOn_Icc hp₁ hq₁ζ).mono sdiff_subset)
    have hS₂c : IsCompact S₂ :=
      (isCompact_Icc.diff isOpen_Ioo).image_of_continuousOn
        ((IsPathGood.continuousOn_Icc hp₂ hq₂ζ).mono sdiff_subset)
    have hpS₁ : α u₀ ∉ S₁ := by
      rintro ⟨u, hu, hue⟩
      have := IsPathGood.injOn_Icc hp₁ hq₁ζ hu.1 ⟨zero_le, hq₁a.le⟩ hue
      exact hu.2 (this ▸ ⟨hlu₀, hwu₀⟩)
    have hpS₂ : α u₀ ∉ S₂ := by
      rintro ⟨v, hv, hve⟩
      rw [← hβt] at hve
      have := IsPathGood.injOn_Icc hp₂ hq₂ζ hv.1 ⟨zero_le, hq₂a.le⟩ hve
      exact hv.2 (this ▸ ⟨hmono hlI hu₀I hlu₀, hq₂a⟩)
    obtain ⟨d₁, hd₁, hd₁S⟩ := exists_ball_notMem hS₁c hpS₁
    obtain ⟨d₂, hd₂, hd₂S⟩ := exists_ball_notMem hS₂c hpS₂
    refine ⟨min d₁ d₂, lt_min hd₁ hd₂, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hzb⟩
      have huI : u ∈ Ioo l w := by
        by_contra hno
        exact hd₁S _ ⟨u, ⟨hu, hno⟩, rfl⟩ (ball_subset_ball (min_le_left _ _) hzb)
      have huI' : u ∈ Icc l r := ⟨huI.1.le, huI.2.le.trans hwI'.2⟩
      refine ⟨⟨g u, ⟨zero_le, ?_⟩, (hg u huI').2⟩, hzb⟩
      rw [← hgw]
      exact (hmono huI' hwI' huI.2).le
    · rintro ⟨⟨v, hv, rfl⟩, hzb⟩
      have hvI : v ∈ Ioo (g l) q₂ := by
        by_contra hno
        exact hd₂S _ ⟨v, ⟨hv, hno⟩, rfl⟩ (ball_subset_ball (min_le_right _ _) hzb)
      obtain ⟨u, hu, hgu⟩ := hivt hlI hwI' (hlu₀.le.trans hwu₀.le) ⟨hvI.1.le, hgw ▸ hv.2⟩
      refine ⟨⟨u, ⟨zero_le, hu.2.trans hwq₁.le⟩, ?_⟩, hzb⟩
      rw [← hgu]
      exact ((hg u ⟨hu.1, hu.2.trans hwI'.2⟩).2).symm
  -- the interiorized completions
  obtain ⟨α'', β'', hα'', hβ'', hord'', hrα, hrβ, -⟩ :=
    Supp7.exists_interiorized_completions (IsProperCompletion.mono hα' (hq₁I.2.trans hra))
      (IsProperCompletion.mono hβ' hq₂c) (by rw [hα0]; simp) hord'
  have hpc₁'' := isProperCurve_of_isProperCompletion hα''
  have hpc₂'' := isProperCurve_of_isProperCompletion hβ''
  have hα''0 : α'' 0 = x₁ := by rw [hα''.2.2.2.2 0 zero_le, hα0]
  have hβ''0 : β'' 0 = x₂ := by rw [hβ''.2.2.2.2 0 zero_le, hβ0]
  have hco'' : ∀ {s s' t t' : ℝ≥0}, α'' s = β'' t → α'' s' = β'' t' → s < s' → t < t' := fun hst hst' hss' =>
    contact_order hpc₁'' hpc₂'' (by rw [hα''0]; simp) (by rw [hβ''0]; simp) (by rw [hα''0, hβ''0]; simpa using hx)
      hord'' hst hst' hss'
  have hu₀q₁ : u₀ ≤ q₁ := hq₁a.le
  have hcon₀ : α'' u₀ = β'' t := by
    rw [hα''.2.2.2.2 u₀ hu₀q₁, hβ''.2.2.2.2 t hq₂a.le, hβt]
  have hαH : ∀ u, u₀ ≤ u → u ≤ q₁ → α u ∈ H := fun u h1 h2 =>
    (hIcc u ⟨hlu₀.le.trans h1, h2.trans hq₁I.2⟩).1
  refine ⟨r₁, r₂, l, u₀, t, hq₁I.2.trans hra, hq₂c, hlu₀, hq₁a, hq₂a, hβt, ?_, hβq₂, hclear, α'', β'', hpc₁'',
    hpc₂'', fun u hu => hα''.2.2.2.2 u hu, fun v hv => hβ''.2.2.2.2 v hv, hord'', ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (hIcc u ⟨hu.1, hu.2.trans hq₁I.2⟩).1
  · -- the tail of the first completion
    intro u hu
    by_contra hnot
    have him := im_eq_zero_of_not_mem_H (hpc₁''.2.2.1 u) hnot
    rcases hrα u him with ⟨v, hv, hve⟩ | ⟨v, hv, hve⟩
    · rw [← hα''.2.2.2.2 v hv] at hve
      have := hpc₁''.2.1 hve
      exact absurd (this ▸ (mem_Iic.1 hv)) (not_le.2 hu)
    · have hcon : α'' u = β'' v := by rw [← hve, hβ''.2.2.2.2 v hv]
      have htv : t < v := hco'' hcon₀ hcon (hu₀q₁.trans_lt hu)
      obtain ⟨u', hu', hβu'⟩ := harc v htv.le hv
      have hH : β v ∈ H := hβu' ▸ hαH u' hu'.1 (hu'.2.trans hwq₁.le)
      rw [hve] at hH
      exact not_mem_H_of_im_eq_zero him hH
  · -- the tail of the second completion
    intro v hv
    by_contra hnot
    have him := im_eq_zero_of_not_mem_H (hpc₂''.2.2.1 v) hnot
    rcases hrβ v him with ⟨u, hu, hue⟩ | ⟨v', hv', hve⟩
    · have hcon : α'' u = β'' v := by rw [hα''.2.2.2.2 u hu, hue]
      rcases lt_trichotomy u u₀ with hlt | heq | hgt
      · have := hco'' hcon hcon₀ hlt
        exact absurd (this.trans hq₂a) (not_lt.2 hv.le)
      · rw [heq] at hue
        rw [← hue] at him
        exact not_mem_H_of_im_eq_zero him hu₀H
      · rw [← hue] at him
        exact not_mem_H_of_im_eq_zero him (hαH u hgt.le hu)
    · rw [← hβ''.2.2.2.2 v' hv'] at hve
      have := hpc₂''.2.1 hve
      exact absurd (this ▸ (mem_Iic.1 hv')) (not_le.2 hv)

end Select

/-! ### The chart geometry of a cooriented common arc -/

section Chart

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **The right side of the right-hand completion lies in the right side of the left-hand one** (proof of Lemma W0b:
"its right collar avoids the other path"; the source's normalized right domains `C₁ ⊆ C₂`). -/
theorem rightSide_subset_rightSide {α'' β'' : ℝ≥0 → ℂ} (hc₁ : IsProperCurve α'') (hc₂ : IsProperCurve β'')
    (hα0 : α'' 0 = x₁) (hβ0 : β'' 0 = x₂) (hx : x₂ ≤ x₁) (hord : range β'' ⊆ closedLeftSide α'') :
    rightSide α'' ⊆ rightSide β'' := by
  have h0₁ : (α'' 0).im = 0 := by rw [hα0]; simp
  have h0₂ : (β'' 0).im = 0 := by rw [hβ0]; simp
  have hnotβ : ∀ w ∈ rightSide α'', w ∉ range β'' := fun w hw hwβ => by
    rcases hord hwβ with hL | hS
    · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hc₁ h0₁) hL hw
    · exact connectedComponentIn_subset _ _ hw hS
  have hsubc : rightSide α'' ⊆ (seedRayClosure β'')ᶜ := by
    intro w hw hwS
    rcases hwS with hwβ | ⟨hre, him⟩
    · exact hnotβ w hw hwβ
    · rw [hβ0, ofReal_re] at hre
      rw [h0₂] at him
      rcases eq_or_lt_of_le him with him0 | hneg
      · refine hnotβ w hw ⟨0, ?_⟩
        rw [hβ0]
        exact Complex.ext (by simp [hre]) (by simp [him0])
      · rcases hx.lt_or_eq with hlt | heq
        · have hL : w ∈ leftSide α'' :=
            lowerLeft_subset_leftSide hc₁.2.2.1 h0₁ ⟨by rw [hα0, ofReal_re, hre]; exact hlt, hneg⟩
          exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hc₁ h0₁) hL hw
        · refine connectedComponentIn_subset _ _ hw (Or.inr ⟨?_, ?_⟩)
          · rw [hα0, ofReal_re, hre, heq]
          · rw [h0₁]; exact hneg.le
  have href : rightRef α'' ∈ rightSide α'' := rightRef_mem_rightSide hc₁.2.2.1 h0₁
  have href₂ : rightRef α'' ∈ rightSide β'' := by
    refine lowerRight_subset_rightSide hc₂.2.2.1 h0₂ ⟨?_, ?_⟩
    · simp only [rightRef, hα0, hβ0, sub_re, add_re, ofReal_re, one_re, I_re, sub_zero]; linarith
    · simp [rightRef, h0₁]
  have := isPreconnected_connectedComponentIn.subset_connectedComponentIn href hsubc
  unfold rightSide at href₂ ⊢
  rw [connectedComponentIn_eq href₂]
  exact this

/-- **The chart geometry of a cooriented common arc** (proof of Lemma W0b, p. 529): with the stops of
`exists_coorientedStops`, the common point `α(s) = β(t)` is approached from the joint unbounded domain (from the right
side of the right-hand completion) along a nontrivial filter on which both centred charts tend to **positive** reals
and the two canonical derivative-argument lifts differ by a quantity tending to `0` (Aux. lemma 57). -/
theorem coorientedArcChart (hx : x₂ ≤ x₁) {W₁ W₂ : ℝ≥0 → ℝ}
    (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁)) (hW₁c : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁})
    (hW₁0 : W₁ 0 = 0) (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂))
    (hW₂c : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂}) (hW₂0 : W₂ 0 = 0)
    (hi₁ : InjOn α {t | (t : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    {a c : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ₁) (hc : (c : ℝ≥0∞) < ζ₂)
    (hord : HasOrderedProperCompletions α a β c) (hcom : HasCommonOpenSubarc α a β c) :
    ∃ (r₁ r₂ : ℚ) (s t : ℝ≥0), (r₁ : ℝ).toNNReal ≤ a ∧ (r₂ : ℝ).toNNReal ≤ c ∧ s < (r₁ : ℝ).toNNReal ∧
      t < (r₂ : ℝ).toNNReal ∧ β t = α s ∧ α s ∈ H ∧
      (∃ ρ > 0, α '' Icc 0 (r₁ : ℝ).toNNReal ∩ ball (α s) ρ = β '' Icc 0 (r₂ : ℝ).toNNReal ∩ ball (α s) ρ) ∧
      ∃ F : Filter ℂ, F.NeBot ∧
        F ≤ 𝓝[H \ fillH (α '' Icc 0 (r₁ : ℝ).toNNReal ∪ β '' Icc 0 (r₂ : ℝ).toNNReal)] (α s) ∧
        ∃ y₁ y₂ : ℝ, 0 < y₁ ∧ 0 < y₂ ∧
        Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₁ r.toNNReal) (r₁ : ℝ).toNNReal (z - x₁)) F
          (𝓝 (y₁ : ℂ)) ∧
        Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₂ r.toNNReal) (r₂ : ℝ).toNNReal (z - x₂)) F
          (𝓝 (y₂ : ℂ)) ∧
        Tendsto (fun z => (QuantumZipper.logDerivFwd (fun r : ℝ => W₁ r.toNNReal) (r₁ : ℝ).toNNReal (z - x₁)).im -
          (QuantumZipper.logDerivFwd (fun r : ℝ => W₂ r.toNNReal) (r₂ : ℝ).toNNReal (z - x₂)).im) F (𝓝 0) := by
  have hp₁ : IsPathGood α ζ₁ x₁ := ⟨hi₁, W₁, hW₁c, hW₁0, hg₁⟩
  have hp₂ : IsPathGood β ζ₂ x₂ := ⟨hi₂, W₂, hW₂c, hW₂0, hg₂⟩
  obtain ⟨r₁, r₂, l, s, t, hq₁a, hq₂c, hls, hsq₁, htq₂, hβt, hαlH, hβq₂H, ⟨ρ, hρ, hagree⟩, α'', β'', hc₁, hc₂,
    hag₁, hag₂, hord'', htail₁, htail₂⟩ := exists_coorientedStops hp₁ hp₂ hx ha hc hord hcom
  set q₁ := (r₁ : ℝ).toNNReal with hq₁
  set q₂ := (r₂ : ℝ).toNNReal with hq₂
  set A := α '' Icc 0 q₁ with hAdef
  set B := β '' Icc 0 q₂ with hBdef
  have hq₁ζ : (q₁ : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.2 hq₁a).trans_lt ha
  have hq₂ζ : (q₂ : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.2 hq₂c).trans_lt hc
  have hsζ : (s : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hsq₁.le).trans hq₁ζ.le
  have hsH : α s ∈ H := hαlH ⟨s, ⟨hls.le, hsq₁.le⟩, rfl⟩
  have hq₁H : α q₁ ∈ H := hαlH ⟨q₁, ⟨(hls.trans hsq₁).le, le_rfl⟩, rfl⟩
  have hα0 : α'' 0 = x₁ := by rw [hag₁ 0 zero_le, IsPathGood.zero hp₁]
  have hβ0 : β'' 0 = x₂ := by rw [hag₂ 0 zero_le, IsPathGood.zero hp₂]
  have h0₁ : (α'' 0).im = 0 := by rw [hα0]; simp
  have h0₂ : (β'' 0).im = 0 := by rw [hβ0]; simp
  set R := rightSide α'' with hR
  set D₁ := H \ fillH A with hD₁
  have hRα : ∀ w ∈ R, ∀ u, w ≠ α'' u := fun w hw u hwu =>
    connectedComponentIn_subset _ _ hw (Or.inl ⟨u, hwu.symm⟩)
  -- the common point is adherent to `R ∩ D₁`
  obtain ⟨ε, hε, hball⟩ := IsPathGood.isFreeAt_of_lt hp₁ hls hsζ
  have hcl : α s ∈ closure (R ∩ D₁) := by
    have hpR : α s ∈ closure R :=
      seedRayClosure_subset_closure_rightSide hc₁ h0₁ (Or.inl ⟨s, hag₁ s hsq₁.le⟩)
    rw [Metric.mem_closure_iff] at hpR ⊢
    intro δ hδ
    have hpos : (0 : ℝ) < (α s).im := hsH
    obtain ⟨z, hzR, hzd⟩ := hpR (min δ (min ε (α s).im)) (lt_min hδ (lt_min hε hpos))
    have hzH : z ∈ H := by
      have h1 : |(α s).im - z.im| ≤ dist (α s) z := by
        rw [dist_eq_norm, ← sub_im]; exact abs_im_le_norm _
      have h2 := (abs_le.1 (h1.trans (hzd.le.trans ((min_le_right _ _).trans (min_le_right _ _))))).2
      show 0 < z.im
      by_contra hneg
      have h3 := lt_of_lt_of_le hzd ((min_le_right _ _).trans (min_le_right _ _))
      have h4 : (α s).im ≤ dist (α s) z := by
        have := (abs_le.1 h1).1
        have h5 := abs_sub_abs_le_abs_sub (α s).im z.im
        linarith [not_lt.1 hneg, le_abs_self ((α s).im - z.im)]
      linarith
    have hzb : z ∈ ball (α s) ε := by
      rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hzd ((min_le_right _ _).trans (min_le_left _ _))
    have hzA : z ∉ α '' Icc 0 q₁ := by
      rintro ⟨u, hu, rfl⟩
      exact hRα _ hzR u (hag₁ u hu.2).symm
    have hzD : z ∈ D₁ := Sec7.IsPathGood.mem_H_diff_fillH_of_slit hp₁ (hls.trans hsq₁) hq₁ζ.le hαlH
      (hball ⟨hzb, hzH⟩) hzA
    exact ⟨z, ⟨hzR, hzD⟩, lt_of_lt_of_le hzd (min_le_left _ _)⟩
  have hneb : (𝓝[R ∩ D₁] (α s)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  set U := Ultrafilter.of (𝓝[R ∩ D₁] (α s)) with hUdef
  have hU : (U : Filter ℂ) ≤ 𝓝[R ∩ D₁] (α s) := Ultrafilter.of_le _
  -- the first chart
  obtain ⟨y₁, hy₁, hf₁⟩ := exists_pos_tendsto_of_rightSide_phys hg₁ hW₁c hW₁0 hi₁ hq₁ζ hq₁H hc₁ h0₁ hag₁ htail₁
    hsq₁ hsH U hU
  -- the joint unbounded domain
  have hAc : IsCompact A := IsPathGood.isCompact_image hp₁ hq₁ζ.le
  have hBc : IsCompact B := IsPathGood.isCompact_image hp₂ hq₂ζ.le
  have hABc : IsCompact (A ∪ B) := hAc.union hBc
  have hq₁0 : 0 < q₁ := lt_of_le_of_lt zero_le hsq₁
  have hq₂0 : 0 < q₂ := lt_of_le_of_lt zero_le htq₂
  have hRD : R ∩ D₁ ⊆ H \ fillH (A ∪ B) := by
    refine subset_H_diff_fillH_of_rightSide_phys hg₁ hW₁c hW₁0 hi₁ hq₁ζ hq₁0 hq₁H hc₁ h0₁ hag₁ htail₁
      hABc.isClosed ?_
    rintro w (hwA | ⟨v, hv, rfl⟩) hwR hwD
    · exact hwD.2 ⟨hwD.1, Or.inl (subset_closure hwA)⟩
    · have hβv : β v = β'' v := (hag₂ v hv.2).symm
      rcases hord'' ⟨v, hβv.symm⟩ with hL | hS
      · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hc₁ h0₁) (hβv ▸ hL) hwR
      · exact connectedComponentIn_subset _ _ hwR (hβv ▸ hS)
  have hUD : (U : Filter ℂ) ≤ 𝓝[H \ fillH (A ∪ B)] (α s) := hU.trans (nhdsWithin_mono _ hRD)
  -- the second chart
  have hRR := rightSide_subset_rightSide hc₁ hc₂ hα0 hβ0 hx hord''
  have hU₂ : (U : Filter ℂ) ≤ 𝓝[rightSide β'' ∩ (H \ fillH B)] (β t) := by
    rw [hβt]
    refine hU.trans (nhdsWithin_mono _ fun z hz => ⟨hRR hz.1, ?_⟩)
    exact sdiff_subset_sdiff_right (fillH_mono subset_union_right) (hRD hz)
  obtain ⟨y₂, hy₂, hf₂⟩ := exists_pos_tendsto_of_rightSide_phys hg₂ hW₂c hW₂0 hi₂ hq₂ζ hβq₂H hc₂ h0₂ hag₂ htail₂
    htq₂ (hβt ▸ hsH) U hU₂
  -- the joint hull and its lift
  have hKΓ : IsHPHull (fillH (A ∪ B)) := by
    refine isHPHull_fillH_of_isPreconnected hABc.isBounded ?_
    have hApc : IsPreconnected A := isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hp₁ hq₁ζ.le)
    have hBpc : IsPreconnected B := isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hp₂ hq₂ζ.le)
    have hlow : IsPreconnected {z : ℂ | z.im ≤ 0} := isPreconnected_lowerHalf
    have hx₁ : (x₁ : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₁⟩
    have hx₂ : (x₂ : ℂ) ∈ B := ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₂⟩
    have h1 := hApc.union (x₁ : ℂ) hx₁ (show (x₁ : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp) hlow
    have h2 := h1.union (x₂ : ℂ) (Or.inr (show (x₂ : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)) hx₂ hBpc
    rwa [union_right_comm] at h2
  set gK := ConformalImage.mapOut (fillH (A ∪ B)) with hgKdef
  have hgK : IsMapOut (fillH (A ∪ B)) gK := ConformalImage.isMapOut_mapOut hKΓ
  obtain ⟨LK, hLK⟩ := exists_isCanonicalDerivLog hKΓ hgK
  have hF : (U : Filter ℂ) ≤ 𝓟 (H \ fillH (A ∪ B)) := hUD.trans inf_le_right
  have hlift : ∀ {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0} {y : ℝ},
      IsGeneratingTrace W ζ (fun t => γ t - x) → ContinuousOn W {s | (s : ℝ≥0∞) < ζ} → W 0 = 0 →
      InjOn γ {t | (t : ℝ≥0∞) ≤ ζ} → (q : ℝ≥0∞) < ζ → 0 < q → γ '' Icc 0 q ⊆ A ∪ B →
      (A ∪ B) ∩ ball (α s) ρ ⊆ γ '' Icc 0 q →
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ)) →
      Tendsto (fun z => (LK z).im - (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) U
        (𝓝 0) := by
    intro γ ζ x W q y hg hWc hW0 hi hq hq0 hsub hloc hfy
    obtain ⟨κ, hK, hgm, hL⟩ := exists_physChart hg hWc hW0 hq
    obtain ⟨Φ, hΦc, hΦH, -, hinv, hmaps⟩ := exists_physInv hg hWc hW0 hi hq hq0
    obtain ⟨ε', hε', hno⟩ := exists_ball_notMem_of_approach hABc.isClosed hsub hmaps hΦc hΦH hinv hρ hloc U hUD hfy
    have hd : Disjoint (ball (((y + κ : ℝ)) : ℂ) ε')
        ((fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) '' (fillH (A ∪ B) \
          fillH (γ '' Icc 0 q))) := by
      rw [Set.disjoint_left]
      rintro w hwb ⟨z, ⟨hzK, hzA⟩, rfl⟩
      refine hno z ⟨hzK.1, hzA⟩ hzK ?_
      rw [mem_ball, dist_eq_norm] at hwb ⊢
      convert hwb using 2
      push_cast; ring
    have hq' : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) U
        (𝓝[H] (((y + κ : ℝ)) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := hfy.add_const (κ : ℂ)
        convert this using 2
        push_cast; ring
      · filter_upwards [hF (mem_principal_self _)] with z hz
        exact hgm.1.2.mapsTo ⟨hz.1, fun h => hz.2 (fillH_mono hsub h)⟩
    exact tendsto_im_sub_of_le hK hKΓ (fillH_mono hsub) hgm hgK hL hLK hF hε' hd hq'
  have hloc₁ : (A ∪ B) ∩ ball (α s) ρ ⊆ A := by
    rintro z ⟨hz | hz, hzb⟩
    · exact hz
    · have : z ∈ B ∩ ball (α s) ρ := ⟨hz, hzb⟩
      rw [← hagree] at this
      exact this.1
  have hloc₂ : (A ∪ B) ∩ ball (α s) ρ ⊆ B := by
    rintro z ⟨hz | hz, hzb⟩
    · have : z ∈ A ∩ ball (α s) ρ := ⟨hz, hzb⟩
      rw [hagree] at this
      exact this.1
    · exact hz
  have hl₁ := hlift hg₁ hW₁c hW₁0 hi₁ hq₁ζ hq₁0 subset_union_left hloc₁ hf₁
  have hl₂ := hlift hg₂ hW₂c hW₂0 hi₂ hq₂ζ hq₂0 subset_union_right hloc₂ hf₂
  refine ⟨r₁, r₂, s, t, hq₁a, hq₂c, hsq₁, htq₂, hβt, hsH, ⟨ρ, hρ, hagree⟩, U, inferInstance, hUD, y₁, y₂, hy₁, hy₂,
    hf₁, hf₂, ?_⟩
  have := hl₂.sub hl₁
  rw [sub_zero] at this
  refine this.congr fun z => ?_
  ring

end Chart

end W0b

end Supp9

end InteractingSLE
