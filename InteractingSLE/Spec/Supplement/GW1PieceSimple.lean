/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9DCuts
import InteractingSLE.Spec.Supplement.GB6Order
import InteractingSLE.Spec.Supplement.GW2aPieceChart

/-!
# Lemma GW1, the next ordinary piece: simple, and meeting the old union only at its seed (deterministic core)

Packet PROVE-T14-GW1Z. Lemma GW1, proof (`source/spec/p577-624.md` L957, p. 619), "The next ordinary piece and the
full old union":

> "Apply GB6, within the independently established complete conditional pair in item 2, to every available
> interior-tip prefix of `β_j`. It lies in `η[0, T_{w_j}]` in reverse first-visit order. Continuity gives the same
> inclusion at a finite endpoint. Each point of the entire old `A_j \ {w_j}` is first visited strictly later than
> `T_{w_j}`, by item 3. Therefore no new raw point can equal one of those old points. The relative seed is visited only
> initially; a second physical fiber of `w_j` would be a visit to the target of this conditional counterflow before
> its terminal time, and is excluded by the same first-visit comparison. The continuous inverse chart is injective
> away from those old boundary fibers. The physical new piece is consequently simple and joins `A_j` only at `w_j`."

This file is the pathwise argument, for one realization, in the launch chart `c` of the piece.

* **Chart coordinates** (`visit_and_injOn_of_firstContact`). Let `α` be the piece's continuous generating trace up to
  its stop `S` and `γ` the continuous trace of the conditional counterflow (in the counterflow chart; its path in the
  flow chart is `η = R̂ ∘ γ`, `R̂(z) = −1/z` on the sphere). If at every dyadic own time `s < S` with an interior
  tip the counterflow first meets `α([0, s])` at `α(s)` (GB6's first-contact assertion), then every point `α(t)`,
  `t > 0`, is visited by `η` at a finite time (so it is `−1/γ(r)` with `γ(r) ≠ 0`), and `α` is injective on
  `[0, S]`. Injectivity: if `α(t) = α(t')`, `t < t'`, the first-contact times force `α` to be constant on
  `[t, t']`, and the hulls of a generating trace grow strictly (`hcap(K_t) = 2t`).
* **Physical coordinates** (`piece_simple_of_firstContact`, `piece_simple_of_visit`). If moreover every tip of the
  counterflow read through `c` and the inversion lies outside a set `A` (GW1's items 2–3: the conditional
  counterflow is the original one before its first visit to the old union `A`), and the boundary-limit map `f` of
  `c⁻¹` is injective at points whose image is not in `A` ("the continuous inverse chart is injective away from those
  old boundary fibers"), then `f ∘ α` is injective on `[0, S]` and `f(α(t)) ∉ A` for `t > 0`.
* `piece_simple_of_visit` is the same conclusion from the visits and the chart injectivity directly (the form used
  after the measurable transfer, `GW1PieceSimpleMeas`); `exists_param_of_injOn`, `exists_param_of_visit`: the piece's
  physical points are then the image of a continuous injective parametrization starting at the piece's tip at time
  `0`, outside `A` after time `0`, proper for an infinite stop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE

namespace Theorem14

namespace GW1Z

open Supp8.GB6 (IsFirstContactAtTip sphereInv)

/-! ### The hulls of a generating trace grow strictly -/

section Growth

open HalfPlaneSep Supp9B Sec2.Assembly

/-- **A generating trace adds new points on every interval before its horizon** (the hulls grow strictly,
`hcap(K_t) = 2t`): if `x < m < T`, then `η([x, m]) ⊄ η([0, x])`. -/
theorem image_Icc_not_subset {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {x m : ℝ≥0} (hxm : x < m) (hm : (m : ℝ≥0∞) < T) : ¬ η '' Icc x m ⊆ η '' Icc 0 x := by
  intro hsub
  have hx : (x : ℝ≥0∞) < T := lt_trans (ENNReal.coe_lt_coe.2 hxm) hm
  have hcont : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → IsCompact (η '' Icc 0 s) := fun s hs =>
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht =>
      (ENNReal.coe_le_coe.2 ht.2).trans hs.le)
  have hAeq : η '' Icc 0 x = η '' Icc 0 m := by
    refine Subset.antisymm (image_mono (Icc_subset_Icc le_rfl hxm.le)) ?_
    rintro _ ⟨t, ht, rfl⟩
    rcases le_total t x with htx | hxt
    · exact ⟨t, ⟨ht.1, htx⟩, rfl⟩
    · exact hsub ⟨t, ⟨hxt, ht.2⟩, rfl⟩
  have hF1 := (isFilling_iff_inter_H_eq_fillH (hcont x hx).isBounded (hcont x hx).isClosed).1 (hη.2.2 x hx)
  have hF2 := (isFilling_iff_inter_H_eq_fillH (hcont m hm).isBounded (hcont m hm).isClosed).1 (hη.2.2 m hm)
  rw [inter_eq_left.2 (fun _ hz => hz.1)] at hF1 hF2
  obtain ⟨t₂, hmt₂, ht₂T⟩ := exists_real_btwn_of_lt hm
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg m).trans hmt₂.le
  have hW₂c : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂T
  have hW₂0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, (fun s : ℝ => w s.toNNReal) r = frozenDrive w t₂ r := fun r hr =>
    (frozenDrive_eq hr).symm
  have hxt₂ : (x : ℝ) < t₂ := lt_trans (by exact_mod_cast hxm) hmt₂
  rw [fwdHull_eq_of_eqOn (NNReal.coe_nonneg x) hxt₂ heq] at hF1
  rw [fwdHull_eq_of_eqOn (NNReal.coe_nonneg m) hmt₂ heq] at hF2
  exact fwdHull_ne_of_lt hW₂c hW₂0 (NNReal.coe_nonneg x) (by exact_mod_cast hxm)
    (hF1.trans ((congrArg fillH hAeq).trans hF2.symm))

end Growth

/-- **Dyadic interior times are dense below the stop**: between `x < y ≤ S` there is a dyadic time `s` with an
interior tip (`α(s) ∈ ℍ`) and `s < S`. -/
theorem exists_dyad_mem_H_of_le {w : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w S α)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < S}) (hw0 : w 0 = 0) {x y : ℝ≥0} (hxy : x < y)
    (hy : (y : ℝ≥0∞) ≤ S) : ∃ s ∈ Supp9D.dyadSet, x < s ∧ s < y ∧ (s : ℝ≥0∞) < S ∧ α s ∈ H := by
  obtain ⟨m, hxm, hmy⟩ := exists_between hxy
  have hm : (m : ℝ≥0∞) < S := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hmy) hy
  obtain ⟨r, hr, hxr, hrm, hrH⟩ := Supp9D.exists_dyad_mem_H hα.2.1
    (fun a b hab hb => Supp9D.exists_mem_H_of_isGeneratingTrace hα hw hw0 hab hb) hxm hm
  exact ⟨r, hr, hxr, hrm.trans hmy, lt_trans (ENNReal.coe_lt_coe.2 hrm) hm, hrH⟩

/-! ### Visits from first contacts at a dense set of times -/

section Visit

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [TopologicalSpace X] [T2Space X] in
/-- The first-contact time at `v` is unique. -/
theorem firstContact_time_eq {η α : ℝ≥0 → X} {v T T' : ℝ≥0} (hT : η T = α v) (hTf : ∀ u < T, η u ∉ α '' Icc 0 v)
    (hT' : η T' = α v) (hT'f : ∀ u < T', η u ∉ α '' Icc 0 v) : T = T' :=
  le_antisymm (IsFirstContactAtTip.le_of_mem hTf le_rfl hT') (IsFirstContactAtTip.le_of_mem hT'f le_rfl hT)

/-- **A visit at a limit time** (GB6, final assertion: "Continuity gives the same inclusion at a finite endpoint").
Let the first-contact assertion hold on a set `D` of own times that is dense in `(s₀, t)`, and let `η` be continuous
and `α` continuous from the left at `t`. Then `η` visits `α(t)` at a time `L` that is at most the first-contact time of
every `v ∈ D ∩ (s₀, t)`. -/
theorem exists_visit_of_firstContact {η α : ℝ≥0 → X} {D : Set ℝ≥0} (hη : Continuous η)
    (hD : ∀ s ∈ D, IsFirstContactAtTip η α s) {s₀ t : ℝ≥0} (hs₀t : s₀ < t)
    (hdense : ∀ a : ℝ≥0, s₀ ≤ a → a < t → ∃ s ∈ D, a < s ∧ s < t)
    (hα : Tendsto α (𝓝[<] t) (𝓝 (α t))) :
    ∃ L : ℝ≥0, η L = α t ∧ ∀ v ∈ D, s₀ < v → v < t → ∀ T : ℝ≥0, η T = α v →
      (∀ u < T, η u ∉ α '' Icc 0 v) → L ≤ T := by
  choose T hTη hTfirst using hD
  set A : Set ℝ≥0 := D ∩ Ioo s₀ t with hA
  have hAne : A.Nonempty := by
    obtain ⟨v, hv, h1, h2⟩ := hdense s₀ le_rfl hs₀t
    exact ⟨v, hv, h1, h2⟩
  have hmono : ∀ u (hu : u ∈ D) v (hv : v ∈ D), u ≤ v → T v hv ≤ T u hu := fun u hu v hv huv =>
    IsFirstContactAtTip.le_of_mem (hTfirst v hv) huv (hTη u hu)
  set Tinf : ℝ≥0 := ⨅ u : A, T u.1 u.2.1 with hTinf
  have hbdd : BddBelow (range fun u : A => T u.1 u.2.1) := ⟨0, fun _ _ => zero_le⟩
  have : Nonempty A := hAne.to_subtype
  have hseq : ∀ n : ℕ, ∃ v ∈ A, t - 1 / ((n : ℝ≥0) + 1) < v := by
    intro n
    have ht0 : 0 < t := lt_of_le_of_lt zero_le hs₀t
    have ha : max s₀ (t - 1 / ((n : ℝ≥0) + 1)) < t :=
      max_lt hs₀t (tsub_lt_self ht0 (by positivity))
    obtain ⟨v, hv, h1, h2⟩ := hdense _ (le_max_left _ _) ha
    exact ⟨v, ⟨hv, lt_of_le_of_lt (le_max_left _ _) h1, h2⟩, lt_of_le_of_lt (le_max_right _ _) h1⟩
  choose u hu hu_gt using hseq
  have hu_tend : Tendsto u atTop (𝓝 t) := by
    have hlow : Tendsto (fun n : ℕ => t - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
        _root_.tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := t)).sub h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hu_gt n).le) (fun n => (hu n).2.2.le)
  have hu_tend' : Tendsto u atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hu_tend, Eventually.of_forall fun n => (hu n).2.2⟩
  have hTle : ∀ n, Tinf ≤ T (u n) (hu n).1 := fun n => ciInf_le hbdd ⟨u n, hu n⟩
  have hTinf_tend : Tendsto (fun n => T (u n) (hu n).1) atTop (𝓝 Tinf) := by
    rw [tendsto_order]
    refine ⟨fun x hx => Eventually.of_forall fun n => lt_of_lt_of_le hx (hTle n), fun x hx => ?_⟩
    obtain ⟨⟨v, hvA⟩, hvx⟩ := exists_lt_of_ciInf_lt (show Tinf < x from hx)
    have hv_lt : v < t := hvA.2.2
    have hev : ∀ᶠ n in atTop, v ≤ u n := (hu_tend.eventually (Ioi_mem_nhds hv_lt)).mono fun n hn => hn.le
    exact hev.mono fun n hn => lt_of_le_of_lt (hmono v hvA.1 (u n) (hu n).1 hn) hvx
  have hvisit : η Tinf = α t := by
    have h1 : Tendsto (fun n => η (T (u n) (hu n).1)) atTop (𝓝 (η Tinf)) :=
      (hη.tendsto Tinf).comp hTinf_tend
    have h2 : Tendsto (fun n => η (T (u n) (hu n).1)) atTop (𝓝 (α t)) := by
      have e : (fun n => η (T (u n) (hu n).1)) = fun n => α (u n) := funext fun n => hTη (u n) (hu n).1
      rw [e]
      exact hα.comp hu_tend'
    exact tendsto_nhds_unique h1 h2
  refine ⟨Tinf, hvisit, fun v hv hs₀v hvt T' hT'η hT'first => ?_⟩
  rw [← firstContact_time_eq (hTη v hv) (hTfirst v hv) hT'η hT'first]
  exact ciInf_le hbdd ⟨v, hv, hs₀v, hvt⟩

end Visit

/-! ### Chart coordinates: visits and injectivity from GB6's first contacts -/

theorem sphereInv_eq_coe {z w : ℂ} (h : sphereInv (z : OnePoint ℂ) = (w : OnePoint ℂ)) : z ≠ 0 ∧ w = -z⁻¹ := by
  rw [Supp8.GB6.sphereInv_coe] at h
  split_ifs at h with hz
  · exact absurd h.symm (OnePoint.coe_ne_infty w)
  · exact ⟨hz, (OnePoint.coe_injective h).symm⟩

/-- **GB6's final assertion up to a finite stop, with injectivity** (chart coordinates). Let `α` be a continuous
generating trace of a driver continuous on `[0, S]`, and `γ` a continuous path (the counterflow trace in its own
chart). If at every dyadic own time `s < S` with an interior tip, `η = R̂ ∘ γ` first meets `α([0, s])` at `α(s)`, then
every `α(t)`, `0 < t ≤ S`, is a finite point `−1/γ(r)` of the counterflow, and `α` is injective on `[0, S]`. -/
theorem visit_and_injOn_of_firstContact {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (hfc : ∀ s ∈ Supp9D.dyadSet, (s : ℝ≥0∞) < S → α s ∈ H →
      IsFirstContactAtTip (fun t => sphereInv (γ t : OnePoint ℂ)) (fun t => (α t : OnePoint ℂ)) s) :
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∃ r, γ r ≠ 0 ∧ α t = -(γ r)⁻¹) ∧
      InjOn α {t | (t : ℝ≥0∞) ≤ S} := by
  set η : ℝ≥0 → OnePoint ℂ := fun t => sphereInv (γ t : OnePoint ℂ) with hηdef
  set α' : ℝ≥0 → OnePoint ℂ := fun t => (α t : OnePoint ℂ) with hα'def
  set D : Set ℝ≥0 := {s | s ∈ Supp9D.dyadSet ∧ (s : ℝ≥0∞) < S ∧ α s ∈ H} with hDdef
  have hηc : Continuous η := Supp8.GB6.continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγ)
  have hDfc : ∀ s ∈ D, IsFirstContactAtTip η α' s := fun s hs => hfc s hs.1 hs.2.1 hs.2.2
  have hWlt : ContinuousOn W {s | (s : ℝ≥0∞) < S} :=
    hW.mono fun s (hs : (s : ℝ≥0∞) < S) => (le_of_lt hs : (s : ℝ≥0∞) ≤ S)
  have hdense : ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) ≤ S → ∃ s ∈ D, x < s ∧ s < y := by
    intro x y hxy hy
    obtain ⟨s, hs, h1, h2, h3, h4⟩ := exists_dyad_mem_H_of_le hα hWlt hW0 hxy hy
    exact ⟨s, ⟨hs, h3, h4⟩, h1, h2⟩
  have hleft : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → Tendsto α' (𝓝[<] t) (𝓝 (α' t)) := by
    intro t ht
    have h1 : ContinuousWithinAt α {s | (s : ℝ≥0∞) ≤ S} t := hα.2.1 t ht
    have h2 : Tendsto α (𝓝[<] t) (𝓝 (α t)) :=
      h1.mono fun s (hs : s < t) => (le_trans (ENNReal.coe_le_coe.2 hs.le) ht : (s : ℝ≥0∞) ≤ S)
    exact (OnePoint.continuous_coe.tendsto _).comp h2
  have hvisit : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∃ r, γ r ≠ 0 ∧ α t = -(γ r)⁻¹ := by
    intro t ht0 ht
    obtain ⟨s₀, -, -, hs₀t⟩ := hdense 0 t ht0 ht
    obtain ⟨L, hL, -⟩ := exists_visit_of_firstContact hηc hDfc hs₀t
      (fun a _ hat => hdense a t hat ht) (hleft t ht)
    obtain ⟨hne, heq⟩ := sphereInv_eq_coe hL
    exact ⟨L, hne, heq⟩
  -- a repeated value forces `α` to be constant at the dense times in between
  have hconst : ∀ t t' : ℝ≥0, t < t' → (t' : ℝ≥0∞) ≤ S → α t = α t' →
      ∀ v ∈ D, t < v → v < t' → α v = α t := by
    intro t t' _ ht' heq v hv htv hvt'
    obtain ⟨L, hL, hLle⟩ := exists_visit_of_firstContact hηc hDfc hvt'
      (fun a _ hat => hdense a t' hat ht') (hleft t' ht')
    obtain ⟨v', hv', hvv', hv't'⟩ := hdense v t' hvt' ht'
    obtain ⟨T', hT'η, hT'f⟩ := hDfc v' hv'
    obtain ⟨Tv, hTvη, hTvf⟩ := hDfc v hv
    have hLt : η L = α' t := hL.trans (congrArg (fun z : ℂ => (z : OnePoint ℂ)) heq.symm)
    have h1 : L ≤ T' := hLle v' hv' hvv' hv't' T' hT'η hT'f
    have h2 : T' ≤ Tv := IsFirstContactAtTip.le_of_mem hT'f hvv'.le hTvη
    have h3 : Tv ≤ L := IsFirstContactAtTip.le_of_mem hTvf htv.le hLt
    have hLT : L = Tv := le_antisymm (h1.trans h2) h3
    have : α' v = α' t := by rw [← hTvη, ← hLT, hLt]
    exact OnePoint.coe_injective this
  refine ⟨hvisit, ?_⟩
  have hne0 : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → α t ≠ α 0 := by
    intro t ht0 ht h
    obtain ⟨r, hr, hrt⟩ := hvisit t ht0 ht
    rw [hα.1, hrt] at h
    exact neg_ne_zero.2 (inv_ne_zero hr) h
  have hlt : ∀ t t' : ℝ≥0, t < t' → (t' : ℝ≥0∞) ≤ S → α t ≠ α t' := by
    intro t t' htt' ht' heq
    rcases eq_zero_or_pos t with h0 | ht0
    · subst h0
      exact hne0 t' htt' ht' heq.symm
    · have hall : ∀ u ∈ Ioo t t', α u = α t := by
        intro u hu
        have hu' : (u : ℝ≥0∞) < S := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hu.2) ht'
        have hseq : ∀ n : ℕ, ∃ v ∈ D, u < v ∧ v < min t' (u + 1 / ((n : ℝ≥0) + 1)) := fun n =>
          hdense u _ (lt_min hu.2 (lt_add_of_pos_right u (by positivity)))
            (le_trans (ENNReal.coe_le_coe.2 (min_le_left _ _)) ht')
        choose v hv huv hvlt using hseq
        have hv_tend : Tendsto v atTop (𝓝 u) := by
          have hup : Tendsto (fun n : ℕ => u + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 u) := by
            have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
              _root_.tendsto_one_div_add_atTop_nhds_zero_nat
            simpa using (tendsto_const_nhds (x := u)).add h0
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (huv n).le)
            fun n => ((hvlt n).trans_le (min_le_right _ _)).le
        have hcu : ContinuousAt α u :=
          hα.2.1.continuousAt (mem_of_superset ((Supp9.isOpen_setOf_coe_lt S).mem_nhds hu')
            fun s (hs : (s : ℝ≥0∞) < S) => (le_of_lt hs : (s : ℝ≥0∞) ≤ S))
        have hlim : Tendsto (fun n => α (v n)) atTop (𝓝 (α u)) := hcu.tendsto.comp hv_tend
        have hval : ∀ n, α (v n) = α t := fun n =>
          hconst t t' htt' ht' heq (v n) (hv n) (hu.1.trans (huv n)) ((hvlt n).trans_le (min_le_left _ _))
        exact (tendsto_nhds_unique tendsto_const_nhds (hlim.congr hval)).symm
      obtain ⟨m, htm, hmt'⟩ := exists_between htt'
      have hm : (m : ℝ≥0∞) < S := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hmt') ht'
      refine image_Icc_not_subset hα hWlt hW0 htm hm ?_
      rintro _ ⟨u, hu, rfl⟩
      rcases eq_or_lt_of_le hu.1 with h | h
      · exact ⟨u, ⟨zero_le, h.ge⟩, rfl⟩
      · exact ⟨t, ⟨zero_le, le_rfl⟩, (hall u ⟨h, hu.2.trans_lt hmt'⟩).symm⟩
  intro t ht t' ht' h
  rcases lt_trichotomy t t' with hlt' | heq | hgt
  · exact absurd h (hlt t t' hlt' ht')
  · exact heq
  · exact absurd h.symm (hlt t' t hgt ht)

/-! ### Physical coordinates: the piece is simple and avoids the old union after its seed -/

/-- **GW1's next ordinary piece, pathwise, from visits** (p. 619: "no new raw point can equal one of those old points
… The physical new piece is consequently simple and joins `A_j` only at `w_j`"). In a chart `c` whose inverse has the
boundary-limit map `f`, let `α` be the piece (a continuous generating trace up to its stop `S`), injective on `[0, S]`,
each of whose points `α(t)`, `t > 0`, is a point `−1/γ(r)` of the conditional counterflow (`γ` a continuous
generating trace of its driver `Wk`). If every tip of `Wk` read through `c` and the inversion lies outside `A`, and `f`
is injective at points with image outside `A`, then `f ∘ α` is injective on `[0, S]` and `f(α(t)) ∉ A` for
`0 < t ≤ S`. -/
theorem piece_simple_of_visit {c : Chart} {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {A : Set ℂ}
    (hfib : ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ A → x = y)
    {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    {Wk : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace Wk ⊤ γ) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hvis : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∃ r, γ r ≠ 0 ∧ α t = -(γ r)⁻¹)
    (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ S})
    (hclock : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z → z ∉ A) :
    InjOn (f ∘ α) {t | (t : ℝ≥0∞) ≤ S} ∧ ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → f (α t) ∉ A := by
  have hWlt : ContinuousOn W {s | (s : ℝ≥0∞) < S} :=
    hW.mono fun s (hs : (s : ℝ≥0∞) < S) => (le_of_lt hs : (s : ℝ≥0∞) ≤ S)
  have hHbar : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 ht
  have havoid : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → f (α t) ∉ A := by
    intro t ht0 ht
    obtain ⟨r, hr, hrt⟩ := hvis t ht0 ht
    rw [hrt]
    exact hclock r _ (GW2aPiece.tipAt_trans_of_ne_zero hf hγ hWk hWk0 hr)
  have key : ∀ t t' : ℝ≥0, (t : ℝ≥0∞) ≤ S → (t' : ℝ≥0∞) ≤ S → 0 < t' → f (α t) = f (α t') → t = t' := by
    intro t t' ht ht' ht'0 h
    refine hinj ht ht' (hfib _ (hHbar t ht) _ (hHbar t' ht') h ?_)
    rw [h]
    exact havoid t' ht'0 ht'
  refine ⟨fun t ht t' ht' h => ?_, havoid⟩
  rcases eq_zero_or_pos t' with h0 | h0
  · rcases eq_zero_or_pos t with h1 | h1
    · rw [h0, h1]
    · exact (key t' t ht' ht h1 h.symm).symm
  · exact key t t' ht ht' h0 h

/-- **A simple piece as a parametrized curve.** If the physical piece `f ∘ α` (`f` the boundary-limit map of `c⁻¹`,
moving points by at most `C`; `α` a continuous generating trace up to `S`, transient when `S = ∞`) is injective on
`[0, S]` and avoids `A` after time `0`, then the physical points of the piece (`Chart.tipSet` of its stopped driver)
are the image of `[0, S]` under a continuous injective map `g` which starts at the piece's tip at time `0`, avoids `A`
after time `0`, and is proper when `S = ∞`. -/
theorem exists_param_of_injOn {c : Chart} {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    {A : Set ℂ} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    (htr : S = ⊤ → Tendsto (fun t => ‖α t‖) atTop atTop)
    (hinj' : InjOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ S})
    (havoid : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → f (α t) ∉ A) :
    ∃ g : ℝ≥0 → ℂ, ContinuousOn g {t | (t : ℝ≥0∞) ≤ S} ∧ InjOn g {t | (t : ℝ≥0∞) ≤ S} ∧
      g '' {t | (t : ℝ≥0∞) ≤ S} = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ∧
      c.tipAt (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) 0 (g 0) ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → g t ∉ A) ∧
      (S = ⊤ → Tendsto (fun t => ‖g t‖) atTop atTop) := by
  have hWlt : ContinuousOn W {s | (s : ℝ≥0∞) < S} :=
    hW.mono fun s (hs : (s : ℝ≥0∞) < S) => (le_of_lt hs : (s : ℝ≥0∞) ≤ S)
  have hHbar : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 ht
  have hfc' : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  refine ⟨f ∘ α, hfc'.comp hα.2.1 fun t ht => hHbar t ht, hinj', ?_, ?_, havoid, fun hS => ?_⟩
  · rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hW hW0 fun t ht => hf _ (hHbar t ht), image_comp]
  · have hreg : GW1P.PieceRegular W S := ⟨hW0, hW, α, hα, htr⟩
    obtain ⟨hU, hU0⟩ := hreg.continuous_stoppedReal
    have h0H : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
    have hlim : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[H] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h1 : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝 0) (𝓝 ((0 : ℝ) * Complex.I)) :=
          ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
        simpa using h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        show 0 < ((y : ℂ) * Complex.I).im
        simpa using hy
    have h2 := (hf 0 h0H).comp hlim
    rw [Function.comp_apply, hα.1]
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * Complex.I ∈ H := show 0 < ((y : ℂ) * Complex.I).im by simpa using hy
    simp only [Function.comp_apply]
    rw [NNReal.coe_zero, InteractingSLE.fwdMapInv_zero_time hU hU0 hyH]
  · have h1 : Tendsto (fun t => ‖α t‖ + -C) atTop atTop := tendsto_atTop_add_const_right _ (-C) (htr hS)
    refine tendsto_atTop_mono (fun t => ?_) h1
    have h2 := hC (α t) (hHbar t (by rw [hS]; exact le_top))
    have h3 := norm_sub_norm_le (α t) (f (α t))
    rw [norm_sub_rev] at h3
    simp only [Function.comp_apply]
    linarith

/-- **The piece as a parametrized curve, from visits** (`exists_param_of_injOn` with
`piece_simple_of_visit`). -/
theorem exists_param_of_visit {c : Chart} {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    {A : Set ℂ} (hfib : ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ A → x = y)
    {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    (htr : S = ⊤ → Tendsto (fun t => ‖α t‖) atTop atTop)
    {Wk : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace Wk ⊤ γ) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hvis : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∃ r, γ r ≠ 0 ∧ α t = -(γ r)⁻¹)
    (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ S})
    (hclock : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z → z ∉ A) :
    ∃ g : ℝ≥0 → ℂ, ContinuousOn g {t | (t : ℝ≥0∞) ≤ S} ∧ InjOn g {t | (t : ℝ≥0∞) ≤ S} ∧
      g '' {t | (t : ℝ≥0∞) ≤ S} = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ∧
      c.tipAt (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) 0 (g 0) ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → g t ∉ A) ∧
      (S = ⊤ → Tendsto (fun t => ‖g t‖) atTop atTop) := by
  obtain ⟨hinj', havoid⟩ := piece_simple_of_visit hf hfib hα hW hW0 hγ hWk hWk0 hvis hinj hclock
  exact exists_param_of_injOn hf hC hα hW hW0 htr hinj' havoid

/-- **GW1's next ordinary piece, pathwise, from GB6's first contacts** (`piece_simple_of_visit` with the visits and
the injectivity of `visit_and_injOn_of_firstContact`). -/
theorem piece_simple_of_firstContact {c : Chart} {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {A : Set ℂ}
    (hfib : ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ A → x = y)
    {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    {Wk : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace Wk ⊤ γ) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hfc : ∀ s ∈ Supp9D.dyadSet, (s : ℝ≥0∞) < S → α s ∈ H →
      IsFirstContactAtTip (fun t => sphereInv (γ t : OnePoint ℂ)) (fun t => (α t : OnePoint ℂ)) s)
    (hclock : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z → z ∉ A) :
    InjOn (f ∘ α) {t | (t : ℝ≥0∞) ≤ S} ∧ ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → f (α t) ∉ A := by
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  obtain ⟨hvis, hinj⟩ := visit_and_injOn_of_firstContact hα hW hW0 hγc hfc
  exact piece_simple_of_visit hf hfib hα hW hW0 hγ hWk hWk0 hvis hinj hclock

end GW1Z

end Theorem14

end InteractingSLE
