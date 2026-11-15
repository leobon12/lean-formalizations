/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7ClockGeom

/-!
# The chart path of a retained continuation, through its terminal point

Packet PROVE-G7B. Lemma G7 (`source/spec/p481-528.md`, pp. 497–498): "its relative image is a continuous simple
Loewner trace through this stop, including its continuous terminal endpoint".

Setting (`IsRetCont`): a good path `η` (`IsPathGood`), its prefix `η([0, a])`, a compact set `O` (the other retained
prefix), `K = O ∪ η([0, a])`, `D = ℍ \ fill K`, the tip `η(a)` interior, off `O` and adherent to `D`, and a chart
`(φ, ψ)` of `D` (`IsDomChart`) sending the tip to `0`, with forward limits and unique preimages at the points of
`closure D` off `K`.

* `contSet η ζ a K`: the continuation times `a ≤ t ≤ ζ` with no point of `K` strictly between `a` and `t` (the
  continuation up to and including its first new contact with `K`, exactly the time set of `IsRetainedClock`);
  `contStop` its supremum; `contSet = [a, contStop]` (`contSet_eq`).
* `contPath D φ η a V`: the chart path in continuation time, `V = contStop − a`: the forward chart limit at
  `η(a + r)` for `r < V`, and its left limit at `V` (the terminal point, possibly a two-sided point of `K`).
* `IsRetCont.contPath_spec`: `0 < V`; the chart path is continuous, starts at `0`, lies in `ℍ̄`, and
  `ψ ∘ Γ = η(a + ·)` on `[0, V]`. Before `V` it is the unique preimage (confinement and regularity); at a finite `V`
  the left limit exists by the cluster-set lemma (`exists_tendsto_left_of_tendsto_comp`: `ψ` is not constant on any
  real interval).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### The continuation interval -/

/-- **The continuation interval up to and including the first new contact with `K`**. -/
def contSet (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) : Set ℝ≥0 :=
  {t | a ≤ t ∧ (t : ℝ≥0∞) ≤ ζ ∧ ∀ t' : ℝ≥0, a < t' → t' < t → η t' ∉ K}

/-- The end of the continuation: the first new contact time, or the lifetime. -/
def contStop (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) : ℝ≥0∞ :=
  ⨆ t ∈ contSet η ζ a K, (t : ℝ≥0∞)

section ContSet

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {K : Set ℂ}

theorem contStop_le : contStop η ζ a K ≤ ζ := iSup₂_le fun _ ht => ht.2.1

theorem self_mem_contSet (ha : (a : ℝ≥0∞) ≤ ζ) : a ∈ contSet η ζ a K :=
  ⟨le_rfl, ha, fun _ h1 h2 => absurd (h1.trans h2) (lt_irrefl a)⟩

theorem le_contStop {t : ℝ≥0} (ht : t ∈ contSet η ζ a K) : (t : ℝ≥0∞) ≤ contStop η ζ a K :=
  le_iSup₂ (f := fun t (_ : t ∈ contSet η ζ a K) => (t : ℝ≥0∞)) t ht

/-- Before the end of the continuation, the path is off `K`. -/
theorem notMem_of_lt_contStop {t : ℝ≥0} (hat : a < t) (ht : (t : ℝ≥0∞) < contStop η ζ a K) : η t ∉ K := by
  obtain ⟨s, hs, hts⟩ := lt_biSup_iff.1 ht
  exact hs.2.2 t hat (ENNReal.coe_lt_coe.1 hts)

theorem mem_contSet_of_le {t : ℝ≥0} (hat : a ≤ t) (ht : (t : ℝ≥0∞) ≤ contStop η ζ a K) :
    t ∈ contSet η ζ a K :=
  ⟨hat, ht.trans contStop_le, fun _ h1 h2 =>
    notMem_of_lt_contStop h1 ((ENNReal.coe_lt_coe.2 h2).trans_le ht)⟩

/-- **The continuation interval is `[a, contStop]`.** -/
theorem contSet_eq : contSet η ζ a K = {t | a ≤ t ∧ (t : ℝ≥0∞) ≤ contStop η ζ a K} := by
  ext t
  exact ⟨fun ht => ⟨ht.1, le_contStop ht⟩, fun ht => mem_contSet_of_le ht.1 ht.2⟩

/-- The relative lifetime of the continuation. -/
def contLife (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) : ℝ≥0∞ := contStop η ζ a K - a

theorem coe_add_lt_iff {r : ℝ≥0} {c : ℝ≥0∞} : (r : ℝ≥0∞) < c - a ↔ ((a + r : ℝ≥0) : ℝ≥0∞) < c := by
  rw [ENNReal.coe_add, lt_tsub_iff_left]

theorem coe_add_le_iff {r : ℝ≥0} {c : ℝ≥0∞} (ha : (a : ℝ≥0∞) ≤ c) :
    (r : ℝ≥0∞) ≤ c - a ↔ ((a + r : ℝ≥0) : ℝ≥0∞) ≤ c :=
  coe_le_sub_iff ha

end ContSet

/-! ### The chart path -/

/-- **The chart path of a continuation** in continuation time: the forward chart limit at `η(a + r)` for `r < V`,
and the left limit at `V` afterwards. -/
def contPath (D : Set ℂ) (φ : ℂ → ℂ) (η : ℝ≥0 → ℂ) (a : ℝ≥0) (V : ℝ≥0∞) (r : ℝ≥0) : ℂ :=
  if (r : ℝ≥0∞) < V then limUnder (𝓝[D] (η (a + r))) φ
  else limUnder (𝓝[<] V.toNNReal) fun s => limUnder (𝓝[D] (η (a + s))) φ

theorem contPath_of_lt {D : Set ℂ} {φ : ℂ → ℂ} {η : ℝ≥0 → ℂ} {a : ℝ≥0} {V : ℝ≥0∞} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < V) : contPath D φ η a V r = limUnder (𝓝[D] (η (a + r))) φ := by
  simp only [contPath, hr, ↓reduceIte]

theorem contPath_of_le {D : Set ℂ} {φ : ℂ → ℂ} {η : ℝ≥0 → ℂ} {a : ℝ≥0} {V : ℝ≥0∞} {r : ℝ≥0}
    (hr : V ≤ (r : ℝ≥0∞)) :
    contPath D φ η a V r = limUnder (𝓝[<] V.toNNReal) fun s => limUnder (𝓝[D] (η (a + s))) φ := by
  simp only [contPath, not_lt.2 hr, ↓reduceIte]

theorem neBot_nhdsLT {c : ℝ≥0} (hc : 0 < c) : (𝓝[<] c).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' (show (Iio c).Nonempty from ⟨0, hc⟩)]
  exact Set.mem_Iic.2 le_rfl

/-! ### The hypotheses -/

/-- **A retained continuation with a chart** (Lemma G7's hypotheses, pathwise): `η` a good path, the tip `η(a)`
interior, off the compact set `O` and adherent to `D = ℍ \ fill(O ∪ η([0, a]))`; `O` attached to the real line;
`(φ, ψ)` a hydrodynamic chart of `D` sending the tip to `0` (unique preimage), with forward limits and unique
preimages at the points of `closure D` off `O ∪ η([0, a])`. -/
structure IsRetCont (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (x : ℝ) (a : ℝ≥0) (O : Set ℂ) (φ ψ : ℂ → ℂ) : Prop where
  path : IsPathGood η ζ x
  lt : (a : ℝ≥0∞) < ζ
  compact : IsCompact O
  hull : IsPreconnected (O ∪ {z : ℂ | z.im ≤ 0})
  tipH : η a ∈ H
  tipO : η a ∉ O
  tipCl : η a ∈ closure (H \ fillH (O ∪ η '' Icc 0 a))
  chart : IsDomChart (O ∪ η '' Icc 0 a) φ ψ
  hydro : ∃ x₀ : ℝ, ∀ z, φ z = ConformalImage.mapOut (fillH (O ∪ η '' Icc 0 a)) z - x₀
  tipLim : Tendsto φ (𝓝[H \ fillH (O ∪ η '' Icc 0 a)] (η a)) (𝓝 0)
  tipInv : ψ 0 = η a
  tipUniq : ∀ w ∈ Hbar, ψ w = η a → w = 0
  reg : ∀ z ∈ closure (H \ fillH (O ∪ η '' Icc 0 a)), z ∉ O ∪ η '' Icc 0 a →
    ∃ w ∈ Hbar, Tendsto φ (𝓝[H \ fillH (O ∪ η '' Icc 0 a)] z) (𝓝 w) ∧ ψ w = z ∧
      ∀ w' ∈ Hbar, ψ w' = z → w' = w

namespace IsRetCont

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}
  (hR : IsRetCont η ζ x a O φ ψ)
include hR

theorem isCompact_K : IsCompact (O ∪ η '' Icc 0 a) :=
  hR.compact.union (IsPathGood.isCompact_image_Icc_of_le hR.path hR.lt.le)

theorem isClosed_K : IsClosed (O ∪ η '' Icc 0 a) := hR.isCompact_K.isClosed

/-- The end of the continuation is after `a`. -/
theorem lt_contStop : (a : ℝ≥0∞) < contStop η ζ a (O ∪ η '' Icc 0 a) := by
  have hev := IsPathGood.eventually_mem_of_seed hR.path hR.lt hR.compact.isClosed hR.tipH hR.tipO hR.tipCl
  have hζev : ∀ᶠ t : ℝ≥0 in 𝓝[>] a, (t : ℝ≥0∞) < ζ := by
    have h1 : ∀ᶠ t : ℝ≥0 in 𝓝 a, (t : ℝ≥0∞) < ζ :=
      (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hR.lt
    exact nhdsWithin_le_nhds h1
  obtain ⟨b, hab, hb⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (hev.and hζev)
  obtain ⟨t, hat, htb⟩ := exists_between (show a < b from hab)
  have ht : t ∈ contSet η ζ a (O ∪ η '' Icc 0 a) := by
    refine ⟨hat.le, (hb ⟨hat, htb⟩).2.le, fun t' h1 h2 hK => ?_⟩
    have hD := (hb ⟨h1, h2.trans htb⟩).1
    exact hD.2 (mem_fillH_of_mem_closure hD.1 (subset_closure hK))
  exact (ENNReal.coe_lt_coe.2 hat).trans_le (le_contStop ht)

/-- **Confinement on the continuation interval.** -/
theorem mem_closure_of_mem_contSet {t : ℝ≥0} (ht : t ∈ contSet η ζ a (O ∪ η '' Icc 0 a)) :
    η t ∈ closure (H \ fillH (O ∪ η '' Icc 0 a)) := by
  rcases ht.1.lt_or_eq with hat | rfl
  · exact IsPathGood.mem_closure_of_noContact hR.path hR.lt hR.compact hR.tipH hR.tipO hR.tipCl hat ht.2.1
      ht.2.2
  · exact hR.tipCl

/-- A continuation point in `ℍ` before the end is in `D`. -/
theorem mem_D_of_lt_contStop {t : ℝ≥0} (hat : a < t) (ht : (t : ℝ≥0∞) < contStop η ζ a (O ∪ η '' Icc 0 a))
    (htH : η t ∈ H) : η t ∈ H \ fillH (O ∪ η '' Icc 0 a) :=
  mem_H_diff_fillH_of_mem_closure hR.isClosed_K htH (notMem_of_lt_contStop hat ht)
    (hR.mem_closure_of_mem_contSet (mem_contSet_of_le hat.le ht.le))

/-- **The chart path before the end**: the forward limit with a unique preimage. -/
theorem contPath_spec_lt {r : ℝ≥0} (hr : (r : ℝ≥0∞) < contLife η ζ a (O ∪ η '' Icc 0 a)) :
    let Γ := contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))
    Γ r ∈ Hbar ∧ Tendsto φ (𝓝[H \ fillH (O ∪ η '' Icc 0 a)] (η (a + r))) (𝓝 (Γ r)) ∧ ψ (Γ r) = η (a + r) ∧
      ∀ w' ∈ Hbar, ψ w' = η (a + r) → w' = Γ r := by
  intro Γ
  set K := O ∪ η '' Icc 0 a with hK
  set D := H \ fillH K with hD
  have hΓ : Γ r = limUnder (𝓝[D] (η (a + r))) φ := contPath_of_lt hr
  have hlt : ((a + r : ℝ≥0) : ℝ≥0∞) < contStop η ζ a K := coe_add_lt_iff.1 hr
  have hcl : η (a + r) ∈ closure D :=
    hR.mem_closure_of_mem_contSet (mem_contSet_of_le le_self_add hlt.le)
  have hne : (𝓝[D] (η (a + r))).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  obtain ⟨w, hwH, hwt, hwψ, hwu⟩ : ∃ w ∈ Hbar, Tendsto φ (𝓝[D] (η (a + r))) (𝓝 w) ∧ ψ w = η (a + r) ∧
      ∀ w' ∈ Hbar, ψ w' = η (a + r) → w' = w := by
    rcases (zero_le : (0 : ℝ≥0) ≤ r).lt_or_eq with h0 | h0
    · exact hR.reg _ hcl (notMem_of_lt_contStop (lt_add_of_pos_right a h0) hlt)
    · subst h0
      rw [add_zero]
      exact ⟨0, show (0 : ℝ) ≤ (0 : ℂ).im by simp, hR.tipLim, hR.tipInv, hR.tipUniq⟩
  have hw : Γ r = w := by rw [hΓ]; exact hwt.limUnder_eq
  rw [hw]
  exact ⟨hwH, hwt, hwψ, hwu⟩

theorem pos_contLife : 0 < contLife η ζ a (O ∪ η '' Icc 0 a) := tsub_pos_of_lt hR.lt_contStop

/-- The chart path is continuous before the end. -/
theorem continuousOn_contPath_lt :
    ContinuousOn (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)))
      {r | (r : ℝ≥0∞) < contLife η ζ a (O ∪ η '' Icc 0 a)} := by
  obtain ⟨M, hM⟩ := hR.chart.bdd
  have hρ : ContinuousOn (fun r => η (a + r)) {r | (r : ℝ≥0∞) < contLife η ζ a (O ∪ η '' Icc 0 a)} :=
    hR.path.continuousOn.comp (continuous_const.add continuous_id).continuousOn fun r hr =>
      (coe_add_lt_iff.1 hr).le.trans contStop_le
  exact continuousOn_of_unique_preimage hR.chart.continuousOn_inv hM hρ (fun r hr => (hR.contPath_spec_lt hr).1)
    (fun r hr => (hR.contPath_spec_lt hr).2.2.1) fun r hr w hw hwψ => (hR.contPath_spec_lt hr).2.2.2 w hw hwψ

/-- **The terminal point** (Lemma G7's proof, p. 497): at a finite end of the continuation, the chart path has a
left limit, which lies in `ℍ̄` and over the terminal physical point. -/
theorem contPath_endpoint (hV : contLife η ζ a (O ∪ η '' Icc 0 a) ≠ ⊤) :
    let Γ := contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))
    let c := (contLife η ζ a (O ∪ η '' Icc 0 a)).toNNReal
    Γ c ∈ Hbar ∧ ψ (Γ c) = η (a + c) ∧ Tendsto Γ (𝓝[<] c) (𝓝 (Γ c)) := by
  intro Γ c
  set K := O ∪ η '' Icc 0 a with hK
  set D := H \ fillH K with hD
  set V := contLife η ζ a K with hVdef
  have hc : (c : ℝ≥0∞) = V := ENNReal.coe_toNNReal hV
  have hc0 : 0 < c := ENNReal.toNNReal_pos hR.pos_contLife.ne' hV
  have := neBot_nhdsLT hc0
  set γ₀ : ℝ≥0 → ℂ := fun s => limUnder (𝓝[D] (η (a + s))) φ with hγ₀
  have hΓc : Γ c = limUnder (𝓝[<] c) γ₀ := contPath_of_le hc.symm.le
  have hlt : ∀ s ∈ Ico 0 c, (s : ℝ≥0∞) < V := fun s hs => hc ▸ ENNReal.coe_lt_coe.2 hs.2
  have heq : ∀ s ∈ Ico 0 c, Γ s = γ₀ s := fun s hs => contPath_of_lt (hlt s hs)
  have hcont : ContinuousOn γ₀ (Ico 0 c) :=
    (hR.continuousOn_contPath_lt.mono fun s hs => hlt s hs).congr fun s hs => (heq s hs).symm
  have hcζ : ((a + c : ℝ≥0) : ℝ≥0∞) ≤ ζ := by
    rw [ENNReal.coe_add, hc, hVdef, contLife, add_tsub_cancel_of_le hR.lt_contStop.le]
    exact contStop_le
  obtain ⟨M, hM⟩ := hR.chart.bdd
  obtain ⟨R, hR'⟩ := (IsPathGood.isCompact_image_Icc_of_le hR.path hcζ).isBounded.subset_closedBall 0
  have hH : ∀ s ∈ Ico 0 c, γ₀ s ∈ Hbar := fun s hs => heq s hs ▸ (hR.contPath_spec_lt (hlt s hs)).1
  have hψ : ∀ s ∈ Ico 0 c, ψ (γ₀ s) = η (a + s) := fun s hs => heq s hs ▸ (hR.contPath_spec_lt (hlt s hs)).2.2.1
  have hbd : ∀ s ∈ Ico 0 c, ‖γ₀ s‖ ≤ R + M := by
    intro s hs
    have h1 := IsDomChart.norm_le_of_inv hM (hH s hs)
    have h2 := mem_closedBall_zero_iff.1 (hR' ⟨a + s, ⟨zero_le, add_le_add_right hs.2.le a⟩, rfl⟩)
    rw [hψ s hs] at h1
    linarith
  have hlimψ : Tendsto (fun s => ψ (γ₀ s)) (𝓝[<] c) (𝓝 (η (a + c))) := by
    have h1 : Tendsto (fun s : ℝ≥0 => a + s) (𝓝[<] c) (𝓝[{s | (s : ℝ≥0∞) ≤ ζ}] (a + c)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add continuous_id).tendsto c).mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (ENNReal.coe_le_coe.2 (add_le_add_right (le_of_lt hs) a)).trans hcζ
    refine ((hR.path.continuousOn (a + c) hcζ).tendsto.comp h1).congr' ?_
    filter_upwards [Ico_mem_nhdsLT hc0] with s hs
    exact (hψ s hs).symm
  obtain ⟨ξ, hξH, hψξ, hξ⟩ := exists_tendsto_left_of_tendsto_comp hR.chart.differentiableOn_inv
    hR.chart.continuousOn_inv hR.chart.injOn_inv hR.chart.inv_real_notMem_image hc0 hcont hH hbd hlimψ
  have hΓξ : Γ c = ξ := by rw [hΓc]; exact hξ.limUnder_eq
  refine ⟨hΓξ ▸ hξH, hΓξ ▸ hψξ, ?_⟩
  rw [hΓξ]
  refine hξ.congr' ?_
  filter_upwards [Ico_mem_nhdsLT hc0] with s hs
  exact (heq s hs).symm

/-- **The chart path is continuous** (constant after a finite end). -/
theorem continuous_contPath :
    Continuous (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))) := by
  set V := contLife η ζ a (O ∪ η '' Icc 0 a) with hVdef
  set Γ := contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a V with hΓ
  by_cases hV : V = ⊤
  · have hall : ∀ r : ℝ≥0, (r : ℝ≥0∞) < V := fun r => hV ▸ ENNReal.coe_lt_top
    exact continuousOn_univ.1 (hR.continuousOn_contPath_lt.mono fun r _ => hall r)
  · set c := V.toNNReal with hcdef
    have hc : (c : ℝ≥0∞) = V := ENNReal.coe_toNNReal hV
    obtain ⟨-, -, hlim⟩ := hR.contPath_endpoint hV
    have hconst : ∀ r, c ≤ r → Γ r = Γ c := fun r hr => by
      rw [hΓ, contPath_of_le (hc ▸ ENNReal.coe_le_coe.2 hr), contPath_of_le hc.symm.le]
    refine continuous_iff_continuousAt.2 fun r => ?_
    rcases lt_trichotomy r c with h | rfl | h
    · exact (hR.continuousOn_contPath_lt.mono fun s (hs : s < c) =>
        show (s : ℝ≥0∞) < V from hc ▸ ENNReal.coe_lt_coe.2 hs).continuousAt
        (Iio_mem_nhds h)
    · rw [continuousAt_iff_continuous_left_right]
      refine ⟨?_, continuousWithinAt_const.congr (fun s hs => hconst s hs) (hconst _ le_rfl)⟩
      rw [← Iio_insert, continuousWithinAt_insert_self]
      exact hlim
    · have hev : (fun _ => Γ c) =ᶠ[𝓝 r] Γ := by
        filter_upwards [Ioi_mem_nhds h] with s hs
        exact (hconst s (le_of_lt hs)).symm
      exact continuousAt_const.congr hev

/-- **The chart path on the whole continuation**: in `ℍ̄`, over the continuation. -/
theorem contPath_spec {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ contLife η ζ a (O ∪ η '' Icc 0 a)) :
    contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) r ∈ Hbar ∧
      ψ (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) r) = η (a + r) := by
  rcases hr.lt_or_eq with h | h
  · exact ⟨(hR.contPath_spec_lt h).1, (hR.contPath_spec_lt h).2.2.1⟩
  · have hV : contLife η ζ a (O ∪ η '' Icc 0 a) ≠ ⊤ := h ▸ ENNReal.coe_ne_top
    have hr' : r = (contLife η ζ a (O ∪ η '' Icc 0 a)).toNNReal := by rw [← h, ENNReal.toNNReal_coe]
    obtain ⟨h1, h2, -⟩ := hR.contPath_endpoint hV
    rw [hr']
    exact ⟨h1, h2⟩

theorem contPath_zero :
    contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) 0 = 0 := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contLife η ζ a (O ∪ η '' Icc 0 a) := by
    rw [ENNReal.coe_zero]; exact hR.pos_contLife
  exact ((hR.contPath_spec_lt h0).2.2.2 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp)
    (by rw [add_zero]; exact hR.tipInv)).symm

/-- At an interior continuation point before the end, the chart path is the chart value, in `ℍ`. -/
theorem contPath_mem_H {r : ℝ≥0} (hr0 : 0 < r) (hr : (r : ℝ≥0∞) < contLife η ζ a (O ∪ η '' Icc 0 a))
    (hH : η (a + r) ∈ H) :
    contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) r ∈ H ∧
      contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) r = φ (η (a + r)) := by
  have hD := hR.mem_D_of_lt_contStop (lt_add_of_pos_right a hr0) (coe_add_lt_iff.1 hr) hH
  have hψ := (hR.contPath_spec_lt hr).2.2.1
  have hΓH := hR.chart.mem_H_of_inv_mem (hψ ▸ hD)
  exact ⟨hΓH, by rw [← hψ, hR.chart.fwd_inv _ hΓH]⟩

end IsRetCont

end Supp7

end InteractingSLE
