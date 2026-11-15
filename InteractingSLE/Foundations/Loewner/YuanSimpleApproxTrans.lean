import InteractingSLE.Foundations.Loewner.YuanCorollary13

/-!
# Simple approximations of Loewner traces, I: the transition maps between charts

Input to [Yua22, Theorem 1.1, (i) ⇒ (iii)] (Y. Yuan, *Topological characterisations of Loewner
traces*, `source/external/Yua22/arxiv-latex/TraceTopology.tex` §4, L467–L583).

Let `η` be a continuous Loewner trace of the continuous driver `W` (`W 0 = 0`). For `0 ≤ a ≤ b`
the **transition map** `trMap W a b = F̄_{a,b}` is the boundary extension of the centred inverse
map `F^{(a)}_{b-a}` of the chain driven by `W(a + ·) − W(a)`: it maps the chart of time `b` to
the chart of time `a`. By [Yua22] Corollary 1.3 (`IsLoewnerTrace.isLoewnerTrace_shift`) the
shifted chain has a continuous trace `γ_a = loewnerTip (shiftDrive W a)`, so `F̄_{a,b}` is
continuous on `ℍ̄`.

## Main results

* `trMap_continuousOn`, `trMap_mapsTo_Hbar`, `trMap_mem_H`, `trMap_injOn`,
  `trMap_differentiableOn`: `F̄_{a,b}` is continuous on `ℍ̄`, maps `ℍ̄` into `ℍ̄` and `ℍ` into
  `ℍ`, and is holomorphic and injective on `ℍ`;
* `trMap_self`, `trMap_trMap`: `F̄_{a,a} = id` and `F̄_{a,b} ∘ F̄_{b,c} = F̄_{a,c}` on `ℍ̄`;
* `continuousOn_trMap_zero`: the tip `b ↦ F̄_{a,b}(0) = γ_a(b − a)` is continuous;
* `trMap_zero_notMem_image`: the earlier tips `F̄_{a,b'}(0)`, `a ≤ b' ≤ b`, are not in
  `F̄_{a,b}(ℍ)`;
* `IsCutTime`, `exists_isCutTime_mem_Ioo`: times `t` with `η t ∈ ℍ \ η([0, t))` are dense
  ([Yua22] Lemma `countable_dense_times`);
* `IsCutTime.trMap_zero_mem_H`: at a cut time `t > a`, the tip `F̄_{a,t}(0)` is in `ℍ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanSimpleApprox

/-- The **transition map** `F̄_{a,b}` from the chart of time `b` to the chart of time `a`: the
boundary extension of the centred inverse map of the chain driven by `W(a + ·) − W(a)` at time
`b − a`. -/
def trMap (W : ℝ → ℝ) (a b : ℝ) : ℂ → ℂ := extendFrom H (fwdMapInv (shiftDrive W a) (b - a))

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

theorem shiftDrive_zero_eq (hW0 : W 0 = 0) : shiftDrive W 0 = W := by
  funext r
  simp [shiftDrive, hW0]

theorem trMap_zero_left (hW0 : W 0 = 0) (b : ℝ) :
    trMap W 0 b = extendFrom H (fwdMapInv W b) := by
  rw [trMap, shiftDrive_zero_eq hW0, sub_zero]

theorem trMap_zero (W : ℝ → ℝ) (a b : ℝ) :
    trMap W a b 0 = loewnerTip (shiftDrive W a) (b - a) := rfl

theorem trMap_eq_fwdMapInv (hW : Continuous W) {a b : ℝ} (hab : a ≤ b) {w : ℂ} (hw : w ∈ H) :
    trMap W a b w = fwdMapInv (shiftDrive W a) (b - a) w :=
  extendFrom_H_eq (continuousOn_fwdMapInv (QuantumZipper.RS.continuous_shiftDrive hW a)
    (shiftDrive_zero W a) (sub_nonneg.2 hab)) hw

/-- `F̄_{a,a}` is the identity on `ℍ̄`. -/
theorem trMap_self (hW : Continuous W) (a : ℝ) {w : ℂ} (hw : w ∈ Hbar) : trMap W a a w = w := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 := shiftDrive_zero W a
  have h : Tendsto (fwdMapInv (shiftDrive W a) (a - a)) (𝓝[H] w) (𝓝 w) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [sub_self]
    exact (fwdMapInv_zero_time hV hV0 hz).symm
  exact extendFrom_eq (by rw [closure_H]; exact hw) h

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
include hη hW hW0

/-- The shifted chain at `a ≥ 0` has a continuous Loewner trace ([Yua22] Corollary 1.3). -/
theorem isLoewnerTrace_shift' {a : ℝ} (ha : 0 ≤ a) :
    IsLoewnerTrace (shiftDrive W a) (loewnerTip (shiftDrive W a)) :=
  hη.isLoewnerTrace_shift hW hW0 ha

theorem trMap_fiber_hyps {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    DifferentiableOn ℂ (trMap W a b) H ∧ ContinuousOn (trMap W a b) Hbar ∧
      InjOn (trMap W a b) H ∧ ∀ x : ℂ, x.im = 0 → trMap W a b x ∉ trMap W a b '' H :=
  (isLoewnerTrace_shift' hη hW hW0 ha).fiber_hyps (QuantumZipper.RS.continuous_shiftDrive hW a)
    (shiftDrive_zero W a) (sub_nonneg.2 hab)

theorem trMap_continuousOn {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ContinuousOn (trMap W a b) Hbar :=
  (trMap_fiber_hyps hη hW hW0 ha hab).2.1

theorem trMap_differentiableOn {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    DifferentiableOn ℂ (trMap W a b) H :=
  (trMap_fiber_hyps hη hW hW0 ha hab).1

theorem trMap_injOn {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : InjOn (trMap W a b) H :=
  (trMap_fiber_hyps hη hW hW0 ha hab).2.2.1

omit hη hW0 in
theorem trMap_mem_H {a b : ℝ} (hab : a ≤ b) {w : ℂ} (hw : w ∈ H) :
    trMap W a b w ∈ H := by
  rw [trMap_eq_fwdMapInv hW hab hw]
  exact QuantumZipper.RS.fwdMapInv_mem_H (QuantumZipper.RS.continuous_shiftDrive hW a)
    (shiftDrive_zero W a) (sub_nonneg.2 hab) hw

theorem trMap_mapsTo_Hbar {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MapsTo (trMap W a b) Hbar Hbar := by
  intro x hx
  have hc := trMap_continuousOn hη hW hW0 ha hab
  have h1 : Tendsto (trMap W a b) (𝓝[H] x) (𝓝 (trMap W a b x)) :=
    (hc x hx).mono H_subset_Hbar
  have hne : (𝓝[H] x).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]; exact hx
  refine isClosed_Hbar.mem_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact H_subset_Hbar (trMap_mem_H hW hab hw)

/-- **Composition of transition maps**: `F̄_{a,b} ∘ F̄_{b,c} = F̄_{a,c}` on `ℍ̄`. -/
theorem trMap_trMap {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) {w : ℂ}
    (hw : w ∈ Hbar) : trMap W a b (trMap W b c w) = trMap W a c w := by
  have hσ := isLoewnerTrace_shift' hη hW hW0 ha
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 := shiftDrive_zero W a
  obtain ⟨ξ, -, hFξ, hlim⟩ :=
    hσ.exists_tendsto_shift hV hV0 (sub_nonneg.2 hab) (sub_nonneg.2 hbc) hw
  rw [YuanCorollary13.shiftDrive_shiftDrive, add_sub_cancel] at hlim
  have hξ : trMap W b c w = ξ := extendFrom_eq (by rw [closure_H]; exact hw) hlim
  rw [hξ]
  simp only [trMap]
  rw [hFξ, show b - a + (c - b) = c - a by ring]

/-- The tip `b ↦ F̄_{a,b}(0)` is continuous for `b ≥ a`. -/
theorem continuousOn_trMap_zero {a : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun b => trMap W a b 0) (Ici a) := by
  have hσ := isLoewnerTrace_shift' hη hW hW0 ha
  exact hσ.2.1.comp (continuous_id.sub continuous_const).continuousOn
    fun b hb => show (0 : ℝ) ≤ b - a from sub_nonneg.2 hb

theorem trMap_zero_mem_Hbar {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : trMap W a b 0 ∈ Hbar :=
  trMap_mapsTo_Hbar hη hW hW0 ha hab zero_mem_Hbar

omit hη hW0 in
/-- `F̄_{a,b}(ℍ)` avoids the hull of the shifted chain at time `b − a`. -/
theorem trMap_image_subset {a b : ℝ} (hab : a ≤ b) :
    trMap W a b '' H ⊆ H \ fwdHull (shiftDrive W a) (b - a) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [trMap_eq_fwdMapInv hW hab hw]
  exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull (QuantumZipper.RS.continuous_shiftDrive hW a)
    (shiftDrive_zero W a) (sub_nonneg.2 hab) hw

/-- **Earlier tips are not in the image of `ℍ`**: for `a ≤ b' ≤ b`, `F̄_{a,b'}(0) ∉ F̄_{a,b}(ℍ)`
(the tip `γ_a(b' − a)` lies on the trace of the shifted chain, hence in its hull or on `ℝ`). -/
theorem trMap_zero_notMem_image {a b' b : ℝ} (ha : 0 ≤ a) (hab' : a ≤ b') (hb'b : b' ≤ b) :
    trMap W a b' 0 ∉ trMap W a b '' H := by
  intro hmem
  have hsub := trMap_image_subset hW (hab'.trans hb'b) hmem
  have hσ := isLoewnerTrace_shift' hη hW hW0 ha
  rw [hσ.2.2 (b - a) (sub_nonneg.2 (hab'.trans hb'b))] at hsub
  refine hsub.2 ⟨hsub.1, Or.inl (subset_closure ⟨b' - a, ⟨sub_nonneg.2 hab', ?_⟩, rfl⟩)⟩
  linarith

end Trace

/-! ### Cut times -/

/-- A **cut time** of `η`: `η t ∈ ℍ` is visited for the first time at `t`
([Yua22] Lemma `countable_dense_times`: `γ(t) ∉ γ([0, t)) ∪ ℝ`). -/
def IsCutTime (η : ℝ → ℂ) (t : ℝ) : Prop := η t ∈ H ∧ η t ∉ η '' Ico 0 t

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
include hη hW hW0

/-- **Cut times are dense** ([Yua22] Lemma `countable_dense_times`): every interval `(a, b)`,
`0 ≤ a < b`, contains a cut time. Strict growth gives `η u ∈ K_{b'} \ K_a` for some `u`; the
first visit of `η u` is a cut time after `a`. -/
theorem exists_isCutTime_mem_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ t ∈ Ioo a b, IsCutTime η t := by
  set b' := (a + b) / 2 with hb'
  have hab' : a < b' := by rw [hb']; linarith
  have hb'b : b' < b := by rw [hb']; linarith
  obtain ⟨u, hu, hηu⟩ := hη.exists_mem_diff hW hW0 ha hab'
  set p := η u with hp
  have hpH : p ∈ H := hηu.1.1
  set Z : Set ℝ := {v ∈ Icc 0 u | η v = p} with hZ
  have hu0 : 0 ≤ u := ha.trans hu.1.le
  have hZc : IsClosed Z := by
    have : ContinuousOn η (Icc 0 u) := hη.2.1.mono Icc_subset_Ici_self
    exact this.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := ⟨u, ⟨hu0, le_rfl⟩, rfl⟩
  have hZb : BddBelow Z := ⟨0, fun v hv => hv.1.1⟩
  set t := sInf Z with ht
  have htZ : t ∈ Z := hZc.csInf_mem hZne hZb
  have hta : a < t := by
    by_contra hle
    rw [not_lt] at hle
    apply hηu.2
    rw [hη.2.2 a ha]
    refine ⟨hpH, Or.inl (subset_closure ⟨t, ⟨htZ.1.1, hle⟩, ?_⟩)⟩
    exact htZ.2
  refine ⟨t, ⟨hta, lt_of_le_of_lt (htZ.1.2.trans hu.2) hb'b⟩, ?_, ?_⟩
  · rw [htZ.2]; exact hpH
  · rintro ⟨v, hv, hve⟩
    have hvZ : v ∈ Z := ⟨⟨hv.1, (hv.2.le.trans htZ.1.2)⟩, hve.trans htZ.2⟩
    exact absurd (csInf_le hZb hvZ) (not_le.2 hv.2)

/-- At a cut time `t > a ≥ 0` the tip `F̄_{a,t}(0) = γ_a(t − a)` lies in `ℍ`: `η t` is not in the
earlier hull `K_a`, and no real point is mapped by `F̄_a` into `ℍ \ K_a`. -/
theorem IsCutTime.trMap_zero_mem_H {a t : ℝ} (hcut : IsCutTime η t) (ha : 0 ≤ a)
    (hat : a < t) : trMap W a t 0 ∈ H := by
  obtain ⟨hHbar, hF, -⟩ := hη.extendFrom_shift_tip hW hW0 ha (sub_nonneg.2 hat.le)
  rw [add_sub_cancel] at hF
  -- `η t ∉ K_a`
  have ht0 : 0 ≤ t := ha.trans hat.le
  have hnot : η t ∉ fwdHull W a := by
    intro hK
    have hcl : η t ∈ closure (H \ fwdHull W a) := by
      have hlim := hη.tendsto_fwdMapInv_tip hW hW0 ht0
      have hne : (𝓝[H] (0 : ℂ)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]; exact zero_mem_Hbar
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht0 hw
      exact ⟨h1.1, fun h => h1.2 (fwdHull_mono' hat.le h)⟩
    rw [hη.2.2 a ha] at hK hcl
    have h2 := YuanCorollary13.mem_closure_of_mem_fillH_of_mem_closure hK hcl
    rw [(hη.isCompact_image a).isClosed.closure_eq] at h2
    obtain ⟨v, hv, hve⟩ := h2
    exact hcut.2 ⟨v, ⟨hv.1, lt_of_le_of_lt hv.2 hat⟩, hve⟩
  have hmem : η t ∈ H \ fwdHull W a := ⟨hcut.1, hnot⟩
  by_contra hH
  have him : (trMap W a t 0).im = 0 := le_antisymm (not_lt.1 hH) hHbar
  exact hη.extendFrom_not_mem hW hW0 ha him (hF ▸ hmem)

end Trace

end YuanSimpleApprox

end InteractingSLE
