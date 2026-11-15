import InteractingSLE.Spec.Dimension.TraceBridge
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import Mathlib.MeasureTheory.Function.Floor

/-!
# Corollary LP11, second proof part: Borel reconstruction of the entire trace from the driver

Packet PROVE-LP (specification supplement §6.7, Corollary LP11, "Proof: measurable reconstruction of the entire
trace", `source/spec/p481-528.md` L196–L211, pp. 488–489; graph node `SPEC.id-LP11#borel-trace-from-driver`).

This is "the deterministic measurability step which upgrades a driving graph to a full-path graph". A recorded
driving history is a pair `(T, w)` of a lifetime `T ∈ [0, ∞]` and a real path `w : ℝ≥0 → ℝ` (only its values before
`T` matter), with the product σ-algebra on paths. We construct one map

  `drivingTrace : ℝ≥0∞ × (ℝ≥0 → ℝ) → ℝ≥0∞ × (ℝ≥0 → ℂ)`

which is measurable (`measurable_drivingTrace`) and returns `(T, t ↦ η(t ∧ T))` for **every** continuous generating
trace `η` of the Loewner chain driven by `w` on `[0, T]` (the frozen `IsGeneratingTrace`), whenever `w` is
continuous before `T` with `w 0 = 0` (`drivingTrace_eq`). In particular such a trace is unique
(`IsGeneratingTrace.eq_of_le`).

The source's steps and their Lean form:

* "`z_{q,n} = g_q⁻¹(W_q + i2^{−n})` is a Borel function of `W|_{[0,q]}` … ordinary differential equation dependence
  on the continuous driving function is continuous": QuantumZipper's path-measurable trace selector
  `G1Pkg.traceSel` (a radial limit along positive rationals of the inverse map driven by a measurably regularized
  path, measurable by the Gronwall stability `ReverseFlow.norm_revMap_sub_revMap_le`), applied to the path frozen
  after time `q` (`freezeAt`); this is `traceAt q`.
* "the deterministic Loewner tip identity gives `η(q) = lim_n z_{q,n}`": `IsGeneratingTrace.trace_eq`
  (`Spec/Dimension/TraceBridge.lean`), and the inverse map at time `q` only depends on the driver on `[0, q]`
  (`fwdMapInv_eq_of_eqOn_Icc`, through the time-reversed reverse flow); together `traceAt_eq_of_isGeneratingTrace`.
* "If `0 < T_* < ∞`, choose the Borel dyadic times `q_n(T_*) = max{0, 2^{−n}(⌈2^n T_*⌉ − 1)} < T_*`. They increase to
  `T_*`. Their already reconstructed trace values converge to the finite endpoint": `dyadicBelow`
  (`dyadicBelow_lt`, `tendsto_dyadicBelow`, `measurable_dyadicBelow_eval`) and `endpointTrace`.
* "For `T_* = 0` use the seed. Freeze the path after any finite lifetime": the endpoint value at `T = 0` is the seed
  `0`, and `drivingTrace` returns `η(t ∧ T)`.

The source evaluates the trace only at rational times and then extends continuously; the product σ-algebra on
`ℝ≥0 → ℂ` only needs each coordinate `t ↦ η(t ∧ T)` to be measurable, and the selector `traceAt t` is measurable for
every real `t`, so no extension step is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H fwdMapInv revMap trace)

namespace InteractingSLE

namespace LP

/-! ### Dependence of the inverse map on the driver up to the current time -/

/-- For continuous drivers with `W 0 = W' 0 = 0` that agree on `[0, t]`, the inverse maps at time `t` agree on `ℍ`
(through the time-reversed reverse flow, which only reads the driver on `[0, t]`). -/
theorem fwdMapInv_eq_of_eqOn_Icc {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn W W' (Icc 0 t)) {z : ℂ}
    (hz : z ∈ H) : fwdMapInv W t z = fwdMapInv W' t z := by
  rw [QuantumZipper.UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hz,
    QuantumZipper.UnzipInvariance.fwdMapInv_eq_revMap_timeRev W' hW' hW'0 ht hz]
  refine QuantumZipper.ReverseFlow.revMap_congr_drive z fun r hr => ?_
  have h1 : t - r ∈ Icc (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have h2 : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  simp only [h h1, h h2]

/-- The radial-limit trace at time `t` of two continuous drivers that agree on `[0, t]` (both vanishing at `0`). -/
theorem trace_eq_of_eqOn_Icc {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn W W' (Icc 0 t)) :
    trace W t = trace W' t := by
  unfold QuantumZipper.trace limUnder
  congr 1
  refine Filter.map_congr ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact fwdMapInv_eq_of_eqOn_Icc hW hW' hW0 hW'0 ht h
    (show (0 : ℝ) < ((y : ℂ) * I).im by simpa using hy)

/-! ### Freezing a path and the measurable trace evaluation -/

/-- The path `w` frozen after time `s`: `r ↦ w (r ∧ s)`. -/
def freezeAt (s : ℝ≥0) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun r => w (min r s)

theorem measurable_freezeAt (s : ℝ≥0) : Measurable (freezeAt s) :=
  measurable_pi_iff.2 fun r => measurable_pi_apply (min r s)

theorem freezeAt_congr {s : ℝ≥0} {w w' : ℝ≥0 → ℝ} (h : ∀ r ≤ s, w r = w' r) :
    freezeAt s w = freezeAt s w' :=
  funext fun r => h _ (min_le_right r s)

theorem continuous_freezeAt {s : ℝ≥0} {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic s)) :
    Continuous (freezeAt s w) :=
  hw.comp_continuous (continuous_id.min continuous_const) fun r => min_le_right r s

/-- **The measurable trace evaluation at time `s`.** QuantumZipper's path-measurable radial-limit selector
`G1Pkg.traceSel` (parameter `1`: the driver is the path itself) applied to the path frozen after `s`, read at time
`s`. -/
def traceAt (s : ℝ≥0) (w : ℝ≥0 → ℝ) : ℂ :=
  QuantumZipper.Thm18Asm.G1Pkg.traceSel 1 (freezeAt s w) s

theorem measurable_traceAt (s : ℝ≥0) : Measurable (traceAt s) :=
  (measurable_pi_iff.1 (QuantumZipper.Thm18Asm.G1Pkg.measurable_traceSel 1) (s : ℝ)).comp
    (measurable_freezeAt s)

theorem traceAt_congr {s : ℝ≥0} {w w' : ℝ≥0 → ℝ} (h : ∀ r ≤ s, w r = w' r) :
    traceAt s w = traceAt s w' := by
  unfold traceAt
  rw [freezeAt_congr h]

/-- **The tip identity for the measurable evaluation.** If `w` is continuous on `[0, s₂]` with `s < s₂` and
`w 0 = 0`, then `traceAt s w` is the radial-limit trace `lim_{y ↓ 0} g_s⁻¹(w_s + iy)` of the driver `w`. -/
theorem traceAt_eq_trace {w : ℝ≥0 → ℝ} {s : ℝ≥0} {s₂ : ℝ} (hss₂ : (s : ℝ) < s₂)
    (hw : ContinuousOn w (Iic s₂.toNNReal)) (hw0 : w 0 = 0) :
    traceAt s w = trace (fun r : ℝ => w r.toNNReal) s := by
  have hs₂ : 0 ≤ s₂ := (NNReal.coe_nonneg s).trans hss₂.le
  have hsle : s ≤ s₂.toNNReal := Real.le_toNNReal_iff_coe_le hs₂ |>.2 hss₂.le
  have ha : Continuous (freezeAt s w) := continuous_freezeAt (hw.mono (Iic_subset_Iic.2 hsle))
  have ha0 : freezeAt s w 0 = 0 := by simp [freezeAt, hw0]
  unfold traceAt
  rw [QuantumZipper.Thm18Asm.G1Pkg.traceSel_eq ha ha0 (NNReal.coe_nonneg s)]
  unfold QuantumZipper.Thm18Asm.pathTrace
  simp only [Real.sqrt_one, one_mul]
  have hc1 : Continuous fun r : ℝ => freezeAt s w r.toNNReal := ha.comp continuous_real_toNNReal
  have hc2 : Continuous (frozenDrive w s₂) := continuous_frozenDrive hw
  rw [trace_eq_of_eqOn_Icc hc1 hc2 (by simpa using ha0) (by rw [frozenDrive_zero hs₂, hw0])
    (NNReal.coe_nonneg s) fun r hr => ?_]
  · exact trace_eq_of_eqOn (NNReal.coe_nonneg s) hss₂ fun r hr => frozenDrive_eq hr
  · have hr' : r.toNNReal ≤ s := (Real.toNNReal_le_iff_le_coe).2 hr.2
    show w (min r.toNNReal s) = frozenDrive w s₂ r
    rw [min_eq_left hr', frozenDrive_eq ⟨hr.1, hr.2.trans hss₂.le⟩]

/-- **The tip identity for a generating trace.** For a continuous generating trace `η` of the driver `w` on
`[0, T]` (`w` continuous before `T`, `w 0 = 0`) and every `s < T`, `traceAt s w = η s`. -/
theorem traceAt_eq_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) : traceAt s w = η s := by
  obtain ⟨s₂, hss₂, hs₂T⟩ := exists_real_btwn_of_lt hs
  have hcont : ContinuousOn w (Iic s₂.toNNReal) := hw.mono fun r hr => by
    show (r : ℝ≥0∞) < T
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (show r ≤ s₂.toNNReal from hr)) hs₂T
  rw [traceAt_eq_trace hss₂ hcont hw0, hη.trace_eq hw hw0 hs]

/-! ### The dyadic times below a lifetime -/

/-- The index `⌈2^n x⌉ − 1` of the dyadic time below `x`. -/
def dyadicIdx (n : ℕ) (x : ℝ≥0) : ℕ := ⌈(2 : ℝ≥0) ^ n * x⌉₊ - 1

/-- The dyadic time `q_n(x) = 2^{−n}(⌈2^n x⌉ − 1)` (and `0` when `x = 0`) of LP11's proof (p. 489). -/
def dyadicBelow (n : ℕ) (x : ℝ≥0) : ℝ≥0 := (dyadicIdx n x : ℝ≥0) / 2 ^ n

theorem measurable_dyadicIdx (n : ℕ) : Measurable (dyadicIdx n) :=
  (measurable_from_nat (f := fun k : ℕ => k - 1)).comp
    (Nat.measurable_ceil.comp (measurable_const_mul _))

theorem dyadicBelow_lt {x : ℝ≥0} (hx : 0 < x) (n : ℕ) : dyadicBelow n x < x := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  have hpos : 0 < (2 : ℝ≥0) ^ n * x := mul_pos h2 hx
  have hc : 1 ≤ ⌈(2 : ℝ≥0) ^ n * x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
  have hlt := Nat.ceil_lt_add_one hpos.le
  have hsub : ((⌈(2 : ℝ≥0) ^ n * x⌉₊ - 1 : ℕ) : ℝ≥0) + 1 = ⌈(2 : ℝ≥0) ^ n * x⌉₊ := by
    exact_mod_cast Nat.sub_add_cancel hc
  have key : ((⌈(2 : ℝ≥0) ^ n * x⌉₊ - 1 : ℕ) : ℝ≥0) < 2 ^ n * x := by
    rw [← hsub] at hlt
    exact lt_of_add_lt_add_right hlt
  unfold dyadicBelow dyadicIdx
  rw [div_lt_iff₀ h2, mul_comm x]
  exact key

theorem le_dyadicBelow_add (x : ℝ≥0) (n : ℕ) : x ≤ dyadicBelow n x + 1 / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyadicBelow dyadicIdx
  rw [← add_div, le_div_iff₀ h2]
  have h1 : (2 : ℝ≥0) ^ n * x ≤ ⌈(2 : ℝ≥0) ^ n * x⌉₊ := Nat.le_ceil _
  have h3 : ((⌈(2 : ℝ≥0) ^ n * x⌉₊ : ℕ) : ℝ≥0) ≤ ((⌈(2 : ℝ≥0) ^ n * x⌉₊ - 1 : ℕ) : ℝ≥0) + 1 := by
    exact_mod_cast (le_tsub_add : ⌈(2 : ℝ≥0) ^ n * x⌉₊ ≤ _ - 1 + 1)
  calc x * 2 ^ n = 2 ^ n * x := mul_comm _ _
    _ ≤ _ := h1.trans h3

theorem tendsto_dyadicBelow (x : ℝ≥0) : Tendsto (fun n => dyadicBelow n x) atTop (𝓝 x) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp [dyadicBelow, dyadicIdx]
  replace hx : 0 < x := pos_iff_ne_zero.2 hx
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun n => (dyadicBelow_lt hx n).trans ha⟩
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
    simp only [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [(tendsto_order.1 hlim).2 (x - a) (tsub_pos_of_lt ha)] with n hn
  have := le_dyadicBelow_add x n
  by_contra hcon
  replace hcon := not_lt.1 hcon
  have : x < a + (x - a) := by
    calc x ≤ dyadicBelow n x + 1 / 2 ^ n := this
      _ < a + (x - a) := add_lt_add_of_le_of_lt hcon hn
  rw [add_tsub_cancel_of_le ha.le] at this
  exact lt_irrefl _ this

/-- The trace evaluation at the dyadic time below the lifetime is jointly measurable in the recorded history. -/
theorem measurable_traceAt_dyadicBelow (n : ℕ) :
    Measurable fun p : ℝ≥0∞ × (ℝ≥0 → ℝ) => traceAt (dyadicBelow n p.1.toNNReal) p.2 := by
  set G : (ℝ≥0 → ℝ) × ℕ → ℂ := fun q => traceAt ((q.2 : ℝ≥0) / 2 ^ n) q.1 with hGdef
  have hG : Measurable G := measurable_from_prod_countable_left fun k => by
    show Measurable fun w => traceAt ((k : ℝ≥0) / 2 ^ n) w
    exact measurable_traceAt _
  have hg : Measurable fun p : ℝ≥0∞ × (ℝ≥0 → ℝ) => (p.2, dyadicIdx n p.1.toNNReal) :=
    measurable_snd.prodMk ((measurable_dyadicIdx n).comp (ENNReal.measurable_toNNReal.comp measurable_fst))
  have heq : (fun p : ℝ≥0∞ × (ℝ≥0 → ℝ) => traceAt (dyadicBelow n p.1.toNNReal) p.2) =
      G ∘ fun p : ℝ≥0∞ × (ℝ≥0 → ℝ) => (p.2, dyadicIdx n p.1.toNNReal) := rfl
  rw [heq]
  exact hG.comp hg

/-! ### The reconstruction map -/

/-- The endpoint value read from a recorded history `(T, w)`: the seed `0` if `T = 0`, otherwise the limit of the
trace evaluations at the dyadic times below `T` (junk if `T = ∞` or if the limit does not exist). -/
def endpointTrace (T : ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℂ :=
  if T = 0 then 0 else limUnder atTop fun n => traceAt (dyadicBelow n T.toNNReal) w

/-- **The Borel trace of a recorded driving history** (LP11, p. 489): `(T, w) ↦ (T, t ↦ η(t ∧ T))`, with
`η(t) = traceAt t w` before `T` and the endpoint value `endpointTrace T w` from `T` on. -/
def drivingTrace (p : ℝ≥0∞ × (ℝ≥0 → ℝ)) : ℝ≥0∞ × (ℝ≥0 → ℂ) :=
  (p.1, fun t => if (t : ℝ≥0∞) < p.1 then traceAt t p.2 else endpointTrace p.1 p.2)

theorem measurable_endpointTrace :
    Measurable fun p : ℝ≥0∞ × (ℝ≥0 → ℝ) => endpointTrace p.1 p.2 := by
  unfold endpointTrace
  refine Measurable.ite (measurable_fst (measurableSet_singleton 0)) measurable_const ?_
  exact (StronglyMeasurable.limUnder fun n =>
    (measurable_traceAt_dyadicBelow n).stronglyMeasurable).measurable

/-- **The reconstruction map is measurable** (product σ-algebras on paths). -/
theorem measurable_drivingTrace : Measurable drivingTrace := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun t => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((measurable_traceAt t).comp measurable_snd) measurable_endpointTrace

/-- **LP11, the deterministic reconstruction.** Let `η` be a continuous generating trace of the Loewner chain
driven by `w` on `[0, T]` (`w` continuous before `T`, `w 0 = 0`), and let `w'` be any path that agrees with `w`
before `T` (the recorded driving history only determines the path before its lifetime). Then the reconstruction
of `(T, w')` is `(T, t ↦ η(t ∧ T))`: the trace before `T`, frozen at its endpoint after a finite lifetime. -/
theorem drivingTrace_eq {w w' : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (hww' : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → w' s = w s) :
    drivingTrace (T, w') = (T, fun t : ℝ≥0 => η (min (t : ℝ≥0∞) T).toNNReal) := by
  refine Prod.ext rfl (funext fun t => ?_)
  show (if (t : ℝ≥0∞) < T then traceAt t w' else endpointTrace T w') = η (min (t : ℝ≥0∞) T).toNNReal
  split_ifs with ht
  · rw [min_eq_left ht.le, ENNReal.toNNReal_coe,
      traceAt_congr (w' := w) fun r hr => hww' r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht)]
    exact traceAt_eq_of_isGeneratingTrace hη hw hw0 ht
  · have hTt : T ≤ t := not_lt.1 ht
    rw [min_eq_right hTt]
    have hTtop : T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hTt
    unfold endpointTrace
    split_ifs with hT0
    · rw [hT0, ENNReal.toNNReal_zero, hη.1]
    set x := T.toNNReal with hx
    have hTx : T = (x : ℝ≥0∞) := (ENNReal.coe_toNNReal hTtop).symm
    have hxpos : 0 < x := by
      rw [hx]
      exact ENNReal.toNNReal_pos hT0 hTtop
    have hq : ∀ n, ((dyadicBelow n x : ℝ≥0) : ℝ≥0∞) < T := fun n => by
      rw [hTx]
      exact ENNReal.coe_lt_coe.2 (dyadicBelow_lt hxpos n)
    have hval : ∀ n, traceAt (dyadicBelow n x) w' = η (dyadicBelow n x) := fun n => by
      rw [traceAt_congr (w' := w) fun r hr => hww' r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) (hq n))]
      exact traceAt_eq_of_isGeneratingTrace hη hw hw0 (hq n)
    simp only [hval]
    have hxmem : x ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} := by
      show (x : ℝ≥0∞) ≤ T
      rw [hTx]
    have hlim : Tendsto (fun n => dyadicBelow n x) atTop (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ T}] x) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicBelow x, Eventually.of_forall fun n => (hq n).le⟩
    exact ((hη.2.1 x hxmem).tendsto.comp hlim).limUnder_eq

/-- **Uniqueness of the generating trace.** Two continuous generating traces of the Loewner chain driven by `w`
on `[0, T]` agree on `[0, T]` (`w` continuous before `T`, `w 0 = 0`). -/
theorem _root_.InteractingSLE.IsGeneratingTrace.eq_of_le {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η η' : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hη' : IsGeneratingTrace w T η')
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ T) :
    η t = η' t := by
  have h := (drivingTrace_eq hη hw hw0 fun _ _ => rfl).symm.trans
    (drivingTrace_eq hη' hw hw0 fun _ _ => rfl)
  have := congrFun (Prod.ext_iff.1 h).2 t
  simpa [min_eq_left ht] using this

end LP

end InteractingSLE
