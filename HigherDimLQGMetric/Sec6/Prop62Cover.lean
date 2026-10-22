import HigherDimLQGMetric.Sec6.Prop62Trap
import HigherDimLQGMetric.Sec6.TrapStable

/-!
# [S] Proposition 6.2: Borel trap sets of configurations

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Construction*: "Finite subcover `𝒩_{κ₁}, …, 𝒩_{κ_J}` of
`𝒢`; `N_j := 𝒩_{κ_j}` (Borel …)"; *Proof of (T)*), blueprint Part A §6 (`prop:62`, step (8)).

The trap set `N_j` must be a measurable set of MA3's `Config d` (four `ℝ≥0∞`-valued functions on
`ℝ^d × ℝ^d`, product σ-algebra), while the stability neighbourhoods live in M2b's `C(β)`
(`C(W × W, ℝ)` coordinates, local uniform topology). The bridge (ruling M27):

* `s6bDense d`: a fixed countable dense subset `S` of the outer configuration annulus;
* `s6bNSet hd c C β κ ε`: the configurations whose outer coordinates agree on `S × S` with
  `ofReal ∘ q` for some `q ∈ C(β)` that is `ε`-close (non-strictly) to `κ` on `Ā_{1,3}`. It is the
  preimage under a measurable restriction map of the continuous image of a compact set, hence
  Borel (`s6b_measurableSet_NSet`);
* `s6b_mem_NSet` (for (P)): the configuration of two length metrics whose continuous version lies in
  `C(β)` and is close to `κ` lies in `N`;
* `s6b_eq_of_mem_NSet` (for (T)): conversely, membership gives a `q ∈ C(β)` close to `κ` whose
  `ofReal` coordinates **are** the outer configuration coordinates everywhere (density of `S × S`
  and continuity of the M2b coordinates);
* `s6b_trapProps_of_stable`: (T) from `S6bStable` via S6a's `trapProps_of_stable`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter BoundedContinuousFunction unitInterval
open _root_.Topology
open HigherDimLFPP (Rd)
open scoped ENNReal
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### A countable dense set of the outer annulus -/

theorem s6b_exists_dense (d : ℕ) : ∃ S : Set (configOuter d), S.Countable ∧ Dense S :=
  TopologicalSpace.exists_countable_dense (configOuter d)

/-- A fixed countable dense subset of the outer configuration annulus. -/
def s6bDense (d : ℕ) : Set (configOuter d) := Classical.choose (s6b_exists_dense d)

theorem s6bDense_countable (d : ℕ) : (s6bDense d).Countable :=
  (Classical.choose_spec (s6b_exists_dense d)).1

theorem s6bDense_dense (d : ℕ) : Dense (s6bDense d) :=
  (Classical.choose_spec (s6b_exists_dense d)).2

instance s6bDense_countable_inst (d : ℕ) : Countable (s6bDense d) :=
  (s6bDense_countable d).to_subtype

/-- The two outer coordinates of an MA3 configuration on `S × S`. -/
def s6bRestr (d : ℕ) (κ' : Config d) :
    (s6bDense d × s6bDense d → ℝ≥0∞) × (s6bDense d × s6bDense d → ℝ≥0∞) :=
  (fun p => κ'.1 ((p.1 : configOuter d) : Rd d) ((p.2 : configOuter d) : Rd d),
   fun p => κ'.2.1 ((p.1 : configOuter d) : Rd d) ((p.2 : configOuter d) : Rd d))

/-- The two outer coordinates of an M2b configuration on `S × S`, in `ℝ≥0∞`. -/
def s6bRestrC (d : ℕ) (q : ConfigC d) :
    (s6bDense d × s6bDense d → ℝ≥0∞) × (s6bDense d × s6bDense d → ℝ≥0∞) :=
  (fun p => ENNReal.ofReal (q.1 ((p.1 : configOuter d), (p.2 : configOuter d))),
   fun p => ENNReal.ofReal (q.2.1 ((p.1 : configOuter d), (p.2 : configOuter d))))

theorem s6b_measurable_restr (d : ℕ) : Measurable (s6bRestr d) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.2 fun p => ?_
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)
  · refine measurable_pi_iff.2 fun p => ?_
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_fst.comp measurable_snd))

theorem s6b_continuous_restrC (d : ℕ) : Continuous (s6bRestrC d) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun p => ?_
    exact ENNReal.continuous_ofReal.comp ((continuous_eval_const _).comp continuous_fst)
  · refine continuous_pi fun p => ?_
    exact ENNReal.continuous_ofReal.comp ((continuous_eval_const _).comp
      (continuous_fst.comp continuous_snd))

/-! ### Closeness sets -/

/-- Non-strict `ε`-closeness on `Ā_{1,3}` (outer coordinates). -/
def S6bCloseLe (q κ : ConfigC d) (ε : ℝ) : Prop :=
  ∀ x y : configOuter d, (x : Rd d) ∈ annCl (0 : Rd d) 1 3 → (y : Rd d) ∈ annCl (0 : Rd d) 1 3 →
    |q.1 (x, y) - κ.1 (x, y)| ≤ ε ∧ |q.2.1 (x, y) - κ.2.1 (x, y)| ≤ ε

theorem s6b_isClosed_closeLe (κ : ConfigC d) (ε : ℝ) :
    IsClosed {q : ConfigC d | S6bCloseLe q κ ε} := by
  have h : {q : ConfigC d | S6bCloseLe q κ ε} =
      ⋂ x : configOuter d, ⋂ y : configOuter d, ⋂ (_ : (x : Rd d) ∈ annCl (0 : Rd d) 1 3),
        ⋂ (_ : (y : Rd d) ∈ annCl (0 : Rd d) 1 3),
          ({q : ConfigC d | |q.1 (x, y) - κ.1 (x, y)| ≤ ε} ∩
            {q : ConfigC d | |q.2.1 (x, y) - κ.2.1 (x, y)| ≤ ε}) := by
    ext q
    simp only [S6bCloseLe, mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [h]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => IsClosed.inter ?_ ?_
  · exact isClosed_le (((continuous_eval_const _).comp continuous_fst).sub continuous_const).abs
      continuous_const
  · exact isClosed_le (((continuous_eval_const _).comp
      (continuous_fst.comp continuous_snd)).sub continuous_const).abs continuous_const

theorem S6bClose.closeLe {q κ : ConfigC d} {ε : ℝ} (h : S6bClose q κ ε) : S6bCloseLe q κ ε :=
  fun x y hx hy => ⟨(h x y hx hy).1.le, (h x y hx hy).2.le⟩

theorem S6bCloseLe.close {q κ : ConfigC d} {ε ε' : ℝ} (h : S6bCloseLe q κ ε) (hε : ε < ε') :
    S6bClose q κ ε' :=
  fun x y hx hy => ⟨(h x y hx hy).1.trans_lt hε, (h x y hx hy).2.trans_lt hε⟩

/-- The strict closeness set is a neighbourhood. -/
theorem s6b_close_mem_nhds (κ : ConfigC d) {ε : ℝ} (hε : 0 < ε) :
    {q : ConfigC d | S6bClose q κ ε} ∈ 𝓝 κ := by
  have hK : IsCompact (s6bCore d ×ˢ s6bCore d) := s6bCore_isCompact.prod s6bCore_isCompact
  have h1 := s6b_tendstoUniformlyOn_fst (F := fun q : ConfigC d => q) (q := κ)
    (l := 𝓝 κ) tendsto_id hK
  have h2 := s6b_tendstoUniformlyOn_snd (F := fun q : ConfigC d => q) (q := κ)
    (l := 𝓝 κ) tendsto_id hK
  have e1 := (Metric.tendstoUniformlyOn_iff.1 h1) ε hε
  have e2 := (Metric.tendstoUniformlyOn_iff.1 h2) ε hε
  filter_upwards [e1, e2] with q hq1 hq2
  intro x y hx hy
  have hp : (x, y) ∈ s6bCore d ×ˢ s6bCore d := ⟨hx, hy⟩
  refine ⟨?_, ?_⟩
  · have := hq1 (x, y) hp
    rwa [Real.dist_eq, abs_sub_comm] at this
  · have := hq2 (x, y) hp
    rwa [Real.dist_eq, abs_sub_comm] at this

/-! ### The trap sets -/

/-- The Borel trap set attached to `κ` and `ε`. -/
def s6bNSet (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) (κ : ConfigC d) (ε : ℝ) :
    Set (Config d) :=
  s6bRestr d ⁻¹'
    (s6bRestrC d '' {q : ConfigC d | q ∈ configCompactFamily hd c C β ∧ S6bCloseLe q κ ε})

theorem s6b_measurableSet_NSet (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) (κ : ConfigC d)
    (ε : ℝ) : MeasurableSet (s6bNSet hd c C β κ ε) := by
  have hK : IsCompact {q : ConfigC d | q ∈ configCompactFamily hd c C β ∧ S6bCloseLe q κ ε} :=
    (configCompactFamily_isCompact hd c C β).inter_right (s6b_isClosed_closeLe κ ε)
  exact (s6b_measurable_restr d) ((hK.image (s6b_continuous_restrC d)).isClosed.measurableSet)

/-- **(P) direction.** -/
theorem s6b_mem_NSet (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {κ : ConfigC d} {ε : ℝ}
    {D₀ Dt₀ : ContMetric d} (hD₀ : D₀.IsLength) (hDt₀ : Dt₀.IsLength) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) (z : Rd d)
    (hC : configC hd D₀ Dt₀ hD₀ hDt₀ hs hr z ∈ configCompactFamily hd c C β)
    (hclose : S6bCloseLe (configC hd D₀ Dt₀ hD₀ hDt₀ hs hr z) κ ε) :
    config D₀ Dt₀ s r z ∈ s6bNSet hd c C β κ ε := by
  refine ⟨configC hd D₀ Dt₀ hD₀ hDt₀ hs hr z, ⟨hC, hclose⟩, ?_⟩
  simp only [s6bRestrC, s6bRestr]
  congr 1
  · funext p
    exact configC_bridge_outer hd D₀ Dt₀ hD₀ hDt₀ hs hr z p.1 p.2
  · funext p
    exact configC_bridge_outer_tilde hd D₀ Dt₀ hD₀ hDt₀ hs hr z p.1 p.2

/-- **(T) direction.** Membership gives a close `q ∈ C(β)` whose coordinates are the outer
configuration coordinates. -/
theorem s6b_eq_of_mem_NSet (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {κ : ConfigC d} {ε : ℝ}
    {D₀ Dt₀ : ContMetric d} (hD₀ : D₀.IsLength) (hDt₀ : Dt₀.IsLength) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) (z : Rd d) (hN : config D₀ Dt₀ s r z ∈ s6bNSet hd c C β κ ε) :
    ∃ q ∈ configCompactFamily hd c C β, S6bCloseLe q κ ε ∧
      (∀ u v : configOuter d,
        (config D₀ Dt₀ s r z).1 (u : Rd d) (v : Rd d) = ENNReal.ofReal (q.1 (u, v))) ∧
      (∀ u v : configOuter d,
        (config D₀ Dt₀ s r z).2.1 (u : Rd d) (v : Rd d) = ENNReal.ofReal (q.2.1 (u, v))) := by
  obtain ⟨q, ⟨hqC, hqclose⟩, hq⟩ := hN
  set q₀ := configC hd D₀ Dt₀ hD₀ hDt₀ hs hr z with hq₀
  have hdense : Dense (s6bDense d ×ˢ s6bDense d) := (s6bDense_dense d).prod (s6bDense_dense d)
  have hagree1 : (fun p : configOuter d × configOuter d => ENNReal.ofReal (q₀.1 p)) =
      fun p => ENNReal.ofReal (q.1 p) := by
    refine Continuous.ext_on hdense (ENNReal.continuous_ofReal.comp q₀.1.continuous)
      (ENNReal.continuous_ofReal.comp q.1.continuous) ?_
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have h1 := congrFun (congrArg Prod.fst hq) (⟨u, hu⟩, ⟨v, hv⟩)
    simp only [s6bRestrC, s6bRestr] at h1
    show ENNReal.ofReal (q₀.1 (u, v)) = ENNReal.ofReal (q.1 (u, v))
    rw [h1]
    exact configC_bridge_outer hd D₀ Dt₀ hD₀ hDt₀ hs hr z u v
  have hagree2 : (fun p : configOuter d × configOuter d => ENNReal.ofReal (q₀.2.1 p)) =
      fun p => ENNReal.ofReal (q.2.1 p) := by
    refine Continuous.ext_on hdense (ENNReal.continuous_ofReal.comp q₀.2.1.continuous)
      (ENNReal.continuous_ofReal.comp q.2.1.continuous) ?_
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have h1 := congrFun (congrArg Prod.snd hq) (⟨u, hu⟩, ⟨v, hv⟩)
    simp only [s6bRestrC, s6bRestr] at h1
    show ENNReal.ofReal (q₀.2.1 (u, v)) = ENNReal.ofReal (q.2.1 (u, v))
    rw [h1]
    exact configC_bridge_outer_tilde hd D₀ Dt₀ hD₀ hDt₀ hs hr z u v
  refine ⟨q, hqC, hqclose, fun u v => ?_, fun u v => ?_⟩
  · rw [← configC_bridge_outer hd D₀ Dt₀ hD₀ hDt₀ hs hr z u v]
    exact congrFun hagree1 (u, v)
  · rw [← configC_bridge_outer_tilde hd D₀ Dt₀ hD₀ hDt₀ hs hr z u v]
    exact congrFun hagree2 (u, v)

/-! ### (T) from the stability properties -/

/-- **(T)** for a configuration in a trap set (S6a's `trapProps_of_stable`, recipe of its handoff
§2). -/
theorem s6b_trapProps_of_mem (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 ≤ ξ) {c C : ℝ} {β : ConfigBounds d}
    {κ : ConfigC d} {ε : ℝ} {V : Set (Rd d)} (hV : IsOpen V)
    (hVA : closure V ⊆ ann (0 : Rd d) 1 3) {fκ : C(Rd d, ℝ)} (hf0 : ∀ x, 0 ≤ fκ x)
    (hfV : ∀ x, 0 < fκ x ↔ x ∈ V) {Mf : ℝ} (hfM : ∀ x, fκ x ≤ Mf)
    {f' : ℕ → C(Rd d, ℝ)} {J j : ℕ} (hf'j : f' j = fκ)
    (hf'supp : ∀ i < J, tsupport (f' i) ⊆ ann (0 : Rd d) 1 3)
    {a b cκ c₀ c' ε₀ : ℝ} (ha : 0 < a) (hba : b ≤ a) (hc₀ : c₀ ≤ cκ) (hε₀ : 3 * ε₀ ≤ a)
    {ε' : ℝ} (hεε' : ε < ε')
    (hstab : ∀ q ∈ configCompactFamily hd c C β, S6bClose q κ ε' →
      S6bStable ξ V fκ ε₀ b cκ c' a q.1 q.2.1)
    {D₀ Dt₀ : ContMetric d} (hD₀ : D₀.IsLength) (hDt₀ : Dt₀.IsLength) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) (z : Rd d) (hN : config D₀ Dt₀ s r z ∈ s6bNSet hd c C β κ ε) :
    TrapProps ξ V f' J a b c₀ a (a * Real.exp (ξ * Mf)) c' D₀ Dt₀ s r z j := by
  obtain ⟨q, hqC, hqclose, hE1, hE2⟩ := s6b_eq_of_mem_NSet hd hD₀ hDt₀ hs hr z hN
  obtain ⟨L1, L2, L3⟩ := hstab q hqC (hqclose.close hεε')
  refine trapProps_of_stable hξ D₀ Dt₀ hs hr z hV hVA hf0 hfV hfM hf'j hf'supp ha hba
    (E := fun u v => ENNReal.ofReal (q.1 (u, v)))
    (Et := fun u v => ENNReal.ofReal (q.2.1 (u, v)))
    (fun u v => (hE1 u v).symm) (fun u v => (hE2 u v).symm)
    (w := fun z => Real.exp (-(ξ * fκ z))) (fun _ => rfl)
    (fun x y hx hy => (L1 x y hx hy).le.trans (ENNReal.ofReal_le_ofReal hε₀))
    (fun Q hQ h0 h1 hmin hb => ?_)
    (fun x y hx hy => ENNReal.ofReal_le_ofReal (by linarith [L3 x y hx hy]))
  have hc1 := (configCompactFamily_outer_P1 hd c C β hqC).1
  have hnn : 0 ≤ q.1 (Q 0, Q 1) := by
    have h := dist_nonneg (x := MetricFunSpace.pt q.1 hc1.metric (Q 0))
      (y := MetricFunSpace.pt q.1 hc1.metric (Q 1))
    exact h
  obtain ⟨u, v, hu, huv, hv, hlen, S, hS⟩ :=
    L2 Q hQ h0 h1 hmin ((ENNReal.ofReal_le_ofReal_iff hnn).1 hb)
  exact ⟨u, v, hu, huv, hv, (ENNReal.ofReal_le_ofReal hc₀).trans hlen, S, hS⟩

end HigherDimLQGMetric
