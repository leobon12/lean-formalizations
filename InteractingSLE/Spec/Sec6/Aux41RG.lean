/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Gate
import InteractingSLE.Spec.Sec6.Aux39Fresh
import InteractingSLE.Spec.Sec6.Aux40Clock

/-!
# Aux. lemma 41, (RG1)–(RG2): mapped gap equality after an erased prefix

Specification §6.2, **Aux.** lemma 41 (`source/spec/p193-240.md` L214–L265), in the repaired form of
ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt`, Proposition 1.6, L273–L315):

> Fix a nonterminal erased time and let `s < σ` be the right endpoint of its original-time clock
> fibre. For every later positive gap `[a, b]` with common physical endpoint `p`, one has
> `δ_s(a) = δ_s(b)`. ... If `p ∉ R_s`, then `p ∈ D_s` ... `g_s` is analytic at `p` and the claimed
> equality follows. Suppose `p ∈ R_s`. ... Choose a rational `r` with `s < r < a`,
> `r > max{T(p₁), T(p₂)}`. Both prefixes are unchanged on `[r, b]` by Lemma 1.2(3). The fixed-chart
> gate lemma applies ... and gives `δ_r(a) = δ_r(b)`. ... the continuous inverse-increment
> composition from Lemma 1.2(2) gives `δ_s(a) = f_{s,r}(δ_r(a)) = f_{s,r}(δ_r(b)) = δ_s(b)`.

Here (RG1) is the own-mapped future `δ_s(t) = trMap W s t 0` ([Yua22, Corollary 1.3],
PROVE-YUAN-M1). This file proves:

* `trace_notMem_fwdHull`: original no-entry into filled pockets: a later interior point not in
  `R_s` is in `D_s`;
* `ownFuture_eq_of_mem_domain`: the case `p ∈ D_s` of Proposition 1.6;
* `ownFuture_mem_closure_face`: confinement (1.2) from (1.1) (`η(t) ∈ C ⇒ δ_r(t) ∈ F̄_r`, also at
  endpoints approached by `C`-visits), via Lemma 1.2(1);
* `ownFuture_gap_eq_of_face`: **Proposition 1.6 in a fixed chart** — given the central Jordan-face
  geometry of the chart at `r` (the data of Lemma 1.3, finite junction) with (1.1), `f̄_r(F_r) ⊆ C`
  and the incoming tree unvisited on the gap, the mapped gap endpoints agree in every earlier chart
  `s ≤ r`; and the physical equality `η(a) = η(b)` (Proposition 1.5 / (GC1), old-start case);
* `continuousOn_collapsed_ownFuture`: the collapsed future `v ↦ δ_s(fibreRight v)` is continuous
  once every gap has equal mapped endpoints ((RG2) ⇒ the continuous `Δ_s` of Aux. 41).

The chart-face geometry itself (the lifted arms, `F_r = g_r(E_r)` and (1.1)) is the geometric part
of **Aux.** lemma 36 and is a hypothesis here (distinct names; see the handoff).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- `f̄_s(ℍ) = ℍ \ K_s`. -/
theorem trMap_zero_image_H (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    trMap W 0 s '' H = H \ fwdHull W s := by
  rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hs]
  refine image_congr fun v hv => ?_
  rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs hv, YuanSimpleApprox.shiftDrive_zero_eq hW0,
    sub_zero]

/-- Values of `f̄_s` on `ℍ̄` are adherent to `D_s = ℍ \ K_s`. -/
theorem trMap_zero_mem_closure (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : w ∈ Hbar) :
    trMap W 0 s w ∈ closure (H \ fwdHull W s) := by
  rw [← trMap_zero_image_H hW hW0 hs]
  have hc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs
  have hwcl : w ∈ closure H := by rw [closure_H]; exact hw
  exact (hc.mono (by rw [closure_H])).image_closure ⟨w, hwcl, rfl⟩

/-- **No entry into filled pockets.** A point `η(t)`, `t ≥ s`, of `ℍ` which was not visited by
time `s` lies in `D_s = ℍ \ K_s`. -/
theorem trace_notMem_fwdHull (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hnot : η t ∉ η '' Icc 0 s) : η t ∉ fwdHull W s := by
  intro hK
  have hcl : η t ∈ closure (H \ fwdHull W s) := by
    rw [← traceMapOut_trMap_zero hη hW hW0 hs hst]
    exact trMap_zero_mem_closure hη hW hW0 hs
      (YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hs hst)
  rw [hη.2.2 s hs] at hK hcl
  have := mem_closure_of_mem_fillH_of_mem_closure hK hcl
  have hcpt : IsCompact (η '' Icc 0 s) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun r hr => hr.1)
  rw [hcpt.isClosed.closure_eq] at this
  exact hnot this

/-- **Proposition 1.6, the case `p ∈ D_s`.** If `η(a) = η(b) = p ∈ ℍ \ K_s` with `s ≤ a, b`, then
`δ_s(a) = δ_s(b)`. -/
theorem ownFuture_eq_of_mem_domain (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hsb : s ≤ b) (hab : η a = η b)
    (hD : η a ∈ H \ fwdHull W s) : trMap W s a 0 = trMap W s b 0 := by
  obtain ⟨-, -, hinj, hR⟩ := YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl hs
  have himg := trMap_zero_image_H hW hW0 hs
  have hH : ∀ t, s ≤ t → η t = η a → trMap W s t 0 ∈ H := by
    intro t hst ht
    have hHbar := YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hs hst
    by_contra hnH
    have him : (trMap W s t 0).im = 0 := le_antisymm (not_lt.1 hnH) hHbar
    have hval : trMap W 0 s (trMap W s t 0) = η a := by
      rw [traceMapOut_trMap_zero hη hW hW0 hs hst, ht]
    exact hR _ him (by rw [hval, himg]; exact hD)
  refine hinj (hH a hsa rfl) (hH b hsb hab.symm) ?_
  rw [traceMapOut_trMap_zero hη hW hW0 hs hsa, traceMapOut_trMap_zero hη hW hW0 hs hsb, hab]

/-- **Confinement (1.2) from (1.1).** Suppose every `C`-visit at a time `t ≥ r` whose own-mapped
value lies in `ℍ` has that value in `F` (1.1). Then the own-mapped value at every time `a` which is
a limit of `C`-visit times after `r` lies in `F̄`. (This includes `C`-visit times themselves, as `C`
is open, and gap endpoints approached by interior visits.) -/
theorem ownFuture_mem_closure_face (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C F : Set ℂ} (hC : IsOpen C) {r a : ℝ} (hr : 0 ≤ r)
    (h11 : ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H → trMap W r t 0 ∈ F)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C}) : trMap W r a 0 ∈ closure F := by
  have hδc : ContinuousOn (fun t => trMap W r t 0) (Ici r) :=
    YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr
  have har : r ≤ a := by
    have : closure {t | r < t ∧ η t ∈ C} ⊆ Ici r :=
      closure_minimal (fun t ht => le_of_lt ht.1) isClosed_Ici
    exact this ha
  -- every `C`-visit time after `r` maps into `F̄`
  have hvisit : ∀ t, r < t → η t ∈ C → trMap W r t 0 ∈ closure F := by
    intro t hrt htC
    have hηc : ContinuousAt η t := hη.2.1.continuousAt (Ici_mem_nhds (hr.trans_lt hrt))
    have hopen : ∀ᶠ t' in 𝓝 t, η t' ∈ C ∧ r < t' :=
      (hηc.eventually (hC.mem_nhds htC)).and (eventually_gt_nhds hrt)
    obtain ⟨ε, hε, hεt⟩ := Metric.eventually_nhds_iff.1 hopen
    -- `H`-valued times are dense near `t`
    have hdense : ∀ η' > 0, ∃ t' ∈ Icc (t - min η' (ε / 2)) (t + min η' (ε / 2)),
        trMap W r t' 0 ∈ H ∧ η t' ∈ C ∧ r < t' := by
      intro η' hη'
      have hm : 0 < min η' (ε / 2) := lt_min hη' (half_pos hε)
      have hle : min η' (ε / 2) ≤ ε / 2 := min_le_right _ _
      have hc : r ≤ t - min η' (ε / 2) := by
        have := (hεt (y := t - min η' (ε / 2)) (by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith)).2
        exact this.le
      obtain ⟨t', ht', hH⟩ := ownFuture_not_forall_real hη hW hW0 hr hc
        (d := t + min η' (ε / 2)) (by linarith)
      have hd : dist t' t < ε := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht'.1, ht'.2]
      exact ⟨t', ht', hH, (hεt hd).1, (hεt hd).2⟩
    have hδt : ContinuousAt (fun t => trMap W r t 0) t := hδc.continuousAt (Ici_mem_nhds hrt)
    refine mem_closure_iff_seq_limit.2 ?_
    choose f hf using fun n : ℕ => hdense (1 / (n + 1)) (by positivity)
    refine ⟨fun n => trMap W r (f n) 0, fun n => h11 (f n) (hf n).2.2.2.le (hf n).2.2.1
      (hf n).2.1, ?_⟩
    have hft : Tendsto f atTop (𝓝 t) := by
      have h0 : Tendsto (fun n : ℕ => min (1 / ((n : ℝ) + 1)) (ε / 2)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := h1.min (tendsto_const_nhds (x := ε / 2))
        rwa [min_eq_left (half_pos hε).le] at h2
      have hlo : Tendsto (fun n : ℕ => t - min (1 / ((n : ℝ) + 1)) (ε / 2)) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).sub h0
      have hhi : Tendsto (fun n : ℕ => t + min (1 / ((n : ℝ) + 1)) (ε / 2)) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).add h0
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => (hf n).1.1)
        (fun n => (hf n).1.2)
    exact hδt.tendsto.comp hft
  -- limits of visit times
  have hδa : ContinuousWithinAt (fun t => trMap W r t 0) (Ici r) a := hδc a har
  have hsub : {t | r < t ∧ η t ∈ C} ⊆ Ici r := fun t ht => le_of_lt ht.1
  have := (hδa.mono hsub).mem_closure_image ha
  refine closure_minimal ?_ isClosed_closure this
  rintro _ ⟨t, ht, rfl⟩
  exact hvisit t ht.1 ht.2

/-- **Proposition 1.6 / (RG2) in a fixed chart** (finite junction, distinct gates). In the chart at
time `r`, let the incoming tree (`A₁, A₂` from the gates `q₁ < q₂` to the junction `z`, `A₃` from
`z` to `∞`) bound the central face `F = innerSide Γ` as in Lemma 1.3. Suppose the confinement
(1.1) at `r`, that `f̄_r(F) ⊆ C`, and that on the gap `[a, b]` (`r < a < b`) the trace avoids `C`
and its own-mapped future avoids the incoming tree, both endpoints being limits of later/earlier
`C`-visits after `r`. Then `δ_s(a) = δ_s(b)` for every `0 ≤ s ≤ r`, and `η(a) = η(b)`. -/
theorem ownFuture_gap_eq_of_face (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {C : Set ℂ} (hC : IsOpen C) {q₁ q₂ : ℝ} {z : ℂ} {a₁ a₂ a₃ : ℝ → ℂ} (hq : q₁ < q₂)
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q₁)
    (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z) (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H)
    (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H) (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z})
    (ha₃ : ContinuousOn a₃ (Ici 0)) (ha₃i : InjOn a₃ (Ici 0)) (ha₃0 : a₃ 0 = z)
    (ha₃H : ∀ t ∈ Ici (0 : ℝ), a₃ t ∈ H) (ha₃t : Tendsto (fun t => ‖a₃ t‖) atTop atTop)
    (h13 : a₁ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z}) (h23 : a₂ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z})
    {s r a b : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r < a) (hab : a < b)
    (h11 : ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
      trMap W r t 0 ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))
    (hFC : trMap W 0 r '' innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) ⊆ C)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (htree : ∀ t ∈ Icc a b, trMap W r t 0 ∉ a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1 ∪ a₃ '' Ici 0)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C}) (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr : 0 ≤ r := hs.trans hsr
  set δ : ℝ → ℂ := fun t => trMap W r t 0 with hδ
  have hδc : ContinuousOn δ (Icc a b) :=
    (YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr).mono fun t ht => hra.le.trans ht.1
  have hδH : MapsTo δ (Icc a b) Hbar := fun t ht =>
    YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hr (hra.le.trans ht.1)
  -- the gap avoids the face: `f̄_r(F) ⊆ C`
  have hδF : ∀ t ∈ Icc a b,
      δ t ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) := by
    intro t ht hF
    have := hFC ⟨δ t, hF, rfl⟩
    rw [hδ, traceMapOut_trMap_zero hη hW hW0 hr (hra.le.trans ht.1)] at this
    exact hgap t ht this
  have hR : ∀ c d, a ≤ c → c < d → d ≤ b → ∃ t ∈ Icc c d, δ t ∈ H := fun c d hac hcd _ =>
    ownFuture_not_forall_real hη hW hW0 hr (hra.le.trans hac) hcd
  have hgate := gate_lemma hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12 ha₃ ha₃i ha₃0
    ha₃H ha₃t h13 h23 hab hδc hδH hδF (fun t ht h => htree t ht (Or.inl (Or.inl h)))
    (fun t ht h => htree t ht (Or.inl (Or.inr h))) (fun t ht h => htree t ht (Or.inr h)) hR
    (ownFuture_mem_closure_face hη hW hW0 hC hr h11 ha)
    (ownFuture_mem_closure_face hη hW hW0 hC hr h11 hb)
  have heq : δ a = δ b := hgate.1
  refine ⟨?_, ?_⟩
  · rw [ownFuture_trans hη hW hW0 hs hsr hra.le, ownFuture_trans hη hW hW0 hs hsr
      (hra.le.trans hab.le)]
    exact congrArg (trMap W s r) heq
  · rw [← traceMapOut_trMap_zero hη hW hW0 hr hra.le,
      ← traceMapOut_trMap_zero hη hW hW0 hr (hra.le.trans hab.le)]
    exact congrArg (trMap W 0 r) heq

/-- **The collapsed own-mapped future is continuous** ((RG2) ⇒ the continuous `Δ_s` of Aux. 41).
With the erasure clock `ℓ` (continuous, nondecreasing) and `s ≥ 0`, if the own-mapped future
`δ_s` takes equal values at the two endpoints of every nondegenerate maximal clock fibre in
`[s, S]`, then `v ↦ δ_s(fibreRight v)` is continuous on `[ℓ s, ℓ S]`. -/
theorem continuousOn_collapsed_ownFuture (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {ℓ : ℝ → ℝ} (hℓ : Continuous ℓ) (hℓm : Monotone ℓ) {s S : ℝ} (hs : 0 ≤ s)
    (hsS : s ≤ S)
    (hfib : ∀ a ∈ Icc s S, ∀ b ∈ Icc s S, a < b → ℓ a = ℓ b →
      (∀ t ∈ Icc s S, ℓ t = ℓ a → t ∈ Icc a b) → trMap W s a 0 = trMap W s b 0) :
    ContinuousOn (fun v => trMap W s (fibreRight ℓ s S v) 0) (Icc (ℓ s) (ℓ S)) :=
  continuousOn_comp_fibreRight (X := fun t => trMap W s t 0) hℓ hℓm hsS
    ((YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hs).mono fun _ ht => ht.1) hfib

end InteractingSLE.Sec6
