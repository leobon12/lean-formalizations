/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9DChart

/-!
# Theorem 1.5 (iii) at every contact: the chart event and the transfer back (ruling R124 (c))

Packet PROVE-RC-CROSS. Deterministic and measurability steps of the proof of
`RealContact.CriticalCrossingContactStatement` from clause (i) applied in the first-contact restart chart
(`RealContact.criticalCrossingContact_of_ordered`, `Spec/RealContact/Cross.lean`).

* **Capacity clocks** (`clock_zero`, `clock_coe_eq_iff`, `tendsto_clock_left`): a strictly increasing clock `c`
  mapping `[0, U]` onto `[s₀, ζ]` (`s₀ < ζ`) starts at `s₀`, reaches `ζ` exactly at a finite `U`, and is continuous
  from the left there. So chart terminal times and physical terminal times correspond.
* **Cluster lemma** (`eq_of_tendsto_of_cluster`): if `φ` has limits `L i` along `D` at points `x i ∈ closure D`, with
  `x i → p` and `L i → ℓ`, and `φ → m` along `D` at `p`, then `ℓ = m`. It identifies the chart point of a terminal
  physical time with the chart limit of the other path at the same physical point.
* **The chart event** `EndpointContactsOnly f A g B`: every contact `f u = g v` of the closed available paths has
  `u ∈ {0, A}` and `v ∈ {0, B}`. Clause (i) in the chart (common seed `0`) gives it, and it is a measurable event of the
  restart coordinates (`measurableSet_endpointContactsOnly`: a countable description by contacts in rectangles with
  dyadic corners, `Supp9D.measurableSet_hasContactIn`).
* **Transfer** (`isFirstContact_or_terminal_of_chart`): at the first contact `(s₀, t₀)` of injective continuous
  available paths with Lemma 7.7's confinement, the chart limits of the restart carrier and the chart event give: every
  contact of the closed available paths is the first contact or terminal for both.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace RealContact

open Sec2.Assembly

/-! ### Capacity clocks -/

section Clock

variable {c : ℝ≥0 → ℝ≥0} {U ζ : ℝ≥0∞} {s₀ : ℝ≥0}

/-- A strictly increasing clock from `[0, U]` onto `[s₀, ζ]` starts at `s₀`. -/
theorem clock_zero (hm : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (him : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ) :
    c 0 = s₀ := by
  have hs : s₀ ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := by rw [him]; exact ⟨le_rfl, hs₀⟩
  obtain ⟨w, hw, hcw⟩ := hs
  have h0 : (0 : ℝ≥0) ∈ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U} := by
    show ((0 : ℝ≥0) : ℝ≥0∞) ≤ U
    rw [ENNReal.coe_zero]
    exact zero_le
  have hc0 : c 0 ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := mem_image_of_mem c h0
  rw [him] at hc0
  exact le_antisymm (hcw ▸ hm.monotoneOn h0 hw zero_le) hc0.1

/-- A strictly increasing clock from `[0, U]` onto `[s₀, ζ]` (`s₀ < ζ`) takes the value `ζ` exactly at `U`. -/
theorem clock_coe_eq_iff (hm : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (him : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) ≤ U) : ((c v : ℝ≥0∞) = ζ ↔ (v : ℝ≥0∞) = U) := by
  have hcv : c v ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := mem_image_of_mem c hv
  rw [him] at hcv
  constructor
  · intro hζ
    by_contra hne
    obtain ⟨r, hvr, hrU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_of_le_of_ne hv hne)
    have hr : r ∈ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U} := hrU.le
    have hlt : c v < c r := hm hv hr (ENNReal.coe_lt_coe.1 hvr)
    have hcr : c r ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := mem_image_of_mem c hr
    rw [him] at hcr
    exact absurd (hcr.2.trans_eq hζ.symm) (not_le.2 (ENNReal.coe_lt_coe.2 hlt))
  · intro hU
    refine le_antisymm hcv.2 ?_
    by_contra hlt
    obtain ⟨r, hvr, hrζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hlt)
    have hvr' : c v < r := ENNReal.coe_lt_coe.1 hvr
    have hr : r ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := by
      rw [him]
      exact ⟨hcv.1.trans hvr'.le, hrζ.le⟩
    obtain ⟨w, hw, hcw⟩ := hr
    have hwv : w ≤ v := ENNReal.coe_le_coe.1 (hw.trans hU.symm.le)
    exact absurd (hcw ▸ hm.monotoneOn hw hv hwv) (not_le.2 hvr')

/-- A strictly increasing clock from `[0, U]` onto `[s₀, ζ]` (`s₀ < ζ`) with `U` finite is continuous from the left
at `U`. -/
theorem tendsto_clock_left (hm : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (him : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) (hs₀ : (s₀ : ℝ≥0∞) < ζ) {V : ℝ≥0}
    (hV : (V : ℝ≥0∞) = U) : Tendsto c (𝓝[<] V) (𝓝 (c V)) := by
  have hset : Iic V = {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U} := by
    ext u
    simp only [mem_Iic, mem_ofPred_eq, ← hV, ENNReal.coe_le_coe]
  have hm' : StrictMonoOn c (Iic V) := hset ▸ hm
  have hcV : (c V : ℝ≥0∞) = ζ := (clock_coe_eq_iff hm him hV.le).2 hV
  have hcont : ContinuousWithinAt c (Iic V) V := by
    refine hm'.continuousWithinAt_left_of_exists_between self_mem_nhdsWithin fun b hb => ?_
    have hy : max b s₀ ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := by
      rw [him]
      refine ⟨le_max_right _ _, ?_⟩
      rw [← hcV]
      exact ENNReal.coe_le_coe.2 (max_le hb.le (ENNReal.coe_le_coe.1 (hcV ▸ hs₀).le))
    obtain ⟨w, hw, hcw⟩ := hy
    refine ⟨w, hset ▸ hw, ?_, ?_⟩
    · rw [hcw]
      exact le_max_left _ _
    · rw [hcw]
      exact max_lt hb (ENNReal.coe_lt_coe.1 (hcV ▸ hs₀))
  exact hcont.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

end Clock

/-! ### Limits along a domain at cluster points -/

/-- **Cluster lemma.** If `φ` tends to `L i` along `D` at points `x i ∈ closure D`, with `x i → p` and `L i → ℓ` along
a nontrivial filter, and `φ` tends to `m` along `D` at `p`, then `ℓ = m`. -/
theorem eq_of_tendsto_of_cluster {ι : Type*} {F : Filter ι} [F.NeBot] {φ : ℂ → ℂ} {D : Set ℂ}
    {x L : ι → ℂ} {p ℓ m : ℂ} (hx : Tendsto x F (𝓝 p)) (hL : Tendsto L F (𝓝 ℓ))
    (hloc : ∀ᶠ i in F, x i ∈ closure D ∧ Tendsto φ (𝓝[D] (x i)) (𝓝 (L i)))
    (hp : Tendsto φ (𝓝[D] p) (𝓝 m)) : ℓ = m := by
  by_contra hne
  have hε : 0 < dist ℓ m / 3 := by
    have := dist_pos.2 hne
    positivity
  obtain ⟨δ, hδ, hD⟩ := Metric.tendsto_nhdsWithin_nhds.1 hp _ hε
  obtain ⟨i, hxi, hLi, hcl, hti⟩ := ((Metric.tendsto_nhds.1 hx (δ / 2) (half_pos hδ)).and
    ((Metric.tendsto_nhds.1 hL _ hε).and hloc)).exists
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have h1 : ∀ᶠ z in 𝓝[D] (x i), dist (φ z) (L i) < dist ℓ m / 3 := Metric.tendsto_nhds.1 hti _ hε
  have h2 : ∀ᶠ z in 𝓝[D] (x i), z ∈ ball (x i) (δ / 2) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (half_pos hδ))
  have h3 : ∀ᶠ z in 𝓝[D] (x i), z ∈ D := self_mem_nhdsWithin
  obtain ⟨z, hz1, hz2, hz3⟩ := (h1.and (h2.and h3)).exists
  have hzp : dist z p < δ := by
    calc dist z p ≤ dist z (x i) + dist (x i) p := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (Metric.mem_ball.1 hz2) hxi
      _ = δ := add_halves δ
  have hzm := hD hz3 hzp
  have hlt : dist ℓ m < dist ℓ m := by
    calc dist ℓ m ≤ dist ℓ (L i) + dist (L i) (φ z) + dist (φ z) m := dist_triangle4 _ _ _ _
      _ < dist ℓ m / 3 + dist ℓ m / 3 + dist ℓ m / 3 := by
          refine add_lt_add (add_lt_add ?_ ?_) hzm
          · rw [dist_comm]; exact hLi
          · rw [dist_comm]; exact hz1
      _ = dist ℓ m := by ring
  exact lt_irrefl _ hlt

/-! ### The chart event -/

/-- **The chart event**: every contact `f u = g v` of the closed available paths `f|[0, A]`, `g|[0, B]` is at endpoint
parameters, `u ∈ {0, A}` and `v ∈ {0, B}`. -/
def EndpointContactsOnly (f : ℝ≥0 → ℂ) (A : ℝ≥0∞) (g : ℝ≥0 → ℂ) (B : ℝ≥0∞) : Prop :=
  ∀ u v : ℝ≥0, (u : ℝ≥0∞) ≤ A → (v : ℝ≥0∞) ≤ B → f u = g v →
    (u = 0 ∨ (u : ℝ≥0∞) = A) ∧ (v = 0 ∨ (v : ℝ≥0∞) = B)

/-- No contact `f u = g v` with `0 < u < A` and `v ≤ B`. -/
def NoMidContact (f : ℝ≥0 → ℂ) (A : ℝ≥0∞) (g : ℝ≥0 → ℂ) (B : ℝ≥0∞) : Prop :=
  ∀ u v : ℝ≥0, 0 < u → (u : ℝ≥0∞) < A → (v : ℝ≥0∞) ≤ B → f u ≠ g v

theorem endpointContactsOnly_iff {f g : ℝ≥0 → ℂ} {A B : ℝ≥0∞} :
    EndpointContactsOnly f A g B ↔ NoMidContact f A g B ∧ NoMidContact g B f A := by
  constructor
  · intro h
    refine ⟨fun u v hu huA hvB he => ?_, fun v u hv hvB huA he => ?_⟩
    · rcases (h u v huA.le hvB he).1 with h0 | hA
      · exact hu.ne' h0
      · exact huA.ne hA
    · rcases (h u v huA hvB.le he.symm).2 with h0 | hB
      · exact hv.ne' h0
      · exact hvB.ne hB
  · rintro ⟨h₁, h₂⟩ u v huA hvB he
    refine ⟨?_, ?_⟩
    · by_contra hn
      obtain ⟨hn0, hnA⟩ := not_or.1 hn
      exact h₁ u v (pos_iff_ne_zero.2 hn0) (lt_of_le_of_ne huA hnA) hvB he
    · by_contra hn
      obtain ⟨hn0, hnB⟩ := not_or.1 hn
      exact h₂ v u (pos_iff_ne_zero.2 hn0) (lt_of_le_of_ne hvB hnB) huA he.symm

/-- **No middle contact, countably**: no contact in any rectangle `[a, b] × [0, N]` with dyadic `0 < a`, dyadic
`b < A` and `N ∈ ℕ`. -/
theorem noMidContact_iff {f g : ℝ≥0 → ℂ} {A B : ℝ≥0∞} :
    NoMidContact f A g B ↔ ∀ p i q j N : ℕ, 0 < dyad p i → (dyad q j : ℝ≥0∞) < A →
      ¬ Supp9D.HasContactIn f g A B (dyad p i) (dyad q j) (dyad 0 0) N := by
  constructor
  · rintro h p i q j N ha hb ⟨x, y, hax, hxb, -, -, hxA, hyB, hxy⟩
    exact h x y (ha.trans_le hax) ((ENNReal.coe_le_coe.2 hxb).trans_lt hb) hyB hxy
  · intro h u v hu huA hvB huv
    obtain ⟨p, hp⟩ := ((tendsto_dyad_flr u).eventually (lt_mem_nhds hu)).exists
    obtain ⟨r, hur, hrA⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 huA
    obtain ⟨q, hq⟩ := ((tendsto_dyad_flr r).eventually (lt_mem_nhds (ENNReal.coe_lt_coe.1 hur))).exists
    refine h p (flr p u) q (flr q r) ⌈v⌉₊ hp
      ((ENNReal.coe_le_coe.2 (dyad_flr_le q r)).trans_lt hrA)
      ⟨u, v, dyad_flr_le p u, hq.le, ?_, Nat.le_ceil v, huA.le, hvB, huv⟩
    rw [Supp9D.dyad_zero_zero']
    exact zero_le

section Meas

variable {S : Type*} [MeasurableSpace S] {H : S → LQGMetric.DistOn upperHalfPlaneOpens}
  {Γ₁ Γ₂ : S → ℝ≥0 → ℂ} {U₁ U₂ : S → ℝ≥0∞}

/-- The restart coordinates with the two paths exchanged. -/
theorem isRestartCoordinates_swap (hc : Restart.IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂) :
    Restart.IsRestartCoordinates H Γ₂ Γ₁ U₂ U₁ := by
  obtain ⟨hH, hU₁, hU₂, hΓ₁, hΓ₂, hc₁, hc₂⟩ := hc
  exact ⟨hH, hU₂, hU₁, hΓ₂, hΓ₁, hc₂, hc₁⟩

theorem measurableSet_noMidContact (hc : Restart.IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂) :
    MeasurableSet {s | NoMidContact (Γ₁ s) (U₁ s) (Γ₂ s) (U₂ s)} := by
  have hU₁ : Measurable U₁ := hc.2.1
  have hset : {s | NoMidContact (Γ₁ s) (U₁ s) (Γ₂ s) (U₂ s)} =
      ⋂ (p : ℕ) (i : ℕ) (q : ℕ) (j : ℕ) (N : ℕ), {s | 0 < dyad p i → (dyad q j : ℝ≥0∞) < U₁ s →
        ¬ Supp9D.HasContactIn (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad p i) (dyad q j) (dyad 0 0) N} := by
    ext s
    simp only [mem_ofPred_eq, mem_iInter]
    exact noMidContact_iff
  rw [hset]
  refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun i => MeasurableSet.iInter fun q =>
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun N => ?_
  refine measurableSet_setOfPred.2 (Measurable.imp measurable_const (Measurable.imp ?_ (Measurable.not ?_)))
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hU₁)
  · exact measurableSet_setOfPred.1 (Supp9D.measurableSet_hasContactIn hc p i _ 0 0 _)

/-- **The chart event is measurable** on the canonical space of the restart coordinates. -/
theorem measurableSet_endpointContactsOnly (hc : Restart.IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂) :
    MeasurableSet {s | EndpointContactsOnly (Γ₁ s) (U₁ s) (Γ₂ s) (U₂ s)} := by
  have hset : {s | EndpointContactsOnly (Γ₁ s) (U₁ s) (Γ₂ s) (U₂ s)} =
      {s | NoMidContact (Γ₁ s) (U₁ s) (Γ₂ s) (U₂ s)} ∩ {s | NoMidContact (Γ₂ s) (U₂ s) (Γ₁ s) (U₁ s)} := by
    ext s
    exact endpointContactsOnly_iff
  rw [hset]
  exact (measurableSet_noMidContact hc).inter (measurableSet_noMidContact (isRestartCoordinates_swap hc))

end Meas

/-! ### The transfer back to physical contacts -/

/-- **The chart point at a terminal time.** For a path `η` continuous on `[0, ζ]` and confined to `closure D` after
`s₀ < ζ`, a clock `c` from `[0, U]` onto `[s₀, ζ]`, a continuous chart path `γ` on `[0, U]` with `φ → γ u` along `D`
at `η (c u)` for `u < U`: at a finite lifetime `V = U`, if `φ → m` along `D` at the terminal point `η (c V)`, then
`γ V = m` (cluster lemma along the clock as `u ↑ V`). -/
theorem chart_terminal_eq {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {s₀ : ℝ≥0}
    (hcη : ContinuousOn η {s | (s : ℝ≥0∞) ≤ ζ}) {D : Set ℂ}
    (hconf : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ → η s ∈ closure D) {φ : ℂ → ℂ}
    {γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} {c : ℝ≥0 → ℝ≥0} (hγ : ContinuousOn γ {u | (u : ℝ≥0∞) ≤ U})
    (hm : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (him : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) (hs₀ : (s₀ : ℝ≥0∞) < ζ)
    (hlim : ∀ u : ℝ≥0, (u : ℝ≥0∞) < U → Tendsto φ (𝓝[D] (η (c u))) (𝓝 (γ u)))
    {V : ℝ≥0} (hV : (V : ℝ≥0∞) = U) {m : ℂ} (hp : Tendsto φ (𝓝[D] (η (c V))) (𝓝 m)) : γ V = m := by
  have hVU : V ∈ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U} := hV.le
  have hcVζ : (c V : ℝ≥0∞) = ζ := (clock_coe_eq_iff hm him hV.le).2 hV
  have hpos : (0 : ℝ≥0) < V := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, clock_zero hm him hs₀.le] at hcVζ
    exact hs₀.ne hcVζ
  have : (𝓝[<] V).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  have hlt : ∀ᶠ u in 𝓝[<] V, u < V := self_mem_nhdsWithin
  have hle : ∀ u : ℝ≥0, u < V → (u : ℝ≥0∞) ≤ U := fun u hu => hV ▸ ENNReal.coe_le_coe.2 hu.le
  have hmem : ∀ u : ℝ≥0, u < V → c u ∈ {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ} := fun u hu => by
    rw [← him]
    exact mem_image_of_mem c (hle u hu)
  have hx : Tendsto (fun u => η (c u)) (𝓝[<] V) (𝓝 (η (c V))) := by
    have hc' : Tendsto c (𝓝[<] V) (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ ζ}] (c V)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_clock_left hm him hs₀ hV, hlt.mono fun u hu => (hmem u hu).2⟩
    exact ((hcη (c V) hcVζ.le).tendsto).comp hc'
  have hL : Tendsto γ (𝓝[<] V) (𝓝 (γ V)) :=
    ((hγ V hVU).tendsto).mono_left (nhdsWithin_mono _ fun u (hu : u < V) => hle u hu)
  refine eq_of_tendsto_of_cluster hx hL (hlt.mono fun u hu => ⟨hconf _ (hmem u hu).1 (hmem u hu).2,
    hlim u ?_⟩) hp
  rw [← hV]
  exact ENNReal.coe_lt_coe.2 hu

/-- **The transfer back to physical contacts** (supplement p. 544, extended to every contact). Let `(s₀, t₀)` be the
first contact of injective continuous available paths, both confined after it to `closure D` (Lemma 7.7). Suppose that,
when both continuations are nonempty, there are a map `φ`, chart continuations `γᵢ` (continuous on `[0, Uᵢ]`), capacity
clocks `cᵢ` from `[0, Uᵢ]` onto the physical continuations, the chart limits `φ → γᵢ u` along `D` at `ηᵢ (cᵢ u)`
(`u < Uᵢ`), and that every chart contact is at endpoint parameters (`EndpointContactsOnly`, clause (i) in the chart).
Then every contact of the closed available paths is the first contact or terminal for both.

Cases: a first contact terminal for one path forces every contact to be it (injectivity); two parameters before the
lifetimes give equal chart limits at one physical point, so a chart contact, hence the seed `(0, 0)`, i.e. the first
contact; one terminal parameter gives a chart contact by the cluster lemma (`chart_terminal_eq`), whose other parameter
is then the seed, contradicting injectivity; two terminal parameters are terminal for both. -/
theorem isFirstContact_or_terminal_of_chart {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
    (hc₁ : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) {D : Set ℂ}
    (hconf₁ : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure D)
    (hconf₂ : ∀ t : ℝ≥0, t₀ ≤ t → (t : ℝ≥0∞) ≤ ζ₂ → η₂ t ∈ closure D)
    (hchart : (s₀ : ℝ≥0∞) < ζ₁ → (t₀ : ℝ≥0∞) < ζ₂ →
      ∃ (φ : ℂ → ℂ) (γ₁ γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) (c₁ c₂ : ℝ≥0 → ℝ≥0),
        ContinuousOn γ₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧ ContinuousOn γ₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
        StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧
        c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁} ∧
        StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
        c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂} ∧
        (∀ u : ℝ≥0, (u : ℝ≥0∞) < U₁ → Tendsto φ (𝓝[D] (η₁ (c₁ u))) (𝓝 (γ₁ u))) ∧
        (∀ u : ℝ≥0, (u : ℝ≥0∞) < U₂ → Tendsto φ (𝓝[D] (η₂ (c₂ u))) (𝓝 (γ₂ u))) ∧
        EndpointContactsOnly γ₂ U₂ γ₁ U₁)
    {s t : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ₁) (ht : (t : ℝ≥0∞) ≤ ζ₂) (hst : η₁ s = η₂ t) :
    IsFirstContact η₁ ζ₁ η₂ ζ₂ s t ∨ ((s : ℝ≥0∞) = ζ₁ ∧ (t : ℝ≥0∞) = ζ₂) := by
  obtain ⟨hss, htt⟩ := h₀.2.2.2 s t hs ht hst
  by_cases hs₀ : (s₀ : ℝ≥0∞) < ζ₁
  swap
  · have hse : s = s₀ := le_antisymm (ENNReal.coe_le_coe.1 (hs.trans (not_lt.1 hs₀))) hss
    have hte : t = t₀ := hi₂ ht h₀.2.1 (hst.symm.trans (hse ▸ h₀.2.2.1))
    rw [hse, hte]
    exact Or.inl h₀
  by_cases ht₀ : (t₀ : ℝ≥0∞) < ζ₂
  swap
  · have hte : t = t₀ := le_antisymm (ENNReal.coe_le_coe.1 (ht.trans (not_lt.1 ht₀))) htt
    have hse : s = s₀ := hi₁ hs h₀.1 (hst.trans (hte ▸ h₀.2.2.1.symm))
    rw [hse, hte]
    exact Or.inl h₀
  obtain ⟨φ, γ₁, γ₂, U₁, U₂, c₁, c₂, hγ₁, hγ₂, hm₁, him₁, hm₂, him₂, hl₁, hl₂, hE⟩ := hchart hs₀ ht₀
  have hsI : s ∈ c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} := by rw [him₁]; exact ⟨hss, hs⟩
  have htI : t ∈ c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} := by rw [him₂]; exact ⟨htt, ht⟩
  obtain ⟨v, hv, rfl⟩ := hsI
  obtain ⟨u, hu, rfl⟩ := htI
  replace hv : (v : ℝ≥0∞) ≤ U₁ := hv
  replace hu : (u : ℝ≥0∞) ≤ U₂ := hu
  have hz₁ := clock_zero hm₁ him₁ h₀.1
  have hz₂ := clock_zero hm₂ him₂ h₀.2.1
  rcases lt_or_eq_of_le hv with hvU | hvU <;> rcases lt_or_eq_of_le hu with huU | huU
  · -- both parameters before the lifetimes: equal chart limits at one physical point
    have := mem_closure_iff_nhdsWithin_neBot.1 (hconf₁ _ hss hs)
    have hl₂' : Tendsto φ (𝓝[D] (η₁ (c₁ v))) (𝓝 (γ₂ u)) := by rw [hst]; exact hl₂ u huU
    have heq : γ₁ v = γ₂ u := tendsto_nhds_unique (hl₁ v hvU) hl₂'
    obtain ⟨h1, h2⟩ := hE u v hu hv heq.symm
    rcases h1 with rfl | h1
    · rcases h2 with rfl | h2
      · left
        rw [hz₁, hz₂]
        exact h₀
      · exact absurd h2 hvU.ne
    · exact absurd h1 huU.ne
  · -- the second path at its lifetime, the first before
    have hp : Tendsto φ (𝓝[D] (η₂ (c₂ u))) (𝓝 (γ₁ v)) := by rw [← hst]; exact hl₁ v hvU
    have heq : γ₂ u = γ₁ v := chart_terminal_eq hc₂ hconf₂ hγ₂ hm₂ him₂ ht₀ hl₂ huU hp
    obtain ⟨-, h2⟩ := hE u v hu hv heq
    rcases h2 with rfl | h2
    · exfalso
      rw [hz₁] at hst
      have hte : c₂ u = t₀ := hi₂ ht h₀.2.1 (hst.symm.trans h₀.2.2.1)
      have hζ := (clock_coe_eq_iff hm₂ him₂ hu).2 huU
      rw [hte] at hζ
      exact ht₀.ne hζ
    · exact absurd h2 hvU.ne
  · -- the first path at its lifetime, the second before
    have hp : Tendsto φ (𝓝[D] (η₁ (c₁ v))) (𝓝 (γ₂ u)) := by rw [hst]; exact hl₂ u huU
    have heq : γ₁ v = γ₂ u := chart_terminal_eq hc₁ hconf₁ hγ₁ hm₁ him₁ hs₀ hl₁ hvU hp
    obtain ⟨h1, -⟩ := hE u v hu hv heq.symm
    rcases h1 with rfl | h1
    · exfalso
      rw [hz₂] at hst
      have hse : c₁ v = s₀ := hi₁ hs h₀.1 (hst.trans h₀.2.2.1.symm)
      have hζ := (clock_coe_eq_iff hm₁ him₁ hv).2 hvU
      rw [hse] at hζ
      exact hs₀.ne hζ
    · exact absurd h1 huU.ne
  · -- both at their lifetimes
    exact Or.inr ⟨(clock_coe_eq_iff hm₁ him₁ hv).2 hvU, (clock_coe_eq_iff hm₂ him₂ hu).2 huU⟩

end RealContact

end InteractingSLE
