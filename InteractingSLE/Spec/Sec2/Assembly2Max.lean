/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Stage

/-!
# Theorem 2.2, existence: the maximal local solution driven by a path

Packet PROVE-SEC2-PATCH3. For a separated word `s` and a driving code `c` (uniformly continuous on
bounded dyadic sets, e.g. the code of a continuous path), `lifeMax s c` is the supremum of the
horizons of the local solutions from `s` driven by `c`, and `maxCode s c = lInv (s, c, lifeMax s c)`
the code of the local solution up to it:

* `measurable_lifeMax`, `measurable_maxCode`: both are jointly measurable in `(s, c)`;
* `mem_lSet_of_le`, `mem_lSet_zero`, `le_lifeMax`, `mem_lSet_of_lt_lifeMax`: the horizons that carry
  a local solution form the interval `[0, lifeMax s c]`;
* `isSLEPathUpTo_of_forall_lt`: a path that is a local solution before every earlier horizon is a
  local solution;
* **`mem_lSet_lifeMax`**: the supremum is attained (the local solutions up to the smaller horizons
  agree by local pathwise uniqueness and glue);
* **`lifeMax_eq_of_eqOn`**: the maximal horizon and the maximal solution only see the driving path
  up to any time after the maximal horizon.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

open Assembly

variable {nL nR : ℕ} {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-! ### The horizons that carry a local solution -/

/-- Smaller horizons carry the restricted local solution. -/
theorem mem_lSet_of_le {s : MWord nL nR} {c : PCode} {q q' : ℝ≥0∞}
    (hp : (s, c, q) ∈ LSet a ρL ρR) (hq : q' ≤ q) : (s, c, q') ∈ LSet a ρL ρR := by
  have huc := uc_of_mem_lSet hp
  have := mem_lSet_of_isSLEPathUpTo (sep_of_mem_lSet hp) (continuous_dec_of_uc huc)
    (isSLEPathUpTo_lInv hp) hq
  rwa [enc_dec_of_uc huc] at this

/-- The horizon `0` always carries a local solution (the constant state). -/
theorem mem_lSet_zero {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c : PCode}
    (hc : ∀ T : ℕ, UC c T) : (s, c, 0) ∈ LSet a ρL ρR := by
  have hno : ∀ {t : ℝ≥0}, ¬ (t : ℝ≥0∞) < 0 := fun h => absurd h (not_lt.2 bot_le)
  have hnull : ∀ (f g : ℝ≥0 → ℝ),
      volume {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < 0 ∧ f r.toNNReal = g r.toNNReal} = 0 :=
    fun f g => by
      have : {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < 0 ∧ f r.toNNReal = g r.toNNReal} = ∅ :=
        eq_empty_of_forall_notMem fun r hr => hno hr.2.1
      rw [this, measure_empty]
  have h : IsSLEPathUpTo a s.1 s.2 ρL ρR (fun _ => 0) (fun i _ => s.1 i) (fun j _ => s.2 j)
      (dec c) 0 :=
    { w_zero := rfl
      vL_zero := fun _ => rfl
      vR_zero := fun _ => rfl
      continuousOn_w := continuousOn_const
      continuousOn_vL := fun _ => continuousOn_const
      continuousOn_vR := fun _ => continuousOn_const
      antitone_vL := fun ht => absurd ht hno
      vL_le_w := fun ht => absurd ht hno
      w_le_vR := fun ht => absurd ht hno
      monotone_vR := fun ht => absurd ht hno
      integrable_gapL := fun ht => absurd ht hno
      integrable_gapR := fun ht => absurd ht hno
      w_eq := fun ht => absurd ht hno
      vL_eq := fun ht => absurd ht hno
      vR_eq := fun ht => absurd ht hno
      volume_collisionL := fun i => hnull (fun _ => 0) (fun _ => s.1 i)
      volume_collisionR := fun j => hnull (fun _ => 0) (fun _ => s.2 j)
      not_threshold := fun ht => absurd ht hno }
  have := mem_lSet_of_isSLEPathUpTo hs (continuous_dec_of_uc hc) h le_rfl
  rwa [enc_dec_of_uc hc] at this

open Classical in
variable (a ρL ρR) in
/-- **The maximal horizon** of the local solutions from `s` driven by `c`: the supremum of the
dyadic horizons that carry a local solution. -/
def lifeMax (s : MWord nL nR) (c : PCode) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (k : ℕ), if (s, c, (dyad n k : ℝ≥0∞)) ∈ LSet a ρL ρR then (dyad n k : ℝ≥0∞) else 0

theorem measurable_lifeMax :
    Measurable fun p : MWord nL nR × PCode => lifeMax a ρL ρR p.1 p.2 := by
  refine Measurable.iSup fun n => Measurable.iSup fun k => Measurable.ite ?_ measurable_const
    measurable_const
  exact measurableSet_lSet.preimage
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

variable (a ρL ρR) in
/-- **The maximal local solution** from `s` driven by `c`: the local solution code up to
`lifeMax s c`. -/
def maxCode (s : MWord nL nR) (c : PCode) : XCode nL nR :=
  lInv a ρL ρR (s, c, lifeMax a ρL ρR s c)

theorem measurable_maxCode :
    Measurable fun p : MWord nL nR × PCode => maxCode a ρL ρR p.1 p.2 :=
  measurable_lInv.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_lifeMax))

theorem mem_lSet_of_lt_lifeMax {s : MWord nL nR} {c : PCode} {q : ℝ≥0∞}
    (hq : q < lifeMax a ρL ρR s c) : (s, c, q) ∈ LSet a ρL ρR := by
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hq
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hn
  split_ifs at hk with hmem
  · exact mem_lSet_of_le hmem hk.le
  · exact absurd hk (not_lt.2 bot_le)

/-- **Every horizon that carries a local solution is at most the maximal horizon.** -/
theorem le_lifeMax {s : MWord nL nR} {c : PCode} {q : ℝ≥0∞} (hp : (s, c, q) ∈ LSet a ρL ρR) :
    q ≤ lifeMax a ρL ρR s c := by
  refine le_of_forall_lt fun r hr => ?_
  have hrfin : r ≠ ⊤ := (lt_of_lt_of_le hr le_top).ne
  have hr' : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < q := by rw [ENNReal.coe_toNNReal hrfin]; exact hr
  obtain ⟨n, k, hrd, hdq⟩ := exists_dyad_btwn hr'
  have hmem := mem_lSet_of_le hp hdq.le
  have hle : (dyad n k : ℝ≥0∞) ≤ lifeMax a ρL ρR s c := by
    classical
    unfold lifeMax
    refine le_iSup₂_of_le n k ?_
    simp only [hmem, ↓reduceIte, le_refl]
  calc r = ((r.toNNReal : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_toNNReal hrfin).symm
    _ < dyad n k := by exact_mod_cast hrd
    _ ≤ lifeMax a ρL ρR s c := hle

/-! ### Gluing local solutions -/

/-- **A path that is a local solution before every smaller positive horizon is a local
solution.** -/
theorem isSLEPathUpTo_of_forall_lt {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞} (hτ : 0 < τ)
    (h : ∀ q : ℝ≥0∞, 0 < q → q < τ → IsSLEPathUpTo a xL xR ρL ρR w vL vR b q) :
    IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ := by
  have hloc : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      ∃ q : ℝ≥0∞, (t : ℝ≥0∞) < q ∧ IsSLEPathUpTo a xL xR ρL ρR w vL vR b q := fun {t} ht => by
    obtain ⟨q, h1, h2⟩ := exists_between ht
    exact ⟨q, h1, h (q) (lt_of_le_of_lt bot_le h1) h2⟩
  obtain ⟨q₀, hq₀, hq₀τ⟩ := exists_between hτ
  have h₀ := h q₀ hq₀ hq₀τ
  have hopen : ∀ q : ℝ≥0∞, IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < q} := fun q =>
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ∀ {f : ℝ≥0 → ℝ},
      (∀ q : ℝ≥0∞, IsSLEPathUpTo a xL xR ρL ρR w vL vR b q → ContinuousOn f {t | (t : ℝ≥0∞) < q}) →
      ContinuousOn f {t | (t : ℝ≥0∞) < τ} := fun {f} hf t ht => by
    obtain ⟨q, htq, hq⟩ := hloc ht
    exact ((hf q hq).continuousAt ((hopen q).mem_nhds htq)).continuousWithinAt
  have hcoll : ∀ (f g : ℝ≥0 → ℝ), (∀ q : ℝ≥0∞, 0 < q → q < τ →
      volume {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < q ∧ f r.toNNReal = g r.toNNReal} = 0) →
      volume {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < τ ∧ f r.toNNReal = g r.toNNReal} = 0 := by
    intro f g hfg
    have hsub : {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < τ ∧ f r.toNNReal = g r.toNNReal} ⊆
        ⋃ (n : ℕ) (k : ℕ), {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < dyad n k ∧
          (dyad n k : ℝ≥0∞) < τ ∧ f r.toNNReal = g r.toNNReal} := by
      rintro r ⟨h1, h2, h3⟩
      obtain ⟨n, k, hrd, hdτ⟩ := exists_dyad_btwn h2
      exact mem_iUnion₂.2 ⟨n, k, h1, by exact_mod_cast hrd, hdτ, h3⟩
    refine measure_mono_null hsub (measure_iUnion_null fun n => measure_iUnion_null fun k => ?_)
    by_cases hd : (dyad n k : ℝ≥0∞) < τ ∧ 0 < (dyad n k : ℝ≥0∞)
    · refine measure_mono_null ?_ (hfg _ hd.2 hd.1)
      rintro r ⟨h1, h2, -, h4⟩
      exact ⟨h1, h2, h4⟩
    · have : {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < dyad n k ∧
          (dyad n k : ℝ≥0∞) < τ ∧ f r.toNNReal = g r.toNNReal} = ∅ :=
        eq_empty_of_forall_notMem fun r ⟨_, h2, h3, _⟩ =>
          hd ⟨h3, lt_of_le_of_lt bot_le h2⟩
      rw [this, measure_empty]
  exact
    { w_zero := h₀.w_zero
      vL_zero := h₀.vL_zero
      vR_zero := h₀.vR_zero
      continuousOn_w := hcont fun q hq => hq.continuousOn_w
      continuousOn_vL := fun i => hcont fun q hq => hq.continuousOn_vL i
      continuousOn_vR := fun j => hcont fun q hq => hq.continuousOn_vR j
      antitone_vL := fun ht => (hloc ht).elim fun _ hq => hq.2.antitone_vL hq.1
      vL_le_w := fun ht => (hloc ht).elim fun _ hq => hq.2.vL_le_w hq.1
      w_le_vR := fun ht => (hloc ht).elim fun _ hq => hq.2.w_le_vR hq.1
      monotone_vR := fun ht => (hloc ht).elim fun _ hq => hq.2.monotone_vR hq.1
      integrable_gapL := fun ht => (hloc ht).elim fun _ hq => hq.2.integrable_gapL hq.1
      integrable_gapR := fun ht => (hloc ht).elim fun _ hq => hq.2.integrable_gapR hq.1
      w_eq := fun ht => (hloc ht).elim fun _ hq => hq.2.w_eq hq.1
      vL_eq := fun ht => (hloc ht).elim fun _ hq => hq.2.vL_eq hq.1
      vR_eq := fun ht => (hloc ht).elim fun _ hq => hq.2.vR_eq hq.1
      volume_collisionL := fun i => hcoll _ _ fun q h1 h2 => (h q h1 h2).volume_collisionL i
      volume_collisionR := fun j => hcoll _ _ fun q h1 h2 => (h q h1 h2).volume_collisionR j
      not_threshold := fun ht => (hloc ht).elim fun _ hq => hq.2.not_threshold hq.1 }

/-- **The maximal horizon is attained**: the local solutions up to the smaller horizons agree
(local pathwise uniqueness) and glue to a local solution up to `lifeMax s c`. -/
theorem mem_lSet_lifeMax {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c : PCode}
    (hc : ∀ T : ℕ, UC c T) : (s, c, lifeMax a ρL ρR s c) ∈ LSet a ρL ρR := by
  set ℓ := lifeMax a ρL ρR s c with hℓ
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ ℓ) with h0 | h0
  · rw [← h0]; exact mem_lSet_zero hs hc
  set hor : ℝ≥0 → ℝ≥0∞ := fun t =>
    if ht : (t : ℝ≥0∞) < ℓ then Classical.choose (exists_between ht) else 0 with hhor
  have hhor_spec : ∀ {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ℓ), (t : ℝ≥0∞) < hor t ∧ hor t < ℓ :=
    fun {t} ht => by
      simp only [hhor, ht, ↓reduceDIte]
      exact Classical.choose_spec (exists_between ht)
  set U : ℝ≥0 → ℝ := fun t => cw (lInv a ρL ρR (s, c, hor t)) t with hU
  set UL : Fin nL → ℝ≥0 → ℝ := fun i t => cvL (lInv a ρL ρR (s, c, hor t)) i t with hUL
  set UR : Fin nR → ℝ≥0 → ℝ := fun j t => cvR (lInv a ρL ρR (s, c, hor t)) j t with hUR
  have hpath : ∀ q : ℝ≥0∞, q < ℓ → IsSLEPathUpTo a s.1 s.2 ρL ρR (cw (lInv a ρL ρR (s, c, q)))
      (cvL (lInv a ρL ρR (s, c, q))) (cvR (lInv a ρL ρR (s, c, q))) (dec c) q :=
    fun q hq => isSLEPathUpTo_lInv (mem_lSet_of_lt_lifeMax hq)
  have hagree : ∀ q : ℝ≥0∞, q < ℓ → ∀ t : ℝ≥0, (t : ℝ≥0∞) < q →
      UpTo.Agree (cw (lInv a ρL ρR (s, c, q))) (cvL (lInv a ρL ρR (s, c, q)))
        (cvR (lInv a ρL ρR (s, c, q))) U UL UR t := fun q hq t htq => by
    have htℓ : (t : ℝ≥0∞) < ℓ := htq.trans hq
    have h1 := hpath q hq
    have h2 := hpath (hor t) (hhor_spec htℓ).2
    exact UpTo.agree_of_lt_min hs h1 h1.driverEq h2 h2.driverEq (lt_min htq (hhor_spec htℓ).1)
  have hglue : IsSLEPathUpTo a s.1 s.2 ρL ρR U UL UR (dec c) ℓ := by
    refine isSLEPathUpTo_of_forall_lt h0 fun q hq0 hqℓ => ?_
    have hq0' : ((0 : ℝ≥0) : ℝ≥0∞) < q := by rw [ENNReal.coe_zero]; exact hq0
    refine isSLEPathUpTo_congr (hpath q hqℓ) (hagree q hqℓ 0 hq0').1.symm
      (fun i => ((hagree q hqℓ 0 hq0').2.1 i).symm) (fun j => ((hagree q hqℓ 0 hq0').2.2 j).symm)
      (fun t ht => (hagree q hqℓ t ht).1.symm) (fun t ht i => ((hagree q hqℓ t ht).2.1 i).symm)
      (fun t ht j => ((hagree q hqℓ t ht).2.2 j).symm) fun _ _ => rfl
  have := mem_lSet_of_isSLEPathUpTo hs (continuous_dec_of_uc hc) hglue le_rfl
  rwa [enc_dec_of_uc hc] at this

/-- The maximal local solution decodes to a local solution up to the maximal horizon. -/
theorem isSLEPathUpTo_maxCode {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c : PCode}
    (hc : ∀ T : ℕ, UC c T) :
    IsSLEPathUpTo a s.1 s.2 ρL ρR (cw (maxCode a ρL ρR s c)) (cvL (maxCode a ρL ρR s c))
      (cvR (maxCode a ρL ρR s c)) (dec c) (lifeMax a ρL ρR s c) :=
  isSLEPathUpTo_lInv (mem_lSet_lifeMax hs hc)

theorem maxCode_mem {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c : PCode}
    (hc : ∀ T : ℕ, UC c T) :
    maxCode a ρL ρR s c ∈ LRel a ρL ρR ∧
      lProj (maxCode a ρL ρR s c) = (s, c, lifeMax a ρL ρR s c) :=
  lInv_mem (mem_lSet_lifeMax hs hc)

/-! ### The maximal solution only sees the past of the driving path -/

/-- **The maximal horizon and the maximal solution only see the driving path up to any time `r`
after the maximal horizon.** -/
theorem lifeMax_eq_of_eqOn {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c c' : PCode}
    (hc : ∀ T : ℕ, UC c T) (hc' : ∀ T : ℕ, UC c' T) {r : ℝ≥0}
    (heq : ∀ t : ℝ≥0, t ≤ r → dec c' t = dec c t) (hlt : lifeMax a ρL ρR s c < r) :
    lifeMax a ρL ρR s c' = lifeMax a ρL ρR s c ∧
      (maxCode a ρL ρR s c').2 = (maxCode a ρL ρR s c).2 := by
  set ℓ := lifeMax a ρL ρR s c with hℓdef
  have hℓ := mem_lSet_lifeMax (a := a) (ρL := ρL) (ρR := ρR) hs hc
  have hlt' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ℓ → dec c' t = dec c t := fun t ht =>
    heq t (by exact_mod_cast (ht.trans hlt).le)
  obtain ⟨hℓ', hcode⟩ := lInv_setB hℓ hc' hlt'
  have hge : ℓ ≤ lifeMax a ρL ρR s c' := le_lifeMax hℓ'
  have hle : lifeMax a ρL ρR s c' ≤ ℓ := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨q, hq1, hq2⟩ := exists_between (lt_min hcon hlt)
    have hq' := mem_lSet_of_lt_lifeMax (hq2.trans_le (min_le_left _ _))
    have hqr : q ≤ (r : ℝ≥0∞) := (hq2.trans_le (min_le_right _ _)).le
    have := (lInv_setB hq' hc fun t ht =>
      (heq t (by exact_mod_cast (ht.trans_le hqr).le)).symm).1
    exact absurd (le_lifeMax this) (not_le.2 hq1)
  have he : lifeMax a ρL ρR s c' = ℓ := le_antisymm hle hge
  refine ⟨he, ?_⟩
  show (lInv a ρL ρR (s, c', lifeMax a ρL ρR s c')).2 = (lInv a ρL ρR (s, c, ℓ)).2
  rw [he]
  exact hcode

/-- The maximal solution agrees with every local solution before its horizon. -/
theorem stateAt_maxCode_eq {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c : PCode}
    (hc : ∀ T : ℕ, UC c T) {q : ℝ≥0∞} (hq : (s, c, q) ∈ LSet a ρL ρR) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < q) :
    stateAt (maxCode a ρL ρR s c) t = stateAt (lInv a ρL ρR (s, c, q)) t := by
  have h1 := isSLEPathUpTo_maxCode (a := a) (ρL := ρL) (ρR := ρR) hs hc
  have h2 := isSLEPathUpTo_lInv hq
  obtain ⟨e1, e2, e3⟩ := UpTo.agree_of_lt_min hs h1 h1.driverEq h2 h2.driverEq
    (lt_min (ht.trans_le (le_lifeMax hq)) ht)
  simp only [stateAt, e1, funext e2, funext e3]

/-- One direction of `lifeMax_lt_iff_of_eqOn`. -/
theorem lt_lifeMax_of_eqOn {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c c' : PCode}
    (hc : ∀ T : ℕ, UC c T) (hc' : ∀ T : ℕ, UC c' T) {r : ℝ≥0}
    (heq : ∀ t : ℝ≥0, t ≤ r → dec c' t = dec c t) {t : ℝ≥0} (htr : t < r)
    (ht : (t : ℝ≥0∞) < lifeMax a ρL ρR s c) :
    (t : ℝ≥0∞) < lifeMax a ρL ρR s c' ∧
      stateAt (maxCode a ρL ρR s c') t = stateAt (maxCode a ρL ρR s c) t := by
  by_cases hlt : lifeMax a ρL ρR s c < r
  · obtain ⟨e1, e2⟩ := lifeMax_eq_of_eqOn hs hc hc' heq hlt
    refine ⟨by rw [e1]; exact ht, ?_⟩
    unfold stateAt cw cvL cvR
    rw [e2]
  · rw [not_lt] at hlt
    have hr := mem_lSet_of_le (mem_lSet_lifeMax (a := a) (ρL := ρL) (ρR := ρR) hs hc) hlt
    have htr' : (t : ℝ≥0∞) < r := by exact_mod_cast htr
    obtain ⟨hr', hcode⟩ := lInv_setB hr hc' fun t' ht' =>
      heq t' (by exact_mod_cast (ht'.le))
    refine ⟨htr'.trans_le (le_lifeMax hr'), ?_⟩
    rw [stateAt_maxCode_eq hs hc' hr' htr', stateAt_maxCode_eq hs hc hr htr']
    unfold stateAt cw cvL cvR
    rw [hcode]

/-- **Locality at a time**: if `c, c'` decode to paths that agree up to `r > t`, then `t` is before
the maximal horizon for both or for neither, and then the maximal solutions agree at `t`. -/
theorem lt_lifeMax_iff_of_eqOn {s : MWord nL nR} (hs : ∀ i j, s.1 i < s.2 j) {c c' : PCode}
    (hc : ∀ T : ℕ, UC c T) (hc' : ∀ T : ℕ, UC c' T) {r : ℝ≥0}
    (heq : ∀ t : ℝ≥0, t ≤ r → dec c' t = dec c t) {t : ℝ≥0} (htr : t < r) :
    ((t : ℝ≥0∞) < lifeMax a ρL ρR s c' ↔ (t : ℝ≥0∞) < lifeMax a ρL ρR s c) ∧
      ((t : ℝ≥0∞) < lifeMax a ρL ρR s c →
        stateAt (maxCode a ρL ρR s c') t = stateAt (maxCode a ρL ρR s c) t) :=
  ⟨⟨fun h => (lt_lifeMax_of_eqOn hs hc' hc (fun t' ht' => (heq t' ht').symm) htr h).1,
    fun h => (lt_lifeMax_of_eqOn hs hc hc' heq htr h).1⟩,
    fun h => (lt_lifeMax_of_eqOn hs hc hc' heq htr h).2⟩

end Assembly2

end Sec2

end InteractingSLE
