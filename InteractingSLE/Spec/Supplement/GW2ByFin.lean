/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxAvoid

/-!
# D75's bad sets are avoided from a time past the uncapped exit (one sample)

Packet PROVE-GW2-BUF (round 22; D83). Round 21's `avoid_atS` finishes with a time `t₁` after the history, before the
uncapped contact and the uncapped life, with `e + S < clock t₁ ≤ d_u` (its internal `hfinish`). That step reads only
`Wc`'s continuity, `Wc 0 = 0` and its hull identity below the death clock, not the trace or clock clauses of
`GW2Ni.IsCanonUX`. Here it is a lemma of its own, so the death-first case of the stopped uncapped law
(`GW2Ni.IsCanonUXS`) can use it.

* **`avoid_ofT`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh
  GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

/-- **The bad sets are avoided at one sample** from a time `t₁` past the uncapped exit. -/
theorem avoid_ofT {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (ξ : Ω)
    (n i : ℕ)
    (hα : IsGeneratingTrace (c.W · ξ) ⊤ (c.α ξ)) (hW : Continuous (c.W · ξ)) (hW0 : c.W 0 ξ = 0) (hζ : c.ζ ξ = ⊤)
    (harc : ∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ξ u‖ < 1)
    (huc : Continuous (GW2Ni.uncW c r l i · ξ)) (hu0 : GW2Ni.uncW c r l i 0 ξ = 0)
    (huγ : IsGeneratingTrace (GW2Ni.uncW c r l i · ξ) ⊤ (GW2Ni.uncTr c r l i ξ))
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ) < GW2Ni.uncDeathX c r l i ξ →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ)
    (hUA : ∀ a : ℕ, RootJ31.candidateAngle c r a = RootJ31.angleEnumeration c r i →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a,
        schedW c r l a t ξ = GW2Ni.uncW c r l i t ξ ∧ schedTr c r l a ξ t = GW2Ni.uncTr c r l i ξ t)
    (hGT : ∀ a, ξ ∈ schedGTX h13 c r l a) (hcov : ξ ∈ RootCv.coverEvent c r) (hold : RootJ31.oldSuccess c r l ξ)
    (hTc : ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (href : ∀ a j : ℕ,
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (ver₀ Ω c r l a).V j ξ →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l)
          ((ver₀ Ω c r l a).R j) ξ = GW2Rl.refPreV h13 ver₀ Ω c r l ξ)
    (hver : ∀ a j, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver₀ Ω c r l a).V j ξ →
      fwdHull (fun q : ℝ => (ver₀ Ω c r l a).R j q.toNNReal ξ)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (hexh : ∀ a : ℕ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      t < RootJ31.historyTime c r l + RootJ31.candidateCap c r a →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ →
      ∀ᶠ k in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < (ver₀ Ω c r l a).V k ξ)
    {t₁ : ℝ≥0} (hTt₁ : RootJ31.historyTime c r l < t₁)
    (ht₁c : (t₁ : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ)
    (het₁ : exitN c r l n (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ,
        stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal) +
      ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) <
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t₁ ξ))
    (ht₁d : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t₁ ξ) ≤ GW2Ni.uncDeathX c r l i ξ)
    (hlife : ((t₁ - RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < GW2Ni.uncLife c r l i ξ) :
    ∃ Q : ℝ≥0, ∀ q : ℕ, Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
      ∀ᶠ b in atTop, ξ ∉ ZbS h13 ver₀ ch c r l n i q b := by
  classical
  set T := RootJ31.historyTime c r l with hT
  set x₀ := rootPt r.1 with hx₀
  set clu : ℝ≥0 → ℝ := fun t => clockX x₀ c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ with hclu
  set S : ℝ≥0 := (clu T).toNNReal with hS
  set y := augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ with hy
  set e := exitN c r l n (y, stgDrv Wc S) with he
  set L := GW2Bh.contactLifeX x₀ c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ) (GW2Ni.uncTr c r l i ξ) (c.α ξ)
    with hL
  set Tcu := contactX x₀ c.s (GW2Ni.uncTr c r l i) c.α ξ with hTcu
  set du := GW2Ni.uncDeathX c r l i ξ with hdu
  obtain ⟨ha0, hsm, hac⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hs hx harc huc hu0 huγ
  have hUc : Continuous (GW2Ni.uncTr c r l i ξ) := GW2Cone.continuous_of_isGeneratingTrace_top huγ
  have hE : IsPathRule (exitN c r l n) := (exitB_spec Ω c r l n 0).1
  -- the candidates of the angle
  have hang : ∀ q b : ℕ, RootJ31.candidateAngle c r (Nat.pair i (Nat.pair q b)) = RootJ31.angleEnumeration c r i :=
    fun q b => GW2Sdy.candidateAngle_pair c r i _
  have hcapq : ∀ q b : ℕ, RootJ31.candidateCap c r (Nat.pair i (Nat.pair q b)) =
      (RootJ31.timeEnumeration c r q : ℝ≥0) := fun q b => by
    simp only [RootJ31.candidateCap, Nat.unpair_pair]
  have hT0 : ∀ q : ℕ, T < T + (RootJ31.timeEnumeration c r q : ℝ≥0) := fun q =>
    lt_add_of_pos_right T (c.hQpos _ (RootJ31.timeEnumeration c r q).2)
  have hgr : GoodRoot c r := ⟨hx, hs⟩
  have hTcu : (T : ℝ≥0∞) < Tcu := by
    have h := hUA (Nat.pair i (Nat.pair 0 0)) (hang 0 0)
    rw [hcapq] at h
    exact lt_contactX_of_agree (fun u hu => (h u hu).2) (hT0 0) (hTc _)
  -- the facts at one good slot: the slot's exit is below its cap, and the exit term is version `m`'s exit
  have hslot : ∀ q b m : ℕ, ξ ∈ slotGoodS h13 ver₀ ch c r l n m (Nat.pair i (Nat.pair q b)) →
      exitN c r l n (y, stgDrv (fun u => (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).R
          (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1)) u ξ) S) +
          (S : ℝ≥0∞) < (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V
            (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1)) ξ ∧
        (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V
            (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1)) ξ ≤
          (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V
            (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) m) ξ ∧
        (exitN c r l n (y, stgDrv (fun u => (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).R
            (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) m) u ξ) S) + (S : ℝ≥0∞) <
            (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V
              (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) m) ξ →
          exitTermS h13 ver₀ ch c r l hx n m (Nat.pair i (Nat.pair q b)) ξ =
            exitN c r l n (y, stgDrv (fun u => (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).R
              (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) m) u ξ) S)) := by
    intro q b m hm
    have hg' : slotGoodS h13 ver₀ ch c r l n m (Nat.pair i (Nat.pair q b)) = goodVer h13 ver₀
        ch c r l hx (exitN c r l) n (Nat.pair i (Nat.pair q b))
        (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1)) := by
      simp only [slotGoodS, hgr, ↓reduceDIte]
    rw [hg'] at hm
    obtain ⟨h1, h2, h3⟩ := exitTermS_eq_of_good h13 ver₀ ch c r l hx hs ξ n m _ hm (hTc _) (hGT _) (href _)
    have hclk : clockX x₀ c.s c.W c.ζ (schedW c r l (Nat.pair i (Nat.pair q b))) T ξ = clu T :=
      clockX_eq_of_agree fun u hu => ((hUA _ (hang q b)) u (hu.trans (by rw [hcapq]; exact (hT0 q).le))).1
    have hSa : (clockX x₀ c.s c.W c.ζ (schedW c r l (Nat.pair i (Nat.pair q b))) T ξ).toNNReal = S := by
      rw [hclk]
    rw [hSa] at h1 h3
    exact ⟨h1, h2, h3⟩
  -- the agreement of a slot's version with `Wc` below an uncapped clock value
  have hagree : ∀ q b j : ℕ, ∀ t₂ : ℝ≥0, t₂ < T + (RootJ31.timeEnumeration c r q : ℝ≥0) → (t₂ : ℝ≥0∞) < Tcu →
      ENNReal.ofReal (clu t₂) ≤ du → ∀ u : ℝ≥0,
      (u : ℝ≥0∞) < min ((ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V j ξ)
        (ENNReal.ofReal (clu t₂)) →
      (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).R j u ξ = Wc u := by
    intro q b j t₂ ht₂ ht₂c ht₂d
    have hA := (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).isA hx j
    obtain ⟨⟨hwc₁, hw0₁, hγ₁⟩, -, -, -, -⟩ := (schedGTX_spec h13 c r l (Nat.pair i (Nat.pair q b))).1 ξ (hGT _)
    have hUA' := hUA _ (hang q b)
    rw [hcapq] at hUA'
    exact agree_below_clock c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁ huc hu0 huγ
      (fun u hu => (hUA' u hu).1) (fun u hu => (hUA' u hu).2) (hA.1.1.2.1 ξ) (hA.1.1.2.2.1 ξ) (hver _ j)
      hWc hWc0 hK ht₂ ht₂c ht₂d
  -- a good slot whose versions agree with `Wc` below `min (V, B)` has exit term `e`
  have hkey : ∀ q b m : ℕ, ∀ B : ℝ≥0∞, ξ ∈ slotGoodS h13 ver₀ ch c r l n m (Nat.pair i (Nat.pair q b)) →
      (∀ j : ℕ, ∀ u : ℝ≥0, (u : ℝ≥0∞) < min ((ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V j ξ) B →
        (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).R j u ξ = Wc u) →
      (e + S < B ∨ (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b))
          m) ξ ≤ B) →
      exitTermS h13 ver₀ ch c r l hx n m (Nat.pair i (Nat.pair q b)) ξ = e ∧
        e + S < (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q b)) (m -
        1)) ξ := by
    intro q b m B hm hagB hB
    obtain ⟨h1, hVV, h3⟩ := hslot q b m hm
    have hexJ : exitN c r l n (y, stgDrv (fun u => (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).R (JS h13 ver₀ ch Ω c r
        l (Nat.pair i (Nat.pair q b)) (m - 1)) u ξ) S) = e := by
      rcases hB with hB | hB
      · exact exit_eq_of_agree_below hE y (hagB _) h1 hB
      · exact exit_eq_of_agree_cap hE y (fun u hu => hagB _ u (lt_min hu (hu.trans_le (hVV.trans hB)))) h1
    have heS : e + S < (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V (JS h13 ver₀ ch Ω c r l (Nat.pair i (Nat.pair q
        b)) (m - 1)) ξ := by
      rw [← hexJ]
      exact h1
    have hmin : e + S < min ((ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).V (JS h13 ver₀ ch Ω c r l (Nat.pair i
        (Nat.pair q b)) m) ξ) B := by
      rcases hB with hB | hB
      · exact lt_min (heS.trans_le hVV) hB
      · exact lt_min (heS.trans_le hVV) ((heS.trans_le hVV).trans_le hB)
    have hexJ' : exitN c r l n (y, stgDrv (fun u => (ver₀ Ω c r l (Nat.pair i (Nat.pair q b))).R (JS h13 ver₀ ch Ω c
        r l (Nat.pair i (Nat.pair q b)) m) u ξ) S) = e :=
      pathRule_stgDrv_eq hE y (fun u hu => hagB _ u hu) hmin
    refine ⟨(h3 ?_).trans hexJ', heS⟩
    rw [hexJ']
    exact heS.trans_le hVV
  -- membership in the bad set
  have hZ : ∀ q b, ξ ∈ ZbS h13 ver₀ ch c r l n i q b → (∃ m, ξ ∈ slotGoodS h13 ver₀ ch c r l n m
      (Nat.pair i (Nat.pair q b)) ∧ (GW2Sdg.rootGain c r l (Nat.pair i (Nat.pair q b)) ξ : ℝ≥0∞) <
        exitTermS h13 ver₀ ch c r l hx n m (Nat.pair i (Nat.pair q b)) ξ) ∨
      ¬ ∃ K, ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n (Nat.pair i (Nat.pair q b)) K := fun q b h => by
    rw [ZbS_eq h13 ver₀ ch c r l hgr] at h
    simpa only [mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq] using h
  have hclT0 : 0 ≤ clu T := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with h | h
    · rw [hclu, ← h]; exact ha0.ge
    · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < Tcu := lt_of_le_of_lt (by exact_mod_cast zero_le) hTcu
      exact le_of_lt (lt_of_eq_of_lt ha0.symm (hsm h0 hTcu h))
  have hSr : (S : ℝ) = clu T := Real.coe_toNNReal _ hclT0
  -- a time `t₁ > T` before the contact with `e + S < clock t₁`, the death after it, gives the bound
  have hfinish : ∀ t₁ : ℝ≥0, T < t₁ → (t₁ : ℝ≥0∞) < Tcu → e + S < ENNReal.ofReal (clu t₁) →
      ENNReal.ofReal (clu t₁) ≤ du → ((t₁ - T : ℝ≥0) : ℝ≥0∞) < GW2Ni.uncLife c r l i ξ →
      ∃ Q : ℝ≥0, ∀ q : ℕ, Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
        ∀ᶠ b in atTop, ξ ∉ ZbS h13 ver₀ ch c r l n i q b := by
    intro t₁ hTt₁ ht₁c het₁ ht₁d hlife
    have hT₁ : T + (t₁ - T) = t₁ := add_tsub_cancel_of_le hTt₁.le
    obtain ⟨Q₂, hQ₂⟩ := GW2Ni.exists_capBuf_of_unc h13 c r l i hx (fun k => hGT _) hcov hold hUA hUc hlife
      (by rw [hT₁]; exact ht₁c) (by rw [hT₁]; exact het₁)
    refine ⟨max Q₂ (t₁ - T + 1), fun q hq => ?_⟩
    filter_upwards [hQ₂ q ((le_max_left _ _).trans hq)] with b hb hmem
    have hcap₁ : t₁ < T + (RootJ31.timeEnumeration c r q : ℝ≥0) := by
      have h3 : t₁ - T + 1 ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) := (le_max_right _ _).trans hq
      calc t₁ = T + (t₁ - T) := hT₁.symm
        _ < T + (t₁ - T + 1) := by simp
        _ ≤ _ := add_le_add (le_refl T) h3
    rcases hZ q b hmem with ⟨m, hm, hlt⟩ | hng
    · obtain ⟨h1, -⟩ := hkey q b m _ hm (fun j => hagree q b j t₁ hcap₁ ht₁c ht₁d) (Or.inl het₁)
      rw [h1] at hlt
      exact absurd hlt (not_lt.2 hb.le)
    · exact hng (goodFrom_of_unc h13 ver₀ ch c r l hx hs ξ n i hα hW hW0 hζ harc huc hu0 huγ hWc hWc0 hK
        (Nat.pair i (Nat.pair q b)) (hang q b) (hUA _ (hang q b)) (hGT _) (hTc _) (href _) (hver _) (hexh _)
        hTt₁ ht₁c (by rw [hcapq]; exact hcap₁) het₁ ht₁d hlife)
  exact hfinish t₁ hTt₁ ht₁c het₁ ht₁d hlife

end InteractingSLE.Theorem14.GW2Bh
