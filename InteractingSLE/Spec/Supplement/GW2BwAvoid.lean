/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BwAgree

/-!
# The bad sets are avoided for large caps and large buffers (one sample)

Packet PROVE-GW2-BUF (round 20; `hsrc`). At one alive sample, for a level `n` and an angle index `i`, let `Wc` be a
canonical driver of the uncapped curve (`GW2Ni.IsCanonUX`) and `e` the near cell's exit on its stage path. Every good
slot of every candidate `Nat.pair i (Nat.pair q b)` with a large cap has its exit term equal to `e`, and the gain
eventually exceeds `e` in the buffer (`GW2Ni.exists_capBuf_of_unc`). So `Zb n i q b` is avoided.

* **Contact first** (`L_u ≤ d_u`): `e` is before the uncapped life (`ae_uncExit_lt_life`). Below an uncapped clock
  value past `e`, every version agrees with `Wc` (`agree_below_clock`, from the versions' hull identities); then
  `exit_eq_of_agree_below` on the good slot `J` and `pathRule_stgDrv_eq` on version `m`'s slot `J' ≥ J`.
* **Death first** (`d_u < L_u`, so the piece dies at `T + ζ` before the contact): for a cap past `ζ`, every version's
  cap is below the candidate's death clock `= d_u`. The versions agree with `Wc` below their caps; then
  `exit_eq_of_agree_cap`. So a good slot forces `e + S < d_u`.

No stage law of the capped candidates is used: the versions are compared with `Wc` through their hull identities.

* **`avoid_at`**.
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

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u})

/-- **The bad sets are avoided at one sample** for large caps and large buffers. -/
theorem avoid_at {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (ξ : Ω)
    (n i : ℕ)
    (hα : IsGeneratingTrace (c.W · ξ) ⊤ (c.α ξ)) (hW : Continuous (c.W · ξ)) (hW0 : c.W 0 ξ = 0) (hζ : c.ζ ξ = ⊤)
    (harc : ∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ξ u‖ < 1)
    (huc : Continuous (GW2Ni.uncW c r l i · ξ)) (hu0 : GW2Ni.uncW c r l i 0 ξ = 0)
    (huγ : IsGeneratingTrace (GW2Ni.uncW c r l i · ξ) ⊤ (GW2Ni.uncTr c r l i ξ))
    {Wc : ℝ≥0 → ℝ} (hcanU : GW2Ni.IsCanonUX c r l i ξ Wc)
    (hUA : ∀ a : ℕ, RootJ31.candidateAngle c r a = RootJ31.angleEnumeration c r i →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a,
        schedW c r l a t ξ = GW2Ni.uncW c r l i t ξ ∧ schedTr c r l a ξ t = GW2Ni.uncTr c r l i ξ t)
    (hGT : ∀ a, ξ ∈ schedGTX h13 c r l a) (hcov : ξ ∈ RootCv.coverEvent c r) (hold : RootJ31.oldSuccess c r l ξ)
    (hTc : ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (href : ∀ a j : ℕ,
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (schedVerXDeathFamily h13 Ω c r l a).V j ξ →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((schedVerXDeathFamily h13 Ω c r l a).V j) (RootJ31.historyTime c r l)
          ((schedVerXDeathFamily h13 Ω c r l a).R j) ξ = refPre h13 Ω c r l ξ)
    (hver : ∀ a j, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (schedVerXDeathFamily h13 Ω c r l a).V j ξ
      →
      fwdHull (fun q : ℝ => (schedVerXDeathFamily h13 Ω c r l a).R j q.toNNReal ξ)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (hdc : ∀ a j, (schedVerXDeathFamily h13 Ω c r l a).V j ξ < deathClockX c r l a ξ)
    (hexitA : ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ)
        (GW2Ni.uncTr c r l i ξ) (c.α ξ)) ≤ GW2Ni.uncDeathX c r l i ξ →
      exitN c r l n (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ,
          stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal) +
        ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) <
        ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ)
          (GW2Ni.uncTr c r l i ξ) (c.α ξ))) :
    ∃ Q : ℝ≥0, ∀ q : ℕ, Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
      ∀ᶠ b in atTop, ξ ∉ Zb h13 h12 c r l n i q b := by
  classical
  set T := RootJ31.historyTime c r l with hT
  set x₀ := rootPt r.1 with hx₀
  set clu : ℝ≥0 → ℝ := fun t => clockX x₀ c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ with hclu
  set S : ℝ≥0 := (clu T).toNNReal with hS
  set y := augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ with hy
  set e := exitN c r l n (y, stgDrv Wc S) with he
  set L := GW2Bh.contactLifeX x₀ c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ) (GW2Ni.uncTr c r l i ξ) (c.α ξ)
    with hL
  set Tcu := contactX x₀ c.s (GW2Ni.uncTr c r l i) c.α ξ with hTcu
  set du := GW2Ni.uncDeathX c r l i ξ with hdu
  obtain ⟨hWc, hWc0, hK, -, M, hM⟩ := hcanU
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
  have hslot : ∀ q b m : ℕ, ξ ∈ slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) →
      exitN c r l n (y, stgDrv (fun u => (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).R
          (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1) + (m - 1)) u ξ) S) +
          (S : ℝ≥0∞) < (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V
            (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1) + (m - 1)) ξ ∧
        (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V
            (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1) + (m - 1)) ξ ≤
          (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V
            (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) m + m) ξ ∧
        (exitN c r l n (y, stgDrv (fun u => (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).R
            (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) m + m) u ξ) S) + (S : ℝ≥0∞) <
            (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V
              (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) m + m) ξ →
          exitTerm h13 h12 c r l hx n m (Nat.pair i (Nat.pair q b)) ξ =
            exitN c r l n (y, stgDrv (fun u => (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).R
              (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) m + m) u ξ) S)) := by
    intro q b m hm
    have hg' : slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) = goodVer h13 (schedVerXDeathFamily h13)
        (pkgCh h13 h12 cwSrc) c r l hx (exitN c r l) n (Nat.pair i (Nat.pair q b))
        (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1) + (m - 1)) := by
      simp only [slotGood, hgr, ↓reduceDIte]
    rw [hg'] at hm
    obtain ⟨h1, h2, h3⟩ := exitTerm_eq_of_good h13 h12 c r l hx hs ξ n m _ hm (hTc _) (hGT _) (href _)
    have hclk : clockX x₀ c.s c.W c.ζ (schedW c r l (Nat.pair i (Nat.pair q b))) T ξ = clu T :=
      clockX_eq_of_agree fun u hu => ((hUA _ (hang q b)) u (hu.trans (by rw [hcapq]; exact (hT0 q).le))).1
    have hSa : (clockX x₀ c.s c.W c.ζ (schedW c r l (Nat.pair i (Nat.pair q b))) T ξ).toNNReal = S := by
      rw [hclk]
    rw [hSa] at h1 h3
    exact ⟨h1, h2, h3⟩
  -- the agreement of a slot's version with `Wc` below an uncapped clock value
  have hagree : ∀ q b j : ℕ, ∀ t₂ : ℝ≥0, t₂ < T + (RootJ31.timeEnumeration c r q : ℝ≥0) → (t₂ : ℝ≥0∞) < Tcu →
      ENNReal.ofReal (clu t₂) ≤ du → ∀ u : ℝ≥0,
      (u : ℝ≥0∞) < min ((schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V j ξ)
        (ENNReal.ofReal (clu t₂)) →
      (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).R j u ξ = Wc u := by
    intro q b j t₂ ht₂ ht₂c ht₂d
    have hA := (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).isA hx j
    obtain ⟨⟨hwc₁, hw0₁, hγ₁⟩, -, -, -, -⟩ := (schedGTX_spec h13 c r l (Nat.pair i (Nat.pair q b))).1 ξ (hGT _)
    have hUA' := hUA _ (hang q b)
    rw [hcapq] at hUA'
    exact agree_below_clock c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁ huc hu0 huγ
      (fun u hu => (hUA' u hu).1) (fun u hu => (hUA' u hu).2) (hA.1.1.2.1 ξ) (hA.1.1.2.2.1 ξ) (hver _ j)
      hWc hWc0 hK ht₂ ht₂c ht₂d
  -- a good slot whose versions agree with `Wc` below `min (V, B)` has exit term `e`
  have hkey : ∀ q b m : ℕ, ∀ B : ℝ≥0∞, ξ ∈ slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) →
      (∀ j : ℕ, ∀ u : ℝ≥0, (u : ℝ≥0∞) < min ((schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V j ξ) B →
        (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).R j u ξ = Wc u) →
      (e + S < B ∨ (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V (pkgPsi h13 (psiGoodFam h13 h12)
          Ω c r l (Nat.pair i (Nat.pair q b)) m + m) ξ ≤ B) →
      exitTerm h13 h12 c r l hx n m (Nat.pair i (Nat.pair q b)) ξ = e ∧
        e + S < (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V (pkgPsi h13 (psiGoodFam h13 h12) Ω c r
        l (Nat.pair i (Nat.pair q b)) (m - 1) + (m - 1)) ξ := by
    intro q b m B hm hagB hB
    obtain ⟨h1, hVV, h3⟩ := hslot q b m hm
    have hexJ : exitN c r l n (y, stgDrv (fun u => (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).R
        (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1) + (m - 1)) u ξ) S) = e := by
      rcases hB with hB | hB
      · exact exit_eq_of_agree_below hE y (hagB _) h1 hB
      · exact exit_eq_of_agree_cap hE y (fun u hu => hagB _ u (lt_min hu (hu.trans_le (hVV.trans hB)))) h1
    have heS : e + S < (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V (pkgPsi h13 (psiGoodFam h13
        h12) Ω c r l (Nat.pair i (Nat.pair q b)) (m - 1) + (m - 1)) ξ := by
      rw [← hexJ]
      exact h1
    have hmin : e + S < min ((schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).V (pkgPsi h13 (psiGoodFam
        h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) m + m) ξ) B := by
      rcases hB with hB | hB
      · exact lt_min (heS.trans_le hVV) hB
      · exact lt_min (heS.trans_le hVV) ((heS.trans_le hVV).trans_le hB)
    have hexJ' : exitN c r l n (y, stgDrv (fun u => (schedVerXDeathFamily h13 Ω c r l (Nat.pair i (Nat.pair q b))).R
        (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l (Nat.pair i (Nat.pair q b)) m + m) u ξ) S) = e :=
      pathRule_stgDrv_eq hE y (fun u hu => hagB _ u hu) hmin
    refine ⟨(h3 ?_).trans hexJ', heS⟩
    rw [hexJ']
    exact heS.trans_le hVV
  -- membership in the bad set
  have hZ : ∀ q b, ξ ∈ Zb h13 h12 c r l n i q b ↔ ∃ m, ξ ∈ slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) ∧
      (GW2Sdg.rootGain c r l (Nat.pair i (Nat.pair q b)) ξ : ℝ≥0∞) <
        exitTerm h13 h12 c r l hx n m (Nat.pair i (Nat.pair q b)) ξ := fun q b => by
    simp only [Zb, hgr, ↓reduceDIte, mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
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
        ∀ᶠ b in atTop, ξ ∉ Zb h13 h12 c r l n i q b := by
    intro t₁ hTt₁ ht₁c het₁ ht₁d hlife
    have hT₁ : T + (t₁ - T) = t₁ := add_tsub_cancel_of_le hTt₁.le
    obtain ⟨Q₂, hQ₂⟩ := GW2Ni.exists_capBuf_of_unc h13 c r l i hx (fun k => hGT _) hcov hold hUA hUc hlife
      (by rw [hT₁]; exact ht₁c) (by rw [hT₁]; exact het₁)
    refine ⟨max Q₂ (t₁ - T + 1), fun q hq => ?_⟩
    filter_upwards [hQ₂ q ((le_max_left _ _).trans hq)] with b hb hmem
    obtain ⟨m, hm, hlt⟩ := (hZ q b).1 hmem
    have hcap₁ : t₁ < T + (RootJ31.timeEnumeration c r q : ℝ≥0) := by
      have h3 : t₁ - T + 1 ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) := (le_max_right _ _).trans hq
      calc t₁ = T + (t₁ - T) := hT₁.symm
        _ < T + (t₁ - T + 1) := by simp
        _ ≤ _ := add_le_add (le_refl T) h3
    obtain ⟨h1, -⟩ := hkey q b m _ hm (fun j => hagree q b j t₁ hcap₁ ht₁c ht₁d) (Or.inl het₁)
    rw [h1] at hlt
    exact absurd hlt (not_lt.2 hb.le)
  rcases le_or_gt (ENNReal.ofReal L) du with hA | hB
  · -- contact first
    have he' : e + S < ENNReal.ofReal L := hexitA hA
    have hfin : e + S ≠ ⊤ := ne_top_of_lt he'
    have hv : (e + S).toReal < L := (ENNReal.lt_ofReal_iff_toReal_lt hfin).1 he'
    have hne : (clu '' {t : ℝ≥0 | (t : ℝ≥0∞) < Tcu}).Nonempty :=
      ⟨clu 0, 0, show ((0 : ℝ≥0) : ℝ≥0∞) < Tcu from lt_of_le_of_lt (by exact_mod_cast zero_le) hTcu, rfl⟩
    obtain ⟨_, ⟨t₁, ht₁c, rfl⟩, hv₁⟩ := exists_lt_of_lt_csSup hne hv
    have hSle : (S : ℝ) ≤ (e + S).toReal := by
      rw [ENNReal.toReal_add (ne_top_of_le_ne_top hfin le_self_add) ENNReal.coe_ne_top]
      simp
    have hTt₁ : T < t₁ := by
      by_contra h
      rw [not_lt] at h
      rcases eq_or_lt_of_le h with h' | h'
      · rw [h', ← hSr] at hv₁; linarith
      · have h2 : clu t₁ < clu T := hsm ht₁c hTcu h'
        rw [← hSr] at h2; linarith
    have het₁ : e + S < ENNReal.ofReal (clu t₁) := (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 hv₁
    have hlt₁ : clu t₁ < L := clock_lt_life hsm hM ht₁c
    have ht₁d : ENNReal.ofReal (clu t₁) ≤ du := (ENNReal.ofReal_le_ofReal hlt₁.le).trans hA
    refine hfinish t₁ hTt₁ ht₁c het₁ ht₁d ?_
    -- the piece lives past `t₁` (otherwise the death comes before the contact)
    by_contra hζl
    rw [not_lt] at hζl
    have hfinl : GW2Ni.uncLife c r l i ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζl
    have hl₁ : T + (GW2Ni.uncLife c r l i ξ).toNNReal ≤ t₁ := by
      have h := ENNReal.toNNReal_mono ENNReal.coe_ne_top hζl
      rw [ENNReal.toNNReal_coe] at h
      calc T + (GW2Ni.uncLife c r l i ξ).toNNReal ≤ T + (t₁ - T) := add_le_add (le_refl T) h
        _ = t₁ := add_tsub_cancel_of_le hTt₁.le
    have hl₁c : ((T + (GW2Ni.uncLife c r l i ξ).toNNReal : ℝ≥0) : ℝ≥0∞) < Tcu :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hl₁) ht₁c
    have hdu' : du = ENNReal.ofReal (clu (T + (GW2Ni.uncLife c r l i ξ).toNNReal)) := by
      rw [hdu]
      unfold GW2Ni.uncDeathX
      exact ite_eq_left ⟨hfinl, hl₁c⟩
    have hlt₂ : clu (T + (GW2Ni.uncLife c r l i ξ).toNNReal) < L := clock_lt_life hsm hM hl₁c
    have : du < ENNReal.ofReal L := by
      rw [hdu']
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T + (GW2Ni.uncLife c r l i ξ).toNNReal) with h | h
        · rw [← h]; exact ha0.ge
        · exact le_of_lt (lt_of_eq_of_lt ha0.symm (hsm (lt_of_le_of_lt (by exact_mod_cast zero_le) hTcu)
            hl₁c h))) hlt₂)).2 hlt₂
    exact absurd hA (not_le.2 this)
  · -- death first
    have hdne : du ≠ ⊤ := ne_top_of_lt hB
    have hcond : GW2Ni.uncLife c r l i ξ ≠ ⊤ ∧
        ((T + (GW2Ni.uncLife c r l i ξ).toNNReal : ℝ≥0) : ℝ≥0∞) < Tcu := by
      by_contra h
      apply hdne
      rw [hdu]
      unfold GW2Ni.uncDeathX
      exact ite_eq_right h
    set lf := (GW2Ni.uncLife c r l i ξ).toNNReal with hlf
    have hdu' : du = ENNReal.ofReal (clu (T + lf)) := by
      rw [hdu]
      unfold GW2Ni.uncDeathX
      exact ite_eq_left hcond
    -- for caps past the life, a good slot's exit is `e`, below the death
    have hgoodcap : ∀ q b m : ℕ, lf + 1 ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
        ξ ∈ slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) →
        exitTerm h13 h12 c r l hx n m (Nat.pair i (Nat.pair q b)) ξ = e ∧ e + S < du := by
      intro q b m hq hm
      set a := Nat.pair i (Nat.pair q b) with ha
      set J := pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (m - 1) + (m - 1) with hJ
      have hcapl : T + lf < T + (RootJ31.timeEnumeration c r q : ℝ≥0) :=
        (add_lt_add_iff_left T).2 (lt_of_lt_of_le (lt_add_one lf) hq)
      have hUA' := hUA a (hang q b)
      rw [hcapq] at hUA'
      -- the candidate's death clock is `d_u`
      have hlifea : candLife c r l a ξ = GW2Ni.uncLife c r l i ξ :=
        GW2Rd.candLife_eq_of_angle c r l (by rw [hang q b, GW2Ni.candidateAngle_angCand]) ξ
      have hlfc : ((T + lf : ℝ≥0) : ℝ≥0∞) < contactX x₀ c.s (schedTr c r l a) c.α ξ :=
        lt_contactX_of_agree (fun u hu => ((hUA' u hu).2).symm) hcapl hcond.2
      have hdca : deathClockX c r l a ξ = du := by
        have hle : candLife c r l a ξ ≤ (RootJ31.candidateCap c r a : ℝ≥0∞) := by
          rw [hlifea, hcapq, ← ENNReal.coe_toNNReal hcond.1]
          exact ENNReal.coe_le_coe.2 ((le_add_of_nonneg_right zero_le_one).trans hq)
        have hlt : ((T + (candLife c r l a ξ).toNNReal : ℝ≥0) : ℝ≥0∞) <
            contactX x₀ c.s (schedTr c r l a) c.α ξ := by rw [hlifea]; exact hlfc
        have hdc' : deathClockX c r l a ξ = ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l a)
            (T + (candLife c r l a ξ).toNNReal) ξ) := by
          unfold deathClockX
          exact ite_eq_left ⟨hle, hlt⟩
        have hck : clockX x₀ c.s c.W c.ζ (schedW c r l a) (T + (GW2Ni.uncLife c r l i ξ).toNNReal) ξ =
            clockX x₀ c.s c.W c.ζ (GW2Ni.uncW c r l i) (T + (GW2Ni.uncLife c r l i ξ).toNNReal) ξ :=
          clockX_eq_of_agree fun u hu => (hUA' u (hu.trans hcapl.le)).1
        rw [hdc', hdu', hlifea, hck]
      have hVd : (schedVerXDeathFamily h13 Ω c r l a).V J ξ < du := by rw [← hdca]; exact hdc a J
      have hVd' : (schedVerXDeathFamily h13 Ω c r l a).V (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a m + m) ξ < du := by
        rw [← hdca]; exact hdc a _
      obtain ⟨h1, h2⟩ := hkey q b m du hm (fun j u hu => hagree q b j (T + lf) hcapl hcond.2 (by rw [hdu']) u
        (by rw [← hdu']; exact hu)) (Or.inr hVd'.le)
      exact ⟨h1, h2.trans hVd⟩
    by_cases he₂ : e + S < du
    · -- the gain eventually passes `e`
      have hfin : e + S ≠ ⊤ := ne_top_of_lt he₂
      rw [hdu'] at he₂
      have hv : (e + S).toReal < clu (T + lf) := (ENNReal.lt_ofReal_iff_toReal_lt hfin).1 he₂
      have hcont : ContinuousOn clu (Icc 0 (T + lf)) := hac.mono fun t ht => lt_of_le_of_lt
        (ENNReal.coe_le_coe.2 ht.2) hcond.2
      set w := ((e + S).toReal + clu (T + lf)) / 2 with hw
      have hSle : (S : ℝ) ≤ (e + S).toReal := by
        rw [ENNReal.toReal_add (ne_top_of_le_ne_top hfin le_self_add) ENNReal.coe_ne_top]
        simp
      have hwmem : w ∈ Icc (clu 0) (clu (T + lf)) := by
        have h0 : clu 0 = 0 := ha0
        have hS0 : (0 : ℝ) ≤ S := S.2
        rw [h0, hw]
        constructor <;> linarith
      obtain ⟨t₁, ht₁, ht₁eq'⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ T + lf) hcont hwmem
      have ht₁eq : clu t₁ = w := ht₁eq'
      have ht₁c : (t₁ : ℝ≥0∞) < Tcu := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₁.2) hcond.2
      have hTt₁ : T < t₁ := by
        by_contra h
        rw [not_lt] at h
        rcases eq_or_lt_of_le h with h' | h'
        · rw [h', ← hSr] at ht₁eq; rw [hw] at ht₁eq; linarith
        · have h2 : clu t₁ < clu T := hsm ht₁c hTcu h'
          rw [← hSr, ht₁eq, hw] at h2; linarith
      have ht₁l : t₁ < T + lf := by
        rcases eq_or_lt_of_le ht₁.2 with h | h
        · rw [h, hw] at ht₁eq; linarith
        · exact h
      have het₁ : e + S < ENNReal.ofReal (clu t₁) := by
        rw [ht₁eq]
        exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 (by rw [hw]; linarith)
      have ht₁d : ENNReal.ofReal (clu t₁) ≤ du := by
        rw [hdu']
        exact ENNReal.ofReal_le_ofReal (by rw [ht₁eq, hw]; linarith)
      have hlife : ((t₁ - T : ℝ≥0) : ℝ≥0∞) < GW2Ni.uncLife c r l i ξ := by
        rw [← ENNReal.coe_toNNReal hcond.1]
        exact ENNReal.coe_lt_coe.2 ((tsub_lt_iff_left hTt₁.le).2 ht₁l)
      exact hfinish t₁ hTt₁ ht₁c het₁ ht₁d hlife
    · -- no slot of a large cap is good
      refine ⟨lf + 1, fun q hq => Eventually.of_forall fun b hmem => ?_⟩
      obtain ⟨m, hm, -⟩ := (hZ q b).1 hmem
      exact he₂ (hgoodcap q b m hq hm).2

end InteractingSLE.Theorem14.GW2Bh
