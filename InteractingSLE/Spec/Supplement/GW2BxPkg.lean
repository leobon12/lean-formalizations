/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxRef
import InteractingSLE.Spec.Supplement.GW2BwZ

/-!
# The nearImg package for a base version family (decision D75)

Packet PROVE-GW2-BUF (round 21). Round 19's package hard-codes RELDET's death family; D75 moves nearImg to NOTHR's
stop family. Here everything is stated for a base family `ver₀` and a choice family `ch`:

* the goodness re-indexing **`psiGoodS h13 ver₀ ch`** (round 18's kernel loss lemma on `ver₀`'s good events; the
  good events do not read `ch`'s word data) and its spec;
* the package family **`verS = GW2Rl.verU ver₀ (psiGoodS …)`** (ROOTX's uniformly covering re-indexing; at
  `ver₀ = GW2Nx.schedVerXStopFamily`, ROOTX's `oneVerS`); slot `m` of candidate `a` reads base version `JS a m`;
* the near stops `KbS = nearStopPkgX h13 verS ch exitB K₀`, the package
  **`pkgS = withNearSB (pkgX h13 verS ch KbS) nearLam (GW2Rl.refNb h13 verS cwSrc) (kSel k)`**;
* the slot identities `pkgS_nearVar_eq`, `pkgS_nearVar_stop`, `pkgS_nearVar_R`;
* D75's corrected bad sets: **`ZbS n i q b`** = (good slots whose gain is below the exit term) ∪
  `{¬ ∃ k, goodFrom k}`; `measurableSet_ZbS`, `nearStopS_le_exitTermS`, **`srcBadS_subset_ZbS`**,
  **`not_goodFrom_subset_ZbS`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

section Meas

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- **The good events of any family are measurable** (no instance inputs). -/
theorem measurableSet_goodVerV (hg : GoodRoot c r) (n a j : ℕ) :
    MeasurableSet (goodVer h13 ver₀ ch c r l hg.1 (exitN c r l) n a j) := by
  obtain ⟨hx, hs⟩ := hg
  obtain ⟨hGT, hGTm, hGTae⟩ := schedGTX_spec h13 c r l a
  have hA := (ver₀ Ω c r l a).isA hx j
  have hWm : ∀ t, Measurable (schedW c r l a t) := measurable_schedW c r l a
  have hpre : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l) ((ver₀ Ω c r l a).R j)) :=
    (measurable_stgPreRecX hGT hs hx (measurable_gb6Rec_src c) hWm
      (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGTm hGTae) hA.1
      (RootJ31.historyTime c r l)).mono
      ((Supp8.RelSafe.physFilt (measurable_gb6Rec_src c) hWm c.P).le (RootJ31.historyTime c r l)) le_rfl
  have hrec : Measurable ((instX h13 ver₀ ch Ω c r l a j hx).srecX c r l (rootPt r.1)) :=
    measurable_augRec ((measurable_stageEncRec_sigma c r l).mono (sigma_le_ambient c r l) le_rfl) hpre
  have hS : Measurable (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l)) := measurable_stgStartX_of_pre hpre
  have hpath : Measurable fun ξ => fun t => (instX h13 ver₀ ch Ω c r l a j hx).drvX c (rootPt r.1) t ξ :=
    measurable_pi_iff.2 fun t => measurable_stgDrv hA.1.1.1 hA.1.1.2.1 hS t
  have hV : Measurable ((ver₀ Ω c r l a).V j) := hA.1.1.2.2.2.2.1
  exact measurableSet_lt ((((exitB_spec Ω c r l n 0).2).comp (hrec.prodMk hpath)).add
    (measurable_coe_nnreal_ennreal.comp hS)) hV

theorem measurableSet_goodFromV (hg : GoodRoot c r) (n a k : ℕ) :
    MeasurableSet (goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n a k) :=
  MeasurableSet.biInter (to_countable _) fun j _ => measurableSet_goodVerV h13 ver₀ ch c r l hg n a j

theorem measurableSet_not_goodFrom (hg : GoodRoot c r) (n a : ℕ) :
    MeasurableSet {ξ : Ω | ¬ ∃ k, ξ ∈ goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n a k} := by
  have e : {ξ : Ω | ¬ ∃ k, ξ ∈ goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n a k} =
      (⋃ k, goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n a k)ᶜ := by
    ext ξ
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion]
  rw [e]
  exact (MeasurableSet.iUnion fun k => measurableSet_goodFromV h13 ver₀ ch c r l hg n a k).compl

end Meas

open Classical in
/-- **The goodness re-indexing of a base family** (round 18's kernel loss lemma on its good events; the identity off
the good roots). -/
def psiGoodS : PsiFam.{u} := fun _ _ _ c r l =>
  if hg : GoodRoot c r then
    (exists_reindex_kernel_loss (P := c.P) (sigma_le_ambient c r l)
      (goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l)) (measurableSet_goodFromV h13 ver₀ ch c r l hg)
      monotone_goodFrom).choose
  else fun _ m => m

/-- **The kernel loss bound of the goodness re-indexing.** -/
theorem psiGoodS_spec {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hg : GoodRoot c r) :
    ∀ᵐ ω₀ ∂c.P, ∀ (sel : ℕ → ℕ → ℕ) (n : ℕ) {ε : ℝ≥0∞}, 0 < ε → ∀ᶠ m in atTop,
      condExpKernel c.P (c.sigma r l) ω₀
        ({ξ | ∃ k, ξ ∈ goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n (sel n m) k} \
          goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n (sel n m) (psiGoodS h13 ver₀ ch Ω c r l (sel n m) m)) ≤
        ε := by
  have e : psiGoodS h13 ver₀ ch Ω c r l = (exists_reindex_kernel_loss (P := c.P) (sigma_le_ambient c r l)
      (goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l)) (measurableSet_goodFromV h13 ver₀ ch c r l hg)
      monotone_goodFrom).choose := by
    simp only [psiGoodS, hg, ↓reduceDIte]
  rw [e]
  exact (exists_reindex_kernel_loss (P := c.P) (sigma_le_ambient c r l)
    (goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l)) (measurableSet_goodFromV h13 ver₀ ch c r l hg)
    monotone_goodFrom).choose_spec.2.2

/-! ### The package -/

/-- **The package's version family**: ROOTX's uniformly covering re-indexing of `ver₀` with the goodness
re-indexing as `ψx`. -/
abbrev verS : SchedVerXFamily.{u} := GW2Rl.verU ver₀ (psiGoodS h13 ver₀ ch)

/-- The base version read by slot `m` of candidate `a`. -/
abbrev JS (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) : ℕ :=
  GW2Rl.psiAll ver₀ (psiGoodS h13 ver₀ ch) Ω c r l a m + m

theorem monotone_JS (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Monotone (JS h13 ver₀ ch Ω c r l a) :=
  fun _ _ h => Nat.add_le_add (GW2Rl.monotone_psiAll ver₀ (psiGoodS h13 ver₀ ch) Ω c r l a h) h

theorem psiGoodS_le_JS (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    psiGoodS h13 ver₀ ch Ω c r l a m ≤ JS h13 ver₀ ch Ω c r l a m :=
  ((Finset.le_sup (f := psiGoodS h13 ver₀ ch Ω c r l a) (Finset.mem_range.2 (Nat.lt_succ_self m))).trans
    (le_max_right _ _)).trans (Nat.le_add_right _ _)

variable (K₀ : PkgFamily.{u})

/-- **The package's near stops**: BUF's near stops for the exit rules `exitB`. -/
abbrev KbS : PkgFamily.{u} := nearStopPkgX h13 (verS h13 ver₀ ch) ch exitB K₀

/-- **The nearImg package** at buffer index `k`: the rightward selection on ROOTX's reference near base. -/
abbrev pkgS (kSel : NearSelB.{u}) (k : ℕ) : VPkgXFamily.{u} :=
  withNearSB (pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀)) nearLam
    (GW2Rl.refNb h13 (verS h13 ver₀ ch) cwSrc) (kSel k)

section Slots

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

theorem pkgS_nearVar_eq (hg : GoodRoot c r) (n m a : ℕ) :
    (pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀) Ω c r).nearVar l n m a =
      (instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hg.1).varX c r l (rootPt r.1)
        ((KbS h13 ver₀ ch K₀ Ω c r).nearStop l n m a) :=
  GW2Rl.pkgX_nearVar_eq (KbS h13 ver₀ ch K₀) c r hg l n m a

/-- **The package's near stop** at a good root (`m = m' + 1`). -/
theorem pkgS_nearVar_stop (kSel : NearSelB.{u}) (hg : GoodRoot c r) (k n m' a : ℕ) (ξ : Ω) :
    (((pkgS h13 ver₀ ch K₀ kSel k).at 0 Ω c r).nearVar l n (m' + 1) a).stop ξ =
      min ((lowCapStopX c l (instX h13 (verS h13 ver₀ ch) ch Ω c r l a (m' + 1) hg.1) (rootPt r.1)
          ((verS h13 ver₀ ch Ω c r l a).V m') ((verS h13 ver₀ ch Ω c r l a).isA hg.1 m').1.2.choose).stop ξ)
        (exitB.{u} Ω c r l n a
          ((instX h13 (verS h13 ver₀ ch) ch Ω c r l a (m' + 1) hg.1).srecX c r l (rootPt r.1) ξ,
            killPath ((fun t => (instX h13 (verS h13 ver₀ ch) ch Ω c r l a (m' + 1) hg.1).drvX c (rootPt r.1) t ξ),
              (instX h13 (verS h13 ver₀ ch) ch Ω c r l a (m' + 1) hg.1).capX c (rootPt r.1) ξ))) := by
  change ((pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀) Ω c r).nearVar l n (m' + 1) a).stop ξ = _
  rw [pkgS_nearVar_eq h13 ver₀ ch K₀ c r l hg n (m' + 1) a]
  change ((KbS h13 ver₀ ch K₀ Ω c r).nearStop l n (m' + 1) a).stop ξ = _
  simp only [KbS, nearStopPkgX, hg, ↓reduceDIte, Nat.add_sub_cancel]
  rfl

/-- The package's near driver at a good root is the instance's stage driver. -/
theorem pkgS_nearVar_R (kSel : NearSelB.{u}) (hg : GoodRoot c r) (k n m a : ℕ) :
    (((pkgS h13 ver₀ ch K₀ kSel k).at 0 Ω c r).nearVar l n m a).R =
      (instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hg.1).drvX c (rootPt r.1) := by
  change ((pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀) Ω c r).nearVar l n m a).R = _
  rw [pkgS_nearVar_eq h13 ver₀ ch K₀ c r l hg n m a]
  rfl

open Classical in
/-- **The good event of slot `(l, n, m, a)`**: base version `JS a (m − 1)` is good. -/
def slotGoodS (n m a : ℕ) : Set Ω :=
  if hg : GoodRoot c r then goodVer h13 ver₀ ch c r l hg.1 (exitN c r l) n a (JS h13 ver₀ ch Ω c r l a (m - 1))
  else ∅

/-- **Clause (iii)'s source-buffer loss at slot `(l, n, m, a)`.** -/
def srcBadS (n m a : ℕ) : Set Ω :=
  slotGoodS h13 ver₀ ch c r l n m a ∩
    {ξ | (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) <
      ((pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀) Ω c r).nearVar l n m a).stop ξ}

/-- **The exit term of slot `(l, n, m, a)`**: the exit rule on the killed stage path of version `m`. -/
def exitTermS (hx : 0 ≤ rootPt r.1) (n m a : ℕ) (ξ : Ω) : ℝ≥0∞ :=
  exitB.{u} Ω c r l n a
    ((instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hx).srecX c r l (rootPt r.1) ξ,
      killPath ((fun t => (instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hx).drvX c (rootPt r.1) t ξ),
        (instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hx).capX c (rootPt r.1) ξ))

open Classical in
/-- **D75's bad set of the `kSel` bound** for level `n`, angle index `i`, cap index `q` and buffer `b`: a good slot
whose gain is below its exit term, or no version of the candidate is ever good from some index on. -/
def ZbS (n i q b : ℕ) : Set Ω :=
  if hg : GoodRoot c r then
    (⋃ m : ℕ, slotGoodS h13 ver₀ ch c r l n m (Nat.pair i (Nat.pair q b)) ∩
      {ξ | (GW2Sdg.rootGain c r l (Nat.pair i (Nat.pair q b)) ξ : ℝ≥0∞) <
        exitTermS h13 ver₀ ch c r l hg.1 n m (Nat.pair i (Nat.pair q b)) ξ}) ∪
      {ξ | ¬ ∃ k, ξ ∈ goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n (Nat.pair i (Nat.pair q b)) k}
  else ∅

theorem measurable_exitTermS (hI : InstInputsX h13 (verS h13 ver₀ ch) ch) (hTO : GW2Sdx.HistOrdered c r l)
    (hg : GoodRoot c r) (n m a : ℕ) : Measurable (exitTermS h13 ver₀ ch c r l hg.1 n m a) := by
  have hgood := hI.goodX hTO hg a m
  have hpre := hgood.measurable_pre
  have hrec : Measurable ((instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hg.1).srecX c r l (rootPt r.1)) :=
    measurable_augRec ((measurable_stageEncRec_sigma c r l).mono (sigma_le_ambient c r l) le_rfl) hpre
  have hS : Measurable (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((verS h13 ver₀ ch Ω c r l a).V m) (RootJ31.historyTime c r l)) := measurable_stgStartX_of_pre hpre
  have hD : ∀ t, Measurable ((instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hg.1).drvX c (rootPt r.1) t) := fun t =>
    measurable_stgDrv hgood.version.1 hgood.version.2.1 hS t
  have hV : Measurable ((verS h13 ver₀ ch Ω c r l a).V m) := hgood.version.2.2.2.2.1
  have hcap : Measurable ((instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hg.1).capX c (rootPt r.1)) :=
    hV.sub (measurable_coe_nnreal_ennreal.comp hS)
  exact (exitB_spec Ω c r l n a).2.comp (hrec.prodMk (measurable_killPath_comp hD hcap))

theorem measurableSet_slotGoodS (hg : GoodRoot c r) (n m a : ℕ) :
    MeasurableSet (slotGoodS h13 ver₀ ch c r l n m a) := by
  classical
  have e : slotGoodS h13 ver₀ ch c r l n m a =
      goodVer h13 ver₀ ch c r l hg.1 (exitN c r l) n a (JS h13 ver₀ ch Ω c r l a (m - 1)) := by
    simp only [slotGoodS, hg, ↓reduceDIte]
  rw [e]
  exact measurableSet_goodVerV h13 ver₀ ch c r l hg n a _

/-- **The bad sets are measurable.** -/
theorem measurableSet_ZbS (hI : InstInputsX h13 (verS h13 ver₀ ch) ch) (hTO : GW2Sdx.HistOrdered c r l)
    (n i q b : ℕ) : MeasurableSet (ZbS h13 ver₀ ch c r l n i q b) := by
  classical
  unfold ZbS
  split_ifs with hg
  · exact (MeasurableSet.iUnion fun m => (measurableSet_slotGoodS h13 ver₀ ch c r l hg n m _).inter
      (measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_rootGain c r l _))
        (measurable_exitTermS h13 ver₀ ch c r l hI hTO hg n m _))).union
      (measurableSet_not_goodFrom h13 ver₀ ch c r l hg n _)
  · exact MeasurableSet.empty

/-- **The near stop is at most the exit term.** -/
theorem nearStopS_le_exitTermS (hg : GoodRoot c r) (n m a : ℕ) (ξ : Ω) :
    ((pkgX h13 (verS h13 ver₀ ch) ch (KbS h13 ver₀ ch K₀) Ω c r).nearVar l n m a).stop ξ ≤
      exitTermS h13 ver₀ ch c r l hg.1 n m a ξ := by
  rw [pkgS_nearVar_eq h13 ver₀ ch K₀ c r l hg n m a]
  change ((KbS h13 ver₀ ch K₀ Ω c r).nearStop l n m a).stop ξ ≤ _
  simp only [KbS, nearStopPkgX, hg, ↓reduceDIte]
  exact min_le_right _ _

theorem ZbS_eq (hg : GoodRoot c r) (n i q b : ℕ) :
    ZbS h13 ver₀ ch c r l n i q b =
      (⋃ m : ℕ, slotGoodS h13 ver₀ ch c r l n m (Nat.pair i (Nat.pair q b)) ∩
        {ξ | (GW2Sdg.rootGain c r l (Nat.pair i (Nat.pair q b)) ξ : ℝ≥0∞) <
          exitTermS h13 ver₀ ch c r l hg.1 n m (Nat.pair i (Nat.pair q b)) ξ}) ∪
        {ξ | ¬ ∃ k, ξ ∈ goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n (Nat.pair i (Nat.pair q b)) k} := by
  simp only [ZbS, hg, ↓reduceDIte]

/-- **Every source-buffer loss lies in the bad set** of its candidate's angle, cap and buffer indices. -/
theorem srcBadS_subset_ZbS (n m i q b : ℕ) :
    srcBadS h13 ver₀ ch K₀ c r l n m (Nat.pair i (Nat.pair q b)) ⊆ ZbS h13 ver₀ ch c r l n i q b := by
  classical
  intro ξ hξ
  by_cases hg : GoodRoot c r
  · rw [ZbS_eq h13 ver₀ ch c r l hg]
    exact Or.inl (mem_iUnion.2 ⟨m, hξ.1, lt_of_lt_of_le hξ.2 (nearStopS_le_exitTermS h13 ver₀ ch K₀ c r l hg n m _
      ξ)⟩)
  · have h0 : slotGoodS h13 ver₀ ch c r l n m (Nat.pair i (Nat.pair q b)) = ∅ := by
      simp only [slotGoodS, hg, ↓reduceDIte]
    exact absurd hξ.1 (by rw [h0]; exact notMem_empty ξ)

/-- **A candidate never good from any index lies in the bad set.** -/
theorem not_goodFrom_subset_ZbS (hg : GoodRoot c r) (n i q b : ℕ) :
    {ξ | ¬ ∃ k, ξ ∈ goodFrom h13 ver₀ ch c r l hg.1 (exitN c r l) n (Nat.pair i (Nat.pair q b)) k} ⊆
      ZbS h13 ver₀ ch c r l n i q b := by
  rw [ZbS_eq h13 ver₀ ch c r l hg]
  exact subset_union_right

end Slots

end InteractingSLE.Theorem14.GW2Bh
