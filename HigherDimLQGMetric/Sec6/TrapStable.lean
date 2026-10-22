import HigherDimLQGMetric.Sec6.Collar

/-!
# [S] Proposition 6.2, deterministic part: (T1)–(T4) from the stability properties

Packet S6a (MA3 D-6.2, *Proof of (T)*; blueprint `prop:62` (T); source l. 996–1119). For two continuous
metrics `D₀, D̃₀`, a scale `s > 0`, a radius `r > 0` and a centre `z`, write
`κ' = config D₀ D̃₀ s r z` and let `E, Ẽ` be its first two components (the normalized internal metrics
`s⁻¹ D₀(z + r·, z + r·; A_{r/2,5r}(z))`, `s⁻¹ D̃₀(…)`) on the configuration carrier `U = A_{1/2,5}`, and
`w = e^{−ξ f}` for the discount `f`. The **stability properties** (i′)–(iii′) of D-6.2, stated on `κ'` in
exactly the form of the conclusions of S3's `lemma42_trap` (after M27's bridge `ofReal ∘ configC = config`):

* (i′) any two points of `closure V` are joined inside `A_{1,3}` at weighted cost `(w·E)_{A_{1,3}} ≤ a`;
* (ii′) every minimizer `Q` of the `U`-internal weighted metric `(w·E)_U` between points of `closure V`
  with `E(Q 0, Q 1) ≥ b` has a subsegment `[u, v]` of weighted length `≥ c` whose endpoints are joined inside
  `A_{1,3}` by a path of `w·Ẽ`-length `≤ c'` times that length;
* (iii′) the collar `E(x, y) ≥ a` for `x ∈ closure V`, `y ∈ frontier A_{1,3}`;

imply `TrapProps ξ V f' J a b c a (a e^{ξ M_f}) c' D₀ D̃₀ s r z j` for every family `f'` with `f' j = f` whose
members are supported in `A_{1,3}` (the last condition is needed for (T4); see the handoff). (T3) is proved
with the internal `B_{4r}(z)` threshold through the threshold equivalence of D-6.2 step (3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

namespace S6a

/-- `x + x ≤ x` is impossible for `0 < x < ∞`. -/
theorem not_add_self_le {x : ℝ≥0∞} (h0 : 0 < x) (htop : x ≠ ⊤) : ¬ x + x ≤ x :=
  not_le.2 (ENNReal.lt_add_right htop h0.ne')

/-- A realized configuration point in the closed collector comes from `closure V`. -/
theorem mem_closure_of_affine_mem {r : ℝ} (hr : r ≠ 0) (z : Rd d) {V : Set (Rd d)} {u : Rd d}
    (hu : r • u + z ∈ closure ((fun x : Rd d => r • x + z) '' V)) : u ∈ closure V := by
  rw [closure_collector hr z V] at hu
  obtain ⟨x, hx, hxu⟩ := hu
  have hxu' : x = u := (affHomeo r hr z).injective hxu
  rwa [← hxu']

end S6a

/-- **[S] Proposition 6.2 (T), deterministic part** (MA3 D-6.2, *Proof of (T)*). The stability properties
(i′)–(iii′) of the configuration `config D₀ D̃₀ s r z` (with respect to the discount `f`) imply the trap
properties (T1)–(T4) at `(z, r, j)` with scale `s`, `g = a` and `H = a e^{ξ M_f}`, for every family `f'` with
`f' j = f` whose members (`i < J`) are supported in `A_{1,3}`. (T3) holds with the internal `B_{4r}(z)`
threshold (MA3 E11). `E`, `Ẽ`, `w` are the configuration coordinates and the weight, passed with their
defining equations so that the hypotheses read exactly like the conclusions of `lemma42_trap`. -/
theorem trapProps_of_stable {ξ : ℝ} (hξ : 0 ≤ ξ) (D₀ Dt₀ : ContMetric d)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d)
    {V : Set (Rd d)} (hV : IsOpen V) (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    {f : C(Rd d, ℝ)} (hf0 : ∀ x, 0 ≤ f x) (hfV : ∀ x, 0 < f x ↔ x ∈ V)
    {Mf : ℝ} (hfM : ∀ x, f x ≤ Mf)
    {f' : ℕ → C(Rd d, ℝ)} {J j : ℕ} (hf'j : f' j = f)
    (hf'supp : ∀ i < J, tsupport (f' i) ⊆ ann (0 : Rd d) 1 3)
    {a b c c' : ℝ} (ha : 0 < a) (hba : b ≤ a)
    {E Et : ↥(ann (0 : Rd d) (1 / 2) 5) → ↥(ann (0 : Rd d) (1 / 2) 5) → ℝ≥0∞}
    (hE : ∀ u v, E u v = (config D₀ Dt₀ s r z).1 u v)
    (hEt : ∀ u v, Et u v = (config D₀ Dt₀ s r z).2.1 u v)
    {w : ↥(ann (0 : Rd d) (1 / 2) 5) → ℝ} (hw : ∀ u, w u = Real.exp (-(ξ * f u)))
    (hi : ∀ x y : ↥(ann (0 : Rd d) (1 / 2) 5), (x : Rd d) ∈ closure V →
      (y : Rd d) ∈ closure V →
      weylDistOnWith E w {u | (u : Rd d) ∈ ann (0 : Rd d) 1 3} x y ≤ ENNReal.ofReal a)
    (hii : ∀ Q : ℝ → ↥(ann (0 : Rd d) (1 / 2) 5), ContinuousOn Q (Icc 0 1) →
      (Q 0 : Rd d) ∈ closure V → (Q 1 : Rd d) ∈ closure V →
      weightedLengthWith E w Q 0 1 = weylDistOnWith E w univ (Q 0) (Q 1) →
      ENNReal.ofReal b ≤ E (Q 0) (Q 1) →
      ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧ ENNReal.ofReal c ≤ weightedLengthWith E w Q u v ∧
        ∃ S : ℝ → ↥(ann (0 : Rd d) (1 / 2) 5), ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧
          S 1 = Q v ∧ MapsTo S (Icc 0 1) {x | (x : Rd d) ∈ ann (0 : Rd d) 1 3} ∧
          weightedLengthWith Et w S 0 1 ≤ ENNReal.ofReal c' * weightedLengthWith E w Q u v)
    (hiii : ∀ x y : ↥(ann (0 : Rd d) (1 / 2) 5), (x : Rd d) ∈ closure V →
      (y : Rd d) ∈ frontier (ann (0 : Rd d) 1 3) → ENNReal.ofReal a ≤ E x y) :
    TrapProps ξ V f' J a b c a (a * Real.exp (ξ * Mf)) c' D₀ Dt₀ s r z j := by
  subst hf'j
  -- the configuration coordinates as normalized internal metrics at `(z, r)`
  have hE' : ∀ u v : ↥(ann (0 : Rd d) (1 / 2) 5), E u v = ENNReal.ofReal s⁻¹ *
      D₀.internal (ann z (r / 2) (5 * r)) (r • (u : Rd d) + z) (r • (v : Rd d) + z) := hE
  have hEt' : ∀ u v : ↥(ann (0 : Rd d) (1 / 2) 5), Et u v = ENNReal.ofReal s⁻¹ *
      Dt₀.internal (ann z (r / 2) (5 * r)) (r • (u : Rd d) + z) (r • (v : Rd d) + z) := hEt
  -- the sets: `A = A_{r,3r}(z)`, `W = A_{r/2,5r}(z)`, `V_z = z + rV`
  have hAo : IsOpen (ann z r (3 * r)) := isOpen_ann z r (3 * r)
  have hVzo : IsOpen ((fun x : Rd d => r • x + z) '' V) := S6a.isOpen_collector hr.ne' z hV
  have hVzA : closure ((fun x : Rd d => r • x + z) '' V) ⊆ ann z r (3 * r) :=
    S6a.closure_collector_subset hr z hVA
  have hAW : closure (ann z r (3 * r)) ⊆ ann z (r / 2) (5 * r) := S6a.closure_ann_subset_cfg hr z
  have hAB : ann z r (3 * r) ⊆ ball z (4 * r) := S6a.ann_subset_ball hr z
  have hfV0 : ∀ x, x ∉ V → f' j x = 0 := fun x hx =>
    le_antisymm (not_lt.1 fun h => hx ((hfV x).1 h)) (hf0 x)
  have has0 : 0 < ENNReal.ofReal (a * s) := ENNReal.ofReal_pos.2 (mul_pos ha hs)
  have hastop : ENNReal.ofReal (a * s) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the collar `D₀(x, y; W) ≥ a s` for `x ∈ closure V_z`, `y ∈ frontier A` ((iii′) rescaled)
  have hcol : ∀ x ∈ closure ((fun x : Rd d => r • x + z) '' V), ∀ y ∈ frontier (ann z r (3 * r)),
      ENNReal.ofReal (a * s) ≤ D₀.internal (ann z (r / 2) (5 * r)) x y := by
    intro x hx y hy
    rw [S6a.closure_collector hr.ne' z V] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [S6a.frontier_ann13 hr z] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hx'U : x' ∈ ann (0 : Rd d) (1 / 2) 5 := S6a.ann13_subset_cfg (hVA hx')
    have hy'U : y' ∈ ann (0 : Rd d) (1 / 2) 5 := S6a.annCl13_subset_cfg
      (S6a.closure_ann_subset_annCl 0 1 3 (frontier_subset_closure hy'))
    have h := hiii ⟨x', hx'U⟩ ⟨y', hy'U⟩ hx' hy'
    rw [hE'] at h
    calc ENNReal.ofReal (a * s) = ENNReal.ofReal s * ENNReal.ofReal a := S6a.ofReal_mul_scale hs a
      _ ≤ ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ *
            D₀.internal (ann z (r / 2) (5 * r)) (r • x' + z) (r • y' + z)) := mul_le_mul' le_rfl h
      _ = D₀.internal (ann z (r / 2) (5 * r)) (r • x' + z) (r • y' + z) :=
          S6a.ofReal_mul_ofReal_inv_mul hs _
  -- the connection bound in `A` for every discounted metric that agrees with `e^{−ξ f_{z,r}}` on `A`
  have hT2gen : ∀ (g : C(Rd d, ℝ)) (D' : ContMetric d), IsWeylOf ξ g D₀ D' →
      (∀ u : ↥(ann (0 : Rd d) (1 / 2) 5), (u : Rd d) ∈ ann (0 : Rd d) 1 3 →
        w u = Real.exp (ξ * g (r • (u : Rd d) + z))) →
      ∀ x ∈ closure ((fun x : Rd d => r • x + z) '' V),
      ∀ y ∈ closure ((fun x : Rd d => r • x + z) '' V),
        D'.internal (ann z r (3 * r)) x y ≤ ENNReal.ofReal (a * s) := by
    intro g D' hD' hwg x hx y hy
    rw [S6a.closure_collector hr.ne' z V] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hx'U : x' ∈ ann (0 : Rd d) (1 / 2) 5 := S6a.ann13_subset_cfg (hVA hx')
    have hy'U : y' ∈ ann (0 : Rd d) (1 / 2) 5 := S6a.ann13_subset_cfg (hVA hy')
    calc D'.internal (ann z r (3 * r)) (r • x' + z) (r • y' + z)
        ≤ ENNReal.ofReal s * weylDistOnWith E w {u | (u : Rd d) ∈ ann (0 : Rd d) 1 3}
            ⟨x', hx'U⟩ ⟨y', hy'U⟩ :=
          S6a.internal_le_weylDistOnWith hD' hs hr hE' hwg ⟨x', hx'U⟩ ⟨y', hy'U⟩
      _ ≤ ENNReal.ofReal s * ENNReal.ofReal a := mul_le_mul' le_rfl (hi _ _ hx' hy')
      _ = ENNReal.ofReal (a * s) := (S6a.ofReal_mul_scale hs a).symm
  -- the single discount `g = −f_{z,r,j}` matches the weight everywhere
  have hwg : ∀ u : ↥(ann (0 : Rd d) (1 / 2) 5),
      w u = Real.exp (ξ * (-bumpAt (f' j) r z) (r • (u : Rd d) + z)) := by
    intro u
    rw [hw u, ContinuousMap.neg_apply, bumpAt_affine _ hr.ne', mul_neg]
  have hg1 : ∀ x ∈ closure (ann z r (3 * r)), x ∉ (fun x : Rd d => r • x + z) '' V →
      (-bumpAt (f' j) r z) x = 0 := by
    intro x _ hxV
    rw [ContinuousMap.neg_apply, S6a.bumpAt_eq_zero_of_notMem hfV0 hr.ne' z hxV, neg_zero]
  refine ⟨?T1, ?T2, ?T3, ?T4⟩
  case T1 =>
    -- (T1): cut at the first exit from `A`
    intro P hPc hP0 hP1
    have h1A : P 1 ∉ ann z r (3 * r) := by
      rintro ⟨h1, h2⟩
      rcases hP1 with h | h
      · rw [mem_sphere, dist_eq_norm] at h
        linarith
      · rw [mem_sphere, dist_eq_norm] at h
        linarith
    exact S6a.collar_le_len D₀ hAo hVzA hAW hcol hPc hP0 ⟨zero_le_one, le_rfl⟩ h1A
  case T2 =>
    -- (T2): (i′) rescaled
    intro D' hD' u hu v hv
    have h := hT2gen _ D' hD' (fun u _ => hwg u) u hu v hv
    rwa [show (2 * a - a) * s = a * s by ring]
  case T3 =>
    intro D' Dt' hD' hDt' P hP σ₁ σ₂ hσ₁ hσ₁₂ hσ₂ hPσ₁ hPσ₂ _ hthr
    have hPc : ContinuousOn P (Icc 0 1) := hP.1
    have hPB : ∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ ball z (4 * r) := hP.2.1
    -- `D'` is a length metric, so its internal metric on the ball is finite
    have hD'len : D'.IsLength := isLength_of_eq_weylScale D' hD'
    have hfin : D'.internal (ball z (4 * r)) (P 0) (P 1) ≠ ⊤ :=
      D'.internal_ne_top_of_isPreconnected hD'len isOpen_ball
        (convex_ball z (4 * r)).isPreconnected (hPB 0 ⟨le_rfl, zero_le_one⟩)
        (hPB 1 ⟨zero_le_one, le_rfl⟩)
    have hseg : D'.len P σ₁ σ₂ ≤ D'.internal (ball z (4 * r)) (P σ₁) (P σ₂) :=
      S6a.len_le_internal_of_isGeodIn hP hfin hσ₁ hσ₁₂ hσ₂
    -- (1) the segment between the collector times costs at most `a s`
    have hcost : D'.len P σ₁ σ₂ ≤ ENNReal.ofReal (a * s) :=
      hseg.trans ((D'.internal_anti hAB _ _).trans
        (hT2gen _ D' hD' (fun u _ => hwg u) _ hPσ₁ _ hPσ₂))
    -- (2) departure and return: the segment stays in `A`
    have hPc12 : ContinuousOn P (Icc σ₁ σ₂) := hPc.mono (Icc_subset_Icc hσ₁ hσ₂)
    have hinA : ∀ t ∈ Icc σ₁ σ₂, P t ∈ ann z r (3 * r) := by
      intro t ht
      by_contra htA
      exact S6a.not_add_self_le has0 hastop
        ((S6a.depart_return hD' hAo hVzo hVzA hAW hg1 hcol hPc12 hPσ₁ hPσ₂ ht htA).trans hcost)
    -- the configuration curve of the segment
    obtain ⟨Q, hQc, hQP, hQA⟩ := S6a.exists_cfg_lift hσ₁₂ hPc12 hr hinA
    have hQ0 : r • (Q 0 : Rd d) + z = P σ₁ := by
      rw [hQP 0 ⟨le_rfl, zero_le_one⟩, zero_mul, add_zero]
    have hQ1 : r • (Q 1 : Rd d) + z = P σ₂ := by
      rw [hQP 1 ⟨zero_le_one, le_rfl⟩, one_mul, add_sub_cancel]
    have hQ0V : (Q 0 : Rd d) ∈ closure V :=
      S6a.mem_closure_of_affine_mem hr.ne' z (hQ0 ▸ hPσ₁)
    have hQ1V : (Q 1 : Rd d) ∈ closure V :=
      S6a.mem_closure_of_affine_mem hr.ne' z (hQ1 ▸ hPσ₂)
    -- weighted configuration lengths of `Q` are rescaled `D'`-lengths of `P`
    have hWL : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 → weightedLengthWith E w Q u v =
        ENNReal.ofReal s⁻¹ * D'.len P (σ₁ + u * (σ₂ - σ₁)) (σ₁ + v * (σ₂ - σ₁)) := by
      intro u v hu huv hv
      rw [S6a.weightedLengthWith_cfg hD' hr hE' hQc.continuousOn (fun t _ => hwg (Q t)),
        D'.len_congr (fun t ht => hQP t ⟨hu.trans ht.1, ht.2.trans hv⟩),
        S6a.len_affine_reparam D' P hσ₁₂ huv]
    have hWL01 : weightedLengthWith E w Q 0 1 = ENNReal.ofReal s⁻¹ * D'.len P σ₁ σ₂ := by
      rw [hWL 0 1 le_rfl zero_le_one le_rfl, zero_mul, add_zero, one_mul, add_sub_cancel]
    -- (2′) `Q` minimizes the `U`-internal weighted metric (D-6.2 step (2))
    have hmin : weightedLengthWith E w Q 0 1 = weylDistOnWith E w univ (Q 0) (Q 1) := by
      refine le_antisymm ?_ (weylDistOnWith_le hQc.continuousOn rfl rfl (mapsTo_univ _ _))
      unfold weylDistOnWith
      refine le_iInf fun R => le_iInf fun hRc => le_iInf fun hR0 => le_iInf fun hR1 =>
        le_iInf fun _ => ?_
      rw [hWL01, S6a.weightedLengthWith_cfg hD' hr hE' hRc (fun t _ => hwg (R t))]
      refine mul_le_mul' le_rfl ?_
      by_contra hlt
      rw [not_le] at hlt
      have hPRc : ContinuousOn (fun t => r • (R t : Rd d) + z) (Icc 0 1) :=
        S6a.continuousOn_realize hRc
      have hPR0 : r • (R 0 : Rd d) + z = P σ₁ := by rw [hR0, hQ0]
      have hPR1 : r • (R 1 : Rd d) + z = P σ₂ := by rw [hR1, hQ1]
      have hPRA : ∀ t ∈ Icc (0 : ℝ) 1, r • (R t : Rd d) + z ∈ ann z r (3 * r) := by
        intro t ht
        by_contra htA
        have h2 := S6a.depart_return hD' hAo hVzo hVzA hAW hg1 hcol hPRc
          (show r • (R 0 : Rd d) + z ∈ _ from hPR0 ▸ hPσ₁)
          (show r • (R 1 : Rd d) + z ∈ _ from hPR1 ▸ hPσ₂) ht htA
        exact S6a.not_add_self_le has0 hastop ((h2.trans hlt.le).trans hcost)
      have hint := D'.internal_le_len zero_le_one hPRc (fun t ht => hAB (hPRA t ht))
      simp only [hPR0, hPR1] at hint
      exact absurd (hint.trans_lt hlt) (not_lt.2 hseg)
    -- (3) threshold equivalence: the internal `B_{4r}(z)` threshold gives the configuration one
    have hthr' : ENNReal.ofReal b ≤ E (Q 0) (Q 1) := by
      rw [hE', hQ0, hQ1]
      have hW : ENNReal.ofReal (b * s) ≤ D₀.internal (ann z (r / 2) (5 * r)) (P σ₁) (P σ₂) := by
        by_contra hlt
        rw [not_le, D₀.internal_eq_iInf_len] at hlt
        obtain ⟨R, hR⟩ := iInf_lt_iff.1 hlt
        obtain ⟨hRc, hR⟩ := iInf_lt_iff.1 hR
        obtain ⟨hR0, hR⟩ := iInf_lt_iff.1 hR
        obtain ⟨hR1, hR⟩ := iInf_lt_iff.1 hR
        obtain ⟨-, hRlen⟩ := iInf_lt_iff.1 hR
        have hRA : ∀ t ∈ Icc (0 : ℝ) 1, R t ∈ ann z r (3 * r) := by
          intro t ht
          by_contra htA
          have h1 := S6a.collar_le_len D₀ hAo hVzA hAW hcol hRc (hR0 ▸ hPσ₁) ht htA
          have hbs : ENNReal.ofReal (b * s) ≤ ENNReal.ofReal (a * s) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hba hs.le)
          exact absurd ((h1.trans_lt hRlen).trans_le hbs) (lt_irrefl _)
        have hint := D₀.internal_le_len zero_le_one hRc (fun t ht => hAB (hRA t ht))
        rw [hR0, hR1] at hint
        exact absurd (hint.trans_lt hRlen) (not_lt.2 hthr)
      calc ENNReal.ofReal b = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (b * s) := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.2 hs.le)]
            congr 1
            field_simp
        _ ≤ ENNReal.ofReal s⁻¹ * D₀.internal (ann z (r / 2) (5 * r)) (P σ₁) (P σ₂) :=
            mul_le_mul' le_rfl hW
    -- (4) the shortcut of (ii′), rescaled
    obtain ⟨u, v, hu, huv, hv, hcL, S, hSc, hS0, hS1, hSA, hSlen⟩ :=
      hii Q hQc.continuousOn hQ0V hQ1V hmin hthr'
    have hd : 0 ≤ σ₂ - σ₁ := sub_nonneg.2 hσ₁₂
    have hτ₁ : σ₁ ≤ σ₁ + u * (σ₂ - σ₁) := le_add_of_nonneg_right (mul_nonneg hu hd)
    have hτ₁₂ : σ₁ + u * (σ₂ - σ₁) ≤ σ₁ + v * (σ₂ - σ₁) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right huv hd)
    have hτ₂ : σ₁ + v * (σ₂ - σ₁) ≤ σ₂ := by
      have := mul_le_of_le_one_left hd hv
      linarith
    refine ⟨σ₁ + u * (σ₂ - σ₁), σ₁ + v * (σ₂ - σ₁), hτ₁, hτ₁₂, hτ₂, ?_, ?_⟩
    · rw [hWL u v hu huv hv] at hcL
      calc ENNReal.ofReal (c * s) = ENNReal.ofReal s * ENNReal.ofReal c := S6a.ofReal_mul_scale hs c
        _ ≤ ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ *
              D'.len P (σ₁ + u * (σ₂ - σ₁)) (σ₁ + v * (σ₂ - σ₁))) := mul_le_mul' le_rfl hcL
        _ = D'.len P (σ₁ + u * (σ₂ - σ₁)) (σ₁ + v * (σ₂ - σ₁)) :=
            S6a.ofReal_mul_ofReal_inv_mul hs _
    · have hS' := S6a.weightedLengthWith_cfg hDt' hr hEt' hSc (fun t _ => hwg (S t))
      have hPS0 : r • (S 0 : Rd d) + z = P (σ₁ + u * (σ₂ - σ₁)) := by
        rw [hS0]
        exact hQP u ⟨hu, huv.trans hv⟩
      have hPS1 : r • (S 1 : Rd d) + z = P (σ₁ + v * (σ₂ - σ₁)) := by
        rw [hS1]
        exact hQP v ⟨hu.trans huv, hv⟩
      have hint := Dt'.internal_le_len zero_le_one (S6a.continuousOn_realize hSc)
        (fun t ht => hAB (S6a.affine_mem_ann13 hr z (hSA ht)))
      simp only [hPS0, hPS1] at hint
      calc Dt'.internal (ball z (4 * r)) (P (σ₁ + u * (σ₂ - σ₁))) (P (σ₁ + v * (σ₂ - σ₁)))
          ≤ Dt'.len (fun t => r • (S t : Rd d) + z) 0 1 := hint
        _ = ENNReal.ofReal s * weightedLengthWith Et w S 0 1 := by
            rw [hS', S6a.ofReal_mul_ofReal_inv_mul hs]
        _ ≤ ENNReal.ofReal s * (ENNReal.ofReal c' * weightedLengthWith E w Q u v) :=
            mul_le_mul' le_rfl hSlen
        _ = ENNReal.ofReal c' * D'.len P (σ₁ + u * (σ₂ - σ₁)) (σ₁ + v * (σ₂ - σ₁)) := by
            rw [hWL u v hu huv hv, mul_left_comm, S6a.ofReal_mul_ofReal_inv_mul hs]
  case T4 =>
    intro Z hzZ hZJ hZd D'' hD'' P hP
    -- the total discount agrees with `f_{z,r,j}` on `B_{4r}(z)`
    have hF : ∀ x ∈ ball z (4 * r), (∑ q ∈ Z, bumpAt (f' q.2) r q.1) x = bumpAt (f' j) r z x :=
      fun x hx => S6a.sum_bumpAt_eq hf'supp hr hzZ hZJ hZd hx
    have hgF : ∀ x ∈ closure (ann z r (3 * r)), x ∉ (fun x : Rd d => r • x + z) '' V →
        (-(∑ q ∈ Z, bumpAt (f' q.2) r q.1)) x = 0 := by
      intro x hx hxV
      rw [ContinuousMap.neg_apply, hF x (S6a.closure_ann_subset_ball hr z hx),
        S6a.bumpAt_eq_zero_of_notMem hfV0 hr.ne' z hxV, neg_zero]
    have hwF : ∀ u : ↥(ann (0 : Rd d) (1 / 2) 5), (u : Rd d) ∈ ann (0 : Rd d) 1 3 →
        w u = Real.exp (ξ * (-(∑ q ∈ Z, bumpAt (f' q.2) r q.1)) (r • (u : Rd d) + z)) := by
      intro u hu
      rw [ContinuousMap.neg_apply, hF _ (hAB (S6a.affine_mem_ann13 hr z hu)), hw u,
        bumpAt_affine _ hr.ne', mul_neg]
    -- segments of the geodesic between collector times cost at most `a s`
    have hcostZ : ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ 1 →
        P τ₁ ∈ closure ((fun x : Rd d => r • x + z) '' V) →
        P τ₂ ∈ closure ((fun x : Rd d => r • x + z) '' V) →
        D''.len P τ₁ τ₂ ≤ ENNReal.ofReal (a * s) := by
      intro τ₁ τ₂ h0 h12 h2 hP1 hP2
      exact (S6a.len_le_of_isGeod hP h0 h12 h2).trans
        ((D''.ofReal_le_internal (ann z r (3 * r)) _ _).trans (hT2gen _ D'' hD'' hwF _ hP1 _ hP2))
    refine ⟨?_, ?_⟩
    · -- single excursion
      intro τ₁ τ₂ τ h0 h1 h2 h3 hP1 hP2
      by_contra hτB
      have hτA : P τ ∉ ann z r (3 * r) := fun h => hτB (hAB h)
      have h2' := S6a.depart_return hD'' hAo hVzo hVzA hAW hgF hcol
        (hP.1.mono (Icc_subset_Icc h0 h3)) hP1 hP2 ⟨h1, h2⟩ hτA
      exact S6a.not_add_self_le has0 hastop (h2'.trans (hcostZ τ₁ τ₂ h0 (h1.trans h2) h3 hP1 hP2))
    · -- occupation
      unfold occLen
      refine iSup_le fun I => iSup_le fun hI => iSup_le fun hIc => ?_
      rcases I.eq_empty_or_nonempty with hIe | ⟨p₀, hp₀⟩
      · rw [hIe, Finset.sum_empty]
        exact bot_le
      -- the first and last collector times `σ₁ ≤ σ₂`
      set T : Set ℝ := Icc 0 1 ∩ P ⁻¹' closure ((fun x : Rd d => r • x + z) '' V) with hTdef
      have hTc : IsClosed T := hP.1.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
      obtain ⟨hp₀0, hp₀12, hp₀1, hp₀V⟩ := hIc p₀ hp₀
      have hTne : T.Nonempty :=
        ⟨p₀.1, ⟨hp₀0, hp₀12.trans hp₀1⟩, subset_closure (hp₀V p₀.1 ⟨le_rfl, hp₀12⟩)⟩
      have hTb : BddBelow T := ⟨0, fun x hx => hx.1.1⟩
      have hTa : BddAbove T := ⟨1, fun x hx => hx.1.2⟩
      have hσ₁ : sInf T ∈ T := hTc.csInf_mem hTne hTb
      have hσ₂ : sSup T ∈ T := hTc.csSup_mem hTne hTa
      have hIσ : ∀ p ∈ I, sInf T ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ sSup T := by
        intro p hp
        obtain ⟨hp0, hp12, hp1, hpV⟩ := hIc p hp
        exact ⟨csInf_le hTb ⟨⟨hp0, hp12.trans hp1⟩, subset_closure (hpV p.1 ⟨le_rfl, hp12⟩)⟩, hp12,
          le_csSup hTa ⟨⟨hp0.trans hp12, hp1⟩, subset_closure (hpV p.2 ⟨hp12, le_rfl⟩)⟩⟩
      have hσ₁₂ : sInf T ≤ sSup T := csInf_le hTb hσ₂
      -- in `V_z` the weight is at least `e^{−ξ M_f}`
      have hocc : ∀ p ∈ I, D₀.len P p.1 p.2 ≤
          ENNReal.ofReal (Real.exp (ξ * Mf)) * D''.len P p.1 p.2 := by
        intro p hp
        obtain ⟨hp0, hp12, hp1, hpV⟩ := hIc p hp
        refine S6a.len_le_exp_mul_len_weyl hD'' hp12 (hP.1.mono (Icc_subset_Icc hp0 hp1)) ?_
        intro t ht
        have hPt : P t ∈ ball z (4 * r) := hAB (hVzA (subset_closure (hpV t ht)))
        rw [ContinuousMap.neg_apply, hF _ hPt, bumpAt_apply, mul_neg]
        exact neg_le_neg (mul_le_mul_of_nonneg_left (hfM _) hξ)
      calc ∑ p ∈ I, D₀.len P p.1 p.2
          ≤ ∑ p ∈ I, ENNReal.ofReal (Real.exp (ξ * Mf)) * D''.len P p.1 p.2 :=
            Finset.sum_le_sum hocc
        _ = ENNReal.ofReal (Real.exp (ξ * Mf)) * ∑ p ∈ I, D''.len P p.1 p.2 :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ ENNReal.ofReal (Real.exp (ξ * Mf)) * D''.len P (sInf T) (sSup T) :=
            mul_le_mul' le_rfl (S6a.sum_len_le_of_pairwiseDisjoint D'' P _ I hI _ hIσ)
        _ ≤ ENNReal.ofReal (Real.exp (ξ * Mf)) * ENNReal.ofReal (a * s) :=
            mul_le_mul' le_rfl (hcostZ _ _ hσ₁.1.1 hσ₁₂ hσ₂.1.2 hσ₁.2 hσ₂.2)
        _ = ENNReal.ofReal (a * Real.exp (ξ * Mf) * s) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 1
            ring

end HigherDimLQGMetric
