import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaMeshBudget

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem buffered_inner_internal_upper
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    {W V K : Set ℂ} (hWV : W ⊆ V)
    (hWK : W ⊆ interior K)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hsmall : SmallAnnulusCosts G D K V)
    {r R : ℝ≥0∞} (hrR : r < R)
    (hR : R < ⨅ p ∈ K ×ˢ frontier V, D p)
    (hrpos : 0 < r) (hrfin : r < ∞)
    (x y : W) {d C : ℝ}
    (hd : 0 < d) (hxy : D.internal W (x, y) = ENNReal.ofReal d)
    (hC : d < C) :
    ∃ x' y' : ℕ → V,
      Tendsto x' atTop (𝓝 ⟨(x : ℂ), hWV x.property⟩) ∧
      Tendsto y' atTop (𝓝 ⟨(y : ℂ), hWV y.property⟩) ∧
      ∀ᶠ n in atTop, (G n).internal V (x' n, y' n) < ENNReal.ofReal C := by
  have hrreal : 0 < r.toReal := ENNReal.toReal_pos hrpos.ne' hrfin.ne
  obtain ⟨N, q, hq, hmesh⟩ :=
    exists_uniform_mesh_budget hd hrreal hC
  have hbudget : D.internal W (x, y) < ENNReal.ofReal (d + q) := by
    rw [hxy]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨P, a, b, hP, hPW, hPa, hPb, hPlen⟩ :=
    Uniqueness.Objects.Producer.exists_curve_of_internal_lt
      D x.property y.property hbudget
  have hPfin : D.len P a b ≠ ∞ := by
    exact ne_top_of_lt (lt_trans hPlen ENNReal.ofReal_lt_top)
  obtain ⟨Q, hQ, hunit, hQ0, hQL, hQW, hQlen⟩ :=
    exists_unit_speed_buffered_curve D hP hPW hPfin
  let L : ℝ := (D.len P a b).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hlenReal : ENNReal.ofReal L = D.len P a b :=
    ENNReal.ofReal_toReal hPfin
  have hbase : D.internal W (x, y) ≤ D.len P a b := by
    have h := internal_trace_pair_le_len D hP hPW
      ⟨le_rfl, hP.1⟩ ⟨hP.1, le_rfl⟩
    simpa only [hPa, hPb] using h
  have hdL : d ≤ L := by
    apply (ENNReal.ofReal_le_ofReal_iff hL).mp
    rw [← hxy, hlenReal]
    exact hbase
  have hLupper : L < d + q := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp
    rw [hlenReal]
    exact hPlen
  obtain ⟨hstepLowerReal, hstepUpperReal, htotalReal⟩ :=
    hmesh L hdL hLupper
  have ha : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hstepLower : ENNReal.ofReal q ≤
      ENNReal.ofReal (L / (N + 1 : ℝ)) :=
    ENNReal.ofReal_le_ofReal hstepLowerReal
  have hstepUpper : ENNReal.ofReal (L / (N + 1 : ℝ)) < r := by
    rw [← ENNReal.ofReal_toReal hrfin.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff hrreal).mpr hstepUpperReal
  have hB : ENNReal.ofReal (L / (N + 1 : ℝ)) <
      ENNReal.ofReal ((L + q) / (N + 1 : ℝ)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) ha)).mpr
    apply (div_lt_div_iff_of_pos_right ha).mpr
    linarith
  have hδ : 0 < q / (N + 1 : ℝ) := div_pos hq ha
  have hnear : D.len Q 0 L <
      D.internal W
        (⟨Q 0, hQW 0 ⟨le_rfl, hQ.1⟩⟩,
          ⟨Q L, hQW L ⟨hQ.1, le_rfl⟩⟩) + ENNReal.ofReal q := by
    have hends : D.internal W
        (⟨Q 0, hQW 0 ⟨le_rfl, hQ.1⟩⟩,
          ⟨Q L, hQW L ⟨hQ.1, le_rfl⟩⟩) = D.internal W (x, y) := by
      have hfirst : (⟨Q 0, hQW 0 ⟨le_rfl, hQ.1⟩⟩ : W) = x :=
        Subtype.ext (hQ0.trans hPa)
      have hlast : (⟨Q L, hQW L ⟨hQ.1, le_rfl⟩⟩ : W) = y :=
        Subtype.ext (hQL.trans hPb)
      rw [hfirst, hlast]
    rw [hQlen, hends, hxy, ← ENNReal.ofReal_add hd.le hq.le]
    exact hPlen
  have hQfin : D.len Q 0 L < ∞ := by rw [hQlen]; exact hPfin.lt_top
  obtain ⟨x', y', hx', hy', hbound⟩ :=
    uniform_buffered_inner_path_recovery hG hLen hPath hforget hWV hV
      hK hfront hsmall hrR hR hrfin hQ hunit hQW
      (fun u hu => hWK (hQW u hu)) hQfin hnear N
      hstepLower hstepUpper hB hδ
  have htotal : (N + 1) • ENNReal.ofReal ((L + q) / (N + 1 : ℝ)) +
      N • ENNReal.ofReal (q / (N + 1 : ℝ)) < ENNReal.ofReal C :=
    uniform_mesh_total_lt N hL hq htotalReal
  refine ⟨x', y', ?_, ?_, ?_⟩
  · have hxeq : (⟨Q 0, hWV (hQW 0 ⟨le_rfl, hQ.1⟩)⟩ : V) =
        ⟨(x : ℂ), hWV x.property⟩ := Subtype.ext (hQ0.trans hPa)
    simpa only [hxeq] using hx'
  · have hyeq : (⟨Q L, hWV (hQW L ⟨hQ.1, le_rfl⟩)⟩ : V) =
        ⟨(y : ℂ), hWV y.property⟩ := Subtype.ext (hQL.trans hPb)
    change Tendsto y' atTop
      (𝓝 (⟨Q L, hWV (hQW L ⟨hQ.1, le_rfl⟩)⟩ : V)) at hy'
    rw [hyeq] at hy'
    exact hy'
  · filter_upwards [hbound] with n hn
    exact hn.trans_lt htotal

theorem buffered_inner_internal_upper_real
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    {W V K : Set ℂ} (hWV : W ⊆ V)
    (hWK : W ⊆ interior K)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hsmall : SmallAnnulusCosts G D K V)
    {r R : ℝ≥0∞} (hrR : r < R)
    (hR : R < ⨅ p ∈ K ×ˢ frontier V, D p)
    (hrpos : 0 < r) (hrfin : r < ∞)
    (x y : W) {C : ℝ}
    (hC : 0 < C)
    (hxy : D.internal W (x, y) < ENNReal.ofReal C) :
    ∃ x' y' : ℕ → V,
      Tendsto x' atTop (𝓝 ⟨(x : ℂ), hWV x.property⟩) ∧
      Tendsto y' atTop (𝓝 ⟨(y : ℂ), hWV y.property⟩) ∧
      ∀ᶠ n in atTop, (G n).internal V (x' n, y' n) < ENNReal.ofReal C := by
  by_cases hzero : D.internal W (x, y) = 0
  · have hsame : x = y := (D.isExtMetric_internal W).2.1 x y hzero
    subst y
    let xv : V := ⟨(x : ℂ), hWV x.property⟩
    refine ⟨fun _ => xv, fun _ => xv, tendsto_const_nhds,
      tendsto_const_nhds, ?_⟩
    filter_upwards [] with n
    have hdiag : (G n).internal V (xv, xv) = 0 :=
      (G n).isExtMetric_internal V |>.1 xv
    rw [hdiag]
    exact ENNReal.ofReal_pos.mpr hC
  · have hfin : D.internal W (x, y) ≠ ∞ :=
      ne_top_of_lt (lt_trans hxy ENNReal.ofReal_lt_top)
    have hdpos : 0 < (D.internal W (x, y)).toReal := by
      apply ENNReal.toReal_pos
      · exact (pos_iff_ne_zero).mpr hzero |>.ne'
      · exact hfin
    have hdC : (D.internal W (x, y)).toReal < C := by
      apply (ENNReal.ofReal_lt_ofReal_iff hC).mp
      rw [ENNReal.ofReal_toReal hfin]
      exact hxy
    exact buffered_inner_internal_upper hG hLen hPath hforget hWV hWK
      hV hK hfront hsmall hrR hR hrpos hrfin x y hdpos
      (ENNReal.ofReal_toReal hfin).symm hdC

end SupercriticalLQGUniqueness.B2.PfeAxioms
