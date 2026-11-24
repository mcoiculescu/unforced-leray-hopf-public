import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists.RegularOfSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollTendsto
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.SupBddByXNorm
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Leaf 1 (`PartIII-a:T21/c3/3/1/1/2/2/2/1/1`): `FreeSpSmoothRep`

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.

Constructs a `c`-periodic spatially `C^∞` version `φ' r x = lim_{n → ∞} cellMoll n (φ r) x` on
`[t, s)` for any family `φ` satisfying `∀ k, AdjHkOn c m k (Ico t s) φ` (`0 < c`, `t < s`), and
proves joint continuity of `(r, x) ↦ adjSpatial w (φ' r) x` on `[t, s) × ℝ²` for every spatial
word `w`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub

namespace FreeSpSmoothRepAux

private theorem wordsLe2_len {w' : List (Fin 2)} (hw' : w' ∈ wordsLe2) : w'.length ≤ 2 := by
  simp [wordsLe2] at hw'
  rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Pointwise bound on `{‖x‖ ≤ R}` for a smooth `c`-periodic field from a uniform bound `δ ≥ 0` on
`xNorm c (-m) (adjSpatial w' g)` over `w' ∈ wordsLe2`. -/
private theorem norm_le_of_wordsLe2 {c m R C₁ δ : ℝ} (hC₁0 : 0 ≤ C₁) (hδ0 : 0 ≤ δ)
    (hC₁ : ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g →
      (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) → ∀ x : ℝ × ℝ, ‖x‖ ≤ R →
        ENNReal.ofReal ‖g x‖ ≤
          ENNReal.ofReal C₁ * (wordsLe2.map fun w' => xNorm c (-m) (adjSpatial w' g)).sum)
    {g : ℝ × ℝ → ℂ} (hgs : ContDiff ℝ ∞ g) (hgp : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x)
    (hbd : ∀ w' ∈ wordsLe2, xNorm c (-m) (adjSpatial w' g) ≤ ENNReal.ofReal δ)
    {x : ℝ × ℝ} (hx : ‖x‖ ≤ R) :
    ‖g x‖ ≤ C₁ * (7 * δ) := by
  have hsum : (wordsLe2.map fun w' => xNorm c (-m) (adjSpatial w' g)).sum ≤
      7 * ENNReal.ofReal δ := by
    have h := List.sum_le_card_nsmul
      (wordsLe2.map fun w' => xNorm c (-m) (adjSpatial w' g))
      (ENNReal.ofReal δ) (by
        intro a ha
        obtain ⟨w', hw', rfl⟩ := List.mem_map.1 ha
        exact hbd w' hw')
    simpa [wordsLe2, nsmul_eq_mul] using h
  have hfin : ENNReal.ofReal ‖g x‖ ≤ ENNReal.ofReal (C₁ * (7 * δ)) := by
    calc ENNReal.ofReal ‖g x‖
        ≤ ENNReal.ofReal C₁ * (wordsLe2.map fun w' => xNorm c (-m) (adjSpatial w' g)).sum :=
          hC₁ g hgs hgp x hx
      _ ≤ ENNReal.ofReal C₁ * (7 * ENNReal.ofReal δ) := by gcongr
      _ = ENNReal.ofReal (C₁ * (7 * δ)) := by
          rw [ENNReal.ofReal_mul hC₁0, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7)]
          simp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin

/-- Pointwise limit of the `w`-th spatial partial of `cellMoll n f`. -/
private def mollLim (w : List (Fin 2)) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  limUnder atTop (fun n : ℕ => adjSpatial w (cellMoll n f) x)

/-- Uniform Cauchy estimate on `{‖x‖ ≤ R}` for `n ↦ adjSpatial w (cellMoll n f)` when `f` has a
periodic cell jet of order `|w| + 2`. -/
private theorem moll_unif_cauchy {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} (w : List (Fin 2))
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : IsCellJet c m (w.length + 2) f D) (R : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n₁ ≥ N, ∀ n₂ ≥ N, ∀ x : ℝ × ℝ, ‖x‖ ≤ R →
      ‖adjSpatial w (cellMoll n₁ f) x - adjSpatial w (cellMoll n₂ f) x‖ ≤ ε := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := _root_.supBddByXNorm c m R hc
  set δ : ℝ := ε / (7 * (C₁ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x := by
    rw [← hJ.base]; exact hJ.periodic [] (Nat.zero_le _)
  have hfm : MemLp f 2 (B0579.cellMeasure c (-m)) := by
    rw [← hJ.base]; exact hJ.memX [] (Nat.zero_le _)
  have hev_w : ∀ w' ∈ wordsLe2.toFinset, ∀ᶠ n : ℕ in atTop,
      xNorm c (-m) (cellMoll n (D (w' ++ w)) - D (w' ++ w)) ≤ ENNReal.ofReal (δ / 2) := by
    intro w' hw'
    have hlen : (w' ++ w).length ≤ w.length + 2 := by
      rw [List.length_append]
      have := wordsLe2_len (List.mem_toFinset.1 hw')
      omega
    have hT := cellMollTendsto c m (D (w' ++ w)) hc (hJ.periodic _ hlen) (hJ.memX _ hlen)
    exact ENNReal.tendsto_nhds_zero.1 hT (ENNReal.ofReal (δ / 2)) (ENNReal.ofReal_pos.2 hδ2)
  have hev_all : ∀ᶠ n : ℕ in atTop, ∀ w' ∈ wordsLe2.toFinset,
      xNorm c (-m) (cellMoll n (D (w' ++ w)) - D (w' ++ w)) ≤ ENNReal.ofReal (δ / 2) :=
    (Filter.eventually_all_finset wordsLe2.toFinset).2 hev_w
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev_all
  refine ⟨N, fun n₁ hn₁ n₂ hn₂ x hx => ?_⟩
  obtain ⟨hs₁, hp₁, -⟩ := cellMollSmooth c m n₁ f hc hfp hfm
  obtain ⟨hs₂, hp₂, -⟩ := cellMollSmooth c m n₂ f hc hfp hfm
  have hws₁ : ContDiff ℝ ∞ (adjSpatial w (cellMoll n₁ f)) := st_contDiff_adjSpatial hs₁ w
  have hws₂ : ContDiff ℝ ∞ (adjSpatial w (cellMoll n₂ f)) := st_contDiff_adjSpatial hs₂ w
  have hwp₁ := st_adjSpatial_periodic hp₁ w
  have hwp₂ := st_adjSpatial_periodic hp₂ w
  let g : ℝ × ℝ → ℂ := fun y => adjSpatial w (cellMoll n₁ f) y - adjSpatial w (cellMoll n₂ f) y
  have hgs : ContDiff ℝ ∞ g := hws₁.sub hws₂
  have hgp : ∀ y : ℝ × ℝ, g (y.1 + c, y.2) = g y := fun y => by
    simp only [g, hwp₁ y, hwp₂ y]
  have hbd : ∀ w' ∈ wordsLe2, xNorm c (-m) (adjSpatial w' g) ≤ ENNReal.ofReal δ := by
    intro w' hw'
    have hlen : (w' ++ w).length ≤ w.length + 2 := by
      rw [List.length_append]; have := wordsLe2_len hw'; omega
    let u := D (w' ++ w)
    have hup := hJ.periodic (w' ++ w) hlen
    have hum := hJ.memX (w' ++ w) hlen
    have hums₁ := (cellMollSmooth c m n₁ u hc hup hum).1.continuous.aestronglyMeasurable
      (μ := B0579.cellMeasure c (-m))
    have hums₂ := (cellMollSmooth c m n₂ u hc hup hum).1.continuous.aestronglyMeasurable
      (μ := B0579.cellMeasure c (-m))
    have hEqg : adjSpatial w' g = cellMoll n₁ u - cellMoll n₂ u := by
      change adjSpatial w' (fun y => adjSpatial w (cellMoll n₁ f) y -
        adjSpatial w (cellMoll n₂ f) y) = _
      rw [st_adjSpatial_sub hws₁ hws₂ w', adjSpatial_append, adjSpatial_append,
        adjSpatial_cellMoll_jet cellMollWeakDeriv hc hJ n₁ (w' ++ w) hlen,
        adjSpatial_cellMoll_jet cellMollWeakDeriv hc hJ n₂ (w' ++ w) hlen]
      rfl
    have hsplit : cellMoll n₁ u - cellMoll n₂ u = (cellMoll n₁ u - u) - (cellMoll n₂ u - u) := by
      abel
    rw [hEqg, hsplit]
    unfold xNorm
    have htri := eLpNorm_sub_le (hums₁.sub hum.1) (hums₂.sub hum.1) (p := 2) (by norm_num)
    have hb₁ := hN n₁ hn₁ w' (List.mem_toFinset.2 hw')
    have hb₂ := hN n₂ hn₂ w' (List.mem_toFinset.2 hw')
    calc eLpNorm ((cellMoll n₁ u - u) - (cellMoll n₂ u - u)) 2 (B0579.cellMeasure c (-m))
        ≤ eLpNorm (cellMoll n₁ u - u) 2 (B0579.cellMeasure c (-m)) +
            eLpNorm (cellMoll n₂ u - u) 2 (B0579.cellMeasure c (-m)) := htri
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hb₁ hb₂
      _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add hδ2.le hδ2.le, add_halves]
  have hle := norm_le_of_wordsLe2 hC₁0 hδ.le hC₁ hgs hgp hbd hx
  have hcalc : C₁ * (7 * δ) ≤ ε := by
    have h1 : C₁ ≤ C₁ + 1 := by linarith
    have h2 : C₁ * (7 * δ) ≤ (C₁ + 1) * (7 * δ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (C₁ + 1) * (7 * δ) = ε := by
      simp only [δ]
      have hne : 7 * (C₁ + 1) ≠ 0 := by positivity
      field_simp
    linarith
  exact hle.trans hcalc

/-- Pointwise convergence of `n ↦ adjSpatial w (cellMoll n f) x` to `mollLim w f x`. -/
private theorem tendsto_mollLim {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} (w : List (Fin 2))
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : IsCellJet c m (w.length + 2) f D) (x : ℝ × ℝ) :
    Tendsto (fun n : ℕ => adjSpatial w (cellMoll n f) x) atTop (𝓝 (mollLim w f x)) := by
  have hcauchy : CauchySeq (fun n : ℕ => adjSpatial w (cellMoll n f) x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := moll_unif_cauchy hc w hJ ‖x‖ (half_pos hε)
    refine ⟨N, fun n₁ hn₁ n₂ hn₂ => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hN n₁ hn₁ n₂ hn₂ x le_rfl) (half_lt_self hε)
  exact hcauchy.tendsto_limUnder

/-- Uniform convergence on `Metric.ball 0 R` of `n ↦ adjSpatial w (cellMoll n f)` to `mollLim w f`. -/
private theorem tendstoUniformlyOn_mollLim {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (w : List (Fin 2)) {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hJ : IsCellJet c m (w.length + 2) f D) (R : ℝ) :
    TendstoUniformlyOn (fun n : ℕ => adjSpatial w (cellMoll n f)) (mollLim w f)
      atTop (Metric.ball (0 : ℝ × ℝ) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := moll_unif_cauchy hc w hJ R (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n₁ hn₁ x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact hx.le
  have hlim : Tendsto (fun n₂ : ℕ => ‖adjSpatial w (cellMoll n₁ f) x -
      adjSpatial w (cellMoll n₂ f) x‖) atTop
      (𝓝 ‖adjSpatial w (cellMoll n₁ f) x - mollLim w f x‖) :=
    ((tendsto_const_nhds.sub (tendsto_mollLim hc w hJ x)).norm)
  have hle : ‖adjSpatial w (cellMoll n₁ f) x - mollLim w f x‖ ≤ ε / 2 :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨N, fun n₂ hn₂ => hN n₁ hn₁ n₂ hn₂ x hxR⟩)
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hle (half_lt_self hε)

/-- Continuity of `mollLim w f` when `f` has periodic cell jets of all orders. -/
private theorem continuous_mollLim {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hJet : ∀ k : ℕ, ∃ D, IsCellJet c m k f D) (w : List (Fin 2)) :
    Continuous (mollLim w f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨D, hJ⟩ := hJet (w.length + 2)
  have hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x := by
    rw [← hJ.base]; exact hJ.periodic [] (Nat.zero_le _)
  have hfm : MemLp f 2 (B0579.cellMeasure c (-m)) := by
    rw [← hJ.base]; exact hJ.memX [] (Nat.zero_le _)
  set R : ℝ := ‖x₀‖ + 1
  have hx₀ : x₀ ∈ Metric.ball (0 : ℝ × ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right]; simp [R]
  have hU := tendstoUniformlyOn_mollLim hc w hJ R
  have hcont : ContinuousOn (mollLim w f) (Metric.ball (0 : ℝ × ℝ) R) :=
    hU.continuousOn ((Eventually.of_forall fun n =>
      (st_contDiff_adjSpatial (cellMollSmooth c m n f hc hfp hfm).1 w).continuous.continuousOn).frequently)
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds hx₀)

/-- Linear functional on `ℝ × ℝ` constructed from two partial-derivative values in `ℂ`. -/
private def mkFDeriv (a b : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

private theorem mkFDeriv_apply (a b : ℂ) (v : ℝ × ℝ) :
    mkFDeriv a b v = v.1 • a + v.2 • b := rfl

private theorem norm_mkFDeriv_sub (a b a' b' : ℂ) :
    ‖mkFDeriv a b - mkFDeriv a' b'‖ ≤ ‖a - a'‖ + ‖b - b'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖mkFDeriv a b v - mkFDeriv a' b' v‖ ≤ (‖a - a'‖ + ‖b - b'‖) * ‖v‖
  rw [mkFDeriv_apply, mkFDeriv_apply]
  have heq : (v.1 • a + v.2 • b) - (v.1 • a' + v.2 • b') =
      v.1 • (a - a') + v.2 • (b - b') := by module
  rw [heq]
  have hv1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have hv2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  calc ‖v.1 • (a - a') + v.2 • (b - b')‖
      ≤ ‖v.1 • (a - a')‖ + ‖v.2 • (b - b')‖ := norm_add_le _ _
    _ = ‖v.1‖ * ‖a - a'‖ + ‖v.2‖ * ‖b - b'‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * ‖a - a'‖ + ‖v‖ * ‖b - b'‖ := by gcongr
    _ = (‖a - a'‖ + ‖b - b'‖) * ‖v‖ := by ring

private theorem dir_decomp (v : ℝ × ℝ) : v = v.1 • B0579.dir 0 + v.2 • B0579.dir 1 := by
  ext <;> simp [B0579.dir]

private theorem hasFDerivAt_mkFDeriv {G : ℝ × ℝ → ℂ} (hG : Differentiable ℝ G) (x : ℝ × ℝ) :
    HasFDerivAt G (mkFDeriv (pdCx 0 G x) (pdCx 1 G x)) x := by
  have heq : fderiv ℝ G x = mkFDeriv (pdCx 0 G x) (pdCx 1 G x) :=
    ContinuousLinearMap.ext fun v => by
      conv_lhs => rw [dir_decomp v]
      rw [map_add, map_smul, map_smul]
      rfl
  rw [← heq]
  exact (hG x).hasFDerivAt

/-- Fréchet derivative of `mollLim w f` via `hasFDerivAt_of_tendstoUniformlyOn`. -/
private theorem hasFDerivAt_mollLim {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hJet : ∀ k : ℕ, ∃ D, IsCellJet c m k f D) (w : List (Fin 2)) (x₀ : ℝ × ℝ) :
    HasFDerivAt (mollLim w f)
      (mkFDeriv (mollLim (0 :: w) f x₀) (mollLim (1 :: w) f x₀)) x₀ := by
  obtain ⟨D, hJ⟩ := hJet (w.length + 2)
  obtain ⟨D₀, hJ₀⟩ := hJet ((0 :: w).length + 2)
  obtain ⟨D₁, hJ₁⟩ := hJet ((1 :: w).length + 2)
  have hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x := by
    rw [← hJ.base]; exact hJ.periodic [] (Nat.zero_le _)
  have hfm : MemLp f 2 (B0579.cellMeasure c (-m)) := by
    rw [← hJ.base]; exact hJ.memX [] (Nat.zero_le _)
  set R : ℝ := ‖x₀‖ + 1
  have hx₀ : x₀ ∈ Metric.ball (0 : ℝ × ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right]; simp [R]
  have hU₀ := tendstoUniformlyOn_mollLim hc (0 :: w) hJ₀ R
  have hU₁ := tendstoUniformlyOn_mollLim hc (1 :: w) hJ₁ R
  have hUf' : TendstoUniformlyOn
      (fun (n : ℕ) (x : ℝ × ℝ) =>
        mkFDeriv (adjSpatial (0 :: w) (cellMoll n f) x) (adjSpatial (1 :: w) (cellMoll n f) x))
      (fun x : ℝ × ℝ => mkFDeriv (mollLim (0 :: w) f x) (mollLim (1 :: w) f x))
      atTop (Metric.ball (0 : ℝ × ℝ) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he₀ := Metric.tendstoUniformlyOn_iff.1 hU₀ (ε / 2) (half_pos hε)
    have he₁ := Metric.tendstoUniformlyOn_iff.1 hU₁ (ε / 2) (half_pos hε)
    filter_upwards [he₀, he₁] with n hn₀ hn₁ x hx
    rw [dist_eq_norm]
    have hb := norm_mkFDeriv_sub (mollLim (0 :: w) f x) (mollLim (1 :: w) f x)
      (adjSpatial (0 :: w) (cellMoll n f) x) (adjSpatial (1 :: w) (cellMoll n f) x)
    have hd₀ : ‖mollLim (0 :: w) f x - adjSpatial (0 :: w) (cellMoll n f) x‖ < ε / 2 := by
      simpa [dist_eq_norm] using hn₀ x hx
    have hd₁ : ‖mollLim (1 :: w) f x - adjSpatial (1 :: w) (cellMoll n f) x‖ < ε / 2 := by
      simpa [dist_eq_norm] using hn₁ x hx
    linarith
  refine hasFDerivAt_of_tendstoUniformlyOn (l := atTop) Metric.isOpen_ball hUf'
    (fun n x _ => ?_) (fun x _ => tendsto_mollLim hc w hJ x) hx₀
  have hdiff : Differentiable ℝ (adjSpatial w (cellMoll n f)) :=
    (st_contDiff_adjSpatial (cellMollSmooth c m n f hc hfp hfm).1 w).differentiable (by simp)
  exact hasFDerivAt_mkFDeriv hdiff x

/-- `mollLim [] f` is `C^∞` on `ℝ²` when `f` has periodic cell jets of all orders. -/
private theorem contDiff_mollLim_nil {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hJet : ∀ k : ℕ, ∃ D, IsCellJet c m k f D) :
    ContDiff ℝ ∞ (mollLim [] f) := by
  have hall : ∀ (k : ℕ) (w : List (Fin 2)), ContDiff ℝ k (mollLim w f) := by
    intro k
    induction k with
    | zero =>
      intro w
      exact contDiff_zero.2 (continuous_mollLim hc hJet w)
    | succ k ih =>
      intro w
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun x => (hasFDerivAt_mollLim hc hJet w x).differentiableAt,
        fun hω => by simp at hω, fun y => ?_⟩
      have heq : (fun x => fderiv ℝ (mollLim w f) x y) =
          fun x => y.1 • mollLim (0 :: w) f x + y.2 • mollLim (1 :: w) f x := by
        funext x
        rw [(hasFDerivAt_mollLim hc hJet w x).fderiv]
        rfl
      rw [heq]
      exact ((ih (0 :: w)).const_smul y.1).add ((ih (1 :: w)).const_smul y.2)
  exact contDiff_infty.2 fun k => hall k []

/-- `mollLim [] f` equals `f` a.e. wrt `volume` on `ℝ²`. -/
private theorem mollLim_ae_eq {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hJet : ∀ k : ℕ, ∃ D, IsCellJet c m k f D)
    (hper' : ∀ x : ℝ × ℝ, mollLim [] f (x.1 + c, x.2) = mollLim [] f x) :
    mollLim [] f =ᵐ[volume] f := by
  obtain ⟨D₂, hJ₂⟩ := hJet 2
  have hfp : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x := by
    rw [← hJ₂.base]; exact hJ₂.periodic [] (Nat.zero_le _)
  have hfm : MemLp f 2 (B0579.cellMeasure c (-m)) := by
    rw [← hJ₂.base]; exact hJ₂.memX [] (Nat.zero_le _)
  have hconv : Tendsto (fun n : ℕ => eLpNorm (cellMoll n f - f) 2 (B0579.cellMeasure c (-m)))
      atTop (𝓝 0) :=
    cellMollTendsto c m f hc hfp hfm
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (cellMoll n f) (B0579.cellMeasure c (-m)) :=
    fun n => (cellMollSmooth c m n f hc hfp hfm).1.continuous.aestronglyMeasurable
  have hTIM := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    hmeas hfm.1 hconv
  obtain ⟨ns, hns, hae_lim⟩ := hTIM.exists_seq_tendsto_ae
  have hμae : mollLim [] f =ᵐ[B0579.cellMeasure c (-m)] f := by
    filter_upwards [hae_lim] with x hx
    have hpt : Tendsto (fun i => cellMoll (ns i) f x) atTop (𝓝 (mollLim [] f x)) :=
      (tendsto_mollLim hc [] hJ₂ x).comp hns.tendsto_atTop
    exact tendsto_nhds_unique hpt hx
  have hcell : mollLim [] f =ᵐ[volume.restrict (B0579.cell c)] f :=
    (B0579.ac_cellMeasure c (-m)).ae_le hμae
  exact periodicAeOfCell c hc (mollLim [] f) f hper' hfp hcell

end FreeSpSmoothRepAux

namespace Leaf2DualityNeeded

/-- **Proof of Leaf 1 (`FreeSpSmoothRep`)** (`PartIII-a:T21/c3/3/1/1/2/2/2/1/1`, SP 3060-3061). -/
theorem freeSpSmoothRep (c m t s : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.FreeSpSmoothRep c m t s := by
  intro hc hts φ hHk
  let φ' : ℝ → ℝ × ℝ → ℂ := fun r => FreeSpSmoothRepAux.mollLim [] (φ r)
  have hJet : ∀ r ∈ Ico t s, ∀ k : ℕ, ∃ D, IsCellJet c m k (φ r) D := by
    intro r hr k
    obtain ⟨D, hDj, -⟩ := hHk k
    exact ⟨D r, hDj r hr⟩
  have hsm : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r) :=
    fun r hr => FreeSpSmoothRepAux.contDiff_mollLim_nil hc (hJet r hr)
  have hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x := by
    intro r hr x
    obtain ⟨D₀, hJ₀⟩ := hJet r hr 0
    have hfp : ∀ y : ℝ × ℝ, φ r (y.1 + c, y.2) = φ r y := by
      rw [← hJ₀.base]; exact hJ₀.periodic [] le_rfl
    have hfm : MemLp (φ r) 2 (B0579.cellMeasure c (-m)) := by
      rw [← hJ₀.base]; exact hJ₀.memX [] le_rfl
    have hfn : (fun n : ℕ => cellMoll n (φ r) (x.1 + c, x.2)) =
        fun n : ℕ => cellMoll n (φ r) x :=
      funext fun n => (cellMollSmooth c m n (φ r) hc hfp hfm).2.1 x
    exact congrArg (limUnder atTop) hfn
  have hae : ∀ r ∈ Ico t s, φ' r =ᵐ[volume] φ r :=
    fun r hr => FreeSpSmoothRepAux.mollLim_ae_eq hc (hJet r hr) (hper r hr)
  refine ⟨φ', hae, hsm, hper, fun w => ?_⟩
  rintro ⟨r₀, x₀⟩ ⟨hr₀, -⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨D, hDj, hDc⟩ := hHk (w.length + 2)
  set R : ℝ := ‖x₀‖ + 1
  obtain ⟨C₁, hC₁0, hC₁⟩ := _root_.supBddByXNorm c m R hc
  set δ : ℝ := (ε / 2) / (7 * (C₁ + 1))
  have hδ : 0 < δ := div_pos (half_pos hε) (by positivity)
  have hac : B0579.cellMeasure c (-m) ≪ volume :=
    (B0579.cellMeasure_ac c (-m)).trans Measure.restrict_le_self.absolutelyContinuous
  have hev_r_w : ∀ w' ∈ wordsLe2.toFinset,
      ∀ᶠ r in 𝓝[Ico t s] r₀,
        xNorm c (-m) (D r (w' ++ w) - D r₀ (w' ++ w)) ≤ ENNReal.ofReal δ := by
    intro w' hw'
    have hlen : (w' ++ w).length ≤ w.length + 2 := by
      rw [List.length_append]
      have := FreeSpSmoothRepAux.wordsLe2_len (List.mem_toFinset.1 hw')
      omega
    exact ENNReal.tendsto_nhds_zero.1 (hDc (w' ++ w) hlen r₀ hr₀)
      (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  have hev_r : {r : ℝ | r ∈ Ico t s ∧ ∀ w' ∈ wordsLe2.toFinset,
      xNorm c (-m) (D r (w' ++ w) - D r₀ (w' ++ w)) ≤ ENNReal.ofReal δ} ∈ 𝓝[Ico t s] r₀ :=
    Filter.inter_mem self_mem_nhdsWithin ((Filter.eventually_all_finset wordsLe2.toFinset).2 hev_r_w)
  have hcont_x₀ : Continuous (adjSpatial w (φ' r₀)) :=
    (st_contDiff_adjSpatial (hsm r₀ hr₀) w).continuous
  have hev_x : {x : ℝ × ℝ |
      x ∈ Metric.ball x₀ 1 ∧ dist (adjSpatial w (φ' r₀) x) (adjSpatial w (φ' r₀) x₀) < ε / 2} ∈
        𝓝 x₀ :=
    Filter.inter_mem (Metric.ball_mem_nhds x₀ zero_lt_one)
      (Metric.tendsto_nhds.1 (hcont_x₀.tendsto x₀) (ε / 2) (half_pos hε))
  have hprod_ev :
      ({r : ℝ | r ∈ Ico t s ∧ ∀ w' ∈ wordsLe2.toFinset,
        xNorm c (-m) (D r (w' ++ w) - D r₀ (w' ++ w)) ≤ ENNReal.ofReal δ} ×ˢ
      {x : ℝ × ℝ | x ∈ Metric.ball x₀ 1 ∧
        dist (adjSpatial w (φ' r₀) x) (adjSpatial w (φ' r₀) x₀) < ε / 2}) ∈
      𝓝[Ico t s ×ˢ univ] (r₀, x₀) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact Filter.prod_mem_prod hev_r hev_x
  filter_upwards [hprod_ev] with ⟨r, x⟩ ⟨⟨hr, hrD⟩, ⟨hxB, hxd⟩⟩
  have hxR : ‖x‖ ≤ R := by
    have h1 : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hxB
    have h2 : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_le_norm_sub_add x x₀
    simp only [R]; linarith
  have hws_r : ContDiff ℝ ∞ (adjSpatial w (φ' r)) := st_contDiff_adjSpatial (hsm r hr) w
  have hws_r₀ : ContDiff ℝ ∞ (adjSpatial w (φ' r₀)) := st_contDiff_adjSpatial (hsm r₀ hr₀) w
  have hwp_r := st_adjSpatial_periodic (hper r hr) w
  have hwp_r₀ := st_adjSpatial_periodic (hper r₀ hr₀) w
  let g : ℝ × ℝ → ℂ := fun y => adjSpatial w (φ' r) y - adjSpatial w (φ' r₀) y
  have hgs : ContDiff ℝ ∞ g := hws_r.sub hws_r₀
  have hgp : ∀ y : ℝ × ℝ, g (y.1 + c, y.2) = g y := fun y => by
    simp only [g, hwp_r y, hwp_r₀ y]
  have hbd : ∀ w' ∈ wordsLe2, xNorm c (-m) (adjSpatial w' g) ≤ ENNReal.ofReal δ := by
    intro w' hw'
    have hlen : (w' ++ w).length ≤ w.length + 2 := by
      rw [List.length_append]; have := FreeSpSmoothRepAux.wordsLe2_len hw'; omega
    have hae_r : adjSpatial (w' ++ w) (φ' r) =ᵐ[B0579.cellMeasure c (-m)] D r (w' ++ w) :=
      hac.ae_eq ((smoothAeJet c m (w.length + 2) (φ' r) (φ r) (D r) hc
        (hsm r hr) (hDj r hr) (hae r hr) (w' ++ w) hlen).2)
    have hae_r₀ : adjSpatial (w' ++ w) (φ' r₀) =ᵐ[B0579.cellMeasure c (-m)] D r₀ (w' ++ w) :=
      hac.ae_eq ((smoothAeJet c m (w.length + 2) (φ' r₀) (φ r₀) (D r₀) hc
        (hsm r₀ hr₀) (hDj r₀ hr₀) (hae r₀ hr₀) (w' ++ w) hlen).2)
    have hEqg : adjSpatial w' g = adjSpatial (w' ++ w) (φ' r) - adjSpatial (w' ++ w) (φ' r₀) := by
      change adjSpatial w' (fun y => adjSpatial w (φ' r) y - adjSpatial w (φ' r₀) y) = _
      rw [st_adjSpatial_sub hws_r hws_r₀ w', adjSpatial_append, adjSpatial_append]
      rfl
    rw [hEqg]
    unfold xNorm
    rw [eLpNorm_congr_ae (hae_r.sub hae_r₀)]
    exact hrD w' (List.mem_toFinset.2 hw')
  have hle := FreeSpSmoothRepAux.norm_le_of_wordsLe2 hC₁0 hδ.le hC₁ hgs hgp hbd hxR
  have hcalc : C₁ * (7 * δ) ≤ ε / 2 := by
    have h1 : C₁ ≤ C₁ + 1 := by linarith
    have h2 : C₁ * (7 * δ) ≤ (C₁ + 1) * (7 * δ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (C₁ + 1) * (7 * δ) = ε / 2 := by
      simp only [δ]
      have hne : 7 * (C₁ + 1) ≠ 0 := by positivity
      field_simp
    linarith
  have hg_le : ‖adjSpatial w (φ' r) x - adjSpatial w (φ' r₀) x‖ ≤ ε / 2 := hle.trans hcalc
  rw [dist_eq_norm] at hxd ⊢
  calc ‖adjSpatial w (φ' r) x - adjSpatial w (φ' r₀) x₀‖
      = ‖(adjSpatial w (φ' r) x - adjSpatial w (φ' r₀) x) +
          (adjSpatial w (φ' r₀) x - adjSpatial w (φ' r₀) x₀)‖ := by congr 1; abel
    _ ≤ ‖adjSpatial w (φ' r) x - adjSpatial w (φ' r₀) x‖ +
          ‖adjSpatial w (φ' r₀) x - adjSpatial w (φ' r₀) x₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hg_le hxd
    _ = ε := add_halves ε

end Leaf2DualityNeeded

end UnforcedLeray.Short.IIIa.ComplFreeRateSub

export UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded (freeSpSmoothRep)
