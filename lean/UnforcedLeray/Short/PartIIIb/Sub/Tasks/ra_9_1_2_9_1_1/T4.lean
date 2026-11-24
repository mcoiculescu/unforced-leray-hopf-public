import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# `termwiseWord` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1`, source 5063-5071, 5076-5079)

Termwise conormal differentiation of a lattice sum. Induction on the word `w` (length `≤ 4`).
For the step `a :: w`, the tail summands `G j = wordW w (F j)` are `C^1` on the open set `UChart`
(`tw_wordW_contDiffOn`), and the three conormal derivatives `opW b (G j)` have locally uniform
summable majorants (`LocSumm`, from the budget words `b :: w`). Their sum `∑' G j` therefore has
Fréchet derivative `∑' fderiv (G j)` near `p` (`hasFDerivAt_tsum_of_isPreconnected` on a ball), and
the conormal operator `opW a` commutes with the sum (`tw_opW_tsum`). Equality on the open set
`UChart` passes to the derivatives (`Filter.EventuallyEq.fderiv_eq`).

Note: `UnforcedLeray.Axi.dS/dQ/dEta` are written in full, since the namespace
`PartIIIb.Concrete` has its own `dQ`, `dEta`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma tw_isOpen_UChart : IsOpen UChart := isOpen_Ioi.prod isOpen_univ

lemma tw_mem_budget_of_length (w : List (Fin 3)) (h : w.length ≤ 4) : w ∈ budgetWords :=
  Finset.mem_biUnion.mpr ⟨w.length, Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨fun i => w.get i, Finset.mem_univ _, List.ofFn_get w⟩⟩

lemma tw_length_of_mem_budget (w : List (Fin 3)) (h : w ∈ budgetWords) : w.length ≤ 4 := by
  unfold budgetWords at h
  obtain ⟨n, hn, h2⟩ := Finset.mem_biUnion.mp h
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h2
  have := Finset.mem_range.mp hn
  simp only [List.length_ofFn]
  omega

lemma tw_opW_congr (a : Fin 3) (F G : Chart → Merid) (p : Chart) (h : F =ᶠ[𝓝 p] G) :
    opW a F p = opW a G p := by
  fin_cases a
  · show p.1 • UnforcedLeray.Axi.dS F p = p.1 • UnforcedLeray.Axi.dS G p
    unfold UnforcedLeray.Axi.dS
    rw [h.fderiv_eq]
  · show UnforcedLeray.Axi.dQ F p = UnforcedLeray.Axi.dQ G p
    unfold UnforcedLeray.Axi.dQ
    rw [h.fderiv_eq]
  · show UnforcedLeray.Axi.dEta F p = UnforcedLeray.Axi.dEta G p
    unfold UnforcedLeray.Axi.dEta
    rw [h.fderiv_eq]

lemma tw_opW_contDiffOn (a : Fin 3) (k : ℕ) (H : Chart → Merid)
    (h : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) H UChart) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (opW a H) UChart := by
  have hfd : ContDiffOn ℝ (k : WithTop ℕ∞) (fun y => fderiv ℝ H y) UChart :=
    h.fderiv_of_isOpen tw_isOpen_UChart (le_of_eq (by norm_cast))
  fin_cases a
  · show ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun y : Chart => y.1 • fderiv ℝ H y (1, (0, 0))) UChart
    exact (contDiff_fst.contDiffOn).smul (hfd.clm_apply contDiffOn_const)
  · show ContDiffOn ℝ (k : WithTop ℕ∞) (fun y : Chart => fderiv ℝ H y (0, (1, 0))) UChart
    exact hfd.clm_apply contDiffOn_const
  · show ContDiffOn ℝ (k : WithTop ℕ∞) (fun y : Chart => fderiv ℝ H y (0, (0, 1))) UChart
    exact hfd.clm_apply contDiffOn_const

lemma tw_wordW_contDiffOn : ∀ (w : List (Fin 3)) (k : ℕ) (G : Chart → Merid),
    ContDiffOn ℝ ((k + w.length : ℕ) : WithTop ℕ∞) G UChart →
      ContDiffOn ℝ (k : WithTop ℕ∞) (wordW w G) UChart
  | [], k, G, h => by simpa [wordW] using h
  | a :: w, k, G, h => by
    have e : k + 1 + w.length = k + (a :: w).length := by
      simp only [List.length_cons]; omega
    show ContDiffOn ℝ (k : WithTop ℕ∞) (opW a (wordW w G)) UChart
    apply tw_opW_contDiffOn a k
    apply tw_wordW_contDiffOn w (k + 1) G
    rw [e]
    exact h

lemma tw_fderiv_norm_le (F : Chart → Merid) (q : Chart) (M0 M1 M2 : ℝ)
    (h0 : ‖UnforcedLeray.Axi.dS F q‖ ≤ M0) (h1 : ‖UnforcedLeray.Axi.dQ F q‖ ≤ M1)
    (h2 : ‖UnforcedLeray.Axi.dEta F q‖ ≤ M2) :
    ‖fderiv ℝ F q‖ ≤ M0 + M1 + M2 := by
  have hM0 : 0 ≤ M0 := le_trans (norm_nonneg _) h0
  have hM1 : 0 ≤ M1 := le_trans (norm_nonneg _) h1
  have hM2 : 0 ≤ M2 := le_trans (norm_nonneg _) h2
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun L => ?_)
  have hdec : L = L.1 • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
      + L.2.1 • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) + L.2.2 • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  have hL : fderiv ℝ F q L = L.1 • UnforcedLeray.Axi.dS F q
      + L.2.1 • UnforcedLeray.Axi.dQ F q + L.2.2 • UnforcedLeray.Axi.dEta F q := by
    conv_lhs => rw [hdec]
    simp only [map_add, map_smul]
    rfl
  rw [hL]
  have b1 : ‖L.1‖ ≤ ‖L‖ := norm_fst_le L
  have b2 : ‖L.2.1‖ ≤ ‖L‖ := le_trans (norm_fst_le L.2) (norm_snd_le L)
  have b3 : ‖L.2.2‖ ≤ ‖L‖ := le_trans (norm_snd_le L.2) (norm_snd_le L)
  have e0 : ‖L.1 • UnforcedLeray.Axi.dS F q‖ ≤ ‖L‖ * M0 := by
    rw [norm_smul]; exact mul_le_mul b1 h0 (norm_nonneg _) (norm_nonneg _)
  have e1 : ‖L.2.1 • UnforcedLeray.Axi.dQ F q‖ ≤ ‖L‖ * M1 := by
    rw [norm_smul]; exact mul_le_mul b2 h1 (norm_nonneg _) (norm_nonneg _)
  have e2 : ‖L.2.2 • UnforcedLeray.Axi.dEta F q‖ ≤ ‖L‖ * M2 := by
    rw [norm_smul]; exact mul_le_mul b3 h2 (norm_nonneg _) (norm_nonneg _)
  have t1 := norm_add_le (L.1 • UnforcedLeray.Axi.dS F q + L.2.1 • UnforcedLeray.Axi.dQ F q)
    (L.2.2 • UnforcedLeray.Axi.dEta F q)
  have t2 := norm_add_le (L.1 • UnforcedLeray.Axi.dS F q) (L.2.1 • UnforcedLeray.Axi.dQ F q)
  calc ‖L.1 • UnforcedLeray.Axi.dS F q + L.2.1 • UnforcedLeray.Axi.dQ F q
        + L.2.2 • UnforcedLeray.Axi.dEta F q‖
      ≤ ‖L.1 • UnforcedLeray.Axi.dS F q‖ + ‖L.2.1 • UnforcedLeray.Axi.dQ F q‖
          + ‖L.2.2 • UnforcedLeray.Axi.dEta F q‖ := by linarith
    _ ≤ ‖L‖ * M0 + ‖L‖ * M1 + ‖L‖ * M2 := by linarith
    _ = (M0 + M1 + M2) * ‖L‖ := by ring

lemma tw_fderiv_tsum_apply (H : Chart → Merid) (p : Chart) (L : ℤ → (Chart →L[ℝ] Merid))
    (hH : HasFDerivAt H (∑' j, L j) p) (hs : Summable L) (v : Chart) :
    fderiv ℝ H p v = ∑' j, L j v := by
  rw [hH.fderiv]
  have := (ContinuousLinearMap.apply ℝ Merid v).map_tsum hs
  simpa using this

lemma tw_tsum_hasFDerivAt (G : ℤ → Chart → Merid) (hC : ∀ j, ContDiffOn ℝ 1 (G j) UChart)
    (hV : LocSumm G) (hD : ∀ b : Fin 3, LocSumm (fun j => opW b (G j)))
    (p : Chart) (hp : p ∈ UChart) :
    HasFDerivAt (fun q => ∑' j, G j q) (∑' j, fderiv ℝ (G j) p) p ∧
      Summable (fun j => fderiv ℝ (G j) p) := by
  obtain ⟨N0, hN0, u0, hu0, hb0⟩ := hD 0 p hp
  obtain ⟨N1, hN1, u1, hu1, hb1⟩ := hD 1 p hp
  obtain ⟨N2, hN2, u2, hu2, hb2⟩ := hD 2 p hp
  obtain ⟨NG, hNG, uG, huG, hbG⟩ := hV p hp
  have hO : UChart ∩ N0 ∩ N1 ∩ N2 ∩ NG ∈ 𝓝 p :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem (tw_isOpen_UChart.mem_nhds hp) hN0) hN1) hN2) hNG
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hO
  have hp1 : 0 < p.1 := hp.1
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min ε (p.1 / 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact lt_min hε (by linarith)
  have hrle : r ≤ p.1 / 2 := by rw [hrdef]; exact min_le_right _ _
  have hrε : r ≤ ε := by rw [hrdef]; exact min_le_left _ _
  have hrB : Metric.ball p r ⊆ UChart ∩ N0 ∩ N1 ∩ N2 ∩ NG :=
    fun q hq => hball (Metric.ball_subset_ball hrε hq)
  have hmemN : ∀ q ∈ Metric.ball p r, q ∈ UChart ∧ q ∈ N0 ∧ q ∈ N1 ∧ q ∈ N2 ∧ q ∈ NG := by
    intro q hq
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hrB hq
    exact ⟨h0, h1, h2, h3, h4⟩
  have hq1 : ∀ q ∈ Metric.ball p r, p.1 / 2 < q.1 := by
    intro q hq
    have hd : dist q.1 p.1 ≤ dist q p := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have h3 : |q.1 - p.1| < p.1 / 2 := by
      rw [← Real.dist_eq]
      exact lt_of_le_of_lt hd (lt_of_lt_of_le (Metric.mem_ball.mp hq) hrle)
    have := (abs_lt.mp h3).1
    linarith
  have hdS : ∀ j, ∀ q ∈ Metric.ball p r, ‖UnforcedLeray.Axi.dS (G j) q‖ ≤ 2 * u0 j / p.1 := by
    intro j q hq
    obtain ⟨-, hN0', -, -, -⟩ := hmemN q hq
    have h1 : ‖opW 0 (G j) q‖ ≤ u0 j := hb0 j q hN0'
    have hqpos := hq1 q hq
    have h2 : ‖opW 0 (G j) q‖ = q.1 * ‖UnforcedLeray.Axi.dS (G j) q‖ := by
      show ‖q.1 • UnforcedLeray.Axi.dS (G j) q‖ = _
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    rw [h2] at h1
    rw [le_div_iff₀ hp1]
    nlinarith [mul_le_mul_of_nonneg_right hqpos.le (norm_nonneg (UnforcedLeray.Axi.dS (G j) q))]
  have hdQ : ∀ j, ∀ q ∈ Metric.ball p r, ‖UnforcedLeray.Axi.dQ (G j) q‖ ≤ u1 j := by
    intro j q hq
    obtain ⟨-, -, hN1', -, -⟩ := hmemN q hq
    have h1 : ‖opW 1 (G j) q‖ ≤ u1 j := hb1 j q hN1'
    exact h1
  have hdEta : ∀ j, ∀ q ∈ Metric.ball p r, ‖UnforcedLeray.Axi.dEta (G j) q‖ ≤ u2 j := by
    intro j q hq
    obtain ⟨-, -, -, hN2', -⟩ := hmemN q hq
    have h1 : ‖opW 2 (G j) q‖ ≤ u2 j := hb2 j q hN2'
    exact h1
  have hfd : ∀ j, ∀ q ∈ Metric.ball p r,
      ‖fderiv ℝ (G j) q‖ ≤ 2 * u0 j / p.1 + u1 j + u2 j := by
    intro j q hq
    exact tw_fderiv_norm_le (G j) q _ _ _ (hdS j q hq) (hdQ j q hq) (hdEta j q hq)
  have hVsum : Summable (fun j => 2 * u0 j / p.1 + u1 j + u2 j) :=
    (((hu0.mul_left 2).div_const p.1).add hu1).add hu2
  have hsumfd : Summable (fun j => fderiv ℝ (G j) p) :=
    Summable.of_norm_bounded hVsum (fun j => hfd j p (Metric.mem_ball_self hr0))
  have hdiff : ∀ j, ∀ y ∈ Metric.ball p r, HasFDerivAt (G j) (fderiv ℝ (G j) y) y := by
    intro j y hy
    have hyU : y ∈ UChart := (hmemN y hy).1
    exact (((hC j).differentiableOn (by norm_num)).differentiableAt
      (tw_isOpen_UChart.mem_nhds hyU)).hasFDerivAt
  have hf0 : Summable (fun j => G j p) :=
    Summable.of_norm_bounded huG
      (fun j => hbG j p (hmemN p (Metric.mem_ball_self hr0)).2.2.2.2)
  have hH := hasFDerivAt_tsum_of_isPreconnected (f := G)
    (f' := fun j y => fderiv ℝ (G j) y) (u := fun j => 2 * u0 j / p.1 + u1 j + u2 j)
    hVsum Metric.isOpen_ball Metric.isPreconnected_ball hdiff hfd
    (Metric.mem_ball_self hr0) hf0 (Metric.mem_ball_self hr0)
  exact ⟨hH, hsumfd⟩

lemma tw_opW_tsum (a : Fin 3) (G : ℤ → Chart → Merid) (p : Chart)
    (hH : HasFDerivAt (fun q => ∑' j, G j q) (∑' j, fderiv ℝ (G j) p) p)
    (hs : Summable (fun j => fderiv ℝ (G j) p)) :
    opW a (fun q => ∑' j, G j q) p = ∑' j, opW a (G j) p := by
  fin_cases a
  · show p.1 • UnforcedLeray.Axi.dS (fun q => ∑' j, G j q) p
      = ∑' j, p.1 • UnforcedLeray.Axi.dS (G j) p
    unfold UnforcedLeray.Axi.dS
    rw [tw_fderiv_tsum_apply _ p _ hH hs]
    have hsE : Summable (fun j => fderiv ℝ (G j) p (1, (0, 0))) :=
      (ContinuousLinearMap.apply ℝ Merid ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))).summable hs
    exact (hsE.tsum_const_smul p.1).symm
  · show UnforcedLeray.Axi.dQ (fun q => ∑' j, G j q) p = ∑' j, UnforcedLeray.Axi.dQ (G j) p
    unfold UnforcedLeray.Axi.dQ
    exact tw_fderiv_tsum_apply _ p _ hH hs _
  · show UnforcedLeray.Axi.dEta (fun q => ∑' j, G j q) p
      = ∑' j, UnforcedLeray.Axi.dEta (G j) p
    unfold UnforcedLeray.Axi.dEta
    exact tw_fderiv_tsum_apply _ p _ hH hs _

theorem termwiseWord : TermwiseWord := by
  unfold TermwiseWord
  intro F hF hL
  have main : ∀ w : List (Fin 3), w.length ≤ 4 → ∀ p ∈ UChart,
      wordW w (fun q => ∑' j : ℤ, F j q) p = ∑' j : ℤ, wordW w (F j) p := by
    intro w
    induction w with
    | nil => intro _ p _; rfl
    | cons a w ih =>
      intro hlen p hp
      have hlen' : w.length + 1 ≤ 4 := by simpa only [List.length_cons] using hlen
      have hw : w.length ≤ 4 := by omega
      have hEqN : wordW w (fun q => ∑' j : ℤ, F j q)
          =ᶠ[𝓝 p] (fun q => ∑' j : ℤ, wordW w (F j) q) :=
        Filter.eventually_of_mem (tw_isOpen_UChart.mem_nhds hp) (fun q hq => ih hw q hq)
      have hC : ∀ j, ContDiffOn ℝ 1 (wordW w (F j)) UChart := fun j => by
        have h4 : ContDiffOn ℝ ((1 + w.length : ℕ) : WithTop ℕ∞) (F j) UChart :=
          (hF j).of_le (by exact_mod_cast (by omega : 1 + w.length ≤ 4))
        have := tw_wordW_contDiffOn w 1 (F j) h4
        simpa using this
      have hV : LocSumm (fun j => wordW w (F j)) := hL w (tw_mem_budget_of_length w hw)
      have hD : ∀ b : Fin 3, LocSumm (fun j => opW b (wordW w (F j))) := fun b =>
        hL (b :: w) (tw_mem_budget_of_length (b :: w)
          (by simp only [List.length_cons]; omega))
      obtain ⟨hH, hs⟩ := tw_tsum_hasFDerivAt (fun j => wordW w (F j)) hC hV hD p hp
      show opW a (wordW w (fun q => ∑' j : ℤ, F j q)) p = ∑' j : ℤ, opW a (wordW w (F j)) p
      rw [tw_opW_congr a _ _ p hEqN]
      exact tw_opW_tsum a (fun j => wordW w (F j)) p hH hs
  intro w hw p hp
  exact main w (tw_length_of_mem_budget w hw) p hp

end UnforcedLeray.Short.PartIIIb.Concrete
