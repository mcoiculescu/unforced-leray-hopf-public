import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2
import UnforcedLeray.Units.B0610

/-!
# `PartII-b:F4` (`Sub/PartII-b_F4.lean`): Intermediate-time projections and mixed Green selector

Source of record: `the November 2 reference manuscript` (SP), lines 2189–2210
(displays `short-bg:green` at line 2199 and `short-bg:green-bound` at line 2206).

This module provides:
1. `cellCircCLM` and `cellTestCLM`: bounded linear functionals on `Xmc c m` (`m > 1/2`) realizing
   the cell integral `w ↦ ∫_{cell c} w` and test pairing `w ↦ ∫_{cell c} w φ`, together with
   Bochner-integral preservation of zero circulation (`hasZeroCirculationR_of_bochner`);
2. `blkIdx` and `gen_green_operators_full`: full construction of the intermediate projections
   `Π^u(t) = J_t M_n F_t`, `Π^c(t) = I - Π^u(t)`, Green kernels `G_c, G_u`, entrance functional
   `Γ_α`, operator-algebraic identities, exponential bounds, global propagator bound
   `‖U(r, s)‖ ≤ C_proj ^ (N + 2)`, and the rank-two unstable kernel factorizations
   `G_u(s, r) = -U(s, 0) I_0^u Γ_α(r)` (`0 ≤ s ≤ r ≤ H`) and
   `G_c(s, r) = U(s, r) + U(s, 0) I_0^u Γ_α(r)` (`0 ≤ r ≤ s ≤ H`);
3. `integrableOn_propagator_apply`: Bochner integrability of `t ↦ U(s, t) f(t)` on `(0, s]` and
   `t ↦ Γ_α(t) f(t)` on `(0, H]` via right-grid indicator approximations, yielding the forward
   Duhamel reduction `ω(s) = U(s, 0) (ω 0) + ∫_{0 < t ≤ s} U(s, t) f(t) dt` and unconditional
   proof of `∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s)`;
4. The two leaf propositions of `PartII-b:F4`:
   * `CylCoupledPairingCLM` (`PartII-b:F4/1`, SP 2079–2083, 2195–2201),
   * `PropagatorTriangleFubini` (`PartII-b:F4/2`, SP 2195–2201),
   and the unconditional assembly theorem `mixedGreenSelector_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Cell circulation and test pairings as continuous linear functionals on `Xmc c m` -/

namespace PartIIbF4Aux

/-- Continuous linear functional `w ↦ ∫ x in B0579.cell c, w x` on `Xmc c m` for `1 / 2 < m`. -/
def cellCircCLM (c m : ℝ) (hm : 1 / 2 < m) : Xmc c m →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (B0610.oneH1 c m hm)).comp (B0579.sourceCLM c m)

@[simp] theorem cellCircCLM_apply (c m : ℝ) (hm : 1 / 2 < m) (w : Xmc c m) :
    cellCircCLM c m hm w = ∫ x in B0579.cell c, w x :=
  B0610.sourceCLM_oneH1 hm w

/-- Every `w : Xmc c m` (`1 / 2 < m`) is integrable on `B0579.cell c`. -/
theorem integrableOn_cell_of_Xmc (c m : ℝ) (hm : 1 / 2 < m) (w : Xmc c m) :
    IntegrableOn w (B0579.cell c) volume := by
  have h := B0579.integrableOn_source c m w (B0610.oneH1 c m hm)
  refine h.congr_fun_ae ?_
  filter_upwards [B0610.coeFn_oneX (c := c) hm] with x hx
  rw [B0610.oneH1_value, hx, mul_one]

/-- For `w : Xmc c m` (`1 / 2 < m`), `HasZeroCirculationR c w` holds iff `cellCircCLM c m hm w = 0`. -/
theorem hasZeroCirculationR_iff_cellCircCLM (c m : ℝ) (hm : 1 / 2 < m) (w : Xmc c m) :
    HasZeroCirculationR c w ↔ cellCircCLM c m hm w = 0 := by
  unfold HasZeroCirculationR
  rw [cellCircCLM_apply]
  exact ⟨fun h => h.2, fun h => ⟨integrableOn_cell_of_Xmc c m hm w, h⟩⟩

theorem hasZeroCirculationR_sub {c m : ℝ} (hm : 1 / 2 < m) {u v : Xmc c m}
    (hu : HasZeroCirculationR c u) (hv : HasZeroCirculationR c v) :
    HasZeroCirculationR c (u - v : Xmc c m) := by
  rw [hasZeroCirculationR_iff_cellCircCLM c m hm] at hu hv ⊢
  rw [map_sub, hu, hv, sub_zero]

/-- Bochner integration on `Xmc c m` (`1 / 2 < m`) preserves `HasZeroCirculationR c`. -/
theorem hasZeroCirculationR_of_bochner {c m : ℝ} (hm : 1 / 2 < m)
    (S : Set ℝ) (hS : MeasurableSet S) (g : ℝ → Xmc c m)
    (hg : ∀ᵐ t ∂volume, t ∈ S → HasZeroCirculationR c (g t)) :
    HasZeroCirculationR c (∫ t in S, g t : Xmc c m) := by
  rw [hasZeroCirculationR_iff_cellCircCLM c m hm]
  by_cases hInt : IntegrableOn g S volume
  · rw [← (cellCircCLM c m hm).integral_comp_comm hInt]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [(ae_restrict_iff' hS).mpr hg] with t ht
    exact (hasZeroCirculationR_iff_cellCircCLM c m hm (g t)).1 ht
  · rw [integral_undef hInt, map_zero]

/-- Continuous linear functional `w ↦ ∫ x in B0579.cell c, w x * φ x` on `Xmc c m` for a cylinder
test function `B0579.IsCylTest c φ`. -/
def cellTestCLM (c m : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    Xmc c m →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (B0579.testH1 c (-m) hφ)).comp (B0579.sourceCLM c m)

@[simp] theorem cellTestCLM_apply (c m : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (w : Xmc c m) :
    cellTestCLM c m hφ w = ∫ x in B0579.cell c, w x * φ x :=
  B0579.toDistribution_sourceCLM c m w ⟨φ, hφ⟩

theorem integrableOn_mul_cylTest (c m : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (w : Xmc c m) :
    IntegrableOn (fun x => w x * φ x) (B0579.cell c) volume := by
  have h := B0579.integrableOn_source c m w (B0579.testH1 c (-m) hφ)
  refine h.congr_fun_ae ?_
  filter_upwards [B0579.coeFn_testLp c (-m) hφ] with x hx
  rw [B0579.testH1_value, hx]

/-! ## 2. Right-grid indicator approximations and Bochner integrability of `t ↦ U s t (f t)` -/

section PropagatorIntegrability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Grid points `k * s / (n + 1)` on `[0, s]`. -/
def gridPt (s : ℝ) (n k : ℕ) : ℝ :=
  (k : ℝ) * s / ((n + 1 : ℕ) : ℝ)

/-- Right-grid step approximation of `t ↦ U s t (f t)` on `[0, s)`. -/
def approxProp (U : ℝ → ℝ → (X →L[ℝ] X)) (f : ℝ → X) (s : ℝ) (n : ℕ) (t : ℝ) : X :=
  ∑ k ∈ Finset.range (n + 1),
    (Ico (gridPt s n k) (gridPt s n (k + 1))).indicator
      (fun τ => U s (gridPt s n (k + 1)) (f τ)) t

theorem aestronglyMeasurable_approxProp
    (U : ℝ → ℝ → (X →L[ℝ] X)) {f : ℝ → X} (s : ℝ) (n : ℕ) {μ : Measure ℝ}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (approxProp U f s n) μ := by
  unfold approxProp
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  exact ((U s (gridPt s n (k + 1))).continuous.comp_aestronglyMeasurable hf).indicator
    measurableSet_Ico

theorem gridPt_Properties {s t : ℝ} (ht : t ∈ Ioo 0 s) (n : ℕ) :
    let k : ℕ := ⌊t * ((n + 1 : ℕ) : ℝ) / s⌋₊
    k ∈ Finset.range (n + 1) ∧
    t ∈ Ico (gridPt s n k) (gridPt s n (k + 1)) ∧
    gridPt s n (k + 1) ≤ s ∧
    gridPt s n (k + 1) - t ≤ s / ((n + 1 : ℕ) : ℝ) ∧
    ∀ j ∈ Finset.range (n + 1), j ≠ k → t ∉ Ico (gridPt s n j) (gridPt s n (j + 1)) := by
  intro k
  have hs : 0 < s := ht.1.trans ht.2
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiv_nn : 0 ≤ t * ((n + 1 : ℕ) : ℝ) / s :=
    div_nonneg (mul_nonneg ht.1.le hn1.le) hs.le
  have hdiv_lt : t * ((n + 1 : ℕ) : ℝ) / s < ((n + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hs, mul_comm ((n + 1 : ℕ) : ℝ) s]
    exact mul_lt_mul_of_pos_right ht.2 hn1
  have hk_lt : k < n + 1 := (Nat.floor_lt hdiv_nn).2 hdiv_lt
  have hk_le : (k : ℝ) ≤ t * ((n + 1 : ℕ) : ℝ) / s := Nat.floor_le hdiv_nn
  have hlt_k1 : t * ((n + 1 : ℕ) : ℝ) / s < ((k + 1 : ℕ) : ℝ) := by
    simpa [k, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (t * ((n + 1 : ℕ) : ℝ) / s)
  have h_left : gridPt s n k ≤ t := by
    unfold gridPt
    rw [div_le_iff₀ hn1]
    exact (le_div_iff₀ hs).1 hk_le
  have h_right : t < gridPt s n (k + 1) := by
    unfold gridPt
    rw [lt_div_iff₀ hn1]
    exact (div_lt_iff₀ hs).1 hlt_k1
  have hk1_le : k + 1 ≤ n + 1 := hk_lt
  have h_le_s : gridPt s n (k + 1) ≤ s := by
    unfold gridPt
    rw [div_le_iff₀ hn1]
    have hk1_r : ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hk1_le
    calc ((k + 1 : ℕ) : ℝ) * s ≤ ((n + 1 : ℕ) : ℝ) * s :=
          mul_le_mul_of_nonneg_right hk1_r hs.le
      _ = s * ((n + 1 : ℕ) : ℝ) := mul_comm _ _
  have h_step : gridPt s n (k + 1) - gridPt s n k = s / ((n + 1 : ℕ) : ℝ) := by
    unfold gridPt
    push_cast
    ring
  refine ⟨Finset.mem_range.2 hk_lt, ⟨h_left, h_right⟩, h_le_s, by linarith, ?_⟩
  intro j _ hjk hmem
  rcases lt_or_gt_of_ne hjk with hjk_lt | hjk_gt
  · have hj1_le_k : j + 1 ≤ k := hjk_lt
    have hj1_le_k_r : gridPt s n (j + 1) ≤ gridPt s n k := by
      unfold gridPt
      refine div_le_div_of_nonneg_right ?_ hn1.le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj1_le_k) hs.le
    linarith [hmem.2]
  · have hk1_le_j : k + 1 ≤ j := hjk_gt
    have hk1_le_j_r : gridPt s n (k + 1) ≤ gridPt s n j := by
      unfold gridPt
      refine div_le_div_of_nonneg_right ?_ hn1.le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk1_le_j) hs.le
    linarith [hmem.1]

theorem approxProp_eq_at_grid {U : ℝ → ℝ → (X →L[ℝ] X)} {f : ℝ → X} {s t : ℝ}
    (ht : t ∈ Ioo 0 s) (n : ℕ) :
    approxProp U f s n t =
      U s (gridPt s n (⌊t * ((n + 1 : ℕ) : ℝ) / s⌋₊ + 1)) (f t) := by
  obtain ⟨hk_mem, ht_mem, _, _, hdisj⟩ := gridPt_Properties ht n
  unfold approxProp
  rw [Finset.sum_eq_single (⌊t * ((n + 1 : ℕ) : ℝ) / s⌋₊)]
  · exact Set.indicator_of_mem ht_mem _
  · intro j hj hjk
    exact Set.indicator_of_notMem (hdisj j hj hjk) _
  · intro hnot
    exact False.elim (hnot hk_mem)

theorem tendsto_approxProp_of_mem_Ioo
    {H M_U : ℝ} {U : ℝ → ℝ → (X →L[ℝ] X)} {f : ℝ → X} {s t : ℝ}
    (hsH : s ≤ H) (ht : t ∈ Ioo 0 s)
    (hU_id : ∀ r ∈ Icc 0 H, U r r = ContinuousLinearMap.id ℝ X)
    (hU_coc : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ H → (U c b).comp (U b a) = U c a)
    (hU_cont : ∀ a ∈ Icc 0 H, ∀ g : X, ContinuousOn (fun b => U b a g) (Icc a H))
    (hU_bd : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → ‖U b a‖ ≤ M_U) :
    Tendsto (fun n : ℕ => approxProp U f s n t) atTop (𝓝 (U s t (f t))) := by
  let r_n : ℕ → ℝ := fun n => gridPt s n (⌊t * ((n + 1 : ℕ) : ℝ) / s⌋₊ + 1)
  have hrn_bounds : ∀ n : ℕ, t ≤ r_n n ∧ r_n n ≤ s ∧ r_n n - t ≤ s / ((n + 1 : ℕ) : ℝ) := by
    intro n
    obtain ⟨_, ht_mem, hr_le_s, hdiff, _⟩ := gridPt_Properties ht n
    exact ⟨ht_mem.2.le, hr_le_s, hdiff⟩
  have hrn_tendsto : Tendsto r_n atTop (𝓝 t) := by
    have h0 : Tendsto (fun n : ℕ => r_n n - t) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => sub_nonneg.2 (hrn_bounds n).1) (fun n => (hrn_bounds n).2.2) ?_
      have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      exact tendsto_const_nhds.div_atTop hnat
    simpa using h0.add_const t
  have hrn_nhdsWithin : Tendsto r_n atTop (𝓝[Icc t H] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hrn_tendsto
      (Eventually.of_forall fun n => ⟨(hrn_bounds n).1, (hrn_bounds n).2.1.trans hsH⟩)
  have ht_Icc : t ∈ Icc 0 H := ⟨ht.1.le, ht.2.le.trans hsH⟩
  have hcont_t := (hU_cont t ht_Icc (f t)) t ⟨le_rfl, ht_Icc.2⟩
  have hU_rn_t : Tendsto (fun n : ℕ => U (r_n n) t (f t)) atTop (𝓝 (f t)) := by
    have h := hcont_t.tendsto.comp hrn_nhdsWithin
    rwa [hU_id t ht_Icc, ContinuousLinearMap.id_apply] at h
  have hnorm_zero : Tendsto (fun n : ℕ => ‖f t - U (r_n n) t (f t)‖) atTop (𝓝 0) := by
    simpa [sub_self] using ((tendsto_const_nhds (x := f t)).sub hU_rn_t).norm
  have hbound : ∀ n : ℕ,
      ‖approxProp U f s n t - U s t (f t)‖ ≤ M_U * ‖f t - U (r_n n) t (f t)‖ := by
    intro n
    rw [approxProp_eq_at_grid ht n]
    have hcoc := hU_coc t (r_n n) s ht.1.le (hrn_bounds n).1 (hrn_bounds n).2.1 hsH
    have hsub : U s (r_n n) (f t) - U s t (f t) =
        U s (r_n n) (f t - U (r_n n) t (f t)) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, hcoc]
    rw [hsub]
    calc ‖U s (r_n n) (f t - U (r_n n) t (f t))‖
        ≤ ‖U s (r_n n)‖ * ‖f t - U (r_n n) t (f t)‖ := (U s (r_n n)).le_opNorm _
      _ ≤ M_U * ‖f t - U (r_n n) t (f t)‖ :=
        mul_le_mul_of_nonneg_right
          (hU_bd (r_n n) s (ht.1.le.trans (hrn_bounds n).1) (hrn_bounds n).2.1 hsH)
          (norm_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using hnorm_zero.const_mul M_U)

/-- Bochner integrability of `t ↦ U s t (f t)` on `Ioc 0 s` whenever `f` is Bochner integrable on
`Ioc 0 s` and `U` is a strongly continuous cocycle bounded by `M_U` on `[0, H]`. -/
theorem integrableOn_propagator_apply
    {H M_U : ℝ} {U : ℝ → ℝ → (X →L[ℝ] X)} {f : ℝ → X} {s : ℝ}
    (hs : s ∈ Icc 0 H) (_hM_U : 0 ≤ M_U)
    (hU_id : ∀ r ∈ Icc 0 H, U r r = ContinuousLinearMap.id ℝ X)
    (hU_coc : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ H → (U c b).comp (U b a) = U c a)
    (hU_cont : ∀ a ∈ Icc 0 H, ∀ g : X, ContinuousOn (fun b => U b a g) (Icc a H))
    (hU_bd : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → ‖U b a‖ ≤ M_U)
    (hf : IntegrableOn f (Ioc 0 s) volume) :
    IntegrableOn (fun t => U s t (f t)) (Ioc 0 s) volume := by
  rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
  · rw [Ioc_self]
    exact integrableOn_empty
  · have hae_ne_s : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ s :=
      compl_mem_ae_iff.2 (measure_singleton s)
    have hae_mem_Ioo : ∀ᵐ t ∂volume.restrict (Ioc 0 s), t ∈ Ioo 0 s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae hae_ne_s] with t ht hne
      exact ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    have hmeas : AEStronglyMeasurable (fun t => U s t (f t)) (volume.restrict (Ioc 0 s)) := by
      refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun n t => approxProp U f s n t)
        (fun n => aestronglyMeasurable_approxProp U s n hf.1) ?_
      filter_upwards [hae_mem_Ioo] with t ht
      exact tendsto_approxProp_of_mem_Ioo hs.2 ht hU_id hU_coc hU_cont hU_bd
    refine Integrable.mono' (hf.norm.const_mul M_U) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc ‖U s t (f t)‖ ≤ ‖U s t‖ * ‖f t‖ := (U s t).le_opNorm (f t)
      _ ≤ M_U * ‖f t‖ :=
        mul_le_mul_of_nonneg_right (hU_bd t s ht.1.le ht.2 hs.2) (norm_nonneg _)

end PropagatorIntegrability

/-! ## 3. Block index arithmetic on `[0, N * L]` -/

/-- Block index `min (N - 1) ⌊r / L⌋₊` mapping `r ∈ [0, N * L]` to `n ∈ {0, …, N - 1}` with
`n * L ≤ r ≤ (n + 1) * L`. -/
def blkIdx (N : ℕ) (L r : ℝ) : ℕ :=
  min (N - 1) ⌊r / L⌋₊

theorem blkIdx_lt {N : ℕ} (hN : 1 ≤ N) (L r : ℝ) : blkIdx N L r < N := by
  unfold blkIdx
  have h1 : min (N - 1) ⌊r / L⌋₊ ≤ N - 1 := min_le_left _ _
  omega

theorem blkIdx_zero (N : ℕ) (L : ℝ) : blkIdx N L 0 = 0 := by
  unfold blkIdx
  simp

theorem blkIdx_mono {N : ℕ} {L s r : ℝ} (hL : 0 < L) (hsr : s ≤ r) :
    blkIdx N L s ≤ blkIdx N L r := by
  unfold blkIdx
  exact min_le_min_left (N - 1) (Nat.floor_mono (div_le_div_of_nonneg_right hsr hL.le))

theorem blkIdx_left_le {N : ℕ} {L r : ℝ} (hL : 0 < L) (hr0 : 0 ≤ r) :
    (blkIdx N L r : ℝ) * L ≤ r := by
  have h1 : (blkIdx N L r : ℝ) ≤ (⌊r / L⌋₊ : ℝ) := by
    exact_mod_cast min_le_right (N - 1) ⌊r / L⌋₊
  have h2 : (⌊r / L⌋₊ : ℝ) ≤ r / L := Nat.floor_le (div_nonneg hr0 hL.le)
  exact (le_div_iff₀ hL).1 (h1.trans h2)

theorem le_blkIdx_right {N : ℕ} {L r : ℝ} (hN : 1 ≤ N) (hL : 0 < L) (hrH : r ≤ (N : ℝ) * L) :
    r ≤ ((blkIdx N L r + 1 : ℕ) : ℝ) * L := by
  unfold blkIdx
  rcases le_total (N - 1) ⌊r / L⌋₊ with h | h
  · rw [min_eq_left h]
    have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
    rw [hN1]
    exact hrH
  · rw [min_eq_right h]
    have hlt : r / L < ((⌊r / L⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one (r / L)
    exact ((div_lt_iff₀ hL).1 hlt).le

theorem blkIdx_top {N : ℕ} (_hN : 1 ≤ N) {L : ℝ} (hL : 0 < L) :
    blkIdx N L ((N : ℝ) * L) = N - 1 := by
  unfold blkIdx
  have hdiv : (N : ℝ) * L / L = (N : ℝ) := mul_div_cancel_right₀ (N : ℝ) hL.ne'
  rw [hdiv, Nat.floor_natCast]
  exact min_eq_left (Nat.sub_le N 1)

theorem blkIdx_eq_of_mem_Ico {N k : ℕ} {L r : ℝ} (hk : k < N) (hL : 0 < L)
    (hr : r ∈ Ico ((k : ℝ) * L) (((k + 1 : ℕ) : ℝ) * L)) :
    blkIdx N L r = k := by
  unfold blkIdx
  have hk0 : 0 ≤ (k : ℝ) * L := mul_nonneg (Nat.cast_nonneg k) hL.le
  have hr0 : 0 ≤ r := hk0.trans hr.1
  have hfl : ⌊r / L⌋₊ = k := by
    rw [Nat.floor_eq_iff (div_nonneg hr0 hL.le)]
    refine ⟨(le_div_iff₀ hL).2 hr.1, (div_lt_iff₀ hL).2 ?_⟩
    simpa [Nat.cast_add, Nat.cast_one] using hr.2
  rw [hfl]
  exact min_eq_right (Nat.le_sub_one_of_lt hk)

theorem exp_neg_mul_le_one {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    Real.exp (-b * s) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  nlinarith

theorem one_le_exp_mul {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    1 ≤ Real.exp (a * s) := by
  rw [Real.one_le_exp_iff]
  positivity

/-! ## 4. Generic intermediate-time projections, Green kernels, and forward Duhamel reduction -/

section GenericGreen

variable {X E : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem grid_commute_Piu
    (N : ℕ) (L : ℝ) (U : ℝ → ℝ → (X →L[ℝ] X))
    (Iu : ℕ → (E →L[ℝ] X)) (Pu : ℕ → (X →L[ℝ] E))
    (Piu : ℕ → (X →L[ℝ] X)) (Bn : ℕ → (E →L[ℝ] E))
    (hPiu : ∀ n ≤ N, Piu n = (Iu n).comp (Pu n))
    (hU_id : ∀ n ≤ N, U ((n : ℝ) * L) ((n : ℝ) * L) = ContinuousLinearMap.id ℝ X)
    (hU_coc : ∀ j k : ℕ, j ≤ k → k < N →
      (U (((k + 1 : ℕ) : ℝ) * L) ((k : ℝ) * L)).comp (U ((k : ℝ) * L) ((j : ℝ) * L)) =
        U (((k + 1 : ℕ) : ℝ) * L) ((j : ℝ) * L))
    (hinter : ∀ n < N,
      (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (Iu n) = (Iu (n + 1)).comp (Bn n) ∧
      (Pu (n + 1)).comp (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)) = (Bn n).comp (Pu n)) :
    ∀ {j k : ℕ}, j ≤ k → k ≤ N →
      (U ((k : ℝ) * L) ((j : ℝ) * L)).comp (Piu j) =
        (Piu k).comp (U ((k : ℝ) * L) ((j : ℝ) * L)) := by
  intro j k hjk hkN
  have hstep : ∀ n < N,
      (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (Piu n) =
        (Piu (n + 1)).comp (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)) := by
    intro n hn
    rw [hPiu n hn.le, hPiu (n + 1) hn]
    calc (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp ((Iu n).comp (Pu n))
        = ((U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (Iu n)).comp (Pu n) :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = ((Iu (n + 1)).comp (Bn n)).comp (Pu n) := by rw [(hinter n hn).1]
      _ = (Iu (n + 1)).comp ((Bn n).comp (Pu n)) := ContinuousLinearMap.comp_assoc _ _ _
      _ = (Iu (n + 1)).comp ((Pu (n + 1)).comp (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L))) := by
          rw [← (hinter n hn).2]
      _ = ((Iu (n + 1)).comp (Pu (n + 1))).comp (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)) :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
  have hind : ∀ d : ℕ, j + d ≤ N →
      (U (((j + d : ℕ) : ℝ) * L) ((j : ℝ) * L)).comp (Piu j) =
        (Piu (j + d)).comp (U (((j + d : ℕ) : ℝ) * L) ((j : ℝ) * L)) := by
    intro d
    induction d with
    | zero =>
      intro hjN
      simp only [Nat.add_zero]
      rw [hU_id j hjN, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    | succ d ih =>
      intro hjd1
      have hadd : j + (d + 1) = j + d + 1 := (Nat.add_assoc j d 1).symm
      rw [hadd] at hjd1 ⊢
      have hjd_lt : j + d < N := hjd1
      have hcoc := hU_coc j (j + d) (Nat.le_add_right j d) hjd_lt
      calc (U (((j + d + 1 : ℕ) : ℝ) * L) ((j : ℝ) * L)).comp (Piu j)
          = ((U (((j + d + 1 : ℕ) : ℝ) * L) (((j + d : ℕ) : ℝ) * L)).comp
              (U (((j + d : ℕ) : ℝ) * L) ((j : ℝ) * L))).comp (Piu j) := by rw [hcoc]
        _ = (U (((j + d + 1 : ℕ) : ℝ) * L) (((j + d : ℕ) : ℝ) * L)).comp
              ((U (((j + d : ℕ) : ℝ) * L) ((j : ℝ) * L)).comp (Piu j)) :=
            ContinuousLinearMap.comp_assoc _ _ _
        _ = (U (((j + d + 1 : ℕ) : ℝ) * L) (((j + d : ℕ) : ℝ) * L)).comp
              ((Piu (j + d)).comp (U (((j + d : ℕ) : ℝ) * L) ((j : ℝ) * L))) := by
            rw [ih hjd_lt.le]
        _ = ((U (((j + d + 1 : ℕ) : ℝ) * L) (((j + d : ℕ) : ℝ) * L)).comp (Piu (j + d))).comp
              (U (((j + d : ℕ) : ℝ) * L) ((j : ℝ) * L)) :=
            (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = ((Piu (j + d + 1)).comp (U (((j + d + 1 : ℕ) : ℝ) * L) (((j + d : ℕ) : ℝ) * L))).comp
              (U (((j + d : ℕ) : ℝ) * L) ((j : ℝ) * L)) := by
            rw [hstep (j + d) hjd_lt]
        _ = (Piu (j + d + 1)).comp (U (((j + d + 1 : ℕ) : ℝ) * L) ((j : ℝ) * L)) := by
            rw [ContinuousLinearMap.comp_assoc, hcoc]
  have hjk_add : j + (k - j) = k := Nat.add_sub_of_le hjk
  have h := hind (k - j) (by rw [hjk_add]; exact hkN)
  rwa [hjk_add] at h

def genIntermProjU
    (Jt : E →L[ℝ] X) (Mn : E →L[ℝ] E) (Ft : X →L[ℝ] E) : X →L[ℝ] X :=
  Jt.comp (Mn.comp Ft)

theorem genIntermProjU_idem
    (Jt : E →L[ℝ] X) (Bn Mn : E →L[ℝ] E) (Ft : X →L[ℝ] E)
    (hFJ : Ft.comp Jt = Bn) (hMB : Mn * Bn = 1) :
    (genIntermProjU Jt Mn Ft).comp (genIntermProjU Jt Mn Ft) = genIntermProjU Jt Mn Ft := by
  have hMB' : Mn.comp Bn = ContinuousLinearMap.id ℝ E := hMB
  calc (genIntermProjU Jt Mn Ft).comp (genIntermProjU Jt Mn Ft)
      = Jt.comp ((Mn.comp (Ft.comp Jt)).comp (Mn.comp Ft)) := by
        ext1 x; rfl
    _ = Jt.comp ((Mn.comp Bn).comp (Mn.comp Ft)) := by
        rw [hFJ]
    _ = genIntermProjU Jt Mn Ft := by
        rw [hMB', ContinuousLinearMap.id_comp]; rfl

variable [CompleteSpace X] [CompleteSpace E]

/-- Full construction of the intermediate projections `Piu, Pic`, Green kernels `G_c, G_u`,
entrance functional `Γ_α`, `L¹ → L^∞` Green norm estimate, global propagator bound
`‖U r s‖ ≤ C_proj ^ (N + 2)`, and forward Duhamel reduction
`ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)` over generic Banach spaces `X, E`. -/
theorem gen_green_operators_full
    (N : ℕ) (L L₀ a' b' C_proj : ℝ)
    (hN : 1 ≤ N) (hL₀ : 1 ≤ L₀) (hL_bounds : L₀ ≤ L ∧ L ≤ 2 * L₀)
    (ha' : 0 < a') (hab' : a' < b') (hC_proj : 1 ≤ C_proj)
    (U : ℝ → ℝ → (X →L[ℝ] X))
    (Iu : ℕ → (E →L[ℝ] X)) (Pu : ℕ → (X →L[ℝ] E))
    (Piu Pic : ℕ → (X →L[ℝ] X)) (Bn Mn : ℕ → (E →L[ℝ] E))
    (hU_id : ∀ s ∈ Icc 0 ((N : ℝ) * L), U s s = ContinuousLinearMap.id ℝ X)
    (hU_coc : ∀ s r u : ℝ, 0 ≤ s → s ≤ r → r ≤ u → u ≤ (N : ℝ) * L →
      (U u r).comp (U r s) = U u s)
    (hU_cont : ∀ s ∈ Icc 0 ((N : ℝ) * L), ∀ g : X,
      ContinuousOn (fun r => U r s g) (Icc s ((N : ℝ) * L)))
    (hU_short : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (N : ℝ) * L → r - s ≤ L → ‖U r s‖ ≤ C_proj)
    (hproj : ∀ n ≤ N,
      (Pu n).comp (Iu n) = ContinuousLinearMap.id ℝ E ∧
      Piu n = (Iu n).comp (Pu n) ∧
      Pic n = ContinuousLinearMap.id ℝ X - Piu n)
    (hnorms : ∀ n ≤ N,
      ‖Iu n‖ ≤ C_proj ∧ ‖Pu n‖ ≤ C_proj ∧ ‖Piu n‖ ≤ C_proj ∧ ‖Pic n‖ ≤ C_proj)
    (hinv : ∀ n < N, Mn n * Bn n = 1 ∧ Bn n * Mn n = 1 ∧ ‖Mn n‖ ≤ Real.exp (-b' * L))
    (hinter : ∀ n < N,
      (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)).comp (Iu n) = (Iu (n + 1)).comp (Bn n) ∧
      (Pu (n + 1)).comp (U (((n + 1 : ℕ) : ℝ) * L) ((n : ℝ) * L)) = (Bn n).comp (Pu n))
    (hfwd_c : ∀ j k : ℕ, j ≤ k → k ≤ N →
      ‖(U ((k : ℝ) * L) ((j : ℝ) * L)).comp (Pic j)‖ ≤
        C_proj * Real.exp (a' * ((k : ℝ) * L - (j : ℝ) * L)))
    (hbwd_u : ∀ j k : ℕ, j ≤ k → k ≤ N →
      ∃ M_jk : E →L[ℝ] E,
        (U ((k : ℝ) * L) ((j : ℝ) * L)).comp ((Iu j).comp M_jk) = Iu k ∧
        M_jk.comp ((Pu k).comp (U ((k : ℝ) * L) ((j : ℝ) * L))) = Pu j ∧
        ‖M_jk‖ ≤ Real.exp (-b' * ((k : ℝ) * L - (j : ℝ) * L)) ∧
        ‖(Iu j).comp (M_jk.comp (Pu k))‖ ≤
          C_proj * Real.exp (-b' * ((k : ℝ) * L - (j : ℝ) * L))) :
    let H : ℝ := (N : ℝ) * L
    let C_green : ℝ := 4 * C_proj ^ 5
    (∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ H → ‖U r s‖ ≤ C_proj ^ (N + 2)) ∧
    ∃ (Piu_t Pic_t : ℝ → (X →L[ℝ] X))
      (G_c G_u : ℝ → ℝ → (X →L[ℝ] X))
      (Γ_α : ℝ → (X →L[ℝ] E)),
      (∀ t ∈ Icc 0 H,
        (Piu_t t).comp (Piu_t t) = Piu_t t ∧
        Pic_t t = ContinuousLinearMap.id ℝ X - Piu_t t ∧
        ‖Piu_t t‖ ≤ C_green ∧ ‖Pic_t t‖ ≤ C_green ∧
        ‖Γ_α t‖ ≤ C_green * Real.exp (-b' * t) ∧
        ∃ α_t : X →L[ℝ] E,
          Piu_t t = (U t ((blkIdx N L t : ℝ) * L)).comp ((Iu (blkIdx N L t)).comp α_t)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ H →
        (U t s).comp (Piu_t s) = (Piu_t t).comp (U t s) ∧
        (U t s).comp (Pic_t s) = (Pic_t t).comp (U t s) ∧
        G_c t s = (U t s).comp (Pic_t s) ∧
        (U t s).comp (G_u s t) = Piu_t t ∧
        ‖G_c t s‖ ≤ C_green * Real.exp (a' * (t - s)) ∧
        ‖G_u s t‖ ≤ C_green * Real.exp (-b' * (t - s)) ∧
        ∀ g : X, ∃ α_g : E,
          G_u s t g = U s ((blkIdx N L s : ℝ) * L) (Iu (blkIdx N L s) α_g)) ∧
      (∀ r : ℝ, G_u 0 r = -(Iu 0).comp (Γ_α r)) ∧
      (∀ t ∈ Icc 0 H, (Pu N).comp (G_c H t) = 0) ∧
      (∀ f : ℝ → X, IntegrableOn f (Ioc 0 H) volume →
        let ω : ℝ → X := fun s =>
          (∫ t in Ioc 0 s, G_c s t (f t)) - (∫ t in Ioc s H, G_u s t (f t))
        let α : E := ∫ t in Ioc 0 H, Γ_α t (f t)
        ω 0 = Iu 0 α ∧
        Pu N (ω H) = 0 ∧
        (∀ s ∈ Icc 0 H,
          ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖) ∧
        (∀ s ∈ Icc 0 H,
          ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t))) := by
  classical
  intro H C_green
  have hb' : 0 < b' := lt_trans ha' hab'
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one (hL₀.trans hL_bounds.1)
  have hH_nonneg : 0 ≤ H := by dsimp [H]; positivity
  let t : ℕ → ℝ := fun n => (n : ℝ) * L
  have ht_nonneg : ∀ n : ℕ, 0 ≤ t n := fun n => by dsimp [t]; positivity
  have ht_mono : ∀ {j k : ℕ}, j ≤ k → t j ≤ t k := fun hjk =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) hL_pos.le
  have ht_le_H : ∀ {n : ℕ}, n ≤ N → t n ≤ H := fun hn => ht_mono hn
  have ht_succ_sub : ∀ n : ℕ, t (n + 1) - t n = L := by
    intro n; dsimp [t]; push_cast; ring
  -- Global propagator norm bound ‖U r s‖ ≤ C_proj ^ (N + 2)
  have hU_grid_bd : ∀ j d : ℕ, j + d ≤ N → ‖U (t (j + d)) (t j)‖ ≤ C_proj ^ d := by
    intro j d
    induction d with
    | zero =>
      intro hjN
      simp only [Nat.add_zero, pow_zero]
      rw [hU_id (t j) ⟨ht_nonneg j, ht_le_H hjN⟩]
      exact ContinuousLinearMap.norm_id_le
    | succ d ih =>
      intro hjd1
      have hadd : j + (d + 1) = j + d + 1 := (Nat.add_assoc j d 1).symm
      rw [hadd] at hjd1 ⊢
      have hjd_lt : j + d < N := hjd1
      have hcoc := hU_coc (t j) (t (j + d)) (t (j + d + 1))
        (ht_nonneg j) (ht_mono (Nat.le_add_right j d))
        (ht_mono (Nat.le_succ (j + d))) (ht_le_H hjd1)
      have hstep := hU_short (t (j + d)) (t (j + d + 1))
        (ht_nonneg _) (ht_mono (Nat.le_succ _)) (ht_le_H hjd1)
        (by rw [ht_succ_sub])
      rw [← hcoc]
      calc ‖(U (t (j + d + 1)) (t (j + d))).comp (U (t (j + d)) (t j))‖
          ≤ ‖U (t (j + d + 1)) (t (j + d))‖ * ‖U (t (j + d)) (t j)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C_proj * C_proj ^ d :=
            mul_le_mul hstep (ih hjd_lt.le) (norm_nonneg _) (zero_le_one.trans hC_proj)
        _ = C_proj ^ (d + 1) := by ring
  have hblk_bounds : ∀ {r : ℝ}, r ∈ Icc 0 H →
      blkIdx N L r < N ∧
      0 ≤ t (blkIdx N L r) ∧
      t (blkIdx N L r) ≤ r ∧
      r ≤ t (blkIdx N L r + 1) ∧
      t (blkIdx N L r + 1) ≤ H ∧
      r - t (blkIdx N L r) ≤ L ∧
      t (blkIdx N L r + 1) - r ≤ L := by
    intro r hr
    have hn_lt : blkIdx N L r < N := blkIdx_lt hN L r
    have htn_le : t (blkIdx N L r) ≤ r := blkIdx_left_le hL_pos hr.1
    have hr_le : r ≤ t (blkIdx N L r + 1) := le_blkIdx_right hN hL_pos hr.2
    have hsub := ht_succ_sub (blkIdx N L r)
    exact ⟨hn_lt, ht_nonneg _, htn_le, hr_le, ht_le_H hn_lt, by linarith, by linarith⟩
  have hU_global_bd : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ H → ‖U r s‖ ≤ C_proj ^ (N + 2) := by
    intro s r hs hsr hrH
    rcases le_or_gt (r - s) L with hrsL | hrsL
    · calc ‖U r s‖ ≤ C_proj ^ 1 := by
            rw [pow_one]; exact hU_short s r hs hsr hrH hrsL
        _ ≤ C_proj ^ (N + 2) := pow_le_pow_right₀ hC_proj (by omega)
    · have hs_mem : s ∈ Icc 0 H := ⟨hs, hsr.trans hrH⟩
      have hr_mem : r ∈ Icc 0 H := ⟨hs.trans hsr, hrH⟩
      set j := blkIdx N L s
      set k := blkIdx N L r
      obtain ⟨hj_lt, _, _, hs_tj1, htj1_H, _, htj1_sub⟩ := hblk_bounds hs_mem
      obtain ⟨hk_lt, htk0, htk_r, hr_tk1, _, hr_sub, _⟩ := hblk_bounds hr_mem
      have hj_lt_k : j < k := by
        by_contra hnk
        have hkj : k ≤ j := not_lt.1 hnk
        have hr_le_tj1 : r ≤ t (j + 1) := hr_tk1.trans (ht_mono (Nat.add_le_add_right hkj 1))
        have hsub_j := ht_succ_sub j
        linarith
      have hj1_le_k : j + 1 ≤ k := hj_lt_k
      have htj1_le_tk : t (j + 1) ≤ t k := ht_mono hj1_le_k
      have hcoc1 := hU_coc s (t (j + 1)) r hs hs_tj1 (htj1_le_tk.trans htk_r) hrH
      have hcoc2 := hU_coc (t (j + 1)) (t k) r (ht_nonneg _) htj1_le_tk htk_r hrH
      have hU_r_tk := hU_short (t k) r htk0 htk_r hrH hr_sub
      have hU_tj1_s := hU_short s (t (j + 1)) hs hs_tj1 htj1_H htj1_sub
      have hadd_jk : (j + 1) + (k - (j + 1)) = k := Nat.add_sub_of_le hj1_le_k
      have hmid_d := hU_grid_bd (j + 1) (k - (j + 1)) (by rw [hadd_jk]; exact hk_lt.le)
      rw [hadd_jk] at hmid_d
      have hmid_N : ‖U (t k) (t (j + 1))‖ ≤ C_proj ^ N :=
        hmid_d.trans (pow_le_pow_right₀ hC_proj (by omega))
      rw [← hcoc1, ← hcoc2]
      calc ‖(U r (t k)).comp ((U (t k) (t (j + 1))).comp (U (t (j + 1)) s))‖
          ≤ ‖U r (t k)‖ * ‖(U (t k) (t (j + 1))).comp (U (t (j + 1)) s)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖U r (t k)‖ * (‖U (t k) (t (j + 1))‖ * ‖U (t (j + 1)) s‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
        _ ≤ C_proj * (C_proj ^ N * C_proj) :=
            mul_le_mul hU_r_tk
              (mul_le_mul hmid_N hU_tj1_s (norm_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ = C_proj ^ (N + 2) := by ring
  refine ⟨hU_global_bd, ?_⟩
  let Mjk (j k : ℕ) : E →L[ℝ] E :=
    if h : j ≤ k ∧ k ≤ N then Classical.choose (hbwd_u j k h.1 h.2) else 0
  have hMjk_spec : ∀ {j k : ℕ} (hjk : j ≤ k) (hkN : k ≤ N),
      (U (t k) (t j)).comp ((Iu j).comp (Mjk j k)) = Iu k ∧
      (Mjk j k).comp ((Pu k).comp (U (t k) (t j))) = Pu j ∧
      ‖Mjk j k‖ ≤ Real.exp (-b' * (t k - t j)) := by
    intro j k hjk hkN
    have hspec := Classical.choose_spec (hbwd_u j k hjk hkN)
    have heq : Mjk j k = Classical.choose (hbwd_u j k hjk hkN) := by
      dsimp [Mjk]
      simp only [hjk, hkN, and_self, ↓reduceDIte]
    rw [heq]
    exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩
  let J (r : ℝ) : E →L[ℝ] X :=
    (U r (t (blkIdx N L r))).comp (Iu (blkIdx N L r))
  let F_op (r : ℝ) : X →L[ℝ] E :=
    (Pu (blkIdx N L r + 1)).comp (U (t (blkIdx N L r + 1)) r)
  let Piu_t (r : ℝ) : X →L[ℝ] X :=
    genIntermProjU (J r) (Mn (blkIdx N L r)) (F_op r)
  let Pic_t (r : ℝ) : X →L[ℝ] X :=
    ContinuousLinearMap.id ℝ X - Piu_t r
  let G_c (r s : ℝ) : X →L[ℝ] X := (U r s).comp (Pic_t s)
  let G_u (s r : ℝ) : X →L[ℝ] X :=
    (J s).comp (((Mjk (blkIdx N L s) (blkIdx N L r)).comp (Mn (blkIdx N L r))).comp (F_op r))
  let Γ_α (r : ℝ) : X →L[ℝ] E :=
    -(((Mjk 0 (blkIdx N L r)).comp (Mn (blkIdx N L r))).comp (F_op r))
  -- Grid unstable-subspace forward transport and Mjk factorization
  have hIu_fwd : ∀ j ≤ N, ∃ B_j0 : E →L[ℝ] E,
      (U (t j) (t 0)).comp (Iu 0) = (Iu j).comp B_j0 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨ContinuousLinearMap.id ℝ E, ?_⟩
      rw [hU_id (t 0) ⟨ht_nonneg 0, ht_le_H (Nat.zero_le N)⟩,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    | succ j ih =>
      intro hj1N
      have hj_lt : j < N := hj1N
      obtain ⟨B_j0, hB_j0⟩ := ih hj_lt.le
      refine ⟨(Bn j).comp B_j0, ?_⟩
      have hcoc := hU_coc (t 0) (t j) (t (j + 1))
        (ht_nonneg 0) (ht_mono (Nat.zero_le j)) (ht_mono (Nat.le_succ j)) (ht_le_H hj1N)
      calc (U (t (j + 1)) (t 0)).comp (Iu 0)
          = (U (t (j + 1)) (t j)).comp ((U (t j) (t 0)).comp (Iu 0)) := by
            rw [← hcoc]; ext1 x; rfl
        _ = (U (t (j + 1)) (t j)).comp ((Iu j).comp B_j0) := by rw [hB_j0]
        _ = ((U (t (j + 1)) (t j)).comp (Iu j)).comp B_j0 := by ext1 x; rfl
        _ = ((Iu (j + 1)).comp (Bn j)).comp B_j0 := by rw [(hinter j hj_lt).1]
        _ = (Iu (j + 1)).comp ((Bn j).comp B_j0) := rfl
  have hIu_Mjk_eq : ∀ {j k : ℕ}, j ≤ k → k ≤ N →
      (Iu j).comp (Mjk j k) = (U (t j) (t 0)).comp ((Iu 0).comp (Mjk 0 k)) := by
    intro j k hjk hkN
    obtain ⟨B_j0, hB_j0⟩ := hIu_fwd j (hjk.trans hkN)
    have hRHS : (U (t j) (t 0)).comp ((Iu 0).comp (Mjk 0 k)) =
        (Iu j).comp (B_j0.comp (Mjk 0 k)) := by
      calc (U (t j) (t 0)).comp ((Iu 0).comp (Mjk 0 k))
          = ((U (t j) (t 0)).comp (Iu 0)).comp (Mjk 0 k) := by ext1 x; rfl
        _ = (Iu j).comp (B_j0.comp (Mjk 0 k)) := by rw [hB_j0]; rfl
    rw [hRHS]
    congr 1
    have hcoc := hU_coc (t 0) (t j) (t k)
      (ht_nonneg 0) (ht_mono (Nat.zero_le j)) (ht_mono hjk) (ht_le_H hkN)
    have h0k := (hMjk_spec (Nat.zero_le k) hkN).1
    have hjk_2 := (hMjk_spec hjk hkN).2.1
    have hUk : (U (t k) (t j)).comp ((Iu j).comp (B_j0.comp (Mjk 0 k))) = Iu k := by
      rw [← hRHS, ← ContinuousLinearMap.comp_assoc, hcoc]
      exact h0k
    calc Mjk j k
        = (Mjk j k).comp ((Pu k).comp (Iu k)) := by
          rw [(hproj k hkN).1, ContinuousLinearMap.comp_id]
      _ = ((Mjk j k).comp ((Pu k).comp (U (t k) (t j)))).comp
            ((Iu j).comp (B_j0.comp (Mjk 0 k))) := by
          rw [← hUk]; ext1 x; rfl
      _ = (Pu j).comp ((Iu j).comp (B_j0.comp (Mjk 0 k))) := by rw [hjk_2]
      _ = B_j0.comp (Mjk 0 k) := by
          rw [← ContinuousLinearMap.comp_assoc, (hproj j (hjk.trans hkN)).1,
            ContinuousLinearMap.id_comp]
  have hFJ : ∀ {r : ℝ}, r ∈ Icc 0 H → (F_op r).comp (J r) = Bn (blkIdx N L r) := by
    intro r hr
    set n := blkIdx N L r
    obtain ⟨hn_lt, htn0, htn_r, hr_tn1, htn1_H, _, _⟩ := hblk_bounds hr
    have hcoc := hU_coc (t n) r (t (n + 1)) htn0 htn_r hr_tn1 htn1_H
    calc (F_op r).comp (J r)
        = (Pu (n + 1)).comp (((U (t (n + 1)) r).comp (U r (t n))).comp (Iu n)) := by
          ext1 x; rfl
      _ = (Pu (n + 1)).comp ((U (t (n + 1)) (t n)).comp (Iu n)) := by rw [hcoc]
      _ = (Pu (n + 1)).comp ((Iu (n + 1)).comp (Bn n)) := by rw [(hinter n hn_lt).1]
      _ = ((Pu (n + 1)).comp (Iu (n + 1))).comp (Bn n) :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = Bn n := by rw [(hproj (n + 1) hn_lt).1, ContinuousLinearMap.id_comp]
  have hJ_norm : ∀ {r : ℝ}, r ∈ Icc 0 H → ‖J r‖ ≤ C_proj ^ 2 := by
    intro r hr
    obtain ⟨hn_lt, htn0, htn_r, _, _, hr_sub, _⟩ := hblk_bounds hr
    have hU_n := hU_short (t (blkIdx N L r)) r htn0 htn_r hr.2 hr_sub
    have hIu_n := (hnorms (blkIdx N L r) hn_lt.le).1
    calc ‖J r‖ ≤ ‖U r (t (blkIdx N L r))‖ * ‖Iu (blkIdx N L r)‖ :=
          (U r (t (blkIdx N L r))).opNorm_comp_le _
      _ ≤ C_proj * C_proj := mul_le_mul hU_n hIu_n (norm_nonneg _) (by positivity)
      _ = C_proj ^ 2 := by ring
  have hF_norm : ∀ {r : ℝ}, r ∈ Icc 0 H → ‖F_op r‖ ≤ C_proj ^ 2 := by
    intro r hr
    obtain ⟨hn_lt, _, _, hr_tn1, htn1_H, _, htn1_sub⟩ := hblk_bounds hr
    have hU_n := hU_short r (t (blkIdx N L r + 1)) hr.1 hr_tn1 htn1_H htn1_sub
    have hPu_n := (hnorms (blkIdx N L r + 1) hn_lt).2.1
    calc ‖F_op r‖ ≤ ‖Pu (blkIdx N L r + 1)‖ * ‖U (t (blkIdx N L r + 1)) r‖ :=
          (Pu (blkIdx N L r + 1)).opNorm_comp_le _
      _ ≤ C_proj * C_proj := mul_le_mul hPu_n hU_n (norm_nonneg _) (by positivity)
      _ = C_proj ^ 2 := by ring
  have hMn_le_one : ∀ {n : ℕ}, n < N → ‖Mn n‖ ≤ 1 := by
    intro n hn
    refine (hinv n hn).2.2.trans ?_
    apply Real.exp_le_one_iff.2
    nlinarith
  have hPiu_norm : ∀ {r : ℝ}, r ∈ Icc 0 H → ‖Piu_t r‖ ≤ C_proj ^ 4 := by
    intro r hr
    obtain ⟨hn_lt, _, _, _, _, _, _⟩ := hblk_bounds hr
    have hMF : ‖(Mn (blkIdx N L r)).comp (F_op r)‖ ≤ 1 * C_proj ^ 2 :=
      ((Mn (blkIdx N L r)).opNorm_comp_le (F_op r)).trans
        (mul_le_mul (hMn_le_one hn_lt) (hF_norm hr) (norm_nonneg _) zero_le_one)
    calc ‖Piu_t r‖ ≤ ‖J r‖ * ‖(Mn (blkIdx N L r)).comp (F_op r)‖ := (J r).opNorm_comp_le _
      _ ≤ C_proj ^ 2 * (1 * C_proj ^ 2) :=
          mul_le_mul (hJ_norm hr) hMF (norm_nonneg _) (by positivity)
      _ = C_proj ^ 4 := by ring
  have hPic_norm : ∀ {r : ℝ}, r ∈ Icc 0 H → ‖Pic_t r‖ ≤ 2 * C_proj ^ 4 := by
    intro r hr
    have hC4 : 1 ≤ C_proj ^ 4 := one_le_pow₀ hC_proj
    calc ‖Pic_t r‖ ≤ ‖ContinuousLinearMap.id ℝ X‖ + ‖Piu_t r‖ := norm_sub_le _ _
      _ ≤ 1 + C_proj ^ 4 := add_le_add ContinuousLinearMap.norm_id_le (hPiu_norm hr)
      _ ≤ 2 * C_proj ^ 4 := by linarith
  have hMjk_Mn_norm : ∀ {s r : ℝ}, 0 ≤ s → s ≤ r → r ≤ H →
      ‖(Mjk (blkIdx N L s) (blkIdx N L r)).comp (Mn (blkIdx N L r))‖ ≤
        Real.exp (-b' * (r - s)) := by
    intro s r hs hsr hrH
    set j := blkIdx N L s
    set k := blkIdx N L r
    have hj_lt : j < N := blkIdx_lt hN L s
    have hk_lt : k < N := blkIdx_lt hN L r
    have hjk : j ≤ k := blkIdx_mono hL_pos hsr
    have htj_le : t j ≤ s := blkIdx_left_le hL_pos hs
    have hr_le_tk1 : r ≤ t (k + 1) := le_blkIdx_right hN hL_pos hrH
    have htk1_sub : t (k + 1) - t k = L := ht_succ_sub k
    have hMjk_n := (hMjk_spec hjk hk_lt.le).2.2
    have hMn_n := (hinv k hk_lt).2.2
    have hexp_le : Real.exp (-b' * (t k - t j) + -b' * L) ≤ Real.exp (-b' * (r - s)) := by
      apply Real.exp_le_exp.2
      have hrs_le : r - s ≤ (t k - t j) + L := by linarith
      nlinarith
    calc ‖(Mjk j k).comp (Mn k)‖
        ≤ ‖Mjk j k‖ * ‖Mn k‖ := (Mjk j k).opNorm_comp_le (Mn k)
      _ ≤ Real.exp (-b' * (t k - t j)) * Real.exp (-b' * L) :=
          mul_le_mul hMjk_n hMn_n (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-b' * (t k - t j) + -b' * L) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-b' * (r - s)) := hexp_le
  have hGu_norm : ∀ {s r : ℝ}, 0 ≤ s → s ≤ r → r ≤ H →
      ‖G_u s r‖ ≤ C_proj ^ 4 * Real.exp (-b' * (r - s)) := by
    intro s r hs hsr hrH
    have hs_mem : s ∈ Icc 0 H := ⟨hs, hsr.trans hrH⟩
    have hr_mem : r ∈ Icc 0 H := ⟨hs.trans hsr, hrH⟩
    have hMMF :
        ‖((Mjk (blkIdx N L s) (blkIdx N L r)).comp (Mn (blkIdx N L r))).comp (F_op r)‖ ≤
          Real.exp (-b' * (r - s)) * C_proj ^ 2 :=
      (((Mjk (blkIdx N L s) (blkIdx N L r)).comp (Mn (blkIdx N L r))).opNorm_comp_le (F_op r)).trans
        (mul_le_mul (hMjk_Mn_norm hs hsr hrH) (hF_norm hr_mem) (norm_nonneg _) (Real.exp_pos _).le)
    calc ‖G_u s r‖
        ≤ ‖J s‖ * ‖((Mjk (blkIdx N L s) (blkIdx N L r)).comp (Mn (blkIdx N L r))).comp (F_op r)‖ :=
          (J s).opNorm_comp_le _
      _ ≤ C_proj ^ 2 * (Real.exp (-b' * (r - s)) * C_proj ^ 2) :=
          mul_le_mul (hJ_norm hs_mem) hMMF (norm_nonneg _) (by positivity)
      _ = C_proj ^ 4 * Real.exp (-b' * (r - s)) := by ring
  have hΓ_norm : ∀ {r : ℝ}, r ∈ Icc 0 H → ‖Γ_α r‖ ≤ C_proj ^ 4 * Real.exp (-b' * r) := by
    intro r hr
    have h0_eq : blkIdx N L 0 = 0 := blkIdx_zero N L
    have hMM : ‖(Mjk 0 (blkIdx N L r)).comp (Mn (blkIdx N L r))‖ ≤ Real.exp (-b' * r) := by
      have h := hMjk_Mn_norm le_rfl hr.1 hr.2
      rwa [h0_eq, sub_zero] at h
    have hMMF : ‖Γ_α r‖ ≤ Real.exp (-b' * r) * C_proj ^ 2 := by
      dsimp [Γ_α]
      rw [norm_neg]
      exact (((Mjk 0 (blkIdx N L r)).comp (Mn (blkIdx N L r))).opNorm_comp_le (F_op r)).trans
        (mul_le_mul hMM (hF_norm hr) (norm_nonneg _) (Real.exp_pos _).le)
    have hC24 : C_proj ^ 2 ≤ C_proj ^ 4 := by nlinarith [one_le_pow₀ (n := 2) hC_proj]
    calc ‖Γ_α r‖ ≤ Real.exp (-b' * r) * C_proj ^ 2 := hMMF
      _ ≤ Real.exp (-b' * r) * C_proj ^ 4 :=
          mul_le_mul_of_nonneg_left hC24 (Real.exp_pos _).le
      _ = C_proj ^ 4 * Real.exp (-b' * r) := by ring
  have hRight_Piu : ∀ {s : ℝ}, s ∈ Icc 0 H →
      (U (t (blkIdx N L s + 1)) s).comp (Piu_t s) =
        (Piu (blkIdx N L s + 1)).comp (U (t (blkIdx N L s + 1)) s) := by
    intro s hs
    set j := blkIdx N L s
    obtain ⟨hj_lt, htj0, htj_s, hs_tj1, htj1_H, _, _⟩ := hblk_bounds hs
    have hcoc := hU_coc (t j) s (t (j + 1)) htj0 htj_s hs_tj1 htj1_H
    have hBM : (Bn j).comp (Mn j) = ContinuousLinearMap.id ℝ E := (hinv j hj_lt).2.1
    have hUJ : ((U (t (j + 1)) s).comp (J s)).comp (Mn j) = Iu (j + 1) := by
      calc ((U (t (j + 1)) s).comp (J s)).comp (Mn j)
          = (((U (t (j + 1)) s).comp (U s (t j))).comp (Iu j)).comp (Mn j) := by ext1 x; rfl
        _ = ((U (t (j + 1)) (t j)).comp (Iu j)).comp (Mn j) := by rw [hcoc]
        _ = ((Iu (j + 1)).comp (Bn j)).comp (Mn j) := by rw [(hinter j hj_lt).1]
        _ = (Iu (j + 1)).comp ((Bn j).comp (Mn j)) := ContinuousLinearMap.comp_assoc _ _ _
        _ = Iu (j + 1) := by rw [hBM, ContinuousLinearMap.comp_id]
    calc (U (t (j + 1)) s).comp (Piu_t s)
        = (((U (t (j + 1)) s).comp (J s)).comp (Mn j)).comp (F_op s) := by ext1 x; rfl
      _ = (Iu (j + 1)).comp ((Pu (j + 1)).comp (U (t (j + 1)) s)) := by rw [hUJ]
      _ = (Piu (j + 1)).comp (U (t (j + 1)) s) := by
          rw [(hproj (j + 1) hj_lt).2.1, ContinuousLinearMap.comp_assoc]
  have hLeft_Piu : ∀ {r : ℝ}, r ∈ Icc 0 H →
      (Piu_t r).comp (U r (t (blkIdx N L r))) =
        (U r (t (blkIdx N L r))).comp (Piu (blkIdx N L r)) := by
    intro r hr
    set k := blkIdx N L r
    obtain ⟨hk_lt, htk0, htk_r, hr_tk1, htk1_H, _, _⟩ := hblk_bounds hr
    have hcoc := hU_coc (t k) r (t (k + 1)) htk0 htk_r hr_tk1 htk1_H
    have hMB : (Mn k).comp (Bn k) = ContinuousLinearMap.id ℝ E := (hinv k hk_lt).1
    have hMFU : (Mn k).comp ((F_op r).comp (U r (t k))) = Pu k := by
      calc (Mn k).comp ((F_op r).comp (U r (t k)))
          = (Mn k).comp ((Pu (k + 1)).comp ((U (t (k + 1)) r).comp (U r (t k)))) := by
            ext1 x; rfl
        _ = (Mn k).comp ((Pu (k + 1)).comp (U (t (k + 1)) (t k))) := by rw [hcoc]
        _ = (Mn k).comp ((Bn k).comp (Pu k)) := by rw [(hinter k hk_lt).2]
        _ = ((Mn k).comp (Bn k)).comp (Pu k) := (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = Pu k := by rw [hMB, ContinuousLinearMap.id_comp]
    calc (Piu_t r).comp (U r (t k))
        = (J r).comp ((Mn k).comp ((F_op r).comp (U r (t k)))) := by ext1 x; rfl
      _ = ((U r (t k)).comp (Iu k)).comp (Pu k) := by rw [hMFU]
      _ = (U r (t k)).comp (Piu k) := by
          rw [(hproj k hk_lt.le).2.1, ContinuousLinearMap.comp_assoc]
  have hComm_Piu : ∀ {s r : ℝ}, 0 ≤ s → s ≤ r → r ≤ H →
      (U r s).comp (Piu_t s) = (Piu_t r).comp (U r s) := by
    intro s r hs hsr hrH
    have hs_mem : s ∈ Icc 0 H := ⟨hs, hsr.trans hrH⟩
    have hr_mem : r ∈ Icc 0 H := ⟨hs.trans hsr, hrH⟩
    set j := blkIdx N L s
    set k := blkIdx N L r
    have hjk : j ≤ k := blkIdx_mono hL_pos hsr
    rcases eq_or_lt_of_le hjk with hjeqk | hjltk
    · obtain ⟨hk_lt, htk0, htk_r, hr_tk1, htk1_H, _, _⟩ := hblk_bounds hr_mem
      have htk_s : t k ≤ s := by rw [← hjeqk]; exact (hblk_bounds hs_mem).2.2.1
      have hcoc1 := hU_coc (t k) s r htk0 htk_s hsr hrH
      have hcoc2 := hU_coc s r (t (k + 1)) hs hsr hr_tk1 htk1_H
      have hjeqk' : blkIdx N L s = k := hjeqk
      have hkeqk' : blkIdx N L r = k := rfl
      dsimp [Piu_t, genIntermProjU, J, F_op]
      rw [hjeqk', hkeqk']
      calc (U r s).comp (((U s (t k)).comp (Iu k)).comp
            ((Mn k).comp ((Pu (k + 1)).comp (U (t (k + 1)) s))))
          = (((U r s).comp (U s (t k))).comp (Iu k)).comp
              ((Mn k).comp ((Pu (k + 1)).comp (U (t (k + 1)) s))) := by ext1 x; rfl
        _ = ((U r (t k)).comp (Iu k)).comp
              ((Mn k).comp ((Pu (k + 1)).comp ((U (t (k + 1)) r).comp (U r s)))) := by
            rw [hcoc1, hcoc2]
        _ = (((U r (t k)).comp (Iu k)).comp
              ((Mn k).comp ((Pu (k + 1)).comp (U (t (k + 1)) r)))).comp (U r s) := by
            ext1 x; rfl
    · have hj1_le_k : j + 1 ≤ k := hjltk
      obtain ⟨hj_lt, _, _, hs_tj1, htj1_H, _, _⟩ := hblk_bounds hs_mem
      obtain ⟨hk_lt, htk0, htk_r, _, _, _, _⟩ := hblk_bounds hr_mem
      have htj1_le_tk : t (j + 1) ≤ t k := ht_mono hj1_le_k
      have hcoc_a := hU_coc s (t (j + 1)) r hs hs_tj1 (htj1_le_tk.trans htk_r) hrH
      have hcoc_b := hU_coc (t (j + 1)) (t k) r (ht_nonneg _) htj1_le_tk htk_r hrH
      have hcoc_c := hU_coc s (t (j + 1)) (t k) hs hs_tj1 htj1_le_tk (ht_le_H hk_lt.le)
      have hcoc_d := hU_coc s (t k) r hs (hs_tj1.trans htj1_le_tk) htk_r hrH
      have hgrid := grid_commute_Piu N L U Iu Pu Piu Bn
        (fun n hn => (hproj n hn).2.1)
        (fun n hn => hU_id (t n) ⟨ht_nonneg n, ht_le_H hn⟩)
        (fun m n hmn hn => hU_coc (t m) (t n) (t (n + 1))
          (ht_nonneg m) (ht_mono hmn) (ht_mono (Nat.le_succ n)) (ht_le_H hn))
        hinter hj1_le_k hk_lt.le
      calc (U r s).comp (Piu_t s)
          = (U r (t k)).comp ((U (t k) (t (j + 1))).comp ((U (t (j + 1)) s).comp (Piu_t s))) := by
            rw [← hcoc_a, ← hcoc_b]; ext1 x; rfl
        _ = (U r (t k)).comp ((U (t k) (t (j + 1))).comp
              ((Piu (j + 1)).comp (U (t (j + 1)) s))) := by
            rw [hRight_Piu hs_mem]
        _ = (U r (t k)).comp (((U (t k) (t (j + 1))).comp (Piu (j + 1))).comp
              (U (t (j + 1)) s)) := by ext1 x; rfl
        _ = (U r (t k)).comp (((Piu k).comp (U (t k) (t (j + 1)))).comp (U (t (j + 1)) s)) := by
            rw [hgrid]
        _ = ((U r (t k)).comp (Piu k)).comp (U (t k) s) := by
            rw [← hcoc_c]; ext1 x; rfl
        _ = ((Piu_t r).comp (U r (t k))).comp (U (t k) s) := by
            rw [hLeft_Piu hr_mem]
        _ = (Piu_t r).comp (U r s) := by
            rw [ContinuousLinearMap.comp_assoc, hcoc_d]
  have hComm_Pic : ∀ {s r : ℝ}, 0 ≤ s → s ≤ r → r ≤ H →
      (U r s).comp (Pic_t s) = (Pic_t r).comp (U r s) := by
    intro s r hs hsr hrH
    dsimp [Pic_t]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
      hComm_Piu hs hsr hrH]
  have hU_Gu : ∀ {s r : ℝ}, 0 ≤ s → s ≤ r → r ≤ H →
      (U r s).comp (G_u s r) = Piu_t r := by
    intro s r hs hsr hrH
    have hs_mem : s ∈ Icc 0 H := ⟨hs, hsr.trans hrH⟩
    have hr_mem : r ∈ Icc 0 H := ⟨hs.trans hsr, hrH⟩
    set j := blkIdx N L s
    set k := blkIdx N L r
    have hj_lt : j < N := blkIdx_lt hN L s
    have hk_lt : k < N := blkIdx_lt hN L r
    have hjk : j ≤ k := blkIdx_mono hL_pos hsr
    have htj_s : t j ≤ s := (hblk_bounds hs_mem).2.2.1
    have htk_r : t k ≤ r := (hblk_bounds hr_mem).2.2.1
    have hcoc1 := hU_coc (t j) s r (ht_nonneg j) htj_s hsr hrH
    have hcoc2 := hU_coc (t j) (t k) r (ht_nonneg j) (ht_mono hjk) htk_r hrH
    have hM1 := (hMjk_spec hjk hk_lt.le).1
    have hUJM : ((U r s).comp (J s)).comp (Mjk j k) = J r := by
      calc ((U r s).comp (J s)).comp (Mjk j k)
          = ((U r s).comp (U s (t j))).comp ((Iu j).comp (Mjk j k)) := by ext1 x; rfl
        _ = (U r (t j)).comp ((Iu j).comp (Mjk j k)) := by rw [hcoc1]
        _ = (U r (t k)).comp ((U (t k) (t j)).comp ((Iu j).comp (Mjk j k))) := by
            rw [← hcoc2]; ext1 x; rfl
        _ = (U r (t k)).comp (Iu k) := by rw [hM1]
        _ = J r := rfl
    calc (U r s).comp (G_u s r)
        = (((U r s).comp (J s)).comp (Mjk j k)).comp ((Mn k).comp (F_op r)) := by ext1 x; rfl
      _ = (J r).comp ((Mn k).comp (F_op r)) := by rw [hUJM]
      _ = Piu_t r := rfl
  -- Rank-two factorizations of G_u, Piu_t, and G_c through (U s 0) ∘ (Iu 0) ∘ (Γ_α r)
  have hGu_eq_U0 : ∀ {s r : ℝ}, 0 ≤ s → s ≤ r → r ≤ H →
      G_u s r = -((U s 0).comp (Iu 0)).comp (Γ_α r) := by
    intro s r hs hsr hrH
    have hs_mem : s ∈ Icc 0 H := ⟨hs, hsr.trans hrH⟩
    set j := blkIdx N L s
    set k := blkIdx N L r
    have hk_lt : k < N := blkIdx_lt hN L r
    have hjk : j ≤ k := blkIdx_mono hL_pos hsr
    have htj_s : t j ≤ s := (hblk_bounds hs_mem).2.2.1
    have ht0 : t 0 = 0 := by dsimp [t]; ring
    have hcoc := hU_coc (t 0) (t j) s (ht_nonneg 0) (ht_mono (Nat.zero_le j)) htj_s hs_mem.2
    have hJM : (J s).comp (Mjk j k) = (U s 0).comp ((Iu 0).comp (Mjk 0 k)) := by
      calc (J s).comp (Mjk j k)
          = (U s (t j)).comp ((Iu j).comp (Mjk j k)) := by ext1 x; rfl
        _ = (U s (t j)).comp ((U (t j) (t 0)).comp ((Iu 0).comp (Mjk 0 k))) := by
            rw [hIu_Mjk_eq hjk hk_lt.le]
        _ = ((U s (t j)).comp (U (t j) (t 0))).comp ((Iu 0).comp (Mjk 0 k)) := by ext1 x; rfl
        _ = (U s 0).comp ((Iu 0).comp (Mjk 0 k)) := by rw [hcoc, ht0]
    dsimp [G_u, Γ_α]
    rw [ContinuousLinearMap.comp_neg, neg_neg]
    calc (J s).comp (((Mjk j k).comp (Mn k)).comp (F_op r))
        = ((J s).comp (Mjk j k)).comp ((Mn k).comp (F_op r)) := by ext1 x; rfl
      _ = ((U s 0).comp ((Iu 0).comp (Mjk 0 k))).comp ((Mn k).comp (F_op r)) := by rw [hJM]
      _ = ((U s 0).comp (Iu 0)).comp (((Mjk 0 k).comp (Mn k)).comp (F_op r)) := by ext1 x; rfl
  have hPiu_eq_U0 : ∀ {r : ℝ}, r ∈ Icc 0 H →
      Piu_t r = -((U r 0).comp (Iu 0)).comp (Γ_α r) := by
    intro r hr
    have h1 := hU_Gu hr.1 le_rfl hr.2
    rw [hU_id r hr, ContinuousLinearMap.id_comp] at h1
    rw [← h1]
    exact hGu_eq_U0 hr.1 le_rfl hr.2
  have hGc_eq_U0 : ∀ {r s : ℝ}, 0 ≤ r → r ≤ s → s ≤ H →
      G_c s r = U s r + ((U s 0).comp (Iu 0)).comp (Γ_α r) := by
    intro r s hr hrs hsH
    have hr_mem : r ∈ Icc 0 H := ⟨hr, hrs.trans hsH⟩
    have hcoc := hU_coc 0 r s le_rfl hr hrs hsH
    dsimp [G_c, Pic_t]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      hPiu_eq_U0 hr_mem, ContinuousLinearMap.comp_neg, sub_neg_eq_add]
    congr 1
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hcoc]
  have hGc_norm : ∀ {s r : ℝ}, 0 ≤ s → s ≤ r → r ≤ H →
      ‖G_c r s‖ ≤ (2 * C_proj ^ 5) * Real.exp (a' * (r - s)) := by
    intro s r hs hsr hrH
    have hs_mem : s ∈ Icc 0 H := ⟨hs, hsr.trans hrH⟩
    have hr_mem : r ∈ Icc 0 H := ⟨hs.trans hsr, hrH⟩
    rcases le_or_gt (r - s) L with hrsL | hrsL
    · have hU_rs := hU_short s r hs hsr hrH hrsL
      have hPic_s := hPic_norm hs_mem
      have hexp1 : 1 ≤ Real.exp (a' * (r - s)) := one_le_exp_mul ha' (sub_nonneg.2 hsr)
      calc ‖G_c r s‖ ≤ ‖U r s‖ * ‖Pic_t s‖ := (U r s).opNorm_comp_le _
        _ ≤ C_proj * (2 * C_proj ^ 4) :=
            mul_le_mul hU_rs hPic_s (norm_nonneg _) (by positivity)
        _ = (2 * C_proj ^ 5) * 1 := by ring
        _ ≤ (2 * C_proj ^ 5) * Real.exp (a' * (r - s)) :=
            mul_le_mul_of_nonneg_left hexp1 (by positivity)
    · set j := blkIdx N L s
      set k := blkIdx N L r
      obtain ⟨hj_lt, htj0, htj_s, hs_tj1, htj1_H, _, htj1_sub⟩ := hblk_bounds hs_mem
      obtain ⟨hk_lt, htk0, htk_r, hr_tk1, _, hr_sub, _⟩ := hblk_bounds hr_mem
      have hj_lt_k : j < k := by
        by_contra hnk
        have hkj : k ≤ j := not_lt.1 hnk
        have hr_le_tj1 : r ≤ t (j + 1) := hr_tk1.trans (ht_mono (Nat.add_le_add_right hkj 1))
        have hsub_j := ht_succ_sub j
        linarith
      have hj1_le_k : j + 1 ≤ k := hj_lt_k
      have htj1_le_tk : t (j + 1) ≤ t k := ht_mono hj1_le_k
      have hRight_Pic : (U (t (j + 1)) s).comp (Pic_t s) =
          (Pic (j + 1)).comp (U (t (j + 1)) s) := by
        dsimp [Pic_t]
        rw [(hproj (j + 1) hj_lt).2.2, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_id,
          ContinuousLinearMap.id_comp, hRight_Piu hs_mem]
      have hcoc1 := hU_coc s (t (j + 1)) r hs hs_tj1 (htj1_le_tk.trans htk_r) hrH
      have hcoc2 := hU_coc (t (j + 1)) (t k) r (ht_nonneg _) htj1_le_tk htk_r hrH
      have hGc_fac : G_c r s =
          (U r (t k)).comp (((U (t k) (t (j + 1))).comp (Pic (j + 1))).comp
            (U (t (j + 1)) s)) := by
        dsimp [G_c]
        calc (U r s).comp (Pic_t s)
            = (U r (t k)).comp ((U (t k) (t (j + 1))).comp ((U (t (j + 1)) s).comp (Pic_t s))) := by
              rw [← hcoc1, ← hcoc2]; ext1 x; rfl
          _ = (U r (t k)).comp ((U (t k) (t (j + 1))).comp
                ((Pic (j + 1)).comp (U (t (j + 1)) s))) := by rw [hRight_Pic]
          _ = (U r (t k)).comp (((U (t k) (t (j + 1))).comp (Pic (j + 1))).comp
                (U (t (j + 1)) s)) := by ext1 x; rfl
      have hU_r_tk := hU_short (t k) r htk0 htk_r hrH hr_sub
      have hU_tj1_s := hU_short s (t (j + 1)) hs hs_tj1 htj1_H htj1_sub
      have hmid := hfwd_c (j + 1) k hj1_le_k hk_lt.le
      have hexp_le : Real.exp (a' * (t k - t (j + 1))) ≤ Real.exp (a' * (r - s)) := by
        apply Real.exp_le_exp.2
        have hdiff_le : t k - t (j + 1) ≤ r - s := by linarith
        exact mul_le_mul_of_nonneg_left hdiff_le ha'.le
      have hmid' : ‖(U (t k) (t (j + 1))).comp (Pic (j + 1))‖ ≤
          C_proj * Real.exp (a' * (r - s)) :=
        hmid.trans (mul_le_mul_of_nonneg_left hexp_le (by positivity))
      have hmid_s :
          ‖((U (t k) (t (j + 1))).comp (Pic (j + 1))).comp (U (t (j + 1)) s)‖ ≤
            (C_proj * Real.exp (a' * (r - s))) * C_proj :=
        (((U (t k) (t (j + 1))).comp (Pic (j + 1))).opNorm_comp_le _).trans
          (mul_le_mul hmid' hU_tj1_s (norm_nonneg _) (by positivity))
      have hC35 : C_proj ^ 3 ≤ 2 * C_proj ^ 5 := by
        have hC2 : 1 ≤ C_proj ^ 2 := one_le_pow₀ hC_proj
        nlinarith [pow_nonneg (zero_le_one.trans hC_proj) 3]
      rw [hGc_fac]
      calc ‖(U r (t k)).comp (((U (t k) (t (j + 1))).comp (Pic (j + 1))).comp (U (t (j + 1)) s))‖
          ≤ ‖U r (t k)‖ *
              ‖((U (t k) (t (j + 1))).comp (Pic (j + 1))).comp (U (t (j + 1)) s)‖ :=
            (U r (t k)).opNorm_comp_le _
        _ ≤ C_proj * ((C_proj * Real.exp (a' * (r - s))) * C_proj) :=
            mul_le_mul hU_r_tk hmid_s (norm_nonneg _) (by positivity)
        _ = C_proj ^ 3 * Real.exp (a' * (r - s)) := by ring
        _ ≤ (2 * C_proj ^ 5) * Real.exp (a' * (r - s)) :=
            mul_le_mul_of_nonneg_right hC35 (Real.exp_pos _).le
  have hGu0 : ∀ r : ℝ, G_u 0 r = -(Iu 0).comp (Γ_α r) := by
    intro r
    have h0_idx : blkIdx N L 0 = 0 := blkIdx_zero N L
    have ht0 : t 0 = 0 := by dsimp [t]; ring
    have hU00 : U 0 0 = ContinuousLinearMap.id ℝ X := hU_id 0 ⟨le_rfl, hH_nonneg⟩
    have hJ0 : J 0 = Iu 0 := by
      dsimp [J]
      rw [h0_idx, ht0, hU00, ContinuousLinearMap.id_comp]
    dsimp [G_u, Γ_α]
    rw [hJ0, h0_idx, ContinuousLinearMap.comp_neg, neg_neg]
  have hPuN_GcH : ∀ r ∈ Icc 0 H, (Pu N).comp (G_c H r) = 0 := by
    intro r hr
    have htop : blkIdx N L H = N - 1 := blkIdx_top hN hL_pos
    have hN1_lt : N - 1 < N := Nat.sub_lt hN zero_lt_one
    have hN1_add : N - 1 + 1 = N := Nat.sub_add_cancel hN
    have htN : t N = H := rfl
    have hJH : J H = (Iu N).comp (Bn (N - 1)) := by
      dsimp [J]
      rw [htop]
      have h := (hinter (N - 1) hN1_lt).1
      rwa [hN1_add] at h
    have hFH : F_op H = Pu N := by
      dsimp [F_op]
      rw [htop, hN1_add, htN, hU_id H ⟨hH_nonneg, le_rfl⟩, ContinuousLinearMap.comp_id]
    have hBM_N1 : (Bn (N - 1)).comp (Mn (N - 1)) = ContinuousLinearMap.id ℝ E :=
      (hinv (N - 1) hN1_lt).2.1
    have hPiuH : Piu_t H = (Iu N).comp (Pu N) := by
      dsimp [Piu_t, genIntermProjU]
      rw [hJH, hFH, htop]
      calc ((Iu N).comp (Bn (N - 1))).comp ((Mn (N - 1)).comp (Pu N))
          = (Iu N).comp (((Bn (N - 1)).comp (Mn (N - 1))).comp (Pu N)) := by ext1 x; rfl
        _ = (Iu N).comp (Pu N) := by rw [hBM_N1, ContinuousLinearMap.id_comp]
    have hPuN_PicH : (Pu N).comp (Pic_t H) = 0 := by
      dsimp [Pic_t]
      rw [hPiuH, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
        ← ContinuousLinearMap.comp_assoc, (hproj N le_rfl).1,
        ContinuousLinearMap.id_comp, sub_self]
    have hGcH : G_c H r = (Pic_t H).comp (U H r) := hComm_Pic hr.1 hr.2 le_rfl
    rw [hGcH, ← ContinuousLinearMap.comp_assoc, hPuN_PicH, ContinuousLinearMap.zero_comp]
  have hC4_le : C_proj ^ 4 ≤ C_green := by
    dsimp [C_green]
    nlinarith [pow_nonneg (zero_le_one.trans hC_proj) 4]
  have h2C4_le : 2 * C_proj ^ 4 ≤ C_green := by
    dsimp [C_green]
    nlinarith [pow_nonneg (zero_le_one.trans hC_proj) 4]
  have h2C5_le : 2 * C_proj ^ 5 ≤ C_green := by
    dsimp [C_green]
    nlinarith [pow_nonneg (zero_le_one.trans hC_proj) 5]
  refine ⟨Piu_t, Pic_t, G_c, G_u, Γ_α, ?_, ?_, hGu0, hPuN_GcH, ?_⟩
  · intro r hr
    obtain ⟨hn_lt, _, _, _, _, _, _⟩ := hblk_bounds hr
    refine ⟨genIntermProjU_idem (J r) (Bn (blkIdx N L r)) (Mn (blkIdx N L r)) (F_op r)
      (hFJ hr) (hinv (blkIdx N L r) hn_lt).1, rfl, (hPiu_norm hr).trans hC4_le,
      (hPic_norm hr).trans h2C4_le,
      (hΓ_norm hr).trans (mul_le_mul_of_nonneg_right hC4_le (Real.exp_pos _).le),
      ⟨(Mn (blkIdx N L r)).comp (F_op r), by ext1 x; rfl⟩⟩
  · intro s r hs hsr hrH
    refine ⟨hComm_Piu hs hsr hrH, hComm_Pic hs hsr hrH, rfl, hU_Gu hs hsr hrH,
      (hGc_norm hs hsr hrH).trans (mul_le_mul_of_nonneg_right h2C5_le (Real.exp_pos _).le),
      (hGu_norm hs hsr hrH).trans (mul_le_mul_of_nonneg_right hC4_le (Real.exp_pos _).le),
      fun g => ⟨((Mjk (blkIdx N L s) (blkIdx N L r)).comp (Mn (blkIdx N L r))) (F_op r g), rfl⟩⟩
  · intro f hf ω α
    -- Prove IntegrableOn (fun r => Γ_α r (f r)) (Ioc 0 H) volume
    have hMU_nn : 0 ≤ C_proj ^ (N + 2) := by positivity
    have hU_int : ∀ s ∈ Icc 0 H,
        IntegrableOn (fun r => U s r (f r)) (Ioc 0 s) volume :=
      fun s hs => integrableOn_propagator_apply hs hMU_nn hU_id hU_coc hU_cont hU_global_bd
        (hf.mono_set (Ioc_subset_Ioc_right hs.2))
    have hΓ_blk_int : ∀ k < N,
        IntegrableOn (fun r => Γ_α r (f r)) (Ioc (t k) (t (k + 1))) volume := by
      intro k hk
      have htk1_Icc : t (k + 1) ∈ Icc 0 H := ⟨ht_nonneg _, ht_le_H hk⟩
      have hU_tk1 : IntegrableOn (fun r => U (t (k + 1)) r (f r)) (Ioc (t k) (t (k + 1))) volume :=
        (hU_int (t (k + 1)) htk1_Icc).mono_set (Ioc_subset_Ioc_left (ht_nonneg k))
      let Lk : X →L[ℝ] E := -(((Mjk 0 k).comp (Mn k)).comp (Pu (k + 1)))
      have hLk_int : IntegrableOn (fun r => Lk (U (t (k + 1)) r (f r)))
          (Ioc (t k) (t (k + 1))) volume := Lk.integrable_comp hU_tk1
      have hae_ne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t (k + 1) :=
        compl_mem_ae_iff.2 (measure_singleton (t (k + 1)))
      refine hLk_int.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae hae_ne] with r hr hne
      have hr_Ico : r ∈ Ico (t k) (t (k + 1)) := ⟨hr.1.le, lt_of_le_of_ne hr.2 hne⟩
      have hidx : blkIdx N L r = k := blkIdx_eq_of_mem_Ico hk hL_pos hr_Ico
      dsimp [Γ_α, F_op, Lk]
      rw [hidx]
      rfl
    have hΓ_int_m : ∀ m ≤ N,
        IntegrableOn (fun r => Γ_α r (f r)) (Ioc 0 (t m)) volume := by
      intro m
      induction m with
      | zero =>
        intro _
        have ht0 : t 0 = 0 := by dsimp [t]; ring
        rw [ht0, Ioc_self]
        exact integrableOn_empty
      | succ m ih =>
        intro hm1
        have hm_lt : m < N := hm1
        have hunion : Ioc 0 (t m) ∪ Ioc (t m) (t (m + 1)) = Ioc 0 (t (m + 1)) :=
          Ioc_union_Ioc_eq_Ioc (ht_nonneg m) (ht_mono (Nat.le_succ m))
        rw [← hunion]
        exact (ih hm_lt.le).union (hΓ_blk_int m hm_lt)
    have hΓ_int : IntegrableOn (fun r => Γ_α r (f r)) (Ioc 0 H) volume :=
      hΓ_int_m N le_rfl
    have hω0_eq : ω 0 = Iu 0 α := by
      dsimp [ω, α]
      rw [Ioc_self, Measure.restrict_empty, integral_zero_measure, zero_sub]
      have hfun : (fun r => G_u 0 r (f r)) = (fun r => -(Iu 0 (Γ_α r (f r)))) := by
        funext r
        rw [hGu0 r]
        rfl
      rw [hfun, integral_neg, neg_neg]
      exact (Iu 0).integral_comp_comm hΓ_int
    refine ⟨hω0_eq, ?_, ?_, ?_⟩
    · -- Pu N (ω H) = 0
      dsimp [ω]
      rw [Ioc_self, Measure.restrict_empty, integral_zero_measure, sub_zero]
      by_cases hInt : IntegrableOn (fun r => G_c H r (f r)) (Ioc 0 H) volume
      · rw [← (Pu N).integral_comp_comm hInt]
        have hzero : EqOn (fun r => Pu N (G_c H r (f r))) (fun _ => 0) (Ioc 0 H) := by
          intro r hr
          change ((Pu N).comp (G_c H r)) (f r) = 0
          rw [hPuN_GcH r ⟨hr.1.le, hr.2⟩]
          rfl
        rw [setIntegral_congr_fun measurableSet_Ioc hzero, integral_zero]
      · rw [integral_undef hInt, map_zero]
    · -- ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖
      intro s hs
      set M₀ : ℝ := 2 * C_proj ^ 5
      have hM₀_pos : 0 < M₀ := by dsimp [M₀]; positivity
      have hf_norm : IntegrableOn (fun t => ‖f t‖) (Ioc 0 H) volume := hf.norm
      have hint_nonneg : 0 ≤ ∫ t in Ioc 0 H, ‖f t‖ :=
        integral_nonneg (fun _ => norm_nonneg _)
      have hI₁ : ‖∫ t in Ioc 0 s, G_c s t (f t)‖ ≤
          M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 s, ‖f t‖ := by
        have h1 : ‖∫ t in Ioc 0 s, G_c s t (f t)‖ ≤ ∫ t in Ioc 0 s, ‖G_c s t (f t)‖ :=
          norm_integral_le_integral_norm _
        have h2 : ∫ t in Ioc 0 s, ‖G_c s t (f t)‖ ≤
            M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 s, ‖f t‖ := by
          by_cases hInt : IntegrableOn (fun t => ‖G_c s t (f t)‖) (Ioc 0 s) volume
          · have hf_s : IntegrableOn (fun t => ‖f t‖) (Ioc 0 s) volume :=
              hf_norm.mono_set (Ioc_subset_Ioc_right hs.2)
            have hpw : ∀ᵐ t ∂volume.restrict (Ioc 0 s),
                ‖G_c s t (f t)‖ ≤ M₀ * Real.exp (a' * H) * ‖f t‖ := by
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
              have hGc_bd := hGc_norm ht.1.le ht.2 hs.2
              have hexp_le : Real.exp (a' * (s - t)) ≤ Real.exp (a' * H) := by
                apply Real.exp_le_exp.2
                have hst_H : s - t ≤ H := by linarith [ht.1, hs.2]
                exact mul_le_mul_of_nonneg_left hst_H ha'.le
              calc ‖G_c s t (f t)‖ ≤ ‖G_c s t‖ * ‖f t‖ := (G_c s t).le_opNorm (f t)
                _ ≤ (M₀ * Real.exp (a' * (s - t))) * ‖f t‖ :=
                    mul_le_mul_of_nonneg_right hGc_bd (norm_nonneg _)
                _ ≤ (M₀ * Real.exp (a' * H)) * ‖f t‖ :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hexp_le hM₀_pos.le) (norm_nonneg _)
            calc ∫ t in Ioc 0 s, ‖G_c s t (f t)‖
                ≤ ∫ t in Ioc 0 s, M₀ * Real.exp (a' * H) * ‖f t‖ :=
                  integral_mono_ae hInt (hf_s.const_mul _) hpw
              _ = M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 s, ‖f t‖ := integral_const_mul _ _
          · rw [integral_undef hInt]
            exact mul_nonneg (mul_nonneg hM₀_pos.le (Real.exp_pos _).le)
              (integral_nonneg (fun _ => norm_nonneg _))
        exact h1.trans h2
      have hI₂ : ‖∫ t in Ioc s H, G_u s t (f t)‖ ≤
          M₀ * Real.exp (a' * H) * ∫ t in Ioc s H, ‖f t‖ := by
        have h1 : ‖∫ t in Ioc s H, G_u s t (f t)‖ ≤ ∫ t in Ioc s H, ‖G_u s t (f t)‖ :=
          norm_integral_le_integral_norm _
        have h2 : ∫ t in Ioc s H, ‖G_u s t (f t)‖ ≤
            M₀ * Real.exp (a' * H) * ∫ t in Ioc s H, ‖f t‖ := by
          by_cases hInt : IntegrableOn (fun t => ‖G_u s t (f t)‖) (Ioc s H) volume
          · have hf_sH : IntegrableOn (fun t => ‖f t‖) (Ioc s H) volume :=
              hf_norm.mono_set (Ioc_subset_Ioc_left hs.1)
            have hpw : ∀ᵐ t ∂volume.restrict (Ioc s H),
                ‖G_u s t (f t)‖ ≤ M₀ * Real.exp (a' * H) * ‖f t‖ := by
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
              have hGu_bd := hGu_norm hs.1 ht.1.le ht.2
              have hexp1 : Real.exp (-b' * (t - s)) ≤ 1 :=
                exp_neg_mul_le_one hb' (sub_nonneg.2 ht.1.le)
              have hexpH : 1 ≤ Real.exp (a' * H) := one_le_exp_mul ha' hH_nonneg
              have hC4_M0 : C_proj ^ 4 ≤ M₀ := by
                dsimp [M₀]; nlinarith [pow_nonneg (zero_le_one.trans hC_proj) 4]
              have hGu_M0 : ‖G_u s t‖ ≤ M₀ * Real.exp (a' * H) := by
                calc ‖G_u s t‖ ≤ C_proj ^ 4 * Real.exp (-b' * (t - s)) := hGu_bd
                  _ ≤ M₀ * 1 := mul_le_mul hC4_M0 hexp1 (Real.exp_pos _).le hM₀_pos.le
                  _ ≤ M₀ * Real.exp (a' * H) := mul_le_mul_of_nonneg_left hexpH hM₀_pos.le
              exact ((G_u s t).le_opNorm (f t)).trans
                (mul_le_mul_of_nonneg_right hGu_M0 (norm_nonneg _))
            calc ∫ t in Ioc s H, ‖G_u s t (f t)‖
                ≤ ∫ t in Ioc s H, M₀ * Real.exp (a' * H) * ‖f t‖ :=
                  integral_mono_ae hInt (hf_sH.const_mul _) hpw
              _ = M₀ * Real.exp (a' * H) * ∫ t in Ioc s H, ‖f t‖ := integral_const_mul _ _
          · rw [integral_undef hInt]
            exact mul_nonneg (mul_nonneg hM₀_pos.le (Real.exp_pos _).le)
              (integral_nonneg (fun _ => norm_nonneg _))
        exact h1.trans h2
      have hα_bd : ‖α‖ ≤ M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖ := by
        have h1 : ‖α‖ ≤ ∫ t in Ioc 0 H, ‖Γ_α t (f t)‖ := norm_integral_le_integral_norm _
        have h2 : ∫ t in Ioc 0 H, ‖Γ_α t (f t)‖ ≤
            M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖ := by
          by_cases hInt : IntegrableOn (fun t => ‖Γ_α t (f t)‖) (Ioc 0 H) volume
          · have hpw : ∀ᵐ t ∂volume.restrict (Ioc 0 H),
                ‖Γ_α t (f t)‖ ≤ M₀ * Real.exp (a' * H) * ‖f t‖ := by
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
              have hΓ_bd := hΓ_norm ⟨ht.1.le, ht.2⟩
              have hexp1 : Real.exp (-b' * t) ≤ 1 := exp_neg_mul_le_one hb' ht.1.le
              have hexpH : 1 ≤ Real.exp (a' * H) := one_le_exp_mul ha' hH_nonneg
              have hC4_M0 : C_proj ^ 4 ≤ M₀ := by
                dsimp [M₀]; nlinarith [pow_nonneg (zero_le_one.trans hC_proj) 4]
              have hΓ_M0 : ‖Γ_α t‖ ≤ M₀ * Real.exp (a' * H) := by
                calc ‖Γ_α t‖ ≤ C_proj ^ 4 * Real.exp (-b' * t) := hΓ_bd
                  _ ≤ M₀ * 1 := mul_le_mul hC4_M0 hexp1 (Real.exp_pos _).le hM₀_pos.le
                  _ ≤ M₀ * Real.exp (a' * H) := mul_le_mul_of_nonneg_left hexpH hM₀_pos.le
              exact ((Γ_α t).le_opNorm (f t)).trans
                (mul_le_mul_of_nonneg_right hΓ_M0 (norm_nonneg _))
            calc ∫ t in Ioc 0 H, ‖Γ_α t (f t)‖
                ≤ ∫ t in Ioc 0 H, M₀ * Real.exp (a' * H) * ‖f t‖ :=
                  integral_mono_ae hInt (hf_norm.const_mul _) hpw
              _ = M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖ := integral_const_mul _ _
          · rw [integral_undef hInt]
            exact mul_nonneg (mul_nonneg hM₀_pos.le (Real.exp_pos _).le) hint_nonneg
        exact h1.trans h2
      have hsplit : (∫ t in Ioc 0 s, ‖f t‖) + (∫ t in Ioc s H, ‖f t‖) =
          ∫ t in Ioc 0 H, ‖f t‖ := by
        have hunion : Ioc 0 s ∪ Ioc s H = Ioc 0 H := Ioc_union_Ioc_eq_Ioc hs.1 hs.2
        have hdisj : Disjoint (Ioc 0 s) (Ioc s H) :=
          disjoint_iff_inf_le.mpr (fun x hx => not_lt_of_ge hx.1.2 hx.2.1)
        rw [← setIntegral_union hdisj measurableSet_Ioc
          (hf_norm.mono_set (Ioc_subset_Ioc_right hs.2))
          (hf_norm.mono_set (Ioc_subset_Ioc_left hs.1)), hunion]
      have hω_bd : ‖ω s‖ ≤ M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖ := by
        calc ‖ω s‖
            ≤ ‖∫ t in Ioc 0 s, G_c s t (f t)‖ + ‖∫ t in Ioc s H, G_u s t (f t)‖ :=
              norm_sub_le _ _
          _ ≤ M₀ * Real.exp (a' * H) * (∫ t in Ioc 0 s, ‖f t‖) +
                M₀ * Real.exp (a' * H) * (∫ t in Ioc s H, ‖f t‖) := add_le_add hI₁ hI₂
          _ = M₀ * Real.exp (a' * H) * ((∫ t in Ioc 0 s, ‖f t‖) + (∫ t in Ioc s H, ‖f t‖)) := by
              ring
          _ = M₀ * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖ := by rw [hsplit]
      calc ‖ω s‖ + ‖α‖
          ≤ M₀ * Real.exp (a' * H) * (∫ t in Ioc 0 H, ‖f t‖) +
              M₀ * Real.exp (a' * H) * (∫ t in Ioc 0 H, ‖f t‖) := add_le_add hω_bd hα_bd
        _ = C_green * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖ := by
            dsimp [C_green, M₀]; ring
    · -- ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)
      intro s hs
      let Ls : E →L[ℝ] X := (U s 0).comp (Iu 0)
      have hΓ_0s : IntegrableOn (fun r => Γ_α r (f r)) (Ioc 0 s) volume :=
        hΓ_int.mono_set (Ioc_subset_Ioc_right hs.2)
      have hΓ_sH : IntegrableOn (fun r => Γ_α r (f r)) (Ioc s H) volume :=
        hΓ_int.mono_set (Ioc_subset_Ioc_left hs.1)
      have hLs_0s : IntegrableOn (fun r => Ls (Γ_α r (f r))) (Ioc 0 s) volume :=
        Ls.integrable_comp hΓ_0s
      have hGc_congr : EqOn (fun r => G_c s r (f r))
          (fun r => U s r (f r) + Ls (Γ_α r (f r))) (Ioc 0 s) := by
        intro r hr
        dsimp only
        rw [hGc_eq_U0 hr.1.le hr.2 hs.2]
        rfl
      have hGu_congr : EqOn (fun r => G_u s r (f r))
          (fun r => -Ls (Γ_α r (f r))) (Ioc s H) := by
        intro r hr
        dsimp only
        rw [hGu_eq_U0 hs.1 hr.1.le hr.2]
        rfl
      have hI1_eq : (∫ r in Ioc 0 s, G_c s r (f r)) =
          (∫ r in Ioc 0 s, U s r (f r)) + Ls (∫ r in Ioc 0 s, Γ_α r (f r)) := by
        rw [setIntegral_congr_fun measurableSet_Ioc hGc_congr,
          integral_add (hU_int s hs) hLs_0s, Ls.integral_comp_comm hΓ_0s]
      have hI2_eq : (∫ r in Ioc s H, G_u s r (f r)) =
          -Ls (∫ r in Ioc s H, Γ_α r (f r)) := by
        rw [setIntegral_congr_fun measurableSet_Ioc hGu_congr,
          integral_neg, Ls.integral_comp_comm hΓ_sH]
      have hsplit_α : (∫ r in Ioc 0 s, Γ_α r (f r)) + (∫ r in Ioc s H, Γ_α r (f r)) = α := by
        have hunion : Ioc 0 s ∪ Ioc s H = Ioc 0 H := Ioc_union_Ioc_eq_Ioc hs.1 hs.2
        have hdisj : Disjoint (Ioc 0 s) (Ioc s H) :=
          disjoint_iff_inf_le.mpr (fun x hx => not_lt_of_ge hx.1.2 hx.2.1)
        rw [← setIntegral_union hdisj measurableSet_Ioc hΓ_0s hΓ_sH, hunion]
      change (∫ r in Ioc 0 s, G_c s r (f r)) - (∫ r in Ioc s H, G_u s r (f r)) =
        U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)
      rw [hI1_eq, hI2_eq, sub_neg_eq_add, add_assoc, ← map_add, hsplit_α, hω0_eq]
      dsimp [Ls]
      exact add_comm _ _

end GenericGreen

end PartIIbF4Aux

/-! ## 5. Leaf propositions (`PartII-b:F4/1` and `PartII-b:F4/2`) and assembly -/

/-- **Leaf 1 (`PartII-b:F4/1`, continuous linear test pairing of `cylCoupledIntegrand`,
SP 2079–2083, 2195–2201)**: for every `m > 8`, cylinder period `c ≥ 1`, viscosity `ν > 0`,
background train `tr : B0140.TrainSol ν c`, cylinder test function `φ : B0579.Plane → ℝ`
(`B0579.IsCylTest c φ`), and terminal age `H ≥ 0`, there exist a uniform bound `C_φ ≥ 0` and a
family of continuous linear functionals `L_φ : ℝ → (Xmc c m →L[ℝ] ℝ)` such that for all
`r ∈ Icc 0 H` and `w : Xmc c m`, `cylCoupledIntegrand tr w r φ` is integrable on `B0579.cell c`,
`L_φ r w = ∫ x in B0579.cell c, cylCoupledIntegrand tr w r φ x`, and `‖L_φ r‖ ≤ C_φ`. -/
def CylCoupledPairingCLM : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (ν c H : ℝ) (tr : B0140.TrainSol ν c) (φ : B0579.Plane → ℝ),
    0 < ν → 1 ≤ c → 0 ≤ H → B0579.IsCylTest c φ →
    ∃ (C_φ : ℝ) (L_φ : ℝ → (Xmc c m →L[ℝ] ℝ)),
      0 ≤ C_φ ∧
      ∀ r ∈ Icc 0 H,
        ‖L_φ r‖ ≤ C_φ ∧
        ∀ w : Xmc c m,
          IntegrableOn (cylCoupledIntegrand tr w r φ) (B0579.cell c) volume ∧
          L_φ r w = ∫ x in B0579.cell c, cylCoupledIntegrand tr w r φ x

/-- **Leaf 2 (`PartII-b:F4/2`, triangle Fubini swap for the coupled propagator Duhamel integral,
SP 2195–2201)**: for every `m > 8`, parameter point `p : Params` with `1 ≤ p.c` and `0 ≤ p.H`,
coupled propagator `U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)` (`IsCoupledPropagator m p U`) bounded
by `M_U ≥ 0` on `0 ≤ t ≤ r ≤ p.H`, cylinder test function `φ : B0579.Plane → ℝ`
(`B0579.IsCylTest p.c φ`), continuous linear functionals `L_φ : ℝ → (Xmc p.c m →L[ℝ] ℝ)` realizing
`w ↦ ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train w r φ x` with `‖L_φ r‖ ≤ C_φ` (`0 ≤ C_φ`)
on `Icc 0 p.H`, and Bochner-integrable source `f : ℝ → Xmc p.c m` on `Ioc 0 p.H`, for every
`s ∈ Icc 0 p.H`, `r ↦ ∫ t in Ioc 0 r, L_φ r (U r t (f t))` is interval-integrable on `0..s` and
`∫ t in Ioc 0 s, ∫ r in Ioc t s, L_φ r (U r t (f t)) = ∫ r in Ioc 0 s, ∫ t in Ioc 0 r, L_φ r (U r t (f t))`. -/
def PropagatorTriangleFubini : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (p : Params) (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)) (M_U : ℝ),
    1 ≤ p.c → 0 ≤ p.H → 0 ≤ M_U → IsCoupledPropagator m p U →
    (∀ t r : ℝ, 0 ≤ t → t ≤ r → r ≤ p.H → ‖U r t‖ ≤ M_U) →
    ∀ (φ : B0579.Plane → ℝ) (C_φ : ℝ) (L_φ : ℝ → (Xmc p.c m →L[ℝ] ℝ)),
      B0579.IsCylTest p.c φ → 0 ≤ C_φ →
      (∀ r ∈ Icc 0 p.H,
        ‖L_φ r‖ ≤ C_φ ∧
        ∀ w : Xmc p.c m,
          IntegrableOn (cylCoupledIntegrand p.train w r φ) (B0579.cell p.c) volume ∧
          L_φ r w = ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train w r φ x) →
      ∀ f : ℝ → Xmc p.c m, IntegrableOn f (Ioc 0 p.H) volume →
      ∀ s ∈ Icc 0 p.H,
        IntervalIntegrable (fun r => ∫ t in Ioc 0 r, L_φ r (U r t (f t))) volume 0 s ∧
        (∫ t in Ioc 0 s, ∫ r in Ioc t s, L_φ r (U r t (f t))) =
          ∫ r in Ioc 0 s, ∫ t in Ioc 0 r, L_φ r (U r t (f t))

open PartIIbF4Aux

/-- **Full assembly of `MixedGreenSelector` (`PartII-b:F4`)** from `CylCoupledPairingCLM`
(`PartII-b:F4/1`), `PropagatorTriangleFubini` (`PartII-b:F4/2`), and `DichotomyProjections`
(`PartII-b:F3`). -/
theorem mixedGreenSelector_of_leaves
    (hPair : CylCoupledPairingCLM)
    (hFub : PropagatorTriangleFubini)
    (hDP : DichotomyProjections) :
    MixedGreenSelector := by
  intro m hm Sig lam q hSig hEig a' b' ha' hab' hb' dm dp hdm
  have hm_half : 1 / 2 < m := by linarith
  obtain ⟨L₀, C_proj, ν₁, hL₀, hC_proj, hν₁, hDP_p⟩ :=
    hDP m hm Sig lam q hSig hEig a' b' ha' hab' hb' dm dp hdm
  set C_green : ℝ := 4 * C_proj ^ 5
  have hC_green_pos : 0 < C_green := by dsimp [C_green]; positivity
  set ν₀ : ℝ := min ν₁ 1
  have hν₀_pos : 0 < ν₀ := lt_min hν₁ zero_lt_one
  refine ⟨C_green, ν₀, hC_green_pos, hν₀_pos, ?_⟩
  intro p d hbg hν hAge hMode
  have hν_le_ν₁ : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν_le_1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hc1 : 1 ≤ p.c := bgRegime_c_ge_one hbg hν_le_1
  obtain ⟨U, D, hU, hD⟩ := hDP_p p d hbg hν_le_ν₁ hAge hMode
  have hL_pos : 0 < D.L := lt_of_lt_of_le zero_lt_one (hL₀.trans hD.L_bounds.1)
  have hH_nonneg : 0 ≤ p.H := by
    rw [← hD.total_age]
    positivity
  have hU_id : ∀ s ∈ Icc 0 ((D.N : ℝ) * D.L), U s s = ContinuousLinearMap.id ℝ (Xmc p.c m) := by
    rw [hD.total_age]; exact hU.id_self
  have hU_coc : ∀ s r u : ℝ, 0 ≤ s → s ≤ r → r ≤ u → u ≤ (D.N : ℝ) * D.L →
      (U u r).comp (U r s) = U u s := by
    rw [hD.total_age]; exact hU.comp_cocycle
  have hU_cont : ∀ s ∈ Icc 0 ((D.N : ℝ) * D.L), ∀ g : Xmc p.c m,
      ContinuousOn (fun r => U r s g) (Icc s ((D.N : ℝ) * D.L)) := by
    rw [hD.total_age]; exact hU.strongCont
  have hU_short : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (D.N : ℝ) * D.L → r - s ≤ D.L →
      ‖U r s‖ ≤ C_proj := by
    rw [hD.total_age]; exact hD.short_prop_norm
  obtain ⟨hU_global_bd, Piu_t, Pic_t, G_c, G_u, Γ_α, hPt, hKer, hGu0, hPuN_Gc, hInt_props⟩ :=
    @gen_green_operators_full (Xmc p.c m) E2 _ _ _ _ _ _
      D.N D.L L₀ a' b' C_proj hD.N_pos hL₀ hD.L_bounds ha' hab' hC_proj
      U D.Iu D.Pu D.Piu D.Pic D.Bn D.Mn
      hU_id hU_coc hU_cont hU_short hD.proj_rel hD.norm_bounds hD.block_inv
      hD.block_intertwine hD.forward_center_bound hD.backward_unstable_bound
  rw [hD.total_age] at hU_global_bd hPt hKer hPuN_Gc hInt_props
  refine ⟨U, D.Pu D.N, Piu_t, Pic_t, G_c, G_u, Γ_α, hU, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := hPt t ht
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro s t hs hst htH
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hKer s t hs hst htH
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · intro f hf hf_circ ω α
    obtain ⟨hω0_eq, hPuN_ωH, hω_norm, hω_duh⟩ := hInt_props f hf
    have hω0_eq' : ω 0 = D.Iu 0 α := hω0_eq
    have hω0_ae : (ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α := by
      rw [hω0_eq']
      exact hD.entrance_eq α
    -- 1. Zero circulation of ω s for all s ∈ Icc 0 p.H
    have hPiu_circ : ∀ t ∈ Icc 0 p.H, ∀ g : Xmc p.c m, HasZeroCirculationR p.c (Piu_t t g) := by
      intro t ht g
      obtain ⟨_, _, _, _, _, α_t, hPiu_eq⟩ := hPt t ht
      rw [hPiu_eq]
      have hj_lt : blkIdx D.N D.L t < D.N := blkIdx_lt hD.N_pos D.L t
      have htj_0 : 0 ≤ (blkIdx D.N D.L t : ℝ) * D.L := by positivity
      have htj_t : (blkIdx D.N D.L t : ℝ) * D.L ≤ t := blkIdx_left_le hL_pos ht.1
      exact hU.zeroCirc ((blkIdx D.N D.L t : ℝ) * D.L) t htj_0 htj_t ht.2
        (D.Iu (blkIdx D.N D.L t) (α_t g)) (hD.zeroCirc_Iu _ hj_lt.le (α_t g))
    have hGu_circ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
        ∀ g : Xmc p.c m, HasZeroCirculationR p.c (G_u s t g) := by
      intro s t hs hst htH g
      obtain ⟨_, _, _, _, _, _, h7⟩ := hKer s t hs hst htH
      obtain ⟨α_g, hGu_eq⟩ := h7 g
      rw [hGu_eq]
      have hj_lt : blkIdx D.N D.L s < D.N := blkIdx_lt hD.N_pos D.L s
      have htj_0 : 0 ≤ (blkIdx D.N D.L s : ℝ) * D.L := by positivity
      have htj_s : (blkIdx D.N D.L s : ℝ) * D.L ≤ s := blkIdx_left_le hL_pos hs
      exact hU.zeroCirc ((blkIdx D.N D.L s : ℝ) * D.L) s htj_0 htj_s (hst.trans htH)
        (D.Iu (blkIdx D.N D.L s) α_g) (hD.zeroCirc_Iu _ hj_lt.le α_g)
    have hω_circ : ∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s) := by
      intro s hs
      dsimp [ω]
      refine hasZeroCirculationR_sub hm_half
        (hasZeroCirculationR_of_bochner hm_half (Ioc 0 s) measurableSet_Ioc
          (fun t => G_c s t (f t)) ?_)
        (hasZeroCirculationR_of_bochner hm_half (Ioc s p.H) measurableSet_Ioc
          (fun t => G_u s t (f t)) ?_)
      · filter_upwards [hf_circ] with t ht ht_mem
        have ht_H : t ∈ Ioc 0 p.H := ⟨ht_mem.1, ht_mem.2.trans hs.2⟩
        have hft_circ : HasZeroCirculationR p.c (f t) := ht ht_H
        have hPic_eq : Pic_t t (f t) = f t - Piu_t t (f t) := by
          rw [(hPt t ⟨ht_mem.1.le, ht_H.2⟩).2.1]
          rfl
        have hPic_circ : HasZeroCirculationR p.c (Pic_t t (f t)) := by
          rw [hPic_eq]
          exact hasZeroCirculationR_sub hm_half hft_circ
            (hPiu_circ t ⟨ht_mem.1.le, ht_H.2⟩ (f t))
        rw [(hKer t s ht_mem.1.le ht_mem.2 hs.2).2.2.1]
        exact hU.zeroCirc t s ht_mem.1.le ht_mem.2 hs.2 (Pic_t t (f t)) hPic_circ
      · filter_upwards with t ht_mem
        exact hGu_circ s t hs.1 ht_mem.1.le ht_mem.2 (f t)
    -- 2. Weak forced coupled cylinder vorticity equation for ω
    refine ⟨hω0_ae, hPuN_ωH, hω_circ, ?_, hω_norm⟩
    intro φ hφ s hs
    set M_U : ℝ := C_proj ^ (D.N + 2)
    have hMU_nn : 0 ≤ M_U := by dsimp [M_U]; positivity
    obtain ⟨C_φ, L_φ, hC_φ, hL_φ⟩ := hPair m hm p.ν p.c p.H p.train φ p.ν_pos hc1 hH_nonneg hφ
    obtain ⟨hFub_int, hFub_eq⟩ :=
      hFub m hm p U M_U hc1 hH_nonneg hMU_nn hU hU_global_bd φ C_φ L_φ hφ hC_φ hL_φ f hf s hs
    let ω_hom : ℝ → Xmc p.c m := fun r => U r 0 (ω 0)
    let ω_inhom : ℝ → Xmc p.c m := fun r => ∫ t in Ioc 0 r, U r t (f t)
    have hU_int : ∀ r ∈ Icc 0 p.H,
        IntegrableOn (fun t => U r t (f t)) (Ioc 0 r) volume :=
      fun r hr => integrableOn_propagator_apply hr hMU_nn
        hU.id_self hU.comp_cocycle hU.strongCont hU_global_bd
        (hf.mono_set (Ioc_subset_Ioc_right hr.2))
    have hω_split : ∀ r ∈ Icc 0 p.H, ω r = ω_hom r + ω_inhom r := hω_duh
    -- Homogeneous weak equation at r = s
    have hweak_hom : cellTestCLM p.c m hφ (ω_hom s) =
        cellTestCLM p.c m hφ (ω 0) + ∫ r in (0 : ℝ)..s, L_φ r (ω_hom r) := by
      simp only [cellTestCLM_apply]
      rw [hU.weak φ hφ 0 s le_rfl hs.1 hs.2 (ω 0)]
      congr 1
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
      rw [uIoc_of_le hs.1] at hr
      exact ((hL_φ r ⟨hr.1.le, hr.2.trans hs.2⟩).2 (ω_hom r)).2.symm
    have hint_hom : IntervalIntegrable (fun r => L_φ r (ω_hom r)) volume 0 s := by
      have h1 := hU.timeIntegrable φ hφ 0 s le_rfl hs.1 hs.2 (ω 0)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1] at h1 ⊢
      refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioc
      exact ((hL_φ r ⟨hr.1.le, hr.2.trans hs.2⟩).2 (ω_hom r)).2.symm
    -- Inhomogeneous weak equation at r = s
    have hf_s : IntegrableOn f (Ioc 0 s) volume := hf.mono_set (Ioc_subset_Ioc_right hs.2)
    have htest_f_int : IntegrableOn (fun t => cellTestCLM p.c m hφ (f t)) (Ioc 0 s) volume :=
      (cellTestCLM p.c m hφ).integrable_comp hf_s
    have htest_U_int : IntegrableOn (fun t => cellTestCLM p.c m hφ (U s t (f t))) (Ioc 0 s) volume :=
      (cellTestCLM p.c m hφ).integrable_comp (hU_int s hs)
    have hpt_weak_t : ∀ t ∈ Ioc 0 s,
        cellTestCLM p.c m hφ (U s t (f t)) =
          cellTestCLM p.c m hφ (f t) + ∫ r in Ioc t s, L_φ r (U r t (f t)) := by
      intro t ht
      simp only [cellTestCLM_apply]
      rw [hU.weak φ hφ t s ht.1.le ht.2 hs.2 (f t), intervalIntegral.integral_of_le ht.2]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
      exact ((hL_φ r ⟨(ht.1.trans hr.1).le, hr.2.trans hs.2⟩).2 (U r t (f t))).2.symm
    have hinner_int : IntegrableOn (fun t => ∫ r in Ioc t s, L_φ r (U r t (f t))) (Ioc 0 s) volume := by
      refine (htest_U_int.sub htest_f_int).congr_fun (fun t ht => ?_) measurableSet_Ioc
      simp only [Pi.sub_apply, hpt_weak_t t ht, add_sub_cancel_left]
    have hweak_inhom_1 : cellTestCLM p.c m hφ (ω_inhom s) =
        (∫ r in (0 : ℝ)..s, cellTestCLM p.c m hφ (f r)) +
          ∫ r in (0 : ℝ)..s, L_φ r (ω_inhom r) := by
      dsimp [ω_inhom]
      rw [← (cellTestCLM p.c m hφ).integral_comp_comm (hU_int s hs),
        setIntegral_congr_fun measurableSet_Ioc hpt_weak_t,
        integral_add htest_f_int hinner_int,
        hFub_eq, ← intervalIntegral.integral_of_le hs.1,
        ← intervalIntegral.integral_of_le hs.1]
      congr 1
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
      rw [uIoc_of_le hs.1] at hr
      have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2.trans hs.2⟩
      exact (L_φ r).integral_comp_comm (hU_int r hr_Icc)
    have hint_inhom : IntervalIntegrable (fun r => L_φ r (ω_inhom r)) volume 0 s := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1] at hFub_int ⊢
      refine hFub_int.congr_fun (fun r hr => ?_) measurableSet_Ioc
      have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2.trans hs.2⟩
      exact (L_φ r).integral_comp_comm (hU_int r hr_Icc)
    have hint_f : IntervalIntegrable (fun r => cellTestCLM p.c m hφ (f r)) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2 htest_f_int
    -- Combine homogeneous and inhomogeneous parts
    rw [← cellTestCLM_apply p.c m hφ (ω s), ← cellTestCLM_apply p.c m hφ (ω 0),
      hω_split s hs, map_add, hweak_hom, hweak_inhom_1]
    have hcomb :
        (cellTestCLM p.c m hφ (ω 0) + ∫ r in (0 : ℝ)..s, L_φ r (ω_hom r)) +
          ((∫ r in (0 : ℝ)..s, cellTestCLM p.c m hφ (f r)) +
            ∫ r in (0 : ℝ)..s, L_φ r (ω_inhom r)) =
        cellTestCLM p.c m hφ (ω 0) +
          ((∫ r in (0 : ℝ)..s, L_φ r (ω_hom r)) +
            (∫ r in (0 : ℝ)..s, L_φ r (ω_inhom r)) +
            (∫ r in (0 : ℝ)..s, cellTestCLM p.c m hφ (f r))) := by ring
    rw [hcomb, ← intervalIntegral.integral_add hint_hom hint_inhom,
      ← intervalIntegral.integral_add (hint_hom.add hint_inhom) hint_f]
    congr 1
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hs.1] at hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2.trans hs.2⟩
    have hLr_add : L_φ r (ω_hom r) + L_φ r (ω_inhom r) = L_φ r (ω r) := by
      rw [← map_add, ← hω_split r hr_Icc]
    rw [hLr_add, ((hL_φ r hr_Icc).2 (ω r)).2, cellTestCLM_apply,
      ← integral_add ((hL_φ r hr_Icc).2 (ω r)).1 (integrableOn_mul_cylTest p.c m hφ (f r))]

end UnforcedLeray.Short.IIb

end
