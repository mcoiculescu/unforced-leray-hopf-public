import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.HorizonGluing.TestLift
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Lib.BochnerTime.Energy

/-!
# `HorizonGluing.EarlyTrace`: `C((0, T]; H¹_σ(C_c))` representative and horizon trace at `s = T`

Internal helper module for `MeridionalHorizonGluing` (`PartII-b:F7/2/2`).
Combines:
1. `hasWeakDerivTime_opJ_Z0` (`TestLift.lean`),
2. the smooth cylinder IBP dissipation / drift estimates `inner_viscous_L2_nonpos` and
   `inner_viscous_drift_H1_le` (`MollOp.lean`),
3. `BochnerTime.HasWeakDerivTime.norm_sq_sub` (`Lib/BochnerTime/Energy.lean`), and
4. `Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Ioc`
to construct a jointly strongly measurable, everywhere `c`-periodic representative
`(z₁, zq₁, zη₁)` of `(z_eb, zq_eb, zη_eb)` on `(0, T]` that is continuous in `cylSliceH1` on
`Ioc 0 T` and has a genuine `IsCylH1Slice` horizon trace at `s = T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.IIb.HorizonGluingAux

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIIa

/-! ### 1. `L¹(Ioo 0 T)` convergence of double-mollified Bochner paths -/

lemma integrableOn_norm_opJ_sq_sub {c T : ℝ} (hc : 0 < c)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J) (k : ℕ)
    {U : ℝ → LMH c} (hU : IntegrableOn U (Ioo 0 T) volume) :
    IntegrableOn (fun r => ‖opJ c hc J hJ k (opJ c hc J hJ k (U r)) - U r‖) (Ioo 0 T) volume :=
  (((opJ c hc J hJ k).integrable_comp ((opJ c hc J hJ k).integrable_comp hU)).sub hU).norm

lemma tendsto_integral_norm_opJ_sq_sub {c T : ℝ} (hc : 0 < c)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    {U : ℝ → LMH c} (hU : IntegrableOn U (Ioo 0 T) volume) :
    Tendsto (fun k => ∫ r in Ioo 0 T, ‖opJ c hc J hJ k (opJ c hc J hJ k (U r)) - U r‖)
      atTop (𝓝 0) := by
  have hbound : IntegrableOn (fun r => 2 * ‖U r‖) (Ioo 0 T) volume := hU.norm.const_mul 2
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun r => ‖opJ c hc J hJ k (opJ c hc J hJ k (U r)) - U r‖)
      (volume.restrict (Ioo 0 T)) :=
    fun k => (integrableOn_norm_opJ_sq_sub hc hJ k hU).aestronglyMeasurable
  have hle : ∀ k : ℕ, ∀ᵐ r ∂(volume.restrict (Ioo 0 T)),
      ‖‖opJ c hc J hJ k (opJ c hc J hJ k (U r)) - U r‖‖ ≤ 2 * ‖U r‖ := fun k => by
    refine ae_of_all _ fun r => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have h1 : ‖opJ c hc J hJ k (opJ c hc J hJ k (U r))‖ ≤ ‖opJ c hc J hJ k (U r)‖ :=
      norm_opJ_le hc hJ k _
    have h2 : ‖opJ c hc J hJ k (U r)‖ ≤ ‖U r‖ := norm_opJ_le hc hJ k _
    have h3 : ‖opJ c hc J hJ k (opJ c hc J hJ k (U r)) - U r‖ ≤
        ‖opJ c hc J hJ k (opJ c hc J hJ k (U r))‖ + ‖U r‖ := norm_sub_le _ _
    linarith
  have hpt : ∀ᵐ r ∂(volume.restrict (Ioo 0 T)),
      Tendsto (fun k => ‖opJ c hc J hJ k (opJ c hc J hJ k (U r)) - U r‖) atTop (𝓝 0) :=
    ae_of_all _ fun r => tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_opJ_sq hc hJ (U r))
  have hlim := tendsto_integral_of_dominated_convergence (fun r => 2 * ‖U r‖) hmeas hbound hle hpt
  simpa using hlim

/-! ### 2. Abstract Cauchy limit in `C((0, T]; LMH c)` from pairwise Hilbert energy bounds -/

lemma exists_continuousOn_limit_Ioc {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    {W : ℝ → LMH c} {V' : ℕ → ℝ → LMH c} {a : ℕ → ℝ → ℝ}
    (hV : ∀ k : ℕ, BochnerTime.HasWeakDerivTime 0 T
      (fun s => opJ c hc J hJ k (opJ c hc J hJ k (W s))) (V' k))
    (ha_nn : ∀ k r, 0 ≤ a k r)
    (ha_int : ∀ k, IntegrableOn (a k) (Ioo 0 T) volume)
    (ha_tend : Tendsto (fun k => ∫ r in Ioo 0 T, a k r) atTop (𝓝 0))
    (hpair : ∀ k m : ℕ, ∀ᵐ r ∂volume, r ∈ Ioo 0 T →
      2 * ⟪V' k r - V' m r,
        opJ c hc J hJ k (opJ c hc J hJ k (W r)) -
          opJ c hc J hJ m (opJ c hc J hJ m (W r))⟫ ≤ a k r + a m r) :
    ∃ W_lim : ℝ → LMH c,
      ContinuousOn W_lim (Ioc 0 T) ∧
      (∀ᵐ s ∂volume, s ∈ Ioo 0 T → W_lim s = W s) := by
  let ũ : ℕ → ℝ → LMH c := fun k => (hV k).rep
  let W_lim : ℝ → LMH c := fun t => limUnder atTop (fun k => ũ k t)
  have hae_all : ∀ᵐ s ∂volume, ∀ k : ℕ, s ∈ Ioo 0 T →
      opJ c hc J hJ k (opJ c hc J hJ k (W s)) = ũ k s :=
    ae_all_iff.2 fun k => (ae_restrict_iff' measurableSet_Ioo).1 (hV k).ae_eq_rep
  have hae_lim : ∀ᵐ s ∂volume, s ∈ Ioo 0 T → W_lim s = W s := by
    filter_upwards [hae_all] with s hs hmem
    have ht : Tendsto (fun k => ũ k s) atTop (𝓝 (W s)) :=
      (tendsto_opJ_sq hc hJ (W s)).congr fun k => hs k hmem
    exact ht.limUnder_eq
  -- Pairwise energy inequality on any `[s₀, T]` with `s₀ ∈ Ioo 0 T`
  have henergy : ∀ {s₀ t : ℝ}, s₀ ∈ Ioo 0 T → t ∈ Icc s₀ T → ∀ k m : ℕ,
      ‖ũ k t - ũ m t‖ ^ 2 ≤
        ‖ũ k s₀ - ũ m s₀‖ ^ 2 + (∫ r in Ioo 0 T, a k r) + (∫ r in Ioo 0 T, a m r) := by
    intro s₀ t hs₀ ht k m
    have hd : BochnerTime.HasWeakDerivTime 0 T
        (fun s => opJ c hc J hJ k (opJ c hc J hJ k (W s)) -
          opJ c hc J hJ m (opJ c hc J hJ m (W s)))
        (fun s => V' k s - V' m s) :=
      ((hV k).add ((hV m).const_smul (-1 : ℝ))).congr_ae
        (Eventually.of_forall fun s => by simp [sub_eq_add_neg])
        (Eventually.of_forall fun s => by simp [sub_eq_add_neg])
    have heq_rep : EqOn (fun r => ũ k r - ũ m r) hd.rep (Icc 0 T) :=
      hd.eqOn_rep hT (((hV k).continuousOn_rep).sub ((hV m).continuousOn_rep))
        (((hV k).ae_eq_rep).sub ((hV m).ae_eq_rep))
    have hs₀_cc : s₀ ∈ Icc 0 T := ⟨hs₀.1.le, hs₀.2.le⟩
    have ht_cc : t ∈ Icc 0 T := ⟨hs₀.1.le.trans ht.1, ht.2⟩
    have hid := hd.norm_sq_sub hs₀_cc ht_cc
    rw [← heq_rep ht_cc, ← heq_rep hs₀_cc, ← intervalIntegral.integral_const_mul] at hid
    have hint_lhs : IntervalIntegrable
        (fun r => 2 * ⟪V' k r - V' m r, hd.rep r⟫) volume s₀ t :=
      (hd.intervalIntegrable_inner_rep hs₀_cc ht_cc).const_mul 2
    have ha_cc : ∀ n : ℕ, IntegrableOn (a n) (Icc 0 T) volume := fun n => by
      rw [integrableOn_Icc_iff_integrableOn_Ioo]; exact ha_int n
    have hsub_oc : Ioc s₀ t ⊆ Icc 0 T := fun r hr => ⟨hs₀.1.le.trans hr.1.le, hr.2.trans ht.2⟩
    have hint_rhs_oc : IntegrableOn (fun r => a k r + a m r) (Ioc s₀ t) volume :=
      ((ha_cc k).add (ha_cc m)).mono_set hsub_oc
    have hint_rhs : IntervalIntegrable (fun r => a k r + a m r) volume s₀ t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 hint_rhs_oc
    have hae_rep : ∀ᵐ r ∂volume, r ∈ Ioo 0 T →
        opJ c hc J hJ k (opJ c hc J hJ k (W r)) -
          opJ c hc J hJ m (opJ c hc J hJ m (W r)) = hd.rep r :=
      (ae_restrict_iff' measurableSet_Ioo).1 hd.ae_eq_rep
    have hneT : ∀ᵐ r : ℝ ∂volume, r ≠ T := by simp [ae_iff, measure_singleton]
    have hae_le : ∀ᵐ r ∂(volume.restrict (Ioc s₀ t)),
        2 * ⟪V' k r - V' m r, hd.rep r⟫ ≤ a k r + a m r := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hae_rep, hpair k m, hneT] with r hrep hp hrT hmem
      have hr_oo : r ∈ Ioo 0 T :=
        ⟨hs₀.1.trans hmem.1, lt_of_le_of_ne (hmem.2.trans ht.2) hrT⟩
      rw [← hrep hr_oo]
      exact hp hr_oo
    have hmono : (∫ r in s₀..t, 2 * ⟪V' k r - V' m r, hd.rep r⟫) ≤
        ∫ r in s₀..t, (a k r + a m r) := by
      rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
      exact integral_mono_ae
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 hint_lhs) hint_rhs_oc hae_le
    have hrhs_le : (∫ r in s₀..t, (a k r + a m r)) ≤
        (∫ r in Ioo 0 T, a k r) + (∫ r in Ioo 0 T, a m r) := by
      rw [intervalIntegral.integral_of_le ht.1]
      calc (∫ r in Ioc s₀ t, (a k r + a m r))
          ≤ ∫ r in Icc 0 T, (a k r + a m r) :=
            setIntegral_mono_set ((ha_cc k).add (ha_cc m))
              (ae_of_all _ fun r => add_nonneg (ha_nn k r) (ha_nn m r))
              (Eventually.of_forall hsub_oc)
        _ = (∫ r in Icc 0 T, a k r) + (∫ r in Icc 0 T, a m r) :=
            integral_add (ha_cc k) (ha_cc m)
        _ = (∫ r in Ioo 0 T, a k r) + (∫ r in Ioo 0 T, a m r) := by
            rw [setIntegral_congr_set Ioo_ae_eq_Icc, setIntegral_congr_set Ioo_ae_eq_Icc]
    linarith
  -- Given a good `s₀ ∈ Ioo 0 T`, `(ũ k)` converges uniformly on `Icc s₀ T` to `W_lim`
  have hunif_on_good : ∀ {s₀ : ℝ}, s₀ ∈ Ioo 0 T →
      (∀ k : ℕ, opJ c hc J hJ k (opJ c hc J hJ k (W s₀)) = ũ k s₀) →
      (∀ t ∈ Icc s₀ T, Tendsto (fun k => ũ k t) atTop (𝓝 (W_lim t))) ∧
      (∀ k : ℕ, ∀ t ∈ Icc s₀ T,
        ‖ũ k t - W_lim t‖ ^ 2 ≤ ‖ũ k s₀ - W_lim s₀‖ ^ 2 + ∫ r in Ioo 0 T, a k r) := by
    intro s₀ hs₀ hgood_s0
    have ht_s0 : Tendsto (fun k => ũ k s₀) atTop (𝓝 (W s₀)) :=
      (tendsto_opJ_sq hc hJ (W s₀)).congr hgood_s0
    have htend_t : ∀ t ∈ Icc s₀ T, Tendsto (fun k => ũ k t) atTop (𝓝 (W_lim t)) := by
      intro t ht
      have hcau : CauchySeq (fun k => ũ k t) := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        have hε4 : 0 < ε / 4 := by positivity
        have hεsq4 : 0 < ε ^ 2 / 4 := by positivity
        obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
          (Metric.tendsto_nhds.1 ht_s0 (ε / 4) hε4)
        obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
          ((tendsto_order.1 ha_tend).2 (ε ^ 2 / 4) hεsq4)
        refine ⟨max N₁ N₂, fun k hk m hm => ?_⟩
        have hk1 : N₁ ≤ k := (le_max_left _ _).trans hk
        have hm1 : N₁ ≤ m := (le_max_left _ _).trans hm
        have hk2 : N₂ ≤ k := (le_max_right _ _).trans hk
        have hm2 : N₂ ≤ m := (le_max_right _ _).trans hm
        have hds0 : ‖ũ k s₀ - ũ m s₀‖ < ε / 2 := by
          rw [← dist_eq_norm]
          calc dist (ũ k s₀) (ũ m s₀)
              ≤ dist (ũ k s₀) (W s₀) + dist (W s₀) (ũ m s₀) := dist_triangle _ _ _
            _ = dist (ũ k s₀) (W s₀) + dist (ũ m s₀) (W s₀) := by rw [dist_comm (W s₀)]
            _ < ε / 4 + ε / 4 := add_lt_add (hN₁ k hk1) (hN₁ m hm1)
            _ = ε / 2 := by ring
        have hds0_sq : ‖ũ k s₀ - ũ m s₀‖ ^ 2 < ε ^ 2 / 4 := by
          nlinarith [norm_nonneg (ũ k s₀ - ũ m s₀)]
        have hak := hN₂ k hk2
        have ham := hN₂ m hm2
        have hen := henergy hs₀ ht k m
        have hsq_lt : ‖ũ k t - ũ m t‖ ^ 2 < ε ^ 2 := by linarith
        rw [dist_eq_norm]
        nlinarith [norm_nonneg (ũ k t - ũ m t)]
      obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
      have hy_eq : W_lim t = y := hy.limUnder_eq
      rwa [hy_eq]
    refine ⟨htend_t, fun k t ht => ?_⟩
    have hlhs_t : Tendsto (fun m => ‖ũ k t - ũ m t‖ ^ 2) atTop (𝓝 (‖ũ k t - W_lim t‖ ^ 2)) :=
      (((tendsto_const_nhds.sub (htend_t t ht)).norm).pow 2)
    have hrhs_t : Tendsto
        (fun m => ‖ũ k s₀ - ũ m s₀‖ ^ 2 + (∫ r in Ioo 0 T, a k r) + (∫ r in Ioo 0 T, a m r))
        atTop (𝓝 (‖ũ k s₀ - W_lim s₀‖ ^ 2 + (∫ r in Ioo 0 T, a k r) + 0)) :=
      ((((tendsto_const_nhds.sub (htend_t s₀ ⟨le_rfl, hs₀.2.le⟩)).norm).pow 2).add
        tendsto_const_nhds).add ha_tend
    have hlim_le := le_of_tendsto_of_tendsto hlhs_t hrhs_t
      (Eventually.of_forall fun m => henergy hs₀ ht k m)
    linarith
  -- Continuity of `W_lim` on `Ioc 0 T`
  refine ⟨W_lim, fun t₀ ht₀ => ?_, hae_lim⟩
  -- Pick a good `s₀ ∈ Ioo 0 t₀`
  have hV_pos : 0 < volume (Ioo 0 t₀) :=
    isOpen_Ioo.measure_pos volume ⟨t₀ / 2, by linarith [ht₀.1], by linarith [ht₀.1]⟩
  have hN0 : volume {s : ℝ | ¬(∀ k : ℕ, s ∈ Ioo 0 T →
      opJ c hc J hJ k (opJ c hc J hJ k (W s)) = ũ k s)} = 0 := ae_iff.1 hae_all
  obtain ⟨s₀, hs₀_lt, hs₀_good_raw⟩ : ∃ s₀ ∈ Ioo 0 t₀,
      ∀ k : ℕ, s₀ ∈ Ioo 0 T → opJ c hc J hJ k (opJ c hc J hJ k (W s₀)) = ũ k s₀ := by
    by_contra hcon
    have hsub : Ioo 0 t₀ ⊆ {s : ℝ | ¬(∀ k : ℕ, s ∈ Ioo 0 T →
        opJ c hc J hJ k (opJ c hc J hJ k (W s)) = ũ k s)} :=
      fun s hs hh => hcon ⟨s, hs, hh⟩
    exact hV_pos.ne' (measure_mono_null hsub hN0)
  have hs₀_oo : s₀ ∈ Ioo 0 T := ⟨hs₀_lt.1, hs₀_lt.2.trans_le ht₀.2⟩
  have hs₀_good : ∀ k : ℕ, opJ c hc J hJ k (opJ c hc J hJ k (W s₀)) = ũ k s₀ :=
    fun k => hs₀_good_raw k hs₀_oo
  obtain ⟨htend_t, htail⟩ := hunif_on_good hs₀_oo hs₀_good
  have ht₀_cc : t₀ ∈ Icc s₀ T := ⟨hs₀_lt.2.le, ht₀.2⟩
  have hcont_cc : ContinuousWithinAt W_lim (Icc s₀ T) t₀ := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have herr_tend : Tendsto
        (fun k => ‖ũ k s₀ - W_lim s₀‖ ^ 2 + ∫ r in Ioo 0 T, a k r) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => ‖ũ k s₀ - W_lim s₀‖ ^ 2) atTop (𝓝 0) := by
        have hn := tendsto_iff_norm_sub_tendsto_zero.1 (htend_t s₀ ⟨le_rfl, hs₀_oo.2.le⟩)
        simpa using hn.pow 2
      simpa using h1.add ha_tend
    have hε3_sq : 0 < (ε / 3) ^ 2 := by positivity
    obtain ⟨k, hk⟩ := (((tendsto_order.1 herr_tend).2 ((ε / 3) ^ 2) hε3_sq)).exists
    have hk_unif : ∀ t ∈ Icc s₀ T, dist (ũ k t) (W_lim t) < ε / 3 := by
      intro t ht
      rw [dist_eq_norm]
      have hsq : ‖ũ k t - W_lim t‖ ^ 2 < (ε / 3) ^ 2 := (htail k t ht).trans_lt hk
      nlinarith [norm_nonneg (ũ k t - W_lim t)]
    have hũk_cont : ContinuousWithinAt (ũ k) (Icc s₀ T) t₀ :=
      ((hV k).continuousOn_rep.mono (Icc_subset_Icc hs₀_oo.1.le le_rfl)) t₀ ht₀_cc
    obtain ⟨δ, hδ, hδ_ball⟩ := Metric.continuousWithinAt_iff.1 hũk_cont (ε / 3) (by positivity)
    refine ⟨δ, hδ, fun t ht hdist => ?_⟩
    calc dist (W_lim t) (W_lim t₀)
        ≤ dist (W_lim t) (ũ k t) + dist (ũ k t) (W_lim t₀) := dist_triangle _ _ _
      _ ≤ dist (W_lim t) (ũ k t) + (dist (ũ k t) (ũ k t₀) + dist (ũ k t₀) (W_lim t₀)) :=
          add_le_add_right (dist_triangle _ _ _) _
      _ = dist (ũ k t) (W_lim t) + dist (ũ k t) (ũ k t₀) + dist (ũ k t₀) (W_lim t₀) := by
          rw [dist_comm (W_lim t)]; ring
      _ < ε / 3 + ε / 3 + ε / 3 :=
          add_lt_add (add_lt_add (hk_unif t ht) (hδ_ball ht hdist)) (hk_unif t₀ ht₀_cc)
      _ = ε := by ring
  have hmem_nhds : Icc s₀ T ∈ 𝓝[Ioc 0 T] t₀ := by
    refine Filter.mem_of_superset
      (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hs₀_lt.2))) ?_
    rintro x ⟨hx_oc, hx_gt⟩
    exact ⟨le_of_lt hx_gt, hx_oc.2⟩
  exact hcont_cc.mono_of_mem_nhdsWithin hmem_nhds

/-! ### 3. `L²` and `H¹` mollified Bochner derivatives and pairwise energy bounds -/

private lemma integrableOn_early_all {p : Params} {T M C_tr : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    {g gq gη z₀ zq₀ zη₀ b_cut : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_sm : StronglyMeasurable b_cut)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => b_cut (s, y)) ≤ ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M) :
    IntegrableOn (cprofToLMH p.c z₀) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c zq₀) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c zη₀) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c b_cut) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c g) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c gq) (Ioo 0 T) volume ∧
      IntegrableOn (cprofToLMH p.c gη) (Ioo 0 T) volume := by
  have _ : 0 < T := hT
  have hvol_fin : volume (Ioo 0 T) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hgood := ae_earlyGoodSlice hM hC_tr hg hg_int hz hb_sm hb_le hbdd
  have hfin_of_le : ∀ (W : CProf) (K : ℝ),
      (∀ᵐ s ∂volume, s ∈ Ioo 0 T → cylSliceL2 p.c (fun y => W (s, y)) ≤ ENNReal.ofReal K) →
      (∫⁻ s in Ioo 0 T, cylSliceL2 p.c (fun y => W (s, y))) < ⊤ := by
    intro W K hK
    calc ∫⁻ s in Ioo 0 T, cylSliceL2 p.c (fun y => W (s, y))
        ≤ ∫⁻ _s in Ioo 0 T, ENNReal.ofReal K :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 hK)
      _ = ENNReal.ofReal K * volume (Ioo 0 T) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol_fin
  have hg_sub : ∀ (W : CProf),
      (∀ s, cylSliceL2 p.c (fun y => W (s, y)) ≤ sliceH1Norm p.c g gq gη s) →
      (∫⁻ s in Ioo 0 T, cylSliceL2 p.c (fun y => W (s, y))) < ⊤ := fun W hW => by
    calc ∫⁻ s in Ioo 0 T, cylSliceL2 p.c (fun y => W (s, y))
        ≤ ∫⁻ s in Ioc 0 T, cylSliceL2 p.c (fun y => W (s, y)) :=
          lintegral_mono_set Ioo_subset_Ioc_self
      _ ≤ ∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s := lintegral_mono hW
      _ < ⊤ := hg_int
  refine ⟨integrableOn_cprofToLMH hz.sm_z measurableSet_Ioo (hfin_of_le z₀ M ?_),
    integrableOn_cprofToLMH hz.sm_zq measurableSet_Ioo (hfin_of_le zq₀ M ?_),
    integrableOn_cprofToLMH hz.sm_zη measurableSet_Ioo (hfin_of_le zη₀ M ?_),
    integrableOn_cprofToLMH hb_sm measurableSet_Ioo (hfin_of_le b_cut (C_tr * M) ?_),
    integrableOn_cprofToLMH hg.sm_g measurableSet_Ioo (hg_sub g fun _ =>
      (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)),
    integrableOn_cprofToLMH hg.sm_gq measurableSet_Ioo (hg_sub gq fun _ =>
      (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)),
    integrableOn_cprofToLMH hg.sm_gη measurableSet_Ioo (hg_sub gη fun _ =>
      le_add_of_nonneg_left zero_le)⟩
  · filter_upwards [hgood] with s hs hmem
    exact ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)).trans
      (hs hmem).bound_z
  · filter_upwards [hgood] with s hs hmem
    exact ((le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)).trans
      (hs hmem).bound_z
  · filter_upwards [hgood] with s hs hmem
    exact (le_add_of_nonneg_left zero_le).trans (hs hmem).bound_z
  · filter_upwards [hgood] with s hs hmem
    exact (hs hmem).bound_b

private lemma exists_early_lmH_limits {p : Params} {T M C_tr : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hC_tr : 0 ≤ C_tr)
    {g gq gη z₀ zq₀ zη₀ : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : IsEarlyBorelRep p T g z₀ zq₀ zη₀)
    (hb_le : ∀ s ∈ Ioc 0 T,
      cylSliceL2 p.c (fun y => bCut p T z₀ zq₀ zη₀ (s, y)) ≤
        ENNReal.ofReal C_tr * sliceH1Norm p.c z₀ zq₀ zη₀ s)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z₀ zq₀ zη₀ s ≤ ENNReal.ofReal M) :
    ∃ Z_lim Zq_lim Zη_lim : ℝ → LMH p.c,
      ContinuousOn Z_lim (Ioc 0 T) ∧
      ContinuousOn Zq_lim (Ioc 0 T) ∧
      ContinuousOn Zη_lim (Ioc 0 T) ∧
      (∀ᵐ s ∂volume, s ∈ Ioo 0 T →
        Z_lim s = cprofToLMH p.c z₀ s ∧
        Zq_lim s = cprofToLMH p.c zq₀ s ∧
        Zη_lim s = cprofToLMH p.c zη₀ s) := by
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  obtain ⟨J, hJ⟩ := hasLMMollifier p.c hc
  set b_cut := bCut p T z₀ zq₀ zη₀
  have hb_sm : StronglyMeasurable b_cut := stronglyMeasurable_bCut p T hz.sm_z hz.sm_zq hz.sm_zη
  obtain ⟨hZ0_int, hZq0_int, hZη0_int, hB_int, hG_int, hGq_int, hGη_int⟩ :=
    integrableOn_early_all hT hM hC_tr hg hg_int hz hb_sm hb_le hbdd
  set Z0 := cprofToLMH p.c z₀
  set Zd0 : Fin 2 → ℝ → LMH p.c := fun j => cprofToLMH p.c (![zq₀, zη₀] j)
  set P0B : ℝ → LMH p.c := fun s => opP0 p.c hc (cprofToLMH p.c b_cut s)
  set G0 := cprofToLMH p.c g
  set Gd0 : Fin 2 → ℝ → LMH p.c := fun j => cprofToLMH p.c (![gq, gη] j)
  have hP0B_int : IntegrableOn P0B (Ioo 0 T) volume := (opP0 p.c hc).integrable_comp hB_int
  have hGd_int : ∀ d : Fin 2, IntegrableOn (Gd0 d) (Ioo 0 T) volume := fun d => by
    fin_cases d
    · exact hGq_int
    · exact hGη_int
  have hgood := ae_earlyGoodSlice hM hC_tr hg hg_int hz hb_sm hb_le hbdd
  have hderiv1 : ∀ k : ℕ, BochnerTime.HasWeakDerivTime 0 T
      (fun s => opJ p.c hc J hJ k (Z0 s))
      (mollTimeDeriv p hc J hJ k zq₀ zη₀ b_cut g) :=
    fun k => hasWeakDerivTime_opJ_Z0 hT hM hC_tr hc J hJ k hg hg_int hz hb_le hbdd
  -- 1. `L²` path `Z_lim`
  let V0' : ℕ → ℝ → LMH p.c := fun k s =>
    opJ p.c hc J hJ k (mollTimeDeriv p hc J hJ k zq₀ zη₀ b_cut g s)
  let a0 : ℕ → ℝ → ℝ := fun k r =>
    4 * M * (‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
      ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) - G0 r‖)
  have hV0 : ∀ k : ℕ, BochnerTime.HasWeakDerivTime 0 T
      (fun s => opJ p.c hc J hJ k (opJ p.c hc J hJ k (Z0 s))) (V0' k) :=
    fun k => (hderiv1 k).map (opJ p.c hc J hJ k)
  have ha0_nn : ∀ k r, 0 ≤ a0 k r := fun k r => by
    dsimp [a0]; positivity
  have ha0_int : ∀ k, IntegrableOn (a0 k) (Ioo 0 T) volume := fun k =>
    ((integrableOn_norm_opJ_sq_sub hc hJ k hP0B_int).add
      (integrableOn_norm_opJ_sq_sub hc hJ k hG_int)).const_mul (4 * M)
  have ha0_tend : Tendsto (fun k => ∫ r in Ioo 0 T, a0 k r) atTop (𝓝 0) := by
    have h1 := tendsto_integral_norm_opJ_sq_sub hc hJ hP0B_int
    have h2 := tendsto_integral_norm_opJ_sq_sub hc hJ hG_int
    have hsum : Tendsto (fun k => 4 * M *
        ((∫ r in Ioo 0 T, ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖) +
          (∫ r in Ioo 0 T, ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) - G0 r‖)))
        atTop (𝓝 0) := by
      simpa using (h1.add h2).const_mul (4 * M)
    refine hsum.congr fun k => ?_
    have i1 := integrableOn_norm_opJ_sq_sub hc hJ k hP0B_int
    have i2 := integrableOn_norm_opJ_sq_sub hc hJ k hG_int
    rw [← integral_add i1 i2, ← integral_const_mul]
  have hpair0 : ∀ k m : ℕ, ∀ᵐ r ∂volume, r ∈ Ioo 0 T →
      2 * ⟪V0' k r - V0' m r,
        opJ p.c hc J hJ k (opJ p.c hc J hJ k (Z0 r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (Z0 r))⟫ ≤ a0 k r + a0 m r := by
    intro k m
    filter_upwards [hgood] with r hr hmem
    have hgs := hr hmem
    set W : LMH p.c :=
      opJ p.c hc J hJ k (opJ p.c hc J hJ k (Z0 r)) -
        opJ p.c hc J hJ m (opJ p.c hc J hJ m (Z0 r))
    have hW_le : ‖W‖ ≤ 2 * M := by
      have h1 : ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Z0 r))‖ ≤ M :=
        (norm_opJ_le hc hJ k _).trans ((norm_opJ_le hc hJ k _).trans (hgs.norm_Z0_le hM))
      have h2 : ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (Z0 r))‖ ≤ M :=
        (norm_opJ_le hc hJ m _).trans ((norm_opJ_le hc hJ m _).trans (hgs.norm_Z0_le hM))
      have h3 : ‖W‖ ≤ ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Z0 r))‖ +
          ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (Z0 r))‖ := norm_sub_le _ _
      linarith
    have hV0_diff : V0' k r - V0' m r =
        p.ν • (∑ j : Fin 2,
          (opJ p.c hc J hJ k (opDJ p.c hc J hJ k j (Zd0 j r)) -
            opJ p.c hc J hJ m (opDJ p.c hc J hJ m j (Zd0 j r)))) -
        (opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r))) +
        (opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r))) := by
      simp only [V0', mollTimeDeriv, Fin.sum_univ_two, Zd0, P0B, G0,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        map_add, map_sub, map_smul, smul_add, smul_sub]
      abel
    have hvisc := inner_viscous_L2_nonpos hc hJ k m hgs.lmWeakPd_Z
    have hdr : -⟪opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)), W⟫ ≤
        (‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
          ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r‖) * (2 * M) := by
      have hcs := abs_real_inner_le_norm
        (opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r))) W
      have htri : ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r))‖ ≤
          ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
            ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r‖ := by
        have heq : opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) =
          (opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r) -
            (opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r) := by abel
        rw [heq]; exact norm_sub_le _ _
      have hneg_le : -⟪opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)), W⟫ ≤
          |⟪opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)), W⟫| := neg_le_abs _
      exact (hneg_le.trans hcs).trans (mul_le_mul htri hW_le (norm_nonneg _) (by positivity))
    have hsrc : ⟪opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r)), W⟫ ≤
        (‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) - G0 r‖ +
          ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r)) - G0 r‖) * (2 * M) := by
      have hcs := real_inner_le_norm
        (opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r))) W
      have htri : ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r))‖ ≤
          ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) - G0 r‖ +
            ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r)) - G0 r‖ := by
        have heq : opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r)) =
          (opJ p.c hc J hJ k (opJ p.c hc J hJ k (G0 r)) - G0 r) -
            (opJ p.c hc J hJ m (opJ p.c hc J hJ m (G0 r)) - G0 r) := by abel
        rw [heq]; exact norm_sub_le _ _
      exact hcs.trans (mul_le_mul htri hW_le (norm_nonneg _) (by positivity))
    rw [hV0_diff, inner_add_left, inner_sub_left, real_inner_smul_left]
    have hν_visc : p.ν * ⟪∑ j : Fin 2,
        (opJ p.c hc J hJ k (opDJ p.c hc J hJ k j (Zd0 j r)) -
          opJ p.c hc J hJ m (opDJ p.c hc J hJ m j (Zd0 j r))), W⟫ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hν.le hvisc
    dsimp [a0]
    linarith
  obtain ⟨Z_lim, hZ_cont, hZ_ae⟩ :=
    exists_continuousOn_limit_Ioc hc hT hJ hV0 ha0_nn ha0_int ha0_tend hpair0
  -- 2. `H¹` derivative paths `Zq_lim`, `Zη_lim` (`d : Fin 2`)
  have hex_d : ∀ d : Fin 2, ∃ Zd_lim : ℝ → LMH p.c,
      ContinuousOn Zd_lim (Ioc 0 T) ∧
      (∀ᵐ s ∂volume, s ∈ Ioo 0 T → Zd_lim s = Zd0 d s) := by
    intro d
    let Vd' : ℕ → ℝ → LMH p.c := fun k s =>
      p.ν • (∑ j : Fin 2, opDJ p.c hc J hJ k d (opDJ p.c hc J hJ k j (Zd0 j s))) -
        opDJ p.c hc J hJ k d (opJ p.c hc J hJ k (P0B s)) +
        opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d s))
    let ad : ℕ → ℝ → ℝ := fun k r =>
      p.ν⁻¹ * (2 * (C_tr * M)) * ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
        4 * M * ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) - Gd0 d r‖
    have hVd : ∀ k : ℕ, BochnerTime.HasWeakDerivTime 0 T
        (fun s => opJ p.c hc J hJ k (opJ p.c hc J hJ k (Zd0 d s))) (Vd' k) := by
      intro k
      refine ((hderiv1 k).map (opDJ p.c hc J hJ k d)).congr_ae ?_ ?_
      · rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hgood] with s hs hmem
        have hgs := hs hmem
        change opDJ p.c hc J hJ k d (opJ p.c hc J hJ k (Z0 s)) =
          opJ p.c hc J hJ k (opJ p.c hc J hJ k (Zd0 d s))
        rw [opDJ_comm_opJ hc hJ k k d (Z0 s),
          opDJ_eq_opJ_of_weakPd hc hJ k d (hgs.lmWeakPd_Z d)]
      · rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hgood] with s hs hmem
        have hgs := hs hmem
        have hg_comm : opDJ p.c hc J hJ k d (opJ p.c hc J hJ k (G0 s)) =
            opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d s)) := by
          rw [opDJ_comm_opJ hc hJ k k d (G0 s),
            opDJ_eq_opJ_of_weakPd hc hJ k d (hgs.lmWeakPd_G d)]
        simp only [Vd', mollTimeDeriv, Fin.sum_univ_two, Zd0, P0B, G0,
          map_add, map_sub, map_smul, hg_comm]
        simp
    have had_nn : ∀ k r, 0 ≤ ad k r := fun k r => by
      dsimp [ad]; positivity
    have had_int : ∀ k, IntegrableOn (ad k) (Ioo 0 T) volume := fun k =>
      ((integrableOn_norm_opJ_sq_sub hc hJ k hP0B_int).const_mul (p.ν⁻¹ * (2 * (C_tr * M)))).add
        ((integrableOn_norm_opJ_sq_sub hc hJ k (hGd_int d)).const_mul (4 * M))
    have had_tend : Tendsto (fun k => ∫ r in Ioo 0 T, ad k r) atTop (𝓝 0) := by
      have h1 := (tendsto_integral_norm_opJ_sq_sub hc hJ hP0B_int).const_mul
        (p.ν⁻¹ * (2 * (C_tr * M)))
      have h2 := (tendsto_integral_norm_opJ_sq_sub hc hJ (hGd_int d)).const_mul (4 * M)
      have hsum : Tendsto (fun k =>
          p.ν⁻¹ * (2 * (C_tr * M)) *
            (∫ r in Ioo 0 T, ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖) +
          4 * M *
            (∫ r in Ioo 0 T, ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) - Gd0 d r‖))
          atTop (𝓝 0) := by
        simpa using h1.add h2
      refine hsum.congr fun k => ?_
      have i1 := (integrableOn_norm_opJ_sq_sub hc hJ k hP0B_int).const_mul
        (p.ν⁻¹ * (2 * (C_tr * M)))
      have i2 := (integrableOn_norm_opJ_sq_sub hc hJ k (hGd_int d)).const_mul (4 * M)
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
    have hpair_d : ∀ k m : ℕ, ∀ᵐ r ∂volume, r ∈ Ioo 0 T →
        2 * ⟪Vd' k r - Vd' m r,
          opJ p.c hc J hJ k (opJ p.c hc J hJ k (Zd0 d r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (Zd0 d r))⟫ ≤ ad k r + ad m r := by
      intro k m
      filter_upwards [hgood] with r hr hmem
      have hgs := hr hmem
      set Wd : LMH p.c :=
        opJ p.c hc J hJ k (opJ p.c hc J hJ k (Zd0 d r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (Zd0 d r))
      have hZd_le : ‖Zd0 d r‖ ≤ M := by
        fin_cases d
        · exact hgs.norm_Zq0_le hM
        · exact hgs.norm_Zη0_le hM
      have hWd_le : ‖Wd‖ ≤ 2 * M := by
        have h1 : ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Zd0 d r))‖ ≤ M :=
          (norm_opJ_le hc hJ k _).trans ((norm_opJ_le hc hJ k _).trans hZd_le)
        have h2 : ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (Zd0 d r))‖ ≤ M :=
          (norm_opJ_le hc hJ m _).trans ((norm_opJ_le hc hJ m _).trans hZd_le)
        have h3 : ‖Wd‖ ≤ ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Zd0 d r))‖ +
            ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (Zd0 d r))‖ := norm_sub_le _ _
        linarith
      have hVd_diff : Vd' k r - Vd' m r =
          (p.ν • (∑ j : Fin 2,
            (opDJ p.c hc J hJ k d (opDJ p.c hc J hJ k j (Zd0 j r)) -
              opDJ p.c hc J hJ m d (opDJ p.c hc J hJ m j (Zd0 j r)))) -
          (opDJ p.c hc J hJ k d (opJ p.c hc J hJ k (P0B r)) -
            opDJ p.c hc J hJ m d (opJ p.c hc J hJ m (P0B r)))) +
          (opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r))) := by
        simp only [Vd', Fin.sum_univ_two, smul_add, smul_sub]
        abel
      have hvd_est := inner_viscous_drift_H1_le hc hν hJ k m d (P0B r) hgs.lmWeakPd_Z
      have hP0B_le : ‖P0B r‖ ≤ C_tr * M :=
        (norm_opP0_le hc _).trans (hgs.norm_B_le hM hC_tr)
      have hY_sq : ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r))‖ ^ 2 ≤
          2 * (C_tr * M) *
            (‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
              ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r‖) := by
        set D := opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) -
          opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r))
        have hD_bdd : ‖D‖ ≤ 2 * (C_tr * M) := by
          have h1 : ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r))‖ ≤ C_tr * M :=
            (norm_opJ_le hc hJ k _).trans ((norm_opJ_le hc hJ k _).trans hP0B_le)
          have h2 : ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r))‖ ≤ C_tr * M :=
            (norm_opJ_le hc hJ m _).trans ((norm_opJ_le hc hJ m _).trans hP0B_le)
          have h3 : ‖D‖ ≤ ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r))‖ +
              ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r))‖ := norm_sub_le _ _
          linarith
        have hD_tri : ‖D‖ ≤
            ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
              ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r‖ := by
          have heq : D = (opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r) -
              (opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r) := by dsimp [D]; abel
          rw [heq]; exact norm_sub_le _ _
        calc ‖D‖ ^ 2 = ‖D‖ * ‖D‖ := sq ‖D‖
          _ ≤ (2 * (C_tr * M)) *
              (‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
                ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r‖) :=
            mul_le_mul hD_bdd hD_tri (norm_nonneg _) (by positivity)
      have hsrc : 2 * ⟪opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r)), Wd⟫ ≤
          4 * M * (‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) - Gd0 d r‖ +
            ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r)) - Gd0 d r‖) := by
        have hcs := real_inner_le_norm
          (opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) -
            opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r))) Wd
        have htri : ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) -
              opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r))‖ ≤
            ‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) - Gd0 d r‖ +
              ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r)) - Gd0 d r‖ := by
          have heq : opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) -
              opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r)) =
            (opJ p.c hc J hJ k (opJ p.c hc J hJ k (Gd0 d r)) - Gd0 d r) -
              (opJ p.c hc J hJ m (opJ p.c hc J hJ m (Gd0 d r)) - Gd0 d r) := by abel
          rw [heq]; exact norm_sub_le _ _
        have hmul := mul_le_mul htri hWd_le (norm_nonneg _) (by positivity)
        linarith
      rw [hVd_diff, inner_add_left, mul_add]
      have hvd_bound : 2 * ⟪p.ν • (∑ j : Fin 2,
            (opDJ p.c hc J hJ k d (opDJ p.c hc J hJ k j (Zd0 j r)) -
              opDJ p.c hc J hJ m d (opDJ p.c hc J hJ m j (Zd0 j r)))) -
          (opDJ p.c hc J hJ k d (opJ p.c hc J hJ k (P0B r)) -
            opDJ p.c hc J hJ m d (opJ p.c hc J hJ m (P0B r))), Wd⟫ ≤
          p.ν⁻¹ * (2 * (C_tr * M) *
            (‖opJ p.c hc J hJ k (opJ p.c hc J hJ k (P0B r)) - P0B r‖ +
              ‖opJ p.c hc J hJ m (opJ p.c hc J hJ m (P0B r)) - P0B r‖)) :=
        hvd_est.trans (mul_le_mul_of_nonneg_left hY_sq (inv_pos.2 hν).le)
      dsimp [ad]
      linarith
    exact exists_continuousOn_limit_Ioc hc hT hJ hVd had_nn had_int had_tend hpair_d
  obtain ⟨Zq_lim, hZq_cont, hZq_ae⟩ := hex_d 0
  obtain ⟨Zη_lim, hZη_cont, hZη_ae⟩ := hex_d 1
  refine ⟨Z_lim, Zq_lim, Zη_lim, hZ_cont, hZq_cont, hZη_cont, ?_⟩
  filter_upwards [hZ_ae, hZq_ae, hZη_ae] with s h1 h2 h3 hs
  exact ⟨h1 hs, h2 hs, h3 hs⟩

/-! ### 4. Jointly measurable periodic representative `(z₁, zq₁, zη₁)` and horizon trace -/

private lemma hasWeakCellDerivC_congr_ae {c : ℝ} {j : Fin 2} {u v g h : B0579.Plane → ℂ}
    (hu : u =ᵐ[volume.restrict (B0579.cell c)] v)
    (hg : g =ᵐ[volume.restrict (B0579.cell c)] h)
    (hw : HasWeakCellDerivC c j u g) :
    HasWeakCellDerivC c j v h := by
  obtain ⟨hI, hE⟩ := hw
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have e1 : (fun x => u x * (B0579.pd j ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => v x * (B0579.pd j ψ x : ℂ) := hu.mono fun x hx => by dsimp only; rw [hx]
    have e2 : (fun x => g x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => h x * (ψ x : ℂ) := hg.mono fun x hx => by dsimp only; rw [hx]
    exact ⟨(hI ψ hψ).1.congr e1, (hI ψ hψ).2.congr e2⟩
  · have e1 : (fun x => v x * (B0579.pd j ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => u x * (B0579.pd j ψ x : ℂ) := hu.symm.mono fun x hx => by dsimp only; rw [hx]
    have e2 : (fun x => h x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => g x * (ψ x : ℂ) := hg.symm.mono fun x hx => by dsimp only; rw [hx]
    rw [integral_congr_ae e1, integral_congr_ae e2, hE ψ hψ]

private lemma tendsto_cell_comp_integral {c T : ℝ} {W : CProf} {X : ℝ → LMH c}
    (hX_eq : ∀ s ∈ Ioc 0 T, cprofToLMH c W s = X s)
    (hW_mem : ∀ s ∈ Ioc 0 T, MemLp (fun y => W (s, y)) 2 (volume.restrict (B0579.cell c)))
    {sn : ℕ → ℝ} (hsn_mem : ∀ n, sn n ∈ Ioc 0 T) (hT_mem : T ∈ Ioc 0 T)
    (hX_tend : Tendsto (fun n => X (sn n)) atTop (𝓝 (X T)))
    (k : Fin 2) {χ : B0579.Plane → ℝ}
    (hχ : MemLp χ 2 (volume.restrict (B0579.cell c))) :
    Tendsto (fun n => ∫ y in B0579.cell c, W (sn n, y) k * (χ y : ℂ))
      atTop (𝓝 (∫ y in B0579.cell c, W (T, y) k * (χ y : ℂ))) := by
  let φ : B0579.Plane → Fin 2 → ℝ := fun y i => if i = k then χ y else 0
  have hφ : ∀ i : Fin 2, MemLp (fun y => φ y i) 2 (volume.restrict (B0579.cell c)) := fun i => by
    by_cases hik : i = k
    · simpa [φ, hik] using hχ
    · simp [φ, hik]
  have hsum_eq : ∀ s : ℝ,
      (∑ i : Fin 2, ∫ y in B0579.cell c, W (s, y) i * (φ y i : ℂ)) =
        ∫ y in B0579.cell c, W (s, y) k * (χ y : ℂ) := fun s => by
    have hk01 : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk01 with rfl | rfl <;> simp [Fin.sum_univ_two, φ]
  have tin : ∀ A : LMH c,
      Tendsto (fun n => ⟪A, X (sn n)⟫) atTop (𝓝 ⟪A, X T⟫) := fun A => by
    have hsub : Tendsto (fun n => ‖A‖ * ‖X (sn n) - X T‖) atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hX_tend).const_mul ‖A‖
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hsub
    rw [← inner_sub_right, Real.norm_eq_abs]
    exact abs_real_inner_le_norm A (X (sn n) - X T)
  have hre_s : ∀ s ∈ Ioc 0 T,
      (∫ y in B0579.cell c, W (s, y) k * (χ y : ℂ)).re =
        ⟪toLMH (vecRe φ) (vecRe_cellL2 hφ), X s⟫ := fun s hs => by
    rw [← hsum_eq s, re_cell_pair_eq_inner (hW_mem s hs) hφ, hX_eq s hs]
  have him_s : ∀ s ∈ Ioc 0 T,
      (∫ y in B0579.cell c, W (s, y) k * (χ y : ℂ)).im =
        ⟪toLMH (vecIm φ) (vecIm_cellL2 hφ), X s⟫ := fun s hs => by
    rw [← hsum_eq s, im_cell_pair_eq_inner (hW_mem s hs) hφ, hX_eq s hs]
  have hre_tend : Tendsto (fun n => (∫ y in B0579.cell c, W (sn n, y) k * (χ y : ℂ)).re)
      atTop (𝓝 (∫ y in B0579.cell c, W (T, y) k * (χ y : ℂ)).re) := by
    rw [hre_s T hT_mem]
    exact (tin _).congr fun n => (hre_s (sn n) (hsn_mem n)).symm
  have him_tend : Tendsto (fun n => (∫ y in B0579.cell c, W (sn n, y) k * (χ y : ℂ)).im)
      atTop (𝓝 (∫ y in B0579.cell c, W (T, y) k * (χ y : ℂ)).im) := by
    rw [him_s T hT_mem]
    exact (tin _).congr fun n => (him_s (sn n) (hsn_mem n)).symm
  have hcomb := (Complex.continuous_ofReal.tendsto _ |>.comp hre_tend).add
    ((Complex.continuous_ofReal.tendsto _ |>.comp him_tend).mul_const Complex.I)
  simpa [Complex.re_add_im] using hcomb

/-- Extraction of a strongly measurable, everywhere `p.c`-periodic `C((0, T]; H¹_σ(C_c))`
representative `(z₁, zq₁, zη₁)` of `(z_eb, zq_eb, zη_eb)` on `(0, T]`, together with its horizon
slice property `IsCylH1Slice` at `s = T`, uniform `H¹` bound on `Ioc 0 T`, and early weak PDE
properties on `Ioo 0 T ×ˢ univ`. -/
theorem exists_early_horizon_rep {p : Params} {d dm dp T M : ℝ} {α : E2}
    (hbg : BgRegime p d dm dp) (hT : 0 < T) (hM : 0 ≤ M)
    {g gq gη z_eb zq_eb zη_eb : CProf}
    (hg : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioc 0 T, sliceH1Norm p.c g gq gη s) < ⊤)
    (heb : IsMeridionalCorrectionOn p T g z_eb zq_eb zη_eb α)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → sliceH1Norm p.c z_eb zq_eb zη_eb s ≤ ENNReal.ofReal M) :
    ∃ z₁ zq₁ zη₁ : CProf,
      StronglyMeasurable z₁ ∧ StronglyMeasurable zq₁ ∧ StronglyMeasurable zη₁ ∧
      (∀ x : Coord,
        z₁ (qShift p.c x) = z₁ x ∧ zq₁ (qShift p.c x) = zq₁ x ∧ zη₁ (qShift p.c x) = zη₁ x) ∧
      QPeriodic p.c z₁ ∧ QPeriodic p.c zq₁ ∧ QPeriodic p.c zη₁ ∧
      (∀ᵐ x : Coord, x.1 ∈ Ioo 0 T →
        z₁ x = z_eb x ∧ zq₁ x = zq_eb x ∧ zη₁ x = zη_eb x) ∧
      (∀ s ∈ Ioc 0 T,
        Tendsto (fun s' => cylSliceH1 p.c
          (fun y => z₁ (s', y) - z₁ (s, y))
          (fun y => zq₁ (s', y) - zq₁ (s, y))
          (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0)) ∧
      IsCylH1Slice p.c (fun y => z₁ (T, y)) (fun y => zq₁ (T, y)) (fun y => zη₁ (T, y)) ∧
      (∀ s ∈ Ioc 0 T, sliceH1Norm p.c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (3 * M)) ∧
      (∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
        Integrable (fun x => z₁ x i * (coordTranspose vQ0 dZero φ x : ℂ)) ∧
          Integrable (fun x => zq₁ x i * (φ x : ℂ)) ∧
          ∫ x, zq₁ x i * (φ x : ℂ) = ∫ x, z₁ x i * (coordTranspose vQ0 dZero φ x : ℂ)) ∧
      (∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
        Integrable (fun x => z₁ x i * (coordTranspose vEta dZero φ x : ℂ)) ∧
          Integrable (fun x => zη₁ x i * (φ x : ℂ)) ∧
          ∫ x, zη₁ x i * (φ x : ℂ) = ∫ x, z₁ x i * (coordTranspose vEta dZero φ x : ℂ)) ∧
      (∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
        Integrable (fun x => z₁ x 0 * (cpd 1 φ x : ℂ) + z₁ x 1 * (cpd 2 φ x : ℂ)) ∧
          ∫ x, (z₁ x 0 * (cpd 1 φ x : ℂ) + z₁ x 1 * (cpd 2 φ x : ℂ)) = 0) ∧
      (∀ Ψ, IsPlanarSolTest Ψ → (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo 0 T ×ˢ univ) →
        Integrable (fun x => ∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i) ∧
          Integrable (cdot (flatBv p.train z₁ zq₁ zη₁) Ψ) ∧
          Integrable (cdot g Ψ) ∧
          ∫ x, (∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x) =
            ∫ x, cdot g Ψ x) := by
  have hc : 0 < p.c := p.c_pos
  obtain ⟨z₀, zq₀, zη₀, hz₀, hae_eb, hbdd₀⟩ := upgrade_early_correction heb hbdd
  obtain ⟨C_tr, hC_tr, hb_le⟩ :=
    exists_bCut_sliceL2_bound hbg hT z₀ zq₀ zη₀ hz₀.sm_z hz₀.sm_zq hz₀.sm_zη
  obtain ⟨Z_lim, Zq_lim, Zη_lim, hZ_cont, hZq_cont, hZη_cont, hae_lim⟩ :=
    exists_early_lmH_limits hT hM hC_tr hg hg_int hz₀ hb_le hbdd₀
  -- Jointly strongly measurable representatives on `Ioc 0 T`
  obtain ⟨FZ, hFZ_sm, hFZ_rep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Ioc hZ_cont
  obtain ⟨FZq, hFZq_sm, hFZq_rep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Ioc
      hZq_cont
  obtain ⟨FZη, hFZη_sm, hFZη_rep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Ioc
      hZη_cont
  let perCoord : Coord → Coord := fun x => (x.1, lmPer p.c x.2)
  have hper_meas : Measurable perCoord :=
    measurable_fst.prodMk ((measurable_lmPer p.c).comp measurable_snd)
  have hper_qShift : ∀ x : Coord, perCoord (qShift p.c x) = perCoord x := fun x => by
    dsimp [perCoord, qShift]
    rw [lmPer_add p.c hc.ne' x.2]
  let z₁ : CProf := fun x => lmToCMerid (FZ (perCoord x))
  let zq₁ : CProf := fun x => lmToCMerid (FZq (perCoord x))
  let zη₁ : CProf := fun x => lmToCMerid (FZη (perCoord x))
  have hz₁_sm : StronglyMeasurable z₁ :=
    continuous_lmToCMerid.comp_stronglyMeasurable (hFZ_sm.comp_measurable hper_meas)
  have hzq₁_sm : StronglyMeasurable zq₁ :=
    continuous_lmToCMerid.comp_stronglyMeasurable (hFZq_sm.comp_measurable hper_meas)
  have hzη₁_sm : StronglyMeasurable zη₁ :=
    continuous_lmToCMerid.comp_stronglyMeasurable (hFZη_sm.comp_measurable hper_meas)
  have hper_all : ∀ x : Coord,
      z₁ (qShift p.c x) = z₁ x ∧ zq₁ (qShift p.c x) = zq₁ x ∧ zη₁ (qShift p.c x) = zη₁ x :=
    fun x => ⟨by dsimp [z₁]; rw [hper_qShift],
      by dsimp [zq₁]; rw [hper_qShift],
      by dsimp [zη₁]; rw [hper_qShift]⟩
  have hz₁_per : QPeriodic p.c z₁ :=
    QPerHalf.of_ae (Eventually.of_forall fun x => (hper_all x).1)
  have hzq₁_per : QPeriodic p.c zq₁ :=
    QPerHalf.of_ae (Eventually.of_forall fun x => (hper_all x).2.1)
  have hzη₁_per : QPeriodic p.c zη₁ :=
    QPerHalf.of_ae (Eventually.of_forall fun x => (hper_all x).2.2)
  -- Slice a.e. identification on `B0579.cell p.c` for EVERY `s ∈ Ioc 0 T`
  have hslice_cell : ∀ (F : Coord → EuclideanSpace ℝ (Fin 4)) (X : ℝ → LMH p.c),
      (∀ s ∈ Ioc 0 T, (fun y => F (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] X s) →
      ∀ s ∈ Ioc 0 T,
        (fun y => lmToCMerid (F (perCoord (s, y)))) =ᵐ[volume.restrict (B0579.cell p.c)]
          fun y => lmToCMerid ((X s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) y) := by
    intro F X hFX s hs
    have hcell_eq : ∀ᵐ y ∂(volume.restrict (B0579.cell p.c)), perCoord (s, y) = (s, y) := by
      rw [ae_restrict_iff' (B0579.measurableSet_cell p.c)]
      exact Eventually.of_forall fun y hy => by dsimp [perCoord]; rw [lmPer_of_mem hc hy]
    filter_upwards [hcell_eq, hFX s hs] with y hpy hy
    rw [hpy, hy]
  have hz₁_cell : ∀ s ∈ Ioc 0 T,
      (fun y => z₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun y => lmToCMerid ((Z_lim s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) y) :=
    hslice_cell FZ Z_lim hFZ_rep
  have hzq₁_cell : ∀ s ∈ Ioc 0 T,
      (fun y => zq₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun y => lmToCMerid ((Zq_lim s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) y) :=
    hslice_cell FZq Zq_lim hFZq_rep
  have hzη₁_cell : ∀ s ∈ Ioc 0 T,
      (fun y => zη₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun y => lmToCMerid ((Zη_lim s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) y) :=
    hslice_cell FZη Zη_lim hFZη_rep
  -- `MemLp` and `cprofToLMH` identification on all `Ioc 0 T`
  have hmem_of_cell : ∀ (w : CProf) (X : ℝ → LMH p.c), StronglyMeasurable w →
      (∀ s ∈ Ioc 0 T, (fun y => w (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun y => lmToCMerid ((X s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) y)) →
      (∀ s ∈ Ioc 0 T, MemLp (fun y => w (s, y)) 2 (volume.restrict (B0579.cell p.c))) ∧
      (∀ s ∈ Ioc 0 T, cprofToLMH p.c w s = X s) := by
    intro w X hw_sm hcell
    have hmem : ∀ s ∈ Ioc 0 T, MemLp (fun y => w (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
      fun s hs => ⟨(hw_sm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
        by rw [show eLpNorm (fun y => w (s, y)) 2 (volume.restrict (B0579.cell p.c)) =
            cylSliceL2 p.c (fun y => w (s, y)) from rfl,
          cylSliceL2_eq_ofReal_norm (hcell s hs)]; exact ENNReal.ofReal_lt_top⟩
    refine ⟨hmem, fun s hs => Lp.ext_iff.2 ?_⟩
    filter_upwards [cprofToLMH_ae_of_memLp (hmem s hs), hcell s hs] with y hy1 hy2
    rw [hy1, hy2, cmeridToLM_lmToCMerid]
  obtain ⟨hz₁_mem, hz₁_path⟩ := hmem_of_cell z₁ Z_lim hz₁_sm hz₁_cell
  obtain ⟨hzq₁_mem, hzq₁_path⟩ := hmem_of_cell zq₁ Zq_lim hzq₁_sm hzq₁_cell
  obtain ⟨hzη₁_mem, hzη₁_path⟩ := hmem_of_cell zη₁ Zη_lim hzη₁_sm hzη₁_cell
  -- Good slices and `volume`-a.e. identification with `(z₀, zq₀, zη₀)` and `(z_eb, zq_eb, zη_eb)`
  have hb_sm : StronglyMeasurable (bCut p T z₀ zq₀ zη₀) :=
    stronglyMeasurable_bCut p T hz₀.sm_z hz₀.sm_zq hz₀.sm_zη
  have hgood := ae_earlyGoodSlice hM hC_tr hg hg_int hz₀ hb_sm hb_le hbdd₀
  have hcell_z₀ : ∀ᵐ s ∂volume, s ∈ Ioo 0 T →
      (fun y => z₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => z₀ (s, y)) ∧
      (fun y => zq₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zq₀ (s, y)) ∧
      (fun y => zη₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zη₀ (s, y)) := by
    filter_upwards [hgood, hae_lim] with s hs hlim hmem
    have hgs := hs hmem
    obtain ⟨ez, ezq, ezη⟩ := hlim hmem
    have hs_oc : s ∈ Ioc 0 T := Ioo_subset_Ioc_self hmem
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hz₁_cell s hs_oc, cprofToLMH_ae_of_memLp hgs.memL2_z] with y hy1 hy2
      rw [hy1, ez, hy2, lmToCMerid_cmeridToLM]
    · filter_upwards [hzq₁_cell s hs_oc, cprofToLMH_ae_of_memLp hgs.memL2_zq] with y hy1 hy2
      rw [hy1, ezq, hy2, lmToCMerid_cmeridToLM]
    · filter_upwards [hzη₁_cell s hs_oc, cprofToLMH_ae_of_memLp hgs.memL2_zη] with y hy1 hy2
      rw [hy1, ezη, hy2, lmToCMerid_cmeridToLM]
  have hae_z₀ : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → z₁ x = z₀ x :=
    ContBodySourceAux.ae_vol_eq_of_ae_cell_periodic hc hz₁_sm hz₀.sm_z hz₁_per hz₀.per_z
      (hcell_z₀.mono fun s hs hm => (hs hm).1)
  have hae_zq₀ : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → zq₁ x = zq₀ x :=
    ContBodySourceAux.ae_vol_eq_of_ae_cell_periodic hc hzq₁_sm hz₀.sm_zq hzq₁_per hz₀.per_zq
      (hcell_z₀.mono fun s hs hm => (hs hm).2.1)
  have hae_zη₀ : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T → zη₁ x = zη₀ x :=
    ContBodySourceAux.ae_vol_eq_of_ae_cell_periodic hc hzη₁_sm hz₀.sm_zη hzη₁_per hz₀.per_zη
      (hcell_z₀.mono fun s hs hm => (hs hm).2.2)
  have hae_z₁_eb : ∀ᵐ x : Coord, x.1 ∈ Ioo 0 T →
      z₁ x = z_eb x ∧ zq₁ x = zq_eb x ∧ zη₁ x = zη_eb x := by
    filter_upwards [hae_z₀, hae_zq₀, hae_zη₀, hae_eb] with x e1 e2 e3 heb_x hx
    exact ⟨(e1 hx).trans (heb_x hx.1).1,
      (e2 hx).trans (heb_x hx.1).2.1,
      (e3 hx).trans (heb_x hx.1).2.2⟩
  -- Continuity in `cylSliceH1` on `Ioc 0 T`
  have hdiff_l2 : ∀ (w : CProf) (X : ℝ → LMH p.c),
      (∀ s ∈ Ioc 0 T, (fun y => w (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun y => lmToCMerid ((X s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) y)) →
      ∀ {s s' : ℝ}, s ∈ Ioc 0 T → s' ∈ Ioc 0 T →
        cylSliceL2 p.c (fun y => w (s', y) - w (s, y)) = ENNReal.ofReal ‖X s' - X s‖ := by
    intro w X hcell s s' hs hs'
    refine cylSliceL2_eq_ofReal_norm ?_
    filter_upwards [hcell s' hs', hcell s hs, Lp.coeFn_sub (X s') (X s)] with y hy' hy hsub
    rw [hy', hy, hsub, Pi.sub_apply, lmToCMerid_sub]
  have hcont_h1 : ∀ s ∈ Ioc 0 T,
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₁ (s', y) - z₁ (s, y))
        (fun y => zq₁ (s', y) - zq₁ (s, y))
        (fun y => zη₁ (s', y) - zη₁ (s, y))) (𝓝[Ioc 0 T] s) (𝓝 0) := by
    intro s hs
    have ht_part : ∀ (X : ℝ → LMH p.c), ContinuousOn X (Ioc 0 T) →
        Tendsto (fun s' => ENNReal.ofReal ‖X s' - X s‖) (𝓝[Ioc 0 T] s) (𝓝 0) :=
      fun X hXc => by
        have hn := tendsto_iff_norm_sub_tendsto_zero.1 (hXc s hs)
        have hc0 : Tendsto (fun s' => ENNReal.ofReal ‖X s' - X s‖) (𝓝[Ioc 0 T] s)
            (𝓝 (ENNReal.ofReal 0)) :=
          (ENNReal.continuous_ofReal.tendsto 0).comp hn
        rwa [ENNReal.ofReal_zero] at hc0
    have hsum : Tendsto (fun s' =>
        ENNReal.ofReal ‖Z_lim s' - Z_lim s‖ +
          ENNReal.ofReal ‖Zq_lim s' - Zq_lim s‖ +
          ENNReal.ofReal ‖Zη_lim s' - Zη_lim s‖) (𝓝[Ioc 0 T] s) (𝓝 0) := by
      have h0 := ((ht_part Z_lim hZ_cont).add (ht_part Zq_lim hZq_cont)).add
        (ht_part Zη_lim hZη_cont)
      rwa [add_zero, add_zero] at h0
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    simp only [cylSliceH1, hdiff_l2 z₁ Z_lim hz₁_cell hs hs',
      hdiff_l2 zq₁ Zq_lim hzq₁_cell hs hs',
      hdiff_l2 zη₁ Zη_lim hzη₁_cell hs hs']
  -- Sequence `sn ∈ Ioo 0 T` of good slices converging to `T` (and general `s ∈ Ioc 0 T` bound)
  have hslice_bound_all : ∀ s ∈ Ioc 0 T,
      sliceH1Norm p.c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (3 * M) := by
    intro s hs
    have hnorm_le : ∀ (X : ℝ → LMH p.c), ContinuousOn X (Ioc 0 T) →
        (∀ᵐ r ∂volume, r ∈ Ioo 0 T → ‖X r‖ ≤ M) → ‖X s‖ ≤ M := by
      intro X hXc hX_ae
      by_contra hgt
      push Not at hgt
      set ε := (‖X s‖ - M) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hXc s hs) ε hε
      set a₀ := max 0 (s - δ)
      have ha₀_lt : a₀ < s := max_lt hs.1 (by linarith)
      have hV_pos : 0 < volume (Ioo a₀ s) :=
        isOpen_Ioo.measure_pos volume ⟨(a₀ + s) / 2, by linarith, by linarith⟩
      have hN0 : volume {r : ℝ | ¬(r ∈ Ioo 0 T → ‖X r‖ ≤ M)} = 0 := ae_iff.1 hX_ae
      obtain ⟨r, hr_mem, hr_ok⟩ : ∃ r ∈ Ioo a₀ s, r ∈ Ioo 0 T → ‖X r‖ ≤ M := by
        by_contra hcon
        have hsub : Ioo a₀ s ⊆ {r : ℝ | ¬(r ∈ Ioo 0 T → ‖X r‖ ≤ M)} :=
          fun r hr hh => hcon ⟨r, hr, hh⟩
        exact hV_pos.ne' (measure_mono_null hsub hN0)
      have hr_oo : r ∈ Ioo 0 T := ⟨(le_max_left 0 (s - δ)).trans_lt hr_mem.1, hr_mem.2.trans_le hs.2⟩
      have hr_oc : r ∈ Ioc 0 T := Ioo_subset_Ioc_self hr_oo
      have hr_dist : dist r s < δ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [le_max_right 0 (s - δ), hr_mem.1], by linarith [hr_mem.2]⟩
      have hd_X : ‖X r - X s‖ < ε := by simpa [dist_eq_norm] using hball hr_oc hr_dist
      have htri : ‖X s‖ - ‖X r‖ ≤ ‖X r - X s‖ := by
        rw [norm_sub_rev]; exact norm_sub_norm_le _ _
      have hrM := hr_ok hr_oo
      dsimp [ε] at hd_X
      linarith
    have hZ_M : ‖Z_lim s‖ ≤ M := hnorm_le Z_lim hZ_cont (by
      filter_upwards [hgood, hae_lim] with r hr hl hm
      rw [(hl hm).1]; exact (hr hm).norm_Z0_le hM)
    have hZq_M : ‖Zq_lim s‖ ≤ M := hnorm_le Zq_lim hZq_cont (by
      filter_upwards [hgood, hae_lim] with r hr hl hm
      rw [(hl hm).2.1]; exact (hr hm).norm_Zq0_le hM)
    have hZη_M : ‖Zη_lim s‖ ≤ M := hnorm_le Zη_lim hZη_cont (by
      filter_upwards [hgood, hae_lim] with r hr hl hm
      rw [(hl hm).2.2]; exact (hr hm).norm_Zη0_le hM)
    unfold sliceH1Norm
    change cylSliceL2 p.c (fun y => z₁ (s, y)) + cylSliceL2 p.c (fun y => zq₁ (s, y)) +
        cylSliceL2 p.c (fun y => zη₁ (s, y)) ≤ ENNReal.ofReal (3 * M)
    rw [cylSliceL2_eq_ofReal_norm (hz₁_cell s hs),
      cylSliceL2_eq_ofReal_norm (hzq₁_cell s hs),
      cylSliceL2_eq_ofReal_norm (hzη₁_cell s hs)]
    calc ENNReal.ofReal ‖Z_lim s‖ + ENNReal.ofReal ‖Zq_lim s‖ + ENNReal.ofReal ‖Zη_lim s‖
        ≤ ENNReal.ofReal M + ENNReal.ofReal M + ENNReal.ofReal M :=
          add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hZ_M) (ENNReal.ofReal_le_ofReal hZq_M))
            (ENNReal.ofReal_le_ofReal hZη_M)
      _ = ENNReal.ofReal (3 * M) := by
          rw [← ENNReal.ofReal_add hM hM, ← ENNReal.ofReal_add (add_nonneg hM hM) hM]
          ring_nf
  -- Horizon slice `IsCylH1Slice` at `s = T`
  have hT_oc : T ∈ Ioc 0 T := ⟨hT, le_rfl⟩
  have hex_sn : ∀ n : ℕ, ∃ s ∈ Ioo (max 0 (T - ((n : ℝ) + 1)⁻¹)) T,
      EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ (bCut p T z₀ zq₀ zη₀) M C_tr s ∧
      ((fun y => z₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => z₀ (s, y)) ∧
        (fun y => zq₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zq₀ (s, y)) ∧
        (fun y => zη₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zη₀ (s, y))) := by
    intro n
    set an := max 0 (T - ((n : ℝ) + 1)⁻¹)
    have han_lt : an < T := max_lt hT (sub_lt_self T (inv_pos.2 (by positivity)))
    have hV_pos : 0 < volume (Ioo an T) :=
      isOpen_Ioo.measure_pos volume ⟨(an + T) / 2, by linarith, by linarith⟩
    have hcomb_ae := hgood.and hcell_z₀
    have hN0 : volume {s : ℝ | ¬((s ∈ Ioo 0 T →
          EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ (bCut p T z₀ zq₀ zη₀) M C_tr s) ∧
        (s ∈ Ioo 0 T →
          (fun y => z₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => z₀ (s, y)) ∧
          (fun y => zq₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zq₀ (s, y)) ∧
          (fun y => zη₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zη₀ (s, y))))} = 0 :=
      ae_iff.1 hcomb_ae
    obtain ⟨s, hs_an, hs_good⟩ : ∃ s ∈ Ioo an T,
        (s ∈ Ioo 0 T → EarlyGoodSlice p g gq gη z₀ zq₀ zη₀ (bCut p T z₀ zq₀ zη₀) M C_tr s) ∧
        (s ∈ Ioo 0 T →
          (fun y => z₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => z₀ (s, y)) ∧
          (fun y => zq₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zq₀ (s, y)) ∧
          (fun y => zη₁ (s, y)) =ᵐ[volume.restrict (B0579.cell p.c)] (fun y => zη₀ (s, y))) := by
      by_contra hcon
      have hsub : Ioo an T ⊆ _ := fun s hs hh => hcon ⟨s, hs, hh⟩
      exact hV_pos.ne' (measure_mono_null hsub hN0)
    have hs_oo : s ∈ Ioo 0 T := ⟨(le_max_left 0 _).trans_lt hs_an.1, hs_an.2⟩
    exact ⟨s, hs_an, hs_good.1 hs_oo, hs_good.2 hs_oo⟩
  choose sn hsn_mem hsn_good hsn_ae using hex_sn
  have hsn_oc : ∀ n, sn n ∈ Ioc 0 T := fun n =>
    ⟨(le_max_left 0 _).trans_lt (hsn_mem n).1, (hsn_mem n).2.le⟩
  have hsn_tend_nhds : Tendsto sn atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hinv
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos (sub_pos.2 (hsn_mem n).2)]
    have h1 : T - ((n : ℝ) + 1)⁻¹ < sn n :=
      (le_max_right 0 (T - ((n : ℝ) + 1)⁻¹)).trans_lt (hsn_mem n).1
    linarith
  have hsn_tend_within : Tendsto sn atTop (𝓝[Ioc 0 T] T) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsn_tend_nhds
      (Eventually.of_forall hsn_oc)
  have hZ_sn : Tendsto (fun n => Z_lim (sn n)) atTop (𝓝 (Z_lim T)) :=
    (hZ_cont T hT_oc).tendsto.comp hsn_tend_within
  have hZq_sn : Tendsto (fun n => Zq_lim (sn n)) atTop (𝓝 (Zq_lim T)) :=
    (hZq_cont T hT_oc).tendsto.comp hsn_tend_within
  have hZη_sn : Tendsto (fun n => Zη_lim (sn n)) atTop (𝓝 (Zη_lim T)) :=
    (hZη_cont T hT_oc).tendsto.comp hsn_tend_within
  have hslice_T : IsCylH1Slice p.c
      (fun y => z₁ (T, y)) (fun y => zq₁ (T, y)) (fun y => zη₁ (T, y)) := by
    have hint_mul_test : ∀ {w : CProf},
        MemLp (fun y => w (T, y)) 2 (volume.restrict (B0579.cell p.c)) →
        ∀ (k : Fin 2) {χ : B0579.Plane → ℝ}, B0579.IsCylTest p.c χ →
        IntegrableOn (fun y => w (T, y) k * (χ y : ℂ)) (B0579.cell p.c) volume := by
      intro w hw k χ hχ
      exact ((EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).comp_memLp' hw).integrable_mul
        (Complex.ofRealCLM.comp_memLp' (B0583.memLp_cellVol_of_isCylTest hχ))
    refine {
      sm_u := hz₁_sm.comp_measurable (measurable_const.prodMk measurable_id)
      sm_uq := hzq₁_sm.comp_measurable (measurable_const.prodMk measurable_id)
      sm_uη := hzη₁_sm.comp_measurable (measurable_const.prodMk measurable_id)
      weak_q := fun k => by
        refine ⟨fun ψ hψ => ⟨hint_mul_test (hz₁_mem T hT_oc) k (hψ.pd 0),
          hint_mul_test (hzq₁_mem T hT_oc) k hψ⟩, fun ψ hψ => ?_⟩
        have hlhs := tendsto_cell_comp_integral hz₁_path hz₁_mem hsn_oc hT_oc hZ_sn k
          (B0583.memLp_cellVol_of_isCylTest (hψ.pd 0))
        have hrhs := (tendsto_cell_comp_integral hzq₁_path hzq₁_mem hsn_oc hT_oc hZq_sn k
          (B0583.memLp_cellVol_of_isCylTest hψ)).neg
        refine tendsto_nhds_unique hlhs (hrhs.congr fun n => ?_)
        have hw_n := hasWeakCellDerivC_congr_ae
          (v := fun y => z₁ (sn n, y) k) (h := fun y => zq₁ (sn n, y) k)
          ((hsn_ae n).1.symm.mono fun y hy => congrArg (fun u => u k) hy)
          ((hsn_ae n).2.1.symm.mono fun y hy => congrArg (fun u => u k) hy)
          ((hsn_good n).weak_z_q k)
        exact (hw_n.2 ψ hψ).symm
      weak_eta := fun k => by
        refine ⟨fun ψ hψ => ⟨hint_mul_test (hz₁_mem T hT_oc) k (hψ.pd 1),
          hint_mul_test (hzη₁_mem T hT_oc) k hψ⟩, fun ψ hψ => ?_⟩
        have hlhs := tendsto_cell_comp_integral hz₁_path hz₁_mem hsn_oc hT_oc hZ_sn k
          (B0583.memLp_cellVol_of_isCylTest (hψ.pd 1))
        have hrhs := (tendsto_cell_comp_integral hzη₁_path hzη₁_mem hsn_oc hT_oc hZη_sn k
          (B0583.memLp_cellVol_of_isCylTest hψ)).neg
        refine tendsto_nhds_unique hlhs (hrhs.congr fun n => ?_)
        have hw_n := hasWeakCellDerivC_congr_ae
          (v := fun y => z₁ (sn n, y) k) (h := fun y => zη₁ (sn n, y) k)
          ((hsn_ae n).1.symm.mono fun y hy => congrArg (fun u => u k) hy)
          ((hsn_ae n).2.2.symm.mono fun y hy => congrArg (fun u => u k) hy)
          ((hsn_good n).weak_z_eta k)
        exact (hw_n.2 ψ hψ).symm
      solenoidal := fun ψ hψ => by
        have i0 := hint_mul_test (hz₁_mem T hT_oc) 0 (hψ.pd 0)
        have i1 := hint_mul_test (hz₁_mem T hT_oc) 1 (hψ.pd 1)
        refine ⟨i0.add i1, ?_⟩
        rw [integral_add i0 i1]
        have ht0 := tendsto_cell_comp_integral hz₁_path hz₁_mem hsn_oc hT_oc hZ_sn 0
          (B0583.memLp_cellVol_of_isCylTest (hψ.pd 0))
        have ht1 := tendsto_cell_comp_integral hz₁_path hz₁_mem hsn_oc hT_oc hZ_sn 1
          (B0583.memLp_cellVol_of_isCylTest (hψ.pd 1))
        have htsum : Tendsto (fun n =>
            (∫ y in B0579.cell p.c, z₁ (sn n, y) 0 * (B0579.pd 0 ψ y : ℂ)) +
              (∫ y in B0579.cell p.c, z₁ (sn n, y) 1 * (B0579.pd 1 ψ y : ℂ)))
            atTop (𝓝 ((∫ y in B0579.cell p.c, z₁ (T, y) 0 * (B0579.pd 0 ψ y : ℂ)) +
              (∫ y in B0579.cell p.c, z₁ (T, y) 1 * (B0579.pd 1 ψ y : ℂ)))) :=
          ht0.add ht1
        have hzero : ∀ n : ℕ,
            (∫ y in B0579.cell p.c, z₁ (sn n, y) 0 * (B0579.pd 0 ψ y : ℂ)) +
              (∫ y in B0579.cell p.c, z₁ (sn n, y) 1 * (B0579.pd 1 ψ y : ℂ)) = 0 := fun n => by
          have in0 : IntegrableOn (fun y => z₁ (sn n, y) 0 * (B0579.pd 0 ψ y : ℂ))
              (B0579.cell p.c) volume :=
            ((EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ).comp_memLp'
              (hz₁_mem (sn n) (hsn_oc n))).integrable_mul
              (Complex.ofRealCLM.comp_memLp' (B0583.memLp_cellVol_of_isCylTest (hψ.pd 0)))
          have in1 : IntegrableOn (fun y => z₁ (sn n, y) 1 * (B0579.pd 1 ψ y : ℂ))
              (B0579.cell p.c) volume :=
            ((EuclideanSpace.proj (1 : Fin 2) : CMerid →L[ℂ] ℂ).comp_memLp'
              (hz₁_mem (sn n) (hsn_oc n))).integrable_mul
              (Complex.ofRealCLM.comp_memLp' (B0583.memLp_cellVol_of_isCylTest (hψ.pd 1)))
          rw [← integral_add in0 in1, ← ((hsn_good n).sol_z ψ hψ).2]
          refine integral_congr_ae ?_
          filter_upwards [(hsn_ae n).1] with y hy
          simp only [hy]
        exact tendsto_nhds_unique htsum (tendsto_const_nhds.congr fun n => (hzero n).symm)
      memL2_u := hz₁_mem T hT_oc
      memL2_uq := hzq₁_mem T hT_oc
      memL2_uη := hzη₁_mem T hT_oc
    }
  -- Early weak PDE transfer on `Ioo 0 T ×ˢ univ` from `(z₀, zq₀, zη₀)` to `(z₁, zq₁, zη₁)`
  have htsupp_cpd : ∀ {φ : Coord → ℝ}, tsupport φ ⊆ Ioo 0 T ×ˢ univ →
      ∀ (d d' : Fin 3) {x : Coord}, x.1 ∉ Ioo 0 T →
        cpd d φ x = 0 ∧ cpd d' (cpd d φ) x = 0 := by
    intro φ hsupp d d' x hx
    have hnot : x ∉ tsupport φ := fun hm => hx (hsupp hm).1
    have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hnot
    have h1 : cpd d φ x = 0 := by simp [cpd, hev.fderiv_eq]
    obtain ⟨U, hU0, hU_open, hxU⟩ := eventually_nhds_iff.1 hev
    have hev_d : cpd d φ =ᶠ[𝓝 x] 0 := by
      refine Filter.eventually_of_mem (hU_open.mem_nhds hxU) fun y hyU => ?_
      have hy : φ =ᶠ[𝓝 y] 0 := Filter.eventually_of_mem (hU_open.mem_nhds hyU) hU0
      simp [cpd, hy.fderiv_eq]
    exact ⟨h1, by simp [cpd, hev_d.fderiv_eq]⟩
  refine ⟨z₁, zq₁, zη₁, hz₁_sm, hzq₁_sm, hzη₁_sm, hper_all, hz₁_per, hzq₁_per, hzη₁_per,
    hae_z₁_eb, hcont_h1, hslice_T, hslice_bound_all, ?_, ?_, ?_, ?_⟩
  · -- `weak_q` on `Ioo 0 T ×ˢ univ`
    intro i φ hφ hsupp
    have h1 := (hz₀.weak_q i).1 φ hφ
    have h2 := (hz₀.weak_q i).2 φ hφ
    have hae_u : (fun x => z₁ x i * (coordTranspose vQ0 dZero φ x : ℂ)) =ᵐ[volume]
        fun x => z₀ x i * (coordTranspose vQ0 dZero φ x : ℂ) := by
      filter_upwards [hae_z₀] with x hx
      by_cases hm : x.1 ∈ Ioo 0 T
      · simp [hx hm]
      · rw [show vQ0 = ![vQ0, vEta] 0 from rfl, TailPeriodizeAux.coordTranspose_vQ0_vEta 0 φ x,
          show Fin.succ (0 : Fin 2) = (1 : Fin 3) from rfl, (htsupp_cpd hsupp 1 1 hm).1]
        simp
    have hae_g : (fun x => zq₁ x i * (φ x : ℂ)) =ᵐ[volume]
        fun x => zq₀ x i * (φ x : ℂ) := by
      filter_upwards [hae_zq₀] with x hx
      by_cases hm : x.1 ∈ Ioo 0 T
      · simp [hx hm]
      · simp [image_eq_zero_of_notMem_tsupport (fun h => hm (hsupp h).1)]
    exact ⟨h1.1.congr hae_u.symm, h1.2.congr hae_g.symm,
      (integral_congr_ae hae_g).trans (h2.trans (integral_congr_ae hae_u.symm))⟩
  · -- `weak_eta` on `Ioo 0 T ×ˢ univ`
    intro i φ hφ hsupp
    have h1 := (hz₀.weak_eta i).1 φ hφ
    have h2 := (hz₀.weak_eta i).2 φ hφ
    have hae_u : (fun x => z₁ x i * (coordTranspose vEta dZero φ x : ℂ)) =ᵐ[volume]
        fun x => z₀ x i * (coordTranspose vEta dZero φ x : ℂ) := by
      filter_upwards [hae_z₀] with x hx
      by_cases hm : x.1 ∈ Ioo 0 T
      · simp [hx hm]
      · rw [show vEta = ![vQ0, vEta] 1 from rfl, TailPeriodizeAux.coordTranspose_vQ0_vEta 1 φ x,
          show Fin.succ (1 : Fin 2) = (2 : Fin 3) from rfl, (htsupp_cpd hsupp 2 2 hm).1]
        simp
    have hae_g : (fun x => zη₁ x i * (φ x : ℂ)) =ᵐ[volume]
        fun x => zη₀ x i * (φ x : ℂ) := by
      filter_upwards [hae_zη₀] with x hx
      by_cases hm : x.1 ∈ Ioo 0 T
      · simp [hx hm]
      · simp [image_eq_zero_of_notMem_tsupport (fun h => hm (hsupp h).1)]
    exact ⟨h1.1.congr hae_u.symm, h1.2.congr hae_g.symm,
      (integral_congr_ae hae_g).trans (h2.trans (integral_congr_ae hae_u.symm))⟩
  · -- `solenoidal` on `Ioo 0 T ×ˢ univ`
    intro φ hφ hsupp
    obtain ⟨hI, h0⟩ := hz₀.solenoidal φ hφ hsupp
    have hae_sol : (fun x => z₁ x 0 * (cpd 1 φ x : ℂ) + z₁ x 1 * (cpd 2 φ x : ℂ)) =ᵐ[volume]
        fun x => z₀ x 0 * (cpd 1 φ x : ℂ) + z₀ x 1 * (cpd 2 φ x : ℂ) := by
      filter_upwards [hae_z₀] with x hx
      by_cases hm : x.1 ∈ Ioo 0 T
      · simp [hx hm]
      · simp [(htsupp_cpd hsupp 1 1 hm).1, (htsupp_cpd hsupp 2 2 hm).1]
    exact ⟨hI.congr hae_sol.symm, (integral_congr_ae hae_sol).trans h0⟩
  · -- `equation` on `Ioo 0 T ×ˢ univ`
    intro Ψ hΨ hsupp
    obtain ⟨hI1, hI2, hI3, heq⟩ := hz₀.equation Ψ hΨ hsupp
    have hae1 : (fun x => ∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i) =ᵐ[volume]
        fun x => ∑ i : Fin 2, z₀ x i * meridTranspose p.ν Ψ x i := by
      filter_upwards [hae_z₀] with x hx
      by_cases hm : x.1 ∈ Ioo 0 T
      · simp [hx hm]
      · have hm0 : ∀ i : Fin 2, meridTranspose p.ν Ψ x i = 0 := fun i => by
          have hs0 := (htsupp_cpd (hsupp i) 0 0 hm).1
          have hq2 := (htsupp_cpd (hsupp i) 1 1 hm).2
          have hη2 := (htsupp_cpd (hsupp i) 2 2 hm).2
          simp [meridTranspose, hs0, hq2, hη2]
        simp [hm0]
    have hae2 : cdot (flatBv p.train z₁ zq₁ zη₁) Ψ =ᵐ[volume]
        cdot (flatBv p.train z₀ zq₀ zη₀) Ψ := by
      filter_upwards [hae_z₀, hae_zq₀, hae_zη₀] with x e1 e2 e3
      by_cases hm : x.1 ∈ Ioo 0 T
      · simp [cdot, flatBv, e1 hm, e2 hm, e3 hm]
      · have h0 : ∀ i : Fin 2, Ψ x i = 0 :=
          fun i => image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i)
            (fun h => hm (hsupp i h).1)
        simp [cdot, h0]
    have hae12 : (fun x => ∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i +
        cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x) =ᵐ[volume]
        fun x => ∑ i : Fin 2, z₀ x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z₀ zq₀ zη₀) Ψ x := by
      filter_upwards [hae1, hae2] with x e1 e2; rw [e1, e2]
    refine ⟨hI1.congr hae1.symm, hI2.congr hae2.symm, hI3, ?_⟩
    rw [integral_congr_ae hae12]
    exact heq

end UnforcedLeray.Short.IIb.HorizonGluingAux

end
