import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.Needed
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing2.Scale
import UnforcedLeray.Short.PartIIIa.Clock.ZeroCirc
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjDtDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjIBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.WeakFromSmooth
import UnforcedLeray.Lib.Sobolev.Cylinder

/-!
# Leaf (`PartIII-a:T21/c3/3/1/1/2/2/3/a`): `LinFreeAdjPairing`

Source of record: `the November 2 reference manuscript` (SP), lines 2937–2958,
3060–3075.

Proves `LinFreeAdjPairing`: for a weak linearised flow `(w, u)` with zero-circulation initial
datum and a regular reverse-time free adjoint flow `φ` on `[t₁, s]`, the physical cell pairing
changes only by the interaction term `-(u · ∇E) φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2WeakEqNeeded

namespace LinFreeAux

/-! ### 1. Biot-Savart `L²` Lipschitz bound for any `c > 0` -/

private theorem bsBound_pos {m c : ℝ} (hm : 8 < m) (hc : 0 < c) :
    ∃ C : ℝ, ∀ Ω : ℝ × ℝ → ℂ, MemLp Ω 2 (B0579.cellMeasure c m) →
      HasZeroCirculation c Ω → ∀ U : ℝ × ℝ → Fin 2 → ℂ, IsBiotSavart c Ω U → ∀ j : Fin 2,
        eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell c)) ≤
          ENNReal.ofReal C * xNorm c m Ω := by
  set a : ℝ := c ^ 2
  have ha : 0 < a := by positivity
  have hsa : Real.sqrt a = c := Real.sqrt_sq hc.le
  have hcl : cellLen c a = 1 := by
    unfold cellLen
    rw [hsa, div_self hc.ne']
  set M : ℝ := max 1 a⁻¹
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨C₁, hC₁⟩ := ladBSBound m hm
  set K : ℝ := a⁻¹ * max C₁ 0 * (a ^ ((1 : ℝ) / 2) * M ^ (m / 2) * a)
  refine ⟨K, fun Ω hΩ hZ U hU j => ?_⟩
  have hBS := PartIIIb.Concrete.isBiotSavart_jscaleInv c a hc ha Ω U hU
  rw [hcl] at hBS
  have hmem1 := Leaf2WeakEqFrame.KerBSAux.memLp_JscaleInv_pos (c := c) (by linarith : (0 : ℝ) ≤ m) ha hΩ
  rw [hcl] at hmem1
  have hint1 : IntegrableOn (JscaleInv a Ω) (B0579.cell 1) :=
    integrableOn_cell_of_X (by linarith) hmem1
  have hcv := cv_cell (c := c) ha Ω
  rw [hcl, hZ.2] at hcv
  have hX : ∫ y in B0579.cell 1, Ω (Real.sqrt a * y.1, Real.sqrt a * y.2) = 0 := by
    rw [Complex.real_smul] at hcv
    rcases mul_eq_zero.1 hcv with h | h
    · exact absurd h (by exact_mod_cast ha.ne')
    · exact h
  have hZ1 : HasZeroCirculation 1 (JscaleInv a Ω) := by
    refine ⟨hint1, ?_⟩
    unfold JscaleInv
    rw [integral_const_mul, hX, mul_zero]
  have hU1 := hC₁ 1 le_rfl (JscaleInv a Ω) hmem1 hZ1 _ hBS j
  have hUscale := eLpNorm_component_scale (c := c) ha (fun x => U x j)
  rw [hcl] at hUscale
  -- bound `xNorm 1 m (JscaleInv a Ω)` by `xNorm c m Ω`
  set G : ℝ × ℝ → ℂ := fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * Ω x
  have hs2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have ha_split : a ^ 2 = a ^ ((1 : ℝ) / 2) * a ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add ha, show (1 : ℝ) / 2 + 3 / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpt : ∀ y : ℝ × ℝ, ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * JscaleInv a Ω y‖ ≤
      (a ^ ((1 : ℝ) / 2) * M ^ (m / 2)) *
        ‖((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * G (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ := by
    intro y
    have hjb : B0579.jb y ≤ M * B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      have e : B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) = 1 + a * y.1 ^ 2 + a * y.2 ^ 2 := by
        simp only [B0579.jb, mul_pow, hs2]
      rw [e]
      unfold B0579.jb
      have h1 : 1 ≤ M := le_max_left _ _
      have h2 : a⁻¹ ≤ M := le_max_right _ _
      have h3 : 1 ≤ M * a := by
        calc (1 : ℝ) = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
          _ ≤ M * a := by gcongr
      nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hpow : B0579.jb y ^ (m / 2) ≤
        M ^ (m / 2) * B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) ^ (m / 2) := by
      rw [← Real.mul_rpow hM (B0579.jb_pos _).le]
      exact Real.rpow_le_rpow (B0579.jb_pos y).le hjb (by linarith)
    simp only [JscaleInv, G, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos y).le _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2),
      abs_of_nonneg (Real.rpow_nonneg ha.le _),
      abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos _).le _)]
    have hn : 0 ≤ ‖Ω (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ := norm_nonneg _
    have ha2 : 0 ≤ a ^ 2 := by positivity
    calc B0579.jb y ^ (m / 2) * (a ^ 2 * ‖Ω (Real.sqrt a * y.1, Real.sqrt a * y.2)‖)
        ≤ (M ^ (m / 2) * B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) ^ (m / 2)) *
            (a ^ 2 * ‖Ω (Real.sqrt a * y.1, Real.sqrt a * y.2)‖) :=
          mul_le_mul_of_nonneg_right hpow (mul_nonneg ha2 hn)
      _ = (a ^ ((1 : ℝ) / 2) * M ^ (m / 2)) *
            (a ^ ((3 : ℝ) / 2) *
              (B0579.jb (Real.sqrt a * y.1, Real.sqrt a * y.2) ^ (m / 2) *
                ‖Ω (Real.sqrt a * y.1, Real.sqrt a * y.2)‖)) := by
          rw [ha_split]
          ring
  have hx1 : xNorm 1 m (JscaleInv a Ω) ≤
      ENNReal.ofReal (a ^ ((1 : ℝ) / 2) * M ^ (m / 2) * a) * xNorm c m Ω := by
    unfold xNorm
    rw [PairContAux.eLpNorm_cellMeasure_cx 1 m, PairContAux.eLpNorm_cellMeasure_cx c m]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hpt) 2).trans ?_
    have hGs := eLpNorm_component_scale (c := c) ha G
    rw [hcl] at hGs
    rw [hGs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hC1_le : ENNReal.ofReal C₁ ≤ ENNReal.ofReal (max C₁ 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hcomb : ENNReal.ofReal a * eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal (max C₁ 0 * (a ^ ((1 : ℝ) / 2) * M ^ (m / 2) * a)) * xNorm c m Ω := by
    rw [← hUscale]
    refine hU1.trans ((mul_le_mul' hC1_le hx1).trans ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (le_max_right C₁ 0)]
  have hainv : ENNReal.ofReal a⁻¹ * ENNReal.ofReal a = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  calc eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell c))
      = 1 * eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell c)) := (one_mul _).symm
    _ = ENNReal.ofReal a⁻¹ *
          (ENNReal.ofReal a * eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell c))) := by
        rw [← mul_assoc, hainv]
    _ ≤ ENNReal.ofReal a⁻¹ *
          (ENNReal.ofReal (max C₁ 0 * (a ^ ((1 : ℝ) / 2) * M ^ (m / 2) * a)) * xNorm c m Ω) :=
        mul_le_mul' le_rfl hcomb
    _ = ENNReal.ofReal K * xNorm c m Ω := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]
        simp only [K, mul_assoc]

private theorem velLip_pos {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t : ℝ}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hm : 8 < m) (hc : 0 < c) (hf : HasZeroCirculation c f)
    (hw : IsLinearisedFlow ν c m tr t f w u) :
    ∃ C : ℝ, ∀ ρ ρ' : ℝ, t ≤ ρ → t ≤ ρ' → ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j - u ρ' x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal C * xNorm c m (w ρ - w ρ') := by
  obtain ⟨C, hC⟩ := bsBound_pos hm hc
  have hm1 : 1 < m := by linarith
  refine ⟨C, fun ρ ρ' hρ hρ' j => ?_⟩
  have hz := zeroCirculationPreserved ν c m hc hm1 tr t f w u hw hf ρ hρ
  have hz' := zeroCirculationPreserved ν c m hc hm1 tr t f w u hw hf ρ' hρ'
  have hmem := hw.memX ρ hρ
  have hmem' := hw.memX ρ' hρ'
  have hbs := ladBSSub m c (w ρ) (w ρ') (u ρ) (u ρ') hm1 hmem hmem' (hw.biotSavart ρ hρ)
    (hw.biotSavart ρ' hρ')
  have hzd : HasZeroCirculation c (w ρ - w ρ') := by
    refine ⟨hz.1.sub hz'.1, ?_⟩
    have := integral_sub hz.1 hz'.1
    simp only [Pi.sub_apply]
    rw [this, hz.2, hz'.2, sub_zero]
  exact hC (w ρ - w ρ') (hmem.sub hmem') hzd (u ρ - u ρ') hbs j

/-! ### 2. `ladChi = 0` a.e. for a regular free adjoint flow -/

private theorem freeAdj_rate_continuousOn {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (ht : 0 ≤ t)
    (hφ : IsFreeAdjointFlow ν c m tr t s g φ) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ContinuousOn (fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x) (Ioo t s) := by
  have hj := hφ.jointSmooth
  obtain ⟨R, hR⟩ := hψ.band
  have hpdz : ∀ j : Fin 2, ∀ x : ℝ × ℝ, R < |x.2| → B0579.pd j ψ x = 0 := by
    intro j x hx
    show fderiv ℝ ψ x (B0579.dir j) = 0
    exact mpVanishFderiv hR (B0579.dir j) x hx
  have hlapz : ∀ x : ℝ × ℝ, R < |x.2| → UnforcedLeray.Short.IIb.lapP ψ x = 0 := by
    intro x hx
    unfold UnforcedLeray.Short.IIb.lapP
    have h1 : B0579.pd 0 (B0579.pd 0 ψ) x = 0 :=
      mpVanishFderiv (fun y hy => hpdz 0 y hy) (B0579.dir 0) x hx
    have h2 : B0579.pd 1 (B0579.pd 1 ψ) x = 0 :=
      mpVanishFderiv (fun y hy => hpdz 1 y hy) (B0579.dir 1) x hx
    rw [h1, h2, add_zero]
  have hjc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) := hj.continuousOn
  have hvS : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hcoord : ∀ j : Fin 2, Continuous fun v : EuclideanSpace ℝ (Fin 2) => v j := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous
  have hAc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      ν * UnforcedLeray.Short.IIb.lapP ψ p.2 -
        (tr.v p.1 p.2 0 * B0579.pd 0 ψ p.2 + tr.v p.1 p.2 1 * B0579.pd 1 ψ p.2))
      (Ici 0 ×ˢ univ) := by
    have hlapC : Continuous (UnforcedLeray.Short.IIb.lapP ψ) :=
      ((hψ.pd 0).pd 0).continuous.add ((hψ.pd 1).pd 1).continuous
    have hv0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
      (hcoord 0).comp_continuousOn hvS
    have hv1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) (Ici 0 ×ˢ univ) :=
      (hcoord 1).comp_continuousOn hvS
    have hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Short.IIb.lapP ψ p.2)
        (Ici 0 ×ˢ univ) := hlapC.comp_continuousOn continuousOn_snd
    have hD0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd 0 ψ p.2) (Ici 0 ×ˢ univ) :=
      (hψ.pd 0).continuous.comp_continuousOn continuousOn_snd
    have hD1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd 1 ψ p.2) (Ici 0 ×ˢ univ) :=
      (hψ.pd 1).continuous.comp_continuousOn continuousOn_snd
    exact (continuousOn_const.mul hL).sub ((hv0.mul hD0).add (hv1.mul hD1))
  intro ρ hρ
  have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hρ.1 hρ.2)
  have hIcc : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), r ∈ Ioo t s := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hball2 : ∀ r ∈ Metric.ball ρ (ε / 2), r ∈ Icc (ρ - ε / 2) (ρ + ε / 2) := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    constructor <;> linarith [hr.1, hr.2]
  set Kc : Set (ℝ × (ℝ × ℝ)) := Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ
    (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)
  have hKc : IsCompact Kc := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : Kc ⊆ Ico t s ×ˢ univ := fun p hp => ⟨Ioo_subset_Ico_self (hIcc p.1 hp.1), mem_univ _⟩
  have hKsub' : Kc ⊆ Ici 0 ×ˢ univ := fun p hp =>
    ⟨le_trans ht (Ioo_subset_Ico_self (hIcc p.1 hp.1)).1, mem_univ _⟩
  obtain ⟨M1, hM1⟩ := hKc.exists_bound_of_continuousOn (hjc.mono hKsub)
  obtain ⟨M2, hM2⟩ := hKc.exists_bound_of_continuousOn (hAc.mono hKsub')
  set Kx : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hKxc : IsCompact Kx := isCompact_Icc.prod isCompact_Icc
  have hbound_int : Integrable (Kx.indicator fun _ => M1 * M2)
      (volume.restrict (B0579.cell c)) := by
    rw [integrable_indicator_iff hKxc.isClosed.measurableSet]
    exact integrableOn_const (hs := ne_top_of_le_ne_top hKxc.measure_lt_top.ne
      (Measure.restrict_apply_le _ _))
  have hF_meas : ∀ᶠ r in 𝓝 ρ, AEStronglyMeasurable (freeAdjIntegrand tr (φ r) r ψ)
      (volume.restrict (B0579.cell c)) := by
    refine Filter.eventually_of_mem (Ioo_mem_nhds hρ.1 hρ.2) fun r hr => ?_
    have hr0 : 0 ≤ r := le_trans ht (Ioo_subset_Ico_self hr).1
    have hAr : Continuous fun x : ℝ × ℝ => ν * UnforcedLeray.Short.IIb.lapP ψ x -
        (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) :=
      hAc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hr0, mem_univ _⟩)
    have hφr : Continuous fun x => φ r x := (hφ.smooth r (Ioo_subset_Ico_self hr)).continuous
    exact (hφr.mul (Complex.continuous_ofReal.comp hAr)).aestronglyMeasurable
  have h_bound : ∀ᶠ r in 𝓝 ρ, ∀ᵐ a ∂(volume.restrict (B0579.cell c)),
      ‖freeAdjIntegrand tr (φ r) r ψ a‖ ≤ Kx.indicator (fun _ => M1 * M2) a := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds ρ (half_pos hε)) fun r hr => ?_
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (Filter.Eventually.of_forall fun a ha => ?_)
    unfold freeAdjIntegrand
    by_cases haK : a ∈ Kx
    · rw [Set.indicator_of_mem haK]
      have hp : ((r, a) : ℝ × (ℝ × ℝ)) ∈ Kc := ⟨hball2 r hr, haK⟩
      have h1 := hM1 (r, a) hp
      have h2 := hM2 (r, a) hp
      simp only at h1 h2
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
    · rw [Set.indicator_of_notMem haK]
      have hR' : R < |a.2| := by
        by_contra hcon
        exact haK ⟨Ico_subset_Icc_self (Set.mem_prod.1 ha).1, abs_le.1 (le_of_not_gt hcon)⟩
      simp [hlapz a hR', hpdz 0 a hR', hpdz 1 a hR']
  have h_cont : ∀ᵐ a ∂(volume.restrict (B0579.cell c)),
      ContinuousAt (fun r => freeAdjIntegrand tr (φ r) r ψ a) ρ := by
    refine Filter.Eventually.of_forall fun a => ?_
    unfold freeAdjIntegrand
    have h1 : ContinuousAt (fun r : ℝ => φ r a) ρ :=
      (hjc.continuousAt (prod_mem_nhds (Ico_mem_nhds hρ.1 hρ.2) univ_mem)).comp
        (f := fun r : ℝ => ((r, a) : ℝ × (ℝ × ℝ)))
        (continuous_id.prodMk continuous_const).continuousAt
    have h2 : ContinuousAt (fun r : ℝ => ν * UnforcedLeray.Short.IIb.lapP ψ a -
        (tr.v r a 0 * B0579.pd 0 ψ a + tr.v r a 1 * B0579.pd 1 ψ a)) ρ :=
      (hAc.continuousAt (prod_mem_nhds (Ici_mem_nhds hρ0) univ_mem)).comp
        (f := fun r : ℝ => ((r, a) : ℝ × (ℝ × ℝ)))
        (continuous_id.prodMk continuous_const).continuousAt
    exact h1.mul (Complex.continuous_ofReal.continuousAt.comp h2)
  exact (continuousAt_of_dominated hF_meas h_bound hbound_int h_cont).continuousWithinAt

private theorem freeAdj_dt_deriv {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointFlow ν c m tr t s g φ) {ρ : ℝ} (hρ : ρ ∈ Ioo t s)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    HasDerivAt (fun r => ∫ x in B0579.cell c, φ r x * (ψ x : ℂ))
      (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) ρ := by
  have hj := hφ.jointSmooth
  obtain ⟨R, hR⟩ := hψ.band
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hρ.1 hρ.2)
  have hs0nhds : Metric.ball ρ (ε / 2) ∈ 𝓝 ρ := Metric.ball_mem_nhds ρ (half_pos hε)
  have hIcc : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), r ∈ Ioo t s := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hball2 : ∀ r ∈ Metric.ball ρ (ε / 2), r ∈ Icc (ρ - ε / 2) (ρ + ε / 2) := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hJc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) p
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ico t s ×ˢ univ) :=
    (hj.fderivWithin (adjStrip_uniqueDiff t s) (m := ∞) (by simp)).continuousOn.clm_apply
      continuousOn_const
  have hKc : IsCompact (Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) ⊆
      Ico t s ×ˢ univ := fun p hp => ⟨Ioo_subset_Ico_self (hIcc p.1 hp.1), mem_univ _⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hJc.mono hKsub)
  have hLD : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), ∀ x : ℝ × ℝ, x.1 ∈ Icc (-(c / 2)) (c / 2) →
      x.2 ∈ Icc (-R) R → ‖ladDt φ r x‖ ≤ M := by
    intro r hr x hx1 hx2
    rw [ladDt_eq_fderivWithin hj (hIcc r hr) x]
    exact hM (r, x) ⟨hr, hx1, hx2⟩
  have hcellsub : ∀ x : ℝ × ℝ, x ∈ B0579.cell c → x.1 ∈ Icc (-(c / 2)) (c / 2) :=
    fun x hx => Ico_subset_Icc_self (Set.mem_prod.1 hx).1
  have hcont : ∀ r ∈ Ioo t s, Continuous (fun x : ℝ × ℝ => φ r x * ((ψ x : ℝ) : ℂ)) := fun r hr =>
    (hφ.smooth r (Ioo_subset_Ico_self hr)).continuous.mul
      (Complex.continuous_ofReal.comp hψ.continuous)
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hvan : UnforcedLeray.Cyl.VanishesOutside R (fun x => φ ρ x * ((ψ x : ℝ) : ℂ)) :=
    fun x hx => by simp [hR x hx]
  have hF_int : Integrable (fun x => φ ρ x * ((ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := by
    rw [← IntegrableOn, hcell]
    exact hvan.integrableOn_cell (hcont ρ hρ) c
  have hF'_meas : AEStronglyMeasurable (fun x => ladDt φ ρ x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    ((continuous_ladDt hj hρ).mul (Complex.continuous_ofReal.comp hψ.continuous)).aestronglyMeasurable
  have hbound_int : Integrable (fun x => M * ‖ψ x‖) (volume.restrict (B0579.cell c)) :=
    Integrable.const_mul (Integrable.norm hψ.integrableOn) M
  have h_bound : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ r ∈ Metric.ball ρ (ε / 2),
      ‖ladDt φ r a * ((ψ a : ℝ) : ℂ)‖ ≤ M * ‖ψ a‖ := by
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (Filter.Eventually.of_forall fun a ha r hr => ?_)
    by_cases hA2 : |a.2| ≤ R
    · have h1 := hLD r (hball2 r hr) a (hcellsub a ha) (abs_le.1 hA2)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · simp [hR a (not_le.1 hA2)]
  have h_diff : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ r ∈ Metric.ball ρ (ε / 2),
      HasDerivAt (fun r => φ r a * ((ψ a : ℝ) : ℂ)) (ladDt φ r a * ((ψ a : ℝ) : ℂ)) r :=
    Filter.Eventually.of_forall fun a r hr => (ladDt_hasDerivAt hj (hIcc r (hball2 r hr)) a).mul_const _
  have hF_meas : ∀ᶠ r in 𝓝 ρ, AEStronglyMeasurable (fun x => φ r x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hρ.1 hρ.2) fun r hr => (hcont r hr).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs0nhds hF_meas hF_int hF'_meas
    h_bound hbound_int h_diff).2

private theorem freeAdj_ibp {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hc : 0 < c) (ht : 0 ≤ t)
    (hφ : IsFreeAdjointFlow ν c m tr t s g φ) {ρ : ℝ} (hρ : ρ ∈ Ioo t s)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∫ x in B0579.cell c, freeAdjIntegrand tr (φ ρ) ρ ψ x =
      ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
  have hφs : ContDiff ℝ ∞ (φ ρ) := hφ.smooth ρ (Ioo_subset_Ico_self hρ)
  have hper : ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x := hφ.periodic ρ (Ioo_subset_Ico_self hρ)
  have hφd : Differentiable ℝ (φ ρ) := hφs.differentiable (by simp)
  have hvC : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v ρ x) :=
    tr.isTrain.smooth_v.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨hρ0.le, mem_univ _⟩)
  have hcoord : ∀ j : Fin 2, ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 2) => v j) := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff
  have hvr : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => tr.v ρ x j) := fun j =>
    ((hcoord j).comp hvC).differentiable (by simp)
  have hvj : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp ((hcoord j).comp hvC)
  have hvd : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ)) :=
    fun j => (hvj j).differentiable (by simp)
  have hvper : ∀ x : ℝ × ℝ, tr.v ρ (x.1 + c, x.2) = tr.v ρ x := tr.isTrain.periodic_v ρ hρ0.le
  have hdiv : ∀ x : ℝ × ℝ, pdCx 0 (fun y => ((tr.v ρ y 0 : ℝ) : ℂ)) x +
      pdCx 1 (fun y => ((tr.v ρ y 1 : ℝ) : ℂ)) x = 0 := by
    intro x
    rw [ibpPdCx_ofReal _ (hvr 0) 0 x, ibpPdCx_ofReal _ (hvr 1) 1 x, ← Complex.ofReal_add]
    have hd := tr.isTrain.solenoidal ρ hρ0.le x
    unfold UnforcedLeray.Cyl.divergence at hd
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv (hvr 0) x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv (hvr 1) x] at hd
    have hd' : B0579.pd 0 (fun y => tr.v ρ y 0) x + B0579.pd 1 (fun y => tr.v ρ y 1) x = 0 := hd
    rw [hd', Complex.ofReal_zero]
  have hΦs : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x => φ ρ x * ((tr.v ρ x j : ℝ) : ℂ)) :=
    fun j => hφs.mul (hvj j)
  have hΦper : ∀ j : Fin 2, ∀ x : ℝ × ℝ,
      φ ρ (x.1 + c, x.2) * ((tr.v ρ (x.1 + c, x.2) j : ℝ) : ℂ) = φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) :=
    fun j x => by rw [hper x, hvper x]
  have hP : ∀ j : Fin 2,
      IntegrableOn (fun x => φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) * (B0579.pd j ψ x : ℂ))
        (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx j (fun y => φ ρ y * ((tr.v ρ y j : ℝ) : ℂ)) x * (ψ x : ℂ))
        (B0579.cell c) ∧
      ∫ x in B0579.cell c, φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, pdCx j (fun y => φ ρ y * ((tr.v ρ y j : ℝ) : ℂ)) x * (ψ x : ℂ) :=
    fun j => mpWeakCore c hc _ (hΦs j) (hΦper j) j ψ hψ
  have hLap : ∀ k : Fin 2,
      IntegrableOn (fun x => φ ρ x * (B0579.pd k (B0579.pd k ψ) x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx k (pdCx k (φ ρ)) x * (ψ x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, φ ρ x * (B0579.pd k (B0579.pd k ψ) x : ℂ) =
        ∫ x in B0579.cell c, pdCx k (pdCx k (φ ρ)) x * (ψ x : ℂ) := by
    intro k
    obtain ⟨i1, _, e1⟩ := mpWeakCore c hc (φ ρ) hφs hper k (B0579.pd k ψ) (hψ.pd k)
    obtain ⟨_, i2, e2⟩ := mpWeakCore c hc (pdCx k (φ ρ)) (ibpPdCx_smooth hφs k)
      (ibpPdCx_periodic k (φ ρ) hper) k ψ hψ
    refine ⟨i1, i2, ?_⟩
    rw [e1, e2, neg_neg]
  have hTpt : ∀ x : ℝ × ℝ,
      pdCx 0 (fun y => φ ρ y * ((tr.v ρ y 0 : ℝ) : ℂ)) x * (ψ x : ℂ) +
        pdCx 1 (fun y => φ ρ y * ((tr.v ρ y 1 : ℝ) : ℂ)) x * (ψ x : ℂ) =
        ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    intro x
    rw [ibpPdCx_mul hφd (hvd 0) 0 x, ibpPdCx_mul hφd (hvd 1) 1 x]
    have hdx := hdiv x
    simp only [ladTransport]
    linear_combination (φ ρ x * (ψ x : ℂ)) * hdx
  have hTint : IntegrableOn (fun x => ladTransport tr ρ (φ ρ) x * (ψ x : ℂ)) (B0579.cell c) :=
    ((hP 0).2.1.add (hP 1).2.1).congr_fun (fun x _ => by
      simp only [Pi.add_apply]; exact hTpt x) (B0579.measurableSet_cell c)
  have hA1 : ∫ x in B0579.cell c, φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ) =
      ∫ x in B0579.cell c, ladLapCx (φ ρ) x * (ψ x : ℂ) := by
    have hsplit : (fun x => φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) = fun x =>
        φ ρ x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) + φ ρ x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ) := by
      funext x; simp only [UnforcedLeray.Short.IIb.lapP]; push_cast; ring
    rw [hsplit, integral_add (hLap 0).1 (hLap 1).1, (hLap 0).2.2, (hLap 1).2.2,
      ← integral_add (hLap 0).2.1 (hLap 1).2.1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ladLapCx]; ring
  have hB1 : ∫ x in B0579.cell c, φ ρ x *
      ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c, ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    have hsplit : (fun x => φ ρ x *
        ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ)) = fun x =>
        φ ρ x * ((tr.v ρ x 0 : ℝ) : ℂ) * (B0579.pd 0 ψ x : ℂ) +
          φ ρ x * ((tr.v ρ x 1 : ℝ) : ℂ) * (B0579.pd 1 ψ x : ℂ) := by
      funext x; push_cast; ring
    rw [hsplit, integral_add (hP 0).1 (hP 1).1, (hP 0).2.2, (hP 1).2.2, ← neg_add,
      ← integral_add (hP 0).2.1 (hP 1).2.1]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hTpt)
  have hI1 : IntegrableOn (fun x => φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) (B0579.cell c) := by
    have hfun : (fun x => φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) = fun x =>
        φ ρ x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) + φ ρ x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ) := by
      funext x; simp only [UnforcedLeray.Short.IIb.lapP]; push_cast; ring
    rw [hfun]; exact (hLap 0).1.add (hLap 1).1
  have hI2 : IntegrableOn (fun x => φ ρ x *
      ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ)) (B0579.cell c) := by
    refine ((hP 0).1.add (hP 1).1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.add_apply]; push_cast; ring
  have hLHS : ∫ x in B0579.cell c, freeAdjIntegrand tr (φ ρ) ρ ψ x =
      (ν : ℂ) * (∫ x in B0579.cell c, φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) -
        ∫ x in B0579.cell c, φ ρ x *
          ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
    have hpt : freeAdjIntegrand tr (φ ρ) ρ ψ = fun x =>
        (ν : ℂ) * (φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) -
          φ ρ x * ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
      funext x; unfold freeAdjIntegrand; push_cast; ring
    rw [hpt, integral_sub (Integrable.const_mul hI1 (ν : ℂ)) hI2, integral_const_mul]
  have hRHS : ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) =
      (ν : ℂ) * (∫ x in B0579.cell c, ladLapCx (φ ρ) x * (ψ x : ℂ)) +
        ∫ x in B0579.cell c, ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    have hL : IntegrableOn (fun x => ladLapCx (φ ρ) x * (ψ x : ℂ)) (B0579.cell c) := by
      have hfun : (fun x => ladLapCx (φ ρ) x * (ψ x : ℂ)) = fun x =>
          pdCx 0 (pdCx 0 (φ ρ)) x * (ψ x : ℂ) + pdCx 1 (pdCx 1 (φ ρ)) x * (ψ x : ℂ) := by
        funext x; simp only [ladLapCx]; ring
      rw [hfun]; exact (hLap 0).2.1.add (hLap 1).2.1
    rw [← integral_const_mul, ← integral_add (Integrable.const_mul hL (ν : ℂ)) hTint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ladChi, ladTransport, ladLapCx]; ring
  rw [hLHS, hRHS, hA1, hB1]
  ring

private theorem ladChi_ae_zero_of_free {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hc : 0 < c) (ht : 0 ≤ t) (hts : t < s)
    (hφ : IsFreeAdjointFlow ν c m tr t s g φ) {ρ : ℝ} (hρ : ρ ∈ Ioo t s) :
    ladChi tr φ ρ =ᵐ[volume.restrict (B0579.cell c)] 0 := by
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
  have htest0 : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ) = 0 := by
    intro ψ hψ
    set Af : ℝ → ℂ := fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x
    have hcont := freeAdj_rate_continuousOn tr ht hφ hψ
    have hint' : IntervalIntegrable Af volume ρ s :=
      (hφ.timeIntegrable ψ hψ).mono_set (by
        rw [Set.uIcc_of_le hts.le, Set.uIcc_of_le hρ.2.le]
        exact Icc_subset_Icc hρ.1.le le_rfl)
    have hmeas : StronglyMeasurableAtFilter Af (𝓝 ρ) :=
      hcont.stronglyMeasurableAtFilter isOpen_Ioo ρ hρ
    have hcA : ContinuousAt Af ρ := hcont.continuousAt (Ioo_mem_nhds hρ.1 hρ.2)
    have hder1 : HasDerivAt (fun r => ∫ x in B0579.cell c, φ r x * (ψ x : ℂ)) (-Af ρ) ρ := by
      have h0 : HasDerivAt (fun r => (∫ x in B0579.cell c, g x * (ψ x : ℂ)) + ∫ r' in r..s, Af r')
          (-Af ρ) ρ := by
        simpa using (intervalIntegral.integral_hasDerivAt_left hint' hmeas hcA).const_add
          (∫ x in B0579.cell c, g x * (ψ x : ℂ))
      refine h0.congr_of_eventuallyEq ?_
      filter_upwards [Icc_mem_nhds hρ.1 hρ.2] with r hr
      exact hφ.weak ψ hψ r hr
    have hder2 := freeAdj_dt_deriv hφ hρ hψ
    have heq : (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) = -Af ρ := hder2.unique hder1
    have hibp : Af ρ = ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) :=
      freeAdj_ibp tr hc ht hφ hρ hψ
    obtain ⟨R, hR⟩ := hψ.band
    have hVdt : UnforcedLeray.Cyl.VanishesOutside R (fun x => ladDt φ ρ x * (ψ x : ℂ)) := by
      intro x hx
      have hψ0 : ψ x = 0 := hR x hx
      dsimp only
      rw [hψ0, Complex.ofReal_zero, mul_zero]
    have hIdt : IntegrableOn (fun x => ladDt φ ρ x * (ψ x : ℂ)) (B0579.cell c) := by
      rw [hcell]
      exact UnforcedLeray.Cyl.VanishesOutside.integrableOn_cell hVdt
        ((continuous_ladDt hφ.jointSmooth hρ).mul
          (Complex.continuous_ofReal.comp hψ.continuous)) c
    have hVchi : UnforcedLeray.Cyl.VanishesOutside R (fun x => ladChi tr φ ρ x * (ψ x : ℂ)) := by
      intro x hx
      have hψ0 : ψ x = 0 := hR x hx
      dsimp only
      rw [hψ0, Complex.ofReal_zero, mul_zero]
    have hIchi : IntegrableOn (fun x => ladChi tr φ ρ x * (ψ x : ℂ)) (B0579.cell c) := by
      rw [hcell]
      exact UnforcedLeray.Cyl.VanishesOutside.integrableOn_cell hVchi
        ((continuous_ladChi tr ht hφ.jointSmooth hρ).mul
          (Complex.continuous_ofReal.comp hψ.continuous)) c
    have hIdiff : IntegrableOn (fun x => (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ))
        (B0579.cell c) :=
      (hIchi.sub hIdt).congr_fun (fun x _ => by simp only [Pi.sub_apply]; ring)
        (B0579.measurableSet_cell c)
    have hsplit : ∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ) =
        (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) +
          ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) := by
      rw [← integral_add hIdt hIdiff]
      exact integral_congr_ae (Filter.Eventually.of_forall fun _ => by ring)
    rw [hsplit, heq, hibp, neg_add_cancel]
  set U : Set (ℝ × ℝ) := Ioo (-(c / 2)) (c / 2) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hchi_cont : Continuous (ladChi tr φ ρ) := continuous_ladChi tr ht hφ.jointSmooth hρ
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict (B0579.cell c))
    (hchi_cont.locallyIntegrable.mono_measure Measure.restrict_le_self |>.locallyIntegrableOn U)
    (fun ψ hψ hψc hψU => by
      obtain ⟨Φ, hΦ, hΦψ⟩ := UnforcedLeray.Sob.exists_isCylTest_eq hc hψ hψc hψU
      have hΦ' : B0579.IsCylTest c Φ :=
        { smooth := hΦ.smooth
          periodic := fun x => by
            have hx : (x.1 + c, x.2) = x + (c, 0) := by ext <;> simp
            rw [hx]; exact hΦ.periodic x
          band := hΦ.bounded }
      rw [← htest0 Φ hΦ']
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
      have hx' : x ∈ UnforcedLeray.Sob.cylCell c := hx
      rw [hΦψ x hx', Complex.real_smul, mul_comm])
  have hmemU : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), x ∈ U := by
    rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
    filter_upwards [UnforcedLeray.Sob.ae_fst_ne (-(c / 2))] with x hx hxc
    exact ⟨⟨lt_of_le_of_ne hxc.1.1 (Ne.symm hx), hxc.1.2⟩, mem_univ _⟩
  filter_upwards [key, hmemU] with x h1 h2
  exact h1 h2

/-! ### 3. Continuity of the free pairing on `[t, s]` -/

private theorem ladPair_continuousOn_free {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hφ : IsFreeAdjointFlow ν c m tr t s g φ) (hw : IsLinearisedFlow ν c m tr t f w u) :
    ContinuousOn (ladPair c w φ) (Icc t s) := by
  intro r hr
  have hwm : ∀ r' ∈ Icc t s, MemLp (w r') 2 (B0579.cellMeasure c m) := fun r' h => hw.memX r' h.1
  have hφm : ∀ r' ∈ Icc t s, MemLp (φ r') 2 (B0579.cellMeasure c (-m)) := fun r' h => hφ.memX r' h
  set a : ℝ → ℝ := fun r' => (xNorm c m (w r' - w r)).toReal with ha
  set b : ℝ → ℝ := fun r' => (xNorm c (-m) (φ r' - φ r)).toReal with hb
  have ha0 : Tendsto a (𝓝[Icc t s] r) (𝓝 0) := by
    have h1 : Tendsto (fun r' => xNorm c m (w r' - w r)) (𝓝[Icc t s] r) (𝓝 0) :=
      (hw.strongCont r hr.1).mono_left (nhdsWithin_mono _ (fun _ hx => hx.1))
    simpa [ha, Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  have hb0 : Tendsto b (𝓝[Icc t s] r) (𝓝 0) := by
    simpa [hb, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hφ.strongCont r hr)
  set Nφ := (xNorm c (-m) (φ r)).toReal
  set Nw := (xNorm c m (w r)).toReal
  have hbound : ∀ r' ∈ Icc t s, ‖ladPair c w φ r' - ladPair c w φ r‖ ≤
      a r' * (Nφ + b r') + Nw * b r' := by
    intro r' hr'
    have hd1 : MemLp (w r' - w r) 2 (B0579.cellMeasure c m) := (hwm r' hr').sub (hwm r hr)
    have hd2 : MemLp (φ r' - φ r) 2 (B0579.cellMeasure c (-m)) := (hφm r' hr').sub (hφm r hr)
    obtain ⟨i1, n1⟩ := PairContAux.holder hd1 (hφm r' hr')
    obtain ⟨i2, n2⟩ := PairContAux.holder (hwm r hr) hd2
    obtain ⟨i3, -⟩ := PairContAux.holder (hwm r' hr') (hφm r' hr')
    obtain ⟨i4, -⟩ := PairContAux.holder (hwm r hr) (hφm r hr)
    have hsplit : ladPair c w φ r' - ladPair c w φ r =
        (∫ x in B0579.cell c, (w r' - w r) x * φ r' x) +
          ∫ x in B0579.cell c, w r x * (φ r' - φ r) x := by
      unfold ladPair
      rw [← integral_sub i3 i4, ← integral_add i1 i2]
      congr 1; funext x; simp only [Pi.sub_apply]; ring
    have hφn : (xNorm c (-m) (φ r')).toReal ≤ Nφ + b r' := by
      have hle : xNorm c (-m) (φ r') ≤ xNorm c (-m) (φ r) + xNorm c (-m) (φ r' - φ r) := by
        have : φ r' = φ r + (φ r' - φ r) := by abel
        unfold xNorm
        calc eLpNorm (φ r') 2 _ = eLpNorm (φ r + (φ r' - φ r)) 2 _ := by rw [← this]
          _ ≤ _ := eLpNorm_add_le (hφm r hr).1 hd2.1 (by norm_num)
      have h1ne : xNorm c (-m) (φ r) ≠ ⊤ := (hφm r hr).2.ne
      have h2ne : xNorm c (-m) (φ r' - φ r) ≠ ⊤ := hd2.2.ne
      have hfin : xNorm c (-m) (φ r) + xNorm c (-m) (φ r' - φ r) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨h1ne, h2ne⟩
      have := ENNReal.toReal_mono hfin hle
      rwa [ENNReal.toReal_add h1ne h2ne] at this
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ n2)
    exact n1.trans (mul_le_mul_of_nonneg_left hφn ENNReal.toReal_nonneg)
  have hlim : Tendsto (fun r' => a r' * (Nφ + b r') + Nw * b r') (𝓝[Icc t s] r) (𝓝 0) := by
    have := (ha0.mul ((tendsto_const_nhds (x := Nφ)).add hb0)).add
      ((tendsto_const_nhds (x := Nw)).mul hb0)
    simpa using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbound) hlim

end LinFreeAux

theorem linFreeAdjPairing (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqNeeded.LinFreeAdjPairing ν m tr t₁ t₂ := by
  intro hm hν ht₁ _ht12 _htr hB f w u hw hf0 s hs g φ hφ r hr
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν _
  let I : ℝ → ℂ := fun ρ => ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x
  have e_term : ∫ x in B0579.cell c, w s x * g x = ladPair c w φ s := by
    unfold ladPair
    refine integral_congr_ae ?_
    filter_upwards [hφ.terminal] with x hx
    rw [hx]
  rcases eq_or_lt_of_le (hr.1.trans hr.2) with hts | hts
  · -- degenerate interval `t₁ = s`, hence `r = s`
    have hrs : r = s := le_antisymm hr.2 (hts ▸ hr.1)
    subst hrs
    rw [e_term, intervalIntegral.integral_same, sub_zero]
    rfl
  -- main case `t₁ < s`: uniform bounds on `[t₁, s]`
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  obtain ⟨C0, hC0b⟩ := hB s (ht₁.trans hts.le)
  have hx0 : ((0 : ℝ), (0 : ℝ)) ∈ B0579.cell c := ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans ((hC0b t₁ ⟨ht₁, hts.le⟩ _ hx0).1 0)
  have hwc : ContinuousOn (fun ρ => (xNorm c m (w ρ)).toReal) (Ici t₁) :=
    RateBoundAux.contOn_norm w (fun ρ h => hw.memX ρ h) (fun ρ h => hw.strongCont ρ h)
  obtain ⟨A, hA0, hA⟩ := RateBoundAux.bdd_of_cont (hwc.mono (Icc_subset_Ici_self : Icc t₁ s ⊆ Ici t₁))
  have hφc : ContinuousOn (fun ρ => (xNorm c (-m) (φ ρ)).toReal) (Icc t₁ s) :=
    RateBoundAux.contOn_norm φ (fun ρ h => hφ.memX ρ h) (fun ρ h => hφ.strongCont ρ h)
  obtain ⟨Bφ, _hB0, hBφ⟩ := RateBoundAux.bdd_of_cont hφc
  have hLip := LinFreeAux.velLip_pos hm hc0 hf0 hw
  obtain ⟨Cl, hCl⟩ := LinFreeAux.velLip_pos hm hc0 hf0 hw
  have hu2 : ∀ ρ, t₁ ≤ ρ → ∀ j : Fin 2,
      MemLp (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) :=
    fun ρ h j => (hw.biotSavart ρ h).1 j
  have hAe : ∀ ρ ∈ Icc t₁ s, xNorm c m (w ρ) ≤ ENNReal.ofReal A := fun ρ hρ =>
    RateBoundAux.ofReal_toReal_le (hw.memX ρ hρ.1).eLpNorm_ne_top hA0 (hA ρ hρ)
  have hU : ∀ ρ ∈ Icc t₁ s, ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal Cl * (ENNReal.ofReal A + ENNReal.ofReal A) +
          eLpNorm (fun x => u t₁ x j) 2 (volume.restrict (B0579.cell c)) := by
    intro ρ hρ j
    have h1 := eLpNorm_add_le (p := 2) (μ := volume.restrict (B0579.cell c))
      ((hu2 ρ hρ.1 j).1.sub (hu2 t₁ le_rfl j).1) (hu2 t₁ le_rfl j).1 one_le_two
    rw [sub_add_cancel] at h1
    have h2 := hCl ρ t₁ hρ.1 le_rfl j
    have h3 : xNorm c m (w ρ - w t₁) ≤ xNorm c m (w ρ) + xNorm c m (w t₁) :=
      eLpNorm_sub_le (hw.memX ρ hρ.1).1 (hw.memX t₁ le_rfl).1 one_le_two
    have h4 : xNorm c m (w ρ - w t₁) ≤ ENNReal.ofReal A + ENNReal.ofReal A :=
      h3.trans (add_le_add (hAe ρ hρ) (hAe t₁ ⟨le_rfl, hts.le⟩))
    exact h1.trans (add_le_add (h2.trans (mul_le_mul' le_rfl h4)) le_rfl)
  set Fe : ℝ≥0∞ := ENNReal.ofReal C0 *
    ((ENNReal.ofReal Cl * (ENNReal.ofReal A + ENNReal.ofReal A) +
        eLpNorm (fun x => u t₁ x 0) 2 (volume.restrict (B0579.cell c))) +
      (ENNReal.ofReal Cl * (ENNReal.ofReal A + ENNReal.ofReal A) +
        eLpNorm (fun x => u t₁ x 1) 2 (volume.restrict (B0579.cell c))))
  have hFe : Fe ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) <;>
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩),
        (hu2 t₁ le_rfl _).eLpNorm_ne_top⟩
  have hforce : ∀ ρ ∈ Icc t₁ s, MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) ∧
      (xNorm c m (ladForce tr (u ρ) ρ)).toReal ≤ Fe.toReal := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := ladForceMemX m ν c tr s C0 ρ hC0b ⟨ht₁.trans hρ.1, hρ.2⟩ (u ρ)
      (fun j => hu2 ρ hρ.1 j)
    exact ⟨h1, ENNReal.toReal_mono hFe
      (h2.trans (mul_le_mul' le_rfl (add_le_add (hU ρ hρ 0) (hU ρ hρ 1))))⟩
  have hFe0 : 0 ≤ Fe.toReal := ENNReal.toReal_nonneg
  have hK2 : 0 ≤ 3 * |ν| * K + 2 * C0 * K := by positivity
  -- pointwise convergence `ladRate R ρ → -I ρ` on `(t₁, s)`
  have hRateLim : ∀ ρ ∈ Ioo t₁ s,
      Tendsto (fun R : ℝ => ladRate tr w u φ R ρ) atTop (𝓝 (-I ρ)) := by
    intro ρ hρ
    have hρI : ρ ∈ Icc t₁ s := ⟨hρ.1.le, hρ.2.le⟩
    have hρK : ρ ∈ Ico t₁ s := ⟨hρ.1.le, hρ.2⟩
    have hchi0 := LinFreeAux.ladChi_ae_zero_of_free tr hc0 ht₁ hts hφ hρ
    have hA_zero : ∀ R : ℝ,
        ∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x) = 0 := by
      intro R
      have hae : (fun x => w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) =ᵐ[
          volume.restrict (B0579.cell c)] fun _ => (0 : ℂ) := by
        filter_upwards [hchi0] with x hx
        have hx0 : ladChi tr φ ρ x = 0 := hx
        rw [hx0, mul_zero, mul_zero]
      rw [integral_congr_ae hae, integral_zero]
    have hBl := ladCutLimit c m (ladForce tr (u ρ) ρ) (φ ρ) (hforce ρ hρI).1 (hφ.memX ρ hρI)
    have hwm := hw.memX ρ hρ.1.le
    have i1 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memX ρ hρI)
    have i2 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 0)
    have i3 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 1)
    have hInorm := (i1.add i2).add i3
    have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C0 := fun x hx j =>
      (hC0b ρ ⟨ht₁.trans hρ.1.le, hρ.2.le⟩ x hx).1 j
    have hcomm_bd := RateBoundAux.comm_bound tr w φ ρ K C0 hK0 hC00
      (fun R hR x j => (hK R hR).2.2.2.2.1 x j) (fun R hR x => (hK R hR).2.2.2.2.2 x) hv hInorm
    have hCm : Tendsto (fun R : ℝ => ladComm tr w φ R ρ) atTop (𝓝 0) := by
      have h0 : Tendsto (fun R : ℝ => (3 * |ν| * K + 2 * C0 * K) * R⁻¹ *
          ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
            ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖)) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.const_mul (3 * |ν| * K + 2 * C0 * K)).mul_const
          (∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
            ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖))
        simpa using this
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1 using hcomm_bd R hR1
    have hsum := hBl.neg.add hCm
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [ladRateSplit ν c m tr t₁ s f w u φ hc0 ht₁ hts hw hφ.jointSmooth R hR ρ hρ, hA_zero R,
      zero_sub]
    rfl
  -- increment identity on `[t₁, s)`
  have hpdCont : ∀ k : Fin 2,
      ContinuousOn (fun ρ => (eLpNorm (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal)
        (Ico t₁ s) := fun k =>
    RateBoundAux.contOn_norm (fun ρ => pdCx k (φ ρ))
      (fun ρ h => hφ.memH1 ρ h k) (fun ρ h => hφ.strongContH1 ρ h k)
  have hInc : ∀ r' ∈ Ico t₁ s,
      ladPair c w φ r' - ladPair c w φ t₁ = -∫ ρ in t₁..r', I ρ := by
    intro r' hr'
    rcases eq_or_lt_of_le hr'.1 with hrt | hrt
    · rw [← hrt, sub_self, intervalIntegral.integral_same, neg_zero]
    have hsubI : Icc t₁ r' ⊆ Ico t₁ s := fun x hx => ⟨hx.1, hx.2.trans_lt hr'.2⟩
    have h0int : IntervalIntegrable
        (fun ρ => (eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) volume t₁ r' :=
      ((hpdCont 0).mono hsubI).intervalIntegrable_of_Icc hr'.1
    have h1int : IntervalIntegrable
        (fun ρ => (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) volume t₁ r' :=
      ((hpdCont 1).mono hsubI).intervalIntegrable_of_Icc hr'.1
    set D : ℝ → ℝ := fun ρ =>
      Fe.toReal * Bφ + (3 * |ν| * K + 2 * C0 * K) *
        (A * Bφ + A * ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
          (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal))
    have hDint : IntervalIntegrable D volume t₁ r' :=
      intervalIntegrable_const.add ((intervalIntegrable_const.add ((h0int.add h1int).const_mul A)).const_mul _)
    have hDb : ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t₁ r', ‖ladRate tr w u φ R ρ‖ ≤ D ρ := by
      intro R hR ρ hρ
      have hρs : ρ ∈ Ioo t₁ s := ⟨hρ.1, hρ.2.trans hr'.2⟩
      have hρI : ρ ∈ Icc t₁ s := ⟨hρ.1.le, hρs.2.le⟩
      have hρK : ρ ∈ Ico t₁ s := ⟨hρ.1.le, hρs.2⟩
      have hR0 : 0 < R := by linarith
      rw [ladRateSplit ν c m tr t₁ s f w u φ hc0 ht₁ hts hw hφ.jointSmooth R hR0 ρ hρs]
      have hchi0 := LinFreeAux.ladChi_ae_zero_of_free tr hc0 ht₁ hts hφ hρs
      have hA_zero : ∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x) = 0 := by
        have hae : (fun x => w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) =ᵐ[
            volume.restrict (B0579.cell c)] fun _ => (0 : ℂ) := by
          filter_upwards [hchi0] with x hx
          have hx0 : ladChi tr φ ρ x = 0 := hx
          rw [hx0, mul_zero, mul_zero]
        rw [integral_congr_ae hae, integral_zero]
      rw [hA_zero, zero_sub]
      have hcut := hK R hR0
      have hcb : ∀ x, |ladCut R x| ≤ 1 := fun x => by
        rw [abs_of_nonneg (hcut.2.1 x).1]; exact (hcut.2.1 x).2
      have eb : ‖∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x‖ ≤ Fe.toReal * Bφ :=
        (RateBoundAux.cs_cut c m (hcut.1 c).continuous hcb (hforce ρ hρI).1 (hφ.memX ρ hρI)).trans
          (mul_le_mul (hforce ρ hρI).2 (hBφ ρ hρI) ENNReal.toReal_nonneg hFe0)
      have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C0 := fun x hx j =>
        (hC0b ρ ⟨ht₁.trans hρ.1.le, hρs.2.le⟩ x hx).1 j
      have hwm := hw.memX ρ hρ.1.le
      have i1 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memX ρ hρI)
      have i2 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 0)
      have i3 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 1)
      have hInorm := (i1.add i2).add i3
      have ec := RateBoundAux.comm_bound tr w φ ρ K C0 hK0 hC00
        (fun R hR x j => (hK R hR).2.2.2.2.1 x j) (fun R hR x => (hK R hR).2.2.2.2.2 x) hv hInorm R hR
      have hint : ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
          ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) =
          (∫ x in B0579.cell c, ‖w ρ x‖ * ‖φ ρ x‖) +
            (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖) +
            ∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖ := by
        rw [integral_add (f := fun x => ‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖)
          (g := fun x => ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (i1.add i2) i3, integral_add i1 i2]
      have c1 := (RateBoundAux.cs_norm c m hwm (hφ.memX ρ hρI)).trans
        (mul_le_mul (hA ρ hρI) (hBφ ρ hρI) ENNReal.toReal_nonneg hA0)
      have c2 := (RateBoundAux.cs_norm c m hwm (hφ.memH1 ρ hρK 0)).trans
        (mul_le_mul_of_nonneg_right (hA ρ hρI) ENNReal.toReal_nonneg)
      have c3 := (RateBoundAux.cs_norm c m hwm (hφ.memH1 ρ hρK 1)).trans
        (mul_le_mul_of_nonneg_right (hA ρ hρI) ENNReal.toReal_nonneg)
      have hIle : (∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
          ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖)) ≤ A * Bφ +
          A * ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
            (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) := by
        unfold xNorm at c2 c3
        rw [hint, mul_add]; linarith
      have hI0 : 0 ≤ ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
          ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := integral_nonneg fun _ => by positivity
      have hq1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
      have ec' : ‖ladComm tr w φ R ρ‖ ≤ (3 * |ν| * K + 2 * C0 * K) *
          (A * Bφ + A * ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
            (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal)) := by
        refine ec.trans ?_
        calc _ ≤ (3 * |ν| * K + 2 * C0 * K) * 1 * _ := by gcongr
          _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hIle hK2
      refine (norm_add_le _ _).trans (add_le_add ?_ ec')
      rw [norm_neg]; exact eb
    have hprod : ∀ R : ℝ, 0 < R →
        IntervalIntegrable (fun ρ => ladRate tr w u φ R ρ) volume t₁ r' ∧
          ladCutPair c R w φ r' - ladCutPair c R w φ t₁ = ∫ ρ in t₁..r', ladRate tr w u φ R ρ :=
      fun R hR => ladProductRule ν c m tr t₁ s f w u φ hν hc0 ht₁ hts hw hLip hφ.jointSmooth
        hφ.periodic R hR r' hr'
    have hIoc : Ι t₁ r' = Ioc t₁ r' := Set.uIoc_of_le hr'.1
    have hlimInt : Tendsto (fun R : ℝ => ∫ ρ in t₁..r', ladRate tr w u φ R ρ) atTop
        (𝓝 (∫ ρ in t₁..r', (-I ρ))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence D ?_ ?_ hDint ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        exact (intervalIntegrable_iff.mp (hprod R hR).1).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
        filter_upwards [lad_ae_ne r'] with ρ hρr hρI
        rw [hIoc] at hρI
        exact hDb R hR ρ ⟨hρI.1, lt_of_le_of_ne hρI.2 hρr⟩
      · filter_upwards [lad_ae_ne r'] with ρ hρr hρI
        rw [hIoc] at hρI
        exact hRateLim ρ ⟨hρI.1, (lt_of_le_of_ne hρI.2 hρr).trans hr'.2⟩
    have hcutr : Tendsto (fun R : ℝ => ladCutPair c R w φ r') atTop (𝓝 (ladPair c w φ r')) :=
      ladCutLimit c m (w r') (φ r') (hw.memX r' hr'.1) (hφ.memX r' ⟨hr'.1, hr'.2.le⟩)
    have hcutt : Tendsto (fun R : ℝ => ladCutPair c R w φ t₁) atTop (𝓝 (ladPair c w φ t₁)) :=
      ladCutLimit c m (w t₁) (φ t₁) (hw.memX t₁ le_rfl) (hφ.memX t₁ ⟨le_rfl, hts.le⟩)
    have hdiff' : Tendsto (fun R : ℝ => ladCutPair c R w φ r' - ladCutPair c R w φ t₁) atTop
        (𝓝 (∫ ρ in t₁..r', (-I ρ))) := by
      refine hlimInt.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact ((hprod R hR).2).symm
    have heq := tendsto_nhds_unique (hcutr.sub hcutt) hdiff'
    rwa [intervalIntegral.integral_neg] at heq
  -- integrability of `I` on `[t₁, s]` via a.e. limit of cut rates + uniform bound
  let rSeq : ℕ → ℝ := fun n => s - (s - t₁) / ((n : ℝ) + 2)
  have hrSeq : ∀ n : ℕ, rSeq n ∈ Ioo t₁ s := by
    intro n
    have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hpos : 0 < (s - t₁) / ((n : ℝ) + 2) := div_pos (sub_pos.2 hts) (by positivity)
    have hlt : (s - t₁) / ((n : ℝ) + 2) < s - t₁ := div_lt_self (sub_pos.2 hts) hn2
    exact ⟨by dsimp [rSeq]; linarith, by dsimp [rSeq]; linarith⟩
  let gSeq : ℕ → ℝ → ℂ := fun n =>
    (Ioo t₁ (rSeq n)).indicator (fun ρ => -ladRate tr w u φ ((n : ℝ) + 1) ρ)
  have hgSeq_meas : ∀ n : ℕ, AEStronglyMeasurable (gSeq n) (volume.restrict (Icc t₁ s)) := by
    intro n
    have hRn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hint_n := (ladProductRule ν c m tr t₁ s f w u φ hν hc0 ht₁ hts hw hLip hφ.jointSmooth
      hφ.periodic ((n : ℝ) + 1) hRn (rSeq n) ⟨(hrSeq n).1.le, (hrSeq n).2⟩).1
    have hmeas_Ioc : AEStronglyMeasurable (fun ρ => -ladRate tr w u φ ((n : ℝ) + 1) ρ)
        (volume.restrict (Ioc t₁ (rSeq n))) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (hrSeq n).1.le).mp hint_n).aestronglyMeasurable.neg
    have hmeas_Ioo : AEStronglyMeasurable (fun ρ => -ladRate tr w u φ ((n : ℝ) + 1) ρ)
        (volume.restrict (Ioo t₁ (rSeq n))) :=
      hmeas_Ioc.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
    have hinter : Ioo t₁ (rSeq n) ∩ Icc t₁ s = Ioo t₁ (rSeq n) :=
      inter_eq_left.2 (fun ρ hρ => ⟨hρ.1.le, (hρ.2.trans (hrSeq n).2).le⟩)
    dsimp [gSeq]
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, hinter]
    exact hmeas_Ioo
  have hgSeq_lim : ∀ᵐ ρ ∂(volume.restrict (Icc t₁ s)),
      Tendsto (fun n => gSeq n ρ) atTop (𝓝 (I ρ)) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [lad_ae_ne t₁, lad_ae_ne s] with ρ hρt hρs hρIcc
    have hρ : ρ ∈ Ioo t₁ s := ⟨lt_of_le_of_ne hρIcc.1 hρt.symm, lt_of_le_of_ne hρIcc.2 hρs⟩
    have hlimR : Tendsto (fun n : ℕ => -ladRate tr w u φ ((n : ℝ) + 1) ρ) atTop (𝓝 (I ρ)) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h1 : Tendsto (fun n : ℕ => -ladRate tr w u φ ((n : ℝ) + 1) ρ) atTop (𝓝 (- -I ρ)) :=
        ((hRateLim ρ hρ).neg).comp hnat
      rwa [neg_neg] at h1
    refine hlimR.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ((s - t₁) / (s - ρ))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hsρ : 0 < s - ρ := sub_pos.2 hρ.2
    have hn_gt : (s - t₁) / (s - ρ) < (n : ℝ) + 2 := by
      have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
      linarith
    have hdiv_lt : (s - t₁) / ((n : ℝ) + 2) < s - ρ := by
      rw [div_lt_iff₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])]
      have := (div_lt_iff₀ hsρ).1 hn_gt
      linarith
    have hρ_in : ρ ∈ Ioo t₁ (rSeq n) := ⟨hρ.1, by dsimp [rSeq]; linarith⟩
    exact (Set.indicator_of_mem hρ_in (fun ρ' => -ladRate tr w u φ ((n : ℝ) + 1) ρ')).symm
  have hI_meas : AEStronglyMeasurable I (volume.restrict (Icc t₁ s)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hgSeq_meas hgSeq_lim
  have hI_int : IntegrableOn I (Icc t₁ s) volume := by
    refine (integrableOn_const (C := Fe.toReal * Bφ) (hs := isCompact_Icc.measure_lt_top.ne)).mono'
      hI_meas ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun ρ hρ => ?_
    exact (PairContAux.holder (hforce ρ hρ).1 (hφ.memX ρ hρ)).2.trans
      (mul_le_mul (hforce ρ hρ).2 (hBφ ρ hρ) ENNReal.toReal_nonneg hFe0)
  -- extend increment identity from `[t₁, s)` to `[t₁, s]` by continuity
  have hLHS_cont : ContinuousOn (fun r' => ladPair c w φ r' - ladPair c w φ t₁) (Icc t₁ s) :=
    (LinFreeAux.ladPair_continuousOn_free hφ hw).sub continuousOn_const
  have hI_uIcc : IntegrableOn I (Set.uIcc t₁ s) volume := by
    rwa [Set.uIcc_of_le hts.le]
  have hRHS_cont : ContinuousOn (fun r' => -∫ ρ in t₁..r', I ρ) (Icc t₁ s) := by
    have hc : ContinuousOn (fun r' => ∫ ρ in t₁..r', I ρ) (Icc t₁ s) := by
      have h0 := intervalIntegral.continuousOn_primitive_interval hI_uIcc
      rwa [Set.uIcc_of_le hts.le] at h0
    exact hc.neg
  have hEqIcc : EqOn (fun r' => ladPair c w φ r' - ladPair c w φ t₁)
      (fun r' => -∫ ρ in t₁..r', I ρ) (Icc t₁ s) := by
    refine (show EqOn _ _ (Ico t₁ s) from hInc).of_subset_closure hLHS_cont hRHS_cont
      Ico_subset_Icc_self ?_
    rw [closure_Ico hts.ne]
  have hEq_s := hEqIcc ⟨hts.le, le_rfl⟩
  have hEq_r := hEqIcc hr
  have hI_ii : IntervalIntegrable I volume t₁ s := hI_uIcc.intervalIntegrable
  have hInt_t1r : IntervalIntegrable I volume t₁ r :=
    hI_ii.mono_set (by
      rw [Set.uIcc_of_le hr.1, Set.uIcc_of_le hts.le]
      exact Icc_subset_Icc le_rfl hr.2)
  have hInt_rs : IntervalIntegrable I volume r s :=
    hI_ii.mono_set (by
      rw [Set.uIcc_of_le hr.2, Set.uIcc_of_le hts.le]
      exact Icc_subset_Icc hr.1 le_rfl)
  have hadj := intervalIntegral.integral_add_adjacent_intervals hInt_t1r hInt_rs
  rw [e_term]
  change ladPair c w φ s = ladPair c w φ r - ∫ r' in r..s, I r'
  linear_combination hEq_s - hEq_r + hadj

end Leaf2WeakEqNeeded

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa

end
