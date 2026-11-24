import UnforcedLeray.Short.PartIIb.Sub.PartIIb_B3_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2.RawHeat.HeatDecay3
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2.RawHeat.TrainZero
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2.RawHeat.DatumScale
import UnforcedLeray.Loc.Hyp.HeatProfileRegularity.Fields
import UnforcedLeray.Loc.Hyp.ResidualForce.Continuity

/-!
# `PartII-b:B3/2/1/1`: `RawHeatComparison` (`Tasks/HeatRemainderH2/RawHeat.lean`, SP 2586-2603)

Source of record: `the November 2 reference manuscript`, lines 2586-2603
(`short-bg:raw-heat`: `V - H_a ∈ C_per H² ∩ X_{11/4}`, where `V = p.raw + ∑ i, p.coord z i • p.inlet i`
and `H_a = Blueprint.heatProfile p.ν (p.datum (p.coord z))`).

Combining:
1. Gaussian-increment decay `‖D^j(H_a(τ) - a_τ)(y)‖ ≤ K ‖y‖^{-3-j}` (`‖y‖ ≥ 1`, `j ≤ 2`,
   `B3RemH2Sub.heatProfile_sub_scaledDatum_decay`),
2. Exact similarity dilation of `p.datum (p.coord z)` into age-zero ring lifts
   (`RawHeatAux.scaled_datum_eq_Nv_sum`),
3. Far-field `O(s)` stream increment comparison (`RawHeatAux.raw_sub_train0_far_decay3`),
   near-axis cubic heat expansion (`RawHeatAux.raw_near_axis_decay3`), and bounded-radius cubic
   ring-lift decay (`RawHeatAux.train0Datum_near_decay3`, `RawHeatAux.inlet_sub_frozenDatum_decay`),
4. Bounded-ball inverse-distance bounds (`RawAndInletL4.rawDecayAll_of`, `RawAndInletL4.inletDecayAll`,
   `Heat.simHeat_decay`) and off-axis closure (`RawAndInletIteratedDriftSub.inv_pow_decay_of_offAxis`),
we obtain a phase-uniform majorant `‖D^j(V(τ) - H_a(τ))(y)‖ ≤ M_j (1 + ‖y‖)^{-3}` for `j ≤ 2` on all
of `Space`, yielding uniform `L^{11/4}(ℝ³)` (`q0E`) boundedness and `H²(ℝ³)` path continuity by
dominated convergence (`ResidualForceHyp.continuousOn_toL2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

private theorem joint_contDiff_d1 {V : ℝ → SpatialField}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.HeatProfileReg.d1 (V x.1) i x.2) := by
  have h_eq : (fun x : ℝ × Space => UnforcedLeray.HeatProfileReg.d1 (V x.1) i x.2) =
      fun x : ℝ × Space =>
        fderiv ℝ (fun q : ℝ × Space => V q.1 q.2) x (0, UnforcedLeray.coordinateVector i) := by
    funext ⟨τ, y⟩
    have hd : DifferentiableAt ℝ (fun q : ℝ × Space => V q.1 q.2) (τ, y) :=
      (contDiff_infty_iff_fderiv.1 hV).1 (τ, y)
    have hcomp : HasFDerivAt (V τ)
        ((fderiv ℝ (fun q : ℝ × Space => V q.1 q.2) (τ, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
      hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
    simp only [UnforcedLeray.HeatProfileReg.d1, hcomp.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
  rw [h_eq]
  exact (contDiff_infty_iff_fderiv.1 hV).2.clm_apply contDiff_const

private theorem invBound_of_isB3Datum {P : ℝ} {a : SpatialField}
    (ha : Cons.C03.IsB3Datum P a) :
    ∃ C : ℝ, UnforcedLeray.ResidualForceHyp.InvBound a C := by
  obtain ⟨C0, hC0⟩ := ha.bounds 0 (Nat.zero_le _)
  refine ⟨max C0 0, ⟨ha.smooth.continuousOn, fun x hx => ?_⟩⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 := hC0 x hx
  rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h1
  exact (le_mul_inv_iff₀ hxn).2 (h1.trans (le_max_left _ _))

private theorem heat_diff_offAxis_decay3 {P ν : ℝ} (hν : 0 < ν) {a : SpatialField}
    (ha : Cons.C03.IsB3Datum P a) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℝ) (y : Space), 1 ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (fun y' =>
        UnforcedLeray.Blueprint.heatProfile ν a τ y' -
          Real.exp (τ / 2) • a (Real.exp (τ / 2) • y')) y‖ ≤ K := by
  obtain ⟨K0, hK0⟩ := B3RemH2Sub.heatProfile_sub_scaledDatum_decay hν ha hj
  set K : ℝ := max K0 0
  have hK_nn : 0 ≤ K := le_max_right _ _
  refine ⟨8 * K, by positivity, fun τ y hy1 => ?_⟩
  have hyn0 : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy1
  have h1 := hK0 τ y hy1
  rw [Real.rpow_neg hyn0.le, Real.rpow_natCast] at h1
  have hpow_ge : ‖y‖ ^ 3 ≤ ‖y‖ ^ (3 + j) := pow_le_pow_right₀ hy1 (Nat.le_add_right 3 j)
  have hinv_le : (‖y‖ ^ (3 + j))⁻¹ ≤ (‖y‖ ^ 3)⁻¹ :=
    inv_anti₀ (pow_pos hyn0 3) hpow_ge
  have h2 : ‖iteratedFDeriv ℝ j (fun y' =>
      UnforcedLeray.Blueprint.heatProfile ν a τ y' -
        Real.exp (τ / 2) • a (Real.exp (τ / 2) • y')) y‖ ≤ K * (‖y‖ ^ 3)⁻¹ := by
    refine h1.trans ?_
    calc K0 * (‖y‖ ^ (3 + j))⁻¹
        ≤ K * (‖y‖ ^ (3 + j))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ K * (‖y‖ ^ 3)⁻¹ := mul_le_mul_of_nonneg_left hinv_le hK_nn
  have hw_le : (1 + ‖y‖) ^ 3 ≤ 8 * ‖y‖ ^ 3 := by
    have hny : 1 + ‖y‖ ≤ 2 * ‖y‖ := by linarith only [hy1]
    calc (1 + ‖y‖) ^ 3 ≤ (2 * ‖y‖) ^ 3 := pow_le_pow_left₀ (by positivity) hny 3
      _ = 8 * ‖y‖ ^ 3 := by ring
  have hcancel : ‖y‖ ^ 3 * (‖y‖ ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 3 hyn0.ne')
  calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (fun y' =>
        UnforcedLeray.Blueprint.heatProfile ν a τ y' -
          Real.exp (τ / 2) • a (Real.exp (τ / 2) • y')) y‖
      ≤ (8 * ‖y‖ ^ 3) * (K * (‖y‖ ^ 3)⁻¹) :=
        mul_le_mul hw_le h2 (norm_nonneg _) (by positivity)
    _ = 8 * K * (‖y‖ ^ 3 * (‖y‖ ^ 3)⁻¹) := by ring
    _ = 8 * K := by rw [hcancel, mul_one]

private theorem exists_continuous_H2_and_q0E_of_decay3 (F : ℝ → SpatialField)
    (hF_cd : ∀ τ : ℝ, ContDiff ℝ 2 (F τ))
    (hF_cont0 : ∀ y : Space, Continuous (fun τ : ℝ => F τ y))
    (hF_cont1 : ∀ (i : Fin 3) (y : Space),
      Continuous (fun τ : ℝ => UnforcedLeray.HeatProfileReg.d1 (F τ) i y))
    (hF_cont2 : ∀ (i j : Fin 3) (y : Space),
      Continuous (fun τ : ℝ => UnforcedLeray.HeatProfileReg.d2 (F τ) i j y))
    (hF_bd : ∀ j : ℕ, j ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (τ : ℝ) (y : Space),
      ‖iteratedFDeriv ℝ j (F τ) y‖ ≤ M * ((1 + ‖y‖) ^ 3)⁻¹) :
    (∃ R_V : ℝ → UnforcedLeray.SobolevGraph.H2, Continuous R_V ∧
      ∀ τ : ℝ, ((R_V τ).value : SpatialField) =ᵐ[volume] F τ) ∧
    ∃ M_V : ℝ, ∀ τ : ℝ, eLpNorm (F τ) B0412.q0E volume ≤ ENNReal.ofReal M_V := by
  obtain ⟨M₀, hM₀, hb₀⟩ := hF_bd 0 (by norm_num)
  obtain ⟨M₁, hM₁, hb₁⟩ := hF_bd 1 (by norm_num)
  obtain ⟨M₂, hM₂, hb₂⟩ := hF_bd 2 le_rfl
  have hw3_le_w2 : ∀ y : Space, ((1 + ‖y‖) ^ 3)⁻¹ ≤ ((1 + ‖y‖) ^ 2)⁻¹ := by
    intro y
    have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hy1 (by norm_num))
  have hb₀_2 : ∀ (τ : ℝ) (y : Space), ‖F τ y‖ ≤ M₀ / (1 + ‖y‖) ^ 2 := by
    intro τ y
    rw [div_eq_mul_inv]
    have h := hb₀ τ y
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hw3_le_w2 y) hM₀)
  have hb₁_2 : ∀ (i : Fin 3) (τ : ℝ) (y : Space),
      ‖UnforcedLeray.HeatProfileReg.d1 (F τ) i y‖ ≤ M₁ / (1 + ‖y‖) ^ 2 := by
    intro i τ y
    rw [div_eq_mul_inv]
    exact (UnforcedLeray.HeatProfileReg.norm_d1_le (F τ) i y).trans
      ((hb₁ τ y).trans (mul_le_mul_of_nonneg_left (hw3_le_w2 y) hM₁))
  have hb₂_2 : ∀ (i j : Fin 3) (τ : ℝ) (y : Space),
      ‖UnforcedLeray.HeatProfileReg.d2 (F τ) i j y‖ ≤ M₂ / (1 + ‖y‖) ^ 2 := by
    intro i j τ y
    rw [div_eq_mul_inv]
    exact (UnforcedLeray.HeatProfileReg.norm_d2_le (hF_cd τ) i j y).trans
      ((hb₂ τ y).trans (mul_le_mul_of_nonneg_left (hw3_le_w2 y) hM₂))
  have hm₀ : ∀ τ : ℝ, MemLp (F τ) 2 volume := fun τ =>
    UnforcedLeray.ResidualForceHyp.memLp_of_bound
      (hF_cd τ).continuous.aestronglyMeasurable (hb₀_2 τ)
  have hm₁ : ∀ (i : Fin 3) (τ : ℝ), MemLp (UnforcedLeray.HeatProfileReg.d1 (F τ) i) 2 volume :=
    fun i τ => UnforcedLeray.ResidualForceHyp.memLp_of_bound
      (UnforcedLeray.HeatProfileReg.d1_contDiff (hF_cd τ) i).continuous.aestronglyMeasurable
      (hb₁_2 i τ)
  have hm₂ : ∀ (i j : Fin 3) (τ : ℝ), MemLp (UnforcedLeray.HeatProfileReg.d2 (F τ) i j) 2 volume :=
    fun i j τ => UnforcedLeray.ResidualForceHyp.memLp_of_bound
      (UnforcedLeray.HeatProfileReg.d2_continuous (hF_cd τ) i j).aestronglyMeasurable
      (hb₂_2 i j τ)
  let R_V : ℝ → UnforcedLeray.SobolevGraph.H2 := fun τ =>
    UnforcedLeray.SobolevGraph.H2.ofFields (F τ)
      (fun i => UnforcedLeray.HeatProfileReg.d1 (F τ) i)
      (fun i j => UnforcedLeray.HeatProfileReg.d2 (F τ) i j)
      (hm₀ τ)
      (fun i => hm₁ i τ)
      (fun i j => hm₂ i j τ)
      (fun i => UnforcedLeray.hasWeakSpatialDerivative_of_contDiff
        ((hF_cd τ).of_le (by norm_num)) i)
      (fun i j => UnforcedLeray.hasWeakSpatialDerivative_of_contDiff
        (UnforcedLeray.HeatProfileReg.d1_contDiff (hF_cd τ) i) j)
  have hRV_cont : Continuous R_V := by
    rw [← continuousOn_univ, UnforcedLeray.SobolevGraph.H2.continuousOn_iff_components]
    refine ⟨?_, fun i => ?_, fun i j => ?_⟩
    · exact UnforcedLeray.ResidualForceHyp.continuousOn_toL2
        (fun τ _ => (hF_cd τ).continuous.aestronglyMeasurable)
        (fun τ _ y => hb₀_2 τ y)
        (fun y => (hF_cont0 y).continuousOn)
    · exact UnforcedLeray.ResidualForceHyp.continuousOn_toL2
        (fun τ _ => (UnforcedLeray.HeatProfileReg.d1_contDiff
          (hF_cd τ) i).continuous.aestronglyMeasurable)
        (fun τ _ y => hb₁_2 i τ y)
        (fun y => (hF_cont1 i y).continuousOn)
    · exact UnforcedLeray.ResidualForceHyp.continuousOn_toL2
        (fun τ _ => (UnforcedLeray.HeatProfileReg.d2_continuous
          (hF_cd τ) i j).aestronglyMeasurable)
        (fun τ _ y => hb₂_2 i j τ y)
        (fun y => (hF_cont2 i j y).continuousOn)
  have hRV_ae : ∀ τ : ℝ, ((R_V τ).value : SpatialField) =ᵐ[volume] F τ := fun τ =>
    UnforcedLeray.coeFn_toL2 (hm₀ τ)
  -- Uniform `L^{11/4}(ℝ³)` (`B0412.q0E`) bound via `(1 + ‖y‖)⁻³ ∈ L^{11/4}(ℝ³)`
  let w3 : Space → ℝ := fun y => ((1 + ‖y‖) ^ 3)⁻¹
  have hq0_eq : B0412.q0E = ENNReal.ofReal B0281.q0 := by
    rw [← S1Sub.s1_ofReal_bgp_eq_q0E, S1Sub.s1_bgp_eq_q0]
  have hq0_pos : 0 < B0281.q0 := by linarith [S1Sub.s1_q0_gt]
  have hq0_ne0 : B0412.q0E ≠ 0 := by
    rw [hq0_eq]
    exact (ENNReal.ofReal_pos.2 hq0_pos).ne'
  have hq0_top : B0412.q0E ≠ ⊤ := by
    rw [hq0_eq]
    exact ENNReal.ofReal_ne_top
  have hq0_toReal : B0412.q0E.toReal = B0281.q0 := by
    rw [hq0_eq, ENNReal.toReal_ofReal hq0_pos.le]
  have h3q0 : 3 < (3 : ℝ) * B0412.q0E.toReal := by
    rw [hq0_toReal]
    linarith [S1Sub.s1_q0_gt]
  have hw_q0 : MemLp w3 B0412.q0E volume :=
    UnforcedLeray.HeatProfileReg.memLp_weight 3 B0412.q0E hq0_ne0 hq0_top h3q0
  refine ⟨⟨R_V, hRV_cont, hRV_ae⟩,
    ⟨M₀ * (eLpNorm w3 B0412.q0E volume).toReal, fun τ => ?_⟩⟩
  have hpt : ∀ y : Space, ‖F τ y‖ ≤ M₀ * ‖w3 y‖ := by
    intro y
    have hw_nn : 0 ≤ w3 y := by dsimp [w3]; positivity
    rw [Real.norm_of_nonneg hw_nn]
    have h := hb₀ τ y
    rwa [norm_iteratedFDeriv_zero] at h
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (f := F τ) (g := w3) (c := M₀)
    (Eventually.of_forall hpt) B0412.q0E
  refine h1.trans ?_
  rw [ENNReal.ofReal_mul hM₀, ENNReal.ofReal_toReal hw_q0.eLpNorm_ne_top]

private theorem slice_contDiff_of_joint {V : ℝ → SpatialField}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ∞ (V τ) := by
  have hc : ContDiff ℝ ∞ ((fun x : ℝ × Space => V x.1 x.2) ∘ fun y : Space => (τ, y)) :=
    hV.comp (contDiff_prodMk_right τ)
  exact hc

private theorem phase_continuous_of_joint {V : ℝ → SpatialField}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) (y : Space) :
    Continuous (fun τ : ℝ => V τ y) := by
  have hc : Continuous ((fun x : ℝ × Space => V x.1 x.2) ∘ fun τ : ℝ => (τ, y)) :=
    hV.continuous.comp (continuous_id.prodMk continuous_const)
  exact hc

private theorem iteratedFDeriv_lin_comb {f g0 g1 h : SpatialField} {α0 α1 : ℝ}
    {j : ℕ} {y : Space}
    (hf : ContDiffAt ℝ j f y) (hg0 : ContDiffAt ℝ j g0 y)
    (hg1 : ContDiffAt ℝ j g1 y) (hh : ContDiffAt ℝ j h y) :
    iteratedFDeriv ℝ j (fun x => (f x + (α0 • g0 x + α1 • g1 x)) - h x) y =
      (iteratedFDeriv ℝ j f y +
        (α0 • iteratedFDeriv ℝ j g0 y + α1 • iteratedFDeriv ℝ j g1 y)) -
        iteratedFDeriv ℝ j h y := by
  change iteratedFDeriv ℝ j ((f + ((fun x => α0 • g0 x) + (fun x => α1 • g1 x))) - h) y = _
  have hc0 : ContDiffAt ℝ j (fun x => α0 • g0 x) y := hg0.const_smul α0
  have hc1 : ContDiffAt ℝ j (fun x => α1 • g1 x) y := hg1.const_smul α1
  have hc01 : ContDiffAt ℝ j ((fun x => α0 • g0 x) + (fun x => α1 • g1 x)) y := hc0.add hc1
  have hcf : ContDiffAt ℝ j (f + ((fun x => α0 • g0 x) + (fun x => α1 • g1 x))) y := hf.add hc01
  rw [iteratedFDeriv_sub_apply hcf hh, iteratedFDeriv_add_apply hf hc01,
    iteratedFDeriv_add_apply hc0 hc1,
    show (fun x => α0 • g0 x) = α0 • g0 from rfl,
    show (fun x => α1 • g1 x) = α1 • g1 from rfl,
    iteratedFDeriv_const_smul_apply hg0, iteratedFDeriv_const_smul_apply hg1]

private def rawInletSum (p : Cons.C03.Concrete.Params) (α : Fin 2 → ℝ) (τ : ℝ) : SpatialField :=
  fun y => p.raw τ y + ∑ i : Fin 2, α i • p.inlet i τ y

private def rawHeatDiff (p : Cons.C03.Concrete.Params) (α : Fin 2 → ℝ) (τ : ℝ) : SpatialField :=
  rawInletSum p α τ - UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ

private def train0Prof (p : Cons.C03.Concrete.Params) : ℝ × (ℝ × ℝ) → Axi.Merid :=
  fun n => Cons.C03.Concrete.datumProfile p.ε (p.train.ψ 0) n.2

private def frozenProf (p : Cons.C03.Concrete.Params) (i : Fin 2) : ℝ × (ℝ × ℝ) → Axi.Merid :=
  fun n => Cons.C03.Concrete.datumProfile p.ε (p.frozenStream i) n.2

private def scaledDatumField (p : Cons.C03.Concrete.Params) (α : Fin 2 → ℝ) (τ : ℝ) :
    SpatialField :=
  fun x => Real.exp (τ / 2) • p.datum α (Real.exp (τ / 2) • x)

private def rawTrain0Diff (p : Cons.C03.Concrete.Params) (τ : ℝ) : SpatialField :=
  fun x => p.raw τ x - Axi.Nv p.R (train0Prof p) τ x

private def inletFrozenDiff (p : Cons.C03.Concrete.Params) (i : Fin 2) (τ : ℝ) : SpatialField :=
  fun x => p.inlet i τ x - Axi.Nv p.R (frozenProf p i) τ x

private def heatScaledDiff (p : Cons.C03.Concrete.Params) (α : Fin 2 → ℝ) (τ : ℝ) :
    SpatialField :=
  fun x => UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ x - scaledDatumField p α τ x

private theorem rawHeatDiff_regularity (p : Cons.C03.Concrete.Params) (α : Fin 2 → ℝ)
    {C_inv : ℝ} (hv_inv : UnforcedLeray.ResidualForceHyp.InvBound (p.datum α) C_inv)
    (hRaw_j : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    (hInl_j : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) :
    (∀ τ : ℝ, ContDiff ℝ ∞ (rawHeatDiff p α τ)) ∧
    (∀ y : Space, Continuous (fun τ : ℝ => rawHeatDiff p α τ y)) ∧
    (∀ (i : Fin 3) (y : Space),
      Continuous (fun τ : ℝ => UnforcedLeray.HeatProfileReg.d1 (rawHeatDiff p α τ) i y)) ∧
    (∀ (i j : Fin 3) (y : Space),
      Continuous (fun τ : ℝ => UnforcedLeray.HeatProfileReg.d2 (rawHeatDiff p α τ) i j y)) := by
  have hV_joint : ContDiff ℝ ∞ (fun x : ℝ × Space => rawInletSum p α x.1 x.2) := by
    have heq : (fun x : ℝ × Space => rawInletSum p α x.1 x.2) =
        fun x : ℝ × Space =>
          p.raw x.1 x.2 + (α 0 • p.inlet 0 x.1 x.2 + α 1 • p.inlet 1 x.1 x.2) := by
      funext x
      simp only [rawInletSum, Fin.sum_univ_two]
    rw [heq]
    exact hRaw_j.add (((hInl_j 0).const_smul (α 0)).add ((hInl_j 1).const_smul (α 1)))
  have hV_cd : ∀ τ : ℝ, ContDiff ℝ ∞ (rawInletSum p α τ) :=
    fun τ => slice_contDiff_of_joint hV_joint τ
  have hHa_cd : ∀ τ : ℝ,
      ContDiff ℝ ∞ (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) :=
    fun τ => Heat.simHeat_contDiff p.ν_pos hv_inv.heatAdmissible τ
  have hF_cd_inf : ∀ τ : ℝ, ContDiff ℝ ∞ (rawHeatDiff p α τ) :=
    fun τ => (hV_cd τ).sub (hHa_cd τ)
  have hV_d1 : ∀ i : Fin 3, ContDiff ℝ ∞
      (fun x : ℝ × Space => UnforcedLeray.HeatProfileReg.d1 (rawInletSum p α x.1) i x.2) :=
    fun i => joint_contDiff_d1 hV_joint i
  have hV_d2 : ∀ i j : Fin 3, ContDiff ℝ ∞
      (fun x : ℝ × Space => UnforcedLeray.HeatProfileReg.d2 (rawInletSum p α x.1) i j x.2) :=
    fun i j => joint_contDiff_d1
      (V := fun τ => UnforcedLeray.HeatProfileReg.d1 (rawInletSum p α τ) i) (hV_d1 i) j
  refine ⟨hF_cd_inf, fun y => ?_, fun i y => ?_, fun i j y => ?_⟩
  · exact (phase_continuous_of_joint hV_joint y).sub
      (UnforcedLeray.ResidualForceHyp.heatProfile_continuity p.ν_pos hv_inv y 0 0).1
  · have heq : (fun τ : ℝ => UnforcedLeray.HeatProfileReg.d1 (rawHeatDiff p α τ) i y) =
        fun τ : ℝ => UnforcedLeray.HeatProfileReg.d1 (rawInletSum p α τ) i y -
          UnforcedLeray.HeatProfileReg.d1
            (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) i y :=
      funext fun τ => UnforcedLeray.HeatProfileReg.d1_sub
        ((hV_cd τ).of_le (by simp))
        ((hHa_cd τ).of_le (by simp)) i y
    rw [heq]
    exact (phase_continuous_of_joint (V := fun τ => UnforcedLeray.HeatProfileReg.d1
        (rawInletSum p α τ) i) (hV_d1 i) y).sub
      (UnforcedLeray.ResidualForceHyp.heatProfile_continuity p.ν_pos hv_inv y i 0).2.1
  · have heq : (fun τ : ℝ => UnforcedLeray.HeatProfileReg.d2 (rawHeatDiff p α τ) i j y) =
        fun τ : ℝ => UnforcedLeray.HeatProfileReg.d2 (rawInletSum p α τ) i j y -
          UnforcedLeray.HeatProfileReg.d2
            (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) i j y :=
      funext fun τ => UnforcedLeray.HeatProfileReg.d2_sub
        ((hV_cd τ).of_le (by simp))
        ((hHa_cd τ).of_le (by simp)) i j y
    rw [heq]
    exact (phase_continuous_of_joint (V := fun τ => UnforcedLeray.HeatProfileReg.d2
        (rawInletSum p α τ) i j) (hV_d2 i j) y).sub
      (UnforcedLeray.ResidualForceHyp.heatProfile_continuity p.ν_pos hv_inv y i j).2.2

private theorem rawHeatDiff_small_radius_bound (p : Cons.C03.Concrete.Params) (α : Fin 2 → ℝ)
    {C_inv : ℝ} (hv_inv : UnforcedLeray.ResidualForceHyp.InvBound (p.datum α) C_inv)
    (hRaw_cd : ∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ))
    (hInl_cd : ∀ (i : Fin 2) (τ : ℝ), ContDiff ℝ ∞ (p.inlet i τ))
    {j : ℕ} {R_cut B_raw1 B_in1 K_sim_raw : ℝ} (hR_cut0 : 0 ≤ R_cut)
    (_hB_raw10 : 0 ≤ B_raw1) (_hB_in10 : 0 ≤ B_in1)
    (hB_raw1 : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      (1 + ‖y‖) * ‖iteratedFDeriv ℝ j (p.raw τ) y‖ ≤ B_raw1)
    (hB_in1 : ∀ (i : Fin 2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
      (1 + ‖y‖) * ‖iteratedFDeriv ℝ j (p.inlet i τ) y‖ ≤ B_in1)
    (hK_sim_raw : ∀ (τ : ℝ) (y : Space),
      ‖iteratedFDeriv ℝ j (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y‖ ≤
        K_sim_raw * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)))
    (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) (hynorm : ‖y‖ < R_cut) :
    (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖ ≤
      (1 + R_cut) ^ 2 * (B_raw1 + |α 0| * B_in1 + |α 1| * B_in1 + max K_sim_raw 0) := by
  have h1y_pos : 0 < 1 + ‖y‖ := by positivity
  have hw_sq : (1 + ‖y‖) ^ 2 ≤ (1 + R_cut) ^ 2 :=
    pow_le_pow_left₀ h1y_pos.le (by linarith only [hynorm]) 2
  have hHa_cd : ContDiff ℝ ∞ (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) :=
    Heat.simHeat_contDiff p.ν_pos hv_inv.heatAdmissible τ
  have hF_split : rawHeatDiff p α τ = fun x =>
      (p.raw τ x + (α 0 • p.inlet 0 τ x + α 1 • p.inlet 1 τ x)) -
        UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ x := by
    funext x
    simp only [rawHeatDiff, rawInletSum, Fin.sum_univ_two, Pi.sub_apply]
  have hc_raw : ContDiffAt ℝ j (p.raw τ) y :=
    (hRaw_cd τ).contDiffAt.of_le (by simp)
  have hc_in0 : ContDiffAt ℝ j (p.inlet 0 τ) y :=
    (hInl_cd 0 τ).contDiffAt.of_le (by simp)
  have hc_in1 : ContDiffAt ℝ j (p.inlet 1 τ) y :=
    (hInl_cd 1 τ).contDiffAt.of_le (by simp)
  have hc_Ha : ContDiffAt ℝ j (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y :=
    hHa_cd.contDiffAt.of_le (by simp)
  have hD_F : iteratedFDeriv ℝ j (rawHeatDiff p α τ) y =
      (iteratedFDeriv ℝ j (p.raw τ) y +
        (α 0 • iteratedFDeriv ℝ j (p.inlet 0 τ) y +
          α 1 • iteratedFDeriv ℝ j (p.inlet 1 τ) y)) -
        iteratedFDeriv ℝ j (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y := by
    rw [hF_split]
    exact iteratedFDeriv_lin_comb hc_raw hc_in0 hc_in1 hc_Ha
  obtain ⟨K_sim, hK_sim_def⟩ : ∃ x : ℝ, x = max K_sim_raw 0 := ⟨_, rfl⟩
  have hK_sim0 : 0 ≤ K_sim := hK_sim_def ▸ le_max_right _ _
  have hHa_1 : (1 + ‖y‖) *
      ‖iteratedFDeriv ℝ j (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y‖ ≤ K_sim := by
    have hsim := hK_sim_raw τ y
    rw [Real.rpow_neg h1y_pos.le, Real.rpow_natCast] at hsim
    have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have hinv_le : ((1 + ‖y‖) ^ (1 + j))⁻¹ ≤ (1 + ‖y‖)⁻¹ := by
      simpa only [pow_one] using
        inv_anti₀ (pow_pos h1y_pos 1) (pow_le_pow_right₀ hy1 (Nat.le_add_right 1 j))
    have hsim' : ‖iteratedFDeriv ℝ j
        (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y‖ ≤ K_sim * (1 + ‖y‖)⁻¹ := by
      refine hsim.trans ?_
      calc K_sim_raw * ((1 + ‖y‖) ^ (1 + j))⁻¹
          ≤ K_sim * ((1 + ‖y‖) ^ (1 + j))⁻¹ := by
            rw [hK_sim_def]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ K_sim * (1 + ‖y‖)⁻¹ := mul_le_mul_of_nonneg_left hinv_le hK_sim0
    calc (1 + ‖y‖) *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y‖
        ≤ (1 + ‖y‖) * (K_sim * (1 + ‖y‖)⁻¹) :=
          mul_le_mul_of_nonneg_left hsim' h1y_pos.le
      _ = K_sim * ((1 + ‖y‖) * (1 + ‖y‖)⁻¹) := by ring
      _ = K_sim := by rw [mul_inv_cancel₀ h1y_pos.ne', mul_one]
  have htri : ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖ ≤
      ‖iteratedFDeriv ℝ j (p.raw τ) y‖ +
        (|α 0| * ‖iteratedFDeriv ℝ j (p.inlet 0 τ) y‖ +
          |α 1| * ‖iteratedFDeriv ℝ j (p.inlet 1 τ) y‖) +
        ‖iteratedFDeriv ℝ j (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y‖ := by
    rw [hD_F]
    have s1 := norm_sub_le
      (iteratedFDeriv ℝ j (p.raw τ) y +
        (α 0 • iteratedFDeriv ℝ j (p.inlet 0 τ) y +
          α 1 • iteratedFDeriv ℝ j (p.inlet 1 τ) y))
      (iteratedFDeriv ℝ j (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y)
    have s2 := norm_add_le (iteratedFDeriv ℝ j (p.raw τ) y)
      (α 0 • iteratedFDeriv ℝ j (p.inlet 0 τ) y +
        α 1 • iteratedFDeriv ℝ j (p.inlet 1 τ) y)
    have s3 := norm_add_le (α 0 • iteratedFDeriv ℝ j (p.inlet 0 τ) y)
      (α 1 • iteratedFDeriv ℝ j (p.inlet 1 τ) y)
    rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs] at s3
    linarith only [s1, s2, s3]
  have h1_sum : (1 + ‖y‖) * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖ ≤
      B_raw1 + |α 0| * B_in1 + |α 1| * B_in1 + K_sim := by
    have br := hB_raw1 τ y hy
    have bi0 := mul_le_mul_of_nonneg_left (hB_in1 0 τ y hy) (abs_nonneg (α 0))
    have bi1 := mul_le_mul_of_nonneg_left (hB_in1 1 τ y hy) (abs_nonneg (α 1))
    calc (1 + ‖y‖) * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖
        ≤ (1 + ‖y‖) * (‖iteratedFDeriv ℝ j (p.raw τ) y‖ +
            (|α 0| * ‖iteratedFDeriv ℝ j (p.inlet 0 τ) y‖ +
              |α 1| * ‖iteratedFDeriv ℝ j (p.inlet 1 τ) y‖) +
            ‖iteratedFDeriv ℝ j
              (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y‖) :=
          mul_le_mul_of_nonneg_left htri h1y_pos.le
      _ = (1 + ‖y‖) * ‖iteratedFDeriv ℝ j (p.raw τ) y‖ +
            |α 0| * ((1 + ‖y‖) * ‖iteratedFDeriv ℝ j (p.inlet 0 τ) y‖) +
            |α 1| * ((1 + ‖y‖) * ‖iteratedFDeriv ℝ j (p.inlet 1 τ) y‖) +
            (1 + ‖y‖) * ‖iteratedFDeriv ℝ j
              (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) y‖ := by ring
      _ ≤ B_raw1 + |α 0| * B_in1 + |α 1| * B_in1 + K_sim := by
          linarith only [br, bi0, bi1, hHa_1]
  rw [← hK_sim_def]
  calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖
      = (1 + ‖y‖) ^ 2 * ((1 + ‖y‖) * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖) := by ring
    _ ≤ (1 + R_cut) ^ 2 * (B_raw1 + |α 0| * B_in1 + |α 1| * B_in1 + K_sim) :=
        mul_le_mul hw_sq h1_sum (by positivity) (by positivity)

private theorem rawHeatDiff_large_radius_bound (p : Cons.C03.Concrete.Params) (α : Fin 2 → ℝ)
    (hfro : ∀ i : Fin 2, ContDiff ℝ ∞ (p.frozenStream i))
    (ha : Cons.C03.IsB3Datum p.period (p.datum α))
    {C_inv : ℝ} (hv_inv : UnforcedLeray.ResidualForceHyp.InvBound (p.datum α) C_inv)
    (hRaw_cd : ∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ))
    (hInl_cd : ∀ (i : Fin 2) (τ : ℝ), ContDiff ℝ ∞ (p.inlet i τ))
    {j : ℕ} {B_far B_rnear B_dnear M_in0 M_in1 K_h : ℝ}
    (hB_far0 : 0 ≤ B_far) (hB_rnear0 : 0 ≤ B_rnear) (hB_dnear0 : 0 ≤ B_dnear)
    (hB_far : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis → Axi.age p.R y ≤ 1 →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawTrain0Diff p τ) y‖ ≤ B_far)
    (hB_rnear : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis → 1 < Axi.age p.R y → 2 * p.R ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.raw τ) y‖ ≤ B_rnear)
    (hB_dnear : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis → 1 ≤ Axi.age p.R y → 2 * p.R ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y‖ ≤ B_dnear)
    (hM_in0 : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis → 2 * (p.R / √(p.H / 4)) ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y‖ ≤ M_in0)
    (hM_in1 : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis → 2 * (p.R / √(p.H / 4)) ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y‖ ≤ M_in1)
    (hK_h : ∀ (τ : ℝ) (y : Space), 1 ≤ ‖y‖ →
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (heatScaledDiff p α τ) y‖ ≤ K_h)
    (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) (hy1 : 1 ≤ ‖y‖)
    (hyR : 2 * p.R ≤ ‖y‖) (hyH : 2 * (p.R / √(p.H / 4)) ≤ ‖y‖) :
    (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖ ≤
      (B_far + B_rnear + B_dnear) + (|α 0| * M_in0 + |α 1| * M_in1) + K_h := by
  have hR0 : p.R ≠ 0 := p.R_pos.ne'
  have hy_ne0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy1
    linarith only [hy1]
  have hF_ext_eq : rawHeatDiff p α τ = fun x =>
      (rawTrain0Diff p τ x +
        (α 0 • inletFrozenDiff p 0 τ x + α 1 • inletFrozenDiff p 1 τ x)) -
        heatScaledDiff p α τ x := by
    funext x
    have hdil : scaledDatumField p α τ x =
        Axi.Nv p.R (train0Prof p) τ x +
          (α 0 • Axi.Nv p.R (frozenProf p 0) τ x +
            α 1 • Axi.Nv p.R (frozenProf p 1) τ x) := by
      have h := RawHeatAux.scaled_datum_eq_Nv_sum p hfro α τ x
      rw [Fin.sum_univ_two] at h
      exact h
    simp only [rawHeatDiff, rawInletSum, Fin.sum_univ_two, rawTrain0Diff, inletFrozenDiff,
      heatScaledDiff, Pi.sub_apply]
    rw [hdil, smul_sub, smul_sub]
    abel
  have hψ0_cd : ContDiff ℝ ∞ (p.train.ψ 0) :=
    RawHeatAux.contDiff_psi_slice p.train le_rfl
  have hbt0_cd : ContDiff ℝ ∞ (train0Prof p) := by
    have heq : train0Prof p =
        Axi.ringStreamProfile p.R (fun n : ℝ × (ℝ × ℝ) => p.train.ψ 0 n.2) := by
      funext n
      change Cons.C03.Concrete.datumProfile p.ε (p.train.ψ 0) n.2 = _
      rw [(inv_inv p.ε).symm]
      exact RawHeatAux.datumProfile_eq_ringStreamProfile_snd hψ0_cd n
    rw [heq]
    exact inletCD_ringStreamProfile (hψ0_cd.comp contDiff_snd)
  have hbf_cd : ∀ i : Fin 2, ContDiff ℝ ∞ (frozenProf p i) := by
    intro i
    have heq : frozenProf p i =
        Axi.ringStreamProfile p.R (fun n : ℝ × (ℝ × ℝ) => p.frozenStream i n.2) := by
      funext n
      change Cons.C03.Concrete.datumProfile p.ε (p.frozenStream i) n.2 = _
      rw [(inv_inv p.ε).symm]
      exact RawHeatAux.datumProfile_eq_ringStreamProfile_snd (hfro i) n
    rw [heq]
    exact inletCD_ringStreamProfile ((hfro i).comp contDiff_snd)
  have hNv_bt0_at : ContDiffAt ℝ j (Axi.Nv p.R (train0Prof p) τ) y := by
    have hon : ContDiffOn ℝ ∞ (Axi.Nv p.R (train0Prof p) τ) Axi.axisᶜ := by
      rw [ChartJetsAux.Nv_eq_fun]
      exact (ChartJetsAux.contDiffOn_sqrt_age hR0).smul
        (ChartJetsAux.contDiffOn_frameL.clm_apply
          (ChartJetsAux.contDiffOn_comp_chart hbt0_cd hR0 τ))
    exact (hon.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le (by simp)
  have hNv_bf_at : ∀ i : Fin 2, ContDiffAt ℝ j (Axi.Nv p.R (frozenProf p i) τ) y := by
    intro i
    have hon : ContDiffOn ℝ ∞ (Axi.Nv p.R (frozenProf p i) τ) Axi.axisᶜ := by
      rw [ChartJetsAux.Nv_eq_fun]
      exact (ChartJetsAux.contDiffOn_sqrt_age hR0).smul
        (ChartJetsAux.contDiffOn_frameL.clm_apply
          (ChartJetsAux.contDiffOn_comp_chart (hbf_cd i) hR0 τ))
    exact (hon.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le (by simp)
  have ha_dil_at : ContDiffAt ℝ j (scaledDatumField p α τ) y := by
    have hon : ContDiffOn ℝ ∞ (scaledDatumField p α τ) {0}ᶜ :=
      (ha.smooth.comp (contDiff_id.const_smul (Real.exp (τ / 2))).contDiffOn
        (fun x hx => smul_ne_zero (Real.exp_pos _).ne' hx)).const_smul (Real.exp (τ / 2))
    exact (hon.contDiffAt (isOpen_compl_singleton.mem_nhds hy_ne0)).of_le (by simp)
  have hHa_cd : ContDiff ℝ ∞ (UnforcedLeray.Blueprint.heatProfile p.ν (p.datum α) τ) :=
    Heat.simHeat_contDiff p.ν_pos hv_inv.heatAdmissible τ
  have hc_Draw : ContDiffAt ℝ j (rawTrain0Diff p τ) y :=
    ((hRaw_cd τ).contDiffAt.of_le (by simp)).sub hNv_bt0_at
  have hc_Din0 : ContDiffAt ℝ j (inletFrozenDiff p 0 τ) y :=
    ((hInl_cd 0 τ).contDiffAt.of_le (by simp)).sub (hNv_bf_at 0)
  have hc_Din1 : ContDiffAt ℝ j (inletFrozenDiff p 1 τ) y :=
    ((hInl_cd 1 τ).contDiffAt.of_le (by simp)).sub (hNv_bf_at 1)
  have hc_Dheat : ContDiffAt ℝ j (heatScaledDiff p α τ) y :=
    (hHa_cd.contDiffAt.of_le (by simp)).sub ha_dil_at
  have hD_ext : iteratedFDeriv ℝ j (rawHeatDiff p α τ) y =
      (iteratedFDeriv ℝ j (rawTrain0Diff p τ) y +
        (α 0 • iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y +
          α 1 • iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y)) -
        iteratedFDeriv ℝ j (heatScaledDiff p α τ) y := by
    rw [hF_ext_eq]
    exact iteratedFDeriv_lin_comb hc_Draw hc_Din0 hc_Din1 hc_Dheat
  have hb_Draw : (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawTrain0Diff p τ) y‖ ≤
      B_far + B_rnear + B_dnear := by
    by_cases hs1 : Axi.age p.R y ≤ 1
    · have hf := hB_far τ y hy hs1
      linarith only [hf, hB_rnear0, hB_dnear0]
    · have hs_gt1 : 1 < Axi.age p.R y := not_le.1 hs1
      have hsub_raw : iteratedFDeriv ℝ j (rawTrain0Diff p τ) y =
          iteratedFDeriv ℝ j (p.raw τ) y -
            iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y := by
        change iteratedFDeriv ℝ j (p.raw τ - Axi.Nv p.R (train0Prof p) τ) y = _
        exact iteratedFDeriv_sub_apply
          ((hRaw_cd τ).contDiffAt.of_le (by simp)) hNv_bt0_at
      rw [hsub_raw]
      have b1 := hB_rnear τ y hy hs_gt1 hyR
      have b2 := hB_dnear τ y hy hs_gt1.le hyR
      have hw3_nn : 0 ≤ (1 + ‖y‖) ^ 3 := by positivity
      have hns := norm_sub_le (iteratedFDeriv ℝ j (p.raw τ) y)
        (iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y)
      have hprod : (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.raw τ) y -
          iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y‖ ≤
          (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.raw τ) y‖ +
            (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y‖ := by
        calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.raw τ) y -
              iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y‖
            ≤ (1 + ‖y‖) ^ 3 * (‖iteratedFDeriv ℝ j (p.raw τ) y‖ +
                ‖iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y‖) :=
              mul_le_mul_of_nonneg_left hns hw3_nn
          _ = (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (p.raw τ) y‖ +
                (1 + ‖y‖) ^ 3 *
                  ‖iteratedFDeriv ℝ j (Axi.Nv p.R (train0Prof p) τ) y‖ := by ring
      linarith only [hprod, b1, b2, hB_far0]
  have hb_Din0 : |α 0| * ((1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y‖) ≤
      |α 0| * M_in0 :=
    mul_le_mul_of_nonneg_left (hM_in0 τ y hy hyH) (abs_nonneg (α 0))
  have hb_Din1 : |α 1| * ((1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y‖) ≤
      |α 1| * M_in1 :=
    mul_le_mul_of_nonneg_left (hM_in1 τ y hy hyH) (abs_nonneg (α 1))
  have hb_Dheat : (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (heatScaledDiff p α τ) y‖ ≤ K_h :=
    hK_h τ y hy1
  have htri_ext : ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖ ≤
      ‖iteratedFDeriv ℝ j (rawTrain0Diff p τ) y‖ +
        (|α 0| * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y‖ +
          |α 1| * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y‖) +
        ‖iteratedFDeriv ℝ j (heatScaledDiff p α τ) y‖ := by
    rw [hD_ext]
    have s1 := norm_sub_le
      (iteratedFDeriv ℝ j (rawTrain0Diff p τ) y +
        (α 0 • iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y +
          α 1 • iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y))
      (iteratedFDeriv ℝ j (heatScaledDiff p α τ) y)
    have s2 := norm_add_le (iteratedFDeriv ℝ j (rawTrain0Diff p τ) y)
      (α 0 • iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y +
        α 1 • iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y)
    have s3 := norm_add_le (α 0 • iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y)
      (α 1 • iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y)
    rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs] at s3
    linarith only [s1, s2, s3]
  have hw3_nn : 0 ≤ (1 + ‖y‖) ^ 3 := by positivity
  have hmul_tri : (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖ ≤
      (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawTrain0Diff p τ) y‖ +
        |α 0| * ((1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y‖) +
        |α 1| * ((1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y‖) +
        (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (heatScaledDiff p α τ) y‖ := by
    calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawHeatDiff p α τ) y‖
        ≤ (1 + ‖y‖) ^ 3 * (‖iteratedFDeriv ℝ j (rawTrain0Diff p τ) y‖ +
            (|α 0| * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y‖ +
              |α 1| * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y‖) +
            ‖iteratedFDeriv ℝ j (heatScaledDiff p α τ) y‖) :=
          mul_le_mul_of_nonneg_left htri_ext hw3_nn
      _ = (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (rawTrain0Diff p τ) y‖ +
            |α 0| * ((1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 0 τ) y‖) +
            |α 1| * ((1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (inletFrozenDiff p 1 τ) y‖) +
            (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ j (heatScaledDiff p α τ) y‖ := by ring
  linarith only [hmul_tri, hb_Draw, hb_Din0, hb_Din1, hb_Dheat]

/-- **`PartII-b:B3/2/1/1`**: proof of `RawHeatComparison` (`short-bg:raw-heat`, SP 2586-2603). -/
theorem rawHeatComparison_proof : UnforcedLeray.Short.IIb.RawHeatComparison := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, H_dat⟩ := datum_facts_atBallStates Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, H_rawJ⟩ := rawJointSmooth Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, hν₃, H_inlJ⟩ := inletJointSmooth Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₄, hν₄, H_rnear⟩ := RawHeatAux.raw_near_axis_decay3
  obtain ⟨ν₅, hν₅, H_rfar⟩ := RawHeatAux.raw_sub_train0_far_decay3
  obtain ⟨ν₆, hν₆, H_t0near⟩ := RawHeatAux.train0Datum_near_decay3
  obtain ⟨ν₇, hν₇, H_raw1⟩ := RawAndInletL4.rawDecayAll_of
    RawHeatAux.trainStreamWtdBdd_uncond RawHeatAux.trainHeatRemWtd_uncond dm dp
  obtain ⟨_, _, _, -, -, hper0⟩ := frozenStreamBounds lam q hq 0
  set ν₀ : ℝ := min (min (min ν₁ ν₂) (min ν₃ ν₄)) (min (min ν₅ ν₆) (min ν₇ 1))
  have hν₀ : 0 < ν₀ :=
    lt_min (lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄))
      (lt_min (lt_min hν₅ hν₆) (lt_min hν₇ one_pos))
  refine ⟨ν₀, hν₀, fun p d hreg hν hS hmode z hPE hzn => ?_⟩
  have hν₁' : p.ν ≤ ν₁ :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν₂' : p.ν ≤ ν₂ :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν₃' : p.ν ≤ ν₃ :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν₄' : p.ν ≤ ν₄ :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν₅' : p.ν ≤ ν₅ :=
    hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν₆' : p.ν ≤ ν₆ :=
    hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν₇' : p.ν ≤ ν₇ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν1 : p.ν ≤ 1 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hR1 : 1 ≤ p.R := RawAndInletL4.one_le_R_of hreg
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (pow_pos p.ν_pos 2)]
    nlinarith [p.ν_pos, hν1]
  have hfro : ∀ i : Fin 2, ContDiff ℝ ∞ (p.frozenStream i) :=
    fun i => inletCD_frozenStream (hper0 p.c hc1).1 hmode i
  obtain ⟨ha, -, -, -⟩ := H_dat p d hreg hν₁' hS hmode z hPE hzn
  obtain ⟨C_inv, hv_inv⟩ := invBound_of_isB3Datum ha
  obtain ⟨C_id4, hInv4⟩ := B3RemH2Sub.exists_invDistClass4_of_isB3Datum ha
  have hInv2 : Heat.InvDistClass 2 C_id4 (p.datum (p.coord z)) :=
    hInv4.of_le (by norm_num)
  have hRaw_j : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) :=
    H_rawJ p d hreg hν₂' hS hmode 0
  have hInl_j : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    fun i => H_inlJ p d hreg hν₃' hS hmode i
  have hRaw_cd : ∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ) :=
    fun τ => slice_contDiff_of_joint hRaw_j τ
  have hInl_cd : ∀ (i : Fin 2) (τ : ℝ), ContDiff ℝ ∞ (p.inlet i τ) :=
    fun i τ => slice_contDiff_of_joint (hInl_j i) τ
  obtain ⟨hF_cd_inf, hF_cont0, hF_cont1, hF_cont2⟩ :=
    rawHeatDiff_regularity p (p.coord z) hv_inv hRaw_j hInl_j
  have hF_cd : ∀ τ : ℝ, ContDiff ℝ 2 (rawHeatDiff p (p.coord z) τ) :=
    fun τ => (hF_cd_inf τ).of_le (by simp)
  have hF_bd : ∀ j : ℕ, j ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (τ : ℝ) (y : Space),
      ‖iteratedFDeriv ℝ j (rawHeatDiff p (p.coord z) τ) y‖ ≤ M * ((1 + ‖y‖) ^ 3)⁻¹ := by
    intro j hj
    obtain ⟨B_raw1, hB_raw10, hB_raw1⟩ := H_raw1 p d hreg hν₇' j
    obtain ⟨B_in1, hB_in10, hB_in1⟩ :=
      RawAndInletL4.inletDecayAll lam q hq j p hmode hc1 hR1
    obtain ⟨K_sim_raw, hK_sim_raw⟩ := Heat.simHeat_decay p.ν_pos hInv2 hj
    obtain ⟨B_far, hB_far0, hB_far⟩ := H_rfar dm dp p d hreg hν₅' j hj
    obtain ⟨B_rnear, hB_rnear0, hB_rnear⟩ := H_rnear dm dp p d hreg hν₄' j
    obtain ⟨B_dnear, hB_dnear0, hB_dnear⟩ := H_t0near dm dp p d hreg hν₆' j
    obtain ⟨M_in0, hM_in00, hM_in0⟩ :=
      RawHeatAux.inlet_sub_frozenDatum_decay hq hreg hν1 hmode (hfro 0) j
    obtain ⟨M_in1, hM_in10, hM_in1⟩ :=
      RawHeatAux.inlet_sub_frozenDatum_decay hq hreg hν1 hmode (hfro 1) j
    obtain ⟨K_h, hK_h0, hK_h⟩ := heat_diff_offAxis_decay3 p.ν_pos ha hj
    obtain ⟨R_cut, hR_cut_def⟩ :
        ∃ x : ℝ, x = max 2 (max (2 * p.R) (2 * (p.R / √(p.H / 4)))) := ⟨_, rfl⟩
    have hR_cut2 : 2 ≤ R_cut := hR_cut_def ▸ le_max_left _ _
    have hR_cut0 : 0 ≤ R_cut := by linarith only [hR_cut2]
    have hR_cutR : 2 * p.R ≤ R_cut :=
      hR_cut_def ▸ (le_max_left _ _).trans (le_max_right _ _)
    have hR_cutH : 2 * (p.R / √(p.H / 4)) ≤ R_cut :=
      hR_cut_def ▸ (le_max_right _ _).trans (le_max_right _ _)
    obtain ⟨M_small, hM_small_def⟩ : ∃ x : ℝ, x = (1 + R_cut) ^ 2 *
        (B_raw1 + |p.coord z 0| * B_in1 + |p.coord z 1| * B_in1 + max K_sim_raw 0) := ⟨_, rfl⟩
    have hM_small0 : 0 ≤ M_small := by rw [hM_small_def]; positivity
    obtain ⟨M_large, hM_large_def⟩ : ∃ x : ℝ, x = (B_far + B_rnear + B_dnear) +
        (|p.coord z 0| * M_in0 + |p.coord z 1| * M_in1) + K_h := ⟨_, rfl⟩
    have hM_large0 : 0 ≤ M_large := by rw [hM_large_def]; positivity
    refine ⟨M_small + M_large, add_nonneg hM_small0 hM_large0, fun τ => ?_⟩
    refine RawAndInletIteratedDriftSub.inv_pow_decay_of_offAxis
      (hF_cd_inf τ) (fun _ _ => rfl) (fun y hy => ?_)
    by_cases hynorm : ‖y‖ < R_cut
    · have hs := rawHeatDiff_small_radius_bound p (p.coord z) hv_inv hRaw_cd hInl_cd
        hR_cut0 hB_raw10 hB_in10 hB_raw1 hB_in1 hK_sim_raw τ hy hynorm
      rw [← hM_small_def] at hs
      linarith only [hs, hM_large0]
    · have hy_ge : R_cut ≤ ‖y‖ := not_lt.1 hynorm
      have hl := rawHeatDiff_large_radius_bound p (p.coord z) hfro ha hv_inv hRaw_cd hInl_cd
        hB_far0 hB_rnear0 hB_dnear0 hB_far hB_rnear hB_dnear hM_in0 hM_in1 hK_h τ hy
        (by linarith only [hR_cut2, hy_ge]) (hR_cutR.trans hy_ge) (hR_cutH.trans hy_ge)
      rw [← hM_large_def] at hl
      linarith only [hl, hM_small0]
  exact exists_continuous_H2_and_q0E_of_decay3 (rawHeatDiff p (p.coord z))
    hF_cd hF_cont0 hF_cont1 hF_cont2 hF_bd

end UnforcedLeray.Short.IIb

end
