import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairingDefs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing1.PhysCol
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing1.CutDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateBound

/-!
# `PartIII-a:T21/c3/3/1/1/2/2/3/c/1`: frame-column pairing FTC (`FramePairingFTC`)

Source `the November 2 reference manuscript` (SP) lines 2905-2925, 2937-2958.

To differentiate `r ↦ ⟨perE κ (dd ν r) j, Φ(r)⟩_{C_{d(r)}}` for a moving backward free adjoint `Φ`
(`Φ(r) = movingPhi ν φ r` a.e. on `C_{d(r)}`), we pass to physical variables on `C_{ν⁻²}`:
* `⟨perE κ (dd ν q) j, Φ(q)⟩_{C_{d(q)}} = ∫_{C_{ν⁻²}} physFrameE κ ν q j * φ(q)` (`PhysCol.lean`);
* testing `φ` against the transverse-cutoff column `cutCol κ ν R q j = χ_R * physFrameE κ ν q j`
  gives a pairing `cutPair` continuous on `[t₁, s]` (`hφ.strongCont`) and differentiable on
  `(t₁, s)` with derivative `cutRate` continuous on `(t₁, s)` (`CutDeriv.lean`);
* splitting `cutRate` into `∫ physFrameERate * (χ_R * φ)` minus the cutoff commutator
  `∫ colCommKer * φ`, `LadTrainBdd` and `physFrameE_uniform_xNorm` bound `cutRate` uniformly in
  `R ≥ 1` and `q ∈ [t₁, s]` and show the `O(R⁻¹)` commutator vanishes as `R → ∞`;
* FTC on `[r, s']` at finite `R ≥ 1` followed by dominated convergence as `R → ∞` and rescaling back
  to `C_{d(q)}` (`physFrameERate_eq_jscale`, `cell_pair_jscale_movingPhi`) yields `FramePairingFTC`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2WeakEqFrame

namespace FramePairing1Aux

/-- Cutoff commutator kernel `ν(2 ∇χ_R·∇E_phys + (Δχ_R) E_phys) - (v·∇χ_R) E_phys`. -/
def colCommKer (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (R q : ℝ) (j : Fin 2)
    (x : ℝ × ℝ) : ℂ :=
  (ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (physFrameE κ ν q j) x +
      (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (physFrameE κ ν q j) x) +
    (lapP (ladCut R) x : ℂ) * physFrameE κ ν q j x) +
  ((-(tr.v q x 0 * B0579.pd 0 (ladCut R) x + tr.v q x 1 * B0579.pd 1 (ladCut R) x) : ℝ) : ℂ) *
    physFrameE κ ν q j x

/-- Pointwise Leibniz decomposition of the `cutRate` integrand into main rate minus commutator. -/
lemma cutRate_integrand_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q R : ℝ} (hν : 0 < ν) (hq : 0 ≤ q) (hR : 0 < R)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (φ : ℝ → ℝ × ℝ → ℂ)
    (j : Fin 2) (x : ℝ × ℝ) :
    ((ladCut R x : ℂ) * ladDt (fun q' x' => physFrameE κ ν q' j x') q x -
        (ν : ℂ) * ladLapCx (cutCol κ ν R q j) x +
        ladTransport tr q (cutCol κ ν R q j) x) * φ q x =
      physFrameERate κ tr q j x * ((ladCut R x : ℂ) * φ q x) -
        colCommKer κ tr R q j x * φ q x := by
  obtain ⟨_, _, hK⟩ := ladCutProps
  have hχ : ContDiff ℝ ∞ (ladCut R) := ((hK R hR).1 (ν ^ (-2 : ℝ))).smooth
  have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hq)
  have hE : ContDiff ℝ ∞ (physFrameE κ ν q j) := contDiff_physFrameE_slice hκ hν ha j
  have hcol : cutCol κ ν R q j = fun y => (ladCut R y : ℂ) * physFrameE κ ν q j y := rfl
  unfold physFrameERate ladTransport colCommKer
  rw [hcol, RateSplitAux.lap_cut_mul hχ hE x, RateSplitAux.pdCx_cut_mul hχ hE 0 x,
    RateSplitAux.pdCx_cut_mul hχ hE 1 x]
  push_cast
  ring

/-- Spatial continuity of `colCommKer κ tr R q j` for `q ≥ 0` and `R > 0`. -/
lemma continuous_colCommKer {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q R : ℝ} (hν : 0 < ν) (hq : 0 ≤ q) (hR : 0 < R)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (j : Fin 2) :
    Continuous (colCommKer κ tr R q j) := by
  obtain ⟨_, _, hK⟩ := ladCutProps
  have hχ : ContDiff ℝ ∞ (ladCut R) := ((hK R hR).1 (ν ^ (-2 : ℝ))).smooth
  have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hq)
  have hE : ContDiff ℝ ∞ (physFrameE κ ν q j) := contDiff_physFrameE_slice hκ hν ha j
  have hpd0 : Continuous (fun x => (B0579.pd 0 (ladCut R) x : ℂ)) :=
    Complex.continuous_ofReal.comp (ForceMemXAux.contDiff_pd hχ 0).continuous
  have hpd1 : Continuous (fun x => (B0579.pd 1 (ladCut R) x : ℂ)) :=
    Complex.continuous_ofReal.comp (ForceMemXAux.contDiff_pd hχ 1).continuous
  have hlap : Continuous (fun x => (lapP (ladCut R) x : ℂ)) := by
    unfold lapP
    exact Complex.continuous_ofReal.comp
      (((ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 0) 0).continuous).add
        ((ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 1) 1).continuous))
  have hv_k : ∀ k : Fin 2, Continuous (fun x : ℝ × ℝ => tr.v q x k) := by
    intro k
    have hvS : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    have hslice : ContinuousOn (fun x : ℝ × ℝ => tr.v q x) univ :=
      hvS.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ _ => ⟨hq, mem_univ _⟩)
    exact ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp
      (continuousOn_univ.1 hslice)
  have hv_cut : Continuous (fun x : ℝ × ℝ =>
      ((-(tr.v q x 0 * B0579.pd 0 (ladCut R) x +
          tr.v q x 1 * B0579.pd 1 (ladCut R) x) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((hv_k 0).mul (ForceMemXAux.contDiff_pd hχ 0).continuous).add
        ((hv_k 1).mul (ForceMemXAux.contDiff_pd hχ 1).continuous)).neg
  have hE0 : Continuous (pdCx 0 (physFrameE κ ν q j)) :=
    (RateSplitAux.contDiff_pdCx hE 0).continuous
  have hE1 : Continuous (pdCx 1 (physFrameE κ ν q j)) :=
    (RateSplitAux.contDiff_pdCx hE 1).continuous
  unfold colCommKer
  exact (continuous_const.mul ((continuous_const.mul ((hpd0.mul hE0).add (hpd1.mul hE1))).add
    (hlap.mul hE.continuous))).add (hv_cut.mul hE.continuous)

/-- Pointwise bound on `‖colCommKer * φ‖` on `B0579.cell (ν⁻²)` for `R ≥ 1` and `q ∈ [0, s]`. -/
lemma colCommKer_mul_norm_le (κ : PlanarFrameKernels) {ν m s C_tr K_cut R q : ℝ}
    (hK0 : 0 ≤ K_cut)
    (hp : ∀ R' : ℝ, 0 < R' → ∀ (x : ℝ × ℝ) (k : Fin 2), |B0579.pd k (ladCut R') x| ≤ K_cut / R')
    (hl : ∀ R' : ℝ, 0 < R' → ∀ x : ℝ × ℝ, |lapP (ladCut R') x| ≤ K_cut / R' ^ 2)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} (hBdd : LadTrainBdd tr m s C_tr)
    (hq : q ∈ Icc (0 : ℝ) s) (hR1 : 1 ≤ R) (φ : ℝ → ℝ × ℝ → ℂ) (j : Fin 2)
    {x : ℝ × ℝ} (hx : x ∈ B0579.cell (ν ^ (-2 : ℝ))) :
    ‖colCommKer κ tr R q j x * φ q x‖ ≤
      (3 * |ν| * K_cut + 2 * |C_tr| * K_cut) * R⁻¹ *
        (‖physFrameE κ ν q j x‖ * ‖φ q x‖ +
          ‖pdCx 0 (physFrameE κ ν q j) x‖ * ‖φ q x‖ +
          ‖pdCx 1 (physFrameE κ ν q j) x‖ * ‖φ q x‖) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRinv0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  set c_tr : ℝ := |C_tr|
  have hc_tr0 : 0 ≤ c_tr := abs_nonneg C_tr
  have hp0 : |B0579.pd 0 (ladCut R) x| ≤ K_cut * R⁻¹ := by
    simpa [div_eq_mul_inv] using hp R hR0 x 0
  have hp1 : |B0579.pd 1 (ladCut R) x| ≤ K_cut * R⁻¹ := by
    simpa [div_eq_mul_inv] using hp R hR0 x 1
  have hL : |lapP (ladCut R) x| ≤ K_cut * R⁻¹ := by
    have h := hl R hR0 x
    have e : K_cut / R ^ 2 = (K_cut * R⁻¹) * R⁻¹ := by ring
    rw [e] at h
    exact h.trans (mul_le_of_le_one_right (mul_nonneg hK0 hRinv0) hRinv1)
  have hvx := (hBdd q hq x hx).1
  have hvv : |-(tr.v q x 0 * B0579.pd 0 (ladCut R) x + tr.v q x 1 * B0579.pd 1 (ladCut R) x)| ≤
      2 * c_tr * K_cut * R⁻¹ := by
    rw [abs_neg]
    calc |tr.v q x 0 * B0579.pd 0 (ladCut R) x + tr.v q x 1 * B0579.pd 1 (ladCut R) x|
        ≤ |tr.v q x 0 * B0579.pd 0 (ladCut R) x| + |tr.v q x 1 * B0579.pd 1 (ladCut R) x| :=
          abs_add_le _ _
      _ = |tr.v q x 0| * |B0579.pd 0 (ladCut R) x| +
            |tr.v q x 1| * |B0579.pd 1 (ladCut R) x| := by rw [abs_mul, abs_mul]
      _ ≤ c_tr * (K_cut * R⁻¹) + c_tr * (K_cut * R⁻¹) :=
          add_le_add
            (mul_le_mul ((hvx 0).trans (le_abs_self C_tr)) hp0 (abs_nonneg _) hc_tr0)
            (mul_le_mul ((hvx 1).trans (le_abs_self C_tr)) hp1 (abs_nonneg _) hc_tr0)
      _ = 2 * c_tr * K_cut * R⁻¹ := by ring
  have hcomm := CommVanishAux.comm_pointwise ν c_tr K_cut R
    (B0579.pd 0 (ladCut R) x) (B0579.pd 1 (ladCut R) x) (lapP (ladCut R) x)
    (-(tr.v q x 0 * B0579.pd 0 (ladCut R) x + tr.v q x 1 * B0579.pd 1 (ladCut R) x))
    hK0 hc_tr0 hRinv0 hp0 hp1 hL hvv
    (pdCx 0 (physFrameE κ ν q j) x) (pdCx 1 (physFrameE κ ν q j) x) (physFrameE κ ν q j x)
  rw [norm_mul]
  calc ‖colCommKer κ tr R q j x‖ * ‖φ q x‖
      ≤ ((3 * |ν| * K_cut + 2 * c_tr * K_cut) * R⁻¹ *
          (‖physFrameE κ ν q j x‖ + ‖pdCx 0 (physFrameE κ ν q j) x‖ +
            ‖pdCx 1 (physFrameE κ ν q j) x‖)) * ‖φ q x‖ :=
        mul_le_mul_of_nonneg_right hcomm (norm_nonneg _)
    _ = (3 * |ν| * K_cut + 2 * c_tr * K_cut) * R⁻¹ *
          (‖physFrameE κ ν q j x‖ * ‖φ q x‖ +
            ‖pdCx 0 (physFrameE κ ν q j) x‖ * ‖φ q x‖ +
            ‖pdCx 1 (physFrameE κ ν q j) x‖ * ‖φ q x‖) := by ring

/-- Pointwise `R → ∞` limit and uniform `R ≥ 1` bound for `cutRate` at any `q ∈ [t₁, s]`. -/
lemma cutRate_tendsto_and_bound {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m t₁ s C_tr M_col B_φ : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    (hMcol0 : 0 ≤ M_col) (hBφ0 : 0 ≤ B_φ)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} (hBdd : LadTrainBdd tr m s C_tr)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ)
    (hBφ : ∀ q' ∈ Icc t₁ s, (xNorm (ν ^ (-2 : ℝ)) (-m) (φ q')).toReal ≤ B_φ)
    (K_cut : ℝ) (hK0 : 0 ≤ K_cut)
    (hp : ∀ R' : ℝ, 0 < R' → ∀ (x : ℝ × ℝ) (k : Fin 2), |B0579.pd k (ladCut R') x| ≤ K_cut / R')
    (hl : ∀ R' : ℝ, 0 < R' → ∀ x : ℝ × ℝ, |lapP (ladCut R') x| ≤ K_cut / R' ^ 2)
    (j : Fin 2) {q : ℝ} (hq : q ∈ Icc t₁ s)
    (hE_m : MemLp (physFrameE κ ν q j) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hE_n : xNorm (ν ^ (-2 : ℝ)) m (physFrameE κ ν q j) ≤ ENNReal.ofReal M_col)
    (hpd_m : ∀ k : Fin 2,
      MemLp (pdCx k (physFrameE κ ν q j)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hpd_n : ∀ k : Fin 2,
      xNorm (ν ^ (-2 : ℝ)) m (pdCx k (physFrameE κ ν q j)) ≤ ENNReal.ofReal M_col)
    (hR_m : MemLp (physFrameERate κ tr q j) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hR_n : xNorm (ν ^ (-2 : ℝ)) m (physFrameERate κ tr q j) ≤ ENNReal.ofReal M_col) :
    Tendsto (fun R => cutRate κ tr φ R j q) atTop
      (𝓝 (∫ x in B0579.cell (ν ^ (-2 : ℝ)), physFrameERate κ tr q j x * φ q x)) ∧
    ∀ R : ℝ, 1 ≤ R →
      ‖cutRate κ tr φ R j q‖ ≤
        M_col * B_φ + (3 * |ν| * K_cut + 2 * |C_tr| * K_cut) * (3 * (M_col * B_φ)) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hq0 : 0 ≤ q := ht₁.trans hq.1
  have hq_0s : q ∈ Icc (0 : ℝ) s := ⟨hq0, hq.2⟩
  have hφ_m : MemLp (φ q) 2 (B0579.cellMeasure c (-m)) := hφ.memX q hq
  have hφ_toR : (xNorm c (-m) (φ q)).toReal ≤ B_φ := hBφ q hq
  have hφ_nn : 0 ≤ (xNorm c (-m) (φ q)).toReal := ENNReal.toReal_nonneg
  have toReal_le_M : ∀ {F : ℝ × ℝ → ℂ}, xNorm c m F ≤ ENNReal.ofReal M_col →
      (xNorm c m F).toReal ≤ M_col := fun h =>
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hMcol0)
  -- Integrability and Cauchy-Schwarz bound for the 3-term commutator majorant
  have hI_E := CommVanishAux.integrableOn_cell_norm_mul c m hE_m hφ_m
  have hI_0 := CommVanishAux.integrableOn_cell_norm_mul c m (hpd_m 0) hφ_m
  have hI_1 := CommVanishAux.integrableOn_cell_norm_mul c m (hpd_m 1) hφ_m
  set maj : ℝ × ℝ → ℝ := fun x =>
    ‖physFrameE κ ν q j x‖ * ‖φ q x‖ +
      ‖pdCx 0 (physFrameE κ ν q j) x‖ * ‖φ q x‖ +
      ‖pdCx 1 (physFrameE κ ν q j) x‖ * ‖φ q x‖
  have hImaj : IntegrableOn maj (B0579.cell c) := (hI_E.add hI_0).add hI_1
  have hmaj_int_le : ∫ x in B0579.cell c, maj x ≤ 3 * (M_col * B_φ) := by
    have hcs_E : ∫ x in B0579.cell c, ‖physFrameE κ ν q j x‖ * ‖φ q x‖ ≤ M_col * B_φ :=
      (RateBoundAux.cs_norm c m hE_m hφ_m).trans
        (mul_le_mul (toReal_le_M hE_n) hφ_toR hφ_nn hMcol0)
    have hcs_0 : ∫ x in B0579.cell c, ‖pdCx 0 (physFrameE κ ν q j) x‖ * ‖φ q x‖ ≤ M_col * B_φ :=
      (RateBoundAux.cs_norm c m (hpd_m 0) hφ_m).trans
        (mul_le_mul (toReal_le_M (hpd_n 0)) hφ_toR hφ_nn hMcol0)
    have hcs_1 : ∫ x in B0579.cell c, ‖pdCx 1 (physFrameE κ ν q j) x‖ * ‖φ q x‖ ≤ M_col * B_φ :=
      (RateBoundAux.cs_norm c m (hpd_m 1) hφ_m).trans
        (mul_le_mul (toReal_le_M (hpd_n 1)) hφ_toR hφ_nn hMcol0)
    have hadd : ∫ x in B0579.cell c, maj x =
        (∫ x in B0579.cell c, ‖physFrameE κ ν q j x‖ * ‖φ q x‖) +
          (∫ x in B0579.cell c, ‖pdCx 0 (physFrameE κ ν q j) x‖ * ‖φ q x‖) +
          (∫ x in B0579.cell c, ‖pdCx 1 (physFrameE κ ν q j) x‖ * ‖φ q x‖) := by
      have h1 := integral_add (hI_E.add hI_0) hI_1
      have h2 := integral_add hI_E hI_0
      dsimp only [Pi.add_apply] at h1 h2
      dsimp only [maj]
      rw [h1, h2]
    linarith [hcs_E, hcs_0, hcs_1, hadd]
  have hmaj_nn : 0 ≤ ∫ x in B0579.cell c, maj x :=
    setIntegral_nonneg (B0579.measurableSet_cell c) fun x _ => by
      dsimp only [maj]; positivity
  -- Split `cutRate` and bound both pieces for `R ≥ 1`
  set K_comm : ℝ := 3 * |ν| * K_cut + 2 * |C_tr| * K_cut
  have hKcomm0 : 0 ≤ K_comm := by positivity
  have hsplit_and_comm : ∀ R : ℝ, 1 ≤ R →
      cutRate κ tr φ R j q =
        (∫ x in B0579.cell c, physFrameERate κ tr q j x * ((ladCut R x : ℂ) * φ q x)) -
          ∫ x in B0579.cell c, colCommKer κ tr R q j x * φ q x ∧
      ‖∫ x in B0579.cell c, colCommKer κ tr R q j x * φ q x‖ ≤
        K_comm * R⁻¹ * (3 * (M_col * B_φ)) := by
    intro R hR1
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hRinv0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
    have hhG : MemLp (fun x => (ladCut R x : ℂ) * φ q x) 2 (B0579.cellMeasure c (-m)) := by
      refine hφ_m.mono
        ((Complex.continuous_ofReal.comp (CutLimitAux.continuous_cut R)).aestronglyMeasurable.mul
          hφ_m.1) (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (CutLimitAux.nonneg R x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (CutLimitAux.le_one R x)
    have hint_main : IntegrableOn
        (fun x => physFrameERate κ tr q j x * ((ladCut R x : ℂ) * φ q x)) (B0579.cell c) :=
      CutLimitAux.integrable_complex hR_m hhG
    have hpt_comm : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        ‖colCommKer κ tr R q j x * φ q x‖ ≤ (K_comm * R⁻¹) * maj x := by
      rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
      exact Eventually.of_forall fun x hx =>
        colCommKer_mul_norm_le κ hK0 hp hl hBdd hq_0s hR1 φ j hx
    have hmeas_comm : AEStronglyMeasurable (fun x => colCommKer κ tr R q j x * φ q x)
        (volume.restrict (B0579.cell c)) :=
      (continuous_colCommKer hκ hν hq0 hR0 tr j).aestronglyMeasurable.mul
        (hφ_m.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m)))
    have hint_comm : IntegrableOn (fun x => colCommKer κ tr R q j x * φ q x) (B0579.cell c) :=
      (hImaj.const_mul (K_comm * R⁻¹)).mono' hmeas_comm hpt_comm
    have hsplit : cutRate κ tr φ R j q =
        (∫ x in B0579.cell c, physFrameERate κ tr q j x * ((ladCut R x : ℂ) * φ q x)) -
          ∫ x in B0579.cell c, colCommKer κ tr R q j x * φ q x := by
      unfold cutRate
      rw [integral_congr_ae (Eventually.of_forall (cutRate_integrand_eq hκ hν hq0 hR0 tr φ j)),
        integral_sub hint_main hint_comm]
    have hcomm_le : ‖∫ x in B0579.cell c, colCommKer κ tr R q j x * φ q x‖ ≤
        K_comm * R⁻¹ * (3 * (M_col * B_φ)) := by
      calc ‖∫ x in B0579.cell c, colCommKer κ tr R q j x * φ q x‖
          ≤ ∫ x in B0579.cell c, ‖colCommKer κ tr R q j x * φ q x‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in B0579.cell c, (K_comm * R⁻¹) * maj x :=
            integral_mono_ae hint_comm.norm (hImaj.const_mul _) hpt_comm
        _ = (K_comm * R⁻¹) * ∫ x in B0579.cell c, maj x := integral_const_mul _ _
        _ ≤ (K_comm * R⁻¹) * (3 * (M_col * B_φ)) :=
            mul_le_mul_of_nonneg_left hmaj_int_le (mul_nonneg hKcomm0 hRinv0)
    exact ⟨hsplit, hcomm_le⟩
  refine ⟨?_, ?_⟩
  · -- Pointwise limit as `R → ∞`
    have hlim_main := ladCutLimit c m (physFrameERate κ tr q j) (φ q) hR_m hφ_m
    have hlim_comm : Tendsto
        (fun R => ∫ x in B0579.cell c, colCommKer κ tr R q j x * φ q x) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h0 : Tendsto (fun R : ℝ => (K_comm * (3 * (M_col * B_φ))) * R⁻¹) atTop (𝓝 0) := by
        simpa using tendsto_inv_atTop_zero.const_mul (K_comm * (3 * (M_col * B_φ)))
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
      exact ((hsplit_and_comm R hR1).2).trans_eq (by ring)
    have hlim_sub := hlim_main.sub hlim_comm
    rw [sub_zero] at hlim_sub
    refine hlim_sub.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
    exact ((hsplit_and_comm R hR1).1).symm
  · -- Uniform bound for `R ≥ 1`
    intro R hR1
    obtain ⟨hsplit, hcomm_le⟩ := hsplit_and_comm R hR1
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
    have hmain_le : ‖∫ x in B0579.cell c,
        physFrameERate κ tr q j x * ((ladCut R x : ℂ) * φ q x)‖ ≤ M_col * B_φ := by
      have hcut_abs : ∀ x : ℝ × ℝ, |ladCut R x| ≤ 1 := fun x =>
        abs_le.2 ⟨by linarith [CutLimitAux.nonneg R x], CutLimitAux.le_one R x⟩
      exact (RateBoundAux.cs_cut c m (CutLimitAux.continuous_cut R) hcut_abs hR_m hφ_m).trans
        (mul_le_mul (toReal_le_M hR_n) hφ_toR hφ_nn hMcol0)
    have hcomm_le1 : ‖∫ x in B0579.cell c, colCommKer κ tr R q j x * φ q x‖ ≤
        K_comm * (3 * (M_col * B_φ)) := by
      refine hcomm_le.trans ?_
      calc K_comm * R⁻¹ * (3 * (M_col * B_φ))
          = (K_comm * (3 * (M_col * B_φ))) * R⁻¹ := by ring
        _ ≤ (K_comm * (3 * (M_col * B_φ))) * 1 :=
            mul_le_mul_of_nonneg_left hRinv1 (by positivity)
        _ = K_comm * (3 * (M_col * B_φ)) := mul_one _
    rw [hsplit]
    exact (norm_sub_le _ _).trans (add_le_add hmain_le hcomm_le1)

end FramePairing1Aux

theorem framePairingFTC_proof (κ : PlanarFrameKernels) : UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.FramePairingFTC κ := by
  intro hκ P _hP m hm _K
  refine ⟨1, le_rfl, fun b hb => ⟨1, one_pos, ?_⟩⟩
  intro ν hν tr _hbuc hBddAll t₁ s ht₁ hts hbs Γ Φ _hΓ hΦ_mov r hr s' hs' j
  rcases eq_or_lt_of_le hs'.1 with rfl | hrs'_lt
  · rw [sub_self, Ioc_self, setIntegral_empty]
  obtain ⟨φ, hφ, hΦ_ae⟩ := hΦ_mov
  let c : ℝ := ν ^ (-2 : ℝ)
  have hs0 : 0 ≤ s := ht₁.trans hts
  have hs'_Icc : s' ∈ Icc t₁ s := ⟨hr.1.trans hs'.1, hs'.2⟩
  obtain ⟨C_tr, hBdd⟩ := hBddAll s hs0
  obtain ⟨K_cut, hK0, hK⟩ := ladCutProps
  have hp_cut : ∀ R' : ℝ, 0 < R' → ∀ (x : ℝ × ℝ) (k : Fin 2),
      |B0579.pd k (ladCut R') x| ≤ K_cut / R' :=
    fun R' hR' x k => (hK R' hR').2.2.2.2.1 x k
  have hl_cut : ∀ R' : ℝ, 0 < R' → ∀ x : ℝ × ℝ, |lapP (ladCut R') x| ≤ K_cut / R' ^ 2 :=
    fun R' hR' x => (hK R' hR').2.2.2.2.2 x
  obtain ⟨M_col, hMcol0, hUnif⟩ :=
    FramePairing1Aux.physFrameE_uniform_xNorm hκ hm hb hν hs0 hbs hBdd
  obtain ⟨B_φ, hBφ0, hBφ⟩ :=
    RateBoundAux.bdd_of_cont (RateBoundAux.contOn_norm φ hφ.memX hφ.strongCont)
  -- Pointwise limit and uniform bound for `cutRate` across all `q ∈ Icc t₁ s`
  have hRate_all : ∀ q ∈ Icc t₁ s,
      Tendsto (fun R => FramePairing1Aux.cutRate κ tr φ R j q) atTop
        (𝓝 (∫ x in B0579.cell c, FramePairing1Aux.physFrameERate κ tr q j x * φ q x)) ∧
      ∀ R : ℝ, 1 ≤ R →
        ‖FramePairing1Aux.cutRate κ tr φ R j q‖ ≤
          M_col * B_φ + (3 * |ν| * K_cut + 2 * |C_tr| * K_cut) * (3 * (M_col * B_φ)) := by
    intro q hq
    obtain ⟨⟨hE_m, hE_n⟩, hpd, ⟨hR_m, hR_n⟩⟩ := hUnif q ⟨ht₁.trans hq.1, hq.2⟩ j
    exact FramePairing1Aux.cutRate_tendsto_and_bound hκ hν.1 ht₁ hMcol0 hBφ0 hBdd hφ hBφ
      K_cut hK0 hp_cut hl_cut j hq hE_m hE_n (fun k => (hpd k).1) (fun k => (hpd k).2) hR_m hR_n
  set M_tot : ℝ := M_col * B_φ + (3 * |ν| * K_cut + 2 * |C_tr| * K_cut) * (3 * (M_col * B_φ))
  -- Interval integrability and FTC on `[r, s']` for every `R ≥ 1`
  have hIoo_sub : Ioo r s' ⊆ Ioo t₁ s :=
    fun q hq => ⟨lt_of_le_of_lt hr.1 hq.1, lt_of_lt_of_le hq.2 hs'.2⟩
  have hIcc_sub : Icc r s' ⊆ Icc t₁ s := Icc_subset_Icc hr.1 hs'.2
  have hftc : ∀ R : ℝ, 1 ≤ R →
      IntervalIntegrable (FramePairing1Aux.cutRate κ tr φ R j) volume r s' ∧
        ∫ q in r..s', FramePairing1Aux.cutRate κ tr φ R j q =
          FramePairing1Aux.cutPair κ ν φ R j s' - FramePairing1Aux.cutPair κ ν φ R j r := by
    intro R hR1
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hcont_rate : ContinuousOn (FramePairing1Aux.cutRate κ tr φ R j) (Ioo r s') :=
      (FramePairing1Aux.continuousOn_cutRate hκ hν.1 ht₁ hR0 hφ j).mono hIoo_sub
    have hmeas_Ioo : AEStronglyMeasurable (FramePairing1Aux.cutRate κ tr φ R j)
        (volume.restrict (Ioo r s')) :=
      hcont_rate.aestronglyMeasurable measurableSet_Ioo
    have hconst_Ioo : IntegrableOn (fun _ : ℝ => M_tot) (Ioo r s') volume := by
      apply integrableOn_const <;>
        first | exact enorm_ne_top | exact measure_Ioo_lt_top.ne
    have hbnd_Ioo : ∀ᵐ q ∂(volume.restrict (Ioo r s')),
        ‖FramePairing1Aux.cutRate κ tr φ R j q‖ ≤ M_tot := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall fun q hq =>
        (hRate_all q (hIcc_sub (Ioo_subset_Icc_self hq))).2 R hR1
    have hint_Ioo : IntegrableOn (FramePairing1Aux.cutRate κ tr φ R j) (Ioo r s') volume :=
      hconst_Ioo.mono' hmeas_Ioo hbnd_Ioo
    have hint_Ioc : IntegrableOn (FramePairing1Aux.cutRate κ tr φ R j) (Ioc r s') volume :=
      (integrableOn_Ioc_iff_integrableOn_Ioo (hb := enorm_ne_top)).2 hint_Ioo
    have hint_R : IntervalIntegrable (FramePairing1Aux.cutRate κ tr φ R j) volume r s' :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hrs'_lt.le).2 hint_Ioc
    have hcont_pair : ContinuousOn (FramePairing1Aux.cutPair κ ν φ R j) (Icc r s') :=
      (FramePairing1Aux.continuousOn_cutPair hκ hν.1 ht₁ hR0 hφ j).mono hIcc_sub
    have hderiv_pair : ∀ q ∈ Ioo r s',
        HasDerivAt (FramePairing1Aux.cutPair κ ν φ R j)
          (FramePairing1Aux.cutRate κ tr φ R j q) q :=
      fun q hq => FramePairing1Aux.hasDerivAt_cutPair hκ hν.1 ht₁ hR0 hφ j (hIoo_sub hq)
    exact ⟨hint_R,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrs'_lt.le hcont_pair hderiv_pair hint_R⟩
  -- Pass `R → ∞` on `[r, s']` by dominated convergence
  have hI : Ι r s' = Ioc r s' := Set.uIoc_of_le hrs'_lt.le
  have hlim_int : Tendsto (fun R => ∫ q in r..s', FramePairing1Aux.cutRate κ tr φ R j q) atTop
      (𝓝 (∫ q in r..s', ∫ x in B0579.cell c,
        FramePairing1Aux.physFrameERate κ tr q j x * φ q x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (F := fun R q => FramePairing1Aux.cutRate κ tr φ R j q)
      (f := fun q => ∫ x in B0579.cell c, FramePairing1Aux.physFrameERate κ tr q j x * φ q x)
      (fun _ => M_tot) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
      exact (intervalIntegrable_iff.mp (hftc R hR1).1).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
      refine Eventually.of_forall fun q hqI => ?_
      rw [hI] at hqI
      exact (hRate_all q (hIcc_sub (Ioc_subset_Icc_self hqI))).2 R hR1
    · refine Eventually.of_forall fun q hqI => ?_
      rw [hI] at hqI
      exact (hRate_all q (hIcc_sub (Ioc_subset_Icc_self hqI))).1
  have hlim_end : ∀ q₀ ∈ Icc t₁ s,
      Tendsto (fun R => FramePairing1Aux.cutPair κ ν φ R j q₀) atTop
        (𝓝 (∫ x in B0579.cell c, FramePairing1Aux.physFrameE κ ν q₀ j x * φ q₀ x)) := by
    intro q₀ hq₀
    have hE_m := (hUnif q₀ ⟨ht₁.trans hq₀.1, hq₀.2⟩ j).1.1
    have hlim := ladCutLimit c m (FramePairing1Aux.physFrameE κ ν q₀ j) (φ q₀) hE_m (hφ.memX q₀ hq₀)
    refine hlim.congr fun R => integral_congr_ae (Eventually.of_forall fun x => ?_)
    unfold FramePairing1Aux.cutCol ladCutPhi
    ring
  have hphys_ftc :
      (∫ x in B0579.cell c, FramePairing1Aux.physFrameE κ ν s' j x * φ s' x) -
        ∫ x in B0579.cell c, FramePairing1Aux.physFrameE κ ν r j x * φ r x =
      ∫ q in r..s', ∫ x in B0579.cell c,
        FramePairing1Aux.physFrameERate κ tr q j x * φ q x := by
    have hsub := (hlim_end s' hs'_Icc).sub (hlim_end r hr)
    have hint_congr : Tendsto
        (fun R => FramePairing1Aux.cutPair κ ν φ R j s' - FramePairing1Aux.cutPair κ ν φ R j r)
        atTop (𝓝 (∫ q in r..s', ∫ x in B0579.cell c,
          FramePairing1Aux.physFrameERate κ tr q j x * φ q x)) := by
      refine hlim_int.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
      exact (hftc R hR1).2
    exact tendsto_nhds_unique hsub hint_congr
  -- Rewrite endpoints and integrand back to moving coordinates `(dd ν q, Φ q)`
  have hend_eq : ∀ q₀ ∈ Icc t₁ s,
      ∫ y in B0579.cell (dd ν q₀), perE κ (dd ν q₀) j y * Φ q₀ y =
        ∫ x in B0579.cell c, FramePairing1Aux.physFrameE κ ν q₀ j x * φ q₀ x := by
    intro q₀ hq₀
    have ha : 0 < clockA ν q₀ :=
      lt_of_lt_of_le zero_lt_one (one_le_clockA hν.1.le (ht₁.trans hq₀.1))
    have hae : (fun y => perE κ (dd ν q₀) j y * Φ q₀ y) =ᵐ[volume.restrict (B0579.cell (dd ν q₀))]
        fun y => perE κ (dd ν q₀) j y * movingPhi ν φ q₀ y := by
      filter_upwards [hΦ_ae q₀ hq₀] with y hy
      rw [hy]
    rw [integral_congr_ae hae, FramePairing1Aux.cell_pair_jscale_movingPhi hν.1 ha]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      rw [FramePairing1Aux.physFrameE_eq_jscale_perE κ ha j x])
  rw [hend_eq s' hs'_Icc, hend_eq r hr, hphys_ftc, intervalIntegral.integral_of_le hrs'_lt.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun q hq => ?_
  have hq_Icc : q ∈ Icc t₁ s := hIcc_sub (Ioc_subset_Icc_self hq)
  have hq0 : 0 ≤ q := ht₁.trans hq_Icc.1
  have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.1.le hq0)
  set Res : ℝ × ℝ → ℂ := fun y =>
    interactionTerm tr q (perE κ (dd ν q) j) y -
      (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
        modeEigen P j * perE κ (dd ν q) j y)
  have hrate_eq : ∀ x : ℝ × ℝ, FramePairing1Aux.physFrameERate κ tr q j x * φ q x =
      (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * (Jscale (clockA ν q) Res x * φ q x) := by
    intro x
    rw [FramePairing1Aux.physFrameERate_eq_jscale hκ P hν.1 hq0 tr j x, mul_assoc]
  have hae_q : (fun y => Res y * Φ q y) =ᵐ[volume.restrict (B0579.cell (dd ν q))]
      fun y => Res y * movingPhi ν φ q y := by
    filter_upwards [hΦ_ae q hq_Icc] with y hy
    rw [hy]
  rw [integral_congr_ae (Eventually.of_forall hrate_eq), integral_const_mul,
    ← FramePairing1Aux.cell_pair_jscale_movingPhi hν.1 ha Res φ,
    integral_congr_ae hae_q.symm]

end Leaf2WeakEqFrame

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
