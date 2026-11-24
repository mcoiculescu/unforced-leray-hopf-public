import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G1_1_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock

/-!


Source of record: `the November 2 reference manuscript`, lines 4366-4394 and
2975-3004 (`prop:short-full-clock`: damped complement stability in moving coordinates and
finite-band retained block estimates for `R = cmpN` forced by `A_± = ampN`).

Proof of `ActualComplIntegralBound D`:
1. On each full moving block `[t_k, t_{k+1}]` of moving length `B` (`blockCompactDuhamelGapE`) and
   on the final short block `[t_n, s]` of moving length `≤ B` (`shortComplPerturbDuhamel`), combine
   `complModeForceOscillator` and `complModeForceEulerError` with `clockTheta_inv_bounds`
   (`θ(r)⁻¹ ≤ 3 ν` on `[0, 2/ν]`), `amplNorm_eq_clockN_mul_ampSum`, and the exact cocycle
   `clockN P ν t r * clockN P ν r t₂ = clockN P ν t t₂` to obtain pure real single-block integral
   bounds (`single_block_relComplR_le`) for the normalised moving complement `relComplR`.
2. Iterate the `1/2` full-block contraction in `ℝ` (`iter_blocks_integral_le`) using
   `exp(-h₀ B) = 1/2` (`h₀ = log 2 / B`) and `intervalIntegral.integral_add_adjacent_intervals` to
   obtain exponential moving-time variation of constants with rate `h₀`.
3. Convert moving-time decay `exp(-h₀(z_s - z_u))` to physical age decay `exp(-g(s - u))` with
   `g = h₀ / 9` via `movingZ_sub_bounds`, and translate between `relComplR` and `cmpN` via
   `norm_Pc_actualPk_le_compl` and `compl_le_norm_Pc_actualPk`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF FlatSettingInst

/-! ## 1. Transport and finite-band bridges for `ampN`, `cmpN`, and `relComplR` -/

/-- Transport of a train along an equality of cell lengths, with its BUC class and its linearised
flows. -/
private theorem exists_train_cast {ν c c' : ℝ} (m : ℝ) (hc : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c', UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧
      ∀ (t : ℝ) (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
        IIIa.IsLinearisedFlow ν c m tr t f w u → IIIa.IsLinearisedFlow ν c' m tr' t f w u := by
  subst hc
  exact ⟨tr, hbuc, fun _ _ _ _ h => h⟩

/-- Sum of the two normalised amplitude moduli on `actualPk FI`. -/
private def ampSum {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (FI : FlatInstData κ ν c m tr)
    (P : UnforcedLeray.Blueprint.Planar.PlanarData) (t : ℝ) (x : Xmc c m) (r : ℝ) : ℝ :=
  ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x true r‖ +
    ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x false r‖

private theorem ampSum_nonneg {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (FI : FlatInstData κ ν c m tr)
    (P : UnforcedLeray.Blueprint.Planar.PlanarData) (t : ℝ) (x : Xmc c m) (r : ℝ) :
    0 ≤ ampSum FI P t x r :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem continuousOn_ampSum {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (FI : FlatInstData κ ν c m tr)
    (P : UnforcedLeray.Blueprint.Planar.PlanarData) {t H : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    (x : Xmc c m) :
    ContinuousOn (ampSum FI P t x) (Icc t H) :=
  (continuousOn_ampN_actualPk FI P.eigenvalue P.kappa hν ht x true).norm.add
    (continuousOn_ampN_actualPk FI P.eigenvalue P.kappa hν ht x false).norm

/-- On `0 ≤ r ≤ 2/ν`, `amplNorm F w r = ENNReal.ofReal (clockN P ν t r * ampSum FI P t x r)`. -/
private theorem amplNorm_eq_clockN_mul_ampSum {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ}
    [Fact (1 < m)] (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t : ℝ} (ht : 0 ≤ t) (x : Xmc (cOf ν) m)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (2 / ν)) :
    IIIa.amplNorm (IIIa.periodizedFrame κ ν m b K hν hPF)
        (fun q => xFn (FI.ev.U q t x)) r =
      ENNReal.ofReal (IIIa.clockN P ν t r * ampSum FI P t x r) := by
  set F := IIIa.periodizedFrame κ ν m b K hν hPF
  set w : ℝ → ℝ × ℝ → ℂ := fun q => xFn (FI.ev.U q t x)
  have hN : 0 < IIIa.clockN P ν t r := IIIa.clockN_pos P hν ht hr.1
  have hamp : ∀ j : Bool,
      IIIa.clockN P ν t r * ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x j r‖ =
        ‖IIIa.ampl F w r (pmIdx j)‖ := by
    intro j
    unfold ampN
    rw [norm_div, ell_actualPk_eq_ampl hν hPF FI t x j hr, norm_Fpm_eq_clockN P j hν hr.1 ht,
      mul_div_cancel₀ _ hN.ne']
  unfold IIIa.amplNorm ampSum
  rw [Fin.sum_univ_two, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), mul_add,
    hamp true, hamp false]
  rfl

/-- Real-valued normalised moving complement along `actualPk FI`. -/
private def relComplR {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (P : UnforcedLeray.Blueprint.Planar.PlanarData) (hν : 0 < ν)
    (hPF : IIIa.PerFrameFacts κ ν m b K) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (t : ℝ) (x : Xmc (cOf ν) m) (r : ℝ) : ℝ :=
  (IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
    (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
      (fun q => xFn (FI.ev.U q t x)) r)).toReal / IIIa.clockN P ν t r

private theorem relComplR_nonneg {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (P : UnforcedLeray.Blueprint.Planar.PlanarData) (hν : 0 < ν)
    (hPF : IIIa.PerFrameFacts κ ν m b K) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (x : Xmc (cOf ν) m) :
    0 ≤ relComplR P hν hPF FI t x r :=
  div_nonneg ENNReal.toReal_nonneg (IIIa.clockN_pos P hν ht hr).le

private theorem xNorm_compl_ne_top {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (hm : 8 < m) (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (t : ℝ) (x : Xmc (cOf ν) m)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (2 / ν)) :
    IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
      (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
        (fun q => xFn (FI.ev.U q t x)) r) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (compl_le_norm_Pc_actualPk hm hν hPF FI t x hr) ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

private theorem xNorm_compl_eq_ofReal_mul {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ}
    [Fact (1 < m)] (hm : 8 < m) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t : ℝ} (ht : 0 ≤ t) (x : Xmc (cOf ν) m)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (2 / ν)) :
    IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun q => xFn (FI.ev.U q t x)) r) =
      ENNReal.ofReal (IIIa.clockN P ν t r * relComplR P hν hPF FI t x r) := by
  have hN : 0 < IIIa.clockN P ν t r := IIIa.clockN_pos P hν ht hr.1
  unfold relComplR
  rw [mul_div_cancel₀ _ hN.ne', ENNReal.ofReal_toReal (xNorm_compl_ne_top hm hν hPF FI t x hr)]

private theorem cmpN_le_relComplR {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (hm : 8 < m) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t : ℝ} (ht : 0 ≤ t) (x : Xmc (cOf ν) m)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    cmpN (actualPk FI) P.eigenvalue P.kappa ν t x s ≤
      (3 : ℝ) ^ ((m - 3) / 2) * relComplR P hν hPF FI t x s := by
  have hN : 0 < IIIa.clockN P ν t s := IIIa.clockN_pos P hν ht hs.1
  have hPc := norm_Pc_actualPk_le_compl hm hν hPF FI t x hs
  set X := IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν s)) m
    (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) (fun q => xFn (FI.ev.U q t x)) s)
  have hX : X = ENNReal.ofReal X.toReal :=
    (ENNReal.ofReal_toReal (xNorm_compl_ne_top hm hν hPF FI t x hs)).symm
  have hc_pos : 0 ≤ (3 : ℝ) ^ ((m - 3) / 2) := by positivity
  rw [hX, ← ENNReal.ofReal_mul hc_pos,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc_pos ENNReal.toReal_nonneg)] at hPc
  unfold cmpN relComplR
  rw [norm_Fpm_eq_clockN P true hν hs.1 ht, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hPc hN.le

private theorem relComplR_le_cmpN_self {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (hm : 8 < m) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (2 / ν))
    (x : Xmc (cOf ν) m) :
    relComplR P hν hPF FI t x t ≤
      (3 : ℝ) ^ ((3 : ℝ) / 2) * cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t := by
  have hN : 0 < IIIa.clockN P ν t t := IIIa.clockN_pos P hν ht.1 ht.1
  have hPc := compl_le_norm_Pc_actualPk hm hν hPF FI t x ht
  have hc_pos : 0 ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  rw [← ENNReal.ofReal_mul hc_pos] at hPc
  have hreal : (IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t)) m
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun q => xFn (FI.ev.U q t x)) t)).toReal ≤
      (3 : ℝ) ^ ((3 : ℝ) / 2) * ‖Pc (actualPk FI) t ((actualPk FI).Uev t t x)‖ := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPc
    rwa [ENNReal.toReal_ofReal (mul_nonneg hc_pos (norm_nonneg _))] at h1
  unfold relComplR cmpN
  rw [norm_Fpm_eq_clockN P true hν ht.1 ht.1, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hreal hN.le

/-! ## 2. Unified single-block conversion to `ℝ` and real block iteration -/

/-- Converts an `ENNReal` single-block Duhamel inequality on `[t₁, t₂] ⊆ [t, 2/ν]` (either full
block from `BlockCompactDuhamelGapE` or short block from `ShortComplPerturbDuhamel`) into a pure
real integral inequality for `relComplR`. -/
private theorem single_block_relComplR_le {κ : IIIa.PlanarFrameKernels}
    {ν m b K C₁ C₂ α M_uh : ℝ} [Fact (1 < m)]
    (hm : 8 < m) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hPF : IIIa.PerFrameFacts κ ν m b K)
    (tr' : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t t₁ t₂ : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ t₁) (h12 : t₁ ≤ t₂) (ht2 : t₂ ≤ 2 / ν)
    (hbs : b ≤ IIIa.clockTheta ν t₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hα : 0 ≤ α) (hMuh : 0 ≤ M_uh)
    (W : ℝ → ℝ) (hW : ∀ r ∈ Ioc t₁ t₂, 0 ≤ W r ∧ W r ≤ IIIa.clockN P ν r t₂ * M_uh)
    (hOsc : ∀ r ∈ Ioc t₁ t₂, ∀ j : Fin 2,
      AEStronglyMeasurable (IIIa.movOscRes κ ν r j)
        (B0579.cellMeasure (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m) ∧
      IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m (IIIa.movOscRes κ ν r j) ≤
        ENNReal.ofReal (C₁ / IIIa.clockTheta ν r))
    (hEul : ∀ r ∈ Ioc t₁ t₂, ∀ j : Fin 2,
      AEStronglyMeasurable (IIIa.movEulerRes κ P tr' r j)
        (B0579.cellMeasure (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m) ∧
      IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
          (IIIa.movEulerRes κ P tr' r j) ≤
        ENNReal.ofReal (C₂ * ν ^ 3 / IIIa.clockTheta ν r))
    (x : Xmc (cOf ν) m)
    (hDuh :
      let F := IIIa.periodizedFrame κ ν m b K hν hPF
      let w := fun q => xFn (FI.ev.U q t x)
      IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₂)) m (IIIa.compl F w t₂) ≤
        ENNReal.ofReal (IIIa.clockN P ν t₁ t₂ * α) *
            IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₁)) m (IIIa.compl F w t₁) +
          ∫⁻ r in Ioc t₁ t₂,
            ENNReal.ofReal ((IIIa.clockA ν r) ^ (-2 : ℝ) * W r) *
              (∑ j : Fin 2, ENNReal.ofReal ‖IIIa.ampl F w r j‖ *
                IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
                  (IIIa.complModeForce κ P F tr' r j))) :
    let C_force := (1 + 2 * max K 0 ^ 2) * max C₁ C₂
    relComplR P hν hPF FI t x t₂ ≤
      α * relComplR P hν hPF FI t x t₁ +
        (6 * M_uh * C_force * ν) * ∫ r in t₁..t₂, ampSum FI P t x r := by
  intro C_force
  set F := IIIa.periodizedFrame κ ν m b K hν hPF
  set w : ℝ → ℝ × ℝ → ℂ := fun q => xFn (FI.ev.U q t x)
  have ht₁0 : 0 ≤ t₁ := ht.trans ht1
  have ht₂0 : 0 ≤ t₂ := ht₁0.trans h12
  have ht₁I : t₁ ∈ Icc (0 : ℝ) (2 / ν) := ⟨ht₁0, h12.trans ht2⟩
  have ht₂I : t₂ ∈ Icc (0 : ℝ) (2 / ν) := ⟨ht₂0, ht2⟩
  have hCf_nn : 0 ≤ C_force := by
    have : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left C₁ C₂)
    positivity
  have hNt₂ : 0 < IIIa.clockN P ν t t₂ := IIIa.clockN_pos P hν ht ht₂0
  have hNt₁ : 0 < IIIa.clockN P ν t t₁ := IIIa.clockN_pos P hν ht ht₁0
  have hN12 : 0 < IIIa.clockN P ν t₁ t₂ := IIIa.clockN_pos P hν ht₁0 ht₂0
  -- 1. Homogeneous term in ENNReal
  have hHom :
      ENNReal.ofReal (IIIa.clockN P ν t₁ t₂ * α) *
          IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₁)) m (IIIa.compl F w t₁) =
        ENNReal.ofReal (IIIa.clockN P ν t t₂ * (α * relComplR P hν hPF FI t x t₁)) := by
    rw [xNorm_compl_eq_ofReal_mul hm P hν hPF FI ht x ht₁I,
      ← ENNReal.ofReal_mul (mul_nonneg hN12.le hα)]
    congr 1
    have hmul := IIIa.FrameStableSub.clockN_mul P hν ht ht₁0 ht₂0
    calc (IIIa.clockN P ν t₁ t₂ * α) * (IIIa.clockN P ν t t₁ * relComplR P hν hPF FI t x t₁)
        = (IIIa.clockN P ν t t₁ * IIIa.clockN P ν t₁ t₂) * (α * relComplR P hν hPF FI t x t₁) := by
          ring
      _ = IIIa.clockN P ν t t₂ * (α * relComplR P hν hPF FI t x t₁) := by rw [← hmul]
  -- 2. Pointwise bound on Ioc t₁ t₂
  set K_blk : ℝ := 6 * M_uh * C_force * ν
  have hKblk_nn : 0 ≤ K_blk := by positivity
  have hInt_pt : ∀ r ∈ Ioc t₁ t₂,
      ENNReal.ofReal ((IIIa.clockA ν r) ^ (-2 : ℝ) * W r) *
          (∑ j : Fin 2, ENNReal.ofReal ‖IIIa.ampl F w r j‖ *
            IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
              (IIIa.complModeForce κ P F tr' r j)) ≤
        ENNReal.ofReal (IIIa.clockN P ν t t₂ * (K_blk * ampSum FI P t x r)) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁0.trans hr.1.le
    have hrI : r ∈ Icc (0 : ℝ) (2 / ν) := ⟨hr0, hr.2.trans ht2⟩
    have ha1 : 1 ≤ IIIa.clockA ν r := IIIa.one_le_clockA hν.le hr0
    have ha2_le : (IIIa.clockA ν r) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
    have hW_bd := hW r hr
    have haW_le : (IIIa.clockA ν r) ^ (-2 : ℝ) * W r ≤ IIIa.clockN P ν r t₂ * M_uh := by
      calc (IIIa.clockA ν r) ^ (-2 : ℝ) * W r ≤ 1 * W r :=
            mul_le_mul_of_nonneg_right ha2_le hW_bd.1
        _ = W r := one_mul _
        _ ≤ IIIa.clockN P ν r t₂ * M_uh := hW_bd.2
    have hbr : b ≤ IIIa.clockTheta ν r := hbs.trans (IIIa.theta_anti hν hr0 hr.2)
    have hν3 : 1 + ν ^ 3 ≤ 2 := by
      have : ν ^ 3 ≤ 1 := pow_le_one₀ hν.le hν1
      linarith
    have hθ_inv : (IIIa.clockTheta ν r)⁻¹ ≤ 3 * ν := (clockTheta_inv_bounds hν hrI).2.1
    have hη_le : C_force * (1 + ν ^ 3) / IIIa.clockTheta ν r ≤ 6 * C_force * ν := by
      rw [div_eq_mul_inv]
      calc C_force * (1 + ν ^ 3) * (IIIa.clockTheta ν r)⁻¹
          ≤ C_force * 2 * (3 * ν) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hν3 hCf_nn) hθ_inv
              (inv_nonneg.2 (IIIa.theta_pos hν hr0).le) (by positivity)
        _ = 6 * C_force * ν := by ring
    have hforce : ∀ j : Fin 2,
        IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
            (IIIa.complModeForce κ P F tr' r j) ≤
          ENNReal.ofReal (6 * C_force * ν) := by
      intro j
      obtain ⟨hOm, hOb⟩ := hOsc r hr j
      obtain ⟨hEm, hEb⟩ := hEul r hr j
      exact (IIIa.FrameShortBlockSub.xNorm_complModeForce_le κ P F tr' j hν hr0 hbr hC₁ hC₂
        hOm hOb hEm hEb).trans (ENNReal.ofReal_le_ofReal hη_le)
    have hsum := IIIa.FrameShortBlockSub.sum_ampl_complModeForce_le κ P F tr' w hforce
    have hN_rt₂ : 0 ≤ IIIa.clockN P ν r t₂ := (IIIa.clockN_pos P hν hr0 ht₂0).le
    have hN_tr : 0 ≤ IIIa.clockN P ν t r := (IIIa.clockN_pos P hν ht hr0).le
    calc ENNReal.ofReal ((IIIa.clockA ν r) ^ (-2 : ℝ) * W r) *
          (∑ j : Fin 2, ENNReal.ofReal ‖IIIa.ampl F w r j‖ *
            IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
              (IIIa.complModeForce κ P F tr' r j))
        ≤ ENNReal.ofReal (IIIa.clockN P ν r t₂ * M_uh) *
            (ENNReal.ofReal (6 * C_force * ν) * IIIa.amplNorm F w r) :=
          mul_le_mul (ENNReal.ofReal_le_ofReal haW_le) hsum zero_le zero_le
      _ = ENNReal.ofReal (IIIa.clockN P ν r t₂ * M_uh) *
            (ENNReal.ofReal (6 * C_force * ν) *
              ENNReal.ofReal (IIIa.clockN P ν t r * ampSum FI P t x r)) := by
          rw [amplNorm_eq_clockN_mul_ampSum P hν hPF FI ht x hrI]
      _ = ENNReal.ofReal (IIIa.clockN P ν t t₂ * (K_blk * ampSum FI P t x r)) := by
          rw [← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (mul_nonneg hN_rt₂ hMuh)]
          congr 1
          have hmul := IIIa.FrameStableSub.clockN_mul P hν ht hr0 ht₂0
          calc (IIIa.clockN P ν r t₂ * M_uh) *
                (6 * C_force * ν * (IIIa.clockN P ν t r * ampSum FI P t x r))
              = (IIIa.clockN P ν t r * IIIa.clockN P ν r t₂) *
                  (K_blk * ampSum FI P t x r) := by simp only [K_blk]; ring
            _ = IIIa.clockN P ν t t₂ * (K_blk * ampSum FI P t x r) := by rw [← hmul]
  -- 3. Convert Lebesgue integral on Ioc t₁ t₂ to Bochner interval integral
  have hcont_A : ContinuousOn (ampSum FI P t x) (Icc t₁ t₂) :=
    (continuousOn_ampSum FI P hν ht x).mono (Icc_subset_Icc ht1 le_rfl)
  have hcont_f : ContinuousOn (fun r => IIIa.clockN P ν t t₂ * (K_blk * ampSum FI P t x r))
      (Icc t₁ t₂) :=
    continuousOn_const.mul (continuousOn_const.mul hcont_A)
  have hint_f : IntegrableOn (fun r => IIIa.clockN P ν t t₂ * (K_blk * ampSum FI P t x r))
      (Ioc t₁ t₂) :=
    hcont_f.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn_f : 0 ≤ᵐ[volume.restrict (Ioc t₁ t₂)]
      (fun r => IIIa.clockN P ν t t₂ * (K_blk * ampSum FI P t x r)) :=
    ae_of_all _ fun r => mul_nonneg hNt₂.le (mul_nonneg hKblk_nn (ampSum_nonneg FI P t x r))
  have hInt_eq :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal (IIIa.clockN P ν t t₂ * (K_blk * ampSum FI P t x r))) =
      ENNReal.ofReal (IIIa.clockN P ν t t₂ * (K_blk * ∫ r in t₁..t₂, ampSum FI P t x r)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint_f hnn_f,
      ← intervalIntegral.integral_of_le h12, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hInt_le :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal ((IIIa.clockA ν r) ^ (-2 : ℝ) * W r) *
          (∑ j : Fin 2, ENNReal.ofReal ‖IIIa.ampl F w r j‖ *
            IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
              (IIIa.complModeForce κ P F tr' r j))) ≤
      ENNReal.ofReal (IIIa.clockN P ν t t₂ * (K_blk * ∫ r in t₁..t₂, ampSum FI P t x r)) :=
    (setLIntegral_mono' measurableSet_Ioc hInt_pt).trans (le_of_eq hInt_eq)
  -- 4. Conclude in ℝ by cancelling clockN P ν t t₂ > 0
  have hInt_nn : 0 ≤ ∫ r in t₁..t₂, ampSum FI P t x r :=
    intervalIntegral.integral_nonneg h12 fun r _ => ampSum_nonneg FI P t x r
  have hRHS_nn : 0 ≤ IIIa.clockN P ν t t₂ *
      (α * relComplR P hν hPF FI t x t₁ + K_blk * ∫ r in t₁..t₂, ampSum FI P t x r) := by
    have := relComplR_nonneg P hν hPF FI ht ht₁0 x
    positivity
  have hcomb : ENNReal.ofReal (IIIa.clockN P ν t t₂ * relComplR P hν hPF FI t x t₂) ≤
      ENNReal.ofReal (IIIa.clockN P ν t t₂ *
        (α * relComplR P hν hPF FI t x t₁ + K_blk * ∫ r in t₁..t₂, ampSum FI P t x r)) := by
    rw [← xNorm_compl_eq_ofReal_mul hm P hν hPF FI ht x ht₂I]
    refine hDuh.trans ((add_le_add (le_of_eq hHom) hInt_le).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add
      (mul_nonneg hNt₂.le (mul_nonneg hα (relComplR_nonneg P hν hPF FI ht ht₁0 x)))
      (mul_nonneg hNt₂.le (mul_nonneg hKblk_nn hInt_nn)), ← mul_add]
  exact le_of_mul_le_mul_left ((ENNReal.ofReal_le_ofReal_iff hRHS_nn).1 hcomb) hNt₂

/-- Pure real iteration of the full-block `1/2` contraction and final short-block `M_B` bound
along moving-time blocks of length `B > 0`, producing moving-time variation of constants with
exponential rate `h₀ = Real.log 2 / B`. -/
private theorem iter_blocks_integral_le {ν B M_B K_I t s : ℝ} {ρ A : ℝ → ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hMB : 1 ≤ M_B) (hKI : 0 ≤ K_I)
    (ht : 0 ≤ t) (hts : t ≤ s)
    (hA_cont : ContinuousOn A (Icc t s)) (hA_nn : ∀ r ∈ Icc t s, 0 ≤ A r)
    (hρ_nn : ∀ r ∈ Icc t s, 0 ≤ ρ r)
    (hfull : ∀ t₁ t₂, t ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ s → IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁ = B →
      ρ t₂ ≤ (1 / 2) * ρ t₁ + K_I * ν * ∫ r in t₁..t₂, A r)
    (hshort : ∀ t₁ t₂, t ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ s → IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁ ≤ B →
      ρ t₂ ≤ M_B * ρ t₁ + K_I * ν * ∫ r in t₁..t₂, A r) :
    let h₀ := Real.log 2 / B
    ρ s ≤ 2 * M_B * Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν t)) * ρ t +
      4 * M_B * K_I * ν *
        ∫ r in t..s, Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν r)) * A r := by
  intro h₀
  have hh₀ : 0 < h₀ := div_pos (Real.log_pos (by norm_num)) hB
  have hexp_hB : Real.exp (-h₀ * B) = 1 / 2 := by
    have e1 : -h₀ * B = -Real.log 2 := by
      simp only [h₀]
      rw [neg_mul, div_mul_cancel₀ _ hB.ne']
    rw [e1, Real.exp_neg, Real.exp_log (by norm_num), one_div]
  have hcont_Z : ContinuousOn (IIIa.movingZ ν) (Icc t s) := by
    unfold IIIa.movingZ IIIa.clockA
    refine continuousOn_id.div
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) fun r hr => ?_
    have hr0 : 0 ≤ r := ht.trans hr.1
    linarith [mul_nonneg hν.le hr0]
  have hint_A : ∀ {a b' : ℝ}, a ∈ Icc t s → b' ∈ Icc t s → a ≤ b' →
      IntervalIntegrable A volume a b' := fun ha hb' hab =>
    (hA_cont.mono (Icc_subset_Icc ha.1 hb'.2)).intervalIntegrable_of_Icc hab
  have hint_exp : ∀ (z_top : ℝ) {a b' : ℝ}, a ∈ Icc t s → b' ∈ Icc t s → a ≤ b' →
      IntervalIntegrable (fun r => Real.exp (-h₀ * (z_top - IIIa.movingZ ν r)) * A r)
        volume a b' := by
    intro z_top a b' ha hb' hab
    have hc : ContinuousOn (fun r => Real.exp (-h₀ * (z_top - IIIa.movingZ ν r)) * A r)
        (Icc t s) :=
      ((continuousOn_const.mul (continuousOn_const.sub hcont_Z)).rexp).mul hA_cont
    exact (hc.mono (Icc_subset_Icc ha.1 hb'.2)).intervalIntegrable_of_Icc hab
  -- Moving-time grid tk k = moveAgeOfZ ν (zt + k * B)
  set zt := IIIa.movingZ ν t
  set zs := IIIa.movingZ ν s
  have hzt0 : 0 ≤ zt := IIIa.FrameStableSub.movingZ_nonneg hν ht
  have hzs1 : ν * zs < 1 := IIIa.FrameStableSub.nu_mul_movingZ_lt_one hν (ht.trans hts)
  have hzts : zt ≤ zs := IIIa.FrameStableSub.movingZ_le_movingZ hν ht hts
  have hΔz : 0 ≤ zs - zt := sub_nonneg.2 hzts
  set n := Nat.floor ((zs - zt) / B)
  let tk : ℕ → ℝ := fun k => IIIa.FrameStableSub.moveAgeOfZ ν (zt + (k : ℝ) * B)
  have htk_eq0 : tk 0 = t := by
    simp only [tk, Nat.cast_zero, zero_mul, add_zero]
    exact IIIa.FrameStableSub.moveAgeOfZ_movingZ hν ht
  have hzk_le : ∀ k ≤ n, zt + (k : ℝ) * B ≤ zs := by
    intro k hk
    have hkR : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hk
    have hnR : (n : ℝ) ≤ (zs - zt) / B := Nat.floor_le (div_nonneg hΔz hB.le)
    have hmul : (k : ℝ) * B ≤ zs - zt := (le_div_iff₀ hB).1 (hkR.trans hnR)
    linarith
  have htk_mem : ∀ k ≤ n, tk k ∈ Icc t s := by
    intro k hk
    have h1 : zt ≤ zt + (k : ℝ) * B := le_add_of_nonneg_right (by positivity)
    have h2 : zt + (k : ℝ) * B ≤ zs := hzk_le k hk
    constructor
    · rw [← IIIa.FrameStableSub.moveAgeOfZ_movingZ hν ht]
      exact IIIa.FrameStableSub.moveAgeOfZ_mono hν hzt0
        (by linarith [mul_le_mul_of_nonneg_left h2 hν.le]) h1
    · rw [← IIIa.FrameStableSub.moveAgeOfZ_movingZ hν (ht.trans hts)]
      exact IIIa.FrameStableSub.moveAgeOfZ_mono hν (hzt0.trans h1) hzs1 h2
  have htk_mono : ∀ k < n, tk k ≤ tk (k + 1) := by
    intro k hk
    have h1 : zt + (k : ℝ) * B ≤ zt + ((k + 1 : ℕ) : ℝ) * B := by push_cast; linarith
    have h2 := hzk_le (k + 1) hk
    exact IIIa.FrameStableSub.moveAgeOfZ_mono hν (by positivity)
      (by linarith [mul_le_mul_of_nonneg_left h2 hν.le]) h1
  have htk_diff : ∀ k < n, IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν (tk k) = B := by
    intro k hk
    have h2 := hzk_le (k + 1) hk
    have h1 : zt + (k : ℝ) * B ≤ zs := hzk_le k (Nat.le_of_lt hk)
    rw [IIIa.FrameStableSub.movingZ_moveAgeOfZ (by linarith [mul_le_mul_of_nonneg_left h2 hν.le]),
      IIIa.FrameStableSub.movingZ_moveAgeOfZ (by linarith [mul_le_mul_of_nonneg_left h1 hν.le])]
    push_cast
    ring
  -- Helper: on any block [u₁, u₂] ⊆ [t, s] with z(u₂) - z(u₁) ≤ B, A(r) ≤ 2 * exp(-h₀(z(u₂)-z(r))) A(r)
  have hblk_int_le : ∀ {u₁ u₂ : ℝ}, u₁ ∈ Icc t s → u₂ ∈ Icc t s → u₁ ≤ u₂ →
      IIIa.movingZ ν u₂ - IIIa.movingZ ν u₁ ≤ B →
      ∫ r in u₁..u₂, A r ≤
        2 * ∫ r in u₁..u₂, Real.exp (-h₀ * (IIIa.movingZ ν u₂ - IIIa.movingZ ν r)) * A r := by
    intro u₁ u₂ hu₁ hu₂ h12 hzB
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h12 (hint_A hu₁ hu₂ h12)
      ((hint_exp _ hu₁ hu₂ h12).const_mul 2) fun r hr => ?_
    have hrI : r ∈ Icc t s := ⟨hu₁.1.trans hr.1, hr.2.trans hu₂.2⟩
    have hzr : IIIa.movingZ ν u₁ ≤ IIIa.movingZ ν r :=
      IIIa.FrameStableSub.movingZ_le_movingZ hν (ht.trans hu₁.1) hr.1
    have hz_le : IIIa.movingZ ν u₂ - IIIa.movingZ ν r ≤ B := by linarith
    have hexp_ge : 1 / 2 ≤ Real.exp (-h₀ * (IIIa.movingZ ν u₂ - IIIa.movingZ ν r)) := by
      rw [← hexp_hB]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hA_r : 0 ≤ A r := hA_nn r hrI
    nlinarith
  -- Induction over the full blocks 0 ≤ k ≤ n
  have hiter : ∀ k ≤ n,
      ρ (tk k) ≤ (1 / 2 : ℝ) ^ k * ρ (tk 0) +
        2 * K_I * ν * ∫ r in tk 0..tk k,
          Real.exp (-h₀ * (IIIa.movingZ ν (tk k) - IIIa.movingZ ν r)) * A r := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [pow_zero, one_mul, intervalIntegral.integral_same, mul_zero, add_zero]
    | succ k ih =>
      intro hk1
      have hk_lt : k < n := hk1
      have hk_le : k ≤ n := Nat.le_of_lt hk_lt
      have h0_mem := htk_mem 0 (Nat.zero_le n)
      have hk_mem := htk_mem k hk_le
      have hk1_mem := htk_mem (k + 1) hk1
      have h0k : tk 0 ≤ tk k := by
        rw [htk_eq0]
        exact hk_mem.1
      have hkk1 : tk k ≤ tk (k + 1) := htk_mono k hk_lt
      have hstep := hfull (tk k) (tk (k + 1)) hk_mem.1 hkk1 hk1_mem.2 (htk_diff k hk_lt)
      have hih := ih hk_le
      have hshift_fn : (fun r => (1 / 2 : ℝ) *
            (Real.exp (-h₀ * (IIIa.movingZ ν (tk k) - IIIa.movingZ ν r)) * A r)) =
          fun r => Real.exp (-h₀ * (IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν r)) * A r := by
        funext r
        have hdiff := htk_diff k hk_lt
        have hz_split : IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν r =
            B + (IIIa.movingZ ν (tk k) - IIIa.movingZ ν r) := by linarith
        have heq_z : -h₀ * (IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν r) =
            -h₀ * B + (-h₀ * (IIIa.movingZ ν (tk k) - IIIa.movingZ ν r)) := by
          rw [hz_split]
          ring
        rw [heq_z, Real.exp_add, hexp_hB]
        ring
      have hshift_int :
          (1 / 2 : ℝ) * (∫ r in tk 0..tk k,
              Real.exp (-h₀ * (IIIa.movingZ ν (tk k) - IIIa.movingZ ν r)) * A r) =
            ∫ r in tk 0..tk k,
              Real.exp (-h₀ * (IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν r)) * A r := by
        rw [← intervalIntegral.integral_const_mul, hshift_fn]
      have hnew_int := hblk_int_le hk_mem hk1_mem hkk1 (htk_diff k hk_lt).le
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hint_exp (IIIa.movingZ ν (tk (k + 1))) h0_mem hk_mem h0k)
        (hint_exp (IIIa.movingZ ν (tk (k + 1))) hk_mem hk1_mem hkk1)
      have hKν_nn : 0 ≤ K_I * ν := mul_nonneg hKI hν.le
      calc ρ (tk (k + 1))
          ≤ (1 / 2) * ρ (tk k) + K_I * ν * ∫ r in tk k..tk (k + 1), A r := hstep
        _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ k * ρ (tk 0) +
              2 * K_I * ν * ∫ r in tk 0..tk k,
                Real.exp (-h₀ * (IIIa.movingZ ν (tk k) - IIIa.movingZ ν r)) * A r) +
            K_I * ν * (2 * ∫ r in tk k..tk (k + 1),
              Real.exp (-h₀ * (IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν r)) * A r) :=
          add_le_add (mul_le_mul_of_nonneg_left hih (by norm_num))
            (mul_le_mul_of_nonneg_left hnew_int hKν_nn)
        _ = (1 / 2 : ℝ) ^ (k + 1) * ρ (tk 0) +
            2 * K_I * ν * (((1 / 2 : ℝ) * ∫ r in tk 0..tk k,
                Real.exp (-h₀ * (IIIa.movingZ ν (tk k) - IIIa.movingZ ν r)) * A r) +
              (∫ r in tk k..tk (k + 1),
                Real.exp (-h₀ * (IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν r)) * A r)) := by
          rw [pow_succ']
          ring
        _ = (1 / 2 : ℝ) ^ (k + 1) * ρ (tk 0) +
            2 * K_I * ν * ∫ r in tk 0..tk (k + 1),
              Real.exp (-h₀ * (IIIa.movingZ ν (tk (k + 1)) - IIIa.movingZ ν r)) * A r := by
          rw [hshift_int, hadj]
  -- Combine full-block bound at k = n with final short block [tk n, s]
  have hn_mem := htk_mem n le_rfl
  have hs_mem : s ∈ Icc t s := ⟨hts, le_rfl⟩
  have ht_mem : t ∈ Icc t s := ⟨le_rfl, hts⟩
  have hshort_len : IIIa.movingZ ν s - IIIa.movingZ ν (tk n) ≤ B := by
    have h1 := hzk_le n le_rfl
    rw [IIIa.FrameStableSub.movingZ_moveAgeOfZ (by linarith [mul_le_mul_of_nonneg_left h1 hν.le])]
    have hlt : (zs - zt) / B < (n : ℝ) + 1 := Nat.lt_floor_add_one ((zs - zt) / B)
    have hmul : zs - zt < ((n : ℝ) + 1) * B := (div_lt_iff₀ hB).1 hlt
    linarith
  have hstep_s := hshort (tk n) s hn_mem.1 hn_mem.2 le_rfl hshort_len
  have hiter_n := hiter n le_rfl
  rw [htk_eq0] at hiter_n
  have hMB_nn : 0 ≤ M_B := by linarith
  have hHom_s : M_B * ((1 / 2 : ℝ) ^ n * ρ t) ≤
      2 * M_B * Real.exp (-h₀ * (zs - zt)) * ρ t := by
    have hexp := IIIa.FrameStableSub.half_pow_floor_le_exp hB hΔz
    calc M_B * ((1 / 2 : ℝ) ^ n * ρ t)
        = M_B * (1 / 2 : ℝ) ^ n * ρ t := by ring
      _ ≤ M_B * (2 * Real.exp (-h₀ * (zs - zt))) * ρ t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hMB_nn) (hρ_nn t ht_mem)
      _ = 2 * M_B * Real.exp (-h₀ * (zs - zt)) * ρ t := by ring
  have hInt_past :
      ∫ r in t..tk n, Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r ≤
        2 * ∫ r in t..tk n, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hn_mem.1
      (hint_exp _ ht_mem hn_mem hn_mem.1) ((hint_exp _ ht_mem hn_mem hn_mem.1).const_mul 2)
      fun r hr => ?_
    have hrI : r ∈ Icc t s := ⟨hr.1, hr.2.trans hn_mem.2⟩
    have hexp_ge : 1 / 2 ≤ Real.exp (-h₀ * (zs - IIIa.movingZ ν (tk n))) := by
      rw [← hexp_hB]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hsplit : Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) =
        Real.exp (-h₀ * (zs - IIIa.movingZ ν (tk n))) *
          Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hpos : 0 ≤ Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r :=
      mul_nonneg (Real.exp_pos _).le (hA_nn r hrI)
    rw [hsplit]
    calc Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r
        = 1 * (Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r) :=
          (one_mul _).symm
      _ ≤ (2 * Real.exp (-h₀ * (zs - IIIa.movingZ ν (tk n)))) *
            (Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
      _ = 2 * (Real.exp (-h₀ * (zs - IIIa.movingZ ν (tk n))) *
            Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r) := by ring
  have hInt_tail :
      ∫ r in tk n..s, A r ≤
        4 * M_B * ∫ r in tk n..s, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r := by
    have h1 := hblk_int_le hn_mem hs_mem hn_mem.2 hshort_len
    have hnn_int : 0 ≤ ∫ r in tk n..s, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r :=
      intervalIntegral.integral_nonneg hn_mem.2 fun r hr =>
        mul_nonneg (Real.exp_pos _).le (hA_nn r ⟨hn_mem.1.trans hr.1, hr.2⟩)
    nlinarith
  have hadj_final := intervalIntegral.integral_add_adjacent_intervals
    (hint_exp zs ht_mem hn_mem hn_mem.1) (hint_exp zs hn_mem hs_mem hn_mem.2)
  have hKν_nn : 0 ≤ K_I * ν := mul_nonneg hKI hν.le
  have h2MBKν_nn : 0 ≤ 2 * M_B * K_I * ν := by positivity
  calc ρ s
      ≤ M_B * ρ (tk n) + K_I * ν * ∫ r in tk n..s, A r := hstep_s
    _ ≤ M_B * ((1 / 2 : ℝ) ^ n * ρ t +
          2 * K_I * ν * ∫ r in t..tk n,
            Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r) +
        K_I * ν * ∫ r in tk n..s, A r :=
      add_le_add (mul_le_mul_of_nonneg_left hiter_n hMB_nn) le_rfl
    _ = M_B * ((1 / 2 : ℝ) ^ n * ρ t) +
        2 * M_B * K_I * ν * (∫ r in t..tk n,
          Real.exp (-h₀ * (IIIa.movingZ ν (tk n) - IIIa.movingZ ν r)) * A r) +
        K_I * ν * ∫ r in tk n..s, A r := by ring
    _ ≤ 2 * M_B * Real.exp (-h₀ * (zs - zt)) * ρ t +
        2 * M_B * K_I * ν * (2 * ∫ r in t..tk n, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r) +
        K_I * ν * (4 * M_B * ∫ r in tk n..s, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r) :=
      add_le_add (add_le_add hHom_s (mul_le_mul_of_nonneg_left hInt_past h2MBKν_nn))
        (mul_le_mul_of_nonneg_left hInt_tail hKν_nn)
    _ = 2 * M_B * Real.exp (-h₀ * (zs - zt)) * ρ t +
        4 * M_B * K_I * ν * ((∫ r in t..tk n, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r) +
          ∫ r in tk n..s, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r) := by ring
    _ = 2 * M_B * Real.exp (-h₀ * (zs - zt)) * ρ t +
        4 * M_B * K_I * ν * ∫ r in t..s, Real.exp (-h₀ * (zs - IIIa.movingZ ν r)) * A r := by
      rw [hadj_final]

/-! ## 3. Single-level assembly, small-`ν` regime, and `actualComplIntegralBound` -/

/-- Combines the full-block and short-block real integral bounds at a fixed viscosity `ν` with
`iter_blocks_integral_le`, `movingZ_sub_bounds`, `cmpN_le_relComplR`, and
`relComplR_le_cmpN_self` to deduce the physical-age `cmpN` integral inequality. -/
private theorem compl_bound_at_nu {κ : IIIa.PlanarFrameKernels} {ν m b K B M_B K_I C : ℝ}
    [Fact (1 < m)] (hm : 8 < m) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hB : 0 < B) (hMB : 1 ≤ M_B) (hKI : 0 ≤ K_I) (hC_pos : 0 < C)
    (hC1 : 2 * (3 : ℝ) ^ ((m - 3) / 2) * (3 : ℝ) ^ ((3 : ℝ) / 2) * M_B ≤ C)
    (hC2 : 4 * (3 : ℝ) ^ ((m - 3) / 2) * M_B * K_I ≤ C)
    (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 2 / ν) (x : Xmc (cOf ν) m)
    (hfull : ∀ t₁ t₂, t ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ s →
      IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁ = B →
      relComplR P hν hPF FI t x t₂ ≤
        (1 / 2) * relComplR P hν hPF FI t x t₁ + K_I * ν * ∫ r in t₁..t₂, ampSum FI P t x r)
    (hshort : ∀ t₁ t₂, t ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ s →
      IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁ ≤ B →
      relComplR P hν hPF FI t x t₂ ≤
        M_B * relComplR P hν hPF FI t x t₁ + K_I * ν * ∫ r in t₁..t₂, ampSum FI P t x r) :
    let g := (Real.log 2 / B) / 9
    cmpN (actualPk FI) P.eigenvalue P.kappa ν t x s ≤
      C * Real.exp (-g * (s - t)) * cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t +
        C * (ν + ν ^ 4) * ∫ r in t..s, Real.exp (-g * (s - r)) *
          (‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x true r‖ +
            ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x false r‖) := by
  intro g
  set h₀ : ℝ := Real.log 2 / B
  have hh₀_pos : 0 < h₀ := div_pos (Real.log_pos (by norm_num)) hB
  have htI : t ∈ Icc (0 : ℝ) (2 / ν) := ⟨ht, hts.trans hs⟩
  have hsI : s ∈ Icc (0 : ℝ) (2 / ν) := ⟨ht.trans hts, hs⟩
  have hA_cont : ContinuousOn (ampSum FI P t x) (Icc t s) :=
    continuousOn_ampSum FI P hν ht x
  have hA_nn : ∀ r ∈ Icc t s, 0 ≤ ampSum FI P t x r := fun r _ => ampSum_nonneg FI P t x r
  have hρ_nn : ∀ r ∈ Icc t s, 0 ≤ relComplR P hν hPF FI t x r := fun r hr =>
    relComplR_nonneg P hν hPF FI ht (ht.trans hr.1) x
  have hiter := iter_blocks_integral_le hν hB hMB hKI ht hts hA_cont hA_nn hρ_nn hfull hshort
  have hexp_z_le : ∀ {u : ℝ}, 0 ≤ u → u ≤ s →
      Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν u)) ≤ Real.exp (-g * (s - u)) := by
    intro u hu hus
    have hz_lb := (movingZ_sub_bounds hν hu hus hs).1
    apply Real.exp_le_exp.2
    have : -h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν u) ≤ -h₀ * ((s - u) / 9) :=
      mul_le_mul_of_nonpos_left hz_lb (by linarith)
    refine this.trans (le_of_eq ?_)
    simp only [g, h₀]
    ring
  have hcont_Z : ContinuousOn (IIIa.movingZ ν) (Icc t s) := by
    unfold IIIa.movingZ IIIa.clockA
    refine continuousOn_id.div
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) fun r hr => ?_
    linarith [mul_nonneg hν.le (ht.trans hr.1)]
  have hint_mov : IntervalIntegrable
      (fun r => Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν r)) * ampSum FI P t x r)
      volume t s :=
    (((continuousOn_const.mul (continuousOn_const.sub hcont_Z)).rexp).mul hA_cont
      ).intervalIntegrable_of_Icc hts
  have hint_phys : IntervalIntegrable
      (fun r => Real.exp (-g * (s - r)) * ampSum FI P t x r) volume t s :=
    (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).rexp).mul hA_cont
      ).intervalIntegrable_of_Icc hts
  have hInt_phys_le :
      ∫ r in t..s, Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν r)) * ampSum FI P t x r ≤
        ∫ r in t..s, Real.exp (-g * (s - r)) * ampSum FI P t x r :=
    intervalIntegral.integral_mono_on hts hint_mov hint_phys fun r hr =>
      mul_le_mul_of_nonneg_right (hexp_z_le (ht.trans hr.1) hr.2) (ampSum_nonneg FI P t x r)
  have hInt_phys_nn : 0 ≤ ∫ r in t..s, Real.exp (-g * (s - r)) * ampSum FI P t x r :=
    intervalIntegral.integral_nonneg hts fun r _ =>
      mul_nonneg (Real.exp_pos _).le (ampSum_nonneg FI P t x r)
  set cs : ℝ := (3 : ℝ) ^ ((m - 3) / 2)
  set ct : ℝ := (3 : ℝ) ^ ((3 : ℝ) / 2)
  have hcs_pos : 0 < cs := by positivity
  have hct_pos : 0 < ct := by positivity
  have hMB_pos : 0 < M_B := by linarith
  have hcmp_s := cmpN_le_relComplR hm P hν hPF FI ht x hsI
  have hcmp_t := relComplR_le_cmpN_self hm P hν hPF FI htI x
  have hcmp_t_nn : 0 ≤ cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t := by
    unfold cmpN
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hν_le_add : ν ≤ ν + ν ^ 4 := le_add_of_nonneg_right (pow_nonneg hν.le 4)
  change cmpN (actualPk FI) P.eigenvalue P.kappa ν t x s ≤
    C * Real.exp (-g * (s - t)) * cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t +
      C * (ν + ν ^ 4) * ∫ r in t..s, Real.exp (-g * (s - r)) * ampSum FI P t x r
  calc cmpN (actualPk FI) P.eigenvalue P.kappa ν t x s
      ≤ cs * relComplR P hν hPF FI t x s := hcmp_s
    _ ≤ cs * (2 * M_B * Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν t)) *
            relComplR P hν hPF FI t x t +
          4 * M_B * K_I * ν *
            ∫ r in t..s, Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν r)) *
              ampSum FI P t x r) :=
      mul_le_mul_of_nonneg_left hiter hcs_pos.le
    _ = 2 * cs * M_B * Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν t)) *
          relComplR P hν hPF FI t x t +
        4 * cs * M_B * K_I * ν *
          ∫ r in t..s, Real.exp (-h₀ * (IIIa.movingZ ν s - IIIa.movingZ ν r)) *
            ampSum FI P t x r := by ring
    _ ≤ 2 * cs * M_B * Real.exp (-g * (s - t)) *
          (ct * cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t) +
        4 * cs * M_B * K_I * ν * ∫ r in t..s, Real.exp (-g * (s - r)) * ampSum FI P t x r := by
      refine add_le_add ?_ (mul_le_mul_of_nonneg_left hInt_phys_le (by positivity))
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hexp_z_le ht hts) (by positivity))
        hcmp_t (relComplR_nonneg P hν hPF FI ht ht x) (by positivity)
    _ = (2 * cs * ct * M_B) * Real.exp (-g * (s - t)) *
          cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t +
        (4 * cs * M_B * K_I * ν) * ∫ r in t..s, Real.exp (-g * (s - r)) * ampSum FI P t x r := by
      ring
    _ ≤ C * Real.exp (-g * (s - t)) * cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t +
        C * (ν + ν ^ 4) * ∫ r in t..s, Real.exp (-g * (s - r)) * ampSum FI P t x r := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le) hcmp_t_nn
      · refine mul_le_mul_of_nonneg_right ?_ hInt_phys_nn
        calc 4 * cs * M_B * K_I * ν ≤ C * ν := mul_le_mul_of_nonneg_right hC2 hν.le
          _ ≤ C * (ν + ν ^ 4) := mul_le_mul_of_nonneg_left hν_le_add hC_pos.le

/-- Uniform small-`ν` regime for the finite-band complementary integral inequality. -/
private theorem exists_compl_integral_regime (κ : IIIa.PlanarFrameKernels)
    (hseed : IIIa.IsSeedKernels κ) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hP : UnforcedLeray.Blueprint.Planar.IsPlanarReference P) (m : ℝ) [Fact (1 < m)] (hm : 8 < m) :
    ∃ (C g ν₀ : ℝ), 0 < C ∧ 0 < g ∧ 0 < ν₀ ∧
      ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ (FI : FlatInstData κ ν (cOf ν) m tr),
            ∀ t ∈ Icc (0 : ℝ) (1.1 / ν), ∀ x : Xmc (cOf ν) m,
              ∀ s ∈ Icc t (2 / ν),
                cmpN (actualPk FI) P.eigenvalue P.kappa ν t x s ≤
                  C * Real.exp (-g * (s - t)) *
                      cmpN (actualPk FI) P.eigenvalue P.kappa ν t x t +
                    C * (ν + ν ^ 4) * ∫ r in t..s, Real.exp (-g * (s - r)) *
                      (‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x true r‖ +
                        ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x false r‖) := by
  obtain ⟨K, bPF, hPFall⟩ := IIIa.perFrameFactsAll κ hseed m hm
  obtain ⟨C₀, h, hC₀, hh, hh_le, hSeedDecay⟩ :=
    IIIa.FrameBlockContractSub.planarDampedComplDecay hseed P hP hm
  have hCp : 0 ≤ 1 + C₀ := by positivity
  have hγ : 0 < P.eigenvalue.re := lt_of_lt_of_le hh hh_le
  obtain ⟨B, hB_pos, hB_contr⟩ := IIIa.exists_block_length_contractionE hC₀ hCp hh hγ
  have hCm_pos : 0 < IIIa.normGrowthConst m := by unfold IIIa.normGrowthConst; positivity
  have hK_num_nn : 0 ≤ IIIa.normGrowthConst m + |P.kappa.re| := by
    have := abs_nonneg P.kappa.re
    positivity
  obtain ⟨ε, b_thr, hε_pos, hb_thr1, hb_thr_exp⟩ :=
    IIIa.FrameBlockContractSub.exists_b_free_rel_bound P.eigenvalue.re hB_pos hK_num_nn
  obtain ⟨b_f0, -, hRelFree⟩ := IIIa.FrameBlockContractSub.relFreeMovingEnergy P hm hε_pos
  set α_free := 2 * Real.exp (-P.eigenvalue.re * B)
  have hα_free_pos : 0 < α_free := by positivity
  have hFreeHyp :
      ∃ b_f : ℝ, 1 ≤ b_f ∧ ∀ b : ℝ, b_f ≤ b → ∃ ν_f : ℝ, 0 < ν_f ∧
        ∀ ν ∈ Ioc 0 ν_f, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ IIIa.clockTheta ν t₂ →
            IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁ = B →
            ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
              ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₁ f ω₀ →
                IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₂)) m
                    (IIIa.JscaleInv (IIIa.clockA ν t₂) (fun x => ((ω₀ t₂ x : ℝ) : ℂ))) ≤
                  ENNReal.ofReal (IIIa.clockN P ν t₁ t₂) *
                    (ENNReal.ofReal α_free *
                      IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₁)) m
                        (IIIa.JscaleInv (IIIa.clockA ν t₁) (fun x => ((f x : ℝ) : ℂ)))) := by
    refine ⟨max b_thr b_f0, hb_thr1.trans (le_max_left _ _), fun b hb => ?_⟩
    obtain ⟨ν_f, hν_f, Hrel⟩ := hRelFree b ((le_max_right _ _).trans hb)
    refine ⟨ν_f, hν_f, fun ν hν tr htr t₁ t₂ ht₁ h12 hbs hZ f hf ω₀ hω₀ => ?_⟩
    have h1 := Hrel ν hν tr htr t₁ t₂ ht₁ h12 hbs f hf ω₀ hω₀
    rw [hZ] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hb_thr_exp b ((le_max_left _ _).trans hb))) zero_le
  obtain ⟨C_uh, b_gap, hC_uh, hb_gap, hGapB⟩ :=
    IIIa.blockCompactDuhamelGapE κ hseed P hP m hm K C₀ h B α_free (1 / 4)
      hC₀ hh hh_le hB_pos hα_free_pos (by norm_num) hSeedDecay hFreeHyp
  obtain ⟨C_pert, b_pert, hC_pert, _, hPertB⟩ :=
    IIIa.shortComplPerturbDuhamel κ IIIa.freeMovingEnergy hseed P hP m hm K
  obtain ⟨C₁, b_osc, hC₁, -, hOscB⟩ := IIIa.complModeForceOscillator κ hseed m hm
  obtain ⟨C₂, b_eul, hC₂, -, hEulB⟩ := IIIa.complModeForceEulerError κ hseed P hP m hm
  set b : ℝ := max (max bPF b_gap) (max b_pert (max b_osc b_eul))
  have hbPF : bPF ≤ b := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb_gap' : b_gap ≤ b := le_trans (le_max_right _ _) (le_max_left _ _)
  have hb_pert' : b_pert ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
  have hb_osc' : b_osc ≤ b :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hb_eul' : b_eul ≤ b :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hb1 : 1 ≤ b := hb_gap.trans hb_gap'
  have hb_pos : 0 < b := lt_of_lt_of_le one_pos hb1
  obtain ⟨ν_pf, hν_pf, HPF⟩ := hPFall b hbPF
  obtain ⟨ν_gap, hν_gap, HGap⟩ := hGapB b hb_gap'
  obtain ⟨ν_pert, hν_pert, HPert⟩ := hPertB b hb_pert'
  obtain ⟨ν_osc, hν_osc, HOsc⟩ := hOscB b hb_osc'
  obtain ⟨ν_eul, hν_eul, HEul⟩ := hEulB b hb_eul'
  set μ_raw := IIIa.normGrowthConst m + 1 + C_pert
  set μ := μ_raw + |P.eigenvalue.re| + |P.kappa.re|
  have hμ_pos : 0 < μ := by
    have := abs_nonneg P.eigenvalue.re
    have := abs_nonneg P.kappa.re
    positivity
  set M_B := Real.exp (μ * B)
  have hMB_ge1 : 1 ≤ M_B := Real.one_le_exp (mul_nonneg hμ_pos.le hB_pos.le)
  set C_force := (1 + 2 * max K 0 ^ 2) * max C₁ C₂
  have hCf_nn : 0 ≤ C_force := by
    have : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left C₁ C₂)
    positivity
  set K_I := max (6 * C_uh * C_force) (6 * M_B * C_force)
  have hKI_nn : 0 ≤ K_I := le_trans (by positivity) (le_max_left _ _)
  set C : ℝ := max (2 * (3 : ℝ) ^ ((m - 3) / 2) * (3 : ℝ) ^ ((3 : ℝ) / 2) * M_B)
    (4 * (3 : ℝ) ^ ((m - 3) / 2) * M_B * K_I) + 1
  have hC_pos : 0 < C := by positivity
  set ν₀ : ℝ := min (min ν_pf ν_gap) (min ν_pert (min ν_osc (min ν_eul (min 1 (1 / (3 * b))))))
  have hν₀_pos : 0 < ν₀ :=
    lt_min (lt_min hν_pf hν_gap)
      (lt_min hν_pert (lt_min hν_osc (lt_min hν_eul (lt_min zero_lt_one (by positivity)))))
  refine ⟨C, (Real.log 2 / B) / 9, ν₀, hC_pos,
    div_pos (div_pos (Real.log_pos (by norm_num)) hB_pos) (by norm_num), hν₀_pos, ?_⟩
  intro ν hν hνle tr htr FI t ht x s hs
  have hν_p : ν ∈ Ioc 0 ν_pf :=
    ⟨hν, hνle.trans (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hν_g : ν ∈ Ioc 0 ν_gap :=
    ⟨hν, hνle.trans (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hr1 : ν ≤ min ν_pert (min ν_osc (min ν_eul (min 1 (1 / (3 * b))))) :=
    hνle.trans (min_le_right _ _)
  have hν_pt : ν ∈ Ioc 0 ν_pert := ⟨hν, hr1.trans (min_le_left _ _)⟩
  have hr2 : ν ≤ min ν_osc (min ν_eul (min 1 (1 / (3 * b)))) := hr1.trans (min_le_right _ _)
  have hν_o : ν ∈ Ioc 0 ν_osc := ⟨hν, hr2.trans (min_le_left _ _)⟩
  have hr3 : ν ≤ min ν_eul (min 1 (1 / (3 * b))) := hr2.trans (min_le_right _ _)
  have hν_e : ν ∈ Ioc 0 ν_eul := ⟨hν, hr3.trans (min_le_left _ _)⟩
  have hr4 : ν ≤ min 1 (1 / (3 * b)) := hr3.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hr4.trans (min_le_left _ _)
  have hν_b : ν ≤ 1 / (3 * b) := hr4.trans (min_le_right _ _)
  have hbν : b ≤ 1 / (3 * ν) := by
    rw [le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * b)).1 hν_b
    nlinarith
  have hbθ : ∀ r ∈ Icc (0 : ℝ) (2 / ν), b ≤ IIIa.clockTheta ν r := fun r hr =>
    hbν.trans (clockTheta_inv_bounds hν hr).2.2
  have hPF : IIIa.PerFrameFacts κ ν m b K := HPF ν hν_p
  obtain ⟨tr', hbuc', hcast⟩ := exists_train_cast m (cOf_eq_rpow hν) tr htr
  obtain ⟨u, hu⟩ := FI.ev.flow t ht.1 x
  set w : ℝ → ℝ × ℝ → ℂ := fun q => xFn (FI.ev.U q t x)
  have hflow : IIIa.IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr' t (xFn x) w u :=
    hcast t _ _ u hu
  have hzero : IIIa.HasZeroCirculation (ν ^ (-2 : ℝ)) (xFn x) := by
    rw [← cOf_eq_rpow hν]
    exact xFn_zeroCirc x
  have hHom_half :
      C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free +
        Real.exp (-P.eigenvalue.re * B) + 1 / 4 ≤ 1 / 2 := by
    simp only [α_free]
    linarith [hB_contr]
  refine compl_bound_at_nu hm P hν hB_pos hMB_ge1 hKI_nn hC_pos
    (le_trans (le_max_left _ _) (by linarith))
    (le_trans (le_max_right _ _) (by linarith))
    hPF FI ht.1 hs.1 hs.2 x ?_ ?_
  · intro t₁ t₂ ht1 h12 ht2s hZ
    have ht₁0 : 0 ≤ t₁ := ht.1.trans ht1
    have ht₂2 : t₂ ≤ 2 / ν := ht2s.trans hs.2
    have hbt₂ : b ≤ IIIa.clockTheta ν t₂ := hbθ t₂ ⟨ht₁0.trans h12, ht₂2⟩
    have hw₁ : IIIa.IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr' t₁ (w t₁) w u := hflow.restart ht1
    have hz₁ : IIIa.HasZeroCirculation (ν ^ (-2 : ℝ)) (w t₁) :=
      IIIa.zeroCirculationPreserved ν (ν ^ (-2 : ℝ)) m (Real.rpow_pos_of_pos hν _)
        (by linarith) tr' t (xFn x) w u hflow hzero t₁ ht1
    have hraw := HGap ν hν_g hPF tr' hbuc' t₁ t₂ ht₁0 h12 hbt₂ hZ (w t₁) w u hw₁ hz₁
    have hDuh :
        IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₂)) m
            (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) w t₂) ≤
          ENNReal.ofReal (IIIa.clockN P ν t₁ t₂ * (1 / 2)) *
              IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₁)) m
                (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) w t₁) +
            ∫⁻ r in Ioc t₁ t₂,
              ENNReal.ofReal ((IIIa.clockA ν r) ^ (-2 : ℝ) * (IIIa.clockN P ν r t₂ * C_uh)) *
                (∑ j : Fin 2,
                  ENNReal.ofReal ‖IIIa.ampl (IIIa.periodizedFrame κ ν m b K hν hPF) w r j‖ *
                    IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
                      (IIIa.complModeForce κ P (IIIa.periodizedFrame κ ν m b K hν hPF) tr' r j)) := by
      refine hraw.trans (add_le_add ?_ le_rfl)
      rw [ENNReal.ofReal_mul (IIIa.clockN_pos P hν ht₁0 (ht₁0.trans h12)).le, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hHom_half) zero_le) zero_le
    have hblk := single_block_relComplR_le hm P hν hν1 hPF tr' FI ht.1 ht1 h12 ht₂2 hbt₂
      hC₁ hC₂ (by norm_num) hC_uh (fun r => IIIa.clockN P ν r t₂ * C_uh)
      (fun r hr => ⟨mul_nonneg (IIIa.clockN_pos P hν (ht₁0.trans hr.1.le) (ht₁0.trans h12)).le hC_uh,
        le_rfl⟩)
      (fun r hr j => HOsc ν hν_o r (ht₁0.trans hr.1.le)
        (hbθ r ⟨ht₁0.trans hr.1.le, hr.2.trans ht₂2⟩) j)
      (fun r hr j => HEul ν hν_e tr' hbuc' r (ht₁0.trans hr.1.le)
        (hbθ r ⟨ht₁0.trans hr.1.le, hr.2.trans ht₂2⟩) j)
      x hDuh
    refine hblk.trans (add_le_add le_rfl ?_)
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hν.le) ?_
    exact intervalIntegral.integral_nonneg h12 fun r _ => ampSum_nonneg FI P t x r
  · intro t₁ t₂ ht1 h12 ht2s hZ
    have ht₁0 : 0 ≤ t₁ := ht.1.trans ht1
    have ht₂0 : 0 ≤ t₂ := ht₁0.trans h12
    have ht₂2 : t₂ ≤ 2 / ν := ht2s.trans hs.2
    have hbt₂ : b ≤ IIIa.clockTheta ν t₂ := hbθ t₂ ⟨ht₂0, ht₂2⟩
    have hθ1 : 1 ≤ IIIa.clockTheta ν t₂ := hb1.trans hbt₂
    have hw₁ : IIIa.IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr' t₁ (w t₁) w u := hflow.restart ht1
    have hz₁ : IIIa.HasZeroCirculation (ν ^ (-2 : ℝ)) (w t₁) :=
      IIIa.zeroCirculationPreserved ν (ν ^ (-2 : ℝ)) m (Real.rpow_pos_of_pos hν _)
        (by linarith) tr' t (xFn x) w u hflow hzero t₁ ht1
    have hraw := HPert ν hν_pt hPF tr' hbuc' t₁ t₂ ht₁0 h12 hbt₂ (w t₁) w u hw₁ hz₁
    have hHom_real :
        Real.exp (μ_raw * (IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁)) ≤
          IIIa.clockN P ν t₁ t₂ * M_B := by
      calc Real.exp (μ_raw * (IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁))
          ≤ IIIa.clockN P ν t₁ t₂ *
              Real.exp (μ * (IIIa.movingZ ν t₂ - IIIa.movingZ ν t₁)) :=
            IIIa.FrameShortBlockSub.exp_mul_le_clockN_mul_exp P μ_raw hν ht₁0 h12 hθ1
        _ ≤ IIIa.clockN P ν t₁ t₂ * M_B :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hZ hμ_pos.le))
              (IIIa.clockN_pos P hν ht₁0 ht₂0).le
    have hDuh :
        IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₂)) m
            (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) w t₂) ≤
          ENNReal.ofReal (IIIa.clockN P ν t₁ t₂ * M_B) *
              IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν t₁)) m
                (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) w t₁) +
            ∫⁻ r in Ioc t₁ t₂,
              ENNReal.ofReal ((IIIa.clockA ν r) ^ (-2 : ℝ) *
                  Real.exp (μ_raw * (IIIa.movingZ ν t₂ - IIIa.movingZ ν r))) *
                (∑ j : Fin 2,
                  ENNReal.ofReal ‖IIIa.ampl (IIIa.periodizedFrame κ ν m b K hν hPF) w r j‖ *
                    IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
                      (IIIa.complModeForce κ P (IIIa.periodizedFrame κ ν m b K hν hPF) tr' r j)) := by
      refine hraw.trans (add_le_add ?_ le_rfl)
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hHom_real) zero_le
    have hW : ∀ r ∈ Ioc t₁ t₂,
        0 ≤ Real.exp (μ_raw * (IIIa.movingZ ν t₂ - IIIa.movingZ ν r)) ∧
          Real.exp (μ_raw * (IIIa.movingZ ν t₂ - IIIa.movingZ ν r)) ≤
            IIIa.clockN P ν r t₂ * M_B := by
      intro r hr
      have hr0 : 0 ≤ r := ht₁0.trans hr.1.le
      have hZr_le : IIIa.movingZ ν t₂ - IIIa.movingZ ν r ≤ B := by
        have := IIIa.FrameStableSub.movingZ_le_movingZ hν ht₁0 hr.1.le
        linarith
      refine ⟨(Real.exp_pos _).le, ?_⟩
      calc Real.exp (μ_raw * (IIIa.movingZ ν t₂ - IIIa.movingZ ν r))
          ≤ IIIa.clockN P ν r t₂ *
              Real.exp (μ * (IIIa.movingZ ν t₂ - IIIa.movingZ ν r)) :=
            IIIa.FrameShortBlockSub.exp_mul_le_clockN_mul_exp P μ_raw hν hr0 hr.2 hθ1
        _ ≤ IIIa.clockN P ν r t₂ * M_B :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hZr_le hμ_pos.le))
              (IIIa.clockN_pos P hν hr0 ht₂0).le
    have hblk := single_block_relComplR_le hm P hν hν1 hPF tr' FI ht.1 ht1 h12 ht₂2 hbt₂
      hC₁ hC₂ (by linarith) (by linarith)
      (fun r => Real.exp (μ_raw * (IIIa.movingZ ν t₂ - IIIa.movingZ ν r))) hW
      (fun r hr j => HOsc ν hν_o r (ht₁0.trans hr.1.le)
        (hbθ r ⟨ht₁0.trans hr.1.le, hr.2.trans ht₂2⟩) j)
      (fun r hr j => HEul ν hν_e tr' hbuc' r (ht₁0.trans hr.1.le)
        (hbθ r ⟨ht₁0.trans hr.1.le, hr.2.trans ht₂2⟩) j)
      x hDuh
    refine hblk.trans (add_le_add le_rfl ?_)
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hν.le) ?_
    exact intervalIntegral.integral_nonneg h12 fun r _ => ampSum_nonneg FI P t x r

/-- **(Leaf 1) Finite-band complementary integral inequality on `actualPk FI`** (source lines
4366-4394 and 2975-3004 `prop:short-full-clock`). -/
theorem actualComplIntegralBound (D : SeqData) :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.ActualComplIntegralBound D := by
  intro dm dp hD κ hκ m hfact hm
  obtain ⟨C, g, ν₀, hC, hg, hν₀, hReg⟩ :=
    exists_compl_integral_regime κ hκ.1 D.Pl hD.planar m hm
  have hlim := retNu_tendsto D.σ₀ hD.omega_ne
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually_lt tendsto_const_nhds hν₀)
  refine ⟨C, g, N, hC, hg, fun n hn FI t ht x s hs => ?_⟩
  exact hReg (nu D n) (retNu_pos D.Pl D.σ₀ n) (hN n hn).le (D.train n) (D.train_buc n)
    FI t ht x s hs

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

end
