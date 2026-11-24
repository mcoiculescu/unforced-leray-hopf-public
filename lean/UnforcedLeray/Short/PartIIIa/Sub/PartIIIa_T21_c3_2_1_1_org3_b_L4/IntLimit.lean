import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.IntPlanar
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.TrainGradCoeff
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3

/-!
# Leaf B4, interaction part: proof of `IntLimitLeaf` (SP 2974-2976)

`movLInt tr r Φ = -(K_d Φ)·∇E_mov(r)` splits as `-(K_d Φ)·(∇E_mov(r) - ∇E₀) - (K_d Φ)·∇E₀`.
* The coefficient `∇E_mov(r) - ∇E₀` is `O(ν³/θ + d⁻²)` in the weighted sup norm on the cell
  (`movingTrainGradE_sub_datum_bound`, and the Gaussian lattice tail `gf_cell_tail_weighted_bound`
  for `∇ curl P_d v₀ - ∇E₀`), so the first term is small by the cylinder operator bound
  (`RelIntA.cxInter_bound`).
* The second term is `C₂ d⁻²`-close to `couplingW W` (`coupling_cyl_bound` with
  `IIb.planarKernelBoundStep_proof`).
Both are `O(ν³/θ) = O(1/b)` (`d⁻² = ν³/θ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

namespace PlanarB

namespace L4

/-- The moving train vorticity gradient as a planar vector field. -/
def gE {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) :
    ℝ × ℝ → ℝ × ℝ :=
  fun y => (movingTrainGradE tr r y 0, movingTrainGradE tr r y 1)

theorem movLInt_eq_cxInter {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (r : ℝ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    movLInt tr r Φ y =
      RelIntA.cxInter (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
          (fun x => gE tr r x - IIb.planarGradE 0 x) Φ y +
        RelIntA.cxInter (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (IIb.planarGradE 0) Φ y := by
  unfold movLInt RelIntA.cxInter gE
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

theorem cellZeroExt_add' (d : ℝ) (f g : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    cellZeroExt d (fun x => f x + g x) y = cellZeroExt d f y + cellZeroExt d g y := by
  unfold cellZeroExt
  by_cases hy : y ∈ B0579.cell d
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, add_zero]

/-- The weighted coefficient bound of `∇E_mov(r) - ∇E₀` on the cell. -/
theorem gE_coeff {m : ℝ} {kw : ℕ} (hkw : m / 2 + 1 ≤ (kw : ℝ)) {C_E C_X C_Y : ℝ}
    (hX : ∀ c : ℝ, 1 ≤ c → ∀ a ∈ Icc (1 : ℝ) (1 + 1), ∀ x ∈ B0579.cell c,
      |B0146.latticeSum c (IIb.eExpX a) x - IIb.eExpX a (B0146.shift c 0 x)| *
        B0579.jb x ^ (m / 2 + 1) ≤ C_X * c ^ (-2 : ℝ))
    (hY : ∀ c : ℝ, 1 ≤ c → ∀ a ∈ Icc (1 : ℝ) (1 + 1), ∀ x ∈ B0579.cell c,
      |B0146.latticeSum c (IIb.eExpY a) x - IIb.eExpY a (B0146.shift c 0 x)| *
        B0579.jb x ^ (m / 2 + 1) ≤ C_Y * c ^ (-2 : ℝ))
    {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ} (hr : 0 ≤ r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hE : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)), ∀ k : Fin 2,
      B0579.jb y ^ kw * |movingTrainGradE tr r y k -
        B0579.pd k (UnforcedLeray.Cyl.curl
          (UnforcedLeray.Train.datum (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) y| ≤
        C_E * ν ^ 3 / clockTheta ν r) :
    IIb.IsCylWeightedCoeff (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
      (2 * (C_E * ν ^ 3 / clockTheta ν r) +
        (C_X + C_Y) * (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ (-2 : ℝ))
      (fun x => gE tr r x - IIb.planarGradE 0 x) := by
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  refine ⟨((EulerErrorSub.continuous_movingTrainGradE tr hr 0).prodMk
    (EulerErrorSub.continuous_movingTrainGradE tr hr 1)).sub (IIb.continuous_planarGradE 0),
    fun x hx => ?_⟩
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hjbk : B0579.jb x ^ (m / 2 + 1) ≤ B0579.jb x ^ kw := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hjb1 hkw
  have hjb_nn : 0 ≤ B0579.jb x ^ (m / 2 + 1) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have ha : (1 : ℝ) + 0 ∈ Icc (1 : ℝ) (1 + 1) := ⟨by norm_num, by norm_num⟩
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the periodized Gaussian gradient is a lattice sum
  have hdat : UnforcedLeray.Train.datum d = UnforcedLeray.Train.Vc 1 d ((0 : ℝ) / 1) := by
    rw [zero_div, UnforcedLeray.Train.Vc_zero]
  have hL0 : B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x =
      B0146.latticeSum d (IIb.eExpX (1 + 0)) x := by
    rw [hdat]; exact IIb.pd_zero_curl_Vc_eq_latticeSum one_pos hd h0mem x
  have hL1 : B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x =
      B0146.latticeSum d (IIb.eExpY (1 + 0)) x := by
    rw [hdat]; exact IIb.pd_one_curl_Vc_eq_latticeSum one_pos hd h0mem x
  have hP0 : (IIb.planarGradE 0 x).1 = IIb.eExpX (1 + 0) (B0146.shift d 0 x) :=
    (IIb.eExpX_shift_zero_eq_planarGradE_fst le_rfl x).symm
  have hP1 : (IIb.planarGradE 0 x).2 = IIb.eExpY (1 + 0) (B0146.shift d 0 x) :=
    (IIb.eExpY_shift_zero_eq_planarGradE_snd le_rfl x).symm
  have hX' := hX d hd (1 + 0) ha x hx
  have hY' := hY d hd (1 + 0) ha x hx
  have hE0 := hE x hx 0
  have hE1 := hE x hx 1
  set e0 := movingTrainGradE tr r x 0 -
    B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x with he0
  set e1 := movingTrainGradE tr r x 1 -
    B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x with he1
  set l0 := B0146.latticeSum d (IIb.eExpX (1 + 0)) x -
    IIb.eExpX (1 + 0) (B0146.shift d 0 x) with hl0
  set l1 := B0146.latticeSum d (IIb.eExpY (1 + 0)) x -
    IIb.eExpY (1 + 0) (B0146.shift d 0 x) with hl1
  have hs0 : (gE tr r x - IIb.planarGradE 0 x).1 = e0 + l0 := by
    simp only [gE, Prod.fst_sub, he0, hl0, hL0, hP0]; ring
  have hs1 : (gE tr r x - IIb.planarGradE 0 x).2 = e1 + l1 := by
    simp only [gE, Prod.snd_sub, he1, hl1, hL1, hP1]; ring
  rw [hs0, hs1]
  have hE0' : |e0| * B0579.jb x ^ (m / 2 + 1) ≤ C_E * ν ^ 3 / clockTheta ν r := by
    calc |e0| * B0579.jb x ^ (m / 2 + 1) ≤ |e0| * B0579.jb x ^ kw :=
          mul_le_mul_of_nonneg_left hjbk (abs_nonneg _)
      _ = B0579.jb x ^ kw * |e0| := mul_comm _ _
      _ ≤ _ := hE0
  have hE1' : |e1| * B0579.jb x ^ (m / 2 + 1) ≤ C_E * ν ^ 3 / clockTheta ν r := by
    calc |e1| * B0579.jb x ^ (m / 2 + 1) ≤ |e1| * B0579.jb x ^ kw :=
          mul_le_mul_of_nonneg_left hjbk (abs_nonneg _)
      _ = B0579.jb x ^ kw * |e1| := mul_comm _ _
      _ ≤ _ := hE1
  calc (|e0 + l0| + |e1 + l1|) * B0579.jb x ^ (m / 2 + 1)
      ≤ (|e0| + |l0| + (|e1| + |l1|)) * B0579.jb x ^ (m / 2 + 1) :=
        mul_le_mul_of_nonneg_right (add_le_add (abs_add_le _ _) (abs_add_le _ _)) hjb_nn
    _ = |e0| * B0579.jb x ^ (m / 2 + 1) + |e1| * B0579.jb x ^ (m / 2 + 1) +
        (|l0| * B0579.jb x ^ (m / 2 + 1) + |l1| * B0579.jb x ^ (m / 2 + 1)) := by ring
    _ ≤ 2 * (C_E * ν ^ 3 / clockTheta ν r) + (C_X * d ^ (-2 : ℝ) + C_Y * d ^ (-2 : ℝ)) := by
        linarith
    _ = _ := by ring

/-- **The interaction leaf** (SP 2974-2976). -/
theorem intLimitLeaf : IntLimitLeaf := by
  intro m hm hm8 ε hε
  set k : ℝ := m / 2 + 1 with hk_def
  have hk : 0 ≤ k := by rw [hk_def]; linarith
  obtain ⟨M₀, hM₀, hpl⟩ := IIb.planarGradE_sup_bound k hk 1 one_pos
  obtain ⟨C_X, hC_X, htX⟩ := IIb.gf_cell_tail_weighted_bound (Sg := 1) hk IIb.gf_eExpX
  obtain ⟨C_Y, hC_Y, htY⟩ := IIb.gf_cell_tail_weighted_bound (Sg := 1) hk IIb.gf_eExpY
  set kw : ℕ := ⌈k⌉₊ with hkw_def
  have hkw : k ≤ (kw : ℝ) := Nat.le_ceil k
  obtain ⟨C_E, ν_E, hC_E, hν_E, hE⟩ := EulerErrorSub.movingTrainGradE_sub_datum_bound kw
  obtain ⟨C₂, hC₂, hPB⟩ := IIb.planarKernelBoundStep_proof m hm8 1 one_pos
  obtain ⟨AplOp, -, hApl⟩ := IIb.planarInteractionCompactStep_proof m hm8 1 one_pos
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hA0 : IIb.IsPlanarInteractionOp m 0 (AplOp 0) := (hApl 0 h0mem).1
  set CK := IIb.cylKernelBoundConst m with hCK
  have hCK0 : 0 < CK := IIb.cylKernelBoundConst_pos m
  set Ctot := 2 * CK * (2 * C_E + C_X + C_Y) + 2 * C₂ + 1 with hCtot
  have hCtot0 : 0 < Ctot := by rw [hCtot]; positivity
  refine ⟨max 1 (Ctot / ε), fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_max_left _ _) hb
  have hbC : Ctot / ε ≤ b := le_trans (le_max_right _ _) hb
  refine ⟨min ν_E 1, lt_min hν_E one_pos, fun ν hν tr htr r hr hθ Φ hΦs hΦc W hW => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hνE : ν ∈ Ioc 0 ν_E := ⟨hν0, hν.2.trans (min_le_left _ _)⟩
  have hθ1 : 1 ≤ clockTheta ν r := hb1.trans hθ
  have hθ0 : 0 < clockTheta ν r := lt_of_lt_of_le one_pos hθ1
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  have hd : 1 ≤ d := ComplCouplingSub.one_le_cellLen_of_theta hν0 hν1 hr hθ1
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd
  set δ := ν ^ 3 / clockTheta ν r with hδ_def
  have hδ0 : 0 ≤ δ := by rw [hδ_def]; positivity
  have hdδ : d ^ (-2 : ℝ) = δ := by
    rw [hδ_def, ← ComplCouplingSub.inv_cellLen_sq_eq_nu_cube_div_theta hν0 hr, ← hd_def,
      Real.rpow_neg hd0.le, one_div]
    norm_cast
  have hδb : δ ≤ 1 / b := by
    rw [hδ_def]
    have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
    calc ν ^ 3 / clockTheta ν r ≤ 1 / clockTheta ν r :=
          div_le_div_of_nonneg_right hν3 hθ0.le
      _ ≤ 1 / b := one_div_le_one_div_of_le (lt_of_lt_of_le one_pos hb1) hθ
  -- the coefficient bounds
  have hb0 : IIb.IsCylWeightedCoeff d m M₀ (IIb.planarGradE 0) :=
    ⟨IIb.continuous_planarGradE 0, fun x _ => hpl 0 h0mem x⟩
  have hbtr := gE_coeff (m := m) (kw := kw) hkw htX htY tr hr hd
    (fun y hy k' => hE ν hνE tr htr r hr hθ1 y hy k')
  set Btr := 2 * (C_E * ν ^ 3 / clockTheta ν r) + (C_X + C_Y) * d ^ (-2 : ℝ) with hBtr
  have hBtr0 : 0 ≤ Btr := by rw [hBtr]; positivity
  have hBtrδ : Btr = (2 * C_E + C_X + C_Y) * δ := by
    rw [hBtr, hdδ, hδ_def]; ring
  -- the field in the cylinder spaces
  obtain ⟨hΦm, hΦn⟩ := memLp_plane_of_rep W hW
  have hΦcell : MemLp Φ 2 (B0579.cellMeasure d m) := by
    rw [IIb.cellMeasure_eq_restrict_planeMeasure]; exact hΦm.restrict _
  have hxΦ : xNorm d m Φ ≤ ENNReal.ofReal ‖W‖ := by
    unfold xNorm
    rw [← hΦn, IIb.cellMeasure_eq_restrict_planeMeasure]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  -- first term: the train coefficient
  obtain ⟨hm1, hb1'⟩ := RelIntA.cxInter_bound hd hm hBtr0 hbtr hΦcell
  have hmem1 : MemLp (RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ) 2
      (B0579.cellMeasure d m) :=
    ⟨hm1, lt_of_le_of_lt hb1' (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΦcell.2)⟩
  have hT1m := (BlockPropagatorSub.memLp_cellZeroExt_cToPlane d m hmem1).1
  have hT1n : eLpNorm (fun z => cellZeroExt d
      (RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ) (cToPlane z)) 2
      (Planar.wMeasure m) ≤ ENNReal.ofReal (2 * CK * Btr * ‖W‖) := by
    rw [BlockPropagatorSub.eLpNorm_cellZeroExt_cToPlane d m hm1]
    calc xNorm d m (RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ)
        ≤ ENNReal.ofReal (2 * CK * Btr) * xNorm d m Φ := hb1'
      _ ≤ ENNReal.ofReal (2 * CK * Btr) * ENNReal.ofReal ‖W‖ := by gcongr
      _ = ENNReal.ofReal (2 * CK * Btr * ‖W‖) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  -- second term: the Gaussian coefficient against the planar coupling
  have hT : IIb.IsGaussCylInteractionOp d m 0 (IIb.cylWeightedOp hd hm hM₀.le hb0) :=
    IIb.isCylWeightedOp_cylWeightedOp hd hm hM₀.le hb0
  have hPB' := hPB d hd 0 h0mem _ (AplOp 0) hT hA0
  obtain ⟨hT2m, hT2n⟩ := coupling_cyl_bound hm hd hM₀.le hb0 (AplOp 0) hA0 hPB' W hW
  -- assembly
  have hsplit : (fun z => cellZeroExt d (movLInt tr r Φ) (cToPlane z) -
      Planar.couplingW hm W z) = fun z =>
      cellZeroExt d (RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ)
        (cToPlane z) +
      (cellZeroExt d (RelIntA.cxInter d (IIb.planarGradE 0) Φ) (cToPlane z) -
        Planar.couplingW hm W z) := by
    funext z
    have h := cellZeroExt_add' d
      (RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ)
      (RelIntA.cxInter d (IIb.planarGradE 0) Φ) (cToPlane z)
    have hf : movLInt tr r Φ = fun y =>
        RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ y +
          RelIntA.cxInter d (IIb.planarGradE 0) Φ y := by
      funext y; exact movLInt_eq_cxInter tr r Φ y
    rw [hf, h]
    ring
  have hmeasF : AEStronglyMeasurable (fun z => cellZeroExt d (movLInt tr r Φ) (cToPlane z) -
      Planar.couplingW hm W z) (Planar.wMeasure m) := by
    rw [hsplit]; exact hT1m.add hT2m
  refine ⟨?_, ?_⟩
  · refine (hmeasF.add (Lp.aestronglyMeasurable (Planar.couplingW hm W))).congr
      (Eventually.of_forall fun z => ?_)
    simp
  · rw [hsplit]
    calc eLpNorm (fun z =>
          cellZeroExt d (RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ)
            (cToPlane z) +
          (cellZeroExt d (RelIntA.cxInter d (IIb.planarGradE 0) Φ) (cToPlane z) -
            Planar.couplingW hm W z)) 2 (Planar.wMeasure m)
        ≤ eLpNorm (fun z => cellZeroExt d
            (RelIntA.cxInter d (fun x => gE tr r x - IIb.planarGradE 0 x) Φ) (cToPlane z)) 2
            (Planar.wMeasure m) +
          eLpNorm (fun z => cellZeroExt d (RelIntA.cxInter d (IIb.planarGradE 0) Φ)
            (cToPlane z) - Planar.couplingW hm W z) 2 (Planar.wMeasure m) :=
          eLpNorm_add_le hT1m hT2m (by norm_num)
      _ ≤ ENNReal.ofReal (2 * CK * Btr * ‖W‖) +
            ENNReal.ofReal (2 * (C₂ * d ^ (-2 : ℝ)) * ‖W‖) := add_le_add hT1n hT2n
      _ = ENNReal.ofReal ((2 * CK * (2 * C_E + C_X + C_Y) + 2 * C₂) * δ * ‖W‖) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), hBtrδ, hdδ]
          congr 1; ring
      _ ≤ ENNReal.ofReal (ε * ‖W‖) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          have hb0' : 0 < b := lt_of_lt_of_le one_pos hb1
          have h1 : (2 * CK * (2 * C_E + C_X + C_Y) + 2 * C₂) * δ ≤ Ctot * δ :=
            mul_le_mul_of_nonneg_right (by rw [hCtot]; linarith) hδ0
          have h2 : Ctot * δ ≤ Ctot * (1 / b) := mul_le_mul_of_nonneg_left hδb hCtot0.le
          have h3 : Ctot * (1 / b) ≤ ε := by
            rw [mul_one_div, div_le_iff₀ hb0']
            rw [div_le_iff₀ hε] at hbC
            linarith
          linarith

end L4

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
