import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.RankAux
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b.FrameCont

/-!
# Leaf B4, finite-rank part: dual rows and the algebraic decomposition (SP 2894-2925)

* `lam_sub_ell`: `|Λ_i(Φ) - ℓ_i(Φ)| = O(d⁻¹) ‖W‖` (Gram inverse `G⁻¹ = I + O(d⁻²)`, the dual
  lattice tail `P_d λ_i - λ_i = O(d⁻²)` on the cell, and the `O(|y|⁻²)` tail of `λ_i` off the
  cell, through the weighted Cauchy–Schwarz inequality on a cell containing the support of `Φ`);
* `movH0_eq_add`: `H₀ = λ'_i Λ_i + ⟨H₀ - λ'_i Λ_i⟩` through `movLamDualSub`;
* `frp_decomp`: the pointwise algebraic decomposition of `movFrameRankPert` against
  `Σ_i (γ - 1 - λ_i) ℓ_i e_i`.
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

theorem cell_mono {d c : ℝ} (h : d ≤ c) : B0579.cell d ⊆ B0579.cell c := by
  intro x hx
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

theorem abs_fst_ge_of_not_mem_cell {d : ℝ} (hd : 0 ≤ d) {x : ℝ × ℝ} (hx : x ∉ B0579.cell d) :
    d / 2 ≤ |x.1| := by
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, not_and_or, not_le,
    not_lt] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- **Dual rows against the planar dual kernels**: `|Λ_i(Φ) - ℓ_i(Φ)| ≤ C d⁻¹ ‖W‖`. -/
theorem lam_sub_ell (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) {m : ℝ} (hm : 8 < m) :
    ∃ C D : ℝ, 0 ≤ C ∧ 1 ≤ D ∧ ∀ d : ℝ, D ≤ d → ∀ (i : Fin 2) (Φ : ℝ × ℝ → ℂ),
      Continuous Φ → HasCompactSupport Φ →
      ∀ W : Planar.L2w m, (⇑W =ᵐ[volume] fun z => Φ (cToPlane z)) →
        ‖(∫ x in B0579.cell d, perLam κ d i x * Φ x) - ∫ x, κ.lamP i x * Φ x‖ ≤
          C / d * ‖W‖ := by
  obtain ⟨C₁, hC₁, hlt⟩ := EulerSubCore.lamP_tails hκ
  obtain ⟨C_inv, D_inv, hCinv, hDinv, hinv⟩ := ComplCouplingEuler.perGram_inv_sub_id_bound κ
  obtain ⟨Cl, hCl⟩ := κ.lamP_decay
  have hm1 : 1 < m := by linarith
  obtain ⟨N, hN, hxneg⟩ := xNorm_neg_le_of_bound hm1
  set A : ℝ := 2 * C_inv * (|Cl| + C₁) + C₁ with hA
  set Bc : ℝ := A + 2 * |Cl| with hBc
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  refine ⟨Bc * N, D_inv, by positivity, hDinv, fun d hd i Φ hΦc hΦs W hW => ?_⟩
  have hd1 : 1 ≤ d := hDinv.trans hd
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd1
  have hlam_le : ∀ (k : Fin 2) (y : ℝ × ℝ), ‖κ.lamP k y‖ ≤ |Cl| * ((1 + |y.1| + |y.2|)⁻¹) ^ 2 :=
    fun k y => (hCl k y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hinvsq_le : ∀ y : ℝ × ℝ, ((1 + |y.1| + |y.2|)⁻¹) ^ 2 ≤ 1 := by
    intro y
    have h1 : 1 ≤ 1 + |y.1| + |y.2| := by linarith [abs_nonneg y.1, abs_nonneg y.2]
    have h2 : (1 + |y.1| + |y.2|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h3 : 0 ≤ (1 + |y.1| + |y.2|)⁻¹ := by positivity
    nlinarith
  have hlam_bdd : ∀ (k : Fin 2) (y : ℝ × ℝ), ‖κ.lamP k y‖ ≤ |Cl| := fun k y =>
    (hlam_le k y).trans (by nlinarith [hinvsq_le y, abs_nonneg Cl])
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hperLam0 : ∀ (k : Fin 2) (y : ℝ × ℝ), y ∈ B0579.cell d → ‖perLam0 κ d k y‖ ≤ |Cl| + C₁ := by
    intro k y hy
    have h := (hlt d hd1 k y hy).1
    have hC1d : C₁ / d ^ 2 ≤ C₁ := div_le_self hC₁ hd2
    calc ‖perLam0 κ d k y‖ = ‖(perLam0 κ d k y - κ.lamP k y) + κ.lamP k y‖ := by ring_nf
      _ ≤ ‖perLam0 κ d k y - κ.lamP k y‖ + ‖κ.lamP k y‖ := norm_add_le _ _
      _ ≤ C₁ + |Cl| := add_le_add (h.trans hC1d) (hlam_bdd k y)
      _ = |Cl| + C₁ := by ring
  -- pointwise bound of `g = 1_cell Λ_i - λ_i`
  set g : ℝ × ℝ → ℂ := fun x => (B0579.cell d).indicator (perLam κ d i) x - κ.lamP i x with hg
  have hgb : ∀ x, ‖g x‖ ≤ Bc / d := by
    intro x
    by_cases hx : x ∈ B0579.cell d
    · simp only [hg, Set.indicator_of_mem hx]
      have hsplit : perLam κ d i x - κ.lamP i x =
          (∑ k : Fin 2, ((perGram κ d)⁻¹ i k - if i = k then 1 else 0) * perLam0 κ d k x) +
            (perLam0 κ d i x - κ.lamP i x) := by
        unfold perLam
        simp only [Fin.sum_univ_two]
        fin_cases i <;> simp <;> ring
      rw [hsplit]
      have hk : ∀ k : Fin 2, ‖((perGram κ d)⁻¹ i k - if i = k then 1 else 0) * perLam0 κ d k x‖ ≤
          C_inv / d ^ 2 * (|Cl| + C₁) := by
        intro k
        rw [norm_mul]
        exact mul_le_mul (hinv d hd i k) (hperLam0 k x hx) (norm_nonneg _) (by positivity)
      have htail := (hlt d hd1 i x hx).1
      calc ‖(∑ k : Fin 2, ((perGram κ d)⁻¹ i k - if i = k then 1 else 0) * perLam0 κ d k x) +
            (perLam0 κ d i x - κ.lamP i x)‖
          ≤ ‖∑ k : Fin 2, ((perGram κ d)⁻¹ i k - if i = k then 1 else 0) * perLam0 κ d k x‖ +
              ‖perLam0 κ d i x - κ.lamP i x‖ := norm_add_le _ _
        _ ≤ (∑ k : Fin 2, ‖((perGram κ d)⁻¹ i k - if i = k then 1 else 0) *
              perLam0 κ d k x‖) + C₁ / d ^ 2 := add_le_add (norm_sum_le _ _) htail
        _ ≤ 2 * (C_inv / d ^ 2 * (|Cl| + C₁)) + C₁ / d ^ 2 := by
            rw [Fin.sum_univ_two]; linarith [hk 0, hk 1]
        _ = A / d ^ 2 := by rw [hA]; ring
        _ ≤ A / d := div_le_div_of_nonneg_left hA0 hd0 (by nlinarith)
        _ ≤ Bc / d := div_le_div_of_nonneg_right (by rw [hBc]; linarith [abs_nonneg Cl]) hd0.le
    · simp only [hg, Set.indicator_of_notMem hx, zero_sub, norm_neg]
      have hx1 := abs_fst_ge_of_not_mem_cell hd0.le hx
      have hpos : 0 < 1 + |x.1| + |x.2| := by positivity
      have hge : d / 2 ≤ 1 + |x.1| + |x.2| := by linarith [abs_nonneg x.2]
      have hinv1 : (1 + |x.1| + |x.2|)⁻¹ ≤ 2 / d := by
        rw [inv_le_comm₀ hpos (by positivity)]
        rw [inv_div]; exact hge
      have hinv2 : (1 + |x.1| + |x.2|)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by linarith [abs_nonneg x.1, abs_nonneg x.2])
      have hsq : ((1 + |x.1| + |x.2|)⁻¹) ^ 2 ≤ 2 / d := by
        have h0 : 0 ≤ (1 + |x.1| + |x.2|)⁻¹ := by positivity
        nlinarith
      calc ‖κ.lamP i x‖ ≤ |Cl| * ((1 + |x.1| + |x.2|)⁻¹) ^ 2 := hlam_le i x
        _ ≤ |Cl| * (2 / d) := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
        _ = 2 * |Cl| / d := by ring
        _ ≤ Bc / d := div_le_div_of_nonneg_right (by rw [hBc]; linarith) hd0.le
  -- a cell containing the support of `Φ`
  obtain ⟨R, hR⟩ := hΦs.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  set c : ℝ := d + 2 * |R| + 2 with hc
  have hdc : d ≤ c := by rw [hc]; linarith [abs_nonneg R]
  have hc1 : 1 ≤ c := hd1.trans hdc
  have hΦ0 : ∀ x, x ∉ B0579.cell c → Φ x = 0 := by
    intro x hx
    have hx1 := abs_fst_ge_of_not_mem_cell (by linarith) hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have h1 := hR hxt
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |x.1| ≤ ‖x‖ := by
      have := norm_fst_le x; rwa [Real.norm_eq_abs] at this
    have h3 : |R| + 1 ≤ c / 2 := by rw [hc]; linarith [abs_nonneg R, hd0]
    linarith [le_abs_self R]
  -- the field in the cylinder spaces
  obtain ⟨hΦm, hΦn⟩ := memLp_plane_of_rep W hW
  have hΦcell : MemLp Φ 2 (B0579.cellMeasure c m) := by
    rw [IIb.cellMeasure_eq_restrict_planeMeasure]; exact hΦm.restrict _
  have hxΦ : xNorm c m Φ ≤ ENNReal.ofReal ‖W‖ := by
    unfold xNorm
    rw [← hΦn, IIb.cellMeasure_eq_restrict_planeMeasure]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hgc : Continuous (perLam κ d i) := FrameCont.perLam_continuous κ hd0 i
  have hgm : AEStronglyMeasurable g (B0579.cellMeasure c (-m)) := by
    refine (((hgc.measurable.indicator (B0579.measurableSet_cell d)).sub
      (κ.lamP_cont i).measurable).aestronglyMeasurable)
  have hgx : xNorm c (-m) g ≤ ENNReal.ofReal (Bc / d * N) :=
    hxneg c (Bc / d) g (by positivity) (fun x _ => hgb x)
  have hgL : MemLp g 2 (B0579.cellMeasure c (-m)) :=
    ⟨hgm, lt_of_le_of_lt hgx ENNReal.ofReal_lt_top⟩
  obtain ⟨hgΦi, hgΦb⟩ := ComplCouplingSub.xNorm_pairing_bound hgL hΦcell
  -- rewrite both pairings on the cell `c`
  have hlamΦ : Integrable (fun x => κ.lamP i x * Φ x) :=
    ((κ.lamP_cont i).mul hΦc).integrable_of_hasCompactSupport hΦs.mul_left
  have h1 : (∫ x in B0579.cell d, perLam κ d i x * Φ x) =
      ∫ x in B0579.cell c, (B0579.cell d).indicator (perLam κ d i) x * Φ x := by
    have hind : (fun x => (B0579.cell d).indicator (perLam κ d i) x * Φ x) =
        (B0579.cell d).indicator (fun x => perLam κ d i x * Φ x) := by
      funext x
      by_cases hx : x ∈ B0579.cell d
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hind, setIntegral_indicator (B0579.measurableSet_cell d),
      Set.inter_eq_right.2 (cell_mono hdc)]
  have h2 : (∫ x, κ.lamP i x * Φ x) = ∫ x in B0579.cell c, κ.lamP i x * Φ x := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [hΦ0 x hx, mul_zero]
  have h3 : (∫ x in B0579.cell c, (B0579.cell d).indicator (perLam κ d i) x * Φ x) -
      ∫ x in B0579.cell c, κ.lamP i x * Φ x = ∫ x in B0579.cell c, g x * Φ x := by
    have hI2 : IntegrableOn (fun x => κ.lamP i x * Φ x) (B0579.cell c) := hlamΦ.integrableOn
    have hI1 : IntegrableOn (fun x => (B0579.cell d).indicator (perLam κ d i) x * Φ x)
        (B0579.cell c) := by
      refine (hgΦi.add hI2).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
      show g x * Φ x + κ.lamP i x * Φ x = _
      simp only [hg]; ring
    rw [← integral_sub hI1 hI2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hg]; ring
  rw [h1, h2, h3]
  have hfin : ENNReal.ofReal ‖∫ x in B0579.cell c, g x * Φ x‖ ≤
      ENNReal.ofReal (Bc * N / d * ‖W‖) := by
    refine hgΦb.trans ?_
    calc xNorm c (-m) g * xNorm c m Φ ≤ ENNReal.ofReal (Bc / d * N) * ENNReal.ofReal ‖W‖ :=
          mul_le_mul' hgx hxΦ
      _ = ENNReal.ofReal (Bc * N / d * ‖W‖) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin

/-- `movH0 κ tr r i V = λ'_i Λ_i(V) + ∫_cell movLamDualSub(λ') V` for `V ∈ X_{m,d}`. -/
theorem movH0_eq_add (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (lam : ℂ) {m : ℝ}
    (hm : 8 < m) (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (i : Fin 2)
    {V : ℝ × ℝ → ℂ} (hV : MemLp V 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m))
    (hSub : MemLp (movLamDualSub κ lam tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    movH0 κ tr r i V =
      seedModeEigen lam i *
          (∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i x * V x) +
        ∫ x in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
          movLamDualSub κ lam tr r i x * V x := by
  rw [ComplCouplingSub.movH0_eq_integral_movLamDual]
  have hI1 := ComplCouplingSub.integrableOn_perLam_mul κ hm hd i hV
  have hI2 := (ComplCouplingSub.xNorm_pairing_bound hSub hV).1
  have hpt : (fun y => movLamDual κ tr r i y * V y) = fun y =>
      seedModeEigen lam i * (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y * V y) +
        movLamDualSub κ lam tr r i y * V y := by
    funext y
    unfold movLamDualSub
    ring
  change ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
    movLamDual κ tr r i y * V y = _
  rw [hpt, integral_add (hI1.const_mul _) hI2, integral_const_mul]

/-- **Algebraic decomposition** of the finite-rank part against the planar limit. -/
theorem frp_decomp (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (Φ : ℝ × ℝ → ℂ)
    (ℓ : Fin 2 → ℂ) (y : ℝ × ℝ) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    let Λ := fun j => movLamPair κ ν r j Φ
    let H := fun i => movH0 κ tr r i Φ
    let lamE := modeEigen P
    let c := fun i => (((P.eigenvalue.re - 1 : ℝ) : ℂ) - lamE i)
    let μ := fun i j => movM0 κ P tr r i j - if i = j then lamE j else 0
    let δa := fun i => -(H i - lamE i * Λ i) +
      (((movBeta0 P ν r - P.eigenvalue.re : ℝ) : ℂ)) * Λ i + c i * (Λ i - ℓ i) +
      ∑ j : Fin 2, μ i j * Λ j
    cellZeroExt d (movFrameRankPert κ P tr r Φ) y -
        ∑ i : Fin 2, c i * ℓ i * κ.e i y =
      ∑ i : Fin 2, δa i * cellZeroExt d (perE κ d i) y +
        ∑ i : Fin 2, c i * ℓ i * (cellZeroExt d (perE κ d i) y - κ.e i y) -
        ∑ j : Fin 2, Λ j * cellZeroExt d
          (fun x => movOscRes κ ν r j x + movEulerRes κ P tr r j x) y := by
  intro d Λ H lamE c μ δa
  unfold cellZeroExt
  by_cases hy : y ∈ B0579.cell d
  · simp only [Set.indicator_of_mem hy]
    simp only [movFrameRankPert, movK0, Fin.sum_univ_two, δa, μ, c, Λ, H, lamE, d]
    simp only [Fin.isValue, if_true, show ((0 : Fin 2) = 1) = False by decide,
      show ((1 : Fin 2) = 0) = False by decide, if_false]
    push_cast
    ring
  · simp only [Set.indicator_of_notMem hy]
    simp only [Fin.sum_univ_two, mul_zero, zero_sub, add_zero, zero_add]
    ring

end L4

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
