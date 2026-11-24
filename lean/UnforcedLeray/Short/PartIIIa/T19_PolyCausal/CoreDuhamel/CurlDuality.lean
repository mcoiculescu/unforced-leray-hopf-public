import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Part III-a, task `PartIII-a:T19/2/1`: spatial curl duality in `Z^{-1}_{9,c}`

Source of record: `the November 2 reference manuscript` (SP), lines 3456-3480
(Step P2-duality: spatial curl duality in `Z^{-1}_{9,c}`).

Proves:
* `advStretch_pointwise_bound`: for any `C¹` vector field `v` with
  `⟨x⟩^9 (‖v(x)‖ + ‖Dv(x)‖) ≤ A_m` on `B0579.cell c`,
  `⟨x⟩^9 vnorm2 (advStretch v u G x) ≤ 4 * A_m * (vnorm2 (u x) + tnorm2 (G x))`.
* `advStretch_weighted_l2_bound`: the weighted `L²(cell c)` bound (Clause 2 of `CoreCurlDuality`).
* `negNorm_le_of_advStretch_pairing`: the `Z^{-1}_{9,c}` duality bound (Clause 3 of
  `CoreCurlDuality`).
* `coreCurlDuality_with_C_dual`: full `CoreCurlDuality` with `C_dual * A_m` in Clause 1 as well as
  Clauses 2 and 3.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace CurlDualityAux

/-- The partial derivative `B0579.pd j (fun y => v y i) x` of a `C¹` vector field `v` equals
`(fderiv ℝ v x (B0579.dir j)) i`. -/
lemma pd_coord_eq {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v) (i j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (fun y => v y i) x = (fderiv ℝ v x (B0579.dir j)) i := by
  have hdiff : DifferentiableAt ℝ v x := (hv.differentiable (by decide)).differentiableAt
  set L : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hcomp := L.hasFDerivAt.comp x hdiff.hasFDerivAt
  simpa [B0579.pd, Function.comp_def, L] using congrArg (fun D => D (B0579.dir j)) hcomp.fderiv

/-- For a `C¹` vector field `v`, `B0579.pd j (fun y => v y i)` is continuous. -/
lemma continuous_pd_coord {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v) (i j : Fin 2) :
    Continuous (B0579.pd j (fun y => v y i)) := by
  have : B0579.pd j (fun y => v y i) = fun x => (fderiv ℝ v x (B0579.dir j)) i :=
    funext (pd_coord_eq hv i j)
  rw [this]
  exact (continuous_apply i).comp
    (((ContinuousLinearMap.apply ℝ (Fin 2 → ℝ) (B0579.dir j)).continuous).comp
      (hv.continuous_fderiv (by decide)))

/-- `‖B0579.dir j‖ ≤ 1` in `ℝ × ℝ`. -/
lemma norm_dir_le_one (j : Fin 2) : ‖B0579.dir j‖ ≤ 1 := by
  fin_cases j <;> simp [B0579.dir, Prod.norm_def]

/-- `|B0579.pd j (fun y => v y i) x| ≤ ‖fderiv ℝ v x‖` for `C¹` vector field `v`. -/
lemma abs_pd_coord_le {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v) (i j : Fin 2) (x : ℝ × ℝ) :
    |B0579.pd j (fun y => v y i) x| ≤ ‖fderiv ℝ v x‖ := by
  rw [pd_coord_eq hv i j x, ← Real.norm_eq_abs]
  calc ‖(fderiv ℝ v x (B0579.dir j)) i‖
      ≤ ‖fderiv ℝ v x (B0579.dir j)‖ := norm_le_pi_norm (fderiv ℝ v x (B0579.dir j)) i
    _ ≤ ‖fderiv ℝ v x‖ * ‖B0579.dir j‖ := ContinuousLinearMap.le_opNorm (fderiv ℝ v x) (B0579.dir j)
    _ ≤ ‖fderiv ℝ v x‖ * 1 := mul_le_mul_of_nonneg_left (norm_dir_le_one j) (norm_nonneg _)
    _ = ‖fderiv ℝ v x‖ := mul_one _

/-- `‖u j‖ ≤ vnorm2 u` for `j : Fin 2`. -/
lemma norm_le_vnorm2 (u : Fin 2 → ℂ) (j : Fin 2) : ‖u j‖ ≤ vnorm2 u := by
  have hsq : ‖u j‖ ^ 2 ≤ ∑ i : Fin 2, ‖u i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  calc ‖u j‖ = Real.sqrt (‖u j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ vnorm2 u := Real.sqrt_le_sqrt hsq

/-- `‖G i j‖ ≤ tnorm2 G` for `i, j : Fin 2`. -/
lemma norm_le_tnorm2 (G : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) : ‖G i j‖ ≤ tnorm2 G := by
  have h1 : ‖G i j‖ ^ 2 ≤ ∑ k : Fin 2, ‖G i k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖G i k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ k : Fin 2, ‖G i k‖ ^ 2 ≤ ∑ l : Fin 2, ∑ k : Fin 2, ‖G l k‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ∑ k : Fin 2, ‖G l k‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖G i j‖ = Real.sqrt (‖G i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ tnorm2 G := Real.sqrt_le_sqrt (h1.trans h2)

/-- Pointwise bound on `vnorm2 (advStretch v u G x)`:
`vnorm2 (advStretch v u G x) ≤ 4 * (‖v x‖ + ‖fderiv ℝ v x‖) * (vnorm2 (u x) + tnorm2 (G x))`. -/
lemma vnorm2_advStretch_le {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ) (x : ℝ × ℝ) :
    vnorm2 (advStretch v u G x) ≤
      4 * (‖v x‖ + ‖fderiv ℝ v x‖) * (vnorm2 (u x) + tnorm2 (G x)) := by
  set M : ℝ := 2 * (‖v x‖ + ‖fderiv ℝ v x‖) * (vnorm2 (u x) + tnorm2 (G x))
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
      (add_nonneg (vnorm2_nonneg _) (tnorm2_nonneg _))
  have hcomp : ∀ i : Fin 2, ‖advStretch v u G x i‖ ≤ M := by
    intro i
    unfold advStretch
    rw [Fin.sum_univ_two]
    have hv0 : |v x 0| ≤ ‖v x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (v x) 0
    have hv1 : |v x 1| ≤ ‖v x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (v x) 1
    have hpd0 := abs_pd_coord_le hv i 0 x
    have hpd1 := abs_pd_coord_le hv i 1 x
    have hu0 := norm_le_vnorm2 (u x) 0
    have hu1 := norm_le_vnorm2 (u x) 1
    have hG0 := norm_le_tnorm2 (G x) i 0
    have hG1 := norm_le_tnorm2 (G x) i 1
    have htri : ‖((v x 0 : ℂ) * G x i 0 + u x 0 * (B0579.pd 0 (fun y => v y i) x : ℂ)) +
          ((v x 1 : ℂ) * G x i 1 + u x 1 * (B0579.pd 1 (fun y => v y i) x : ℂ))‖ ≤
        |v x 0| * ‖G x i 0‖ + ‖u x 0‖ * |B0579.pd 0 (fun y => v y i) x| +
          (|v x 1| * ‖G x i 1‖ + ‖u x 1‖ * |B0579.pd 1 (fun y => v y i) x|) := by
      calc ‖((v x 0 : ℂ) * G x i 0 + u x 0 * (B0579.pd 0 (fun y => v y i) x : ℂ)) +
            ((v x 1 : ℂ) * G x i 1 + u x 1 * (B0579.pd 1 (fun y => v y i) x : ℂ))‖
          ≤ ‖(v x 0 : ℂ) * G x i 0 + u x 0 * (B0579.pd 0 (fun y => v y i) x : ℂ)‖ +
              ‖(v x 1 : ℂ) * G x i 1 + u x 1 * (B0579.pd 1 (fun y => v y i) x : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ (‖(v x 0 : ℂ) * G x i 0‖ + ‖u x 0 * (B0579.pd 0 (fun y => v y i) x : ℂ)‖) +
              (‖(v x 1 : ℂ) * G x i 1‖ + ‖u x 1 * (B0579.pd 1 (fun y => v y i) x : ℂ)‖) :=
            add_le_add (norm_add_le _ _) (norm_add_le _ _)
        _ = |v x 0| * ‖G x i 0‖ + ‖u x 0‖ * |B0579.pd 0 (fun y => v y i) x| +
              (|v x 1| * ‖G x i 1‖ + ‖u x 1‖ * |B0579.pd 1 (fun y => v y i) x|) := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine htri.trans ?_
    dsimp [M]
    nlinarith [norm_nonneg (v x), norm_nonneg (fderiv ℝ v x),
      vnorm2_nonneg (u x), tnorm2_nonneg (G x),
      norm_nonneg (u x 0), norm_nonneg (u x 1),
      norm_nonneg (G x i 0), norm_nonneg (G x i 1)]
  have hsq : ∑ i : Fin 2, ‖advStretch v u G x i‖ ^ 2 ≤ (2 * M) ^ 2 := by
    rw [Fin.sum_univ_two]
    have h0 := pow_le_pow_left₀ (norm_nonneg _) (hcomp 0) 2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hcomp 1) 2
    nlinarith [sq_nonneg M]
  calc vnorm2 (advStretch v u G x)
      ≤ Real.sqrt ((2 * M) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * M := Real.sqrt_sq (by positivity)
    _ = 4 * (‖v x‖ + ‖fderiv ℝ v x‖) * (vnorm2 (u x) + tnorm2 (G x)) := by dsimp [M]; ring

/-- Measurability of `advStretch v u G · i` for `C¹` `v` and measurable `(u, G)`. -/
lemma measurable_advStretch {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    {u : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun x => u x i) (hG : ∀ i j, Measurable fun x => G x i j) (i : Fin 2) :
    Measurable fun x => advStretch v u G x i := by
  unfold advStretch
  refine Finset.measurable_sum Finset.univ fun j _ => ?_
  have hvj : Measurable fun x => (v x j : ℂ) :=
    Complex.continuous_ofReal.measurable.comp ((continuous_apply j).comp hv.continuous).measurable
  have hpdj : Measurable fun x => (B0579.pd j (fun y => v y i) x : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (continuous_pd_coord hv i j).measurable
  exact (hvj.mul (hG i j)).add ((hu j).mul hpdj)

/-- Subadditivity `(a + b) ^ (1 / 2 : ℝ) ≤ a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)` in `ℝ≥0∞`. -/
lemma rpow_half_add_le (a b : ℝ≥0∞) :
    (a + b) ^ (1 / 2 : ℝ) ≤ a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ) := by
  apply le_of_sq_le_sq
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  rw [hsq (a + b)]
  calc a + b ≤ (a ^ (1 / 2 : ℝ)) ^ 2 + (b ^ (1 / 2 : ℝ)) ^ 2 +
        2 * a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) := by
        rw [hsq a, hsq b]
        exact le_self_add
    _ = (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) ^ 2 := by ring

/-- If `HasWeakCellDerivC c j φ g` holds, then `g` is a.e. strongly measurable on `B0579.cell c`. -/
lemma aestronglyMeasurable_of_hasWeakCellDerivC {c : ℝ} {j : Fin 2} {φ g : ℝ × ℝ → ℂ}
    (hg : HasWeakCellDerivC c j φ g) :
    AEStronglyMeasurable g (volume.restrict (B0579.cell c)) := by
  let b : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let ψ : ℕ → B0579.Plane → ℝ := fun n x => b n x.2
  have hψ : ∀ n, B0579.IsCylTest c (ψ n) := fun n =>
    ⟨(b n).contDiff.comp contDiff_snd, fun _ => rfl, ⟨(n : ℝ) + 2, fun x hx =>
      (b n).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx.le)⟩⟩
  have hm : ∀ n, AEStronglyMeasurable (fun x => g x * (ψ n x : ℂ))
      (volume.restrict (B0579.cell c)) :=
    fun n => ((hg.1 (ψ n) (hψ n)).2).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hm (Eventually.of_forall fun x => ?_)
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|x.2|⌉₊) fun n hn => ?_
  have hle : |x.2| ≤ (n : ℝ) + 1 := by
    have : (⌈|x.2|⌉₊ : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    linarith [Nat.le_ceil |x.2|]
  have hone : ψ n x = 1 := (b n).one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hle)
  simp [hone]

/-- `xNorm c (-9) h ^ 2 = ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖h x‖ ^ 2)`. -/
lemma xNorm_neg_nine_sq_eq (c : ℝ) (h : ℝ × ℝ → ℂ) :
    xNorm c (-9) h ^ 2 =
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖h x‖ ^ 2) := by
  unfold xNorm
  have hnorm : eLpNorm h 2 (B0579.cellMeasure c (-9)) =
      eLpNorm (fun x => ‖h x‖) 2 (B0579.cellMeasure c (-9)) :=
    (eLpNorm_congr_norm_ae (Eventually.of_forall fun x => norm_norm (h x))).symm
  rw [hnorm, eLpNorm_two_sq_eq_lintegral_nonneg (B0579.cellMeasure c (-9))
    (fun x => ‖h x‖) (fun _ => norm_nonneg _), B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density (-9)).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, B0579.coe_density,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _)]

end CurlDualityAux

open CurlDualityAux

/-- Pointwise bound on `⟨x⟩^9 vnorm2 (advStretch v u G x)` with constant `C_dual = 8` (Clause 1 of
`CoreCurlDuality` with `C_dual * A_m`). -/
theorem advStretch_pointwise_bound {c A_m : ℝ} (_hc : 0 < c) (_hAm : 0 ≤ A_m)
    {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    (hv_bd : ∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m)
    (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ) :
    ∀ x ∈ B0579.cell c,
      B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x) ≤
        4 * A_m * (vnorm2 (u x) + tnorm2 (G x)) := by
  intro x hx
  have hbr : 0 ≤ B0579.bracket x ^ (9 : ℝ) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hpt := vnorm2_advStretch_le hv u G x
  have hbd := hv_bd x hx
  calc B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x)
      ≤ B0579.bracket x ^ (9 : ℝ) *
          (4 * (‖v x‖ + ‖fderiv ℝ v x‖) * (vnorm2 (u x) + tnorm2 (G x))) :=
        mul_le_mul_of_nonneg_left hpt hbr
    _ = 4 * (B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖)) *
          (vnorm2 (u x) + tnorm2 (G x)) := by ring
    _ ≤ 4 * A_m * (vnorm2 (u x) + tnorm2 (G x)) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (add_nonneg (vnorm2_nonneg _) (tnorm2_nonneg _))

/-- Weighted `L²(cell c)` bound on `advStretch v u G` with `C_dual = 8` (Clause 2 of
`CoreCurlDuality`). -/
theorem advStretch_weighted_l2_bound {c A_m : ℝ} (hc : 0 < c) (hAm : 0 ≤ A_m)
    {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    (hv_bd : ∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m)
    {u : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun x => u x i) (_hG : ∀ i j, Measurable fun x => G x i j) :
    (∫⁻ x in B0579.cell c,
        ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
      (1 / 2 : ℝ) ≤
      ENNReal.ofReal (8 * A_m) *
        ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) := by
  have hpt_sq : ∀ x ∈ B0579.cell c,
      ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2) ≤
        ENNReal.ofReal ((8 * A_m) ^ 2) *
          (ENNReal.ofReal (vnorm2 (u x) ^ 2) + ENNReal.ofReal (tnorm2 (G x) ^ 2)) := by
    intro x hx
    have hpt := advStretch_pointwise_bound hc hAm hv hv_bd u G x hx
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr18 : B0579.bracket x ^ (18 : ℝ) = (B0579.bracket x ^ (9 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (B0579.bracket x ^ (9 : ℝ)) 2, ← Real.rpow_mul hbr_pos.le]
      norm_num
    have hnonneg : 0 ≤ B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x) :=
      mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)
    have hsq_le : B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2 ≤
        (8 * A_m) ^ 2 * (vnorm2 (u x) ^ 2 + tnorm2 (G x) ^ 2) := by
      calc B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2
          = (B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x)) ^ 2 := by
            rw [hbr18, mul_pow]
        _ ≤ (4 * A_m * (vnorm2 (u x) + tnorm2 (G x))) ^ 2 :=
            pow_le_pow_left₀ hnonneg hpt 2
        _ ≤ (8 * A_m) ^ 2 * (vnorm2 (u x) ^ 2 + tnorm2 (G x) ^ 2) := by
            nlinarith [sq_nonneg (vnorm2 (u x) - tnorm2 (G x)),
              sq_nonneg (vnorm2 (u x)), sq_nonneg (tnorm2 (G x)), sq_nonneg A_m]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hsq_le
  have hint_le : ∫⁻ x in B0579.cell c,
      ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2) ≤
      ENNReal.ofReal ((8 * A_m) ^ 2) *
        ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) +
          ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) := by
    calc ∫⁻ x in B0579.cell c,
            ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)
        ≤ ∫⁻ x in B0579.cell c, ENNReal.ofReal ((8 * A_m) ^ 2) *
            (ENNReal.ofReal (vnorm2 (u x) ^ 2) + ENNReal.ofReal (tnorm2 (G x) ^ 2)) :=
          setLIntegral_mono' (B0579.measurableSet_cell c) hpt_sq
      _ = ENNReal.ofReal ((8 * A_m) ^ 2) *
            ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) +
              ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left (((causalLin_measurable_vnorm2 hu).pow_const 2).ennreal_ofReal)]
  have hconst_sqrt : ENNReal.ofReal ((8 * A_m) ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal (8 * A_m) := by
    rw [ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  calc (∫⁻ x in B0579.cell c,
          ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
        (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((8 * A_m) ^ 2) *
          ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) +
            ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hint_le (by norm_num)
    _ = ENNReal.ofReal (8 * A_m) *
          ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) +
            ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hconst_sqrt]
    _ ≤ ENNReal.ofReal (8 * A_m) *
          ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
            (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (rpow_half_add_le _ _) bot_le

/-- `Z^{-1}_{9,c}` duality bound on `negNorm c 9 f` with `C_dual = 8` (Clause 3 of
`CoreCurlDuality`). -/
theorem negNorm_le_of_advStretch_pairing {c A_m : ℝ} (hc : 0 < c) (hAm : 0 ≤ A_m)
    {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    (hv_bd : ∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m)
    {u : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun x => u x i) (hG : ∀ i j, Measurable fun x => G x i j)
    (f : ℝ × ℝ → ℂ)
    (hpair : ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
      ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖ ≤
        ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x))) :
    negNorm c 9 f ≤
      ENNReal.ofReal (8 * A_m) *
        ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) := by
  unfold negNorm
  refine iSup₂_le fun φ g => iSup₂_le fun hg hh1 => ?_
  set F₁ : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x))
  set F₂ : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (B0579.bracket x ^ (-9 : ℝ) * vnorm2 (fun j => g j x))
  have hF₁ : AEMeasurable F₁ (volume.restrict (B0579.cell c)) := by
    have hm_br : Measurable fun x : ℝ × ℝ => B0579.bracket x ^ (9 : ℝ) :=
      ((B0579.continuous_jb.sqrt).rpow_const (fun _ => Or.inr (by norm_num))).measurable
    have hm_adv : Measurable fun x : ℝ × ℝ => vnorm2 (advStretch v u G x) :=
      causalLin_measurable_vnorm2 (measurable_advStretch hv hu hG)
    exact (hm_br.mul hm_adv).ennreal_ofReal.aemeasurable
  have hgm : ∀ j : Fin 2, AEStronglyMeasurable (g j) (volume.restrict (B0579.cell c)) :=
    fun j => aestronglyMeasurable_of_hasWeakCellDerivC (hg j)
  have hF₂ : AEMeasurable F₂ (volume.restrict (B0579.cell c)) := by
    have hm_br : AEMeasurable (fun x : ℝ × ℝ => B0579.bracket x ^ (-9 : ℝ))
        (volume.restrict (B0579.cell c)) := by
      have heq : (fun x : ℝ × ℝ => B0579.bracket x ^ (-9 : ℝ)) =
          fun x => B0579.jb x ^ (-9 / 2 : ℝ) := funext (B0579.bracket_rpow (-9))
      rw [heq]
      exact (B0579.continuous_jb_rpow (-9 / 2)).measurable.aemeasurable
    have hm_g : AEMeasurable (fun x : ℝ × ℝ => vnorm2 (fun j => g j x))
        (volume.restrict (B0579.cell c)) := by
      unfold vnorm2
      refine Real.continuous_sqrt.measurable.comp_aemeasurable ?_
      rw [show (fun x : ℝ × ℝ => ∑ i : Fin 2, ‖g i x‖ ^ 2) =
          fun x => ‖g 0 x‖ ^ 2 + ‖g 1 x‖ ^ 2 from funext fun _ => Fin.sum_univ_two _]
      exact (((hgm 0).norm.aemeasurable.pow_const 2).add ((hgm 1).norm.aemeasurable.pow_const 2))
    exact (hm_br.mul hm_g).ennreal_ofReal
  have hprod_eq : ∀ x,
      ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) = F₁ x * F₂ x := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr_mul : B0579.bracket x ^ (9 : ℝ) * B0579.bracket x ^ (-9 : ℝ) = 1 := by
      rw [← Real.rpow_add hbr_pos, add_neg_cancel, Real.rpow_zero]
    dsimp [F₁, F₂]
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _))]
    congr 1
    calc vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)
        = (B0579.bracket x ^ (9 : ℝ) * B0579.bracket x ^ (-9 : ℝ)) *
            (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) := by
          rw [hbr_mul, one_mul]
      _ = B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x) *
            (B0579.bracket x ^ (-9 : ℝ) * vnorm2 (fun j => g j x)) := by ring
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (B0579.cell c))
    Real.HolderConjugate.two_two hF₁ hF₂
  have hF₁_sq : ∀ x, F₁ x ^ (2 : ℝ) =
      ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2) := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr18 : B0579.bracket x ^ (18 : ℝ) = (B0579.bracket x ^ (9 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (B0579.bracket x ^ (9 : ℝ)) 2, ← Real.rpow_mul hbr_pos.le]
      norm_num
    dsimp [F₁]
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)),
      mul_pow, hbr18]
  have hF₂_sq : ∀ x, F₂ x ^ (2 : ℝ) =
      ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 0 x‖ ^ 2) +
        ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 1 x‖ ^ 2) := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr_neg18 : (B0579.bracket x ^ (-9 : ℝ)) ^ 2 = B0579.jb x ^ (-9 : ℝ) := by
      rw [B0579.bracket_rpow (-9), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (B0579.jb_pos x).le]
      congr 1
      norm_num
    have hv_sq : vnorm2 (fun j => g j x) ^ 2 = ‖g 0 x‖ ^ 2 + ‖g 1 x‖ ^ 2 := by
      unfold vnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_two]
    dsimp [F₂]
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)),
      mul_pow, hbr_neg18, hv_sq, mul_add,
      ENNReal.ofReal_add
        (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
        (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))]
  have hF₂_int : (∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
    have hm0 : AEMeasurable
        (fun x : ℝ × ℝ => ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 0 x‖ ^ 2))
        (volume.restrict (B0579.cell c)) :=
      ((B0579.continuous_jb_rpow (-9)).measurable.aemeasurable.mul
        ((hgm 0).norm.aemeasurable.pow_const 2)).ennreal_ofReal
    have hint_eq : ∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ) =
        ∑ j : Fin 2, xNorm c (-9) (g j) ^ 2 := by
      simp_rw [hF₂_sq]
      rw [lintegral_add_left' hm0, ← xNorm_neg_nine_sq_eq c (g 0),
        ← xNorm_neg_nine_sq_eq c (g 1), Fin.sum_univ_two]
    rw [hint_eq]
    calc (∑ j : Fin 2, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ)
        ≤ (xNorm c (-9) φ ^ 2 + ∑ j : Fin 2, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow le_add_self (by norm_num)
      _ = h1Norm c 9 φ g := rfl
      _ ≤ 1 := hh1
  calc ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖
      ≤ ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) :=
        hpair φ g hg hh1
    _ = ∫⁻ x in B0579.cell c, (F₁ * F₂) x := lintegral_congr hprod_eq
    _ ≤ (∫⁻ x in B0579.cell c, F₁ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hCS
    _ ≤ (∫⁻ x in B0579.cell c,
          ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
            (1 / 2 : ℝ) * 1 := by
        simp_rw [hF₁_sq]
        exact mul_le_mul_of_nonneg_left hF₂_int bot_le
    _ = (∫⁻ x in B0579.cell c,
          ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
            (1 / 2 : ℝ) := mul_one _
    _ ≤ ENNReal.ofReal (8 * A_m) *
          ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
            (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) :=
        advStretch_weighted_l2_bound hc hAm hv hv_bd hu hG

/-- Full `CoreCurlDuality` with `C_dual * A_m` in Clause 1 as well as Clauses 2 and 3. -/
theorem coreCurlDuality_with_C_dual :
    ∃ C_dual : ℝ, 0 ≤ C_dual ∧
      ∀ (c A_m : ℝ), 0 < c → 0 ≤ A_m →
        ∀ (v : ℝ × ℝ → Fin 2 → ℝ), ContDiff ℝ 1 v →
          (∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m) →
          ∀ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
            (∀ i, Measurable fun x => u x i) → (∀ i j, Measurable fun x => G x i j) →
            (∀ x ∈ B0579.cell c,
              B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x) ≤
                C_dual * A_m * (vnorm2 (u x) + tnorm2 (G x))) ∧
            (∫⁻ x in B0579.cell c,
                ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
              (1 / 2 : ℝ) ≤
              ENNReal.ofReal (C_dual * A_m) *
                ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                  (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) ∧
            ∀ (f : ℝ × ℝ → ℂ),
              (∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
                (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
                ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖ ≤
                  ∫⁻ x in B0579.cell c,
                    ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x))) →
              negNorm c 9 f ≤
                ENNReal.ofReal (C_dual * A_m) *
                  ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                    (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) := by
  refine ⟨8, by norm_num, fun c A_m hc hAm v hv hv_bd u G hu hG =>
    ⟨fun x hx => (advStretch_pointwise_bound hc hAm hv hv_bd u G x hx).trans
      (mul_le_mul_of_nonneg_right (by linarith)
        (add_nonneg (vnorm2_nonneg _) (tnorm2_nonneg _))),
      advStretch_weighted_l2_bound hc hAm hv hv_bd hu hG,
      negNorm_le_of_advStretch_pairing hc hAm hv hv_bd hu hG⟩⟩

/-- **Leaf `PartIII-a:T19/2/1` (`CoreCurlDuality`, SP lines 3456-3480)**:
Spatial curl duality in `Z^{-1}_{9,c}` on `B0579.cell c`. -/
theorem coreCurlDuality : UnforcedLeray.Short.IIIa.CoreCurlDuality :=
  coreCurlDuality_with_C_dual

end UnforcedLeray.Short.IIIa
