import UnforcedLeray.Short.PartI.Sub.PartI_T23_2
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive.MeanStreamDiffDuhamelL1
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# `PartI:T23/2/1` (`StreamDuhamel.lean`): 1D heat Duhamel representation of `meanStream`

Source of record: `the November 2 reference manuscript`, lines 397-412, 448-456,
and 528-534, in the proof of Lemma `sct:expansion`.

Proves `trainMeanStreamDuhamel_proof : TrainMeanStreamDuhamel`:
for `ρ > 1/2`, `0 < ν ≤ 1` (so `c = trainPeriod ρ ν ≥ 1`), `IsBUCTrain tr`, `s > 0`, and `η ∈ ℝ`,
`meanStream tr s η = meanDatumDuhamel tr s η + meanSourceDuhamel tr s η`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)

namespace StreamDuhamel

/-! ### 1. Gaussian algebraic bounds and rescaled convolution identity -/

private theorem exp_neg_mul_one_add_le {u : ℝ} (hu : 0 ≤ u) :
    (1 + u) * Real.exp (-u) ≤ 27 * (1 + u)⁻¹ ^ 2 := by
  have h1 : 1 + u / 3 ≤ Real.exp (u / 3) := by linarith [Real.add_one_le_exp (u / 3)]
  have h3 : (1 + u / 3) ^ 3 ≤ Real.exp u := by
    calc (1 + u / 3) ^ 3 ≤ (Real.exp (u / 3)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = Real.exp u := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hpoly : (1 + u) * (1 + u) ^ 2 ≤ 27 * (1 + u / 3) ^ 3 := by
    have : 27 * (1 + u / 3) ^ 3 - (1 + u) * (1 + u) ^ 2 =
        26 + 24 * u + 6 * u ^ 2 := by ring
    nlinarith [sq_nonneg u]
  have hpos : 0 < (1 + u) ^ 2 := by positivity
  rw [inv_pow, le_mul_inv_iff₀ hpos]
  calc (1 + u) * Real.exp (-u) * (1 + u) ^ 2
      = ((1 + u) * (1 + u) ^ 2) * Real.exp (-u) := by ring
    _ ≤ (27 * (1 + u / 3) ^ 3) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ ≤ (27 * Real.exp u) * Real.exp (-u) := by
        gcongr
    _ = 27 * (Real.exp u * Real.exp (-u)) := by ring
    _ = 27 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

private theorem exp_neg_le_inv_one_add_sq {a : ℝ} (ha : 0 < a) (y : ℝ) :
    (1 + y ^ 2 / (4 * a)) * Real.exp (-(y ^ 2) / (4 * a)) ≤
      27 * (1 + (y / Real.sqrt (4 * a)) ^ 2)⁻¹ := by
  have ha4 : 0 < 4 * a := by positivity
  set u : ℝ := y ^ 2 / (4 * a)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu_eq : u = (y / Real.sqrt (4 * a)) ^ 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt ha4.le]
  have h1 := exp_neg_mul_one_add_le hu
  have h2 : (1 + u)⁻¹ ^ 2 ≤ (1 + u)⁻¹ := by
    rw [sq]
    exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  have hneg : -(y ^ 2) / (4 * a) = -u := by dsimp [u]; ring
  rw [hneg, ← hu_eq]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

private theorem abs_le_one_add_sq_div {a : ℝ} (ha : 0 < a) (y : ℝ) :
    |y| ≤ (1 + a) * (1 + y ^ 2 / (4 * a)) := by
  have h1 : 0 ≤ (|y| - 2 * a) ^ 2 := sq_nonneg _
  have h2 : |y| * (4 * a) ≤ 4 * a ^ 2 + y ^ 2 := by
    have : (|y| - 2 * a) ^ 2 = y ^ 2 - |y| * (4 * a) + 4 * a ^ 2 := by
      rw [sub_sq, sq_abs]; ring
    linarith
  have ha4 : 0 < 4 * a := by positivity
  rw [← le_div_iff₀ ha4] at h2
  have h3 : (4 * a ^ 2 + y ^ 2) / (4 * a) = a + y ^ 2 / (4 * a) := by
    field_simp [ha.ne']
  rw [h3] at h2
  have hy2 : 0 ≤ y ^ 2 / (4 * a) := by positivity
  nlinarith

private theorem quad_le_one_add_sq_div {a A B C : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (y : ℝ) :
    A + B * |y| + C * y ^ 2 ≤
      (A + B * (1 + a) + C * (4 * a)) * (1 + y ^ 2 / (4 * a)) := by
  have hy2 : 0 ≤ y ^ 2 / (4 * a) := by positivity
  have h1 : 1 ≤ 1 + y ^ 2 / (4 * a) := by linarith
  have h2 := abs_le_one_add_sq_div ha y
  have h3 : y ^ 2 ≤ (4 * a) * (1 + y ^ 2 / (4 * a)) := by
    have : (4 * a) * (1 + y ^ 2 / (4 * a)) = 4 * a + y ^ 2 := by field_simp [ha.ne']
    linarith
  nlinarith

private theorem continuous_heatKernel1 {a : ℝ} (_ha : 0 < a) :
    Continuous (heatKernel1 a) := by
  unfold heatKernel1
  exact continuous_const.mul
    (Real.continuous_exp.comp (((continuous_id.pow 2).neg).div_const (4 * a)))

private theorem integrable_heatKernel1 {a : ℝ} (ha : 0 < a) :
    Integrable (heatKernel1 a) volume := by
  have hsq : 0 < Real.sqrt (4 * a) := Real.sqrt_pos.2 (by positivity)
  set env : ℝ → ℝ := fun z => 27 * (1 + (z / Real.sqrt (4 * a)) ^ 2)⁻¹
  have henv_int : Integrable env volume :=
    (integrable_inv_one_add_sq.comp_div hsq.ne').const_mul 27
  set pre : ℝ := (Real.sqrt (4 * Real.pi * a))⁻¹
  have hpre_pos : 0 < pre := by dsimp [pre]; positivity
  refine (henv_int.const_mul pre).mono' (continuous_heatKernel1 ha).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  have hpos : 0 ≤ heatKernel1 a z := by unfold heatKernel1; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  have hbd := exp_neg_le_inv_one_add_sq ha z
  have hz2_nn : 0 ≤ z ^ 2 / (4 * a) := by positivity
  have hexp_le : Real.exp (-(z ^ 2) / (4 * a)) ≤ env z := by
    calc Real.exp (-(z ^ 2) / (4 * a))
        ≤ (1 + z ^ 2 / (4 * a)) * Real.exp (-(z ^ 2) / (4 * a)) :=
          le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
      _ ≤ env z := hbd
  unfold heatKernel1
  exact mul_le_mul_of_nonneg_left hexp_le hpre_pos.le

/-- Change of variables `ξ = η - √a * z` in `∫ ξ, G_a(η - ξ) * F(ξ) dξ`:
for `a > 0`, `∫ ξ : ℝ, heatKernel1 a (η - ξ) * F ξ = ∫ z : ℝ, heatKernel1 1 z * F (η - √a * z)`. -/
private theorem integral_heatKernel1_mul_eq_std {a : ℝ} (ha : 0 < a) (η : ℝ) (F : ℝ → ℝ) :
    (∫ ξ : ℝ, heatKernel1 a (η - ξ) * F ξ) =
      ∫ z : ℝ, heatKernel1 1 z * F (η - Real.sqrt a * z) := by
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsub := integral_sub_left_eq_self (fun u : ℝ => heatKernel1 a u * F (η - u)) volume η
  have hsub' : (∫ ξ : ℝ, heatKernel1 a (η - ξ) * F ξ) =
      ∫ u : ℝ, heatKernel1 a u * F (η - u) := by
    refine (integral_congr_ae (Eventually.of_forall fun ξ => ?_)).trans hsub
    change heatKernel1 a (η - ξ) * F ξ = heatKernel1 a (η - ξ) * F (η - (η - ξ))
    rw [show η - (η - ξ) = ξ by ring]
  rw [hsub']
  have hmul := Measure.integral_comp_mul_left
    (fun u : ℝ => heatKernel1 a u * F (η - u)) (Real.sqrt a)
  rw [abs_inv, abs_of_pos hsq, smul_eq_mul] at hmul
  have hmul' : (∫ u : ℝ, heatKernel1 a u * F (η - u)) =
      Real.sqrt a * ∫ z : ℝ, heatKernel1 a (Real.sqrt a * z) * F (η - Real.sqrt a * z) := by
    rw [hmul, mul_inv_cancel_left₀ hsq.ne']
  rw [hmul', ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have hscale := PartI_T23.heatKernel1_nu_scale ha 1 (Real.sqrt a * z)
  rw [mul_one, mul_one, inv_mul_cancel_left₀ hsq.ne'] at hscale
  change Real.sqrt a * (heatKernel1 a (Real.sqrt a * z) * F (η - Real.sqrt a * z)) =
    heatKernel1 1 z * F (η - Real.sqrt a * z)
  rw [hscale, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hsq.ne', one_mul]

private theorem continuousOn_meanStress_Ici {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContinuousOn (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ici 0 ×ˢ univ) := by
  set prod_ext : ℝ → Plane → ℝ := fun r z => tr.v (max r 0) z 0 * tr.v (max r 0) z 1
  have hp_cont : Continuous (fun p : ℝ × Plane => prod_ext p.1 p.2) := by
    have h0 : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
      (PiLp.continuous_apply 2 _ 0).comp_continuousOn tr.isTrain.smooth_v.continuousOn
    have h1 : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 1) (Ici 0 ×ˢ univ) :=
      (PiLp.continuous_apply 2 _ 1).comp_continuousOn tr.isTrain.smooth_v.continuousOn
    have hmap : Continuous (fun p : ℝ × Plane => ((max p.1 0, p.2) : ℝ × Plane)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    exact (h0.mul h1).comp_continuous hmap
      (fun p => ⟨mem_Ici.2 (le_max_right p.1 0), mem_univ _⟩)
  have hg_cont : Continuous (Function.uncurry (fun r t : ℝ => hmean c (prod_ext r) t)) := by
    have hle : -c / 2 ≤ c / 2 := by linarith
    have hfun : Function.uncurry (fun r t : ℝ => hmean c (prod_ext r) t) =
        fun p : ℝ × ℝ => c⁻¹ * ∫ q in (-c / 2)..(c / 2), prod_ext p.1 (q, p.2) := by
      funext p
      simp only [hmean, smul_eq_mul, intervalIntegral.integral_of_le hle]
      rfl
    rw [hfun]
    have hcont_q : Continuous
        (Function.uncurry (fun (p : ℝ × ℝ) (q : ℝ) => prod_ext p.1 (q, p.2))) :=
      hp_cont.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hcont_q (-c / 2) (c / 2))
  refine hg_cont.continuousOn.congr fun x hx => ?_
  have hmax : max x.1 0 = x.1 := max_eq_left hx.1
  change meanStress tr x.1 x.2 = hmean c (prod_ext x.1) x.2
  simp only [meanStress, prod_ext, hmax]

/-! ### 2. Stream difference `D` and backward heat kernel `K` -/

private def D (ν c : ℝ) (tr : B0140.TrainSol ν c) (r ξ : ℝ) : ℝ :=
  meanStream tr r ξ - vortexMeanStream ν c r ξ

private theorem D_zero {ν c : ℝ} (hc1 : 1 ≤ c) (tr : B0140.TrainSol ν c) (ξ : ℝ) :
    D ν c tr 0 ξ = 0 := by
  unfold D
  rw [meanStream_zero_eq_vortexMeanStream hc1 tr ξ, sub_self]

private theorem continuousOn_D {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) :
    ContinuousOn (fun x : ℝ × ℝ => D ν c tr x.1 x.2) (Ici 0 ×ˢ univ) :=
  (continuousOn_meanStream_Ici hν hc tr hb).sub (contDiffOn_vortexMeanStream hν).continuousOn

private theorem contDiffOn_D {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => D ν c tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
  (trainMeanEquations_proof ν c hν hc tr hb).1.sub
    ((contDiffOn_vortexMeanStream hν).mono (prod_mono Ioi_subset_Ici_self Subset.rfl))

private theorem hasDerivAt_vortexMeanStream_eta' {ν c r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (ξ : ℝ) :
    HasDerivAt (vortexMeanStream ν c r) (deriv (vortexMeanStream ν c r) ξ) ξ := by
  have ha : 0 < width ν r := by unfold width; nlinarith
  have h : HasDerivAt (vortexMeanStream ν c r)
      (-(8 * Real.pi * c⁻¹) * (-(ξ / (2 * width ν r)) * heatKernel1 (width ν r) ξ)) ξ := by
    unfold vortexMeanStream
    exact (hasDerivAt_heatKernel1_eta ha ξ).const_mul (-(8 * Real.pi * c⁻¹))
  exact h.congr_deriv h.deriv.symm

private theorem hasDerivAt_D_eta {ν c : ℝ} (hν : 0 < ν) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (ξ : ℝ) :
    HasDerivAt (D ν c tr r) (-meanVel1 tr r ξ - deriv (vortexMeanStream ν c r) ξ) ξ :=
  (bucVel_S_deriv tr hr ξ).sub (hasDerivAt_vortexMeanStream_eta' hν hr ξ)

private theorem deriv_D_eta {ν c : ℝ} (hν : 0 < ν) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (ξ : ℝ) :
    deriv (D ν c tr r) ξ = -meanVel1 tr r ξ - deriv (vortexMeanStream ν c r) ξ :=
  (hasDerivAt_D_eta hν tr hr ξ).deriv

private theorem D_pde {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    HasDerivAt (fun r' => D ν c tr r' ξ)
      (ν * deriv (deriv (D ν c tr r)) ξ + meanStress tr r ξ) r := by
  have hmean := trainMeanEquations_proof ν c hν hc tr hb
  have hS_smooth := hmean.1
  have hV_smooth := (contDiffOn_vortexMeanStream (ν := ν) (c := c) hν).mono
    (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem : ((r, ξ) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ ξ⟩
  have hpath : HasDerivAt (fun r' : ℝ => ((r', ξ) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r ξ)
  have hS_time : HasDerivAt (fun r' => meanStream tr r' ξ)
      (deriv (fun r' => meanStream tr r' ξ) r) r := by
    have hpt : DifferentiableAt ℝ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (r, ξ) :=
      (hS_smooth.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hpt.hasFDerivAt.comp_hasDerivAt r hpath).differentiableAt.hasDerivAt
  have hV_time : HasDerivAt (fun r' => vortexMeanStream ν c r' ξ)
      (deriv (fun r' => vortexMeanStream ν c r' ξ) r) r := by
    have hpt : DifferentiableAt ℝ (fun x : ℝ × ℝ => vortexMeanStream ν c x.1 x.2) (r, ξ) :=
      (hV_smooth.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hpt.hasFDerivAt.comp_hasDerivAt r hpath).differentiableAt.hasDerivAt
  have hS_slice : ContDiff ℝ ∞ (meanStream tr r) := t01_contDiff_slice hS_smooth hr
  have hV_slice : ContDiff ℝ ∞ (vortexMeanStream ν c r) := t01_contDiff_slice hV_smooth hr
  have hd1 : deriv (D ν c tr r) =
      fun e => deriv (meanStream tr r) e - deriv (vortexMeanStream ν c r) e := by
    funext e
    exact deriv_sub (hS_slice.differentiable (by simp) e) (hV_slice.differentiable (by simp) e)
  have hdS : ContDiff ℝ ∞ (deriv (meanStream tr r)) := hS_slice.deriv'
  have hdV : ContDiff ℝ ∞ (deriv (vortexMeanStream ν c r)) := hV_slice.deriv'
  have hd2 : deriv (deriv (D ν c tr r)) ξ =
      deriv (deriv (meanStream tr r)) ξ - deriv (deriv (vortexMeanStream ν c r)) ξ := by
    rw [hd1]
    exact deriv_sub (hdS.differentiable (by simp) ξ) (hdV.differentiable (by simp) ξ)
  have hmean_pde := (hmean.2 r hr ξ).1
  have hvort_pde := vortexMeanStream_heat_eq (c := c) hν hr.le ξ
  refine (hS_time.sub hV_time).congr_deriv ?_
  rw [hd2]
  linarith

/-- Uniform bounds on `D` and `∂_ξ D` on `[0, s] × ℝ`. -/
private theorem D_uniform_bounds {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) :
    ∃ C₀ M₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ M₁ ∧
      ∀ r ∈ Icc (0 : ℝ) s, ∀ ξ : ℝ,
        |deriv (D ν c tr r) ξ| ≤ M₁ ∧ |D ν c tr r ξ| ≤ C₀ + M₁ * |ξ| := by
  obtain ⟨M0, hM0⟩ := hb.sup_bound hs.le
  have hM0_nn : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 ⟨le_rfl, hs.le⟩ 0)
  have hD0_cont : ContinuousOn (fun r : ℝ => D ν c tr r 0) (Icc 0 s) :=
    (continuousOn_D hν hc tr hb).comp (continuousOn_id.prodMk continuousOn_const)
      (fun r (hr : r ∈ Icc 0 s) => ⟨hr.1, mem_univ 0⟩)
  obtain ⟨C₀, hC₀_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hD0_cont
  have hC₀_nn : 0 ≤ max C₀ 0 := le_max_right _ _
  set M₁ : ℝ := M0 + 8 * Real.pi * c⁻¹
  have hM₁_nn : 0 ≤ M₁ := by dsimp [M₁]; positivity
  refine ⟨max C₀ 0, M₁, hC₀_nn, hM₁_nn, ?_⟩
  intro r hr ξ
  have hu : ∀ x : ℝ, |meanVel1 tr r x| ≤ M0 := by
    intro x
    refine bucVel_hmean_abs_le hc _ x M0 fun q => ?_
    have h := PiLp.norm_apply_le (tr.v r (q, x)) 0
    rw [Real.norm_eq_abs] at h
    exact h.trans (hM0 r hr (q, x))
  have hd : ∀ x : ℝ, |deriv (D ν c tr r) x| ≤ M₁ := by
    intro x
    rw [deriv_D_eta hν tr hr.1 x,
      show -meanVel1 tr r x - deriv (vortexMeanStream ν c r) x =
        -(meanVel1 tr r x + deriv (vortexMeanStream ν c r) x) by ring, abs_neg]
    exact (abs_add_le _ _).trans (add_le_add (hu x) (abs_deriv_vortexMeanStream_le hν hc hr.1 x))
  refine ⟨hd ξ, ?_⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := univ)
    (fun x _ => (hasDerivAt_D_eta hν tr hr.1 x).differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hd x)
    convex_univ (mem_univ 0) (mem_univ ξ)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hmvt
  have h0 : |D ν c tr r 0| ≤ max C₀ 0 := by
    have h := hC₀_bd r hr
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  linarith [abs_sub_abs_le_abs_sub (D ν c tr r ξ) (D ν c tr r 0)]

/-! ### 3. Backward heat kernel `K` and its derivatives -/

private def K (ν s η t ξ : ℝ) : ℝ :=
  heatKernel1 (ν * (s - t)) (η - ξ)

private theorem hasDerivAt_K_eta {ν s t : ℝ} (hν : 0 < ν) (ht : t < s) (η ξ : ℝ) :
    HasDerivAt (K ν s η t)
      ((η - ξ) / (2 * (ν * (s - t))) * K ν s η t ξ) ξ := by
  have ha : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 ht)
  unfold K
  have h1 := (hasDerivAt_heatKernel1_eta ha (η - ξ)).comp ξ
    ((hasDerivAt_const ξ η).sub (hasDerivAt_id ξ))
  refine h1.congr_deriv ?_
  ring

private theorem deriv_K_eta {ν s t : ℝ} (hν : 0 < ν) (ht : t < s) (η ξ : ℝ) :
    deriv (K ν s η t) ξ = (η - ξ) / (2 * (ν * (s - t))) * K ν s η t ξ :=
  (hasDerivAt_K_eta hν ht η ξ).deriv

private theorem hasDerivAt_deriv_K_eta {ν s t : ℝ} (hν : 0 < ν) (ht : t < s) (η ξ : ℝ) :
    HasDerivAt (deriv (K ν s η t))
      (K ν s η t ξ * ((η - ξ) ^ 2 / (4 * (ν * (s - t)) ^ 2) - 1 / (2 * (ν * (s - t))))) ξ := by
  have ha : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 ht)
  have hfun : deriv (K ν s η t) = fun e : ℝ => -deriv (heatKernel1 (ν * (s - t))) (η - e) := by
    funext e
    rw [deriv_K_eta hν ht η e, deriv_heatKernel1_eta ha (η - e)]
    unfold K
    ring
  rw [hfun]
  have h1 := ((hasDerivAt_deriv_heatKernel1_eta ha (η - ξ)).comp ξ
    ((hasDerivAt_const ξ η).sub (hasDerivAt_id ξ))).neg
  refine h1.congr_deriv ?_
  unfold K
  ring

private theorem deriv_deriv_K_eta {ν s t : ℝ} (hν : 0 < ν) (ht : t < s) (η ξ : ℝ) :
    deriv (deriv (K ν s η t)) ξ =
      K ν s η t ξ * ((η - ξ) ^ 2 / (4 * (ν * (s - t)) ^ 2) - 1 / (2 * (ν * (s - t)))) :=
  (hasDerivAt_deriv_K_eta hν ht η ξ).deriv

private theorem hasDerivAt_K_time {ν s t : ℝ} (hν : 0 < ν) (ht : t < s) (η ξ : ℝ) :
    HasDerivAt (fun t' => K ν s η t' ξ) (-ν * deriv (deriv (K ν s η t)) ξ) t := by
  have ha : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 ht)
  have hlin : HasDerivAt (fun t' : ℝ => ν * (s - t')) (-ν) t := by
    have h := ((hasDerivAt_const t s).sub (hasDerivAt_id t)).const_mul ν
    refine h.congr_deriv ?_
    ring
  have hcomp := (hasDerivAt_heatKernel1_time ha (η - ξ)).comp t hlin
  refine hcomp.congr_deriv ?_
  rw [deriv_deriv_K_eta hν ht η ξ]
  unfold K
  ring

private theorem contDiffOn_K {ν s : ℝ} (hν : 0 < ν) (η : ℝ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => K ν s η x.1 x.2) (Iio s ×ˢ univ) := by
  have ha_pos : ∀ x ∈ Iio s ×ˢ (univ : Set ℝ), 0 < ν * (s - x.1) :=
    fun x hx => mul_pos hν (sub_pos.2 hx.1)
  have h4pi_pos : ∀ x ∈ Iio s ×ˢ (univ : Set ℝ), 0 < 4 * Real.pi * (ν * (s - x.1)) :=
    fun x hx => mul_pos (by positivity) (ha_pos x hx)
  have ha_smooth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ν * (s - x.1)) (Iio s ×ˢ univ) :=
    contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_fst)
  have h4pi : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => 4 * Real.pi * (ν * (s - x.1))) (Iio s ×ˢ univ) :=
    contDiffOn_const.mul ha_smooth
  have hsqrt : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => Real.sqrt (4 * Real.pi * (ν * (s - x.1)))) (Iio s ×ˢ univ) :=
    fun x hx => (Real.contDiffAt_sqrt (h4pi_pos x hx).ne').comp_contDiffWithinAt x (h4pi x hx)
  have hinv : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => (Real.sqrt (4 * Real.pi * (ν * (s - x.1))))⁻¹) (Iio s ×ˢ univ) :=
    hsqrt.inv fun x hx => (Real.sqrt_pos.2 (h4pi_pos x hx)).ne'
  have hexp_arg : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => -((η - x.2) ^ 2) / (4 * (ν * (s - x.1)))) (Iio s ×ˢ univ) :=
    ((contDiffOn_const.sub contDiffOn_snd).pow 2).neg.div (contDiffOn_const.mul ha_smooth)
      (fun x hx => mul_ne_zero (by norm_num) (ha_pos x hx).ne')
  exact hinv.mul (Real.contDiff_exp.comp_contDiffOn hexp_arg)

/-! ### 4. Differentiation under `∫ ξ in (-R)..R` and Green's identity on `[0, s₁]` -/

private theorem integral_hasDerivAt_interval_Ioo {s : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 s ×ˢ univ)) {t : ℝ} (ht : t ∈ Ioo 0 s) (a b : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ ξ in a..b, f (r, ξ))
      (∫ ξ in a..b, deriv (fun r => f (r, ξ)) t) t := by
  have ht0 : 0 < t := ht.1
  have hts : t < s := ht.2
  have hopen : IsOpen (Ioo (0 : ℝ) s ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hD : ContinuousOn (fun x : ℝ × ℝ => fderiv ℝ f x (1, 0)) (Ioo 0 s ×ˢ univ) :=
    (hf.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply continuousOn_const
  have hK : IsCompact (Icc (t / 2) ((t + s) / 2) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  have hKsub : Icc (t / 2) ((t + s) / 2) ×ˢ uIcc a b ⊆ Ioo 0 s ×ˢ univ := by
    intro x hx
    exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, mem_univ _⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hD.mono hKsub)
  have hnhds : Ioo (t / 2) ((t + s) / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hslice_cont : ∀ r ∈ Ioo (0 : ℝ) s, Continuous (fun ξ : ℝ => f (r, ξ)) := by
    intro r hr
    exact (hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun ξ _ => ⟨hr, mem_univ ξ⟩)) |> continuousOn_univ.1
  have hmeas : ∀ᶠ x in 𝓝 t,
      AEStronglyMeasurable (fun ξ => f (x, ξ)) ((volume : Measure ℝ).restrict (uIoc a b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (hslice_cont x hx).aestronglyMeasurable
  have hFint : IntervalIntegrable (fun ξ => f (t, ξ)) (volume : Measure ℝ) a b :=
    (hslice_cont t ht).intervalIntegrable _ _
  have hcontT : Continuous (fun ξ : ℝ => fderiv ℝ f (t, ξ) (1, 0)) :=
    (hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun ξ _ => ⟨ht, mem_univ ξ⟩)) |> continuousOn_univ.1
  have hbnd : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∈ uIoc a b → ∀ x ∈ Ioo (t / 2) ((t + s) / 2),
      ‖fderiv ℝ f (x, ξ) (1, 0)‖ ≤ M :=
    ae_of_all _ fun ξ hξ x hx => hM (x, ξ) ⟨⟨hx.1.le, hx.2.le⟩, uIoc_subset_uIcc hξ⟩
  have hfst : ∀ x ∈ Ioo (0 : ℝ) s, ∀ ξ : ℝ,
      HasDerivAt (fun r => f (r, ξ)) (fderiv ℝ f (x, ξ) (1, 0)) x := by
    intro x hx ξ
    have hmem : ((x, ξ) : ℝ × ℝ) ∈ Ioo (0 : ℝ) s ×ˢ (univ : Set ℝ) := ⟨hx, mem_univ ξ⟩
    have hdiff : DifferentiableAt ℝ f (x, ξ) :=
      (hf.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact hdiff.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x ξ))
  have hdiffs : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∈ uIoc a b → ∀ x ∈ Ioo (t / 2) ((t + s) / 2),
      HasDerivAt (fun x => f (x, ξ)) (fderiv ℝ f (x, ξ) (1, 0)) x :=
    ae_of_all _ fun ξ _ x hx => hfst x ⟨by linarith [hx.1], by linarith [hx.2]⟩ ξ
  have hres := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun r ξ => f (r, ξ)) (F' := fun r ξ => fderiv ℝ f (r, ξ) (1, 0))
    (bound := fun _ => M) hnhds hmeas hFint hcontT.aestronglyMeasurable
    hbnd (continuous_const.intervalIntegrable _ _) hdiffs).2
  refine hres.congr_deriv ?_
  refine intervalIntegral.integral_congr fun ξ _ => ?_
  exact (hfst t ht ξ).deriv.symm

/-- Wronskian / Green's flux `W(t, ξ) = K(t, ξ) ∂_ξ D(t, ξ) - ∂_ξ K(t, ξ) D(t, ξ)`. -/
private def W (ν c : ℝ) (tr : B0140.TrainSol ν c) (s η t ξ : ℝ) : ℝ :=
  K ν s η t ξ * deriv (D ν c tr t) ξ - deriv (K ν s η t) ξ * D ν c tr t ξ

private theorem continuousOn_W_time {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {s s₁ : ℝ} (hs₁ : s₁ < s) (η ξ : ℝ) :
    ContinuousOn (fun t : ℝ => W ν c tr s η t ξ) (Icc 0 s₁) := by
  have hsub_Iio : Icc (0 : ℝ) s₁ ⊆ Iio s := fun t ht => lt_of_le_of_lt ht.2 hs₁
  have hsub_Ici : Icc (0 : ℝ) s₁ ⊆ Ici 0 := fun t ht => ht.1
  have hK_cont : ContinuousOn (fun t : ℝ => K ν s η t ξ) (Icc 0 s₁) :=
    (contDiffOn_K hν η).continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨hsub_Iio ht, mem_univ ξ⟩)
  have hdK_cont : ContinuousOn (fun t : ℝ => deriv (K ν s η t) ξ) (Icc 0 s₁) := by
    have h1 : ContinuousOn
        (fun t : ℝ => (η - ξ) / (2 * (ν * (s - t))) * K ν s η t ξ) (Icc 0 s₁) :=
      (continuousOn_const.div
        (continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
        (fun t ht => mul_ne_zero two_ne_zero (mul_pos hν (sub_pos.2 (hsub_Iio ht))).ne')).mul
        hK_cont
    exact h1.congr fun t ht => deriv_K_eta hν (hsub_Iio ht) η ξ
  have hD_cont : ContinuousOn (fun t : ℝ => D ν c tr t ξ) (Icc 0 s₁) :=
    (continuousOn_D hν hc tr hb).comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨hsub_Ici ht, mem_univ ξ⟩)
  have hdD_cont : ContinuousOn (fun t : ℝ => deriv (D ν c tr t) ξ) (Icc 0 s₁) := by
    set v0_ext : ℝ → Plane → ℝ := fun r z => tr.v (max r 0) z 0
    have hv_cont : Continuous (fun p : ℝ × Plane => v0_ext p.1 p.2) := by
      have hsm : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
        (PiLp.continuous_apply 2 _ 0).comp_continuousOn tr.isTrain.smooth_v.continuousOn
      have hmap : Continuous (fun p : ℝ × Plane => ((max p.1 0, p.2) : ℝ × Plane)) :=
        (continuous_fst.max continuous_const).prodMk continuous_snd
      exact hsm.comp_continuous hmap (fun p => ⟨mem_Ici.2 (le_max_right p.1 0), mem_univ _⟩)
    have hu_cont : Continuous (fun r : ℝ => hmean c (v0_ext r) ξ) := by
      have hle : -c / 2 ≤ c / 2 := by linarith
      have hfun : (fun r : ℝ => hmean c (v0_ext r) ξ) =
          fun r : ℝ => c⁻¹ * ∫ q in (-c / 2)..(c / 2), v0_ext r (q, ξ) := by
        funext r
        simp only [hmean, smul_eq_mul, intervalIntegral.integral_of_le hle]
      rw [hfun]
      have hcont_q : Continuous (Function.uncurry (fun r q : ℝ => v0_ext r (q, ξ))) :=
        hv_cont.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
      exact continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          hcont_q (-c / 2) (c / 2))
    have hvel_cont : ContinuousOn (fun t : ℝ => meanVel1 tr t ξ) (Icc 0 s₁) := by
      refine hu_cont.continuousOn.congr fun t ht => ?_
      have hmax : max t 0 = t := max_eq_left ht.1
      simp only [meanVel1, v0_ext, hmax]
    have hvort_cont : ContinuousOn (fun t : ℝ => deriv (vortexMeanStream ν c t) ξ) (Icc 0 s₁) := by
      have hw_cont : ContinuousOn (width ν) (Icc 0 s₁) :=
        continuousOn_const.add (continuousOn_const.mul continuousOn_id)
      have hw_pos : ∀ t ∈ Icc (0 : ℝ) s₁, 0 < width ν t := by
        intro t ht; unfold width; have : 0 ≤ t := ht.1; nlinarith
      have hV_K : ContinuousOn (fun t : ℝ => heatKernel1 (width ν t) ξ) (Icc 0 s₁) := by
        unfold heatKernel1
        refine ContinuousOn.mul ?_ ?_
        · exact (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hw_cont)).inv₀
            fun t ht => (Real.sqrt_pos.2 (mul_pos (by positivity) (hw_pos t ht))).ne'
        · exact Real.continuous_exp.comp_continuousOn
            (continuousOn_const.div (continuousOn_const.mul hw_cont)
              fun t ht => mul_ne_zero (by norm_num) (hw_pos t ht).ne')
      have h1 : ContinuousOn
          (fun t : ℝ => -(8 * Real.pi * c⁻¹) * (-(ξ / (2 * width ν t)) *
            heatKernel1 (width ν t) ξ)) (Icc 0 s₁) :=
        continuousOn_const.mul
          (((continuousOn_const.div (continuousOn_const.mul hw_cont)
            fun t ht => mul_ne_zero two_ne_zero (hw_pos t ht).ne').neg).mul hV_K)
      refine h1.congr fun t ht => ?_
      unfold vortexMeanStream
      exact ((hasDerivAt_heatKernel1_eta (hw_pos t ht) ξ).const_mul (-(8 * Real.pi * c⁻¹))).deriv
    exact (hvel_cont.neg.sub hvort_cont).congr fun t ht => deriv_D_eta hν tr ht.1 ξ
  exact (hK_cont.mul hdD_cont).sub (hdK_cont.mul hD_cont)

/-- Finite-interval Green's identity on `[0, s₁] × [-R, R]` for `0 < s₁ < s`. -/
private theorem green_identity_box {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {s s₁ : ℝ}
    (hs₁0 : 0 < s₁) (hs₁s : s₁ < s) (η R : ℝ) :
    (∫ ξ in (-R)..R, K ν s η s₁ ξ * D ν c tr s₁ ξ) =
      ν * (∫ t in (0 : ℝ)..s₁, (W ν c tr s η t R - W ν c tr s η t (-R))) +
        ∫ t in (0 : ℝ)..s₁, ∫ ξ in (-R)..R, K ν s η t ξ * meanStress tr t ξ := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  set I_R : ℝ → ℝ := fun t => ∫ ξ in (-R)..R, K ν s η t ξ * D ν c tr t ξ
  set f'_R : ℝ → ℝ := fun t =>
    ν * (W ν c tr s η t R - W ν c tr s η t (-R)) +
      ∫ ξ in (-R)..R, K ν s η t ξ * meanStress tr t ξ
  have hI_zero : I_R 0 = 0 := by
    dsimp [I_R]
    simp_rw [D_zero hc1 tr, mul_zero, intervalIntegral.integral_zero]
  have hI_cont : ContinuousOn I_R (Icc 0 s₁) := by
    set F_ext : ℝ → ℝ → ℝ := fun t ξ =>
      K ν s η (min (max t 0) s₁) ξ * D ν c tr (min (max t 0) s₁) ξ
    have hclamp : Continuous (fun t : ℝ => min (max t 0) s₁) :=
      (continuous_id.max continuous_const).min continuous_const
    have hclamp_mem : ∀ t : ℝ, min (max t 0) s₁ ∈ Icc (0 : ℝ) s₁ :=
      fun t => ⟨le_min (le_max_right t 0) hs₁0.le, min_le_right _ _⟩
    have hF_cont : Continuous (Function.uncurry F_ext) := by
      have hmap : Continuous (fun p : ℝ × ℝ => ((min (max p.1 0) s₁, p.2) : ℝ × ℝ)) :=
        (hclamp.comp continuous_fst).prodMk continuous_snd
      have hK_c : Continuous (fun p : ℝ × ℝ => K ν s η (min (max p.1 0) s₁) p.2) :=
        (contDiffOn_K hν η).continuousOn.comp_continuous hmap
          (fun p => ⟨lt_of_le_of_lt (hclamp_mem p.1).2 hs₁s, mem_univ p.2⟩)
      have hD_c : Continuous (fun p : ℝ × ℝ => D ν c tr (min (max p.1 0) s₁) p.2) :=
        (continuousOn_D hν hc0 tr hb).comp_continuous hmap
          (fun p => ⟨(hclamp_mem p.1).1, mem_univ p.2⟩)
      exact hK_c.mul hD_c
    have hInt_c : Continuous (fun t : ℝ => ∫ ξ in (-R)..R, F_ext t ξ) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF_cont (-R) R
    refine hInt_c.continuousOn.congr fun t ht => ?_
    have hcl : min (max t 0) s₁ = t := by rw [max_eq_left ht.1, min_eq_left ht.2]
    simp only [I_R, F_ext, hcl]
  have hstress_cont : ContinuousOn
      (fun t : ℝ => ∫ ξ in (-R)..R, K ν s η t ξ * meanStress tr t ξ) (Icc 0 s₁) := by
    set G_ext : ℝ → ℝ → ℝ := fun t ξ =>
      K ν s η (min (max t 0) s₁) ξ * meanStress tr (min (max t 0) s₁) ξ
    have hclamp : Continuous (fun t : ℝ => min (max t 0) s₁) :=
      (continuous_id.max continuous_const).min continuous_const
    have hclamp_mem : ∀ t : ℝ, min (max t 0) s₁ ∈ Icc (0 : ℝ) s₁ :=
      fun t => ⟨le_min (le_max_right t 0) hs₁0.le, min_le_right _ _⟩
    have hms_Ici := continuousOn_meanStress_Ici hc0 tr
    have hG_cont : Continuous (Function.uncurry G_ext) := by
      have hmap : Continuous (fun p : ℝ × ℝ => ((min (max p.1 0) s₁, p.2) : ℝ × ℝ)) :=
        (hclamp.comp continuous_fst).prodMk continuous_snd
      have hK_c : Continuous (fun p : ℝ × ℝ => K ν s η (min (max p.1 0) s₁) p.2) :=
        (contDiffOn_K hν η).continuousOn.comp_continuous hmap
          (fun p => ⟨lt_of_le_of_lt (hclamp_mem p.1).2 hs₁s, mem_univ p.2⟩)
      have hms_c : Continuous (fun p : ℝ × ℝ => meanStress tr (min (max p.1 0) s₁) p.2) :=
        hms_Ici.comp_continuous hmap (fun p => ⟨(hclamp_mem p.1).1, mem_univ p.2⟩)
      exact hK_c.mul hms_c
    have hInt_c : Continuous (fun t : ℝ => ∫ ξ in (-R)..R, G_ext t ξ) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG_cont (-R) R
    refine hInt_c.continuousOn.congr fun t ht => ?_
    have hcl : min (max t 0) s₁ = t := by rw [max_eq_left ht.1, min_eq_left ht.2]
    simp only [G_ext, hcl]
  have hW_cont : ContinuousOn (fun t : ℝ => W ν c tr s η t R - W ν c tr s η t (-R)) (Icc 0 s₁) :=
    (continuousOn_W_time hν hc0 tr hb hs₁s η R).sub
      (continuousOn_W_time hν hc0 tr hb hs₁s η (-R))
  have hint_W : IntervalIntegrable
      (fun t => W ν c tr s η t R - W ν c tr s η t (-R)) volume 0 s₁ :=
    hW_cont.intervalIntegrable_of_Icc hs₁0.le
  have hint_S : IntervalIntegrable
      (fun t => ∫ ξ in (-R)..R, K ν s η t ξ * meanStress tr t ξ) volume 0 s₁ :=
    hstress_cont.intervalIntegrable_of_Icc hs₁0.le
  have hint_f' : IntervalIntegrable f'_R volume 0 s₁ :=
    (hint_W.const_mul ν).add hint_S
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) s₁, HasDerivAt I_R (f'_R t) t := by
    intro t ht
    have ht_s : t ∈ Ioo (0 : ℝ) s := ⟨ht.1, lt_trans ht.2 hs₁s⟩
    have hKD_smooth : ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => K ν s η x.1 x.2 * D ν c tr x.1 x.2) (Ioo 0 s ×ˢ univ) :=
      ((contDiffOn_K hν η).mono (prod_mono Ioo_subset_Iio_self Subset.rfl)).mul
        ((contDiffOn_D hν hc0 tr hb).mono (prod_mono Ioo_subset_Ioi_self Subset.rfl))
    have hI := integral_hasDerivAt_interval_Ioo hKD_smooth ht_s (-R) R
    refine hI.congr_deriv ?_
    have hD_smooth : ContDiff ℝ ∞ (D ν c tr t) :=
      t01_contDiff_slice (contDiffOn_D hν hc0 tr hb) ht.1
    have hdD_smooth : ContDiff ℝ ∞ (deriv (D ν c tr t)) := hD_smooth.deriv'
    have hddD_smooth : ContDiff ℝ ∞ (deriv (deriv (D ν c tr t))) := hdD_smooth.deriv'
    have hddD_cont : Continuous (deriv (deriv (D ν c tr t))) := hddD_smooth.continuous
    have hK_smooth : ContDiff ℝ ∞ (K ν s η t) := by
      have hcomp : ContDiffOn ℝ ∞
          ((fun x : ℝ × ℝ => K ν s η x.1 x.2) ∘ (fun ξ : ℝ => ((t, ξ) : ℝ × ℝ))) univ :=
        (contDiffOn_K hν η).comp (contDiffOn_univ.2 (contDiff_const.prodMk contDiff_id))
          (fun ξ _ => ⟨ht_s.2, mem_univ ξ⟩)
      exact contDiffOn_univ.1 hcomp
    have hdK_smooth : ContDiff ℝ ∞ (deriv (K ν s η t)) := hK_smooth.deriv'
    have hddK_smooth : ContDiff ℝ ∞ (deriv (deriv (K ν s η t))) := hdK_smooth.deriv'
    have hddK_cont : Continuous (deriv (deriv (K ν s η t))) := hddK_smooth.continuous
    set W' : ℝ → ℝ := fun ξ =>
      K ν s η t ξ * deriv (deriv (D ν c tr t)) ξ -
        deriv (deriv (K ν s η t)) ξ * D ν c tr t ξ
    have hW_deriv : ∀ ξ : ℝ, HasDerivAt (W ν c tr s η t) (W' ξ) ξ := by
      intro ξ
      unfold W
      have h1 := ((hK_smooth.differentiable (by simp) ξ).hasDerivAt).mul
        ((hdD_smooth.differentiable (by simp) ξ).hasDerivAt)
      have h2 := ((hdK_smooth.differentiable (by simp) ξ).hasDerivAt).mul
        ((hD_smooth.differentiable (by simp) ξ).hasDerivAt)
      refine (h1.sub h2).congr_deriv ?_
      dsimp [W']
      ring
    have hW'_cont : Continuous W' :=
      (hK_smooth.continuous.mul hddD_cont).sub (hddK_cont.mul hD_smooth.continuous)
    have hKg_cont : Continuous (fun ξ : ℝ => K ν s η t ξ * meanStress tr t ξ) :=
      hK_smooth.continuous.mul (PartI_T23.continuous_meanStress hc0.le tr ht.1.le)
    have hpt_eq : ∀ ξ : ℝ,
        deriv (fun r => K ν s η r ξ * D ν c tr r ξ) t =
          ν * W' ξ + K ν s η t ξ * meanStress tr t ξ := by
      intro ξ
      have hprod := (hasDerivAt_K_time hν ht_s.2 η ξ).mul (D_pde hν hc0 tr hb ht.1 ξ)
      exact (hprod.congr_deriv (by dsimp [W']; ring)).deriv
    simp_rw [hpt_eq]
    rw [intervalIntegral.integral_add ((hW'_cont.intervalIntegrable _ _).const_mul ν)
      (hKg_cont.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ξ _ => hW_deriv ξ)
        (hW'_cont.intervalIntegrable _ _)]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs₁0.le hI_cont hderiv hint_f'
  rw [hI_zero, sub_zero] at hFTC
  change I_R s₁ = _
  rw [← hFTC]
  exact (intervalIntegral.integral_add (hint_W.const_mul ν) hint_S).trans
    (by rw [intervalIntegral.integral_const_mul])

/-! ### 5. Passage to `R → +∞` at fixed `s₁ ∈ (0, s)` and then `s₁ → s⁻` -/

private theorem duhamel_at_s1 {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {s s₁ : ℝ}
    (hs₁0 : 0 < s₁) (hs₁s : s₁ < s) (η : ℝ) :
    (∫ ξ : ℝ, K ν s η s₁ ξ * D ν c tr s₁ ξ) =
      ∫ t in (0 : ℝ)..s₁, ∫ ξ : ℝ, K ν s η t ξ * meanStress tr t ξ := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hs0 : 0 < s := lt_trans hs₁0 hs₁s
  obtain ⟨C₀, M₁, hC₀, hM₁, hD_bd⟩ := D_uniform_bounds hν hc0 tr hb hs0
  obtain ⟨M0, hM0⟩ := hb.sup_bound hs0.le
  have hM0_nn : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 ⟨le_rfl, hs0.le⟩ 0)
  set a_min : ℝ := ν * (s - s₁)
  set a_max : ℝ := ν * s
  have hamin : 0 < a_min := mul_pos hν (sub_pos.2 hs₁s)
  have hamax : 0 < a_max := mul_pos hν hs0
  have ha_range : ∀ t ∈ Icc (0 : ℝ) s₁, a_min ≤ ν * (s - t) ∧ ν * (s - t) ≤ a_max := by
    intro t ht
    dsimp [a_min, a_max]
    exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
  -- 1. Uniform Gaussian-decaying envelope on `t ∈ Icc 0 s₁`
  set pre : ℝ := (Real.sqrt (4 * Real.pi * a_min))⁻¹
  have hpre_pos : 0 < pre := by dsimp [pre]; positivity
  have hK_le : ∀ t ∈ Icc (0 : ℝ) s₁, ∀ ξ : ℝ,
      |K ν s η t ξ| ≤ pre * Real.exp (-((η - ξ) ^ 2) / (4 * a_max)) := by
    intro t ht ξ
    have ha := ha_range t ht
    have hat : 0 < ν * (s - t) := lt_of_lt_of_le hamin ha.1
    unfold K heatKernel1
    rw [abs_of_pos (by positivity)]
    refine mul_le_mul ?_ ?_ (Real.exp_pos _).le hpre_pos.le
    · exact inv_anti₀ (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_le_sqrt (by nlinarith [ha.1, Real.pi_pos]))
    · apply Real.exp_le_exp.2
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith [ha.2])
  -- 2. Integrability and decay of `env ξ := 27 * (1 + ((η - ξ) / √(4 * a_max))²)⁻¹`
  set env : ℝ → ℝ := fun ξ =>
    27 * (1 + ((η - ξ) / Real.sqrt (4 * a_max)) ^ 2)⁻¹
  have henv_int : Integrable env volume := by
    have hsq : 0 < Real.sqrt (4 * a_max) := Real.sqrt_pos.2 (by positivity)
    have h1 := (integrable_inv_one_add_sq.comp_div hsq.ne').comp_sub_left η
    exact h1.const_mul 27
  have henv_tendsto_top : Tendsto env atTop (𝓝 0) := by
    have hsq : 0 < Real.sqrt (4 * a_max) := Real.sqrt_pos.2 (by positivity)
    have hsub : Tendsto (fun ξ : ℝ => (ξ - η) / Real.sqrt (4 * a_max)) atTop atTop :=
      (tendsto_id.atTop_add tendsto_const_nhds).atTop_div_const hsq
    have h1 : Tendsto (fun ξ : ℝ => ((η - ξ) / Real.sqrt (4 * a_max)) ^ 2) atTop atTop := by
      refine ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hsub).congr fun ξ => ?_
      dsimp only [Function.comp_apply]
      rw [← neg_sub η ξ, neg_div, neg_sq]
    have h2 : Tendsto (fun ξ : ℝ => (1 + ((η - ξ) / Real.sqrt (4 * a_max)) ^ 2)⁻¹)
        atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop h1)
    simpa [env, mul_zero] using h2.const_mul 27
  have henv_tendsto_bot : Tendsto env atBot (𝓝 0) := by
    have hsq : 0 < Real.sqrt (4 * a_max) := Real.sqrt_pos.2 (by positivity)
    have hsub : Tendsto (fun ξ : ℝ => (η - ξ) / Real.sqrt (4 * a_max)) atBot atTop :=
      (tendsto_const_nhds.add_atTop tendsto_neg_atBot_atTop).atTop_div_const hsq
    have h1 : Tendsto (fun ξ : ℝ => ((η - ξ) / Real.sqrt (4 * a_max)) ^ 2) atBot atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hsub
    have h2 : Tendsto (fun ξ : ℝ => (1 + ((η - ξ) / Real.sqrt (4 * a_max)) ^ 2)⁻¹)
        atBot (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop h1)
    simpa [env, mul_zero] using h2.const_mul 27
  have hexp_le_env : ∀ ξ : ℝ,
      (1 + (η - ξ) ^ 2 / (4 * a_max)) * Real.exp (-((η - ξ) ^ 2) / (4 * a_max)) ≤ env ξ :=
    fun ξ => exp_neg_le_inv_one_add_sq hamax (η - ξ)
  -- 3. Bound `|W t ξ| ≤ (pre * K_W) * env ξ` for all `t ∈ Icc 0 s₁` and `ξ ∈ ℝ`
  set B_W : ℝ := (2 * a_min)⁻¹ * (C₀ + M₁ * |η|)
  set C_W2 : ℝ := (2 * a_min)⁻¹ * M₁
  set K_W : ℝ := M₁ + B_W * (1 + a_max) + C_W2 * (4 * a_max)
  have hB_W_nn : 0 ≤ B_W := by positivity
  have hC_W2_nn : 0 ≤ C_W2 := by positivity
  have hK_W_nn : 0 ≤ K_W := by positivity
  have hW_le : ∀ t ∈ Icc (0 : ℝ) s₁, ∀ ξ : ℝ,
      |W ν c tr s η t ξ| ≤ (pre * K_W) * env ξ := by
    intro t ht ξ
    have ht_s : t ∈ Icc (0 : ℝ) s := ⟨ht.1, ht.2.trans hs₁s.le⟩
    obtain ⟨hdD_bd, hD_bd'⟩ := hD_bd t ht_s ξ
    have ha := ha_range t ht
    have hat : 0 < ν * (s - t) := lt_of_lt_of_le hamin ha.1
    have hdK_bd : |deriv (K ν s η t) ξ| ≤
        |η - ξ| / (2 * a_min) * (pre * Real.exp (-((η - ξ) ^ 2) / (4 * a_max))) := by
      rw [deriv_K_eta hν (lt_of_le_of_lt ht.2 hs₁s) η ξ, abs_mul, abs_div,
        abs_of_pos (mul_pos two_pos hat)]
      have hdiv : |η - ξ| / (2 * (ν * (s - t))) ≤ |η - ξ| / (2 * a_min) :=
        div_le_div_of_nonneg_left (abs_nonneg (η - ξ)) (mul_pos two_pos hamin) (by linarith [ha.1])
      exact mul_le_mul hdiv (hK_le t ht ξ) (abs_nonneg _) (by positivity)
    have hξ_le : |ξ| ≤ |η| + |η - ξ| := by
      simpa [sub_sub_cancel] using abs_sub η (η - ξ)
    have hquad := quad_le_one_add_sq_div hamax hM₁ hB_W_nn hC_W2_nn (η - ξ)
    have hpoly_le : M₁ + |η - ξ| / (2 * a_min) * (C₀ + M₁ * |ξ|) ≤
        K_W * (1 + (η - ξ) ^ 2 / (4 * a_max)) := by
      have h1 : C₀ + M₁ * |ξ| ≤ (C₀ + M₁ * |η|) + M₁ * |η - ξ| := by nlinarith
      have h2 : |η - ξ| / (2 * a_min) * (C₀ + M₁ * |ξ|) ≤
          B_W * |η - ξ| + C_W2 * (η - ξ) ^ 2 := by
        calc |η - ξ| / (2 * a_min) * (C₀ + M₁ * |ξ|)
            ≤ |η - ξ| / (2 * a_min) * ((C₀ + M₁ * |η|) + M₁ * |η - ξ|) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = B_W * |η - ξ| + C_W2 * |η - ξ| ^ 2 := by dsimp [B_W, C_W2]; ring
          _ = B_W * |η - ξ| + C_W2 * (η - ξ) ^ 2 := by rw [sq_abs]
      dsimp [K_W] at hquad ⊢
      linarith
    unfold W
    calc |K ν s η t ξ * deriv (D ν c tr t) ξ - deriv (K ν s η t) ξ * D ν c tr t ξ|
        ≤ |K ν s η t ξ| * |deriv (D ν c tr t) ξ| +
            |deriv (K ν s η t) ξ| * |D ν c tr t ξ| := by
          simpa [abs_mul] using abs_sub (K ν s η t ξ * deriv (D ν c tr t) ξ)
            (deriv (K ν s η t) ξ * D ν c tr t ξ)
      _ ≤ (pre * Real.exp (-((η - ξ) ^ 2) / (4 * a_max))) * M₁ +
            (|η - ξ| / (2 * a_min) * (pre * Real.exp (-((η - ξ) ^ 2) / (4 * a_max)))) *
              (C₀ + M₁ * |ξ|) :=
          add_le_add (mul_le_mul (hK_le t ht ξ) hdD_bd (abs_nonneg _) (by positivity))
            (mul_le_mul hdK_bd hD_bd' (abs_nonneg _) (by positivity))
      _ = pre * ((M₁ + |η - ξ| / (2 * a_min) * (C₀ + M₁ * |ξ|)) *
            Real.exp (-((η - ξ) ^ 2) / (4 * a_max))) := by ring
      _ ≤ pre * (K_W * ((1 + (η - ξ) ^ 2 / (4 * a_max)) *
            Real.exp (-((η - ξ) ^ 2) / (4 * a_max)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hpre_pos.le
          calc (M₁ + |η - ξ| / (2 * a_min) * (C₀ + M₁ * |ξ|)) *
                Real.exp (-((η - ξ) ^ 2) / (4 * a_max))
              ≤ (K_W * (1 + (η - ξ) ^ 2 / (4 * a_max))) *
                  Real.exp (-((η - ξ) ^ 2) / (4 * a_max)) :=
                mul_le_mul_of_nonneg_right hpoly_le (Real.exp_pos _).le
            _ = _ := by ring
      _ ≤ pre * (K_W * env ξ) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hexp_le_env ξ) hK_W_nn) hpre_pos.le
      _ = (pre * K_W) * env ξ := by ring
  -- 4. Limit of the LHS as `R → +∞`
  set K_D : ℝ := (C₀ + M₁ * |η|) + M₁ * (1 + a_max) + 0 * (4 * a_max)
  have hK_D_nn : 0 ≤ K_D := by dsimp [K_D]; positivity
  have hLHS_int : Integrable (fun ξ : ℝ => K ν s η s₁ ξ * D ν c tr s₁ ξ) volume := by
    have hcont : Continuous (fun ξ : ℝ => K ν s η s₁ ξ * D ν c tr s₁ ξ) := by
      have hK_c : Continuous (fun ξ : ℝ => K ν s η s₁ ξ) :=
        (contDiffOn_K hν η).continuousOn.comp_continuous
          (continuous_const.prodMk continuous_id) (fun ξ => ⟨hs₁s, mem_univ ξ⟩)
      have hD_c : Continuous (fun ξ : ℝ => D ν c tr s₁ ξ) :=
        (continuousOn_D hν hc0 tr hb).comp_continuous
          (continuous_const.prodMk continuous_id) (fun ξ => ⟨hs₁0.le, mem_univ ξ⟩)
      exact hK_c.mul hD_c
    refine (henv_int.const_mul (pre * K_D)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have ht_s1 : s₁ ∈ Icc (0 : ℝ) s₁ := ⟨hs₁0.le, le_rfl⟩
    have ht_s : s₁ ∈ Icc (0 : ℝ) s := ⟨hs₁0.le, hs₁s.le⟩
    obtain ⟨_, hD_bd'⟩ := hD_bd s₁ ht_s ξ
    have hξ_le : |ξ| ≤ |η| + |η - ξ| := by
      simpa [sub_sub_cancel] using abs_sub η (η - ξ)
    have hquad := quad_le_one_add_sq_div hamax
      (by positivity : 0 ≤ C₀ + M₁ * |η|) hM₁ (le_rfl : (0 : ℝ) ≤ 0) (η - ξ)
    have hD_le : C₀ + M₁ * |ξ| ≤ K_D * (1 + (η - ξ) ^ 2 / (4 * a_max)) := by
      have h1 : C₀ + M₁ * |ξ| ≤ (C₀ + M₁ * |η|) + M₁ * |η - ξ| + 0 * (η - ξ) ^ 2 := by
        nlinarith
      exact h1.trans hquad
    calc |K ν s η s₁ ξ| * |D ν c tr s₁ ξ|
        ≤ (pre * Real.exp (-((η - ξ) ^ 2) / (4 * a_max))) * (C₀ + M₁ * |ξ|) :=
          mul_le_mul (hK_le s₁ ht_s1 ξ) hD_bd' (abs_nonneg _) (by positivity)
      _ ≤ (pre * Real.exp (-((η - ξ) ^ 2) / (4 * a_max))) *
            (K_D * (1 + (η - ξ) ^ 2 / (4 * a_max))) :=
          mul_le_mul_of_nonneg_left hD_le (by positivity)
      _ = (pre * K_D) * ((1 + (η - ξ) ^ 2 / (4 * a_max)) *
            Real.exp (-((η - ξ) ^ 2) / (4 * a_max))) := by ring
      _ ≤ (pre * K_D) * env ξ :=
          mul_le_mul_of_nonneg_left (hexp_le_env ξ) (by positivity)
  have hLHS_lim : Tendsto
      (fun R : ℝ => ∫ ξ in (-R)..R, K ν s η s₁ ξ * D ν c tr s₁ ξ)
      atTop (𝓝 (∫ ξ : ℝ, K ν s η s₁ ξ * D ν c tr s₁ ξ)) :=
    intervalIntegral_tendsto_integral hLHS_int tendsto_neg_atTop_atBot tendsto_id
  -- 5. Limit of the boundary term as `R → +∞`
  have hBnd_lim : Tendsto
      (fun R : ℝ => ν * ∫ t in (0 : ℝ)..s₁, (W ν c tr s η t R - W ν c tr s η t (-R)))
      atTop (𝓝 0) := by
    have h0 : Tendsto
        (fun R : ℝ => ∫ t in (0 : ℝ)..s₁, (W ν c tr s η t R - W ν c tr s η t (-R)))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (g := fun R => (pre * K_W) * (env R + env (-R)) * s₁)
        (fun _ => norm_nonneg _) (fun R => ?_) ?_
      · have hpt : ∀ t ∈ uIoc (0 : ℝ) s₁,
            ‖W ν c tr s η t R - W ν c tr s η t (-R)‖ ≤
              (pre * K_W) * (env R + env (-R)) := by
          intro t ht
          rw [uIoc_of_le hs₁0.le] at ht
          have ht_Icc : t ∈ Icc (0 : ℝ) s₁ := ⟨ht.1.le, ht.2⟩
          rw [Real.norm_eq_abs]
          calc |W ν c tr s η t R - W ν c tr s η t (-R)|
              ≤ |W ν c tr s η t R| + |W ν c tr s η t (-R)| := abs_sub _ _
            _ ≤ (pre * K_W) * env R + (pre * K_W) * env (-R) :=
                add_le_add (hW_le t ht_Icc R) (hW_le t ht_Icc (-R))
            _ = (pre * K_W) * (env R + env (-R)) := by ring
        have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
        rwa [sub_zero, abs_of_pos hs₁0] at h
      · have hsum : Tendsto (fun R : ℝ => env R + env (-R)) atTop (𝓝 (0 + 0)) :=
          henv_tendsto_top.add (henv_tendsto_bot.comp tendsto_neg_atTop_atBot)
        simpa using (hsum.const_mul (pre * K_W)).mul_const s₁
    simpa [mul_zero] using h0.const_mul ν
  -- 6. Limit of the source integral as `R → +∞`
  have hSrc_lim : Tendsto
      (fun R : ℝ => ∫ t in (0 : ℝ)..s₁, ∫ ξ in (-R)..R, K ν s η t ξ * meanStress tr t ξ)
      atTop (𝓝 (∫ t in (0 : ℝ)..s₁, ∫ ξ : ℝ, K ν s η t ξ * meanStress tr t ξ)) := by
    have hKg_int : ∀ t ∈ Icc (0 : ℝ) s₁,
        Integrable (fun ξ : ℝ => K ν s η t ξ * meanStress tr t ξ) volume := by
      intro t ht
      have hK_c : Continuous (fun ξ : ℝ => K ν s η t ξ) :=
        (contDiffOn_K hν η).continuousOn.comp_continuous
          (continuous_const.prodMk continuous_id) (fun ξ => ⟨lt_of_le_of_lt ht.2 hs₁s, mem_univ ξ⟩)
      have hcont : Continuous (fun ξ : ℝ => K ν s η t ξ * meanStress tr t ξ) :=
        hK_c.mul (PartI_T23.continuous_meanStress hc0.le tr ht.1)
      refine (henv_int.const_mul (pre * (M0 * M0))).mono' hcont.aestronglyMeasurable
        (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have hg_bd := msi_meanStress_bound hc0 tr
        (fun z => hM0 t ⟨ht.1, ht.2.trans hs₁s.le⟩ z) ξ
      have hexp_le : Real.exp (-((η - ξ) ^ 2) / (4 * a_max)) ≤ env ξ := by
        calc Real.exp (-((η - ξ) ^ 2) / (4 * a_max))
            ≤ (1 + (η - ξ) ^ 2 / (4 * a_max)) * Real.exp (-((η - ξ) ^ 2) / (4 * a_max)) :=
              le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right (by positivity))
          _ ≤ env ξ := hexp_le_env ξ
      calc |K ν s η t ξ| * |meanStress tr t ξ|
          ≤ (pre * Real.exp (-((η - ξ) ^ 2) / (4 * a_max))) * (M0 * M0) :=
            mul_le_mul (hK_le t ht ξ) hg_bd (abs_nonneg _) (by positivity)
        _ ≤ (pre * env ξ) * (M0 * M0) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp_le hpre_pos.le) (by positivity)
        _ = (pre * (M0 * M0)) * env ξ := by ring
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M0 * M0) (Eventually.of_forall fun R => ?_)
      ((eventually_ge_atTop (0 : ℝ)).mono fun R hR => ae_of_all _ fun t ht => ?_)
      intervalIntegrable_const (ae_of_all _ fun t ht => ?_)
    · rw [uIoc_of_le hs₁0.le]
      set G_ext : ℝ → ℝ → ℝ := fun t ξ =>
        K ν s η (min (max t 0) s₁) ξ * meanStress tr (min (max t 0) s₁) ξ
      have hclamp : Continuous (fun t : ℝ => min (max t 0) s₁) :=
        (continuous_id.max continuous_const).min continuous_const
      have hclamp_mem : ∀ t : ℝ, min (max t 0) s₁ ∈ Icc (0 : ℝ) s₁ :=
        fun t => ⟨le_min (le_max_right t 0) hs₁0.le, min_le_right _ _⟩
      have hms_Ici := continuousOn_meanStress_Ici hc0 tr
      have hG_cont : Continuous (Function.uncurry G_ext) := by
        have hmap : Continuous (fun p : ℝ × ℝ => ((min (max p.1 0) s₁, p.2) : ℝ × ℝ)) :=
          (hclamp.comp continuous_fst).prodMk continuous_snd
        have hK_c : Continuous (fun p : ℝ × ℝ => K ν s η (min (max p.1 0) s₁) p.2) :=
          (contDiffOn_K hν η).continuousOn.comp_continuous hmap
            (fun p => ⟨lt_of_le_of_lt (hclamp_mem p.1).2 hs₁s, mem_univ p.2⟩)
        have hms_c : Continuous (fun p : ℝ × ℝ => meanStress tr (min (max p.1 0) s₁) p.2) :=
          hms_Ici.comp_continuous hmap (fun p => ⟨(hclamp_mem p.1).1, mem_univ p.2⟩)
        exact hK_c.mul hms_c
      have hInt_c : Continuous (fun t : ℝ => ∫ ξ in (-R)..R, G_ext t ξ) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG_cont (-R) R
      have hInt_on : ContinuousOn
          (fun t : ℝ => ∫ ξ in (-R)..R, K ν s η t ξ * meanStress tr t ξ) (Ioc 0 s₁) := by
        refine hInt_c.continuousOn.congr fun t ht => ?_
        have hcl : min (max t 0) s₁ = t := by rw [max_eq_left ht.1.le, min_eq_left ht.2]
        simp only [G_ext, hcl]
      exact hInt_on.aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le hs₁0.le] at ht
      have ht_Icc : t ∈ Icc (0 : ℝ) s₁ := ⟨ht.1.le, ht.2⟩
      have hat : 0 < ν * (s - t) := lt_of_lt_of_le hamin (ha_range t ht_Icc).1
      have hK_int : Integrable (fun ξ : ℝ => (M0 * M0) * K ν s η t ξ) volume := by
        unfold K
        exact ((integrable_heatKernel1 hat).comp_sub_left η).const_mul (M0 * M0)
      have hpt_bd : ∀ ξ : ℝ, ‖K ν s η t ξ * meanStress tr t ξ‖ ≤ (M0 * M0) * K ν s η t ξ := by
        intro ξ
        have hK_nn : 0 ≤ K ν s η t ξ := by unfold K heatKernel1; positivity
        have hg_bd := msi_meanStress_bound hc0 tr
          (fun z => hM0 t ⟨ht.1.le, ht.2.trans hs₁s.le⟩ z) ξ
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK_nn, mul_comm]
        exact mul_le_mul_of_nonneg_right hg_bd hK_nn
      rw [intervalIntegral.integral_of_le (by linarith)]
      calc ‖∫ ξ in Ioc (-R) R, K ν s η t ξ * meanStress tr t ξ‖
          ≤ ∫ ξ in Ioc (-R) R, (M0 * M0) * K ν s η t ξ :=
            norm_integral_le_of_norm_le hK_int.integrableOn (Eventually.of_forall hpt_bd)
        _ ≤ ∫ ξ : ℝ, (M0 * M0) * K ν s η t ξ :=
            setIntegral_le_integral hK_int (Eventually.of_forall fun ξ => by
              unfold K heatKernel1; positivity)
        _ = M0 * M0 := by
            unfold K
            rw [integral_const_mul, integral_sub_left_eq_self,
              PartI_T23.integral_heatKernel1_eq_one hat, mul_one]
    · rw [uIoc_of_le hs₁0.le] at ht
      exact intervalIntegral_tendsto_integral (hKg_int t ⟨ht.1.le, ht.2⟩)
        tendsto_neg_atTop_atBot tendsto_id
  have hRHS_lim : Tendsto
      (fun R : ℝ =>
        ν * (∫ t in (0 : ℝ)..s₁, (W ν c tr s η t R - W ν c tr s η t (-R))) +
          ∫ t in (0 : ℝ)..s₁, ∫ ξ in (-R)..R, K ν s η t ξ * meanStress tr t ξ)
      atTop (𝓝 (0 + ∫ t in (0 : ℝ)..s₁, ∫ ξ : ℝ, K ν s η t ξ * meanStress tr t ξ)) :=
    hBnd_lim.add hSrc_lim
  have hRHS_lim' := hRHS_lim.congr fun R =>
    (green_identity_box hν hc1 tr hb hs₁0 hs₁s η R).symm
  have key := tendsto_nhds_unique hLHS_lim hRHS_lim'
  simpa using key

end StreamDuhamel

/-- Proves `TrainMeanStreamDuhamel` (`PartI:T23/2/1`). -/
theorem trainMeanStreamDuhamel_proof
    (_hTails : TrainStreamVelocityPressureTails)
    (_hFD : TrainFluctuationDecay)
    (_hMP : OverlapMeanPrimitive) :
    TrainMeanStreamDuhamel := by
  intro ρ hρ
  refine ⟨1, one_pos, ?_⟩
  intro ν hν hν1
  set c := trainPeriod ρ ν
  intro tr htr s hs η
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  rw [PartI_T23.meanDatumDuhamel_eq_vortexMeanStream hν hc1 tr hs η]
  suffices hD_eq : StreamDuhamel.D ν c tr s η = meanSourceDuhamel tr s η by
    unfold StreamDuhamel.D at hD_eq
    linarith
  -- Send `s₁ (n : ℕ) := s - s / (n + 2) → s` in `StreamDuhamel.duhamel_at_s1`
  set s₁ : ℕ → ℝ := fun n => s - s / ((n : ℝ) + 2)
  have hs₁_mem : ∀ n : ℕ, 0 < s₁ n ∧ s₁ n < s := by
    intro n
    have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hdiv_pos : 0 < s / ((n : ℝ) + 2) := div_pos hs (by positivity)
    have hdiv_le : s / ((n : ℝ) + 2) ≤ s / 2 :=
      div_le_div_of_nonneg_left hs.le two_pos hn2
    exact ⟨by dsimp [s₁]; linarith, by dsimp [s₁]; linarith⟩
  have hs₁_tendsto : Tendsto s₁ atTop (𝓝 s) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
    have hdiv : Tendsto (fun n : ℕ => s / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul s
    simpa [s₁] using tendsto_const_nhds.sub hdiv
  -- 1. LHS limit: `∫ ξ, K ν s η (s₁ n) ξ * D (s₁ n) ξ → D s η`
  obtain ⟨C₀, M₁, hC₀, hM₁, hD_bd⟩ := StreamDuhamel.D_uniform_bounds hν hc0 tr htr hs
  have hLHS_eq : ∀ n : ℕ,
      (∫ ξ : ℝ, StreamDuhamel.K ν s η (s₁ n) ξ * StreamDuhamel.D ν c tr (s₁ n) ξ) =
        ∫ z : ℝ, heatKernel1 1 z *
          StreamDuhamel.D ν c tr (s₁ n) (η - Real.sqrt (ν * (s - s₁ n)) * z) := by
    intro n
    exact StreamDuhamel.integral_heatKernel1_mul_eq_std
      (mul_pos hν (sub_pos.2 (hs₁_mem n).2)) η (StreamDuhamel.D ν c tr (s₁ n))
  have hK1_c : Continuous (heatKernel1 1) := StreamDuhamel.continuous_heatKernel1 one_pos
  have hLHS_lim : Tendsto
      (fun n : ℕ => ∫ ξ : ℝ, StreamDuhamel.K ν s η (s₁ n) ξ * StreamDuhamel.D ν c tr (s₁ n) ξ)
      atTop (𝓝 (StreamDuhamel.D ν c tr s η)) := by
    simp_rw [hLHS_eq]
    set dom : ℝ → ℝ := fun z =>
      heatKernel1 1 z * (C₀ + M₁ * |η| + M₁ * Real.sqrt (ν * s) * |z|)
    have hdom_int : Integrable dom volume := by
      set env1 : ℝ → ℝ := fun z => 27 * (1 + (z / Real.sqrt (4 * 1)) ^ 2)⁻¹
      have henv1_int : Integrable env1 volume :=
        (integrable_inv_one_add_sq.comp_div (Real.sqrt_pos.2 (by positivity)).ne').const_mul 27
      set K_dom : ℝ := (C₀ + M₁ * |η|) + (M₁ * Real.sqrt (ν * s)) * (1 + 1) + 0 * (4 * 1)
      set pre1 : ℝ := (Real.sqrt (4 * Real.pi * 1))⁻¹
      refine (henv1_int.const_mul (pre1 * K_dom)).mono'
        (hK1_c.mul (continuous_const.add (continuous_const.mul continuous_abs))).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [dom]; positivity)]
      have hexp_bd := StreamDuhamel.exp_neg_le_inv_one_add_sq one_pos z
      have hquad := StreamDuhamel.quad_le_one_add_sq_div one_pos
        (by positivity : 0 ≤ C₀ + M₁ * |η|)
        (by positivity : 0 ≤ M₁ * Real.sqrt (ν * s)) (le_rfl : (0 : ℝ) ≤ 0) z
      have hlin_le : C₀ + M₁ * |η| + M₁ * Real.sqrt (ν * s) * |z| ≤
          K_dom * (1 + z ^ 2 / (4 * 1)) := by
        have h1 : C₀ + M₁ * |η| + M₁ * Real.sqrt (ν * s) * |z| ≤
            (C₀ + M₁ * |η|) + (M₁ * Real.sqrt (ν * s)) * |z| + 0 * z ^ 2 := by linarith
        exact h1.trans hquad
      dsimp [dom]
      unfold heatKernel1
      calc pre1 * Real.exp (-(z ^ 2) / (4 * 1)) *
            (C₀ + M₁ * |η| + M₁ * Real.sqrt (ν * s) * |z|)
          ≤ pre1 * Real.exp (-(z ^ 2) / (4 * 1)) * (K_dom * (1 + z ^ 2 / (4 * 1))) :=
            mul_le_mul_of_nonneg_left hlin_le (by dsimp [pre1]; positivity)
        _ = (pre1 * K_dom) * ((1 + z ^ 2 / (4 * 1)) * Real.exp (-(z ^ 2) / (4 * 1))) := by ring
        _ ≤ (pre1 * K_dom) * env1 z :=
            mul_le_mul_of_nonneg_left hexp_bd (by dsimp [pre1, K_dom]; positivity)
    have hlim_int : Tendsto
        (fun n : ℕ => ∫ z : ℝ, heatKernel1 1 z *
          StreamDuhamel.D ν c tr (s₁ n) (η - Real.sqrt (ν * (s - s₁ n)) * z))
        atTop (𝓝 (∫ z : ℝ, heatKernel1 1 z * StreamDuhamel.D ν c tr s η)) := by
      refine tendsto_integral_filter_of_dominated_convergence dom
        (Eventually.of_forall fun n => ?_)
        (Eventually.of_forall fun n => Eventually.of_forall fun z => ?_)
        hdom_int (Eventually.of_forall fun z => ?_)
      · have hD_z : Continuous
            (fun z : ℝ => StreamDuhamel.D ν c tr (s₁ n) (η - Real.sqrt (ν * (s - s₁ n)) * z)) :=
          (StreamDuhamel.continuousOn_D hν hc0 tr htr).comp_continuous
            (continuous_const.prodMk (continuous_const.sub (continuous_const.mul continuous_id)))
            (fun z => ⟨(hs₁_mem n).1.le, mem_univ _⟩)
        exact (hK1_c.mul hD_z).aestronglyMeasurable
      · have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK1_nn]
        refine mul_le_mul_of_nonneg_left ?_ hK1_nn
        have hd := (hD_bd (s₁ n) ⟨(hs₁_mem n).1.le, (hs₁_mem n).2.le⟩
          (η - Real.sqrt (ν * (s - s₁ n)) * z)).2
        have hsq_le : Real.sqrt (ν * (s - s₁ n)) ≤ Real.sqrt (ν * s) :=
          Real.sqrt_le_sqrt (by nlinarith [(hs₁_mem n).1])
        have habs_le : |η - Real.sqrt (ν * (s - s₁ n)) * z| ≤
            |η| + Real.sqrt (ν * s) * |z| := by
          calc |η - Real.sqrt (ν * (s - s₁ n)) * z|
              ≤ |η| + |Real.sqrt (ν * (s - s₁ n)) * z| := abs_sub _ _
            _ = |η| + Real.sqrt (ν * (s - s₁ n)) * |z| := by
                rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
            _ ≤ |η| + Real.sqrt (ν * s) * |z| :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq_le (abs_nonneg z))
        nlinarith
      · have h1 : Tendsto (fun n : ℕ => ν * (s - s₁ n)) atTop (𝓝 (ν * (s - s))) :=
          ((tendsto_const_nhds (x := s)).sub hs₁_tendsto).const_mul ν
        rw [sub_self, mul_zero] at h1
        have hsq_lim : Tendsto (fun n : ℕ => Real.sqrt (ν * (s - s₁ n))) atTop (𝓝 0) := by
          have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
          rwa [Real.sqrt_zero] at h2
        have hpt_lim : Tendsto
            (fun n : ℕ => ((s₁ n, η - Real.sqrt (ν * (s - s₁ n)) * z) : ℝ × ℝ))
            atTop (𝓝 (s, η)) := by
          refine hs₁_tendsto.prodMk_nhds ?_
          simpa [zero_mul, sub_zero] using (tendsto_const_nhds (x := η)).sub (hsq_lim.mul_const z)
        have hD_at : ContinuousWithinAt
            (fun x : ℝ × ℝ => StreamDuhamel.D ν c tr x.1 x.2) (Ici 0 ×ˢ univ) (s, η) :=
          StreamDuhamel.continuousOn_D hν hc0 tr htr (s, η) ⟨hs.le, mem_univ η⟩
        have hD_lim : Tendsto
            (fun n : ℕ => StreamDuhamel.D ν c tr (s₁ n) (η - Real.sqrt (ν * (s - s₁ n)) * z))
            atTop (𝓝 (StreamDuhamel.D ν c tr s η)) :=
          hD_at.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            hpt_lim (Eventually.of_forall fun n => ⟨(hs₁_mem n).1.le, mem_univ _⟩))
        exact hD_lim.const_mul (heatKernel1 1 z)
    rw [integral_mul_const, PartI_T23.integral_heatKernel1_eq_one one_pos, one_mul] at hlim_int
    exact hlim_int
  -- 2. RHS limit: `∫ t in 0..s₁ n, g_int t → meanSourceDuhamel tr s η`
  obtain ⟨M0, hM0⟩ := htr.sup_bound hs.le
  set g_int : ℝ → ℝ := fun t => ∫ ξ : ℝ, StreamDuhamel.K ν s η t ξ * meanStress tr t ξ
  set H_ext : ℝ → ℝ → ℝ := fun t z =>
    heatKernel1 1 z *
      meanStress tr (min (max t 0) s) (η - Real.sqrt (ν * max (s - t) 0) * z)
  set g_ext : ℝ → ℝ := fun t => ∫ z : ℝ, H_ext t z
  have hg_eq_on_Ioo : ∀ t ∈ Ioo (0 : ℝ) s, g_int t = g_ext t := by
    intro t ht
    dsimp [g_int, g_ext, H_ext, StreamDuhamel.K]
    rw [StreamDuhamel.integral_heatKernel1_mul_eq_std (mul_pos hν (sub_pos.2 ht.2)) η]
    congr 1; funext z
    rw [max_eq_left ht.1.le, min_eq_left ht.2.le, max_eq_left (sub_pos.2 ht.2).le]
  have hK1_int : Integrable (fun z : ℝ => (M0 * M0) * heatKernel1 1 z) volume :=
    (StreamDuhamel.integrable_heatKernel1 one_pos).const_mul (M0 * M0)
  have hms_Ici := StreamDuhamel.continuousOn_meanStress_Ici hc0 tr
  have hg_ext_bd : ∀ t : ℝ, ‖g_ext t‖ ≤ M0 * M0 := by
    intro t
    have hcl_mem : min (max t 0) s ∈ Icc (0 : ℝ) s :=
      ⟨le_min (le_max_right t 0) hs.le, min_le_right _ _⟩
    calc ‖∫ z : ℝ, H_ext t z‖
        ≤ ∫ z : ℝ, (M0 * M0) * heatKernel1 1 z := by
          refine norm_integral_le_of_norm_le hK1_int (Eventually.of_forall fun z => ?_)
          have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK1_nn, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (msi_meanStress_bound hc0 tr (fun w => hM0 _ hcl_mem w) _) hK1_nn
      _ = M0 * M0 := by
          rw [integral_const_mul, PartI_T23.integral_heatKernel1_eq_one one_pos, mul_one]
  have hg_ext_cont : Continuous g_ext := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hH_cont_t : ∀ z : ℝ, Continuous (fun t : ℝ => H_ext t z) := by
      intro z
      refine continuous_const.mul (hms_Ici.comp_continuous
        (((continuous_id.max continuous_const).min continuous_const).prodMk
          (continuous_const.sub ((Real.continuous_sqrt.comp
            (continuous_const.mul ((continuous_const.sub continuous_id).max continuous_const))).mul
            continuous_const)))
        (fun t => ⟨le_min (le_max_right t 0) hs.le, mem_univ _⟩))
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => (M0 * M0) * heatKernel1 1 z)
      (Eventually.of_forall fun t => ?_)
      (Eventually.of_forall fun t => Eventually.of_forall fun z => ?_)
      hK1_int
      (Eventually.of_forall fun z => (hH_cont_t z).continuousAt.tendsto)
    · have h1 : Continuous (fun z : ℝ => H_ext t z) := by
        refine hK1_c.mul (hms_Ici.comp_continuous
          (continuous_const.prodMk (continuous_const.sub (continuous_const.mul continuous_id)))
          (fun z => ⟨le_min (le_max_right t 0) hs.le, mem_univ _⟩))
      exact h1.aestronglyMeasurable
    · have hcl_mem : min (max t 0) s ∈ Icc (0 : ℝ) s :=
        ⟨le_min (le_max_right t 0) hs.le, min_le_right _ _⟩
      have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK1_nn, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (msi_meanStress_bound hc0 tr (fun w => hM0 _ hcl_mem w) _) hK1_nn
  have hint_congr : ∀ b ∈ Icc (0 : ℝ) s,
      (∫ t in (0 : ℝ)..b, g_int t) = ∫ t in (0 : ℝ)..b, g_ext t := by
    intro b hb
    rw [intervalIntegral.integral_of_le hb.1, intervalIntegral.integral_of_le hb.1,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    exact hg_eq_on_Ioo t ⟨ht.1, lt_of_lt_of_le ht.2 hb.2⟩
  have hRHS_lim : Tendsto
      (fun n : ℕ => ∫ t in (0 : ℝ)..(s₁ n), g_int t)
      atTop (𝓝 (meanSourceDuhamel tr s η)) := by
    unfold meanSourceDuhamel
    change Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..(s₁ n), g_int t) atTop
      (𝓝 (∫ t in (0 : ℝ)..s, g_int t))
    rw [hint_congr s ⟨hs.le, le_rfl⟩]
    refine (Tendsto.congr (fun n => (hint_congr (s₁ n) ⟨(hs₁_mem n).1.le, (hs₁_mem n).2.le⟩).symm) ?_)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => (M0 * M0) * (s - s₁ n))
      (fun _ => norm_nonneg _) (fun n => ?_) ?_
    · have hsub : (∫ t in (0 : ℝ)..(s₁ n), g_ext t) - (∫ t in (0 : ℝ)..s, g_ext t) =
          -(∫ t in (s₁ n)..s, g_ext t) := by
        have h := intervalIntegral.integral_add_adjacent_intervals
          (hg_ext_cont.intervalIntegrable (μ := volume) 0 (s₁ n))
          (hg_ext_cont.intervalIntegrable (μ := volume) (s₁ n) s)
        linarith
      rw [hsub, norm_neg]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := g_ext) (a := s₁ n) (b := s) (C := M0 * M0) (fun t _ => hg_ext_bd t)
      rwa [abs_of_pos (sub_pos.2 (hs₁_mem n).2)] at h
    · simpa [sub_self, mul_zero] using
        ((tendsto_const_nhds (x := s)).sub hs₁_tendsto).const_mul (M0 * M0)
  have hRHS_lim' := hRHS_lim.congr fun n =>
    (StreamDuhamel.duhamel_at_s1 hν hc1 tr htr (hs₁_mem n).1 (hs₁_mem n).2 η).symm
  exact tendsto_nhds_unique hLHS_lim hRHS_lim'

end UnforcedLeray.Short.PartI
