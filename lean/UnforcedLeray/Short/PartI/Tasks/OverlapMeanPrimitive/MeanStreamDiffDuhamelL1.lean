import UnforcedLeray.Short.PartI.Sub.PartI_T14
import UnforcedLeray.Short.PartI.Sub.PartI_T21
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive.MeanStreamDiffDuhamelL1.Helpers
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanStreamIncrement.Helpers
import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanVelIntegralDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `MeanStreamDiffDuhamelL1` (`PartI:T14/1`)

Proves `meanStreamDiffDuhamelL1_proof : MeanStreamDiffDuhamelL1`:
for a BUC train `tr : B0140.TrainSol ν c` with `0 < ν` and `1 ≤ c`, and every `s > 0`,
`‖meanStream tr s - vortexMeanStream ν c s‖_{L¹(ℝ)} ≤ ∫⁻ r in Ioc 0 s, ‖meanStress tr r‖_{L¹(ℝ)}`.

We establish this via the 1D regularized Kato `L¹` inequality on `[-R, R]` for the difference
`D(r, η) = meanStream tr r η - vortexMeanStream ν c r η`:
* `D(0, η) = 0` (`meanStream_zero_eq_vortexMeanStream`),
* `(∂_r - ν ∂_η²) D = meanStress tr` on `(0, ∞) × ℝ`,
* `D(r, -η) = D(r, η)` is even in `η`, so `∂_η D(r, -R) = -∂_η D(r, R)`.
-/

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)

/-! ### 1. Regularized absolute value `katoPhi δ` and its derivative `katoPsi δ` -/

private noncomputable def katoPhi (δ u : ℝ) : ℝ :=
  Real.sqrt (u ^ 2 + δ ^ 2) - δ

private noncomputable def katoPsi (δ u : ℝ) : ℝ :=
  u / Real.sqrt (u ^ 2 + δ ^ 2)

private theorem kato_denom_pos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 < u ^ 2 + δ ^ 2 := by
  positivity

private theorem kato_sqrt_pos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    0 < Real.sqrt (u ^ 2 + δ ^ 2) :=
  Real.sqrt_pos.2 (kato_denom_pos hδ u)

private theorem katoPhi_zero {δ : ℝ} (hδ : 0 < δ) : katoPhi δ 0 = 0 := by
  unfold katoPhi
  rw [sq, zero_mul, zero_add, Real.sqrt_sq hδ.le, sub_self]

private theorem katoPhi_nonneg {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 ≤ katoPhi δ u := by
  unfold katoPhi
  rw [sub_nonneg]
  calc δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq hδ.le).symm
    _ ≤ Real.sqrt (u ^ 2 + δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])

private theorem abs_sub_le_katoPhi {δ : ℝ} (u : ℝ) : |u| - δ ≤ katoPhi δ u := by
  unfold katoPhi
  gcongr
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])

private theorem abs_katoPsi_le_one {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : |katoPsi δ u| ≤ 1 := by
  unfold katoPsi
  rw [abs_div, abs_of_pos (kato_sqrt_pos hδ u), div_le_iff₀ (kato_sqrt_pos hδ u), one_mul,
    ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])

private theorem hasDerivAt_katoPhi {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    HasDerivAt (katoPhi δ) (katoPsi δ u) u := by
  unfold katoPhi katoPsi
  have hquad : HasDerivAt (fun x : ℝ => x ^ 2 + δ ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (δ ^ 2)
  have hsqrt := (Real.hasDerivAt_sqrt (kato_denom_pos hδ u).ne').comp u hquad
  have hsub := hsqrt.sub_const δ
  refine hsub.congr_deriv ?_
  have hne : Real.sqrt (u ^ 2 + δ ^ 2) ≠ 0 := (kato_sqrt_pos hδ u).ne'
  field_simp [hne]

private theorem hasDerivAt_katoPsi {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    HasDerivAt (katoPsi δ)
      ((δ ^ 2 / (u ^ 2 + δ ^ 2)) * (Real.sqrt (u ^ 2 + δ ^ 2))⁻¹) u := by
  have hfun : katoPsi δ = fun x : ℝ => x * (Real.sqrt (x ^ 2 + δ ^ 2))⁻¹ := by
    funext x; unfold katoPsi; ring
  rw [hfun]
  have hquad : HasDerivAt (fun x : ℝ => x ^ 2 + δ ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (δ ^ 2)
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + δ ^ 2))
      (u / Real.sqrt (u ^ 2 + δ ^ 2)) u := by
    have h := (Real.hasDerivAt_sqrt (kato_denom_pos hδ u).ne').comp u hquad
    refine h.congr_deriv ?_
    have hne : Real.sqrt (u ^ 2 + δ ^ 2) ≠ 0 := (kato_sqrt_pos hδ u).ne'
    field_simp [hne]
  have hne : Real.sqrt (u ^ 2 + δ ^ 2) ≠ 0 := (kato_sqrt_pos hδ u).ne'
  have hinv := hsqrt.inv hne
  have hprod := (hasDerivAt_id u).mul hinv
  refine hprod.congr_deriv ?_
  dsimp only [id, Pi.inv_apply]
  have hsq : Real.sqrt (u ^ 2 + δ ^ 2) ^ 2 = u ^ 2 + δ ^ 2 :=
    Real.sq_sqrt (kato_denom_pos hδ u).le
  rw [hsq]
  have hd_ne : u ^ 2 + δ ^ 2 ≠ 0 := (kato_denom_pos hδ u).ne'
  field_simp [hne, hd_ne]
  ring

private theorem contDiff_katoPhi {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (katoPhi δ) := by
  unfold katoPhi
  have hquad : ContDiff ℝ ∞ (fun x : ℝ => x ^ 2 + δ ^ 2) :=
    (contDiff_id.pow 2).add contDiff_const
  have hsqrt : ContDiff ℝ ∞ (fun x : ℝ => Real.sqrt (x ^ 2 + δ ^ 2)) :=
    contDiff_iff_contDiffAt.2 fun x =>
      (Real.contDiffAt_sqrt (kato_denom_pos hδ x).ne').comp x hquad.contDiffAt
  exact hsqrt.sub contDiff_const

private theorem continuous_katoPsi {δ : ℝ} (hδ : 0 < δ) : Continuous (katoPsi δ) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_katoPsi hδ u).differentiableAt.continuousAt

/-! ### 2. Stream difference `streamDiff` and its regularity / PDE / symmetry -/

private noncomputable def streamDiff (ν c : ℝ) (tr : B0140.TrainSol ν c) (r η : ℝ) : ℝ :=
  meanStream tr r η - vortexMeanStream ν c r η

private theorem streamDiff_zero {ν c : ℝ} (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (η : ℝ) :
    streamDiff ν c tr 0 η = 0 := by
  unfold streamDiff
  rw [meanStream_zero_eq_vortexMeanStream hc tr η, sub_self]

private theorem continuousOn_streamDiff_Ici {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) :
    ContinuousOn (fun x : ℝ × ℝ => streamDiff ν c tr x.1 x.2) (Ici 0 ×ˢ univ) :=
  (continuousOn_meanStream_Ici hν hc tr hb).sub (contDiffOn_vortexMeanStream hν).continuousOn

private theorem contDiffOn_streamDiff_Ioi {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => streamDiff ν c tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
  (trainMeanEquations_proof ν c hν hc tr hb).1.sub
    ((contDiffOn_vortexMeanStream hν).mono (prod_mono Ioi_subset_Ici_self Subset.rfl))

private theorem streamDiff_even {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (η : ℝ) :
    streamDiff ν c tr r (-η) = streamDiff ν c tr r η := by
  unfold streamDiff
  rw [PartI_T21.train_meanStream_even hc tr r hr η]
  unfold vortexMeanStream heatKernel1
  rw [neg_sq]

private theorem hasDerivAt_vortexMeanStream_eta {ν c r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (η : ℝ) :
    HasDerivAt (vortexMeanStream ν c r) (deriv (vortexMeanStream ν c r) η) η := by
  have ha : 0 < width ν r := by unfold width; nlinarith
  have h : HasDerivAt (vortexMeanStream ν c r)
      (-(8 * Real.pi * c⁻¹) * (-(η / (2 * width ν r)) * heatKernel1 (width ν r) η)) η := by
    unfold vortexMeanStream
    exact (hasDerivAt_heatKernel1_eta ha η).const_mul (-(8 * Real.pi * c⁻¹))
  exact h.congr_deriv h.deriv.symm

private theorem hasDerivAt_streamDiff_eta {ν c : ℝ} (hν : 0 < ν) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (η : ℝ) :
    HasDerivAt (streamDiff ν c tr r)
      (-meanVel1 tr r η - deriv (vortexMeanStream ν c r) η) η :=
  (bucVel_S_deriv tr hr η).sub (hasDerivAt_vortexMeanStream_eta hν hr η)

private theorem deriv_streamDiff_eta {ν c : ℝ} (hν : 0 < ν) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (η : ℝ) :
    deriv (streamDiff ν c tr r) η = -meanVel1 tr r η - deriv (vortexMeanStream ν c r) η :=
  (hasDerivAt_streamDiff_eta hν tr hr η).deriv

private theorem deriv_streamDiff_neg {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (R : ℝ) :
    deriv (streamDiff ν c tr r) (-R) = -deriv (streamDiff ν c tr r) R := by
  have hd_neg : HasDerivAt (streamDiff ν c tr r) (deriv (streamDiff ν c tr r) (-R)) (-R) :=
    (hasDerivAt_streamDiff_eta hν tr hr (-R)).congr_deriv
      (deriv_streamDiff_eta hν tr hr (-R)).symm
  have hcomp : HasDerivAt (fun x : ℝ => streamDiff ν c tr r (-x))
      (deriv (streamDiff ν c tr r) (-R) * (-1)) R :=
    hd_neg.comp R (hasDerivAt_neg R)
  have heven : (fun x : ℝ => streamDiff ν c tr r (-x)) = streamDiff ν c tr r := by
    funext x
    exact streamDiff_even hc tr hr x
  rw [heven] at hcomp
  linarith [hcomp.deriv]

private theorem streamDiff_pde {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    deriv (fun r' => streamDiff ν c tr r' η) r =
      ν * deriv (deriv (streamDiff ν c tr r)) η + meanStress tr r η := by
  have hmean := trainMeanEquations_proof ν c hν hc tr hb
  have hS_smooth := hmean.1
  have hV_smooth := (contDiffOn_vortexMeanStream (ν := ν) (c := c) hν).mono
    (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem : ((r, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ η⟩
  have hpath : HasDerivAt (fun r' : ℝ => ((r', η) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r η)
  have hS_time_diff : DifferentiableAt ℝ (fun r' => meanStream tr r' η) r := by
    have hpt : DifferentiableAt ℝ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (r, η) :=
      (hS_smooth.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hpt.hasFDerivAt.comp_hasDerivAt r hpath).differentiableAt
  have hV_time_diff : DifferentiableAt ℝ (fun r' => vortexMeanStream ν c r' η) r := by
    have hpt : DifferentiableAt ℝ (fun x : ℝ × ℝ => vortexMeanStream ν c x.1 x.2) (r, η) :=
      (hV_smooth.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hpt.hasFDerivAt.comp_hasDerivAt r hpath).differentiableAt
  have hdt : deriv (fun r' => streamDiff ν c tr r' η) r =
      deriv (fun r' => meanStream tr r' η) r - deriv (fun r' => vortexMeanStream ν c r' η) r :=
    deriv_sub hS_time_diff hV_time_diff
  have hS_slice : ContDiff ℝ ∞ (meanStream tr r) := t01_contDiff_slice hS_smooth hr
  have hV_slice : ContDiff ℝ ∞ (vortexMeanStream ν c r) := t01_contDiff_slice hV_smooth hr
  have hd1 : deriv (streamDiff ν c tr r) =
      fun e => deriv (meanStream tr r) e - deriv (vortexMeanStream ν c r) e := by
    funext e
    exact deriv_sub (hS_slice.differentiable (by simp) e) (hV_slice.differentiable (by simp) e)
  have hd2 : deriv (deriv (streamDiff ν c tr r)) η =
      deriv (deriv (meanStream tr r)) η - deriv (deriv (vortexMeanStream ν c r)) η := by
    rw [hd1]
    have hdS : ContDiff ℝ ∞ (deriv (meanStream tr r)) := hS_slice.deriv'
    have hdV : ContDiff ℝ ∞ (deriv (vortexMeanStream ν c r)) := hV_slice.deriv'
    exact deriv_sub (hdS.differentiable (by simp) η) (hdV.differentiable (by simp) η)
  have hmean_pde := (hmean.2 r hr η).1
  have hvort_pde := vortexMeanStream_heat_eq (c := c) hν hr.le η
  rw [hdt, hd2]
  linarith

/-! ### 3. Differentiation under the integral on `[a, b]` and the Kato inequality on `[-R, R]` -/

private theorem integral_hasDerivAt_interval {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ)) {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ t in a..b, f (r, t))
      (∫ t in a..b, deriv (fun r => f (r, t)) s) s := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hD : ContinuousOn (fun x : ℝ × ℝ => fderiv ℝ f x (1, 0)) (Ioi 0 ×ˢ univ) :=
    (hf.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply continuousOn_const
  have hK : IsCompact (Icc (s / 2) (2 * s) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  have hKsub : Icc (s / 2) (2 * s) ×ˢ uIcc a b ⊆ Ioi 0 ×ˢ univ := by
    intro x hx
    exact ⟨lt_of_lt_of_le (by linarith) hx.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hD.mono hKsub)
  have hnhds : Ioo (s / 2) (2 * s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (fun t => f (x, t)) ((volume : Measure ℝ).restrict (uIoc a b)) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact (t01_contDiff_slice hf (Set.mem_Ioi.1 hx)).continuous.aestronglyMeasurable
  have hFint : IntervalIntegrable (fun t => f (s, t)) (volume : Measure ℝ) a b :=
    (t01_contDiff_slice hf hs).continuous.intervalIntegrable _ _
  have hcontT : Continuous (fun t : ℝ => fderiv ℝ f (s, t) (1, 0)) := by
    have hpt : Continuous (fun t : ℝ => ((s, t) : ℝ × ℝ)) := continuous_const.prodMk continuous_id
    exact continuousOn_univ.1 (hD.comp hpt.continuousOn fun t _ => ⟨hs, mem_univ t⟩)
  have hbnd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc a b → ∀ x ∈ Ioo (s / 2) (2 * s),
      ‖fderiv ℝ f (x, t) (1, 0)‖ ≤ M :=
    ae_of_all _ fun t ht x hx => hM (x, t) ⟨⟨hx.1.le, hx.2.le⟩, uIoc_subset_uIcc ht⟩
  have hfst : ∀ x t : ℝ, 0 < x →
      HasDerivAt (fun r => f (r, t)) (fderiv ℝ f (x, t) (1, 0)) x := by
    intro x t hx
    have hmem : ((x, t) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hx, mem_univ t⟩
    have hdiff : DifferentiableAt ℝ f (x, t) :=
      (hf.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact hdiff.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))
  have hdiffs : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc a b → ∀ x ∈ Ioo (s / 2) (2 * s),
      HasDerivAt (fun x => f (x, t)) (fderiv ℝ f (x, t) (1, 0)) x :=
    ae_of_all _ fun t _ x hx => hfst x t (by linarith [hx.1])
  have hres := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun r t => f (r, t)) (F' := fun r t => fderiv ℝ f (r, t) (1, 0))
    (bound := fun _ => M) hnhds hmeas hFint hcontT.aestronglyMeasurable
    hbnd (continuous_const.intervalIntegrable _ _) hdiffs).2
  refine hres.congr_deriv ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact (hfst s t hs).deriv.symm

private noncomputable def katoEnergy (ν c : ℝ) (tr : B0140.TrainSol ν c) (R δ r : ℝ) : ℝ :=
  ∫ η in (-R)..R, katoPhi δ (streamDiff ν c tr r η)

private noncomputable def boundaryErr (ν c : ℝ) (tr : B0140.TrainSol ν c) (R r : ℝ) : ℝ :=
  |meanVel1 tr r R + deriv (vortexMeanStream ν c r) R|

private theorem katoEnergy_zero {ν c : ℝ} (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    katoEnergy ν c tr R δ 0 = 0 := by
  unfold katoEnergy
  simp_rw [streamDiff_zero hc tr, katoPhi_zero hδ, intervalIntegral.integral_zero]

private theorem continuousOn_katoEnergy {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (katoEnergy ν c tr R δ) (Ici 0) := by
  set D_ext : ℝ → ℝ → ℝ := fun r η => katoPhi δ (streamDiff ν c tr (max r 0) η)
  have hD_cont : Continuous (Function.uncurry D_ext) := by
    have hmap : Continuous (fun p : ℝ × ℝ => ((max p.1 0, p.2) : ℝ × ℝ)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    have hstream : Continuous (fun p : ℝ × ℝ => streamDiff ν c tr (max p.1 0) p.2) :=
      (continuousOn_streamDiff_Ici hν hc tr hb).comp_continuous hmap
        (fun p => ⟨mem_Ici.2 (le_max_right p.1 0), mem_univ _⟩)
    exact (contDiff_katoPhi hδ).continuous.comp hstream
  have hI_cont : Continuous (fun r : ℝ => ∫ η in (-R)..R, D_ext r η) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hD_cont (-R) R
  refine hI_cont.continuousOn.congr fun r hr => ?_
  have hmax : max r 0 = r := max_eq_left hr
  simp only [katoEnergy, D_ext, hmax]

private theorem hasDerivAt_katoEnergy {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) (R : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (katoEnergy ν c tr R δ)
      (∫ η in (-R)..R,
        katoPsi δ (streamDiff ν c tr r η) * deriv (fun r' => streamDiff ν c tr r' η) r) r := by
  have hf : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => katoPhi δ (streamDiff ν c tr x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    (contDiff_katoPhi hδ).comp_contDiffOn (contDiffOn_streamDiff_Ioi hν hc tr hb)
  have hI := integral_hasDerivAt_interval hf hr (-R) R
  refine hI.congr_deriv ?_
  refine intervalIntegral.integral_congr fun η _ => ?_
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem : ((r, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ η⟩
  have hD_diff : DifferentiableAt ℝ (fun r' => streamDiff ν c tr r' η) r := by
    have hpt : DifferentiableAt ℝ (fun x : ℝ × ℝ => streamDiff ν c tr x.1 x.2) (r, η) :=
      ((contDiffOn_streamDiff_Ioi hν hc tr hb).contDiffAt
        (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hpt.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r η))).differentiableAt
  exact ((hasDerivAt_katoPhi hδ (streamDiff ν c tr r η)).comp r hD_diff.hasDerivAt).deriv

private theorem continuousOn_deriv_katoEnergy {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (deriv (katoEnergy ν c tr R δ)) (Ioi 0) := by
  intro r₀ hr₀
  have hf : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => katoPhi δ (streamDiff ν c tr x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    (contDiff_katoPhi hδ).comp_contDiffOn (contDiffOn_streamDiff_Ioi hν hc tr hb)
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hfd_cont : ContinuousOn
      (fun x : ℝ × ℝ => fderiv ℝ (fun y : ℝ × ℝ => katoPhi δ (streamDiff ν c tr y.1 y.2)) x (1, 0))
      (Ioi 0 ×ˢ univ) :=
    (hf.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply continuousOn_const
  set g_ext : ℝ → ℝ → ℝ := fun r η =>
    fderiv ℝ (fun y : ℝ × ℝ => katoPhi δ (streamDiff ν c tr y.1 y.2)) (max r (r₀ / 2), η) (1, 0)
  have hg_cont : Continuous (Function.uncurry g_ext) := by
    have hmap : Continuous (fun p : ℝ × ℝ => ((max p.1 (r₀ / 2), p.2) : ℝ × ℝ)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    have hpos : 0 < r₀ / 2 := half_pos hr₀
    exact hfd_cont.comp_continuous hmap
      (fun p => ⟨mem_Ioi.2 (lt_of_lt_of_le hpos (le_max_right p.1 (r₀ / 2))), mem_univ _⟩)
  have hI_cont : Continuous (fun r : ℝ => ∫ η in (-R)..R, g_ext r η) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg_cont (-R) R
  have heq : (fun r : ℝ => ∫ η in (-R)..R, g_ext r η) =ᶠ[𝓝 r₀] deriv (katoEnergy ν c tr R δ) := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hr₀)] with r hr
    have hr_pos : 0 < r := lt_trans (half_pos hr₀) hr
    have hmax : max r (r₀ / 2) = r := max_eq_left hr.le
    unfold katoEnergy
    rw [(integral_hasDerivAt_interval hf hr_pos (-R) R).deriv]
    refine intervalIntegral.integral_congr fun η _ => ?_
    simp only [g_ext, hmax]
    have hmem : ((r, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr_pos, mem_univ η⟩
    have hdiff : DifferentiableAt ℝ
        (fun y : ℝ × ℝ => katoPhi δ (streamDiff ν c tr y.1 y.2)) (r, η) :=
      (hf.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r η))).deriv.symm
  exact (hI_cont.continuousAt.congr heq).continuousWithinAt

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

/-- Pointwise differential Kato inequality on `[-R, R]` for `r > 0`. -/
private theorem deriv_katoEnergy_le {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {R δ r : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hr : 0 < r) :
    deriv (katoEnergy ν c tr R δ) r ≤
      2 * ν * boundaryErr ν c tr R r + ∫ η in (-R)..R, |meanStress tr r η| := by
  rw [(hasDerivAt_katoEnergy hν hc tr hb R hδ hr).deriv]
  set D_r : ℝ → ℝ := streamDiff ν c tr r
  have hD_smooth : ContDiff ℝ ∞ D_r :=
    t01_contDiff_slice (contDiffOn_streamDiff_Ioi hν hc tr hb) hr
  have hD_diff : Differentiable ℝ D_r := hD_smooth.differentiable (by simp)
  have hdD_smooth : ContDiff ℝ ∞ (deriv D_r) := hD_smooth.deriv'
  have hdD_diff : Differentiable ℝ (deriv D_r) := hdD_smooth.differentiable (by simp)
  have hddD_smooth : ContDiff ℝ ∞ (deriv (deriv D_r)) := hdD_smooth.deriv'
  have hddD_cont : Continuous (deriv (deriv D_r)) := hddD_smooth.continuous
  set flux : ℝ → ℝ := fun η => katoPsi δ (D_r η) * deriv D_r η
  set katoDiss : ℝ → ℝ := fun η =>
    ((δ ^ 2 / (D_r η ^ 2 + δ ^ 2)) * (Real.sqrt (D_r η ^ 2 + δ ^ 2))⁻¹) * (deriv D_r η) ^ 2
  set flux' : ℝ → ℝ := fun η => katoDiss η + katoPsi δ (D_r η) * deriv (deriv D_r) η
  have hflux_deriv : ∀ η : ℝ, HasDerivAt flux (flux' η) η := by
    intro η
    have hpsi := (hasDerivAt_katoPsi hδ (D_r η)).comp η (hD_diff η).hasDerivAt
    have hmul := hpsi.mul (hdD_diff η).hasDerivAt
    refine hmul.congr_deriv ?_
    dsimp only [flux', katoDiss, Function.comp_apply]
    ring
  have hflux'_cont : Continuous flux' := by
    have h1 : Continuous katoDiss := by
      refine Continuous.mul ?_ (hdD_smooth.continuous.pow 2)
      refine Continuous.mul ?_ ?_
      · exact continuous_const.div
          ((hD_smooth.continuous.pow 2).add continuous_const)
          (fun η => (kato_denom_pos hδ (D_r η)).ne')
      · exact (Real.continuous_sqrt.comp
          ((hD_smooth.continuous.pow 2).add continuous_const)).inv₀
          (fun η => (kato_sqrt_pos hδ (D_r η)).ne')
    have h2 : Continuous (fun η => katoPsi δ (D_r η) * deriv (deriv D_r) η) :=
      ((continuous_katoPsi hδ).comp hD_smooth.continuous).mul hddD_cont
    exact h1.add h2
  have hstress_cont : Continuous (meanStress tr r) :=
    continuousOn_univ.1 ((continuousOn_meanStress_Ici hc tr).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun η _ => ⟨hr.le, mem_univ η⟩))
  have hpt : ∀ η : ℝ,
      katoPsi δ (D_r η) * deriv (fun r' => streamDiff ν c tr r' η) r ≤
        ν * flux' η + |meanStress tr r η| := by
    intro η
    rw [streamDiff_pde hν hc tr hb hr η]
    have hdiss_nn : 0 ≤ katoDiss η := by
      dsimp only [katoDiss]
      have h1 : 0 ≤ δ ^ 2 / (D_r η ^ 2 + δ ^ 2) :=
        div_nonneg (sq_nonneg δ) (kato_denom_pos hδ (D_r η)).le
      have h2 : 0 ≤ (Real.sqrt (D_r η ^ 2 + δ ^ 2))⁻¹ :=
        inv_nonneg.2 (kato_sqrt_pos hδ (D_r η)).le
      exact mul_nonneg (mul_nonneg h1 h2) (sq_nonneg _)
    have hstress_le : katoPsi δ (D_r η) * meanStress tr r η ≤ |meanStress tr r η| := by
      calc katoPsi δ (D_r η) * meanStress tr r η
          ≤ |katoPsi δ (D_r η) * meanStress tr r η| := le_abs_self _
        _ = |katoPsi δ (D_r η)| * |meanStress tr r η| := abs_mul _ _
        _ ≤ 1 * |meanStress tr r η| :=
            mul_le_mul_of_nonneg_right (abs_katoPsi_le_one hδ (D_r η)) (abs_nonneg _)
        _ = |meanStress tr r η| := one_mul _
    dsimp only [flux']
    nlinarith
  have hle_R : -R ≤ R := by linarith
  have hint_lhs : IntervalIntegrable
      (fun η => katoPsi δ (D_r η) * deriv (fun r' => streamDiff ν c tr r' η) r)
      volume (-R) R := by
    have hcont : Continuous
        (fun η => katoPsi δ (D_r η) * deriv (fun r' => streamDiff ν c tr r' η) r) := by
      have h_eq : (fun η => katoPsi δ (D_r η) * deriv (fun r' => streamDiff ν c tr r' η) r) =
          fun η => katoPsi δ (D_r η) * (ν * deriv (deriv D_r) η + meanStress tr r η) := by
        funext η
        rw [streamDiff_pde hν hc tr hb hr η]
      rw [h_eq]
      exact ((continuous_katoPsi hδ).comp hD_smooth.continuous).mul
        ((continuous_const.mul hddD_cont).add hstress_cont)
    exact hcont.intervalIntegrable _ _
  have hint_rhs : IntervalIntegrable
      (fun η => ν * flux' η + |meanStress tr r η|) volume (-R) R :=
    ((continuous_const.mul hflux'_cont).add hstress_cont.abs).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hle_R hint_lhs hint_rhs (fun η _ => hpt η)
  have hsplit : (∫ η in (-R)..R, (ν * flux' η + |meanStress tr r η|)) =
      ν * (∫ η in (-R)..R, flux' η) + ∫ η in (-R)..R, |meanStress tr r η| := by
    rw [intervalIntegral.integral_add ((hflux'_cont.intervalIntegrable _ _).const_mul ν)
      (hstress_cont.abs.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  have hFTC : (∫ η in (-R)..R, flux' η) = flux R - flux (-R) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun η _ => hflux_deriv η)
      (hflux'_cont.intervalIntegrable _ _)
  have hflux_symm : flux R - flux (-R) = 2 * flux R := by
    dsimp only [flux, D_r]
    rw [streamDiff_even hc tr hr.le R, deriv_streamDiff_neg hν hc tr hr.le R]
    ring
  have hflux_le : flux R ≤ boundaryErr ν c tr R r := by
    have h1 : flux R ≤ |flux R| := le_abs_self _
    have h2 : |flux R| ≤ |deriv D_r R| := by
      dsimp only [flux]
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (abs_katoPsi_le_one hδ (D_r R)) (abs_nonneg _)
    have h3 : |deriv D_r R| = boundaryErr ν c tr R r := by
      dsimp only [D_r, boundaryErr]
      rw [deriv_streamDiff_eta hν tr hr.le R,
        show -meanVel1 tr r R - deriv (vortexMeanStream ν c r) R =
          -(meanVel1 tr r R + deriv (vortexMeanStream ν c r) R) by ring,
        abs_neg]
    linarith
  rw [hsplit, hFTC, hflux_symm] at hmono
  change ∫ η in (-R)..R, katoPsi δ (D_r η) * deriv (fun r' => streamDiff ν c tr r' η) r ≤ _
  nlinarith

/-! ### 4. Continuity of `boundaryErr` and the integrated stress on `Ici 0` -/

private theorem continuousOn_boundaryErr {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (R : ℝ) :
    ContinuousOn (boundaryErr ν c tr R) (Ici 0) := by
  set v0_ext : ℝ → Plane → ℝ := fun r z => tr.v (max r 0) z 0
  have hv_cont : Continuous (fun p : ℝ × Plane => v0_ext p.1 p.2) := by
    have hsm : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
      (PiLp.continuous_apply 2 _ 0).comp_continuousOn tr.isTrain.smooth_v.continuousOn
    have hmap : Continuous (fun p : ℝ × Plane => ((max p.1 0, p.2) : ℝ × Plane)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    exact hsm.comp_continuous hmap (fun p => ⟨mem_Ici.2 (le_max_right p.1 0), mem_univ _⟩)
  have hu_cont : Continuous (fun r : ℝ => hmean c (v0_ext r) R) := by
    have hle : -c / 2 ≤ c / 2 := by linarith
    have hfun : (fun r : ℝ => hmean c (v0_ext r) R) =
        fun r : ℝ => c⁻¹ * ∫ q in (-c / 2)..(c / 2), v0_ext r (q, R) := by
      funext r
      simp only [hmean, smul_eq_mul, intervalIntegral.integral_of_le hle]
    rw [hfun]
    have hcont_q : Continuous (Function.uncurry (fun r q : ℝ => v0_ext r (q, R))) :=
      hv_cont.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hcont_q (-c / 2) (c / 2))
  have hvel_cont : ContinuousOn (fun r : ℝ => meanVel1 tr r R) (Ici 0) := by
    refine hu_cont.continuousOn.congr fun r hr => ?_
    have hmax : max r 0 = r := max_eq_left hr
    simp only [meanVel1, v0_ext, hmax]
  have hvort_cont : ContinuousOn (fun r : ℝ => deriv (vortexMeanStream ν c r) R) (Ici 0) := by
    have hw_cont : ContinuousOn (width ν) (Ici 0) :=
      continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    have hw_pos : ∀ r ∈ Ici (0 : ℝ), 0 < width ν r := by
      intro r hr; unfold width; have : 0 ≤ r := hr; nlinarith
    have h1 : ContinuousOn
        (fun r : ℝ => (8 * Real.pi * c⁻¹) * ((Real.sqrt (4 * Real.pi * width ν r))⁻¹ *
          ((R / (2 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r))))) (Ici 0) := by
      refine continuousOn_const.mul (ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_))
      · exact (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hw_cont)).inv₀
          fun r hr => (Real.sqrt_pos.2 (mul_pos (by positivity) (hw_pos r hr))).ne'
      · exact continuousOn_const.div (continuousOn_const.mul hw_cont)
          fun r hr => mul_ne_zero two_ne_zero (hw_pos r hr).ne'
      · exact Real.continuous_exp.comp_continuousOn
          (continuousOn_const.div (continuousOn_const.mul hw_cont)
            fun r hr => mul_ne_zero (by norm_num) (hw_pos r hr).ne')
    refine h1.congr fun r hr => ?_
    unfold vortexMeanStream
    rw [((hasDerivAt_heatKernel1_eta (hw_pos r hr) R).const_mul (-(8 * Real.pi * c⁻¹))).deriv]
    unfold heatKernel1
    ring
  exact (hvel_cont.add hvort_cont).abs

private theorem continuousOn_stressIntegral_Ici {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (R : ℝ) :
    ContinuousOn (fun r : ℝ => ∫ η in (-R)..R, |meanStress tr r η|) (Ici 0) := by
  set G_ext : ℝ → ℝ → ℝ := fun r η => |meanStress tr (max r 0) η|
  have hG_cont : Continuous (Function.uncurry G_ext) := by
    have hmap : Continuous (fun p : ℝ × ℝ => ((max p.1 0, p.2) : ℝ × ℝ)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    exact ((continuousOn_meanStress_Ici hc tr).comp_continuous hmap
      (fun p => ⟨mem_Ici.2 (le_max_right p.1 0), mem_univ _⟩)).abs
  have hI_cont : Continuous (fun r : ℝ => ∫ η in (-R)..R, G_ext r η) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG_cont (-R) R
  refine hI_cont.continuousOn.congr fun r hr => ?_
  have hmax : max r 0 = r := max_eq_left hr
  simp only [G_ext, hmax]

/-! ### 5. Time-integrated Kato inequality on `[0, s]` and passage to the `L¹` limit -/

private theorem katoEnergy_le_of_pos {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs : 0 < s) :
    katoEnergy ν c tr R δ s ≤
      2 * ν * (∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) +
        ∫ r in (0 : ℝ)..s, (∫ η in (-R)..R, |meanStress tr r η|) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hB_cont := continuousOn_boundaryErr hν hc0 tr R
  have hS_cont := continuousOn_stressIntegral_Ici hc0 tr R
  have hB_nn : ∀ r : ℝ, 0 ≤ boundaryErr ν c tr R r := fun r => abs_nonneg _
  have hS_nn : ∀ r ≥ 0, 0 ≤ ∫ η in (-R)..R, |meanStress tr r η| := fun r _ =>
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  -- Step 1: For every `s₁ ∈ Ioc 0 s`, integrate `deriv_katoEnergy_le` over `s₁..s`
  have hstep : ∀ s₁ ∈ Ioc (0 : ℝ) s,
      katoEnergy ν c tr R δ s - katoEnergy ν c tr R δ s₁ ≤
        2 * ν * (∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) +
          ∫ r in (0 : ℝ)..s, (∫ η in (-R)..R, |meanStress tr r η|) := by
    intro s₁ hs₁
    have hs₁_pos : 0 < s₁ := hs₁.1
    have hs₁_le : s₁ ≤ s := hs₁.2
    have hIcc_sub_Ioi : Icc s₁ s ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hs₁_pos hr.1
    have hIcc_sub_Ici : Icc s₁ s ⊆ Ici 0 := fun r hr => (lt_of_lt_of_le hs₁_pos hr.1).le
    have hint_lhs : IntervalIntegrable (deriv (katoEnergy ν c tr R δ)) volume s₁ s :=
      ((continuousOn_deriv_katoEnergy hν hc0 tr hb R hδ).mono hIcc_sub_Ioi).intervalIntegrable_of_Icc
        hs₁_le
    have hint_B1 : IntervalIntegrable (boundaryErr ν c tr R) volume s₁ s :=
      (hB_cont.mono hIcc_sub_Ici).intervalIntegrable_of_Icc hs₁_le
    have hint_S1 : IntervalIntegrable
        (fun r => ∫ η in (-R)..R, |meanStress tr r η|) volume s₁ s :=
      (hS_cont.mono hIcc_sub_Ici).intervalIntegrable_of_Icc hs₁_le
    have hint_rhs : IntervalIntegrable
        (fun r => 2 * ν * boundaryErr ν c tr R r + ∫ η in (-R)..R, |meanStress tr r η|)
        volume s₁ s :=
      (hint_B1.const_mul (2 * ν)).add hint_S1
    have hFTC : (∫ r in s₁..s, deriv (katoEnergy ν c tr R δ) r) =
        katoEnergy ν c tr R δ s - katoEnergy ν c tr R δ s₁ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs₁_le
        ((continuousOn_katoEnergy hν hc0 tr hb R hδ).mono hIcc_sub_Ici)
        (fun r hr =>
          have hr_pos : 0 < r := lt_of_lt_of_le hs₁_pos hr.1.le
          (hasDerivAt_katoEnergy hν hc0 tr hb R hδ hr_pos).congr_deriv
            (hasDerivAt_katoEnergy hν hc0 tr hb R hδ hr_pos).deriv.symm)
        hint_lhs
    have hmono := intervalIntegral.integral_mono_on hs₁_le hint_lhs hint_rhs
      (fun r hr => deriv_katoEnergy_le hν hc0 tr hb hR hδ (lt_of_lt_of_le hs₁_pos hr.1))
    rw [hFTC, intervalIntegral.integral_add (hint_B1.const_mul (2 * ν)) hint_S1,
      intervalIntegral.integral_const_mul] at hmono
    have hint_B0 : IntervalIntegrable (boundaryErr ν c tr R) volume 0 s :=
      (hB_cont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hs.le
    have hint_S0 : IntervalIntegrable
        (fun r => ∫ η in (-R)..R, |meanStress tr r η|) volume 0 s :=
      (hS_cont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hs.le
    have hB_mono : (∫ r in s₁..s, boundaryErr ν c tr R r) ≤
        ∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r :=
      intervalIntegral.integral_mono_interval hs₁_pos.le hs₁_le le_rfl
        (Eventually.of_forall hB_nn) hint_B0
    have hS_mono : (∫ r in s₁..s, ∫ η in (-R)..R, |meanStress tr r η|) ≤
        ∫ r in (0 : ℝ)..s, ∫ η in (-R)..R, |meanStress tr r η| := by
      rw [intervalIntegral.integral_of_le hs₁_le, intervalIntegral.integral_of_le hs.le]
      refine setIntegral_mono_set hint_S0.1
        ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => hS_nn r hr.1.le) ?_
      exact Eventually.of_forall (Ioc_subset_Ioc hs₁_pos.le le_rfl)
    nlinarith
  -- Step 2: Send `s₁ = s / (n + 1) → 0` as `n → ∞`
  have hseq_tendsto : Tendsto (fun n : ℕ => s / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa [div_eq_mul_inv] using hinv.const_mul s
  have hseq_mem : ∀ n : ℕ, s / ((n : ℝ) + 1) ∈ Ioc (0 : ℝ) s := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact ⟨div_pos hs (by positivity), div_le_self hs.le hn1⟩
  have hE_tendsto : Tendsto (fun n : ℕ => katoEnergy ν c tr R δ (s / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h0 := ((continuousOn_katoEnergy hν hc0 tr hb R hδ).continuousWithinAt
      (mem_Ici.2 le_rfl)).tendsto
    rw [katoEnergy_zero hc tr R hδ] at h0
    exact h0.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hseq_tendsto (Eventually.of_forall fun n => (hseq_mem n).1.le))
  have hdiff_tendsto :
      Tendsto (fun n : ℕ => katoEnergy ν c tr R δ s - katoEnergy ν c tr R δ (s / ((n : ℝ) + 1)))
        atTop (𝓝 (katoEnergy ν c tr R δ s - 0)) :=
    tendsto_const_nhds.sub hE_tendsto
  have hle := le_of_tendsto hdiff_tendsto (Eventually.of_forall fun n => hstep _ (hseq_mem n))
  linarith

/-- Proves `MeanStreamDiffDuhamelL1` (`PartI:T14/1`). -/
theorem meanStreamDiffDuhamelL1_proof :
    UnforcedLeray.Short.PartI.MeanStreamDiffDuhamelL1 := by
  intro ν c hν hc tr hb s hs
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  set I : ℝ≥0∞ := ∫⁻ r in Ioc 0 s, eLpNorm (meanStress tr r) 1 volume
  -- Step 1: Bound the double stress integral on `[0, s] × [-R, R]` by `I`
  have hStress_le_I : ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (∫ r in (0 : ℝ)..s, ∫ η in (-R)..R, |meanStress tr r η|) ≤ I := by
    intro R hR
    have hS_cont := continuousOn_stressIntegral_Ici hc0 tr R
    have hS_int : IntegrableOn (fun r => ∫ η in (-R)..R, |meanStress tr r η|) (Ioc 0 s) volume :=
      ((hS_cont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hS_nn : ∀ r : ℝ, 0 ≤ ∫ η in (-R)..R, |meanStress tr r η| := fun r =>
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
    rw [intervalIntegral.integral_of_le hs.le,
      ofReal_integral_eq_lintegral_ofReal hS_int (ae_of_all _ hS_nn)]
    refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
    have hr_cont : Continuous (meanStress tr r) :=
      ((continuousOn_meanStress_Ici hc0 tr).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun η _ => ⟨hr.1.le, mem_univ η⟩)) |> continuousOn_univ.1
    have hr_int : IntegrableOn (fun η => |meanStress tr r η|) (Ioc (-R) R) volume :=
      (hr_cont.abs.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [intervalIntegral.integral_of_le (by linarith),
      ofReal_integral_eq_lintegral_ofReal hr_int (ae_of_all _ fun _ => abs_nonneg _),
      eLpNorm_one_eq_lintegral_enorm]
    have heq : (∫⁻ η in Ioc (-R) R, ENNReal.ofReal |meanStress tr r η|) =
        ∫⁻ η in Ioc (-R) R, ‖meanStress tr r η‖ₑ :=
      lintegral_congr fun η => (Real.enorm_eq_ofReal_abs (meanStress tr r η)).symm
    rw [heq]
    exact setLIntegral_le_lintegral _ _
  -- Step 2: Dominated convergence `∫ r in 0..s, boundaryErr ν c tr R r → 0` as `R → ∞`
  have hB_tendsto : Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) atTop (𝓝 0) := by
    obtain ⟨M0, hM0⟩ := hb.sup_bound hs.le
    set Bd : ℝ := M0 + 8 * Real.pi * c⁻¹
    have hlim : Tendsto (fun R : ℝ => ∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) atTop
        (𝓝 (∫ _ in (0 : ℝ)..s, (0 : ℝ))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Bd)
        (Eventually.of_forall fun R => ?_)
        (Eventually.of_forall fun R => ae_of_all _ fun r hr => ?_)
        intervalIntegrable_const (ae_of_all _ fun r hr => ?_)
      · rw [uIoc_of_le hs.le]
        exact ((continuousOn_boundaryErr hν hc0 tr R).mono
          (Ioc_subset_Icc_self.trans Icc_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioc
      · rw [uIoc_of_le hs.le] at hr
        rw [Real.norm_eq_abs, abs_of_nonneg (by unfold boundaryErr; positivity)]
        have hu : |meanVel1 tr r R| ≤ M0 := by
          refine bucVel_hmean_abs_le hc0 _ R M0 fun q => ?_
          have h := PiLp.norm_apply_le (tr.v r (q, R)) 0
          rw [Real.norm_eq_abs] at h
          exact h.trans (hM0 r ⟨hr.1.le, hr.2⟩ (q, R))
        have hv := abs_deriv_vortexMeanStream_le hν hc0 hr.1.le R
        calc boundaryErr ν c tr R r
            ≤ |meanVel1 tr r R| + |deriv (vortexMeanStream ν c r) R| := abs_add_le _ _
          _ ≤ M0 + 8 * Real.pi * c⁻¹ := add_le_add hu hv
      · rw [uIoc_of_le hs.le] at hr
        have hu := (bucMeanVelDecay ν c hν hc0 tr hb r hr.1.le).1
        have hv := tendsto_deriv_vortexMeanStream_atTop (c := c) hν hr.1.le
        simpa [boundaryErr] using (hu.add hv).abs
    simpa using hlim
  -- Step 3: For every `R₀ > 0` and `δ > 0`, `ENNReal.ofReal (katoEnergy ν c tr R₀ δ s) ≤ I`
  have hkato_le_I : ∀ (R₀ δ : ℝ), 0 < R₀ → 0 < δ →
      ENNReal.ofReal (katoEnergy ν c tr R₀ δ s) ≤ I := by
    intro R₀ δ hR₀ hδ
    have hfor_R : ∀ᶠ R : ℝ in atTop,
        ENNReal.ofReal (katoEnergy ν c tr R₀ δ s) ≤
          ENNReal.ofReal (2 * ν * ∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) + I := by
      filter_upwards [eventually_ge_atTop R₀] with R hR
      have hR_pos : 0 < R := lt_of_lt_of_le hR₀ hR
      have hD_cont : Continuous (fun η => katoPhi δ (streamDiff ν c tr s η)) :=
        (contDiff_katoPhi hδ).continuous.comp
          (t01_contDiff_slice (contDiffOn_streamDiff_Ioi hν hc0 tr hb) hs).continuous
      have hmono_R : katoEnergy ν c tr R₀ δ s ≤ katoEnergy ν c tr R δ s :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Eventually.of_forall fun η => katoPhi_nonneg hδ _)
          (hD_cont.intervalIntegrable _ _)
      have h1 : katoEnergy ν c tr R₀ δ s ≤
          2 * ν * (∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) +
            ∫ r in (0 : ℝ)..s, (∫ η in (-R)..R, |meanStress tr r η|) :=
        hmono_R.trans (katoEnergy_le_of_pos hν hc tr hb hR_pos hδ hs)
      have h2 := (ENNReal.ofReal_le_ofReal h1).trans (ENNReal.ofReal_add_le)
      exact h2.trans (add_le_add le_rfl (hStress_le_I R hR_pos))
    have hrhs_tendsto : Tendsto
        (fun R : ℝ => ENNReal.ofReal (2 * ν * ∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) + I)
        atTop (𝓝 (0 + I)) := by
      have hreal : Tendsto
          (fun R : ℝ => 2 * ν * ∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r) atTop (𝓝 0) := by
        simpa [mul_zero] using hB_tendsto.const_mul (2 * ν)
      have h0 : Tendsto
          (fun R : ℝ => ENNReal.ofReal (2 * ν * ∫ r in (0 : ℝ)..s, boundaryErr ν c tr R r))
          atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hreal
      exact h0.add tendsto_const_nhds
    have hle := ge_of_tendsto hrhs_tendsto hfor_R
    simpa using hle
  -- Step 4: Send `δ = (k + 1)⁻¹ → 0` to get `∫⁻ η in Ioc (-R₀) R₀, ‖streamDiff ν c tr s η‖ₑ ≤ I`
  have hDs_cont : Continuous (streamDiff ν c tr s) :=
    (t01_contDiff_slice (contDiffOn_streamDiff_Ioi hν hc0 tr hb) hs).continuous
  have hBox_le_I : ∀ R₀ : ℝ, 0 < R₀ →
      (∫⁻ η in Ioc (-R₀) R₀, ‖streamDiff ν c tr s η‖ₑ) ≤ I := by
    intro R₀ hR₀
    have hfor_k : ∀ k : ℕ,
        ENNReal.ofReal
          ((∫ η in (-R₀)..R₀, |streamDiff ν c tr s η|) - 2 * R₀ * ((k : ℝ) + 1)⁻¹) ≤ I := by
      intro k
      set δ : ℝ := ((k : ℝ) + 1)⁻¹
      have hδ : 0 < δ := by positivity
      have hsub_le : (∫ η in (-R₀)..R₀, |streamDiff ν c tr s η|) - 2 * R₀ * δ ≤
          katoEnergy ν c tr R₀ δ s := by
        have h1 : (∫ η in (-R₀)..R₀, (|streamDiff ν c tr s η| - δ)) ≤
            ∫ η in (-R₀)..R₀, katoPhi δ (streamDiff ν c tr s η) :=
          intervalIntegral.integral_mono_on (by linarith)
            ((hDs_cont.abs.sub continuous_const).intervalIntegrable _ _)
            (((contDiff_katoPhi hδ).continuous.comp hDs_cont).intervalIntegrable _ _)
            (fun η _ => abs_sub_le_katoPhi _)
        rw [intervalIntegral.integral_sub (hDs_cont.abs.intervalIntegrable _ _)
          intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h1
        unfold katoEnergy
        linarith
      exact (ENNReal.ofReal_le_ofReal hsub_le).trans (hkato_le_I R₀ δ hR₀ hδ)
    have hinv_tendsto : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hreal_tendsto : Tendsto
        (fun k : ℕ => (∫ η in (-R₀)..R₀, |streamDiff ν c tr s η|) - 2 * R₀ * ((k : ℝ) + 1)⁻¹)
        atTop (𝓝 (∫ η in (-R₀)..R₀, |streamDiff ν c tr s η|)) := by
      simpa using tendsto_const_nhds.sub (hinv_tendsto.const_mul (2 * R₀))
    have hofReal_le : ENNReal.ofReal (∫ η in (-R₀)..R₀, |streamDiff ν c tr s η|) ≤ I :=
      le_of_tendsto (ENNReal.tendsto_ofReal hreal_tendsto) (Eventually.of_forall hfor_k)
    have hDs_int : IntegrableOn (fun η => |streamDiff ν c tr s η|) (Ioc (-R₀) R₀) volume :=
      (hDs_cont.abs.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have heq : ENNReal.ofReal (∫ η in (-R₀)..R₀, |streamDiff ν c tr s η|) =
        ∫⁻ η in Ioc (-R₀) R₀, ‖streamDiff ν c tr s η‖ₑ := by
      rw [intervalIntegral.integral_of_le (by linarith),
        ofReal_integral_eq_lintegral_ofReal hDs_int (ae_of_all _ fun _ => abs_nonneg _)]
      exact lintegral_congr fun η => (Real.enorm_eq_ofReal_abs (streamDiff ν c tr s η)).symm
    rwa [← heq]
  -- Step 5: Monotone exhaustion of `ℝ` by `S n = Ioc (-(n + 1)) (n + 1)`
  set S : ℕ → Set ℝ := fun n => Ioc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hmonoS : Monotone S := by
    intro m n hmn η hη
    have hle : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    exact ⟨by linarith [hη.1], by linarith [hη.2]⟩
  have hU : (⋃ n : ℕ, S n) = univ := by
    ext η
    simp only [mem_iUnion, mem_univ, iff_true, S, mem_Ioc]
    refine ⟨⌈|η|⌉₊, ?_, ?_⟩
    · have h1 : -|η| ≤ η := neg_abs_le η
      have h2 : |η| ≤ (⌈|η|⌉₊ : ℝ) := Nat.le_ceil |η|
      linarith
    · have h1 : η ≤ |η| := le_abs_self η
      have h2 : |η| ≤ (⌈|η|⌉₊ : ℝ) := Nat.le_ceil |η|
      linarith
  change eLpNorm (streamDiff ν c tr s) 1 volume ≤ I
  rw [eLpNorm_one_eq_lintegral_enorm, ← setLIntegral_univ, ← hU,
    setLIntegral_iUnion_of_directed _ hmonoS.directed_le]
  exact iSup_le fun n => hBox_le_I ((n : ℝ) + 1) (by positivity)

end UnforcedLeray.Short.PartI
