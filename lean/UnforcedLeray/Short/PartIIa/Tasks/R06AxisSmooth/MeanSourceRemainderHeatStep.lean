import UnforcedLeray.Short.PartIIa.Sub.PartIIa_R06
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# `PartII-a:R06/4`: 1D Inhomogeneous Heat PDE Step for `meanSourceRemainder`

Source of record: `the November 2 reference manuscript`, lines 450 and 534.

Proves `meanSourceRemainderHeatStep : MeanSourceRemainderHeatStep` (`Sub/PartII-a_R06.lean`):
under the Duhamel identity `meanStream = meanDatumDuhamel + meanSourceDuhamel`, the source
Taylor remainder `meanSourceRemainder tr N` satisfies
`∂_η^b ∂_s^{ℓ+1} R_N^{(g)}(s, η) = ν ∂_η^{b+2} ∂_s^ℓ R_N^{(g)}(s, η) + ∂_η^b ∂_s^ℓ (meanStress tr)(s, η)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)
open UnforcedLeray.Short.PartI

namespace MeanSourceRemainderHeatStepAux

/-! ### 1. 1D heat-kernel identities and width derivative -/

theorem iteratedDeriv_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℝ) (k : ℕ) (x : ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) :
    iteratedDeriv k (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, iteratedDeriv k (f i) x := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    have h1 : (fun y => ∑ i ∈ insert a s, f i y) =
        (f a) + (fun y => ∑ i ∈ s, f i y) := by
      funext y
      exact Finset.sum_insert ha
    have hsum_cd : ContDiffAt ℝ ∞ (fun y => ∑ i ∈ s, f i y) x :=
      ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [h1, iteratedDeriv_add
      ((hf a (Finset.mem_insert_self a s)).of_le (by exact_mod_cast le_top))
      (hsum_cd.of_le (by exact_mod_cast le_top)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

theorem contDiff_heatKernel1 (a : ℝ) : ContDiff ℝ ∞ (heatKernel1 a) := by
  unfold heatKernel1
  fun_prop

theorem contDiff_iteratedDeriv (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∀ k : ℕ, ContDiff ℝ ∞ (iteratedDeriv k φ)
  | 0 => by rw [iteratedDeriv_zero]; exact hφ
  | k + 1 => by
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv φ hφ k)).2

theorem iteratedDeriv_comp_iteratedDeriv (φ : ℝ → ℝ) (b m : ℕ) (x : ℝ) :
    iteratedDeriv b (iteratedDeriv m φ) x = iteratedDeriv (b + m) φ x := by
  induction b generalizing x with
  | zero => simp
  | succ b ih =>
    have hfun : iteratedDeriv b (iteratedDeriv m φ) = iteratedDeriv (b + m) φ := funext ih
    rw [iteratedDeriv_succ, hfun, show b + 1 + m = (b + m) + 1 by omega, iteratedDeriv_succ]

def G1_deriv (k : ℕ) : ℝ → ℝ :=
  iteratedDeriv k (heatKernel1 1)

theorem contDiff_G1_deriv (k : ℕ) : ContDiff ℝ ∞ (G1_deriv k) :=
  contDiff_iteratedDeriv (heatKernel1 1) (contDiff_heatKernel1 1) k

theorem hasDerivAt_G1_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (G1_deriv k) (G1_deriv (k + 1) x) x := by
  have hd : DifferentiableAt ℝ (G1_deriv k) x :=
    (contDiff_G1_deriv k).differentiable (by simp) x
  have h := hd.hasDerivAt
  unfold G1_deriv at h ⊢
  rwa [← iteratedDeriv_succ] at h

theorem hasDerivAt_heatKernel1_one (x : ℝ) :
    HasDerivAt (heatKernel1 1) (-(x / 2) * heatKernel1 1 x) x := by
  unfold heatKernel1
  have h1 : HasDerivAt (fun z : ℝ => -(z ^ 2) / (4 * 1)) (-(2 * x) / 4) x := by
    have h := (((hasDerivAt_id' x).pow 2).neg).div_const (4 * 1)
    refine h.congr_deriv ?_
    ring
  refine (h1.exp.const_mul (Real.sqrt (4 * Real.pi * 1))⁻¹).congr_deriv ?_
  ring

theorem G1_deriv_one (x : ℝ) :
    G1_deriv 1 x = -(x / 2) * G1_deriv 0 x := by
  dsimp [G1_deriv]
  rw [iteratedDeriv_one, iteratedDeriv_zero, (hasDerivAt_heatKernel1_one x).deriv]

theorem G1_deriv_succ_succ (k : ℕ) (x : ℝ) :
    G1_deriv (k + 2) x =
      -(((k : ℝ) + 1) / 2) * G1_deriv k x - (x / 2) * G1_deriv (k + 1) x := by
  induction k generalizing x with
  | zero =>
    have h1 : HasDerivAt (G1_deriv 1)
        (-(1 / 2) * G1_deriv 0 x - (x / 2) * G1_deriv 1 x) x := by
      have hlin : HasDerivAt (fun z : ℝ => -(z / 2)) (-(1 / 2)) x :=
        ((hasDerivAt_id' x).div_const 2).neg
      have hprod := (hlin.mul (hasDerivAt_G1_deriv 0 x)).congr_of_eventuallyEq
        (Eventually.of_forall fun z => G1_deriv_one z)
      refine hprod.congr_deriv ?_
      ring
    have h2 := (hasDerivAt_G1_deriv 1 x).unique h1
    rw [h2]
    push_cast
    ring
  | succ k ih =>
    have h1 : HasDerivAt (G1_deriv (k + 2))
        (-(((k : ℝ) + 1 + 1) / 2) * G1_deriv (k + 1) x -
          (x / 2) * G1_deriv (k + 2) x) x := by
      have hterm1 := (hasDerivAt_G1_deriv k x).const_mul (-(((k : ℝ) + 1) / 2))
      have hlin : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) x :=
        (hasDerivAt_id' x).div_const 2
      have hterm2 := hlin.mul (hasDerivAt_G1_deriv (k + 1) x)
      have hsub := (hterm1.sub hterm2).congr_of_eventuallyEq
        (Eventually.of_forall fun z => ih z)
      refine hsub.congr_deriv ?_
      ring
    have h2 := (hasDerivAt_G1_deriv (k + 2) x).unique h1
    rw [h2]
    push_cast
    ring

theorem iteratedDeriv_heatKernel1_scale {a : ℝ} (ha : 0 < a) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (heatKernel1 a) y =
      ((Real.sqrt a)⁻¹) ^ (k + 1) * G1_deriv k ((Real.sqrt a)⁻¹ * y) := by
  have hfun : heatKernel1 a =
      fun e : ℝ => (Real.sqrt a)⁻¹ * heatKernel1 1 ((Real.sqrt a)⁻¹ * e) := by
    funext e
    simpa [mul_one] using PartI_T23.heatKernel1_nu_scale ha 1 e
  rw [hfun, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul ((contDiff_heatKernel1 1).of_le (by exact_mod_cast le_top)),
    pow_succ']
  dsimp [G1_deriv]
  ring

theorem hasDerivAt_iteratedDeriv_heatKernel1_width {a : ℝ} (ha : 0 < a) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun a' => iteratedDeriv k (heatKernel1 a') y)
      (iteratedDeriv (k + 2) (heatKernel1 a) y) a := by
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hg : HasDerivAt (fun a' : ℝ => (Real.sqrt a')⁻¹) (-((Real.sqrt a)⁻¹) ^ 3 / 2) a := by
    have h := (Real.hasDerivAt_sqrt ha.ne').inv hsq.ne'
    refine h.congr_deriv ?_
    field_simp
  have hx : HasDerivAt (fun a' : ℝ => (Real.sqrt a')⁻¹ * y)
      ((-((Real.sqrt a)⁻¹) ^ 3 / 2) * y) a := hg.mul_const y
  have hpow : HasDerivAt (fun a' : ℝ => ((Real.sqrt a')⁻¹) ^ (k + 1))
      (((k : ℝ) + 1) * ((Real.sqrt a)⁻¹) ^ k * (-((Real.sqrt a)⁻¹) ^ 3 / 2)) a := by
    refine (hg.pow (k + 1)).congr_deriv ?_
    push_cast
    ring
  have hG : HasDerivAt (fun a' : ℝ => G1_deriv k ((Real.sqrt a')⁻¹ * y))
      (G1_deriv (k + 1) ((Real.sqrt a)⁻¹ * y) * ((-((Real.sqrt a)⁻¹) ^ 3 / 2) * y)) a :=
    (hasDerivAt_G1_deriv k ((Real.sqrt a)⁻¹ * y)).comp a hx
  have hprod := hpow.mul hG
  have hev : (fun a' : ℝ => ((Real.sqrt a')⁻¹) ^ (k + 1) * G1_deriv k ((Real.sqrt a')⁻¹ * y))
      =ᶠ[𝓝 a] (fun a' : ℝ => iteratedDeriv k (heatKernel1 a') y) := by
    filter_upwards [Ioi_mem_nhds ha] with a' ha'
    exact (iteratedDeriv_heatKernel1_scale ha' k y).symm
  refine (hprod.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [iteratedDeriv_heatKernel1_scale ha (k + 2) y, G1_deriv_succ_succ k ((Real.sqrt a)⁻¹ * y)]
  ring

/-! ### 2. Mixed-derivative symmetry and 1D inhomogeneous heat PDE step -/

theorem deriv_age_eq_fderiv {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    HasDerivAt (fun r => F r e)
      (fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (1, 0)) s ∧
    deriv (fun r => F r e) s =
      fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (1, 0) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, e) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ e⟩
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) :=
    (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hline : HasDerivAt (fun r : ℝ => ((r, e) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s e)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt s hline
  exact ⟨hd, hd.deriv⟩

theorem deriv_eta_eq_fderiv {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    HasDerivAt (fun e' => F s e')
      (fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (0, 1)) e ∧
    deriv (fun e' => F s e') e =
      fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (0, 1) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, e) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ e⟩
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) :=
    (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hline : HasDerivAt (fun e' : ℝ => ((s, e') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) e :=
    (hasDerivAt_const e s).prodMk (hasDerivAt_id' e)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt e hline
  exact ⟨hd, hd.deriv⟩

theorem deriv_age_deriv_eta_comm {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    deriv (fun r => deriv (F r) e) s =
      deriv (fun e' => deriv (fun r => F r e') s) e := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, e) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ e⟩
  let Φ : ℝ × ℝ → ℝ := fun x => F x.1 x.2
  have hcd2 : ContDiffAt ℝ 2 Φ (s, e) :=
    (hF.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hfd : DifferentiableAt ℝ (fderiv ℝ Φ) (s, e) :=
    (hcd2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : IsSymmSndFDerivAt ℝ Φ (s, e) := hcd2.isSymmSndFDerivAt (by simp)
  have hF_eta : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (F x.1) x.2) (Ioi 0 ×ˢ univ) := by
    simpa [iteratedDeriv_one] using UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn F hF 1
  have hF_age : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (fun r => F r x.2) x.1) (Ioi 0 ×ˢ univ) := by
    simpa [iteratedDeriv_one] using UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 F hF 1
  rw [(deriv_age_eq_fderiv (F := fun s' e' => deriv (F s') e') hF_eta hs e).2,
    (deriv_eta_eq_fderiv (F := fun s' e' => deriv (fun r => F r e') s') hF_age hs e).2]
  have hev_eta : (fun x : ℝ × ℝ => deriv (F x.1) x.2) =ᶠ[𝓝 (s, e)]
      (fun x : ℝ × ℝ => fderiv ℝ Φ x (0, 1)) := by
    filter_upwards [hU.mem_nhds hx] with x hx' using (deriv_eta_eq_fderiv hF hx'.1 x.2).2
  have hev_age : (fun x : ℝ × ℝ => deriv (fun r => F r x.2) x.1) =ᶠ[𝓝 (s, e)]
      (fun x : ℝ × ℝ => fderiv ℝ Φ x (1, 0)) := by
    filter_upwards [hU.mem_nhds hx] with x hx' using (deriv_age_eq_fderiv hF hx'.1 x.2).2
  have hclm (v w : ℝ × ℝ) :
      fderiv ℝ (fun z => fderiv ℝ Φ z v) (s, e) w = fderiv ℝ (fderiv ℝ Φ) (s, e) w v := by
    rw [fderiv_clm_apply hfd (differentiableAt_const v)]
    simp
  rw [hev_eta.fderiv_eq, hev_age.fderiv_eq, hclm, hclm]
  exact hsym (1, 0) (0, 1)

theorem deriv_age_iteratedDeriv_eta_comm (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    deriv (fun r => iteratedDeriv k (F r) e) s =
      iteratedDeriv k (fun e' => deriv (fun r => F r e') s) e := by
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
    have hFk : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (F x.1) x.2) (Ioi 0 ×ˢ univ) :=
      UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn F hF k
    have hfun1 : (fun r => iteratedDeriv (k + 1) (F r) e) =
        fun r => deriv (iteratedDeriv k (F r)) e := by
      funext r; rw [iteratedDeriv_succ]
    have hfun2 : (fun e' => deriv (fun r => iteratedDeriv k (F r) e') s) =
        fun e' => iteratedDeriv k (fun y => deriv (fun r => F r y) s) e' :=
      funext ih
    rw [hfun1, deriv_age_deriv_eta_comm (F := fun r e' => iteratedDeriv k (F r) e') hFk hs e,
      hfun2, ← iteratedDeriv_succ]

theorem iteratedDeriv_age_iteratedDeriv_eta_comm (ℓ k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    iteratedDeriv ℓ (fun r => iteratedDeriv k (F r) e) s =
      iteratedDeriv k (fun e' => iteratedDeriv ℓ (fun r => F r e') s) e := by
  induction ℓ generalizing F s e with
  | zero => simp
  | succ ℓ ih =>
    have hF' : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (fun r => F r x.2) x.1) (Ioi 0 ×ˢ univ) := by
      simpa [iteratedDeriv_one] using UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 F hF 1
    have hev : deriv (fun r => iteratedDeriv k (F r) e) =ᶠ[𝓝 s]
        fun r => iteratedDeriv k (fun e' => deriv (fun r' => F r' e') r) e := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
        using deriv_age_iteratedDeriv_eta_comm k hF hr e
    have hfun : (fun e' => iteratedDeriv ℓ (fun r => deriv (fun r' => F r' e') r) s) =
        fun e' => iteratedDeriv (ℓ + 1) (fun r => F r e') s := by
      funext e'; rw [iteratedDeriv_succ']
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq ℓ,
      ih (F := fun r e' => deriv (fun r' => F r' e') r) hF' hs e, hfun]

theorem contDiffOn_meanSourceRemainder {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hD : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e)
    (N : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanSourceRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRemSm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.meanRemainderSmooth_of
      trainMeanEquations_proof UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν c hν hc0 tr htr N
  have hDatSm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanDatumRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    PartI_T23.contDiffOn_meanDatumRemainder hν hc1 tr N
  refine (hRemSm.sub hDatSm).congr fun x hx => ?_
  have h := PartI_T23.meanRemainder_eq_add_of_duhamel tr N (hD x.1 hx.1 x.2)
  linarith

theorem contDiffAt_age_slice_of_contDiffOn {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (e : ℝ) :
    ContDiffAt ℝ ℓ (fun r : ℝ => G r e) s := by
  have hφ : ContDiff ℝ ∞ (fun r : ℝ => ((r, e) : ℝ × ℝ)) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun r : ℝ => ((r, e) : ℝ × ℝ)) (Ioi 0) (Ioi 0 ×ˢ univ) :=
    fun _ hr => ⟨hr, trivial⟩
  have hcomp : ContDiffOn ℝ ∞
      ((fun x : ℝ × ℝ => G x.1 x.2) ∘ (fun r : ℝ => ((r, e) : ℝ × ℝ))) (Ioi 0) :=
    hG.comp hφ.contDiffOn hmaps
  exact (hcomp.contDiffAt (isOpen_Ioi.mem_nhds hs)).of_le (by exact_mod_cast le_top)

theorem contDiff_eta_slice_of_contDiffOn {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun e : ℝ => iteratedDeriv ℓ (fun r => G r e) s) := by
  have hH : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => G r x.2) x.1)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 G hG ℓ
  have hφ : ContDiff ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun e : ℝ => ((s, e) : ℝ × ℝ)) univ (Ioi 0 ×ˢ univ) :=
    fun _ _ => ⟨hs, trivial⟩
  have hcomp : ContDiffOn ℝ ∞
      ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => G r x.2) x.1) ∘ (fun e : ℝ => ((s, e) : ℝ × ℝ)))
      univ :=
    hH.comp (contDiffOn_univ.mpr hφ) hmaps
  exact contDiffOn_univ.mp hcomp

theorem deriv_age_meanSourceRemainder {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hD : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e)
    (N : ℕ) {s : ℝ} (hs : 0 < s) (e : ℝ) :
    deriv (fun r => meanSourceRemainder tr N r e) s =
      ν * iteratedDeriv 2 (meanSourceRemainder tr N s) e + meanStress tr s e := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  -- 1. `meanStream` time derivative from `trainMeanEquations_proof`
  have hMean := trainMeanEquations_proof ν c hν hc0 tr htr
  have hS_hd : HasDerivAt (fun r => meanStream tr r e)
      (ν * iteratedDeriv 2 (meanStream tr s) e + meanStress tr s e) s := by
    have hd := (deriv_age_eq_fderiv hMean.1 hs e).1
    have hpde := (hMean.2 s hs e).1
    have h2 : deriv (deriv (meanStream tr s)) e = iteratedDeriv 2 (meanStream tr s) e := by
      rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd.congr_deriv (by
      rw [← (deriv_age_eq_fderiv hMean.1 hs e).2, ← h2]
      linarith only [hpde])
  -- 2. `vortexMeanStream` time derivative
  have hV_hd : HasDerivAt (fun r => vortexMeanStream ν c r e)
      (ν * iteratedDeriv 2 (vortexMeanStream ν c s) e) s := by
    have ha : 0 < 1 + ν * s := by positivity
    have hlin : HasDerivAt (fun r : ℝ => 1 + ν * r) ν s := by
      exact (((hasDerivAt_id' s).const_mul ν).const_add 1).congr_deriv (by ring)
    have h1 := ((hasDerivAt_iteratedDeriv_heatKernel1_width ha 0 e).comp s hlin).const_mul
      (-(8 * Real.pi * c⁻¹))
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)).congr_deriv ?_
    · dsimp
      unfold vortexMeanStream width
      simp [iteratedDeriv_zero]
    · unfold vortexMeanStream width
      rw [iteratedDeriv_const_mul_field, zero_add]
      ring
  -- 3. Polynomial sum time derivative
  have hPoly_hd : HasDerivAt
      (fun r => ∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e)
      (ν * iteratedDeriv 2
        (fun y => ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y) e) s := by
    have hj_hd : ∀ j ∈ Finset.range (N + 1),
        HasDerivAt
          (fun r => meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e)
          (ν * (meanSourceCoeff tr j *
            iteratedDeriv 2 (iteratedDeriv (2 * j) (heatKernel1 (ν * s))) e)) s := by
      intro j _
      have ha : 0 < ν * s := mul_pos hν hs
      have hlin : HasDerivAt (fun r : ℝ => ν * r) ν s := by
        exact ((hasDerivAt_id' s).const_mul ν).congr_deriv (by ring)
      have h1 := ((hasDerivAt_iteratedDeriv_heatKernel1_width ha (2 * j) e).comp s hlin).const_mul
        (meanSourceCoeff tr j)
      refine h1.congr_deriv ?_
      rw [iteratedDeriv_comp_iteratedDeriv, show 2 + 2 * j = 2 * j + 2 by omega]
      ring
    refine ((HasDerivAt.sum hj_hd).congr_of_eventuallyEq
      (Eventually.of_forall fun r => by simp)).congr_deriv ?_
    rw [iteratedDeriv_finset_sum (Finset.range (N + 1)) _ 2 e fun j _ =>
      (contDiff_const.mul
        (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))).contDiffAt]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_const_mul_field]
  -- 4. Combine via `meanSourceRemainder = meanStream - vortexMeanStream - sum` on `Ioi 0`
  have hev_rem : (fun r => meanSourceRemainder tr N r e) =ᶠ[𝓝 s]
      fun r => (meanStream tr r e - vortexMeanStream ν c r e) -
        ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    unfold meanSourceRemainder
    have hd_r := hD r hr e
    rw [PartI_T23.meanDatumDuhamel_eq_vortexMeanStream hν hc1 tr hr e] at hd_r
    linarith
  have hd_comb := ((hS_hd.sub hV_hd).sub hPoly_hd).congr_of_eventuallyEq hev_rem
  rw [hd_comb.deriv]
  -- Express `iteratedDeriv 2 (meanSourceRemainder tr N s) e` as the combination of the three pieces
  have hrem_s : meanSourceRemainder tr N s =
      (meanStream tr s - vortexMeanStream ν c s) -
        (fun y => ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y) := by
    funext y
    change meanSourceRemainder tr N s y =
      (meanStream tr s y - vortexMeanStream ν c s y) -
        ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y
    unfold meanSourceRemainder
    have hd_s := hD s hs y
    rw [PartI_T23.meanDatumDuhamel_eq_vortexMeanStream hν hc1 tr hs y] at hd_s
    linarith
  have hS_cd : ContDiffAt ℝ 2 (meanStream tr s) e := by
    have h := contDiff_eta_slice_of_contDiffOn hMean.1 0 hs
    simp only [iteratedDeriv_zero] at h
    exact h.contDiffAt.of_le (by simp)
  have hV_cd : ContDiffAt ℝ 2 (vortexMeanStream ν c s) e := by
    unfold vortexMeanStream
    exact (contDiff_const.mul (contDiff_heatKernel1 _)).contDiffAt.of_le (by simp)
  have hP_cd : ContDiffAt ℝ 2
      (fun y => ∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y) e :=
    (ContDiff.sum fun j _ => contDiff_const.mul
      (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))).contDiffAt.of_le
      (by simp)
  have hSV_cd : ContDiffAt ℝ 2 (meanStream tr s - vortexMeanStream ν c s) e :=
    hS_cd.sub hV_cd
  rw [hrem_s, iteratedDeriv_sub hSV_cd hP_cd, iteratedDeriv_sub hS_cd hV_cd]
  ring

theorem slice_meanSourceRemainder_succ {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hD : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e)
    (N b ℓ : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    iteratedDeriv b (fun e => iteratedDeriv (ℓ + 1) (fun r => meanSourceRemainder tr N r e) s) η =
      ν * iteratedDeriv (b + 2)
          (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η +
        iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hSrcSm := contDiffOn_meanSourceRemainder hν hc1 tr htr hD N
  have hStrSm := PartI_T23.contDiffOn_meanStress hc0 tr
  have hSrc2Sm : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => iteratedDeriv 2 (meanSourceRemainder tr N x.1) x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn (meanSourceRemainder tr N) hSrcSm 2
  have he_eq : ∀ e : ℝ,
      iteratedDeriv (ℓ + 1) (fun r => meanSourceRemainder tr N r e) s =
        ν * iteratedDeriv 2
            (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) e +
          iteratedDeriv ℓ (fun r => meanStress tr r e) s := by
    intro e
    have hev : deriv (fun r => meanSourceRemainder tr N r e) =ᶠ[𝓝 s]
        ((fun r => ν * iteratedDeriv 2 (meanSourceRemainder tr N r) e) +
          (fun r => meanStress tr r e)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
        using deriv_age_meanSourceRemainder hν hc1 tr htr hD N hr e
    have h1_cd : ContDiffAt ℝ ℓ
        (fun r => ν * iteratedDeriv 2 (meanSourceRemainder tr N r) e) s :=
      contDiffAt_const.mul
        (contDiffAt_age_slice_of_contDiffOn
          (G := fun r e' => iteratedDeriv 2 (meanSourceRemainder tr N r) e') hSrc2Sm ℓ hs e)
    have h2_cd : ContDiffAt ℝ ℓ (fun r => meanStress tr r e) s :=
      contDiffAt_age_slice_of_contDiffOn hStrSm ℓ hs e
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq ℓ, iteratedDeriv_add h1_cd h2_cd,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_age_iteratedDeriv_eta_comm ℓ 2 hSrcSm hs e]
  have hfun : (fun e => iteratedDeriv (ℓ + 1) (fun r => meanSourceRemainder tr N r e) s) =
      ((fun e => ν * iteratedDeriv 2
          (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) e) +
        (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s)) :=
    funext he_eq
  have hA_sm : ContDiff ℝ ∞
      (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) :=
    contDiff_eta_slice_of_contDiffOn hSrcSm ℓ hs
  have hB_sm : ContDiff ℝ ∞ (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) :=
    contDiff_eta_slice_of_contDiffOn hStrSm ℓ hs
  have hA2_cd : ContDiffAt ℝ b
      (fun e => ν * iteratedDeriv 2
        (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) e) η :=
    (contDiff_const.mul (contDiff_iteratedDeriv _ hA_sm 2)).contDiffAt.of_le
      (by exact_mod_cast le_top)
  have hB_cd : ContDiffAt ℝ b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η :=
    hB_sm.contDiffAt.of_le (by exact_mod_cast le_top)
  rw [hfun, iteratedDeriv_add hA2_cd hB_cd, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_iteratedDeriv]

end MeanSourceRemainderHeatStepAux

/-- **1D inhomogeneous heat PDE step for nested slice derivatives of `meanSourceRemainder`
(`PartII-a:R06/4`)**. -/
theorem meanSourceRemainderHeatStep : MeanSourceRemainderHeatStep :=
  fun _ν _c hν hc1 tr htr hD N b ℓ _s hs η =>
    MeanSourceRemainderHeatStepAux.slice_meanSourceRemainder_succ hν hc1 tr htr hD N b ℓ hs η

end UnforcedLeray.Short.PartIIa
