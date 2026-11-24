import UnforcedLeray.Short.PartI.Sub.PartI_T03
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.ParabolicMinPrinciple
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.SechSupersolution
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.ParabolicSechBarrier

/-!
# Part I, task `PartI:T03/1`: `L^∞` vorticity bound of the train

Source of record: `the November 2 reference manuscript`, lines 276-288.

Route: for `ε > 0` the barrier `M + ε e^{Ks} cosh(η)` with `K > β + ν` dominates `σ ω` by the
parabolic minimum principle (`ParabolicMinPrinciple`), using the sech-free supersolution property
(`SechSupersolution` with amplitude `0`).  Then `ε → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- Limit step: `x ≤ M + ε C` for all `ε > 0` gives `x ≤ M` when `C ≥ 0`. -/
theorem linf_limit (x M C : ℝ) (hC : 0 ≤ C) (H : ∀ ε : ℝ, 0 < ε → x ≤ M + ε * C) : x ≤ M := by
  by_contra hcon
  have hcon' : M < x := lt_of_not_ge hcon
  have hC1 : 0 < C + 1 := by linarith
  have hε : 0 < (x - M) / (C + 1) := div_pos (by linarith) hC1
  have key : (x - M) / (C + 1) * (C + 1) = x - M := div_mul_cancel₀ _ hC1.ne'
  have h := H _ hε
  nlinarith

/-- The vorticity operator kills constants. -/
theorem linf_op_const (ν : ℝ) (b : ℝ → Plane → Vec) (r : ℝ) (w : Plane) :
    vorticityOp ν b (fun _ _ => (1:ℝ)) r w = 0 := by
  unfold vorticityOp
  simp [Cyl.partialQ, Cyl.partialEta, Train.lapS]

/-- Core minimum-principle step with the constant comparison `M + ε e^{Ks} cosh(η)`. -/
theorem linf_core (h₁ : ParabolicMinPrinciple) (h₂ : SechSupersolution)
    (ν c T β M Mw K : ℝ) (b : ℝ → Plane → Vec) (om : ℝ → Plane → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hT : 0 < T) (hβ : 0 ≤ β) (hK : β + ν < K)
    (hb : ∀ r ∈ Icc (0:ℝ) T, ∀ w : Plane, ‖b r w‖ ≤ β)
    (hcont : ContinuousOn (fun x : ℝ × Plane => om x.1 x.2) (Icc 0 T ×ˢ univ))
    (hC2 : ContDiffOn ℝ 2 (fun x : ℝ × Plane => om x.1 x.2) (Ioo 0 T ×ˢ univ))
    (hper : ∀ r ∈ Icc (0:ℝ) T, Cyl.IsPeriodic c (om r))
    (hMw : ∀ r ∈ Icc (0:ℝ) T, ∀ w : Plane, |om r w| ≤ Mw)
    (hop : ∀ r ∈ Ioo (0:ℝ) T, ∀ w : Plane, vorticityOp ν b om r w = 0)
    (hM0 : ∀ w : Plane, |om 0 w| ≤ M)
    (σ : ℝ) (hσ : |σ| ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ r ∈ Ico (0:ℝ) T, ∀ w : Plane, σ * om r w ≤ M + coshBarrier ε K 1 r w := by
  have hsig : ∀ x : ℝ, σ * x ≤ |x| := fun x => by
    calc σ * x ≤ |σ * x| := le_abs_self _
      _ = |σ| * |x| := abs_mul _ _
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hσ (abs_nonneg x)
      _ = |x| := one_mul _
  have hpb : ∀ t w, pbF 0 ε K 1 t w = coshBarrier ε K 1 t w := by
    intro t w
    simp [pbF, sechBarrier]
  have hK0 : 0 ≤ K := by linarith
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM0 0)
  have hF : ContDiff ℝ 2 (fun x : ℝ × Plane => pbF 0 ε K 1 x.1 x.2) := pbF_contDiff 0 ε K 1
  have hcosh_pos : ∀ t w, 0 < coshBarrier ε K 1 t w := by
    intro t w
    unfold coshBarrier
    exact mul_pos (mul_pos hε (Real.exp_pos _)) (Real.cosh_pos _)
  have hDcont : ContinuousOn
      (fun x : ℝ × Plane => (pbF 0 ε K 1 x.1 x.2 - (-M) * 1) - σ * om x.1 x.2)
      (Icc 0 T ×ˢ univ) :=
    ((hF.continuous.continuousOn).sub continuousOn_const).sub (continuousOn_const.mul hcont)
  have hDcd : ContDiffOn ℝ 2
      (fun x : ℝ × Plane => (pbF 0 ε K 1 x.1 x.2 - (-M) * 1) - σ * om x.1 x.2)
      (Ioo 0 T ×ˢ univ) :=
    (hF.contDiffOn.sub contDiffOn_const).sub (contDiffOn_const.mul hC2)
  have hDper : ∀ r ∈ Icc (0:ℝ) T,
      Cyl.IsPeriodic c (fun w => (pbF 0 ε K 1 r w - (-M) * 1) - σ * om r w) := by
    intro r hr
    unfold Cyl.IsPeriodic
    intro w
    have hp : om r (w.1 + c, w.2) = om r w := hper r hr w
    have hq : pbF 0 ε K 1 r (w.1 + c, w.2) = pbF 0 ε K 1 r w := rfl
    show (pbF 0 ε K 1 r (w.1 + c, w.2) - (-M) * 1) - σ * om r (w.1 + c, w.2)
        = (pbF 0 ε K 1 r w - (-M) * 1) - σ * om r w
    rw [hp, hq]
  have hD0 : ∀ w : Plane, 0 ≤ (pbF 0 ε K 1 0 w - (-M) * 1) - σ * om 0 w := by
    intro w
    rw [hpb]
    have h1 := hsig (om 0 w)
    have h3 := hM0 w
    have h4 := hcosh_pos 0 w
    linarith
  obtain ⟨R, hR0, hRM⟩ := pb_exists_R 1 ε Mw one_pos hε
  have hDR : ∀ r ∈ Icc (0:ℝ) T, ∀ w : Plane, R ≤ |w.2| →
      0 ≤ (pbF 0 ε K 1 r w - (-M) * 1) - σ * om r w := by
    intro r hr w hRw
    have hcosh_le : Real.cosh (1 * R) ≤ Real.cosh (1 * w.2) := by
      rw [Real.cosh_le_cosh, one_mul, one_mul, abs_of_nonneg hR0]
      exact hRw
    have hexp1 : 1 ≤ Real.exp (K * r) := Real.one_le_exp (mul_nonneg hK0 hr.1)
    have hΦ : Mw ≤ coshBarrier ε K 1 r w := by
      have h1 : ε * Real.cosh (1 * R) ≤ ε * Real.cosh (1 * w.2) :=
        mul_le_mul_of_nonneg_left hcosh_le hε.le
      have h2 : Real.cosh (1 * w.2) ≤ Real.exp (K * r) * Real.cosh (1 * w.2) :=
        le_mul_of_one_le_left (Real.cosh_pos _).le hexp1
      have h3 : ε * Real.cosh (1 * w.2) ≤ ε * (Real.exp (K * r) * Real.cosh (1 * w.2)) :=
        mul_le_mul_of_nonneg_left h2 hε.le
      unfold coshBarrier
      rw [mul_assoc]
      linarith [hRM]
    have hsx := hsig (om r w)
    have hMr := hMw r hr w
    have hmo : σ * om r w ≤ Mw := hsx.trans hMr
    rw [hpb]
    linarith
  have hDop : ∀ r ∈ Ioo (0:ℝ) T, ∀ w : Plane,
      (fun t u => (pbF 0 ε K 1 t u - (-M) * 1) - σ * om t u) r w < 0 →
        0 < vorticityOp ν b (fun t u => (pbF 0 ε K 1 t u - (-M) * 1) - σ * om t u) r w := by
    intro r hr w _
    have hrI : r ∈ Icc (0:ℝ) T := Ioo_subset_Icc_self hr
    have hd : DifferentiableAt ℝ (fun x : ℝ × Plane => pbF 0 ε K 1 x.1 x.2) (r, w) :=
      (hF.differentiable (by norm_num)) (r, w)
    have hFt : DifferentiableAt ℝ (fun t => pbF 0 ε K 1 t w) r := pb_tslice_diffAt hd
    have hGd : DifferentiableAt ℝ (fun x : ℝ × Plane => om x.1 x.2) (r, w) :=
      (hC2.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ w⟩)
    have hGt : DifferentiableAt ℝ (fun t => om t w) r := pb_tslice_diffAt hGd
    have hFs : ContDiff ℝ 2 (fun u => pbF 0 ε K 1 r u) := pb_slice_contDiff hF r
    have hOs : ContDiff ℝ 2 (om r) := pb_slice_contDiff_om hC2 hr
    have hEt : DifferentiableAt ℝ (fun t => pbF 0 ε K 1 t w - (-M) * 1) r := hFt.sub_const _
    have hEs : ContDiff ℝ 2 (fun u => pbF 0 ε K 1 r u - (-M) * 1) := hFs.sub contDiff_const
    have hConst : ContDiff ℝ 2 (fun _ : Plane => (1:ℝ)) := contDiff_const
    have hl1 : vorticityOp ν b (fun t u => pbF 0 ε K 1 t u - (-M) * 1) r w
        = vorticityOp ν b (fun t u => pbF 0 ε K 1 t u) r w
          - (-M) * vorticityOp ν b (fun _ _ => (1:ℝ)) r w :=
      pb_vorticityOp_sub ν b (fun t u => pbF 0 ε K 1 t u) (fun _ _ => (1:ℝ)) (-M) r w
        hFs hConst hFt (differentiableAt_const _)
    have hl2 : vorticityOp ν b (fun t u => (pbF 0 ε K 1 t u - (-M) * 1) - σ * om t u) r w
        = vorticityOp ν b (fun t u => pbF 0 ε K 1 t u - (-M) * 1) r w
          - σ * vorticityOp ν b om r w :=
      pb_vorticityOp_sub ν b (fun t u => pbF 0 ε K 1 t u - (-M) * 1) om σ r w
        hEs hOs hEt hGt
    have hc1' : vorticityOp ν b (fun _ _ => (1:ℝ)) r w = 0 := linf_op_const ν b r w
    have hop' := hop r hr w
    have hpos : 0 < vorticityOp ν b (fun t u => pbF 0 ε K 1 t u) r w := by
      have h2 := h₂ ν β 0 ε K 1 b r w hν.le one_pos le_rfl hε.le (hb r hrI w)
      have hsech0 : sechBarrier 0 K 1 r w = 0 := by simp [sechBarrier]
      have hLpos : 0 < (K - β * 1 - ν * 1 ^ 2) * (sechBarrier 0 K 1 r w + coshBarrier ε K 1 r w) := by
        rw [hsech0, zero_add]
        have e : K - β * 1 - ν * 1 ^ 2 = K - β - ν := by ring
        rw [e]
        exact mul_pos (by linarith) (hcosh_pos r w)
      exact lt_of_lt_of_le hLpos h2
    have hcollapse : vorticityOp ν b (fun t u => (pbF 0 ε K 1 t u - (-M) * 1) - σ * om t u) r w
        = vorticityOp ν b (fun t u => pbF 0 ε K 1 t u) r w := by
      rw [hl2, hl1, hc1', hop']
      ring
    rw [hcollapse]
    exact hpos
  have hmin := h₁ ν c T R b (fun t u => (pbF 0 ε K 1 t u - (-M) * 1) - σ * om t u)
    hν hc hT hDcont hDcd hDper hD0 hDR hDop
  intro r hr w
  have h := hmin r hr w
  rw [hpb] at h
  linarith

/-- The `L^∞` bound of the train vorticity (source lines 276-288). -/
theorem train_vorticity_linf : TrainVorticityLinf := by
  unfold TrainVorticityLinf
  intro ν c hν hc tr htr M hM s hs z
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hT : (0:ℝ) < s + 1 := by linarith
  have cl := trainSol_isClassicalOn tr (s + 1)
  obtain ⟨hcont, hC2, ⟨Mw, hMw⟩, hper⟩ :=
    curlRegularity c (s + 1) tr.v hc0 hT cl.smooth_v cl.periodic_v (htr (s + 1) hT.le)
  obtain ⟨β0, hβ0⟩ := vfm_sup_bound (htr (s + 1) hT.le)
  have hop : ∀ r ∈ Ioo (0:ℝ) (s + 1), ∀ w : Plane,
      vorticityOp ν tr.v (fun t u => Cyl.curl (tr.v t) u) r w = 0 :=
    fun r hr w => localVorticityEquation ν c (s + 1) tr.v tr.p hν hc1 hT cl r hr w
  have hb : ∀ r ∈ Icc (0:ℝ) (s + 1), ∀ w : Plane, ‖tr.v r w‖ ≤ |β0| :=
    fun r hr w => (hβ0 r hr w).trans (le_abs_self β0)
  have hM0 : ∀ w : Plane, |Cyl.curl (tr.v 0) w| ≤ M := hM
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = |β0| + ν + 1 := ⟨_, rfl⟩
  have hK : |β0| + ν < K := by rw [hKdef]; linarith
  have key1 : ∀ σ : ℝ, |σ| ≤ 1 → ∀ ε : ℝ, 0 < ε →
      σ * Cyl.curl (tr.v s) z ≤ M + coshBarrier ε K 1 s z :=
    fun σ hσ ε hε =>
      linf_core parabolicMinPrinciple sechSupersolution ν c (s + 1) |β0| M Mw K tr.v
        (fun t u => Cyl.curl (tr.v t) u) hν hc0 hT (abs_nonneg _) hK hb hcont hC2 hper hMw
        hop hM0 σ hσ ε hε s ⟨hs, by linarith⟩ z
  have hlim : ∀ σ : ℝ, |σ| ≤ 1 → σ * Cyl.curl (tr.v s) z ≤ M := by
    intro σ hσ
    refine linf_limit _ M (Real.exp (K * s) * Real.cosh (1 * z.2)) ?_ ?_
    · exact mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
    · intro ε hε
      have e : coshBarrier ε K 1 s z = ε * (Real.exp (K * s) * Real.cosh (1 * z.2)) := by
        unfold coshBarrier
        ring
      rw [← e]
      exact key1 σ hσ ε hε
  have h1 := hlim 1 (by norm_num)
  have h2 := hlim (-1) (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end UnforcedLeray.Short.PartI
