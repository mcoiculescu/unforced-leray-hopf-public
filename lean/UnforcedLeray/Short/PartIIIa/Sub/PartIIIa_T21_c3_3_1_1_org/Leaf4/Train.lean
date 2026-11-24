import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4.Meas

/-!
# Leaf (d) of `PartIII-a:T21/c3/3/1/1`, part 3: joint measurability of the train terms
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf4Aux

lemma deriv_q_eq_fderiv {f : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hf : DifferentiableAt ℝ f z) :
    deriv (fun q : ℝ => f (q, z.2)) z.1 = fderiv ℝ f z (1, 0) := by
  have h1 : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have h2 := (hf.hasFDerivAt : HasFDerivAt f (fderiv ℝ f z) (z.1, z.2)).comp_hasDerivAt z.1 h1
  exact h2.deriv

lemma deriv_eta_eq_fderiv {f : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hf : DifferentiableAt ℝ f z) :
    deriv (fun η : ℝ => f (z.1, η)) z.2 = fderiv ℝ f z (0, 1) := by
  have h1 : HasDerivAt (fun η : ℝ => (z.1, η)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have h2 := (hf.hasFDerivAt : HasFDerivAt f (fderiv ℝ f z) (z.1, z.2)).comp_hasDerivAt z.2 h1
  exact h2.deriv

variable {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {t₁ t₂ : ℝ}

lemma continuous_trainV_rho (ht : 0 ≤ t₁) (k : Fin 2) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => tr.v (rho t₁ t₂ p.1) p.2 k) := by
  have hc : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hr0 : ∀ r, 0 ≤ rho t₁ t₂ r := fun r => ht.trans (le_max_left _ _)
  have hcomp : Continuous (fun p : ℝ × (ℝ × ℝ) => tr.v (rho t₁ t₂ p.1) p.2) :=
    hc.comp_continuous (((continuous_rho t₁ t₂).comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨hr0 p.1, mem_univ _⟩)
  exact (PiLp.continuous_apply 2 _ k).comp hcomp

lemma measurable_movingTrainV (ht : 0 ≤ t₁) (k : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movingTrainV tr (rho t₁ t₂ p.1) p.2 k) := by
  unfold movingTrainV
  have hA : Continuous (fun r : ℝ => clockA ν (rho t₁ t₂ r)) := by
    unfold clockA; have := continuous_rho t₁ t₂; fun_prop
  have hs : Continuous (fun p : ℝ × (ℝ × ℝ) => Real.sqrt (clockA ν (rho t₁ t₂ p.1))) :=
    Real.continuous_sqrt.comp (hA.comp continuous_fst)
  have hc : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hr0 : ∀ r, 0 ≤ rho t₁ t₂ r := fun r => ht.trans (le_max_left _ _)
  have hmap : Continuous (fun p : ℝ × (ℝ × ℝ) => (rho t₁ t₂ p.1,
      (Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.1,
        Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.2))) := by
    have := continuous_rho t₁ t₂
    fun_prop
  have hcomp := hc.comp_continuous hmap (fun p => ⟨hr0 p.1, mem_univ _⟩)
  have hk := (PiLp.continuous_apply 2 _ k).comp hcomp
  have hpow : Continuous (fun p : ℝ × (ℝ × ℝ) => clockA ν (rho t₁ t₂ p.1) ^ (3 / 2 : ℝ)) :=
    (hA.comp continuous_fst).rpow_const (fun _ => Or.inr (by norm_num))
  exact (hpow.mul hk).measurable

lemma differentiable_trainV_coord {s : ℝ} (hs : 0 ≤ s) (k : Fin 2) (w : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w : ℝ × ℝ => tr.v s w k) w := by
  have hd : DifferentiableAt ℝ (tr.v s) w :=
    ((UnforcedLeray.B0238.contDiff_Vc tr hs).differentiable (by simp)) w
  exact (EuclideanSpace.proj (𝕜 := ℝ) k).differentiableAt.comp w hd

lemma measurable_Ec (ht : 0 ≤ t₁) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr (rho t₁ t₂ p.1) p.2) := by
  have hr0 : ∀ r, 0 ≤ rho t₁ t₂ r := fun r => ht.trans (le_max_left _ _)
  have hm : ∀ k : Fin 2, Measurable (fun p : ℝ × (ℝ × ℝ) => tr.v (rho t₁ t₂ p.1) p.2 k) :=
    fun k => (continuous_trainV_rho tr (t₂ := t₂) ht k).measurable
  have h1 := measurable_fderiv_apply_param (fun r (w : ℝ × ℝ) => tr.v (rho t₁ t₂ r) w 1) (hm 1)
    (fun r y => differentiable_trainV_coord tr (hr0 r) 1 y) (1, 0)
  have h0 := measurable_fderiv_apply_param (fun r (w : ℝ × ℝ) => tr.v (rho t₁ t₂ r) w 0) (hm 0)
    (fun r y => differentiable_trainV_coord tr (hr0 r) 0 y) (0, 1)
  have heq : (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr (rho t₁ t₂ p.1) p.2) =
      fun p => fderiv ℝ (fun w : ℝ × ℝ => tr.v (rho t₁ t₂ p.1) w 1) p.2 (1, 0) -
        fderiv ℝ (fun w : ℝ × ℝ => tr.v (rho t₁ t₂ p.1) w 0) p.2 (0, 1) := by
    funext p
    unfold UnforcedLeray.B0238.Ec UnforcedLeray.Cyl.curl UnforcedLeray.Cyl.partialQ
      UnforcedLeray.Cyl.partialEta
    rw [deriv_q_eq_fderiv (differentiable_trainV_coord tr (hr0 p.1) 1 p.2),
      deriv_eta_eq_fderiv (differentiable_trainV_coord tr (hr0 p.1) 0 p.2)]
  rw [heq]
  exact h1.sub h0

lemma measurable_movingTrainGradE (ht : 0 ≤ t₁) (k : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movingTrainGradE tr (rho t₁ t₂ p.1) p.2 k) := by
  have hr0 : ∀ r, 0 ≤ rho t₁ t₂ r := fun r => ht.trans (le_max_left _ _)
  have hEd : ∀ r y, DifferentiableAt ℝ (fun w : ℝ × ℝ => UnforcedLeray.B0238.Ec tr (rho t₁ t₂ r) w) y := by
    intro r y
    exact (dcs_contDiff_curl (UnforcedLeray.B0238.contDiff_Vc tr (hr0 r))).differentiable (by simp) y
  have h := measurable_fderiv_apply_param
    (fun r (w : ℝ × ℝ) => UnforcedLeray.B0238.Ec tr (rho t₁ t₂ r) w) (measurable_Ec tr ht) hEd
    (B0579.dir k)
  have hA : Continuous (fun r : ℝ => clockA ν (rho t₁ t₂ r)) := by
    unfold clockA; have := continuous_rho t₁ t₂; fun_prop
  have hs : Continuous (fun p : ℝ × (ℝ × ℝ) => Real.sqrt (clockA ν (rho t₁ t₂ p.1))) :=
    Real.continuous_sqrt.comp (hA.comp continuous_fst)
  have hmap : Measurable (fun p : ℝ × (ℝ × ℝ) => (rho t₁ t₂ p.1,
      (Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.1,
        Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.2))) := by
    have := continuous_rho t₁ t₂
    exact (by fun_prop : Continuous _).measurable
  have hpow : Continuous (fun p : ℝ × (ℝ × ℝ) => clockA ν (rho t₁ t₂ p.1) ^ ((5 : ℝ) / 2)) :=
    (hA.comp continuous_fst).rpow_const (fun _ => Or.inr (by norm_num))
  unfold movingTrainGradE B0579.pd
  exact hpow.measurable.mul (h.comp (measurable_fst.prodMk (by
    have := continuous_rho t₁ t₂
    exact (by fun_prop : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      (Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.1,
        Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.2))).measurable)))

end Leaf4Aux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
