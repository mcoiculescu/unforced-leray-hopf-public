import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonVDivFree

/-!
# The uncut Newton field is harmonic off the old disc (source 4797-4800, 5383-5387)

For `5ν/6 < x₁²+x₂²`, `Σ_l ∂_l² (V_{p})_i (x) = 0`.  Differentiate twice under the `t`-integral
(`iteratedFDeriv_integral_eq` with the domination of `newtonFamDom`) and under the `x'`-integral
(domination of `famF`); the kernel trace vanishes (`newtonD3_trace`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Trace of the second derivative of a parametric integral. -/
theorem trace_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → Vec3 → ℝ}
    {U : Set Vec3} (hU : IsOpen U) (hsmooth : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (F a) U)
    (hmeas : ∀ (n : ℕ), ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) μ)
    (hdom : UnforcedLeray.L09.LocDominated μ F U) {x : Vec3} (hx : x ∈ U) :
    ∑ l : Fin 3, iteratedFDeriv ℝ 2 (fun y => ∫ a, F a y ∂μ) x
        ![Pi.single l 1, Pi.single l 1] =
      ∫ a, ∑ l : Fin 3, iteratedFDeriv ℝ 2 (F a) x ![Pi.single l 1, Pi.single l 1] ∂μ := by
  rw [UnforcedLeray.L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hdom 2 hx]
  have hint := hdom.integrable hmeas 2 hx
  have hA : ∀ l : Fin 3, Integrable
      (fun a => iteratedFDeriv ℝ 2 (F a) x ![Pi.single l 1, Pi.single l 1]) μ := fun l =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Vec3) ℝ
      ![Pi.single l 1, Pi.single l 1]).integrable_comp hint
  rw [integral_finsetSum _ (fun l _ => hA l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Vec3) ℝ
    ![Pi.single l 1, Pi.single l 1]).integral_comp_comm hint).symm

/-- Inner trace: the `x'`-integral of the kernel family has vanishing Hessian trace. -/
theorem famF_integral_trace (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1)
    (i : Fin 3) {x : Vec3} (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) :
    ∑ l : Fin 3, iteratedFDeriv ℝ 2
      (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y) x
        ![Pi.single l 1, Pi.single l 1] = 0 := by
  have hU : IsOpen {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := isOpen_newtonRegion ν
  rw [trace_integral (μ := (volume : Measure (ℝ × ℝ))) hU
    (Filter.Eventually.of_forall fun a => NewtonFam.famF_contDiffOn c ν χo M hν hχ t ht i a)
    (fun n y hy => NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht i n y hy)
    (NewtonFam.famF_locDom c ν χo M hν hχ hc hM t ht i) hx]
  have hz : ∀ a : ℝ × ℝ, ∑ l : Fin 3, iteratedFDeriv ℝ 2 (NewtonFam.famF c ν χo M t i a) x
      ![Pi.single l 1, Pi.single l 1] = 0 := by
    intro a
    by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
    · have hne : x - t • embPlane a ≠ 0 :=
        NewtonFam.kernel_arg_ne_zero x a t (5 * ν / 6) ht.1.le ht.2 ha hx
      have h1 := NewtonFam.fam_iter_eq c ν χo M t i 2 a x (Or.inr hne)
      have hl : ∀ l : Fin 3, iteratedFDeriv ℝ 2 (NewtonFam.famF c ν χo M t i a) x
          ![Pi.single l 1, Pi.single l 1] = ∑ j, ∑ k, sigmaM c ν χo M a j k *
            iteratedFDeriv ℝ 2 (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)
              ![Pi.single l 1, Pi.single l 1] := by
        intro l
        rw [h1]
        simp [sum_apply, smul_apply, smul_eq_mul]
      simp only [hl]
      calc ∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, sigmaM c ν χo M a j k *
            iteratedFDeriv ℝ 2 (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)
              ![Pi.single l 1, Pi.single l 1]
          = ∑ j : Fin 3, ∑ k : Fin 3, sigmaM c ν χo M a j k * ∑ l : Fin 3,
            iteratedFDeriv ℝ 2 (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)
              ![Pi.single l 1, Pi.single l 1] := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
            rw [newtonD3_trace hne i j k, mul_zero]
    · have h0 : sigmaM c ν χo M a = 0 :=
        sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)
      have h1 := NewtonFam.fam_iter_eq c ν χo M t i 2 a x (Or.inl h0)
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [h1]
      simp [h0]
  simp only [hz, integral_zero]


/-- The `t`-family is locally dominated on the region. -/
theorem newtonFam_locDom {c ν p : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hp : 0 < p) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3) :
    UnforcedLeray.L09.LocDominated (volume.restrict (Ioc (0 : ℝ) 1))
      (newtonFam c ν p χo M i) {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
  intro n y hy
  obtain ⟨s, hs, g, hg, hb⟩ := newtonFamDom c ν p χo M hc hν hp hχ hM i n y hy
  refine ⟨s, hs, g, hg, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact fun z hz => hb t ht z hz

theorem newtonFam_smooth_ae {c ν p : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hp : 0 < p) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ContDiffOn ℝ ∞ (newtonFam c ν p χo M i t) {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact newtonFamSmooth c ν p χo M hc hν hp hχ hM i t ht

/-- The `t`-integral of the Newton family is smooth on the region. -/
theorem newtonFam_integral_contDiffOn {c ν p : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c)
    (hν : 0 < ν) (hp : 0 < p) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun y : Vec3 => ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν p χo M i t y)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
  UnforcedLeray.L09.contDiffOn_integral (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (isOpen_newtonRegion ν) (newtonFam_smooth_ae hc hν hp hχ hM i)
    (fun n y hy => newtonFamMeas c ν p χo M hc hν hp hχ hM i n y hy)
    (newtonFam_locDom hc hν hp hχ hM i)

/-- **The uncut Newton field is harmonic off the old disc** (component form, source 4797-4800). -/
theorem newtonV_trace {c ν p : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hp : 0 < p) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3) {x : Vec3}
    (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) :
    ∑ l : Fin 3, iteratedFDeriv ℝ 2 (fun y : Vec3 => newtonV c ν p χo M y i) x
      ![Pi.single l 1, Pi.single l 1] = 0 := by
  have hU : IsOpen {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := isOpen_newtonRegion ν
  have hI : ContDiffAt ℝ 2 (fun y : Vec3 => ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν p χo M i t y) x :=
    ((newtonFam_integral_contDiffOn hc hν hp hχ hM i).contDiffAt (hU.mem_nhds hx)).of_le
      (by norm_cast)
  have e : (fun y : Vec3 => newtonV c ν p χo M y i) =
      (-2 : ℝ) • (fun y : Vec3 => ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν p χo M i t y) := by
    funext y
    simp [newtonV_apply]
  rw [e]
  simp only [iteratedFDeriv_const_smul_apply hI, smul_apply,
    smul_eq_mul, ← Finset.mul_sum]
  rw [trace_integral (μ := volume.restrict (Ioc (0 : ℝ) 1)) hU (newtonFam_smooth_ae hc hν hp hχ hM i)
    (fun n y hy => newtonFamMeas c ν p χo M hc hν hp hχ hM i n y hy)
    (newtonFam_locDom hc hν hp hχ hM i) hx]
  have hz : ∀ t ∈ Ioc (0 : ℝ) 1, ∑ l : Fin 3, iteratedFDeriv ℝ 2 (newtonFam c ν p χo M i t) x
      ![Pi.single l 1, Pi.single l 1] = 0 := by
    intro t ht
    have hG : ContDiffAt ℝ 2 (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y) x :=
      ((NewtonFam.famF_integral_contDiffOn c ν χo M hc hν hχ hM t ht i).contDiffAt
        (hU.mem_nhds hx)).of_le (by norm_cast)
    have e2 : newtonFam c ν p χo M i t = (t ^ (2 * p + 2)) •
        (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y) := by
      funext z
      rfl
    rw [e2]
    simp only [iteratedFDeriv_const_smul_apply hG, smul_apply,
      smul_eq_mul, ← Finset.mul_sum]
    rw [famF_integral_trace c ν χo M hc hν hχ hM t ht i hx, mul_zero]
  have hae : (fun t : ℝ => ∑ l : Fin 3, iteratedFDeriv ℝ 2 (newtonFam c ν p χo M i t) x
      ![Pi.single l 1, Pi.single l 1]) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun _ => (0 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hz t ht
  rw [integral_congr_ae hae, integral_zero, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
