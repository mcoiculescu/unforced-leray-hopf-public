import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonD3Div
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_5
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# `NewtonInnerDiv`: the inner integral of `V_{μ,M}` is solenoidal off the old disc
(task `PartIII-b:C/srcL/7/9`)

Source of record: `the November 2 reference manuscript`, lines 4776-4800.
For `t ∈ (0,1]` and `x` with `5ν/6 < x₁² + x₂²`, differentiate under the `a`-integral
(`hasFDerivAt_integral_of_locDominated`, with the domination and measurability of
`NewtonFam.famF`), then at each `a` use the kernel identity `Σ_i ∂_i ∂_i∂_j∂_k N = 0`
(`newtonD3Div`) after the swap of the finite sums.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The directional derivative of `famF t i a` at `x`, expanded through the kernel. -/
theorem famF_fderiv_apply (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (t : ℝ) (i : Fin 3)
    (a : ℝ × ℝ) (x : Vec3) (h : sigmaM c ν χo M a = 0 ∨ x - t • embPlane a ≠ 0) (v : Vec3) :
    fderiv ℝ (NewtonFam.famF c ν χo M t i a) x v =
      ∑ j, ∑ k, sigmaM c ν χo M a j k *
        fderiv ℝ (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a) v := by
  have h1 := NewtonFam.fam_iter_eq c ν χo M t i 1 a x h
  have h2 := congrArg
    (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Vec3) ℝ => T (fun _ => v)) h1
  simpa [iteratedFDeriv_one_apply, sum_apply, smul_apply, smul_eq_mul] using h2

/-- The pointwise identity in the parameter `a`: `Σ_i ∂_i (famF t i a)(x)(e_i) = 0`. -/
theorem sum_famF_fderiv_zero (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : Vec3)
    (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) (a : ℝ × ℝ) :
    ∑ i, fderiv ℝ (NewtonFam.famF c ν χo M t i a) x (Pi.single i 1) = 0 := by
  by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
  · have hne : x - t • embPlane a ≠ 0 :=
      NewtonFam.kernel_arg_ne_zero x a t (5 * ν / 6) ht.1.le ht.2 ha hx
    have hexp : ∀ i : Fin 3, fderiv ℝ (NewtonFam.famF c ν χo M t i a) x (Pi.single i 1) =
        ∑ j, ∑ k, sigmaM c ν χo M a j k *
          fderiv ℝ (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a) (Pi.single i 1) :=
      fun i => famF_fderiv_apply c ν χo M t i a x (Or.inr hne) _
    simp only [hexp]
    calc ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, sigmaM c ν χo M a j k *
            fderiv ℝ (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a) (Pi.single i 1)
        = ∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, sigmaM c ν χo M a j k *
            fderiv ℝ (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a) (Pi.single i 1) :=
          Finset.sum_comm
      _ = ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, sigmaM c ν χo M a j k *
            fderiv ℝ (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a) (Pi.single i 1) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j : Fin 3, ∑ k : Fin 3, sigmaM c ν χo M a j k *
            ∑ i : Fin 3, fderiv ℝ (fun w : Vec3 => newtonD3 w i j k) (x - t • embPlane a)
              (Pi.single i 1) := by
          simp only [Finset.mul_sum]
      _ = 0 := by
          refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
          rw [newtonD3Div (x - t • embPlane a) hne j k, mul_zero]
  · have h0 : sigmaM c ν χo M a = 0 :=
      sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [famF_fderiv_apply c ν χo M t i a x (Or.inl h0)]
    simp [h0]

/-- **(b3)** The inner integral of `V_{μ,M}` is solenoidal off the old disc. -/
theorem newtonInnerDiv : NewtonInnerDiv := by
  intro c ν χo M hc hν hχ hM t ht x hx
  have hU : IsOpen {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := isOpen_newtonRegion ν
  -- each `a ↦ ∂ (famF t i a) x` is integrable (as a continuous linear map)
  have hint : ∀ i : Fin 3,
      Integrable (fun a : ℝ × ℝ => fderiv ℝ (NewtonFam.famF c ν χo M t i a) x) volume := by
    intro i
    have hi1 := (NewtonFam.famF_locDom c ν χo M hν hχ hc hM t ht i).integrable
      (fun n y hy => NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht i n y hy) 1 hx
    have hL := ((continuousMultilinearCurryFin1 ℝ Vec3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hi1
    refine hL.congr (Filter.Eventually.of_forall fun a => ?_)
    ext v
    simp [iteratedFDeriv_one_apply]
  -- scalar integrability of the `i`-th component
  have hsc : ∀ i : Fin 3, Integrable
      (fun a : ℝ × ℝ => fderiv ℝ (NewtonFam.famF c ν χo M t i a) x (Pi.single i 1)) volume :=
    fun i => (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).integrable_comp (hint i)
  -- differentiate under the integral sign, componentwise
  have hG : ∀ i : Fin 3, fderiv ℝ (fun z : Vec3 => ∫ a : ℝ × ℝ,
      NewtonFam.famF c ν χo M t i a z) x (Pi.single i 1) =
      ∫ a : ℝ × ℝ, fderiv ℝ (NewtonFam.famF c ν χo M t i a) x (Pi.single i 1) := by
    intro i
    have hD : HasFDerivAt (fun z : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a z)
        (∫ a : ℝ × ℝ, fderiv ℝ (NewtonFam.famF c ν χo M t i a) x) x :=
      UnforcedLeray.L09.hasFDerivAt_integral_of_locDominated (μ := (volume : Measure (ℝ × ℝ))) hU
        (Filter.Eventually.of_forall fun a => NewtonFam.famF_contDiffOn c ν χo M hν hχ t ht i a)
        (fun n y hy => NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht i n y hy)
        (NewtonFam.famF_locDom c ν χo M hν hχ hc hM t ht i) hx
    rw [hD.fderiv, ContinuousLinearMap.integral_apply (hint i)]
  change ∑ i, fderiv ℝ (fun z : Vec3 => ∫ a : ℝ × ℝ,
      NewtonFam.famF c ν χo M t i a z) x (Pi.single i 1) = 0
  rw [Finset.sum_congr rfl (fun i _ => hG i), ← integral_finsetSum _ (fun i _ => hsc i)]
  simp only [sum_famF_fderiv_zero c ν χo M hν hχ t ht x hx, integral_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
