import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers

/-!
# Measurability in `t` of the Newton-family iterated derivatives (task `PartIII-b:C/srcL/6/1/1/2`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
Leaf 2 `NewtonFamMeas`: for `y` in the region `U = {5ν/6 < y₀²+y₁²}`, the map
`t ↦ D^n_y[newtonFam i t](y)` is almost everywhere strongly measurable on `(0,1]`.

Proof: `D^n_y[newtonFam i t](y) = t^{2μ+2} • ∫ D^n_y[famF t a](y) da` (`iteratedFDeriv_integral_eq`
and `iteratedFDeriv_const_smul_apply`). The `t`-map `t ↦ ∫ D^n_y[famF t a](y) da` is continuous on
`(0,1]` by dominated convergence (`continuousOn_of_dominated`), with the domination of
`NewtonFam.locDom_unif` and the pointwise continuity from the kernel formula `fam_iter_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem newtonFamMeas : NewtonFamMeas := by
  intro c ν μ χo M hc hν hμ hχ hM i n y hy
  have hU := isOpen_newtonRegion ν
  -- Step 1: the `t`-slice is `t^{2μ+2}` times an integral of the `t`-slice of `famF`.
  have hcontD : ∀ t ∈ Ioc (0 : ℝ) 1,
      iteratedFDeriv ℝ n (newtonFam c ν μ χo M i t) y
        = (t ^ (2 * μ + 2)) •
          (∫ a : ℝ × ℝ, iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y
            ∂(volume : Measure (ℝ × ℝ))) := by
    intro t ht
    have hsmooth := NewtonFam.famF_integral_contDiffOn c ν χo M hc hν hχ hM t ht i
    have hGat : ContDiffAt ℝ (n : WithTop ℕ∞)
        (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y
          ∂(volume : Measure (ℝ × ℝ))) y :=
      (hsmooth.contDiffAt (hU.mem_nhds hy)).of_le (by exact_mod_cast le_top)
    have e : newtonFam c ν μ χo M i t = (t ^ (2 * μ + 2)) •
        (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y
          ∂(volume : Measure (ℝ × ℝ))) := by
      funext z
      rfl
    have hsm : ∀ᵐ a ∂(volume : Measure (ℝ × ℝ)),
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NewtonFam.famF c ν χo M t i a)
          {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
      Filter.Eventually.of_forall fun a => NewtonFam.famF_contDiffOn c ν χo M hν hχ t ht i a
    have hmeas : ∀ (m : ℕ), ∀ x ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2},
        AEStronglyMeasurable (fun a : ℝ × ℝ => iteratedFDeriv ℝ m
          (NewtonFam.famF c ν χo M t i a) x) (volume : Measure (ℝ × ℝ)) :=
      fun m x hx => NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht i m x hx
    have hdom := NewtonFam.famF_locDom c ν χo M hν hχ hc hM t ht i
    have hI : iteratedFDeriv ℝ n (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y
          ∂(volume : Measure (ℝ × ℝ))) y
        = ∫ a : ℝ × ℝ, iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y
          ∂(volume : Measure (ℝ × ℝ)) :=
      UnforcedLeray.L09.iteratedFDeriv_integral_eq (μ := (volume : Measure (ℝ × ℝ)))
        (F := fun a => NewtonFam.famF c ν χo M t i a) hU hsm hmeas hdom n hy
    rw [e, iteratedFDeriv_const_smul_apply hGat, hI]
  -- Step 2: `t ↦ ∫ D^n_y[famF t a](y) da` is continuous on `(0,1]` by dominated convergence.
  have hcont : ContinuousOn (fun t : ℝ => ∫ a : ℝ × ℝ,
      iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y ∂(volume : Measure (ℝ × ℝ)))
      (Ioc (0 : ℝ) 1) := by
    obtain ⟨s, hs, _, C, hC⟩ := NewtonFam.locDom_unif c ν χo M hν hχ i n y hy
    refine continuousOn_of_dominated
      (F := fun t a => iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y)
      (bound := fun a : ℝ × ℝ => (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) * C)
      ?_ ?_ ((NewtonFam.sigma_norm_sum_integrable c ν χo M hc hν hχ hM).mul_const C) ?_
    · intro t ht
      exact NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht i n y hy
    · intro t ht
      exact Filter.Eventually.of_forall fun a => hC t ht a y (mem_of_mem_nhds hs)
    · refine Filter.Eventually.of_forall fun a => ?_
      by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
      · have hform : ∀ t ∈ Ioc (0 : ℝ) 1,
            iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y
              = ∑ j, ∑ k, sigmaM c ν χo M a j k •
                iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (y - t • embPlane a) :=
          fun t ht => NewtonFam.fam_iter_eq c ν χo M t i n a y
            (Or.inr (NewtonFam.kernel_arg_ne_zero y a t (5 * ν / 6) ht.1.le ht.2 ha hy))
        have hcontG : ContinuousOn (fun t : ℝ => ∑ j, ∑ k, sigmaM c ν χo M a j k •
            iteratedFDeriv ℝ n (fun w : Vec3 => newtonD3 w i j k) (y - t • embPlane a))
            (Ioc (0 : ℝ) 1) := by
          refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
          have hmap : ContinuousOn (fun t : ℝ => y - t • embPlane a) (Ioc (0 : ℝ) 1) :=
            (continuous_const.sub (continuous_id.smul continuous_const)).continuousOn
          have hk : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ n
              (fun w : Vec3 => newtonD3 w i j k) (y - t • embPlane a)) (Ioc (0 : ℝ) 1) := by
            refine (NewtonFam.ker_iter_cont n i j k).comp hmap ?_
            intro t ht
            exact NewtonFam.kernel_arg_ne_zero y a t (5 * ν / 6) ht.1.le ht.2 ha hy
          exact hk.const_smul (sigmaM c ν χo M a j k)
        exact hcontG.congr fun t ht => hform t ht
      · have h0 : sigmaM c ν χo M a = 0 :=
          sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)
        have hzero : ∀ t ∈ Ioc (0 : ℝ) 1,
            iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y = 0 := fun t _ => by
          rw [NewtonFam.fam_iter_eq c ν χo M t i n a y (Or.inl h0), h0]
          simp
        exact continuousOn_const.congr fun t ht => hzero t ht
  -- Step 3: multiply by the continuous factor `t ↦ t^{2μ+2}` and conclude.
  have hfinal : ContinuousOn (fun t : ℝ => (t ^ (2 * μ + 2)) •
      (∫ a : ℝ × ℝ, iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y
        ∂(volume : Measure (ℝ × ℝ)))) (Ioc (0 : ℝ) 1) := by
    have hp : ContinuousOn (fun t : ℝ => t ^ (2 * μ + 2)) (Ioc (0 : ℝ) 1) :=
      (continuous_id.rpow_const fun _ => Or.inr (by linarith)).continuousOn
    exact hp.smul hcont
  exact (hfinal.congr fun t ht => hcontD t ht).aestronglyMeasurable measurableSet_Ioc

end UnforcedLeray.Short.PartIIIb.Concrete
