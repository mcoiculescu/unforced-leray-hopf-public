import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3

/-!
# `PartIII-b:C/rep/8/2/3/1`: measurability of the weighted train coefficient

Source: `the November 2 reference manuscript` 5464-5465 (the weight `𝔴_m`),
2045-2051 (the train IVP). `tmMeas : TMMeas` where `TMMeas = ∀ L, Measurable (trainWeight 4 L)`.

Proof outline.
* `trainFv`, `trainFp` are continuous in `(σ, x)` (`smooth_v`, `smooth_p` on `[0,∞) × Plane`,
  composed with `σ ↦ exp σ`).
* `trainFpsi` is measurable as a pointwise limit of continuous functions: the stream is
  recovered from its `η`-derivative `∂_η ψ = -(v)¹` (from `stream`), by the fundamental theorem
  of calculus, with `ψ(s, q, M) → 0` as `M → ∞` (`stream_decay`).
* For order `j ≥ 1`, `‖iteratedFDeriv ℝ j f‖` is measurable for any `f`
  (`iteratedFDeriv_succ_eq_comp_left`, the curry isometry, `measurable_fderiv`); order `0` is
  `norm_iteratedFDeriv_zero`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A function continuous on `[0,∞) × Plane` gives a globally continuous function of the
dilation variable `σ = log s`, since `s = exp σ > 0`. -/
theorem tmM_cont_dilation {β : Type*} [TopologicalSpace β] {g : ℝ → ℝ × ℝ → β}
    (h : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => g x.1 x.2) (Ici 0 ×ˢ univ)) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => g (Real.exp z.1) z.2) :=
  h.comp_continuous (f := fun z : ℝ × (ℝ × ℝ) => (Real.exp z.1, z.2)) (by fun_prop)
    (fun z => Set.mem_prod.2 ⟨Set.mem_Ici.2 (Real.exp_pos z.1).le, Set.mem_univ _⟩)

theorem tmM_trainFv_cont (L : ReturnLevel) : Continuous (trainFv L) :=
  tmM_cont_dilation (g := fun s x => L.train.v s x) L.train.isTrain.smooth_v.continuousOn

theorem tmM_trainFp_cont (L : ReturnLevel) : Continuous (trainFp L) :=
  tmM_cont_dilation (g := fun s x => L.train.p s x) L.train.isTrain.smooth_p.continuousOn

/-- The `η`-derivative of the stream is minus the first component of the velocity. -/
theorem tmM_fst_eq (L : ReturnLevel) (σ : ℝ) (x : ℝ × ℝ) :
    -(trainFv L (σ, x)) 0 = deriv (fun y : ℝ => L.train.ψ (Real.exp σ) (x.1, y)) x.2 := by
  have hs : (0 : ℝ) ≤ Real.exp σ := (Real.exp_pos σ).le
  have e := L.train.isTrain.stream (Real.exp σ) hs x
  have h1 : trainFv L (σ, x) = L.train.v (Real.exp σ) x := rfl
  rw [h1, e]
  simp [UnforcedLeray.GaussianVortex.perpendicularGradient, UnforcedLeray.GaussianVortex.partialY]

/-- The truncated integral `∫_M^η ∂_η ψ`, a continuous function of `z = (σ, q, η)`. -/
def tmM_trunc (L : ReturnLevel) (M : ℕ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  ∫ t in (M : ℝ)..z.2.2, -(trainFv L (z.1, (z.2.1, t))) 0

theorem tmM_trunc_cont (L : ReturnLevel) (M : ℕ) : Continuous (tmM_trunc L M) := by
  have hg : Continuous (fun z : ℝ × (ℝ × ℝ) => -(trainFv L z) 0) :=
    continuous_neg.comp
      ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp (tmM_trainFv_cont L))
  have hf : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ => -(trainFv L (p.1.1, (p.1.2.1, p.2))) 0) :=
    hg.comp (f := fun p : (ℝ × (ℝ × ℝ)) × ℝ => (p.1.1, (p.1.2.1, p.2))) (by fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun z t => -(trainFv L (z.1, (z.2.1, t))) 0) (a₀ := (M : ℝ)) (μ := volume) hf
    (s := fun z : ℝ × (ℝ × ℝ) => z.2.2) (by fun_prop)

theorem tmM_trunc_eq (L : ReturnLevel) (M : ℕ) (z : ℝ × (ℝ × ℝ)) :
    tmM_trunc L M z = trainFpsi L z - L.train.ψ (Real.exp z.1) (z.2.1, (M : ℝ)) := by
  have hs : (0 : ℝ) ≤ Real.exp z.1 := (Real.exp_pos z.1).le
  have hd : ∀ t ∈ uIcc (M : ℝ) z.2.2,
      HasDerivAt (fun y : ℝ => L.train.ψ (Real.exp z.1) (z.2.1, y))
        (-(trainFv L (z.1, (z.2.1, t))) 0) t := by
    intro t _
    rw [tmM_fst_eq L z.1 (z.2.1, t)]
    have hdiff : DifferentiableAt ℝ (L.train.ψ (Real.exp z.1)) (z.2.1, t) :=
      L.train.isTrain.stream_differentiable (Real.exp z.1) hs (z.2.1, t)
    have hin : DifferentiableAt ℝ (fun y : ℝ => ((z.2.1, y) : ℝ × ℝ)) t :=
      (differentiableAt_const z.2.1).prodMk differentiableAt_id
    exact (hdiff.comp t hin).hasDerivAt
  have hcont : Continuous (fun t : ℝ => -(trainFv L (z.1, (z.2.1, t))) 0) := by
    have hg : Continuous (fun w : ℝ × (ℝ × ℝ) => -(trainFv L w) 0) :=
      continuous_neg.comp
        ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp (tmM_trainFv_cont L))
    exact hg.comp (f := fun t : ℝ => (z.1, (z.2.1, t))) (by fun_prop)
  have hint : IntervalIntegrable (fun t : ℝ => -(trainFv L (z.1, (z.2.1, t))) 0) volume
      (M : ℝ) z.2.2 := hcont.intervalIntegrable _ _
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  unfold tmM_trunc
  exact key

theorem tmM_trunc_tendsto (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    Tendsto (fun M : ℕ => tmM_trunc L M z) atTop (𝓝 (trainFpsi L z)) := by
  have hs : (0 : ℝ) ≤ Real.exp z.1 := (Real.exp_pos z.1).le
  have hdec := L.train.isTrain.stream_decay (Real.exp z.1) hs
  have hpath : Tendsto (fun M : ℕ => ((z.2.1, (M : ℝ)) : ℝ × ℝ)) atTop
      (comap (fun w : ℝ × ℝ => |w.2|) atTop) := by
    refine tendsto_comap_iff.2 ?_
    refine Tendsto.congr (fun M : ℕ => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    show (M : ℝ) = |(M : ℝ)|
    exact (abs_of_nonneg (Nat.cast_nonneg M)).symm
  have hX : Tendsto (fun M : ℕ => L.train.ψ (Real.exp z.1) (z.2.1, (M : ℝ))) atTop (𝓝 0) :=
    hdec.comp hpath
  have hlim := (tendsto_const_nhds (x := trainFpsi L z)).sub hX
  rw [sub_zero] at hlim
  exact Tendsto.congr (fun M => (tmM_trunc_eq L M z).symm) hlim

theorem tmM_trainFpsi_meas (L : ReturnLevel) : Measurable (trainFpsi L) :=
  measurable_of_tendsto_metrizable (f := fun M : ℕ => tmM_trunc L M)
    (fun M => (tmM_trunc_cont L M).measurable)
    (tendsto_pi_nhds.2 (fun z => tmM_trunc_tendsto L z))

/-- Order `n + 1` of the iterated derivative has measurable norm for any function. -/
theorem tmM_norm_succ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℝ × (ℝ × ℝ) → F) (n : ℕ) :
    Measurable fun x => ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have h : (fun x => ‖iteratedFDeriv ℝ (n + 1) f x‖)
      = fun x => ‖fderiv ℝ (iteratedFDeriv ℝ n f) x‖ := by
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact LinearIsometryEquiv.norm_map _ _
  rw [h]
  exact (measurable_fderiv (𝕜 := ℝ) (f := iteratedFDeriv ℝ n f)).norm

theorem tmM_norm_iter {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℝ × (ℝ × ℝ) → F) (hf : Measurable fun x => ‖f x‖) (j : ℕ) :
    Measurable fun x => ‖iteratedFDeriv ℝ j f x‖ := by
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hf
  | succ n => exact tmM_norm_succ f n

theorem tmMeas : TMMeas := by
  intro L
  have hφ : Measurable (fun p : ℝ × (ℝ × ℝ) => (Real.log p.1, p.2)) :=
    (Real.measurable_log.comp measurable_fst).prodMk measurable_snd
  have hV : Measurable fun x => ‖trainFv L x‖ := (tmM_trainFv_cont L).norm.measurable
  have hP : Measurable fun x => ‖trainFp L x‖ := (tmM_trainFp_cont L).norm.measurable
  have hS : Measurable fun x => ‖trainFpsi L x‖ := (tmM_trainFpsi_meas L).norm
  unfold trainWeight
  refine Measurable.mul ?_ ?_
  · fun_prop
  · refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.add (Measurable.add ?_ ?_) ?_
    · exact (tmM_norm_iter (trainFv L) hV j).comp hφ
    · exact (tmM_norm_iter (trainFp L) hP j).comp hφ
    · exact (tmM_norm_iter (trainFpsi L) hS j).comp hφ

end UnforcedLeray.Short.PartIIIb.Concrete
