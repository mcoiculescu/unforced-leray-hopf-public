import UnforcedLeray.Short.PartI.Sub.T02_2

/-!
# Part I, task `PartI:T02/PressureGaugeSmooth`: the gauge constant is `C^∞` on `[0,T]`

Source of record: `the November 2 reference manuscript`, line 447 (the gauge
constant `a(s)` is a function of `s` only, and `p' = p - a(s)` must stay `C^∞` up to `s = 0`).
The target `PressureGaugeSmooth` is defined in `Short/PartI/Sub/T02_2.lean`.

Route. Only `smooth_p` and `smooth_v` of `IsClassicalOn` are used. With
`G(s,z) = p(s,z) + v₂(s,z)²`, the gauge constant is `c⁻¹ ∫_{(-c/2,c/2]} G(s,(q,0)) dq`.

* `gs_hasDerivWithinAt`: the age-derivative of the integral, within `[0,T]`, at any point of
  `[0,T]`, is the integral of the within-derivative of the integrand. This is dominated
  convergence for the difference quotient, with a uniform bound on the derivative (compactness of
  `[0,T] × [-c/2,c/2]`) and the mean value inequality on the convex set `[0,T]`.
* `gs_contDiffOn`: induction on the order `n`, using `contDiffOn_succ_iff_derivWithin` on the
  uniquely differentiable set `[0,T]`.
* `pressureGaugeSmooth`: the target is `c⁻¹` times the integral, identified on `[0,T]` by
  `ContDiffOn.congr`.

No open-set hypothesis is used: all statements live on the closed interval `Icc 0 T`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The integrand class: `G` is `C^∞` on `[0,T] × Plane`. -/
def GsClass (T : ℝ) (G : ℝ → Plane → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane))

/-- The within-derivative in the age variable `s` of `G`. -/
def gsDeriv (T : ℝ) (G : ℝ → Plane → ℝ) (s : ℝ) (z : Plane) : ℝ :=
  fderivWithin ℝ (fun x : ℝ × Plane => G x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane))
    (s, z) ((1 : ℝ), (0 : Plane))

/-- The `q`-integral `∫_{(-c/2, c/2]} G(s,(q,0)) dq`. -/
def gsInt (c : ℝ) (G : ℝ → Plane → ℝ) (s : ℝ) : ℝ :=
  ∫ q in Ioc (-c / 2) (c / 2), G s (q, 0)

theorem gs_uniq {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

/-- The age-derivative of an integrand in the class is again in the class. -/
theorem gs_deriv_class {T : ℝ} (hT : 0 < T) {G : ℝ → Plane → ℝ} (hG : GsClass T G) :
    GsClass T (gsDeriv T G) := by
  have h1 := ((contDiffOn_infty_iff_fderivWithin (gs_uniq hT)).1 hG).2
  exact h1.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : Plane))))

/-- Continuity of a slice `q ↦ G(s,(q,0))` for `s ∈ [0,T]`. -/
theorem gs_slice_continuous {T : ℝ} {G : ℝ → Plane → ℝ} (hG : GsClass T G) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) : Continuous (fun q : ℝ => G s (q, 0)) := by
  have hc : Continuous (fun q : ℝ => (s, ((q, 0) : Plane))) := by fun_prop
  exact (ContDiffOn.continuousOn hG).comp_continuous hc (fun q => ⟨hs, mem_univ _⟩)

/-- Slice derivative: the within-`[0,T]` derivative of `t ↦ G(t,z)` at `s` is `gsDeriv`. -/
theorem gs_slice_hasDerivWithinAt {T : ℝ} {G : ℝ → Plane → ℝ} (hG : GsClass T G) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (z : Plane) :
    HasDerivWithinAt (fun t => G t z) (gsDeriv T G s z) (Icc (0 : ℝ) T) s := by
  have hdiff : DifferentiableWithinAt ℝ (fun x : ℝ × Plane => G x.1 x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) (s, z) :=
    (ContDiffOn.differentiableOn hG (by simp)) (s, z) ⟨hs, mem_univ z⟩
  have hline : HasDerivWithinAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : Plane))
      (Icc (0 : ℝ) T) s :=
    ((hasDerivAt_id' s).prodMk (hasDerivAt_const s z)).hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ => (t, z)) (Icc (0 : ℝ) T)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    fun t ht => ⟨ht, mem_univ z⟩
  exact HasFDerivWithinAt.comp_hasDerivWithinAt s hdiff.hasFDerivWithinAt hline hmaps

/-- A uniform bound on the age-derivative of the integrand over `[0,T] × [-c/2, c/2]`. -/
theorem gs_deriv_bound {c T : ℝ} (hT : 0 < T) {G : ℝ → Plane → ℝ} (hG : GsClass T G) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ q ∈ Icc (-c / 2) (c / 2),
      ‖gsDeriv T G s (q, 0)‖ ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ ({0} : Set ℝ))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_singleton)
  have hsub : Icc (0 : ℝ) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ ({0} : Set ℝ)) ⊆
      Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    Set.prod_mono subset_rfl (subset_univ _)
  have hcont : ContinuousOn (fun x : ℝ × Plane => gsDeriv T G x.1 x.2)
      (Icc (0 : ℝ) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ ({0} : Set ℝ))) :=
    (ContDiffOn.continuousOn (gs_deriv_class hT hG)).mono hsub
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨C, fun s hs q hq => hC (s, (q, 0)) ⟨hs, hq, Set.mem_singleton _⟩⟩

/-- The main analytic step: the age-derivative of `∫ G(s,(q,0)) dq` within `[0,T]`. -/
theorem gs_hasDerivWithinAt {c T : ℝ} (hc : 0 < c) (hT : 0 < T) {G : ℝ → Plane → ℝ}
    (hG : GsClass T G) {s0 : ℝ} (hs0 : s0 ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (gsInt c G) (gsInt c (gsDeriv T G) s0) (Icc (0 : ℝ) T) s0 := by
  obtain ⟨C, hC⟩ := gs_deriv_bound (c := c) hT hG
  have hLip : ∀ q ∈ Icc (-c / 2) (c / 2), ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      ‖G t (q, 0) - G s (q, 0)‖ ≤ C * ‖t - s‖ := by
    intro q hq s hs t ht
    exact (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun x => gsDeriv T G x (q, 0))
      (fun x hx => gs_slice_hasDerivWithinAt hG hx (q, 0))
      (fun x hx => hC x hx q hq) hs ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hF : Tendsto
      (fun s : ℝ => ∫ q in Ioc (-c / 2) (c / 2), (s - s0)⁻¹ • (G s (q, 0) - G s0 (q, 0)))
      (𝓝[Icc (0 : ℝ) T \ {s0}] s0) (𝓝 (gsInt c (gsDeriv T G) s0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc (-c / 2) (c / 2)))
      (F := fun s q => (s - s0)⁻¹ • (G s (q, 0) - G s0 (q, 0)))
      (f := fun q => gsDeriv T G s0 (q, 0)) (fun _ => C) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (((gs_slice_continuous hG hs.1).sub (gs_slice_continuous hG hs0)).const_smul
        ((s - s0)⁻¹ : ℝ)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      have hne : ‖s - s0‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs.2)
      rw [norm_smul, norm_inv]
      calc ‖s - s0‖⁻¹ * ‖G s (q, 0) - G s0 (q, 0)‖
          ≤ ‖s - s0‖⁻¹ * (C * ‖s - s0‖) :=
            mul_le_mul_of_nonneg_left (hLip q (Ioc_subset_Icc_self hq) s0 hs0 s hs.1)
              (inv_nonneg.2 (norm_nonneg _))
        _ = C := by field_simp
    · exact integrableOn_const (measure_Ioc_lt_top.ne)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      have hd := hasDerivWithinAt_iff_tendsto_slope.mp (gs_slice_hasDerivWithinAt hG hs0 (q, 0))
      exact Tendsto.congr (fun s => slope_def_module _ _ _) hd
  refine Tendsto.congr' ?_ hF
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hi1 : IntegrableOn (fun q : ℝ => G s (q, 0)) (Ioc (-c / 2) (c / 2)) :=
    ((gs_slice_continuous hG hs.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun q : ℝ => G s0 (q, 0)) (Ioc (-c / 2) (c / 2)) :=
    ((gs_slice_continuous hG hs0).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [slope_def_module, integral_smul, integral_sub hi1 hi2]
  rfl

/-- All orders: `s ↦ ∫ G(s,(q,0)) dq` is `C^n` on `[0,T]`, for every integrand in the class. -/
theorem gs_contDiffOn {c T : ℝ} (hc : 0 < c) (hT : 0 < T) (n : ℕ) :
    ∀ {G : ℝ → Plane → ℝ}, GsClass T G → ContDiffOn ℝ n (gsInt c G) (Icc (0 : ℝ) T) := by
  induction n with
  | zero =>
    intro G hG
    rw [Nat.cast_zero, contDiffOn_zero]
    intro s hs
    exact (gs_hasDerivWithinAt hc hT hG hs).continuousWithinAt
  | succ n ih =>
    intro G hG
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)).2 ⟨?_, ?_, ?_⟩
    · intro s hs
      exact (gs_hasDerivWithinAt hc hT hG hs).differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · refine (ih (gs_deriv_class hT hG)).congr ?_
      intro s hs
      exact (gs_hasDerivWithinAt hc hT hG hs).derivWithin (uniqueDiffOn_Icc hT s hs)

/-- **Smoothness of the gauge constant** (`PressureGaugeSmooth`, source line 447):
`s ↦ p̄(s,0) + \overline{v₂²}(s,0)` is `C^∞` on `[0,T]`. -/
theorem pressureGaugeSmooth : PressureGaugeSmooth := by
  intro ν c T v p h
  have hc : 0 < c := lt_of_lt_of_le one_pos h.one_le
  have hT : 0 < T := h.T_pos
  have hp : GsClass T p := h.classical.smooth_p
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    h.classical.smooth_v
  have hv1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2 1)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  have hv2 : GsClass T (fun s z => v s z 1 ^ 2) := hv1.pow 2
  have hsum : GsClass T (fun s z => p s z + v s z 1 ^ 2) := hp.add hv2
  refine (contDiffOn_infty.2 fun n => (gs_contDiffOn hc hT n hsum).const_smul c⁻¹).congr ?_
  intro s hs
  have hi1 : IntegrableOn (fun q : ℝ => p s (q, 0)) (Ioc (-c / 2) (c / 2)) :=
    ((gs_slice_continuous hp hs).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun q : ℝ => v s (q, 0) 1 ^ 2) (Ioc (-c / 2) (c / 2)) :=
    ((gs_slice_continuous hv2 hs).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  simp only [hmean, gsInt]
  rw [integral_add hi1 hi2, smul_add]

end UnforcedLeray.Short.PartI
