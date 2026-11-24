import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_1
import UnforcedLeray.Lib.Kernels.ParamIntegral
import UnforcedLeray.Units.B0284.Contraction

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/1`: smoothness of the scalar Duhamel solution

Target: `duhamelSmooth : DuhamelSmooth` (`Sub/T18_2_4_1.lean`, SP 3427-3440 of
`the November 2 reference manuscript`). For `c, ν > 0` and a `NiceScalar c h`,
`(s, x) ↦ duhamelHeat ν h s x` is `C^∞`.

Strategy. Write `duhamelHeat` as one integral over `α = (r, z)` with the product measure
`duhSm_μ = (volume.restrict (Ioi 0)).prod volume` (Fubini, `integral_prod`). Split into real and
imaginary parts; each part is a parametric integral `∫ G α * L (h (p - α)) dμ`, which is smooth on
`{p | p.1 < S}` by `UnforcedLeray.Kernels.contDiffOn_integral`. The domination uses the global
bound on the iterated derivatives of `h` (periodicity in `q` plus compactness), and the vanishing
of `h` for `s < a` to cut the integrand off at `r ≤ S - a`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Basic facts -/

/-- The planar heat kernel at the joint parameter `α = (r, z)`, with `θ = ν r`. -/
def duhSm_G (ν : ℝ) (α : ℝ × (ℝ × ℝ)) : ℝ :=
  UnforcedLeray.B0284.heatKernel2 (ν * α.1) α.2

/-- The product measure `dr ⊗ dz` on `(0, ∞) × ℝ²`. -/
abbrev duhSm_μ : Measure (ℝ × (ℝ × ℝ)) :=
  ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ))

theorem duhSm_le (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

theorem duhSm_unfold {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hh : NiceScalar c h) :
    ContDiff ℝ ∞ h ∧ (∀ s x, h (s, (x.1 + c, x.2)) = h (s, x)) ∧
      ∃ a B R : ℝ, 0 < a ∧ ∀ s x, (s < a ∨ B < s ∨ R < |x.2|) → h (s, x) = 0 :=
  hh

theorem duhSm_G_measurable (ν : ℝ) : Measurable (duhSm_G ν) :=
  UnforcedLeray.B0284.measurable_heatKernel2.comp
    ((measurable_const.mul measurable_fst).prodMk measurable_snd)

theorem duhSm_μ_eq :
    duhSm_μ = (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  unfold duhSm_μ
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict, Measure.restrict_univ]

/-- Integrability of the cut-off kernel `G_{νr}(z) 1_{0 < r ≤ T}` on the product measure. -/
theorem duhSm_int_ind {ν : ℝ} (hν : 0 < ν) (T : ℝ) :
    Integrable (fun α : ℝ × (ℝ × ℝ) =>
      (Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) α) duhSm_μ := by
  rw [duhSm_μ_eq]
  refine Integrable.restrict ?_
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  have hmeas : Measurable (fun α : ℝ × (ℝ × ℝ) =>
      (Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) α) :=
    (duhSm_G_measurable ν).indicator (measurableSet_Ioc.prod MeasurableSet.univ)
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine ae_of_all _ fun r => ?_
    by_cases hr : r ∈ Ioc (0 : ℝ) T
    · have hθ : 0 < ν * r := mul_pos hν hr.1
      have hfun : (fun z : ℝ × ℝ =>
          (Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) (r, z))
          = fun z => UnforcedLeray.B0284.heatKernel2 (ν * r) z := by
        funext z
        rw [indicator_of_mem (show (r, z) ∈ Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ)) from
          ⟨hr, mem_univ z⟩)]
        rfl
      rw [hfun]
      exact UnforcedLeray.B0284.integrable_heatKernel2 hθ
    · have hfun : (fun z : ℝ × ℝ =>
          (Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) (r, z)) = fun _ => 0 := by
        funext z
        exact indicator_of_notMem (show (r, z) ∉ Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ)) from
          fun h => hr h.1) _
      rw [hfun]
      exact integrable_zero _ _ _
  · have hfun : (fun r : ℝ => ∫ z : ℝ × ℝ,
        ‖(Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) (r, z)‖) =
        (Ioc (0 : ℝ) T).indicator (fun _ => (1 : ℝ)) := by
      funext r
      by_cases hr : r ∈ Ioc (0 : ℝ) T
      · rw [indicator_of_mem hr]
        have hθ : 0 < ν * r := mul_pos hν hr.1
        have hz : ∀ z : ℝ × ℝ,
            ‖(Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) (r, z)‖
              = UnforcedLeray.B0284.heatKernel2 (ν * r) z := by
          intro z
          rw [indicator_of_mem (show (r, z) ∈ Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ)) from
            ⟨hr, mem_univ z⟩)]
          exact Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ z)
        simp_rw [hz]
        exact UnforcedLeray.B0284.integral_heatKernel2 hθ
      · have hz : ∀ z : ℝ × ℝ,
            ‖(Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) (r, z)‖ = 0 := by
          intro z
          rw [indicator_of_notMem (show (r, z) ∉ Ioc (0 : ℝ) T ×ˢ (univ : Set (ℝ × ℝ)) from
            fun h => hr h.1), norm_zero]
        simp_rw [hz]
        rw [indicator_of_notMem hr]
        simp
    rw [hfun]
    have hfin : volume (Ioc (0 : ℝ) T) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    exact (integrableOn_const (C := (1 : ℝ)) hfin (by simp)).integrable_indicator measurableSet_Ioc

/-! ## Periodicity, vanishing and boundedness of the derivatives of `h` -/

theorem duhSm_per {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hC : ∀ s x, h (s, (x.1 + c, x.2)) = h (s, x))
    (n : ℕ) (q : ℝ × (ℝ × ℝ)) :
    iteratedFDeriv ℝ n h (q.1, (q.2.1 + c, q.2.2)) = iteratedFDeriv ℝ n h q := by
  have hfun : (fun z : ℝ × (ℝ × ℝ) => h (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) = h := by
    funext z
    have e : z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = (z.1, (z.2.1 + c, z.2.2)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [e]
    exact hC z.1 z.2
  have key : iteratedFDeriv ℝ n (fun z : ℝ × (ℝ × ℝ) => h (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))))
      q = iteratedFDeriv ℝ n h (q + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) :=
    iteratedFDeriv_comp_add_right n _ q
  rw [hfun] at key
  rw [key]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem duhSm_iter_zero {h : ℝ × (ℝ × ℝ) → ℂ} {a B R : ℝ}
    (hvan : ∀ s x, (s < a ∨ B < s ∨ R < |x.2|) → h (s, x) = 0) (n : ℕ) (q : ℝ × (ℝ × ℝ))
    (hq : q.1 < a ∨ B < q.1 ∨ R < |q.2.2|) : iteratedFDeriv ℝ n h q = 0 := by
  have hopen : ∀ᶠ p in 𝓝 q, p.1 < a ∨ B < p.1 ∨ R < |p.2.2| := by
    rcases hq with h1 | h1 | h1
    · exact ((continuous_fst.continuousAt).eventually_lt continuousAt_const h1).mono
        fun p hp => Or.inl hp
    · exact (continuousAt_const.eventually_lt continuous_fst.continuousAt h1).mono
        fun p hp => Or.inr (Or.inl hp)
    · exact (continuousAt_const.eventually_lt
        (continuous_abs.comp (continuous_snd.comp continuous_snd)).continuousAt h1).mono
        fun p hp => Or.inr (Or.inr hp)
  have hev : h =ᶠ[𝓝 q] (0 : ℝ × (ℝ × ℝ) → ℂ) := by
    filter_upwards [hopen] with p hp
    exact hvan p.1 p.2 hp
  rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
  simp

theorem duhSm_bound {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hh : NiceScalar c h) (n : ℕ) :
    ∃ K : ℝ, ∀ q : ℝ × (ℝ × ℝ), ‖iteratedFDeriv ℝ n h q‖ ≤ K := by
  obtain ⟨hsm, hC, a, B, R, ha, hvan⟩ := duhSm_unfold hh
  have hcont : Continuous fun q : ℝ × (ℝ × ℝ) => ‖iteratedFDeriv ℝ n h q‖ :=
    (ContDiff.continuous_iteratedFDeriv (duhSm_le n) hsm).norm
  have hKc : IsCompact (Icc a B ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hCb⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun q => ?_⟩
  by_cases hD : a ≤ q.1 ∧ q.1 ≤ B ∧ |q.2.2| ≤ R
  · obtain ⟨hq1, hq2, hq3⟩ := hD
    have hper : Function.Periodic (fun t : ℝ => ‖iteratedFDeriv ℝ n h (q.1, (t, q.2.2))‖) c := by
      intro t
      exact congrArg norm (duhSm_per hC n (q.1, (t, q.2.2)))
    obtain ⟨y, hy, hyeq⟩ := hper.exists_mem_Ico₀ hc q.2.1
    have hmem : ((q.1, (y, q.2.2)) : ℝ × (ℝ × ℝ)) ∈ Icc a B ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R) :=
      ⟨⟨hq1, hq2⟩, ⟨⟨hy.1, hy.2.le⟩, abs_le.mp hq3⟩⟩
    have hb : ‖iteratedFDeriv ℝ n h (q.1, (y, q.2.2))‖ ≤ C := by
      have := hCb _ hmem
      simpa using this
    have hyeq' : ‖iteratedFDeriv ℝ n h q‖ = ‖iteratedFDeriv ℝ n h (q.1, (y, q.2.2))‖ := hyeq
    calc ‖iteratedFDeriv ℝ n h q‖ = ‖iteratedFDeriv ℝ n h (q.1, (y, q.2.2))‖ := hyeq'
      _ ≤ C := hb
      _ ≤ max C 0 := le_max_left _ _
  · have hz : q.1 < a ∨ B < q.1 ∨ R < |q.2.2| := by
      by_contra hcon
      push_neg at hcon
      exact hD hcon
    rw [duhSm_iter_zero hvan n q hz, norm_zero]
    exact le_max_right _ _

/-! ## Derivatives of the integrand -/

theorem duhSm_iter_eq {h : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ h) (L : ℂ →L[ℝ] ℝ) (ν : ℝ)
    (α : ℝ × (ℝ × ℝ)) (n : ℕ) (y : ℝ × (ℝ × ℝ)) :
    iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => duhSm_G ν α * L (h (p - α))) y
      = duhSm_G ν α • L.compContinuousMultilinearMap (iteratedFDeriv ℝ n h (y - α)) := by
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => h (p - α)) :=
    hsm.comp (contDiff_id.sub contDiff_const)
  have hLφ : ContDiff ℝ ∞ (L ∘ fun p : ℝ × (ℝ × ℝ) => h (p - α)) := L.contDiff.comp hφ
  have hfun : (fun p : ℝ × (ℝ × ℝ) => duhSm_G ν α * L (h (p - α)))
      = duhSm_G ν α • (L ∘ fun p : ℝ × (ℝ × ℝ) => h (p - α)) := by
    funext p
    simp [smul_eq_mul]
  rw [hfun, iteratedFDeriv_const_smul_apply (hLφ.contDiffAt.of_le (duhSm_le n)),
    ContinuousLinearMap.iteratedFDeriv_comp_left L hφ.contDiffAt (duhSm_le n),
    iteratedFDeriv_comp_sub]

/-! ## The parametric integral is smooth on half-spaces -/

theorem duhSm_part {c ν : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hν : 0 < ν) (hh : NiceScalar c h)
    (L : ℂ →L[ℝ] ℝ) (K : ℕ → ℝ) (hK : ∀ n q, ‖iteratedFDeriv ℝ n h q‖ ≤ K n) (S : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ∫ α, duhSm_G ν α * L (h (p - α)) ∂duhSm_μ)
      {p : ℝ × (ℝ × ℝ) | p.1 < S} := by
  obtain ⟨hsm, -, a, B, R, ha, hvan⟩ := duhSm_unfold hh
  refine UnforcedLeray.Kernels.contDiffOn_integral (μ := duhSm_μ)
    (F := fun (α : ℝ × (ℝ × ℝ)) (p : ℝ × (ℝ × ℝ)) => duhSm_G ν α * L (h (p - α)))
    (U := {p : ℝ × (ℝ × ℝ) | p.1 < S}) (isOpen_lt continuous_fst continuous_const) ?_ ?_ ?_
  · refine ae_of_all _ fun α => ?_
    exact contDiff_const.mul (L.contDiff.comp (hsm.comp (contDiff_id.sub contDiff_const)))
  · intro n x
    have hcont : Continuous fun α : ℝ × (ℝ × ℝ) =>
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n h (x - α)) :=
      (L.continuous_postcomp_continuousMultilinearMap).comp
        ((ContDiff.continuous_iteratedFDeriv (duhSm_le n) hsm).comp
          (continuous_const.sub continuous_id))
    refine AEStronglyMeasurable.congr (f := fun α : ℝ × (ℝ × ℝ) =>
        duhSm_G ν α • L.compContinuousMultilinearMap (iteratedFDeriv ℝ n h (x - α))) ?_ ?_
    · exact (duhSm_G_measurable ν).aestronglyMeasurable.smul hcont.aestronglyMeasurable
    · refine ae_of_all _ fun α => ?_
      exact (duhSm_iter_eq hsm L ν α n x).symm
  · unfold UnforcedLeray.Kernels.LocDominated
    intro n y0 hy0
    refine ⟨{p : ℝ × (ℝ × ℝ) | p.1 < S},
      (isOpen_lt continuous_fst continuous_const).mem_nhds hy0,
      fun α => (‖L‖ * K n) * (Ioc (0 : ℝ) (S - a) ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) α,
      (duhSm_int_ind hν (S - a)).const_mul _, ?_⟩
    rw [duhSm_μ_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with α hα
    intro y hy
    have hpos : 0 < α.1 := hα.1
    have hy' : y.1 < S := hy
    try dsimp only
    rw [duhSm_iter_eq hsm L ν α n y, norm_smul, Real.norm_eq_abs]
    have hT := ContinuousLinearMap.norm_compContinuousMultilinearMap_le L
      (iteratedFDeriv ℝ n h (y - α))
    by_cases hr : α.1 ≤ S - a
    · have hmem : α ∈ Ioc (0 : ℝ) (S - a) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨⟨hpos, hr⟩, mem_univ _⟩
      rw [indicator_of_mem hmem]
      have hG : 0 ≤ duhSm_G ν α := UnforcedLeray.B0284.heatKernel2_nonneg (mul_pos hν hpos) α.2
      rw [abs_of_nonneg hG]
      calc duhSm_G ν α * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n h (y - α))‖
          ≤ duhSm_G ν α * (‖L‖ * K n) :=
            mul_le_mul_of_nonneg_left (hT.trans (mul_le_mul_of_nonneg_left (hK n _)
              (norm_nonneg L))) hG
        _ = (‖L‖ * K n) * duhSm_G ν α := mul_comm _ _
    · have hnot : α ∉ Ioc (0 : ℝ) (S - a) ×ˢ (univ : Set (ℝ × ℝ)) := fun hm => hr hm.1.2
      rw [indicator_of_notMem hnot, mul_zero]
      have hlt : (y - α).1 < a := by
        show y.1 - α.1 < a
        linarith [not_le.mp hr]
      have hzero : iteratedFDeriv ℝ n h (y - α) = 0 :=
        duhSm_iter_zero hvan n (y - α) (Or.inl hlt)
      have hT0 : ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n h (y - α))‖ ≤ 0 :=
        hT.trans (le_of_eq (by rw [hzero, norm_zero, mul_zero]))
      nlinarith [abs_nonneg (duhSm_G ν α),
        norm_nonneg (L.compContinuousMultilinearMap (iteratedFDeriv ℝ n h (y - α)))]

/-! ## Complex integrability and the decomposition of the Duhamel solution -/

theorem duhSm_int_mul {c ν : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hν : 0 < ν) (hh : NiceScalar c h)
    (M : ℝ) (hM : ∀ q, ‖h q‖ ≤ M) (p : ℝ × (ℝ × ℝ)) :
    Integrable (fun α : ℝ × (ℝ × ℝ) => ((duhSm_G ν α : ℝ) : ℂ) * h (p - α)) duhSm_μ := by
  obtain ⟨hsm, -, a, B, R, ha, hvan⟩ := duhSm_unfold hh
  have hz : ∀ q : ℝ × (ℝ × ℝ), q.1 < a → h q = 0 := fun q hq => hvan q.1 q.2 (Or.inl hq)
  refine ((duhSm_int_ind hν (p.1 - a)).const_mul M).mono' ?_ ?_
  · exact ((Complex.measurable_ofReal.comp (duhSm_G_measurable ν)).mul
      (hsm.continuous.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable
  · rw [duhSm_μ_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with α hα
    have hpos : 0 < α.1 := hα.1
    have hG : 0 ≤ duhSm_G ν α := UnforcedLeray.B0284.heatKernel2_nonneg (mul_pos hν hpos) α.2
    try dsimp only
    by_cases hr : α.1 ≤ p.1 - a
    · have hmem : α ∈ Ioc (0 : ℝ) (p.1 - a) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨⟨hpos, hr⟩, mem_univ _⟩
      rw [indicator_of_mem hmem, norm_mul, Complex.norm_real, Real.norm_of_nonneg hG]
      calc duhSm_G ν α * ‖h (p - α)‖ ≤ duhSm_G ν α * M :=
            mul_le_mul_of_nonneg_left (hM _) hG
        _ = M * duhSm_G ν α := mul_comm _ _
    · have hnot : α ∉ Ioc (0 : ℝ) (p.1 - a) ×ˢ (univ : Set (ℝ × ℝ)) := fun hm => hr hm.1.2
      rw [indicator_of_notMem hnot, mul_zero]
      have hpa : (p - α).1 < a := by
        show p.1 - α.1 < a
        linarith [not_le.mp hr]
      rw [hz (p - α) hpa]
      simp

theorem duhSm_decomp {c ν : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hν : 0 < ν) (hh : NiceScalar c h)
    (M : ℝ) (hM : ∀ q, ‖h q‖ ≤ M) (p : ℝ × (ℝ × ℝ)) :
    duhamelHeat ν h p.1 p.2 =
      (((∫ α, duhSm_G ν α * (h (p - α)).re ∂duhSm_μ : ℝ)) : ℂ)
        + (((∫ α, duhSm_G ν α * (h (p - α)).im ∂duhSm_μ : ℝ)) : ℂ) * Complex.I := by
  have hint := duhSm_int_mul hν hh M hM p
  have hD : duhamelHeat ν h p.1 p.2 = ∫ α, ((duhSm_G ν α : ℝ) : ℂ) * h (p - α) ∂duhSm_μ := by
    unfold duhamelHeat
    exact (integral_prod (fun α : ℝ × (ℝ × ℝ) => ((duhSm_G ν α : ℝ) : ℂ) * h (p - α)) hint).symm
  have hre := integral_re hint
  have him := integral_im hint
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul] at hre him
  rw [hD]
  conv_lhs => rw [← Complex.re_add_im (∫ α, ((duhSm_G ν α : ℝ) : ℂ) * h (p - α) ∂duhSm_μ)]
  rw [← hre, ← him]

/-! ## The main theorem -/

theorem duhamelSmooth : UnforcedLeray.Short.IIIa.DuhamelSmooth := by
  unfold DuhamelSmooth
  intro c ν h hc hν hh
  have hK : ∀ n : ℕ, ∃ K : ℝ, ∀ q : ℝ × (ℝ × ℝ), ‖iteratedFDeriv ℝ n h q‖ ≤ K :=
    fun n => duhSm_bound hc hh n
  choose K hKb using hK
  have hM : ∀ q : ℝ × (ℝ × ℝ), ‖h q‖ ≤ K 0 := fun q => by
    have := hKb 0 q
    rwa [norm_iteratedFDeriv_zero] at this
  have hsmS : ∀ S : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => duhamelHeat ν h p.1 p.2)
      {p : ℝ × (ℝ × ℝ) | p.1 < S} := by
    intro S
    have e : (fun p : ℝ × (ℝ × ℝ) => duhamelHeat ν h p.1 p.2) =
        fun p => (((∫ α, duhSm_G ν α * (h (p - α)).re ∂duhSm_μ : ℝ)) : ℂ)
          + (((∫ α, duhSm_G ν α * (h (p - α)).im ∂duhSm_μ : ℝ)) : ℂ) * Complex.I :=
      funext fun p => duhSm_decomp hν hh (K 0) hM p
    rw [e]
    have h1 := duhSm_part hν hh Complex.reCLM K hKb S
    have h2 := duhSm_part hν hh Complex.imCLM K hKb S
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at h1 h2
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul contDiffOn_const)
  refine contDiff_iff_contDiffAt.2 fun p0 => ?_
  exact (hsmS (p0.1 + 1)).contDiffAt
    ((isOpen_lt continuous_fst continuous_const).mem_nhds (show p0.1 < p0.1 + 1 by linarith))

end UnforcedLeray.Short.IIIa
