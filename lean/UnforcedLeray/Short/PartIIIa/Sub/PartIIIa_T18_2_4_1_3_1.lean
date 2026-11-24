import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelSmooth

/-!
# Part III-a, tasks `PartIII-a:T18/2/4/1/3/1` and `/2`: differentiation of the Duhamel integral

Source: `the November 2 reference manuscript`,
lines 3427-3440. For a nice scalar `g` write `Fd ν g p = ∫_{α=(r,z)} G_{νr}(z) g(p - α)`
(product measure `duhSm_μ`). Then `Fd ν g = duhamelHeat ν g` (Fubini) and the directional
derivative of `Fd ν g` in direction `v` is `Fd ν (∂_v g)`, with `∂_v g` again a nice scalar.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The joint integral over `α = (r, z)`. -/
def duhFd (ν : ℝ) (g : ℝ × (ℝ × ℝ) → ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∫ α, ((duhSm_G ν α : ℝ) : ℂ) * g (p - α) ∂duhSm_μ

/-- The directional derivative of a source. -/
def duhDir (v : ℝ × (ℝ × ℝ)) (g : ℝ × (ℝ × ℝ) → ℂ) : ℝ × (ℝ × ℝ) → ℂ :=
  fun q => fderiv ℝ g q v

theorem duhFd_bdd {c : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hg : NiceScalar c g) :
    ∃ M : ℝ, ∀ q, ‖g q‖ ≤ M := by
  obtain ⟨K, hK⟩ := duhSm_bound hc hg 0
  exact ⟨K, fun q => by simpa [norm_iteratedFDeriv_zero] using hK q⟩

theorem duhFd_eq {c ν : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hν : 0 < ν) (hg : NiceScalar c g)
    (p : ℝ × (ℝ × ℝ)) : duhamelHeat ν g p.1 p.2 = duhFd ν g p := by
  obtain ⟨M, hM⟩ := duhFd_bdd hc hg
  have hint := duhSm_int_mul hν hg M hM p
  unfold duhamelHeat duhFd
  exact (integral_prod (fun α : ℝ × (ℝ × ℝ) => ((duhSm_G ν α : ℝ) : ℂ) * g (p - α)) hint).symm

/-- `fderiv` vanishes where the function vanishes on an open set. -/
theorem duhFd_fderiv_zero {g : ℝ × (ℝ × ℝ) → ℂ} {a B R : ℝ}
    (hvan : ∀ s x, (s < a ∨ B < s ∨ R < |x.2|) → g (s, x) = 0) (q : ℝ × (ℝ × ℝ))
    (hq : q.1 < a ∨ B < q.1 ∨ R < |q.2.2|) : fderiv ℝ g q = 0 := by
  have hopen : ∀ᶠ p in 𝓝 q, p.1 < a ∨ B < p.1 ∨ R < |p.2.2| := by
    rcases hq with h1 | h1 | h1
    · exact ((continuous_fst.continuousAt).eventually_lt continuousAt_const h1).mono
        fun p hp => Or.inl hp
    · exact (continuousAt_const.eventually_lt continuous_fst.continuousAt h1).mono
        fun p hp => Or.inr (Or.inl hp)
    · exact (continuousAt_const.eventually_lt
        (continuous_abs.comp (continuous_snd.comp continuous_snd)).continuousAt h1).mono
        fun p hp => Or.inr (Or.inr hp)
  have hev : g =ᶠ[𝓝 q] (0 : ℝ × (ℝ × ℝ) → ℂ) := by
    filter_upwards [hopen] with p hp
    exact hvan p.1 p.2 hp
  rw [hev.fderiv_eq]
  simp

theorem duhDir_nice {c : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hg : NiceScalar c g) (v : ℝ × (ℝ × ℝ)) :
    NiceScalar c (duhDir v g) := by
  obtain ⟨hsm, hper, a, B, R, ha, hvan⟩ := hg
  refine ⟨?_, ?_, a, B, R, ha, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fderiv ℝ g) := hsm.fderiv_right (by simp)
    exact h1.clm_apply contDiff_const
  · intro s x
    unfold duhDir
    have hfun : (fun z : ℝ × (ℝ × ℝ) => g (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) = g := by
      funext z
      have e : z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = (z.1, (z.2.1 + c, z.2.2)) := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
      rw [e]
      exact hper z.1 z.2
    have key : fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => g (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) (s, x)
        = fderiv ℝ g ((s, x) + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) := fderiv_comp_add_right _
    rw [hfun] at key
    have e2 : ((s, x) : ℝ × (ℝ × ℝ)) + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = (s, (x.1 + c, x.2)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [e2] at key
    rw [← key]
  · intro s x hx
    unfold duhDir
    rw [duhFd_fderiv_zero hvan (s, x) hx]
    simp

theorem duhFd_norm_fderiv_bdd {c : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hg : NiceScalar c g) :
    ∃ K : ℝ, ∀ q, ‖fderiv ℝ g q‖ ≤ K := by
  obtain ⟨K, hK⟩ := duhSm_bound hc hg 1
  exact ⟨K, fun q => by simpa [norm_iteratedFDeriv_one] using hK q⟩

theorem duhFd_hasFDerivAt {c ν : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hν : 0 < ν)
    (hg : NiceScalar c g) (p0 : ℝ × (ℝ × ℝ)) :
    HasFDerivAt (duhFd ν g) (∫ α, ((duhSm_G ν α : ℝ) • fderiv ℝ g (p0 - α)) ∂duhSm_μ) p0 := by
  obtain ⟨hsm, -, a, B, R, ha, hvan⟩ := duhSm_unfold hg
  obtain ⟨M, hM⟩ := duhFd_bdd hc hg
  obtain ⟨K, hK⟩ := duhFd_norm_fderiv_bdd hc hg
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set S : ℝ := p0.1 + 1 with hS
  have hfun : duhFd ν g = fun p => ∫ α, (duhSm_G ν α) • g (p - α) ∂duhSm_μ := by
    funext p
    unfold duhFd
    simp_rw [Complex.real_smul]
  rw [hfun]
  have hcg : Continuous g := hsm.continuous
  have hnhds : {p : ℝ × (ℝ × ℝ) | p.1 < S} ∈ 𝓝 p0 :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds (by show p0.1 < S; linarith)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (p : ℝ × (ℝ × ℝ)) (α : ℝ × (ℝ × ℝ)) => (duhSm_G ν α) • g (p - α))
    (F' := fun (p : ℝ × (ℝ × ℝ)) (α : ℝ × (ℝ × ℝ)) => (duhSm_G ν α) • fderiv ℝ g (p - α))
    (bound := fun α => K * (Ioc (0 : ℝ) (S - a) ×ˢ (univ : Set (ℝ × ℝ))).indicator (duhSm_G ν) α)
    hnhds ?_ ?_ ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun p => ?_
    exact (duhSm_G_measurable ν).aestronglyMeasurable.smul
      (hcg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · have := duhSm_int_mul hν hg M hM p0
    refine this.congr (Eventually.of_forall fun α => ?_)
    simp [Complex.real_smul]
  · exact (duhSm_G_measurable ν).aestronglyMeasurable.smul
      ((hsm.continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [duhSm_μ_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with α hα
    intro y hy
    have hpos : 0 < α.1 := hα.1
    have hy' : y.1 < S := hy
    have hG : 0 ≤ duhSm_G ν α := UnforcedLeray.B0284.heatKernel2_nonneg (mul_pos hν hpos) α.2
    rw [norm_smul, Real.norm_of_nonneg hG]
    by_cases hr : α.1 ≤ S - a
    · have hmem : α ∈ Ioc (0 : ℝ) (S - a) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨⟨hpos, hr⟩, mem_univ _⟩
      rw [indicator_of_mem hmem]
      calc duhSm_G ν α * ‖fderiv ℝ g (y - α)‖ ≤ duhSm_G ν α * K :=
            mul_le_mul_of_nonneg_left (hK _) hG
        _ = K * duhSm_G ν α := mul_comm _ _
    · have hnot : α ∉ Ioc (0 : ℝ) (S - a) ×ˢ (univ : Set (ℝ × ℝ)) := fun hm => hr hm.1.2
      rw [indicator_of_notMem hnot, mul_zero]
      have hlt : (y - α).1 < a := by
        show y.1 - α.1 < a
        linarith [not_le.mp hr]
      rw [duhFd_fderiv_zero hvan (y - α) (Or.inl hlt)]
      simp
  · exact (duhSm_int_ind hν (S - a)).const_mul K
  · refine Eventually.of_forall fun α y _ => ?_
    have h1 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => g (p - α)) (fderiv ℝ g (y - α)) y := by
      have := ((hsm.differentiable (by simp)) (y - α)).hasFDerivAt
      have h2 := this.comp y ((hasFDerivAt_id y).sub_const α)
      rw [ContinuousLinearMap.comp_id] at h2
      exact h2
    exact h1.const_smul (duhSm_G ν α)

theorem duhFd_integrable_fderiv {c ν : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hν : 0 < ν)
    (hg : NiceScalar c g) (p0 : ℝ × (ℝ × ℝ)) :
    Integrable (fun α => ((duhSm_G ν α : ℝ) • fderiv ℝ g (p0 - α))) duhSm_μ := by
  obtain ⟨hsm, -, a, B, R, ha, hvan⟩ := duhSm_unfold hg
  obtain ⟨K, hK⟩ := duhFd_norm_fderiv_bdd hc hg
  refine ((duhSm_int_ind hν (p0.1 - a)).const_mul K).mono' ?_ ?_
  · exact (duhSm_G_measurable ν).aestronglyMeasurable.smul
      ((hsm.continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [duhSm_μ_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with α hα
    have hpos : 0 < α.1 := hα.1
    have hG : 0 ≤ duhSm_G ν α := UnforcedLeray.B0284.heatKernel2_nonneg (mul_pos hν hpos) α.2
    try dsimp only
    rw [norm_smul, Real.norm_of_nonneg hG]
    by_cases hr : α.1 ≤ p0.1 - a
    · have hmem : α ∈ Ioc (0 : ℝ) (p0.1 - a) ×ˢ (univ : Set (ℝ × ℝ)) :=
        ⟨⟨hpos, hr⟩, mem_univ _⟩
      rw [indicator_of_mem hmem]
      calc duhSm_G ν α * ‖fderiv ℝ g (p0 - α)‖ ≤ duhSm_G ν α * K :=
            mul_le_mul_of_nonneg_left (hK _) hG
        _ = K * duhSm_G ν α := mul_comm _ _
    · have hnot : α ∉ Ioc (0 : ℝ) (p0.1 - a) ×ˢ (univ : Set (ℝ × ℝ)) := fun hm => hr hm.1.2
      rw [indicator_of_notMem hnot, mul_zero]
      have hlt : (p0 - α).1 < a := by
        show p0.1 - α.1 < a
        linarith [not_le.mp hr]
      rw [duhFd_fderiv_zero hvan (p0 - α) (Or.inl hlt)]
      simp

/-- The directional derivative of `Fd g` is `Fd (∂_v g)`. -/
theorem duhFd_fderiv_apply {c ν : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hν : 0 < ν)
    (hg : NiceScalar c g) (p : ℝ × (ℝ × ℝ)) (v : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (duhFd ν g) p v = duhFd ν (duhDir v g) p := by
  rw [(duhFd_hasFDerivAt hc hν hg p).fderiv,
    ContinuousLinearMap.integral_apply (duhFd_integrable_fderiv hc hν hg p) v]
  unfold duhFd duhDir
  refine integral_congr_ae (Eventually.of_forall fun α => ?_)
  simp [Complex.real_smul]

theorem duhFd_differentiable {c ν : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hν : 0 < ν)
    (hg : NiceScalar c g) : Differentiable ℝ (duhFd ν g) :=
  fun p => (duhFd_hasFDerivAt hc hν hg p).differentiableAt

/-- The slice integrals `Q_g(r) = ∫ G_{νr}(z) g(s - r, x - z) dz` are integrable on `(0, ∞)`
with integral `duhamelHeat`. -/
theorem duhFd_slice_integrable {c ν : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hν : 0 < ν)
    (hg : NiceScalar c g) (s : ℝ) (x : ℝ × ℝ) :
    IntegrableOn (fun r : ℝ => ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
      g (s - r, (x.1 - z.1, x.2 - z.2))) (Ioi 0) := by
  obtain ⟨M, hM⟩ := duhFd_bdd hc hg
  have hint := duhSm_int_mul hν hg M hM (s, x)
  exact hint.integral_prod_left

end UnforcedLeray.Short.IIIa
