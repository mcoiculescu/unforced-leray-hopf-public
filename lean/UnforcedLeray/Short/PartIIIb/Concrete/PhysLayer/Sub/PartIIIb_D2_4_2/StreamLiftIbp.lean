import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# `StreamLiftIbp`: per-phase weak divergence-free pairing (source 4991-4997, 5036-5039)

Let `F = streamLift Ψ`. It is `C¹` on `ℝ³` and vanishes on `{ϱ < ρ₀}` (`Ψ = 0` on
`{0 < ρ < ρ₀}`), with `div F = 0` everywhere (`div_streamLift_eq_zero` off the axis, `F = 0`
near the axis). For a phase test `φ`, the spatial test `ψ = φ(τ, ·)` is smooth with compact
support, and `∫ ∇ψ · F = -∫ ψ div F = 0` by coordinatewise integration by parts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem streamLiftIbp_proof : StreamLiftIbp := by
  intro P Ψ hΨ ρ0 hρ0 hΨzero φ hφ τ
  set F : Space → Space := streamLift Ψ with hF_def
  -- (a) `F` vanishes on `{ϱ < ρ₀}`
  have hzero : ∀ x : Space, ϱ x < ρ0 → F x = 0 := by
    intro x hx
    rw [hF_def, streamLift_apply]
    by_cases h0 : ϱ x = 0
    · rw [h0]; simp
    · have hpos : 0 < ϱ x := lt_of_le_of_ne (ϱ_nonneg x) (Ne.symm h0)
      have hU : IsOpen (Ioo (0 : ℝ) ρ0 ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
      have hmem : mer x ∈ Ioo (0 : ℝ) ρ0 ×ˢ (univ : Set ℝ) :=
        mem_prod.mpr ⟨mem_Ioo.mpr ⟨hpos, hx⟩, mem_univ _⟩
      have hev : Ψ =ᶠ[𝓝 (mer x)] fun _ => (0 : ℝ) := by
        filter_upwards [hU.mem_nhds hmem] with q hq
        obtain ⟨h1, h2⟩ := mem_Ioo.mp (mem_prod.mp hq).1
        exact hΨzero q h1 h2
      have hf0 : fderiv ℝ Ψ (mer x) = 0 := by
        rw [hev.fderiv_eq]; simp
      simp [dz, dρ, hf0]
  have hnear : ∀ y : Space, ϱ y < ρ0 → F =ᶠ[𝓝 y] fun _ => (0 : Space) := by
    intro y hy
    have hopen : IsOpen {x : Space | ϱ x < ρ0} := isOpen_lt continuous_ϱ continuous_const
    filter_upwards [hopen.mem_nhds hy] with x hx
    exact hzero x hx
  -- (b) `F` is `C¹` on `ℝ³`
  have hcd : ContDiff ℝ 1 F := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ axis
    · have hy0 : ϱ y < ρ0 := by rw [(mem_axis_iff y).1 hy]; exact hρ0
      exact contDiffAt_const.congr_of_eventuallyEq (hnear y hy0)
    · exact (contDiffOn_liftMer (contDiffOn_streamProfile hΨ)).contDiffAt
        (isOpen_compl_axis.mem_nhds hy)
  -- (c) `div F = 0` everywhere
  have hdiv : ∀ x : Space, Axi.divergence F x = 0 := by
    intro x
    by_cases hx : x ∈ axis
    · have hx0 : ϱ x < ρ0 := by rw [(mem_axis_iff x).1 hx]; exact hρ0
      have hfd : fderiv ℝ F x = 0 := by
        rw [(hnear x hx0).fderiv_eq]
        exact fderiv_const_apply _
      simp [Axi.divergence, hfd]
    · exact div_streamLift_eq_zero hΨ hx
  -- (d) the spatial test `ψ = φ(τ, ·)`
  obtain ⟨R, hR⟩ := hφ.bounded_support
  set ψ : Space → ℂ := fun y => φ (τ, y) with hψ_def
  have hψsmooth := ContDiff.comp hφ.smooth (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun y : Space => ((τ, y) : ℝ × Space)))
  have hψcont : Continuous ψ := hψsmooth.continuous
  have hψdiff : ∀ x : Space, DifferentiableAt ℝ ψ x := fun x =>
    hψsmooth.differentiable (by simp) x
  have hψzero : ∀ x : Space, x ∉ Metric.closedBall (0 : Space) R → ψ x = 0 := by
    intro x hx
    exact hR τ x (not_le.mp (fun h => hx (mem_closedBall_zero_iff.mpr h)))
  have hψfder : ∀ x : Space, x ∉ Metric.closedBall (0 : Space) R → ∀ v : Space,
      fderiv ℝ ψ x v = 0 := by
    intro x hx v
    have hev : ψ =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [(Metric.isClosed_closedBall.isOpen_compl).mem_nhds hx] with q hq
      exact hψzero q hq
    rw [hev.fderiv_eq]
    simp
  -- integrability: a continuous function times a test vanishing off a ball
  have hint : ∀ a b : Space → ℂ, Continuous a → Continuous b →
      (∀ x : Space, x ∉ Metric.closedBall (0 : Space) R → b x = 0) →
      Integrable (fun x => a x * b x) := by
    intro a b ha hb hbz
    exact (ha.mul hb).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
        (fun x hx => by simp [hbz x hx]))
  -- (e) the components `G i = F_i` as complex functions
  set G : Fin 3 → Space → ℂ := fun i y => ((F y i : ℝ) : ℂ) with hG_def
  have hGc : ∀ i : Fin 3, ContDiff ℝ 1 (G i) := fun i =>
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hcd)
  have hGd' : ∀ (i : Fin 3) (y : Space), HasFDerivAt (G i)
      (Complex.ofRealCLM.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ F y))) y := by
    intro i y
    have hFd : HasFDerivAt F (fderiv ℝ F y) y := (hcd.differentiable (by simp) y).hasFDerivAt
    exact Complex.ofRealCLM.hasFDerivAt.comp y
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hFd)
  have hGd : ∀ (i : Fin 3) (y v : Space), fderiv ℝ (G i) y v = ((fderiv ℝ F y v i : ℝ) : ℂ) := by
    intro i y v
    rw [(hGd' i y).fderiv]
    simp
  have hdivG : ∀ y : Space, ∑ i : Fin 3, fderiv ℝ (G i) y (coordinateVector i) =
      ((Axi.divergence F y : ℝ) : ℂ) := by
    intro y
    simp [hGd, Axi.divergence, Complex.ofReal_sum]
  have hz : ∀ y : Space, ∑ i : Fin 3, fderiv ℝ (G i) y (coordinateVector i) * ψ y = 0 := by
    intro y
    rw [← Finset.sum_mul, hdivG y, hdiv y, Complex.ofReal_zero, zero_mul]
  -- (f) the phase-test derivative is the spatial derivative of `ψ`
  have hdy : ∀ (i : Fin 3) (y : Space),
      PhaseSpace.dy i φ (τ, y) = fderiv ℝ ψ y (coordinateVector i) := by
    intro i y
    have hφd : DifferentiableAt ℝ φ (τ, y) := hφ.smooth.differentiable (by simp) _
    have h := hφd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
    show fderiv ℝ φ (τ, y) (0, coordinateVector i) =
      fderiv ℝ (fun z : Space => φ (τ, z)) y (coordinateVector i)
    rw [show (fun z : Space => φ (τ, z)) = φ ∘ fun z => (τ, z) from rfl, h.fderiv]
    simp
  -- (g) the integrand is `∑ᵢ G_i ∂ᵢψ`
  have hpt : ∀ y : Space, dotL (gradT φ (τ, y)) (B0412.realC (F y)) =
      ∑ i : Fin 3, G i y * fderiv ℝ ψ y (coordinateVector i) := by
    intro y
    rw [dotL_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : gradT φ (τ, y) i = PhaseSpace.dy i φ (τ, y) := by
      simp [gradT, Pi.single_apply]
    rw [hg, hdy i y, B0412.realC_apply]
    simp only [hG_def]
    ring
  -- (h) integrability of the coordinate products
  have hG_cont : ∀ i : Fin 3, Continuous (G i) := fun i => (hGc i).continuous
  have hdψ_cont : ∀ v : Space, Continuous (fun x => fderiv ℝ ψ x v) := fun v =>
    (hψsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdG_cont : ∀ (i : Fin 3) (v : Space), Continuous (fun x => fderiv ℝ (G i) x v) :=
    fun i v => ((hGc i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hI1 : ∀ i : Fin 3, Integrable (fun y => G i y * fderiv ℝ ψ y (coordinateVector i)) :=
    fun i => hint _ _ (hG_cont i) (hdψ_cont _) (fun x hx => hψfder x hx _)
  have hI2 : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ (G i) y (coordinateVector i) * ψ y) :=
    fun i => hint _ _ (hdG_cont i _) hψcont (fun x hx => hψzero x hx)
  -- (i) coordinatewise integration by parts
  have hIBP : ∀ i : Fin 3, ∫ y, G i y * fderiv ℝ ψ y (coordinateVector i) =
      -∫ y, fderiv ℝ (G i) y (coordinateVector i) * ψ y := by
    intro i
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := G i) (g := ψ) (v := coordinateVector i)
      (hI2 i) (hI1 i)
      (hint _ _ (hG_cont i) hψcont (fun x hx => hψzero x hx))
      (fun x _ => (hGc i).differentiable (by simp) x)
      (fun x _ => hψdiff x)
  -- (j) assemble
  have hfun : (fun y => dotL (gradT φ (τ, y)) (B0412.realC (F y))) =
      fun y => ∑ i : Fin 3, G i y * fderiv ℝ ψ y (coordinateVector i) :=
    funext hpt
  rw [hfun, integral_finsetSum _ (fun i _ => hI1 i)]
  rw [Finset.sum_congr rfl (fun i _ => hIBP i), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun i _ => hI2 i)]
  simp [hz]

end UnforcedLeray.Short.PartIIIb.Concrete
