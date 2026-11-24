import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.AdvSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1

/-!
# Far product rule, transport-by-gradient part (helper for `ProdHom`)

Source `the November 2 reference manuscript`
lines 2542-2549, 2563-2569: for `G` smooth on an open set `U`, with `gradAlong` written as
`∑ₖ Eₖ · realC(∂ₖG)`, `∂_j (gradAlong (G) E) = ∑ₖ ((∂_jEₖ) realC(∂ₖG) + Eₖ realC(∂_j∂ₖG))`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.ProdHom

/-- Slice derivative identity: the spatial derivative of a slice is the joint derivative in
the spatial direction (chain rule, `G` differentiable at `(τ, y)`). -/
theorem slice_fderiv_at {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : ℝ × UnforcedLeray.Space → V) (τ : ℝ) (y v : UnforcedLeray.Space)
    (hG : DifferentiableAt ℝ G (τ, y)) :
    fderiv ℝ (fun w : UnforcedLeray.Space => G (τ, w)) y v = fderiv ℝ G (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun w : UnforcedLeray.Space => ((τ, w) : ℝ × UnforcedLeray.Space))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hG.hasFDerivAt).comp y hmap
  have h := congrArg (fun A : UnforcedLeray.Space →L[ℝ] V => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h

/-- The coordinate vector `e_k` as a Euclidean vector. -/
theorem coordinateVector_eq_single (k : Fin 3) :
    UnforcedLeray.coordinateVector k = (EuclideanSpace.single k (1 : ℝ) : UnforcedLeray.Space) := by
  simp [UnforcedLeray.coordinateVector]

/-- `∂_j G` is differentiable at a point of an open set on which `G` is `C^∞`. -/
theorem diffAt_dy_of_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : ℝ × UnforcedLeray.Space → V) (U : Set (ℝ × UnforcedLeray.Space)) (hU : IsOpen U)
    (hGU : ContDiffOn ℝ ∞ G U) (k : Fin 3) (x : ℝ × UnforcedLeray.Space) (hx : x ∈ U) :
    DifferentiableAt ℝ (dy k G) x := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ G) U := hGU.fderiv_of_isOpen hU (by simp)
  have hc : ContDiffOn ℝ ∞ (fun z => fderiv ℝ G z (0, UnforcedLeray.coordinateVector k)) U :=
    hd.clm_apply contDiffOn_const
  exact (hc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)

/-- Two functions that agree near a point have the same `∂_j` there. -/
theorem dy_congr_nhds {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (j : Fin 3)
    (F H : ℝ × UnforcedLeray.Space → V) (x : ℝ × UnforcedLeray.Space)
    (h : F =ᶠ[nhds x] H) : dy j F x = dy j H x := by
  simp only [dy]
  rw [h.fderiv_eq]

/-- Near a point of an open set on which `G` is `C^∞`, the transport-by-gradient term equals
`∑ₖ Eₖ realC(∂ₖG)` (the slice identity for the spatial derivative). -/
theorem gradAlong_eq_nhds (G : ℝ × UnforcedLeray.Space → UnforcedLeray.Space)
    (E : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (U : Set (ℝ × UnforcedLeray.Space)) (hU : IsOpen U) (hGU : ContDiffOn ℝ ∞ G U)
    (x : ℝ × UnforcedLeray.Space) (hx : x ∈ U) :
    gradAlong (fun t y => G (t, y)) E =ᶠ[nhds x]
      (fun z => ∑ k : Fin 3, E z k • UnforcedLeray.B0412.realC (dy k G z)) := by
  have hGd : ∀ z ∈ U, DifferentiableAt ℝ G z := fun z hz =>
    (hGU.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  filter_upwards [hU.mem_nhds hx] with z hz
  have hs : ∀ k : Fin 3, fderiv ℝ (fun w : UnforcedLeray.Space => G (z.1, w)) z.2
      (EuclideanSpace.single k (1 : ℝ)) = dy k G z := by
    intro k
    rw [← coordinateVector_eq_single]
    exact slice_fderiv_at G z.1 z.2 _ (hGd z hz)
  ext i
  simp [gradAlong, hs, UnforcedLeray.B0412.realC_apply]

/-- `∂_j` of the transport-by-gradient term (`gradAlong` of the slice family `(t,y) ↦ G(t,y)`). -/
theorem dy_gradAlong_pt (j : Fin 3) (G : ℝ × UnforcedLeray.Space → UnforcedLeray.Space)
    (E : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (U : Set (ℝ × UnforcedLeray.Space)) (hU : IsOpen U) (hGU : ContDiffOn ℝ ∞ G U)
    (hE : ContDiff ℝ ∞ E) (x : ℝ × UnforcedLeray.Space) (hx : x ∈ U) :
    dy j (gradAlong (fun t y => G (t, y)) E) x =
      ∑ k : Fin 3, (dy j (fun z => E z k) x •
          UnforcedLeray.B0412.realC (dy k G x) +
        E x k • UnforcedLeray.B0412.realC (dy j (dy k G) x)) := by
  have hev := gradAlong_eq_nhds G E U hU hGU x hx
  have hEd : DifferentiableAt ℝ E x := (hE.differentiable (by simp)) x
  have hdk : ∀ k : Fin 3, DifferentiableAt ℝ (fun z => UnforcedLeray.B0412.realC (dy k G z)) x :=
    fun k => by
      have h0 := (realCLI.toContinuousLinearMap.differentiableAt).comp x
        (diffAt_dy_of_contDiffOn G U hU hGU k x hx)
      exact h0
  rw [dy_congr_nhds j _ _ x hev]
  rw [dy_finset_sum_pt Finset.univ (fun k z => E z k • UnforcedLeray.B0412.realC (dy k G z)) x j
    (fun k _ => (diffAt_apply_k k E x hEd).smul (hdk k))]
  apply Finset.sum_congr rfl
  intro k _
  have h1 := dy_cmul_pt j (fun z => E z k) (fun z => UnforcedLeray.B0412.realC (dy k G z)) x
    (diffAt_apply_k k E x hEd) (hdk k)
  have h2 := dy_realC_pt j (dy k G) x (diffAt_dy_of_contDiffOn G U hU hGU k x hx)
  simp only at h1
  rw [h1, h2, add_comm]

end UnforcedLeray.Short.PartIIIb.Concrete.ProdHom
