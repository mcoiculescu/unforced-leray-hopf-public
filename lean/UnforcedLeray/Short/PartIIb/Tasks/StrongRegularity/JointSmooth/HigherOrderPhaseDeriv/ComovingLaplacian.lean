import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving

set_option autoImplicit false

noncomputable section

open scoped ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

/-- Directional jets of the spatial Laplacian, as a sum over the two-fold directions. -/
theorem hh5_laplacian_jet (F : SpatialField) (hF : ContDiff ℝ ∞ F) (ws : List Space) :
    dirSpatialJet (spatialLaplacian F) ws =
      fun y => ∑ j : Fin 3, dirSpatialJet F
        (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) y := by
  have hs := HigherPhaseSub.dirSpatialJet_sum (Finset.univ : Finset (Fin 3))
    (F := fun j : Fin 3 => dirSpatialJet F [EuclideanSpace.single j 1, EuclideanSpace.single j 1])
    (fun j _ => JointSmoothSub.contDiff_infty_dirSpatialJet hF _) ws
  calc dirSpatialJet (spatialLaplacian F) ws
      = fun y => ∑ j : Fin 3,
          dirSpatialJet (dirSpatialJet F [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) ws y :=
        hs
    _ = fun y => ∑ j : Fin 3, dirSpatialJet F
          (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) y := by
        funext y
        exact Finset.sum_congr rfl fun j _ =>
          congrFun (HigherPhaseSub.dirSpatialJet_append F ws
            [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) y

theorem hh5_laplacian_apply (F : SpatialField) (hF : ContDiff ℝ ∞ F) (ws : List Space) (z : Space) :
    dirSpatialJet (spatialLaplacian F) ws z =
      ∑ j : Fin 3, dirSpatialJet F
        (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) z :=
  congrFun (hh5_laplacian_jet F hF ws) z

theorem hh5_laplacian_contDiff (F : SpatialField) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialLaplacian F) :=
  ContDiff.sum fun j _ => JointSmoothSub.contDiff_infty_dirSpatialJet hF
    [EuclideanSpace.single j 1, EuclideanSpace.single j 1]

end UnforcedLeray.Short.IIb

open UnforcedLeray.Short.IIb in
theorem comovingLaplacianRule_proof : UnforcedLeray.Short.IIb.ComovingLaplacianRule := by
  unfold UnforcedLeray.Short.IIb.ComovingLaplacianRule
  intro V V' hV hV' dV
  intro ws τ y
  dsimp only
  have hfun : (fun t : ℝ => dirSpatialJet (spatialLaplacian (V (τ + t))) ws
      (Real.exp (-t / 2) • y)) =
      fun t : ℝ => ∑ j : Fin 3, dirSpatialJet (V (τ + t))
        (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) (Real.exp (-t / 2) • y) := by
    funext t
    exact UnforcedLeray.Short.IIb.hh5_laplacian_apply (V (τ + t)) (hV (τ + t)) ws _
  have hd : HasDerivAt (fun t : ℝ => ∑ j : Fin 3, dirSpatialJet (V (τ + t))
        (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) (Real.exp (-t / 2) • y))
      (∑ j : Fin 3, (dirSpatialJet (V' τ)
          (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) y +
        ((((ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]).length : ℕ) : ℝ) / 2) •
          dirSpatialJet (V τ)
            (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) y)) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    exact dV _ τ y
  have hΔ' : ContDiff ℝ ∞ (spatialLaplacian (V' τ)) :=
    UnforcedLeray.Short.IIb.hh5_laplacian_contDiff _ (hV' τ)
  have hΔ : ContDiff ℝ ∞ (spatialLaplacian (V τ)) :=
    UnforcedLeray.Short.IIb.hh5_laplacian_contDiff _ (hV τ)
  have hR : dirSpatialJet (spatialLaplacian (V' τ) + spatialLaplacian (V τ)) ws y =
      (∑ j : Fin 3, dirSpatialJet (V' τ)
          (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) y) +
      ∑ j : Fin 3, dirSpatialJet (V τ)
          (ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) y := by
    rw [congrFun (HigherPhaseSub.dirSpatialJet_add hΔ' hΔ ws) y, Pi.add_apply,
      UnforcedLeray.Short.IIb.hh5_laplacian_apply _ (hV' τ),
      UnforcedLeray.Short.IIb.hh5_laplacian_apply _ (hV τ)]
  rw [hfun]
  refine HasDerivAt.congr_deriv hd ?_
  rw [hR, UnforcedLeray.Short.IIb.hh5_laplacian_apply _ (hV τ)]
  have hlen : ∀ j : Fin 3,
      ((((ws ++ [EuclideanSpace.single j 1, EuclideanSpace.single j 1]).length : ℕ) : ℝ) / 2) =
        (ws.length : ℝ) / 2 + 1 := by
    intro j
    simp only [List.length_append, List.length_cons, List.length_nil]
    push_cast
    ring
  simp only [hlen, add_smul, one_smul, Finset.sum_add_distrib, Finset.smul_sum]
  abel
