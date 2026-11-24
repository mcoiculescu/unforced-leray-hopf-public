import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.TrainBandSub
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainVelSmooth

/-!
# `TBChartVel` (`PartIII-b:C/asrc/ra/9/2/2/11/1`)

Source of record: `the November 2 reference manuscript`, 2419-2423, 2075-2077, 4371.

Proof of the chart comparison for the planar train velocity `trPl p s = v(s)`.  For `s > 0` the
velocity `v = trainProf p` is jointly `C^∞` on `(0,∞) × ℝ²` (`trainVelSmooth_proof`); the slice
derivatives of `v` are the partials of its joint derivative.  Then
`‖v‖_∞ ≤ ‖v‖_2`, `‖D_x v‖ ≤ ‖∂_q v‖ + ‖∂_η v‖`, and `‖𝒦v‖_∞ ≤ ‖kAge v‖_2`, which gives the
bound with the factor `2` as slack.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- Derivative of a slice in the first argument. -/
private lemma tbv_slice_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × (ℝ × ℝ) → E} {s : ℝ} {z : ℝ × ℝ} (hG : DifferentiableAt ℝ G (s, z)) :
    HasDerivAt (fun t : ℝ => G (t, z)) (fderiv ℝ G (s, z) (1, 0)) s := by
  have hc : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s z)
  exact hG.hasFDerivAt.comp_hasDerivAt s hc

/-- Fréchet derivative of a spatial slice. -/
private lemma tbv_slice_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × (ℝ × ℝ) → E} {s : ℝ} {z : ℝ × ℝ} (hG : DifferentiableAt ℝ G (s, z)) :
    HasFDerivAt (fun y : ℝ × ℝ => G (s, y))
      ((fderiv ℝ G (s, z)).comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) z := by
  have hc : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
  exact hG.hasFDerivAt.comp z hc

/-- A coordinate of a Euclidean vector is bounded by its norm. -/
private lemma tbv_coord_le (u : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : ‖u i‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le u i

/-- Bound on the sup norm of a planar pair by the Euclidean norm. -/
private lemma tbv_pair_norm_le (u : EuclideanSpace ℝ (Fin 2)) :
    ‖((u 0, u 1) : ℝ × ℝ)‖ ≤ ‖u‖ := by
  rw [Prod.norm_def]
  exact max_le (PiLp.norm_apply_le u 0) (PiLp.norm_apply_le u 1)

/-- Operator norm on `ℝ × ℝ` is at most the sum of the norms of the images of the basis. -/
private lemma tbv_opNorm_pair_le (N : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    ‖N‖ ≤ ‖N (1, 0)‖ + ‖N (0, 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hw : N w = w.1 • N (1, 0) + w.2 • N (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have h1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
  rw [hw]
  calc ‖w.1 • N (1, 0) + w.2 • N (0, 1)‖
      ≤ ‖w.1 • N (1, 0)‖ + ‖w.2 • N (0, 1)‖ := norm_add_le _ _
    _ = ‖w.1‖ * ‖N (1, 0)‖ + ‖w.2‖ * ‖N (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖w‖ * ‖N (1, 0)‖ + ‖w‖ * ‖N (0, 1)‖ := by
        gcongr
    _ = (‖N (1, 0)‖ + ‖N (0, 1)‖) * ‖w‖ := by ring

theorem tbChartVel : TBChartVel := by
  intro p d dm dp hBG s hs x
  have hcd := trainVelSmooth_proof p d dm dp hBG
  -- joint differentiability of the velocity at `(s, z)` with `s > 0`
  have hD : ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      DifferentiableAt ℝ (UnforcedLeray.Short.IIb.trainProf p) y := by
    intro y hy
    exact (hcd.differentiableOn (by simp)).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hy, trivial⟩)
  have hVd : DifferentiableAt ℝ (UnforcedLeray.Short.IIb.trainProf p) (s, x) := hD (s, x) hs
  set V := UnforcedLeray.Short.IIb.trainProf p with hVdef
  -- coordinate functionals on the Euclidean plane
  let ℓ0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 0
  let ℓ1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hℓ0 : ∀ u : EuclideanSpace ℝ (Fin 2), ℓ0 u = u 0 := fun u => rfl
  have hℓ1 : ∀ u : EuclideanSpace ℝ (Fin 2), ℓ1 u = u 1 := fun u => rfl
  -- derivatives of the two planar components of `trPl p s`
  have hf0 : HasFDerivAt (fun y : ℝ × ℝ => ℓ0 (V (s, y)))
      (ℓ0.comp ((fderiv ℝ V (s, x)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))))) x :=
    ℓ0.hasFDerivAt.comp x (tbv_slice_fderiv hVd)
  have hf1 : HasFDerivAt (fun y : ℝ × ℝ => ℓ1 (V (s, y)))
      (ℓ1.comp ((fderiv ℝ V (s, x)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))))) x :=
    ℓ1.hasFDerivAt.comp x (tbv_slice_fderiv hVd)
  have hfd : fderiv ℝ (trPl p s) x = _ := (hf0.prodMk hf1).fderiv
  have hN1 : fderiv ℝ (trPl p s) x (1, 0) =
      (fderiv ℝ V (s, x) (0, (1, 0)) 0, fderiv ℝ V (s, x) (0, (1, 0)) 1) := by
    rw [hfd]
    simp [hℓ0, hℓ1]
  have hN2 : fderiv ℝ (trPl p s) x (0, 1) =
      (fderiv ℝ V (s, x) (0, (0, 1)) 0, fderiv ℝ V (s, x) (0, (0, 1)) 1) := by
    rw [hfd]
    simp [hℓ0, hℓ1]
  -- operator norm of the `x`-derivative of `trPl p s`
  have hNorm : ‖fderiv ℝ (trPl p s) x‖ ≤
      ‖fderiv ℝ V (s, x) (0, (1, 0))‖ + ‖fderiv ℝ V (s, x) (0, (0, 1))‖ := by
    refine le_trans (tbv_opNorm_pair_le _) ?_
    rw [hN1, hN2]
    exact add_le_add (tbv_pair_norm_le _) (tbv_pair_norm_le _)
  -- the first-argument derivative of `v` and the operator `𝒦`
  have ek : UnforcedLeray.Short.IIb.kAge V (s, x) = (2 * s) • fderiv ℝ V (s, x) (1, 0) +
      x.2 • fderiv ℝ V (s, x) (0, (0, 1)) := rfl
  have hK1 : Kop (fun s' y => (trPl p s' y).1) s x = ℓ0 (UnforcedLeray.Short.IIb.kAge V (s, x)) := by
    have e1 : fderiv ℝ (fun y => (trPl p s y).1) x (ei 1) =
        ℓ0 (fderiv ℝ V (s, x) (0, (0, 1))) := by
      show fderiv ℝ (fun y : ℝ × ℝ => ℓ0 (V (s, y))) x (ei 1) = _
      rw [hf0.fderiv]
      simp [hℓ0, ei]
    have e2 : deriv (fun s' => (trPl p s' x).1) s = ℓ0 (fderiv ℝ V (s, x) (1, 0)) :=
      (ℓ0.hasFDerivAt.comp_hasDerivAt s (tbv_slice_deriv hVd)).deriv
    show x.2 * fderiv ℝ (fun y => (trPl p s y).1) x (ei 1) +
      2 * s * deriv (fun s' => (trPl p s' x).1) s = _
    rw [e1, e2, ek]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hK2 : Kop (fun s' y => (trPl p s' y).2) s x = ℓ1 (UnforcedLeray.Short.IIb.kAge V (s, x)) := by
    have e1 : fderiv ℝ (fun y => (trPl p s y).2) x (ei 1) =
        ℓ1 (fderiv ℝ V (s, x) (0, (0, 1))) := by
      show fderiv ℝ (fun y : ℝ × ℝ => ℓ1 (V (s, y))) x (ei 1) = _
      rw [hf1.fderiv]
      simp [hℓ1, ei]
    have e2 : deriv (fun s' => (trPl p s' x).2) s = ℓ1 (fderiv ℝ V (s, x) (1, 0)) :=
      (ℓ1.hasFDerivAt.comp_hasDerivAt s (tbv_slice_deriv hVd)).deriv
    show x.2 * fderiv ℝ (fun y => (trPl p s y).2) x (ei 1) +
      2 * s * deriv (fun s' => (trPl p s' x).2) s = _
    rw [e1, e2, ek]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hcK : ‖cK (trPl p) s x‖ ≤ ‖UnforcedLeray.Short.IIb.kAge V (s, x)‖ := by
    show ‖(Kop (fun s' y => (trPl p s' y).1) s x, Kop (fun s' y => (trPl p s' y).2) s x)‖ ≤ _
    rw [hK1, hK2, Prod.norm_def]
    exact max_le (tbv_coord_le (UnforcedLeray.Short.IIb.kAge V (s, x)) 0)
      (tbv_coord_le (UnforcedLeray.Short.IIb.kAge V (s, x)) 1)
  have hB : ‖trPl p s x‖ ≤ ‖V (s, x)‖ := tbv_pair_norm_le (V (s, x))
  have hA := norm_nonneg (V (s, x))
  have hQ := norm_nonneg (Axi.dQ V (s, x))
  have hE := norm_nonneg (Axi.dEta V (s, x))
  have hK := norm_nonneg (UnforcedLeray.Short.IIb.kAge V (s, x))
  have hNormQ : ‖fderiv ℝ (trPl p s) x‖ ≤ ‖Axi.dQ V (s, x)‖ + ‖Axi.dEta V (s, x)‖ := hNorm
  linarith [hB, hNormQ, hcK, hA, hQ, hE, hK]

end UnforcedLeray.Short.PartIIIb.Concrete
