import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ResponseProfile.Lap

/-!
# `PartII-b:T10/5` helper: `gAct` preserves solenoidal tests and intertwines `gradT`

Source of record: `the November 2 reference manuscript`, lines 1912-1938.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.RespProf

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0412

abbrev Sp := UnforcedLeray.Space

theorem gEntry_orth (g : Sp ≃ₗᵢ[ℝ] Sp) (i k : Fin 3) :
    ∑ j : Fin 3, gEntry g j i * gEntry g j k = if i = k then 1 else 0 := by
  have h := g.inner_map_map (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ))
  rw [PiLp.inner_apply] at h
  simp only [EuclideanSpace.inner_single_left] at h
  simpa [gEntry, mul_comm, PiLp.single_apply, eq_comm] using h

theorem symm_single_eq (g : Sp ≃ₗᵢ[ℝ] Sp) (j : Fin 3) :
    g.symm (EuclideanSpace.single j (1 : ℝ)) = ∑ k : Fin 3, gEntry g j k • EuclideanSpace.single k (1 : ℝ) := by
  ext i
  have h := g.inner_map_map (EuclideanSpace.single i (1 : ℝ)) (g.symm (EuclideanSpace.single j (1 : ℝ)))
  simp only [LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.inner_single_left] at h
  simp only [EuclideanSpace.inner_single_right] at h
  simp [gEntry, Finset.sum_apply, Pi.single_apply] at h ⊢
  rw [← h]

theorem dir_expand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : (ℝ × Sp) →L[ℝ] E) (g : Sp ≃ₗᵢ[ℝ] Sp) (j : Fin 3) :
    D (0, g.symm (EuclideanSpace.single j (1 : ℝ))) =
      ∑ k : Fin 3, gEntry g j k • D (0, EuclideanSpace.single k (1 : ℝ)) := by
  have : ((0 : ℝ), g.symm (EuclideanSpace.single j (1 : ℝ))) =
      ∑ k : Fin 3, gEntry g j k • ((0 : ℝ), (EuclideanSpace.single k (1 : ℝ) : Sp)) := by
    refine Prod.ext (by simp [Prod.fst_sum]) ?_
    rw [symm_single_eq, Prod.snd_sum]
    simp
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul D _ _

theorem dy_gAct (g : Sp ≃ₗᵢ[ℝ] Sp) (Φ : ℝ × Sp → CVec3) (hΦ : Differentiable ℝ Φ)
    (x : ℝ × Sp) (j : Fin 3) :
    dy j (gAct g Φ) x =
      gC g (∑ k : Fin 3, gEntry g j k • dy k Φ (x.1, g.symm x.2)) := by
  have h := GActLeaf3.fderiv_gAct_leaf3 g Φ hΦ x (0, coordinateVector j)
  unfold dy
  rw [h]
  congr 1
  simp only [coordinateVector]
  exact dir_expand (fderiv ℝ Φ (x.1, g.symm x.2)) g j

theorem div_aux (g : Sp ≃ₗᵢ[ℝ] Sp) (v : Fin 3 → CVec3) :
    ∑ j : Fin 3, (gC g (∑ k : Fin 3, gEntry g j k • v k)) j = ∑ i : Fin 3, v i i := by
  simp only [gC_apply]
  have h1 : ∀ j m : Fin 3, (∑ k : Fin 3, gEntry g j k • v k) m =
      ∑ k : Fin 3, ((gEntry g j k : ℝ) : ℂ) * v k m := by
    intro j m
    simp [Finset.sum_apply]
  simp only [h1, Finset.mul_sum]
  calc ∑ j : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3, ((gEntry g j m : ℝ) : ℂ) * (((gEntry g j k : ℝ) : ℂ) * v k m)
      = ∑ m : Fin 3, ∑ k : Fin 3, (∑ j : Fin 3, ((gEntry g j m * gEntry g j k : ℝ) : ℂ)) * v k m := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
    _ = ∑ i : Fin 3, v i i := by
        refine Finset.sum_congr rfl fun m _ => ?_
        have : ∀ k : Fin 3, (∑ j : Fin 3, ((gEntry g j m * gEntry g j k : ℝ) : ℂ)) * v k m =
            if m = k then v k m else 0 := by
          intro k
          rw [← Complex.ofReal_sum, gEntry_orth]
          split_ifs <;> simp
        simp only [this]
        simp

theorem div_gAct (g : Sp ≃ₗᵢ[ℝ] Sp) (Φ : ℝ × Sp → CVec3) (hΦ : Differentiable ℝ Φ)
    (x : ℝ × Sp) :
    ∑ j : Fin 3, dy j (gAct g Φ) x j = ∑ i : Fin 3, dy i Φ (x.1, g.symm x.2) i := by
  simp only [dy_gAct g Φ hΦ x]
  exact div_aux g (fun k => dy k Φ (x.1, g.symm x.2))

/-- Rotation of a scalar test. -/
def rotS (g : Sp ≃ₗᵢ[ℝ] Sp) (φ : ℝ × Sp → ℂ) : ℝ × Sp → ℂ := fun y => φ (y.1, g.symm y.2)

theorem isPhaseTest_rotS (P : ℝ) (g : Sp ≃ₗᵢ[ℝ] Sp) (φ : ℝ × Sp → ℂ) (h : IsPhaseTest P φ) :
    IsPhaseTest P (rotS g φ) := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : ContDiff ℝ ∞ (fun x : ℝ × Sp => (x.1, g.symm x.2)) :=
      contDiff_fst.prodMk ((g.symm.toContinuousLinearEquiv.contDiff).comp contDiff_snd)
    exact h.smooth.comp hL
  · intro τ y
    simp only [rotS]
    exact h.periodic τ _
  · obtain ⟨R, hR⟩ := h.bounded_support
    refine ⟨R, fun τ y hy => ?_⟩
    simp only [rotS]
    exact hR τ _ (by rw [LinearIsometryEquiv.norm_map]; exact hy)

theorem fderiv_rotS (g : Sp ≃ₗᵢ[ℝ] Sp) (φ : ℝ × Sp → ℂ) (hφ : Differentiable ℝ φ)
    (x v : ℝ × Sp) :
    fderiv ℝ (rotS g φ) x v = fderiv ℝ φ (x.1, g.symm x.2) (v.1, g.symm v.2) := by
  set L : (ℝ × Sp) →L[ℝ] (ℝ × Sp) :=
    (ContinuousLinearMap.fst ℝ ℝ Sp).prod
      ((g.symm : Sp →L[ℝ] Sp).comp (ContinuousLinearMap.snd ℝ ℝ Sp)) with hLdef
  have hL : ∀ y : ℝ × Sp, L y = (y.1, g.symm y.2) := fun y => by simp [hLdef]
  have hΨ : rotS g φ = fun y => φ (L y) := by
    funext y; simp [rotS, hL]
  have hd : HasFDerivAt (fun y => φ (L y)) ((fderiv ℝ φ (L x)).comp L) x :=
    (hφ (L x)).hasFDerivAt.comp x L.hasFDerivAt
  rw [hΨ, hd.fderiv]
  simp [hL]

theorem dy_rotS (g : Sp ≃ₗᵢ[ℝ] Sp) (φ : ℝ × Sp → ℂ) (hφ : Differentiable ℝ φ)
    (x : ℝ × Sp) (j : Fin 3) :
    dy j (rotS g φ) x = ∑ k : Fin 3, ((gEntry g j k : ℝ) : ℂ) * dy k φ (x.1, g.symm x.2) := by
  unfold dy
  rw [fderiv_rotS g φ hφ]
  have := dir_expand ((fderiv ℝ φ (x.1, g.symm x.2)).restrictScalars ℝ) g j
  simp only [coordinateVector]
  rw [show (fderiv ℝ φ (x.1, g.symm x.2)) (0, g.symm (EuclideanSpace.single j (1 : ℝ))) = _ from this]
  simp [Complex.real_smul]

theorem gradT_rotS (g : Sp ≃ₗᵢ[ℝ] Sp) (φ : ℝ × Sp → ℂ) (hφ : Differentiable ℝ φ) :
    gradT (rotS g φ) = gAct g (gradT φ) := by
  funext x
  ext m
  have hgr : ∀ (m : Fin 3) (ψ : ℝ × Sp → ℂ) (p : ℝ × Sp), (gradT ψ p) m = dy m ψ p := by
    intro m ψ p
    simp [gradT, Finset.sum_apply, Pi.single_apply]
  rw [hgr, dy_rotS g φ hφ]
  simp only [gAct]
  rw [gC_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hgr]

theorem isSolTest_gAct (P : ℝ) (g : Sp ≃ₗᵢ[ℝ] Sp) (Φ : ℝ × Sp → CVec3) (h : IsSolTest P Φ) :
    IsSolTest P (gAct g Φ) := by
  refine ⟨gActPhaseTest P g Φ h.1, fun x => ?_⟩
  rw [div_gAct g Φ (h.1.smooth.differentiable (by simp))]
  exact h.2 _

end UnforcedLeray.Short.IIb.RespProf
