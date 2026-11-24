import UnforcedLeray.Short.PartI.Sub.L_T02_1_4_6_4_5_2

/-!
# Part I, task `PartI:T02/1/4/6/4/5/2/1`: sup bound of the difference of representatives

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `AdvLipSupDiff`.  Route (no decay in `η` is needed): for each component `j`, the scalar
`f = (w r - w s) j` is smooth and periodic, its derivative words of order `≤ 2` are the `j`-th
components of `vecH3CellDerivCLM α (u r - u s)` a.e. (`IsSpatialRepOn.represents`), hence in
`L²(cell)` with norm `≤ ‖u r - u s‖_{H³}`; `TrainB.smooth_H2_enorm_le_cell` then gives
`|f z| ≤ 12 ‖u r - u s‖` and `C = 24`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- `iterD` commutes with a continuous linear map. -/
theorem advSup_iterD_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {u : Plane → F}
    (hu : ContDiff ℝ ∞ u) (vs : List Plane) :
    Sob.iterD vs (fun z => L (u z)) = fun z => L (Sob.iterD vs u z) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [Sob.iterD_cons, ih]
    have hd : DifferentiableAt ℝ (Sob.iterD vs u) x :=
      ((Sob.contDiff_iterD hu vs).differentiable (by simp)) x
    have h := (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    have e : (fun z => L (Sob.iterD vs u z)) = L ∘ Sob.iterD vs u := rfl
    show fderiv ℝ (fun z => L (Sob.iterD vs u z)) x v = L (fderiv ℝ (Sob.iterD vs u) x v)
    rw [e, h]
    rfl

/-- `iterD` is additive in the (smooth) argument. -/
theorem advSup_iterD_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u₁ u₂ : Plane → F}
    (h₁ : ContDiff ℝ ∞ u₁) (h₂ : ContDiff ℝ ∞ u₂) (vs : List Plane) :
    Sob.iterD vs (fun z => u₁ z - u₂ z) = fun z => Sob.iterD vs u₁ z - Sob.iterD vs u₂ z := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [Sob.iterD_cons, ih]
    have d1 : DifferentiableAt ℝ (Sob.iterD vs u₁) x :=
      ((Sob.contDiff_iterD h₁ vs).differentiable (by simp)) x
    have d2 : DifferentiableAt ℝ (Sob.iterD vs u₂) x :=
      ((Sob.contDiff_iterD h₂ vs).differentiable (by simp)) x
    have e : (fun z => Sob.iterD vs u₁ z - Sob.iterD vs u₂ z) =
        Sob.iterD vs u₁ - Sob.iterD vs u₂ := rfl
    show fderiv ℝ (fun z => Sob.iterD vs u₁ z - Sob.iterD vs u₂ z) x v = _
    rw [e, fderiv_sub d1 d2]
    rfl

/-- The `j`-th component of the derivative word of the difference of two representatives. -/
theorem advSup_iterD_comp {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
    {w : ℝ → Plane → Vec} (hw : IsSpatialRepOn c T u w) {r s : ℝ}
    (hr : r ∈ Icc (0 : ℝ) T) (hs : s ∈ Icc (0 : ℝ) T) (j : Fin 2) (vs : List Plane) :
    Sob.iterD vs (fun z => (w r z - w s z) j) =
      fun z => (Sob.iterD vs (w r) z - Sob.iterD vs (w s) z) j := by
  have h1 := hw.smooth r hr
  have h2 := hw.smooth s hs
  have := advSup_iterD_clm (EuclideanSpace.proj (𝕜 := ℝ) j) (h1.sub h2) vs
  have e : (fun z => (w r z - w s z) j) =
      fun z => (EuclideanSpace.proj (𝕜 := ℝ) j) ((fun z => w r z - w s z) z) := rfl
  rw [e, this, advSup_iterD_sub h1 h2]
  rfl

/-- Each derivative word of the component is in `L²(cell)`, with norm `≤ ‖u r - u s‖`. -/
theorem advSup_term {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
    {w : ℝ → Plane → Vec} (hw : IsSpatialRepOn c T u w) {r s : ℝ}
    (hr : r ∈ Icc (0 : ℝ) T) (hs : s ∈ Icc (0 : ℝ) T) (α : Sob.Idx 2 3) (j : Fin 2) :
    MemLp (Sob.iterD ((Sob.cylinder c).word α) (fun z => (w r z - w s z) j)) 2 (Cyl.cellμ c) ∧
    eLpNorm (Sob.iterD ((Sob.cylinder c).word α) (fun z => (w r z - w s z) j)) 2 (Cyl.cellμ c) ≤
      ENNReal.ofReal ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖ := by
  set vs := (Sob.cylinder c).word α with hvs
  set y := vecH3CellDerivCLM α (u ⟨r, hr⟩ - u ⟨s, hs⟩) with hy
  have hae : (Sob.iterD vs (fun z => (w r z - w s z) j)) =ᵐ[Cyl.cellμ c] fun z => (y z) j := by
    filter_upwards [hw.represents ⟨r, hr⟩ α, hw.represents ⟨s, hs⟩ α,
      Lp.coeFn_sub (vecH3CellDerivCLM α (u ⟨r, hr⟩)) (vecH3CellDerivCLM α (u ⟨s, hs⟩))]
      with z h1 h2 h3
    rw [advSup_iterD_comp hw hr hs j vs, hy, map_sub, h3, Pi.sub_apply, h1, h2]
  have hcont : Continuous (Sob.iterD vs (fun z => (w r z - w s z) j)) := by
    have hsm : ContDiff ℝ ∞ (fun z => (w r z - w s z) j) :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp ((hw.smooth r hr).sub (hw.smooth s hs))
    exact (Sob.contDiff_iterD hsm vs).continuous
  have hle : ∀ᵐ z ∂(Cyl.cellμ c), ‖Sob.iterD vs (fun z => (w r z - w s z) j) z‖ ≤ ‖y z‖ := by
    filter_upwards [hae] with z hz
    rw [hz]
    simpa using PiLp.norm_apply_le (y z) j
  refine ⟨(Lp.memLp y).of_le hcont.aestronglyMeasurable hle, ?_⟩
  refine (eLpNorm_mono_ae hle).trans ?_
  have h1 : eLpNorm (⇑y) 2 (Cyl.cellμ c) = ENNReal.ofReal ‖y‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top y)]
  rw [h1]
  exact ENNReal.ofReal_le_ofReal (vecH3CellDeriv_norm_le α _)

/-- Sup bound of one component of the difference. -/
theorem advSup_comp_le {c T : ℝ} (hc1 : 1 ≤ c)
    {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
    {w : ℝ → Plane → Vec} (hw : IsSpatialRepOn c T u w) {r s : ℝ}
    (hr : r ∈ Icc (0 : ℝ) T) (hs : s ∈ Icc (0 : ℝ) T) (j : Fin 2) (z : Plane) :
    ‖(w r z - w s z) j‖ ≤ 12 * ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖ := by
  set f : Plane → ℝ := fun z => (w r z - w s z) j with hf
  set X := ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖ with hX
  have hsm : ContDiff ℝ ∞ f :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp ((hw.smooth r hr).sub (hw.smooth s hs))
  have hd : Differentiable ℝ f := hsm.differentiable (by simp)
  have hper : Cyl.IsPeriodic c f := by
    intro z
    have h1 := hw.periodic r hr z
    have h2 := hw.periodic s hs z
    simp only [hf, h1, h2]
  let α0 : Sob.Idx 2 3 := Sob.Idx.zero
  let αq : Sob.Idx 2 3 := Sob.Idx.ofList [0] (by norm_num)
  let αη : Sob.Idx 2 3 := Sob.Idx.ofList [1] (by norm_num)
  let αηq : Sob.Idx 2 3 := Sob.Idx.ofList [1, 0] (by norm_num)
  have hw0 : (Sob.cylinder c).word α0 = [] := by
    simp [α0, Sob.TestDomain.word_eq_map]
  have hwq : (Sob.cylinder c).word αq = [(1, 0)] := by
    simp [αq, Sob.TestDomain.word_eq_map, Sob.cylinder_dir, Sob.cylDir]
  have hwη : (Sob.cylinder c).word αη = [(0, 1)] := by
    simp [αη, Sob.TestDomain.word_eq_map, Sob.cylinder_dir, Sob.cylDir]
  have hwηq : (Sob.cylinder c).word αηq = [(0, 1), (1, 0)] := by
    simp [αηq, Sob.TestDomain.word_eq_map, Sob.cylinder_dir, Sob.cylDir]
  have t0 := advSup_term hw hr hs α0 j
  have tq := advSup_term hw hr hs αq j
  have tη := advSup_term hw hr hs αη j
  have tηq := advSup_term hw hr hs αηq j
  rw [hw0] at t0
  rw [hwq] at tq
  rw [hwη] at tη
  rw [hwηq] at tηq
  have hdq : Differentiable ℝ (GaussianVortex.partialX f) :=
    (B0151.contDiff_partialX_infty hsm).differentiable (by simp)
  have eq1 : Sob.iterD [(1, 0)] f = GaussianVortex.partialX f := by
    funext z
    simp [Sob.iterD, B0151.partialX_eq_fderiv hd]
  have eη : Sob.iterD [(0, 1)] f = GaussianVortex.partialY f := by
    funext z
    simp [Sob.iterD, B0151.partialY_eq_fderiv hd]
  have eηq : Sob.iterD [(0, 1), (1, 0)] f =
      GaussianVortex.partialY (GaussianVortex.partialX f) := by
    funext z
    have heq : (fun x => fderiv ℝ f x (1, 0)) = GaussianVortex.partialX f :=
      funext fun x => (B0151.partialX_eq_fderiv hd x).symm
    simp [Sob.iterD, heq, B0151.partialY_eq_fderiv hdq]
  rw [eq1] at tq
  rw [eη] at tη
  rw [eηq] at tηq
  have key := smooth_H2_enorm_le_cell hc1 (hsm.of_le (by simp)) hper t0.1 tq.1 tη.1 tηq.1 z
  have hb : ‖f z‖ₑ ≤ ENNReal.ofReal (12 * X) := by
    refine key.trans ?_
    have hs4 : eLpNorm f 2 (Cyl.cellμ c) + eLpNorm (GaussianVortex.partialX f) 2 (Cyl.cellμ c) +
        eLpNorm (GaussianVortex.partialY f) 2 (Cyl.cellμ c) +
        eLpNorm (GaussianVortex.partialY (GaussianVortex.partialX f)) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal X + ENNReal.ofReal X + ENNReal.ofReal X + ENNReal.ofReal X := by
      gcongr
      · exact t0.2
      · exact tq.2
      · exact tη.2
      · exact tηq.2
    calc 3 * _ ≤ 3 * (ENNReal.ofReal X + ENNReal.ofReal X + ENNReal.ofReal X +
          ENNReal.ofReal X) := by gcongr
      _ = ENNReal.ofReal (12 * X) := by
        have hX0 : 0 ≤ X := norm_nonneg _
        rw [ENNReal.ofReal_mul (by norm_num)]
        have : (ENNReal.ofReal 12) = 3 * 4 := by
          rw [show (12 : ℝ) = 3 * 4 by norm_num, ENNReal.ofReal_mul (by norm_num)]
          simp
        rw [this]
        ring
  rw [← ofReal_norm] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb

theorem advLipSupDiff_proof : UnforcedLeray.Short.PartI.AdvLipSupDiff := by
  intro ν c T hν hc hc1 hT u hu w hw
  refine ⟨24, by norm_num, ?_⟩
  intro r hr s hs z
  have h0 := advSup_comp_le hc1 hw hr hs 0 z
  have h1 := advSup_comp_le hc1 hw hr hs 1 z
  have hn : ‖w r z - w s z‖ ≤ ‖(w r z - w s z) 0‖ + ‖(w r z - w s z) 1‖ := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg ((w r z - w s z) 0), abs_nonneg ((w r z - w s z) 1),
      sq_abs ((w r z - w s z) 0), sq_abs ((w r z - w s z) 1)]
  linarith

end UnforcedLeray.Short.PartI
