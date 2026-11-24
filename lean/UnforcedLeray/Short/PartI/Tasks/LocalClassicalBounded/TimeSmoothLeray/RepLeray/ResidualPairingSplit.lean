import UnforcedLeray.Short.PartI.Sub.T02_1_4_6

/-!
# Part I, task `PartI:T02/1/4/6`, leaf R7: splitting the momentum-residual integral

Source of record: `the November 2 reference manuscript`, lines 261-288.
Target: `residualPairingSplit : ResidualPairingSplit` (`Short/PartI/Sub/T02_1_4_6.lean`).

Route.
* Pointwise, `momentumResidual ν w 0 s z = ∂ₜw + (w·∇)w - ν Δw`, because the gradient of the
  zero pressure vanishes (`gradS (fun _ => 0) z = 0`).  Pairing with `φ z` is linear.
* The three integrands are continuous in `z`.  `∂ₜ w s` is the `fderiv` of the joint map applied
  to `(1,0)` on the open set `(0,T) × ℝ²`.  `w s` is `C^∞`, so `advection` and `vecLaplacian` of
  it are continuous.  `φ` is continuous.
* Each integrand vanishes for `|η| > R` because `φ` does, so it is integrable on the cell
  (`Cyl.VanishesOutside.integrableOn_cell`).
* The cell integral is then split with `integral_sub`, `integral_add`, `integral_const_mul`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-! ### Calculus helpers for `partialQ` and `partialEta` -/

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rps_cd_two {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
  rw [one_add_one_eq_two]
  exact hf.of_le (by norm_num)

theorem rps_cd_one_pQ {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (Cyl.partialQ f) :=
  Cyl.contDiff_partialQ (n := 1) (rps_cd_two hf)

theorem rps_cd_one_pE {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (Cyl.partialEta f) :=
  Cyl.contDiff_partialEta (n := 1) (rps_cd_two hf)

theorem rps_partialQ_cont {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialQ f) :=
  (rps_cd_one_pQ hf).continuous

theorem rps_partialEta_cont {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialEta f) :=
  (rps_cd_one_pE hf).continuous

theorem rps_partialQQ_cont {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialQ (Cyl.partialQ f)) := by
  have h1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialQ f) := by
    rw [zero_add]
    exact rps_cd_one_pQ hf
  exact (Cyl.contDiff_partialQ (n := 0) h1).continuous

theorem rps_partialEE_cont {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialEta (Cyl.partialEta f)) := by
  have h1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialEta f) := by
    rw [zero_add]
    exact rps_cd_one_pE hf
  exact (Cyl.contDiff_partialEta (n := 0) h1).continuous

end Calc

/-! ### Smoothness and continuity of the spatial operators on `Vec`-valued fields -/

theorem rps_comp {u : Plane → Vec} (i : Fin 2) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x => u x i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)).comp hu

theorem rps_toVec_cont : Continuous Train.toVec :=
  Train.toVecL.continuous

theorem rps_lapS_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun z => Train.lapS f z) := by
  unfold Train.lapS
  exact (rps_partialQQ_cont hf).add (rps_partialEE_cont hf)

theorem rps_vecLaplacian_cont {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun z => Train.vecLaplacian u z) := by
  unfold Train.vecLaplacian
  exact rps_toVec_cont.comp
    ((rps_lapS_cont (rps_comp 0 hu)).prodMk (rps_lapS_cont (rps_comp 1 hu)))

theorem rps_advection_cont {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun z => Train.advection u z) := by
  have a0 : Continuous (fun z => u z 0) := (rps_comp 0 hu).continuous
  have a1 : Continuous (fun z => u z 1) := (rps_comp 1 hu).continuous
  have q0 : Continuous (fun z => Cyl.partialQ (fun w => u w 0) z) :=
    rps_partialQ_cont (rps_comp 0 hu)
  have e0 : Continuous (fun z => Cyl.partialEta (fun w => u w 0) z) :=
    rps_partialEta_cont (rps_comp 0 hu)
  have q1 : Continuous (fun z => Cyl.partialQ (fun w => u w 1) z) :=
    rps_partialQ_cont (rps_comp 1 hu)
  have e1 : Continuous (fun z => Cyl.partialEta (fun w => u w 1) z) :=
    rps_partialEta_cont (rps_comp 1 hu)
  unfold Train.advection
  exact rps_toVec_cont.comp
    (((a0.mul q0).add (a1.mul e0)).prodMk ((a0.mul q1).add (a1.mul e1)))

/-- The gradient of the zero pressure vanishes. -/
theorem rps_gradS_zero (z : Plane) : Train.gradS (fun _ : Plane => (0 : ℝ)) z = 0 := by
  have h0 : Cyl.partialQ (fun _ : Plane => (0 : ℝ)) z = 0 := by
    simp [Cyl.partialQ]
  have h1 : Cyl.partialEta (fun _ : Plane => (0 : ℝ)) z = 0 := by
    simp [Cyl.partialEta]
  unfold Train.gradS
  rw [h0, h1]
  exact map_zero Train.toVecL

/-! ### The time derivative of the joint map -/

theorem rps_hasDerivAt {T : ℝ} {w : ℝ → Plane → Vec}
    (hw : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) T) (a : Plane) :
    HasDerivAt (fun t : ℝ => w t a)
      (fderiv ℝ (fun y : ℝ × Plane => w y.1 y.2) (x, a) (1, 0)) x := by
  have hUopen : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hUsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ⊆ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    prod_mono Ioo_subset_Icc_self (subset_refl _)
  have hU : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ∈ 𝓝 (x, a) :=
    hUopen.mem_nhds (mem_prod.2 ⟨hx, mem_univ a⟩)
  have hGa : ContDiffAt ℝ ∞ (fun y : ℝ × Plane => w y.1 y.2) (x, a) :=
    (hw.mono hUsub).contDiffAt hU
  have hGd : HasFDerivAt (fun y : ℝ × Plane => w y.1 y.2)
      (fderiv ℝ (fun y : ℝ × Plane => w y.1 y.2) (x, a)) (x, a) :=
    (hGa.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((t, a) : ℝ × Plane)) ((1 : ℝ), (0 : Plane)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x a)
  exact hGd.comp_hasDerivAt x hline

theorem rps_fderiv_cont {T : ℝ} {w : ℝ → Plane → Vec}
    (hw : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    Continuous (fun a : Plane => fderiv ℝ (fun y : ℝ × Plane => w y.1 y.2) (s, a) (1, 0)) := by
  have hUopen : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hUsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ⊆ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    prod_mono Ioo_subset_Icc_self (subset_refl _)
  have hDcont : ContinuousOn (fderiv ℝ (fun y : ℝ × Plane => w y.1 y.2))
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (hw.mono hUsub).continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hline : Continuous (fun a : Plane => ((s, a) : ℝ × Plane)) :=
    (continuous_const : Continuous fun _ : Plane => s).prodMk continuous_id
  have h1 : ContinuousOn
      (fun a : Plane => fderiv ℝ (fun y : ℝ × Plane => w y.1 y.2) (s, a)) univ :=
    hDcont.comp hline.continuousOn (fun a _ => mem_prod.2 ⟨hs, mem_univ a⟩)
  have h2 : ContinuousOn
      (fun a : Plane => fderiv ℝ (fun y : ℝ × Plane => w y.1 y.2) (s, a) (1, 0)) univ :=
    h1.clm_apply continuousOn_const
  exact continuousOn_univ.1 h2

theorem rps_deriv_cont_inner {T : ℝ} {w : ℝ → Plane → Vec}
    (hw : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => w x.1 x.2) (Icc (0 : ℝ) T ×ˢ univ))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) {φ : Plane → Vec} (hφ : Continuous φ) :
    Continuous (fun z : Plane => inner ℝ (deriv (fun t : ℝ => w t z) s) (φ z)) := by
  have hfun : (fun z : Plane => inner ℝ (deriv (fun t : ℝ => w t z) s) (φ z)) =
      fun z : Plane => inner ℝ (fderiv ℝ (fun y : ℝ × Plane => w y.1 y.2) (s, z) (1, 0)) (φ z) :=
    funext fun z => by rw [(rps_hasDerivAt hw hs z).deriv]
  rw [hfun]
  exact (rps_fderiv_cont hw hs).inner hφ

/-! ### Integrability on the cell -/

theorem rps_integrable (R c : ℝ) {f : Plane → ℝ} (hf : Continuous f)
    (h0 : ∀ z : Plane, R < |z.2| → f z = 0) :
    Integrable f (volume.restrict (Cyl.cell c)) :=
  Cyl.VanishesOutside.integrableOn_cell (R := R) (f := f) h0 hf c

/-! ### The splitting leaf -/

/-- **Leaf R7** (`ResidualPairingSplit`).  For a jointly smooth `w` and a smooth `φ` vanishing for
`|η|` large, the cell integral of `⟨momentumResidual ν w 0 s, φ⟩` is the sum of the cell integrals of
`⟨∂ₜw s, φ⟩`, `⟨(w s·∇)w s, φ⟩` and `-ν ⟨Δ(w s), φ⟩`. -/
theorem residualPairingSplit : ResidualPairingSplit := by
  unfold ResidualPairingSplit
  intro ν c T hc w hw hws s hs φ hφs hφR
  obtain ⟨R, hR⟩ := hφR
  have hsm : ContDiff ℝ ∞ (w s) := hws s (Ioo_subset_Icc_self hs)
  -- pointwise identity: the zero-pressure gradient drops out
  have hpt : ∀ z : Plane,
      inner ℝ (Train.momentumResidual ν w (fun _ _ => (0 : ℝ)) s z) (φ z) =
        inner ℝ (deriv (fun t : ℝ => w t z) s) (φ z) +
          inner ℝ (Train.advection (w s) z) (φ z) -
          ν * inner ℝ (Train.vecLaplacian (w s) z) (φ z) := by
    intro z
    have hg : Train.gradS (fun _ : Plane => (0 : ℝ)) z = 0 := rps_gradS_zero z
    simp only [Train.momentumResidual, hg, add_zero, inner_sub_left, inner_add_left,
      real_inner_smul_left]
  -- integrability of the three integrands on the cell
  have hF : Integrable (fun z : Plane => inner ℝ (deriv (fun t : ℝ => w t z) s) (φ z))
      (volume.restrict (Cyl.cell c)) :=
    rps_integrable R c (rps_deriv_cont_inner hw hs hφs.continuous)
      (fun z hz => by simp [hR z hz])
  have hG : Integrable (fun z : Plane => inner ℝ (Train.advection (w s) z) (φ z))
      (volume.restrict (Cyl.cell c)) :=
    rps_integrable R c ((rps_advection_cont hsm).inner hφs.continuous)
      (fun z hz => by simp [hR z hz])
  have hH : Integrable (fun z : Plane => inner ℝ (Train.vecLaplacian (w s) z) (φ z))
      (volume.restrict (Cyl.cell c)) :=
    rps_integrable R c ((rps_vecLaplacian_cont hsm).inner hφs.continuous)
      (fun z hz => by simp [hR z hz])
  have hFG : Integrable (fun z : Plane =>
      inner ℝ (deriv (fun t : ℝ => w t z) s) (φ z) + inner ℝ (Train.advection (w s) z) (φ z))
      (volume.restrict (Cyl.cell c)) := hF.add hG
  have hHν : Integrable (fun z : Plane =>
      ν * inner ℝ (Train.vecLaplacian (w s) z) (φ z)) (volume.restrict (Cyl.cell c)) :=
    hH.const_mul ν
  simp only [hpt]
  rw [integral_sub hFG hHν, integral_add hF hG, integral_const_mul]

end UnforcedLeray.Short.PartI
