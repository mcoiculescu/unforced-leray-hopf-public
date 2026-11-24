import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8.WeakDq

/-!
# `PartII-b:F5/2/2/1` (`FlatBvWeakLeibniz`): spacetime weak Leibniz rule for `flatBv`

Source of record: `the November 2 reference manuscript`, lines 2213-2239.
The unprojected interaction `flatBv tr b0' b0q b0η` is a sum of products
`(smooth coefficient) * (profile component)`, with the coefficients given by the train velocity
`tr.v` and its first and second plane derivatives. The weak `q`- and `η`-derivatives are obtained
from the scalar product rule for weak derivatives, applied term by term.

The velocity is only smooth on the half-space `s > 0` (`IsTrain.smooth_v` is `ContDiffOn` on
`Ici 0 ×ˢ univ`), and test functions are supported there, so the product rule is proved for
coefficients that are `ContDiffOn` on the open set `U0 = Ioi 0 ×ˢ univ`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

namespace FlatBvWL

/-- Local copy of `vGrad` (the `T16_2` definition; that module is not imported because its import
chain re-declares `phase_chart_bochner`). -/
noncomputable def vGrad (v : Coord → Fin 3 → ℝ) (ψ : Coord → ℝ) (x : Coord) : ℝ :=
  ∑ j : Fin 3, v x j * cpd j ψ x

theorem contDiff_vQ0 (j : Fin 3) : ContDiff ℝ ∞ (fun y : Coord => vQ0 y j) := by
  fin_cases j
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop

theorem contDiff_vEta (j : Fin 3) : ContDiff ℝ ∞ (fun y : Coord => vEta y j) := by
  fin_cases j
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ)); fun_prop

/-- The open half-space `s > 0` where test functions live. -/
abbrev U0 : Set Coord := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))

lemma isOpen_U0 : IsOpen U0 := isOpen_Ioi.prod isOpen_univ

lemma mem_U0_iff {x : Coord} : x ∈ U0 ↔ 0 < x.1 := by
  simp [U0]

lemma not_mem_tsupport_of_nonpos {φ : Coord → ℝ} (hφ : IsCoordTest φ) {x : Coord}
    (hx : ¬ 0 < x.1) : x ∉ tsupport φ :=
  fun h => hx (mem_U0_iff.mp (hφ.supp h))

lemma coordTranspose_eq_zero_of_not_mem {v : Coord → Fin 3 → ℝ} (d : Coord → ℝ)
    {φ : Coord → ℝ} {x : Coord} (hx : x ∉ tsupport φ) :
    coordTranspose v d φ x = 0 := by
  have hj : ∀ j : Fin 3, cpd j (fun y => v y j * φ y) x = 0 := by
    intro j
    have hx' : x ∉ tsupport (fun y => v y j * φ y) :=
      fun h => hx (tsupport_mul_subset_right h)
    simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx']
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [coordTranspose, hj, hφx]

lemma cs_test_U {ψ φ : Coord → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U0) (hφ : IsCoordTest φ) :
    IsCoordTest (fun x => ψ x * φ x) := by
  refine ⟨?_, hφ.compact.mul_left, tsupport_mul_subset_right.trans hφ.supp⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact (hψ.contDiffAt (isOpen_U0.mem_nhds (hφ.supp hx))).mul hφ.smooth.contDiffAt
  · have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
    refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coord => (0 : ℝ)) x).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

lemma cpd_contDiffOn {ψ : Coord → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U0) (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun y => cpd j ψ y) U0 := by
  unfold cpd
  exact (hψ.fderiv_of_isOpen isOpen_U0 (by simp)).clm_apply contDiffOn_const

lemma vGrad_contDiffOn {v : Coord → Fin 3 → ℝ} (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => v y j))
    {ψ : Coord → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U0) : ContDiffOn ℝ ∞ (vGrad v ψ) U0 := by
  have heq : vGrad v ψ = fun x => v x 0 * cpd 0 ψ x + v x 1 * cpd 1 ψ x + v x 2 * cpd 2 ψ x := by
    funext x
    unfold vGrad
    rw [Fin.sum_univ_three]
  rw [heq]
  exact (((hv 0).contDiffOn.mul (cpd_contDiffOn hψ 0)).add
    ((hv 1).contDiffOn.mul (cpd_contDiffOn hψ 1))).add
    ((hv 2).contDiffOn.mul (cpd_contDiffOn hψ 2))

lemma cpd_mul_at {f g : Coord → ℝ} {x : Coord} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    cpd j (fun y => f y * g y) x = f x * cpd j g x + g x * cpd j f x := by
  unfold cpd
  have h := fderiv_mul hf hg
  rw [show (fun y => f y * g y) = f * g from rfl, h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma coordTranspose_mul_U {v : Coord → Fin 3 → ℝ} (d : Coord → ℝ)
    (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => v y j))
    {ψ φ : Coord → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U0) (hφ : IsCoordTest φ) (x : Coord) :
    coordTranspose v d (fun y => ψ y * φ y) x =
      ψ x * coordTranspose v d φ x - vGrad v ψ x * φ x := by
  by_cases hx : x ∈ tsupport φ
  · have hxU : x ∈ U0 := hφ.supp hx
    have hψd : DifferentiableAt ℝ ψ x :=
      (hψ.contDiffAt (isOpen_U0.mem_nhds hxU)).differentiableAt (by simp)
    have hφd : DifferentiableAt ℝ φ x := (hφ.smooth.differentiable (by simp)) x
    have hvd : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => v y j) x :=
      fun j => ((hv j).differentiable (by simp)) x
    have hj : ∀ j : Fin 3, cpd j (fun y => v y j * (ψ y * φ y)) x =
        cpd j ψ x * (v x j * φ x) + ψ x * cpd j (fun y => v y j * φ y) x := by
      intro j
      rw [cpd_mul_at (f := fun y => v y j) (g := fun y => ψ y * φ y) (hvd j) (hψd.mul hφd) j,
        cpd_mul_at hψd hφd j, cpd_mul_at (hvd j) hφd j]
      ring
    simp only [coordTranspose, vGrad, Fin.sum_univ_three]
    rw [hj 0, hj 1, hj 2]
    ring
  · have hx' : x ∉ tsupport (fun y => ψ y * φ y) := fun h => hx (tsupport_mul_subset_right h)
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [coordTranspose_eq_zero_of_not_mem (v := v) d hx',
      coordTranspose_eq_zero_of_not_mem (v := v) d hx, hφx]
    simp

/-- Scalar product rule for weak derivatives with a coefficient `ψ` that is smooth on `s > 0`. -/
lemma hasWeakFO_smul_U {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => v y j))
    {ψ : Coord → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U0)
    {u Du Eu : Coord → ℂ} (hD : HasWeakFO v d u Du) (hE : HasWeakFO vEta dZero u Eu) :
    HasWeakFO v d (fun x => (ψ x : ℂ) * u x)
      (fun x => (ψ x : ℂ) * Du x + (vGrad v ψ x : ℂ) * u x) := by
  have hvg : ContDiffOn ℝ ∞ (vGrad v ψ) U0 := vGrad_contDiffOn hv hψ
  have key : ∀ φ : Coord → ℝ, IsCoordTest φ → ∀ x : Coord,
      ((ψ x : ℂ) * u x) * (coordTranspose v d φ x : ℂ) =
        u x * (coordTranspose v d (fun y => ψ y * φ y) x : ℂ) +
          u x * ((vGrad v ψ x * φ x : ℝ) : ℂ) := by
    intro φ hφ x
    rw [coordTranspose_mul_U d hv hψ hφ x]
    push_cast
    ring
  have hpt : ∀ φ : Coord → ℝ, ∀ x : Coord,
      ((ψ x : ℂ) * Du x + (vGrad v ψ x : ℂ) * u x) * (φ x : ℂ) =
        Du x * ((ψ x * φ x : ℝ) : ℂ) + u x * ((vGrad v ψ x * φ x : ℝ) : ℂ) := by
    intro φ x
    push_cast
    ring
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have i1 := (hD.1 _ (cs_test_U hψ hφ)).1
    have i3 := integrable_mul_coordTest hE (cs_test_U hvg hφ)
    exact (i1.add i3).congr (ae_of_all _ fun x => (key φ hφ x).symm)
  · have i2 := (hD.1 _ (cs_test_U hψ hφ)).2
    have i3 := integrable_mul_coordTest hE (cs_test_U hvg hφ)
    exact (i2.add i3).congr (ae_of_all _ fun x => (hpt φ x).symm)
  · dsimp only
    have i1 := (hD.1 _ (cs_test_U hψ hφ)).1
    have i2 := (hD.1 _ (cs_test_U hψ hφ)).2
    have i3 := integrable_mul_coordTest hE (cs_test_U hvg hφ)
    rw [integral_congr_ae (ae_of_all _ fun x => hpt φ x),
      integral_congr_ae (ae_of_all _ fun x => key φ hφ x), integral_add i2 i3,
      integral_add i1 i3, hD.2 _ (cs_test_U hψ hφ)]

lemma hasWeakFO_add' {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u1 u2 g1 g2 : Coord → ℂ}
    (h1 : HasWeakFO v d u1 g1) (h2 : HasWeakFO v d u2 g2) :
    HasWeakFO v d (fun x => u1 x + u2 x) (fun x => g1 x + g2 x) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have hi := ((h1.1 φ hφ).1).add ((h2.1 φ hφ).1)
    exact hi.congr (Eventually.of_forall fun x => by dsimp; ring)
  · have hi := ((h1.1 φ hφ).2).add ((h2.1 φ hφ).2)
    exact hi.congr (Eventually.of_forall fun x => by dsimp; ring)
  · have he1 : (fun x => (g1 x + g2 x) * (φ x : ℂ)) =
        fun x => g1 x * (φ x : ℂ) + g2 x * (φ x : ℂ) := by ext x; ring
    have he2 : (fun x => (u1 x + u2 x) * (coordTranspose v d φ x : ℂ)) =
        fun x => u1 x * (coordTranspose v d φ x : ℂ) + u2 x * (coordTranspose v d φ x : ℂ) := by
      ext x; ring
    rw [he1, he2, integral_add (h1.1 φ hφ).2 (h2.1 φ hφ).2,
      integral_add (h1.1 φ hφ).1 (h2.1 φ hφ).1, h1.2 φ hφ, h2.2 φ hφ]

/-- Transfer of weak derivatives across values that agree for `s > 0`. -/
lemma hasWeakFO_congr_ae {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u u' g g' : Coord → ℂ}
    (h : HasWeakFO v d u g)
    (hu : ∀ᵐ x : Coord, 0 < x.1 → u' x = u x) (hg : ∀ᵐ x : Coord, 0 < x.1 → g' x = g x) :
    HasWeakFO v d u' g' := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · refine (h.1 φ hφ).1.congr ?_
    filter_upwards [hu] with x hx
    by_cases h0 : 0 < x.1
    · simp [hx h0]
    · simp [coordTranspose_eq_zero_of_not_mem (v := v) d (not_mem_tsupport_of_nonpos hφ h0)]
  · refine (h.1 φ hφ).2.congr ?_
    filter_upwards [hg] with x hx
    by_cases h0 : 0 < x.1
    · simp [hx h0]
    · simp [image_eq_zero_of_notMem_tsupport (not_mem_tsupport_of_nonpos hφ h0)]
  · have e1 : (fun x => g' x * (φ x : ℂ)) =ᵐ[volume] (fun x => g x * (φ x : ℂ)) := by
      filter_upwards [hg] with x hx
      by_cases h0 : 0 < x.1
      · simp [hx h0]
      · simp [image_eq_zero_of_notMem_tsupport (not_mem_tsupport_of_nonpos hφ h0)]
    have e2 : (fun x => u' x * (coordTranspose v d φ x : ℂ)) =ᵐ[volume]
        (fun x => u x * (coordTranspose v d φ x : ℂ)) := by
      filter_upwards [hu] with x hx
      by_cases h0 : 0 < x.1
      · simp [hx h0]
      · simp [coordTranspose_eq_zero_of_not_mem (v := v) d (not_mem_tsupport_of_nonpos hφ h0)]
    rw [integral_congr_ae e1, integral_congr_ae e2]
    exact h.2 φ hφ

lemma hasWeakFO_of_ae {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b b' g : CProf}
    (hb : ∀ᵐ x : Coord, 0 < x.1 → b' x = b x) (h : HasWeakVec v d b g) (k : Fin 2) :
    HasWeakFO v d (fun x => b' x k) (fun x => g x k) :=
  hasWeakFO_congr_ae (h k) (hb.mono fun x hx h0 => by show b' x k = b x k; rw [hx h0])
    (ae_of_all _ fun x _ => rfl)

/-! ## The train components and their plane derivatives -/

/-- Component `k` of the train velocity as a scalar function on `Coord`. -/
noncomputable def gC {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) : Coord → ℝ :=
  fun y => tr.v y.1 y.2 k

/-- The plane derivative of `gC` in direction `d`, as a function on `Coord`. -/
noncomputable def gD {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) (d : ℝ × ℝ) : Coord → ℝ :=
  fun y => fderiv ℝ (gC tr k) y (0, d)

lemma diffAt_of_U0 {f : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f U0) {x : Coord} (hx : 0 < x.1) :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt (isOpen_U0.mem_nhds (mem_U0_iff.mpr hx))).differentiableAt (by simp)

lemma gC_contDiffOn {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) :
    ContDiffOn ℝ ∞ (gC tr k) U0 := by
  have hp : ContDiffOn ℝ ∞ (fun y : Coord => tr.v y.1 y.2) U0 :=
    tr.isTrain.smooth_v.mono (fun y hy =>
      ⟨Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp (Set.mem_prod.mp hy).1)), Set.mem_univ _⟩)
  have hproj : ContDiff ℝ ∞ (fun f : Fin 2 → ℝ => f k) := by fun_prop
  exact (hproj.comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := ∞))).comp_contDiffOn hp

lemma gD_contDiffOn {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) (d : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (gD tr k d) U0 := by
  unfold gD
  exact ((gC_contDiffOn tr k).fderiv_of_isOpen isOpen_U0 (by simp)).clm_apply contDiffOn_const

lemma cpd_plane {G : Coord → ℝ} {x : Coord} (hG : DifferentiableAt ℝ G x) (e : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => G (x.1, z)) x.2 e = fderiv ℝ G x (0, e) := by
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => (x.1, z))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have h2 := hG.hasFDerivAt.comp x.2 h1
  have h3 : fderiv ℝ (fun z : ℝ × ℝ => G (x.1, z)) x.2 =
      (fderiv ℝ G x).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := h2.fderiv
  rw [h3]
  simp

lemma trD1_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) (d : ℝ × ℝ) (k : Fin 2) {x : Coord}
    (hx : 0 < x.1) : trD1 tr d x.1 x.2 k = fderiv ℝ (gC tr k) x (0, d) := by
  unfold trD1
  exact cpd_plane (diffAt_of_U0 (gC_contDiffOn tr k) hx) d

lemma gD_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) (d : ℝ × ℝ) {x : Coord}
    (hx : 0 < x.1) : gD tr k d x = trD1 tr d x.1 x.2 k :=
  (trD1_eq tr d k hx).symm

lemma trD2_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) (d e : ℝ × ℝ) (k : Fin 2) {x : Coord}
    (hx : 0 < x.1) : trD2 tr d e x.1 x.2 k = fderiv ℝ (gD tr k d) x (0, e) := by
  have hfun : (fun w : ℝ × ℝ => trD1 tr d x.1 w k) = (fun w => gD tr k d (x.1, w)) := by
    funext w
    exact trD1_eq tr d k (x := (x.1, w)) hx
  have hD := diffAt_of_U0 (gD_contDiffOn tr k d) hx
  calc trD2 tr d e x.1 x.2 k = fderiv ℝ (fun w => trD1 tr d x.1 w k) x.2 e := rfl
    _ = fderiv ℝ (fun w => gD tr k d (x.1, w)) x.2 e := by rw [hfun]
    _ = fderiv ℝ (gD tr k d) x (0, e) := cpd_plane hD e

lemma vGrad_vQ0 (ψ : Coord → ℝ) (x : Coord) :
    vGrad vQ0 ψ x = fderiv ℝ ψ x (0, (1, 0)) := by
  unfold vGrad
  rw [Fin.sum_univ_three]
  simp [vQ0, cpd, cdir]

lemma vGrad_vEta (ψ : Coord → ℝ) (x : Coord) :
    vGrad vEta ψ x = fderiv ℝ ψ x (0, (0, 1)) := by
  unfold vGrad
  rw [Fin.sum_univ_three]
  simp [vEta, cpd, cdir]

lemma vGQ_gC {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) {x : Coord} (hx : 0 < x.1) :
    vGrad vQ0 (gC tr k) x = trD1 tr (1, 0) x.1 x.2 k := by
  rw [vGrad_vQ0, trD1_eq tr (1, 0) k hx]

lemma vGQ_gD {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) (d : ℝ × ℝ) {x : Coord}
    (hx : 0 < x.1) : vGrad vQ0 (gD tr k d) x = trD2 tr d (1, 0) x.1 x.2 k := by
  rw [vGrad_vQ0, trD2_eq tr d (1, 0) k hx]

lemma vGE_gC {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) {x : Coord} (hx : 0 < x.1) :
    vGrad vEta (gC tr k) x = trD1 tr (0, 1) x.1 x.2 k := by
  rw [vGrad_vEta, trD1_eq tr (0, 1) k hx]

lemma vGE_gD {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) (d : ℝ × ℝ) {x : Coord}
    (hx : 0 < x.1) : vGrad vEta (gD tr k d) x = trD2 tr d (0, 1) x.1 x.2 k := by
  rw [vGrad_vEta, trD2_eq tr d (0, 1) k hx]

lemma flatBv_apply {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf) (x : Coord)
    (i : Fin 2) :
    flatBv tr b0' b0q b0η x i =
      ((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
        b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
        b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ) := rfl

lemma flatBvQ_apply {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d00 d10 : CProf)
    (x : Coord) (i : Fin 2) :
    flatBvQ tr b0' b0q b0η d00 d10 x i =
      ((trD1 tr (1, 0) x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 0 : ℝ) : ℂ) * d00 x i +
      ((trD1 tr (1, 0) x.1 x.2 1 : ℝ) : ℂ) * b0η x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * d10 x i +
      b0q x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
      b0' x 0 * ((trD2 tr (1, 0) (1, 0) x.1 x.2 i : ℝ) : ℂ) +
      b0q x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ) +
      b0' x 1 * ((trD2 tr (0, 1) (1, 0) x.1 x.2 i : ℝ) : ℂ) := rfl

lemma flatBvEta_apply {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η d01 d11 : CProf)
    (x : Coord) (i : Fin 2) :
    flatBvEta tr b0' b0q b0η d01 d11 x i =
      ((trD1 tr (0, 1) x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 0 : ℝ) : ℂ) * d01 x i +
      ((trD1 tr (0, 1) x.1 x.2 1 : ℝ) : ℂ) * b0η x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * d11 x i +
      b0η x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
      b0' x 0 * ((trD2 tr (1, 0) (0, 1) x.1 x.2 i : ℝ) : ℂ) +
      b0η x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ) +
      b0' x 1 * ((trD2 tr (0, 1) (0, 1) x.1 x.2 i : ℝ) : ℂ) := rfl

/-- `q`-component of the weak derivative. -/
lemma compQ {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0 b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf)
    (hab : ∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x)
    (hq0 : HasWeakVec vQ0 dZero b0 b0q) (he0 : HasWeakVec vEta dZero b0 b0η)
    (hQq : HasWeakVec vQ0 dZero b0q (D2 0 0)) (hQe : HasWeakVec vEta dZero b0q (D2 0 1))
    (hEq : HasWeakVec vQ0 dZero b0η (D2 1 0)) (hEe : HasWeakVec vEta dZero b0η (D2 1 1))
    (i : Fin 2) :
    HasWeakFO vQ0 dZero (fun x => flatBv tr b0' b0q b0η x i)
      (fun x => flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) x i) := by
  have hb0 : HasWeakFO vQ0 dZero (fun x => b0' x 0) (fun x => b0q x 0) :=
    hasWeakFO_of_ae hab hq0 0
  have hb1 : HasWeakFO vQ0 dZero (fun x => b0' x 1) (fun x => b0q x 1) :=
    hasWeakFO_of_ae hab hq0 1
  have hc0 : HasWeakFO vEta dZero (fun x => b0' x 0) (fun x => b0η x 0) :=
    hasWeakFO_of_ae hab he0 0
  have hc1 : HasWeakFO vEta dZero (fun x => b0' x 1) (fun x => b0η x 1) :=
    hasWeakFO_of_ae hab he0 1
  have T1 := hasWeakFO_smul_U contDiff_vQ0 (gC_contDiffOn tr 0) (hQq i) (hQe i)
  have T2 := hasWeakFO_smul_U contDiff_vQ0 (gC_contDiffOn tr 1) (hEq i) (hEe i)
  have T3 := hasWeakFO_smul_U contDiff_vQ0 (gD_contDiffOn tr i (1, 0)) hb0 hc0
  have T4 := hasWeakFO_smul_U contDiff_vQ0 (gD_contDiffOn tr i (0, 1)) hb1 hc1
  refine hasWeakFO_congr_ae (hasWeakFO_add' (hasWeakFO_add' (hasWeakFO_add' T1 T2) T3) T4)
    (ae_of_all _ fun x hx => ?_) (ae_of_all _ fun x hx => ?_)
  · dsimp only
    rw [flatBv_apply, gD_eq tr i (1, 0) hx, gD_eq tr i (0, 1) hx]
    simp only [gC]
    ring
  · dsimp only
    rw [flatBvQ_apply, vGQ_gC tr 0 hx, vGQ_gC tr 1 hx, vGQ_gD tr i (1, 0) hx,
      vGQ_gD tr i (0, 1) hx, gD_eq tr i (1, 0) hx, gD_eq tr i (0, 1) hx]
    simp only [gC]
    ring

/-- `η`-component of the weak derivative. -/
lemma compE {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0 b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf)
    (hab : ∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x)
    (hq0 : HasWeakVec vQ0 dZero b0 b0q) (he0 : HasWeakVec vEta dZero b0 b0η)
    (hQq : HasWeakVec vQ0 dZero b0q (D2 0 0)) (hQe : HasWeakVec vEta dZero b0q (D2 0 1))
    (hEq : HasWeakVec vQ0 dZero b0η (D2 1 0)) (hEe : HasWeakVec vEta dZero b0η (D2 1 1))
    (i : Fin 2) :
    HasWeakFO vEta dZero (fun x => flatBv tr b0' b0q b0η x i)
      (fun x => flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) x i) := by
  have hb0 : HasWeakFO vEta dZero (fun x => b0' x 0) (fun x => b0η x 0) :=
    hasWeakFO_of_ae hab he0 0
  have hb1 : HasWeakFO vEta dZero (fun x => b0' x 1) (fun x => b0η x 1) :=
    hasWeakFO_of_ae hab he0 1
  have T1 := hasWeakFO_smul_U contDiff_vEta (gC_contDiffOn tr 0) (hQe i) (hQe i)
  have T2 := hasWeakFO_smul_U contDiff_vEta (gC_contDiffOn tr 1) (hEe i) (hEe i)
  have T3 := hasWeakFO_smul_U contDiff_vEta (gD_contDiffOn tr i (1, 0)) hb0 hb0
  have T4 := hasWeakFO_smul_U contDiff_vEta (gD_contDiffOn tr i (0, 1)) hb1 hb1
  refine hasWeakFO_congr_ae (hasWeakFO_add' (hasWeakFO_add' (hasWeakFO_add' T1 T2) T3) T4)
    (ae_of_all _ fun x hx => ?_) (ae_of_all _ fun x hx => ?_)
  · dsimp only
    rw [flatBv_apply, gD_eq tr i (1, 0) hx, gD_eq tr i (0, 1) hx]
    simp only [gC]
    ring
  · dsimp only
    rw [flatBvEta_apply, vGE_gC tr 0 hx, vGE_gC tr 1 hx, vGE_gD tr i (1, 0) hx,
      vGE_gD tr i (0, 1) hx, gD_eq tr i (1, 0) hx, gD_eq tr i (0, 1) hx]
    simp only [gC]
    ring

end FlatBvWL

open UnforcedLeray.Short.IIb.FlatBvWL in
theorem flatBvWeakLeibniz_proof : UnforcedLeray.Short.IIb.FlatBvWeakLeibniz := by
  intro ν c tr _hc b0 b0' b0q b0η D2 _ hab _ _ _ _ _ _ _ _ hq0 he0 hQq hQe hEq hEe
  exact ⟨fun i => compQ tr b0 b0' b0q b0η D2 hab hq0 he0 hQq hQe hEq hEe i,
    fun i => compE tr b0 b0' b0q b0η D2 hab hq0 he0 hQq hQe hEq hEe i⟩
