import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `PartII-b:F8/1/org/1` (`OrbitSmoothing.lean`): Parabolic `H¹ → H²` smoothing for cylinder Oseen orbits

Source of record: `the November 2 reference manuscript` (SP), lines 2296–2301:
differentiate `(short-bg:body-eq)` homogeneously twice; incompressibility, orthogonality of `P_0`,
and `(short-bg:train-uniform)` yield the cylinder energy hierarchy
`E_j' + ν E_{j+1} ≤ C ∑_{i ≤ j} E_i` (`j ≤ 2`), and the age-weighted Lyapunov functional of
`Sub/PartII-b_F8_1_org.lean` (`F8U.parabolic_multiplier_gronwall`,
`F8U.parabolic_sqrt_E2_le_of_hierarchy`) gives `CylOseenOrbitSmoothing`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace F8Sm

/-! ## 1. Cell `L²` inner product, norms, and component helpers -/

abbrev cellMeas (c : ℝ) : Measure B0579.Plane := volume.restrict (B0579.cell c)

lemma cell_eq_cylCell (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

lemma cellMeas_eq_cyl (c : ℝ) : cellMeas c = UnforcedLeray.Cyl.cellμ c := by
  simp [cellMeas, UnforcedLeray.Cyl.cellμ, cell_eq_cylCell]

lemma memLp_coord_cmerid {c : ℝ} {f : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) (k : Fin 2) :
    MemLp (fun y => f y k) 2 (cellMeas c) := by
  let hπ : CMerid →L[ℂ] ℂ := EuclideanSpace.proj k
  exact hπ.comp_memLp' hf

lemma norm_toLp_eq_cellL2 {c : ℝ} {f : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) :
    ‖hf.toLp f‖ = (F8U.cellL2 c f).toReal := by
  rw [Lp.norm_toLp]
  rfl

lemma integral_norm_sq_eq_cellL2_sq {c : ℝ} {f : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) :
    (∫ y in B0579.cell c, ‖f y‖ ^ 2) = (F8U.cellL2 c f).toReal ^ 2 := by
  have hself : (inner ℂ (hf.toLp f) (hf.toLp f) : ℂ) = ((‖hf.toLp f‖ ^ 2 : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K]
  have hdef : (inner ℂ (hf.toLp f) (hf.toLp f) : ℂ) =
      ∫ y, inner ℂ (hf.toLp f y) (hf.toLp f y) ∂cellMeas c :=
    L2.inner_def (𝕜 := ℂ) (hf.toLp f) (hf.toLp f)
  have hre : (∫ y, inner ℂ (hf.toLp f y) (hf.toLp f y) ∂cellMeas c).re =
      ‖hf.toLp f‖ ^ 2 := by
    rw [← hdef, hself, Complex.ofReal_re]
  have hint0 := L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hf.toLp f)
  have hae : (fun y => (inner ℂ (hf.toLp f y) (hf.toLp f y) : ℂ).re) =ᵐ[cellMeas c]
      fun y => ‖f y‖ ^ 2 := by
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [hy]
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (f y)
  have hre_int : (∫ y, (inner ℂ (hf.toLp f y) (hf.toLp f y) : ℂ) ∂cellMeas c).re =
      ∫ y, ((inner ℂ (hf.toLp f y) (hf.toLp f y) : ℂ)).re ∂cellMeas c := by
    simpa only [RCLike.re_to_complex] using (integral_re hint0).symm
  rw [← norm_toLp_eq_cellL2 hf, ← hre, hre_int]
  exact (integral_congr_ae hae).symm

lemma integrableOn_inner_cell {c : ℝ} {f g : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) (hg : MemLp g 2 (cellMeas c)) :
    IntegrableOn (fun y => (inner ℂ (f y) (g y) : ℂ)) (B0579.cell c) volume := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y hyf hyg
  rw [hyf, hyg]

lemma integral_inner_eq_L2_inner {c : ℝ} {f g : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) (hg : MemLp g 2 (cellMeas c)) :
    (∫ y in B0579.cell c, (inner ℂ (f y) (g y) : ℂ)) =
      inner ℂ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def (𝕜 := ℂ)]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y hyf hyg
  rw [hyf, hyg]

lemma norm_integral_inner_le {c : ℝ} {f g : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) (hg : MemLp g 2 (cellMeas c)) :
    ‖∫ y in B0579.cell c, (inner ℂ (f y) (g y) : ℂ)‖ ≤
      (F8U.cellL2 c f).toReal * (F8U.cellL2 c g).toReal := by
  rw [integral_inner_eq_L2_inner hf hg, ← norm_toLp_eq_cellL2 hf, ← norm_toLp_eq_cellL2 hg]
  exact norm_inner_le_norm (hf.toLp f) (hg.toLp g)

lemma abs_re_integral_inner_le {c : ℝ} {f g : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) (hg : MemLp g 2 (cellMeas c)) :
    |(∫ y in B0579.cell c, (inner ℂ (f y) (g y) : ℂ)).re| ≤
      (F8U.cellL2 c f).toReal * (F8U.cellL2 c g).toReal :=
  (Complex.abs_re_le_norm _).trans (norm_integral_inner_le hf hg)

/-! ## 2. Open-strip smoothness, derivative symmetry, and periodicity -/

def stripSet (σ : ℝ) : Set Coord := Ioo σ (σ + 2) ×ˢ univ

lemma isOpen_stripSet (σ : ℝ) : IsOpen (stripSet σ) :=
  isOpen_Ioo.prod isOpen_univ

lemma mem_stripSet {σ τ : ℝ} (hτ : τ ∈ Ioo σ (σ + 2)) (y : B0579.Plane) :
    (τ, y) ∈ stripSet σ :=
  ⟨hτ, trivial⟩

lemma contDiffOn_fderiv_dir {σ : ℝ} {f : CProf}
    (hf : ContDiffOn ℝ ∞ f (stripSet σ)) (d : Coord) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x d) (stripSet σ) := by
  intro x hx
  have hfa : ContDiffAt ℝ ∞ f x := hf.contDiffAt ((isOpen_stripSet σ).mem_nhds hx)
  exact ((hfa.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

lemma contDiffOn_pd {σ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (F8U.pd i f) (stripSet σ) :=
  contDiffOn_fderiv_dir hf (F8U.sdir i)

lemma contDiffOn_ps {σ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ)) :
    ContDiffOn ℝ ∞ (F8U.ps f) (stripSet σ) :=
  contDiffOn_fderiv_dir hf (1, (0, 0))

lemma contDiffOn_pdIter {σ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ)) :
    ∀ {n : ℕ} (α : Fin n → Fin 2), ContDiffOn ℝ ∞ (F8U.pdIter α f) (stripSet σ)
  | 0, _ => hf
  | _ + 1, α => contDiffOn_pd (contDiffOn_pdIter hf (Fin.tail α)) (α 0)

def lapProf (w : CProf) : CProf :=
  fun x => F8U.pd 0 (F8U.pd 0 w) x + F8U.pd 1 (F8U.pd 1 w) x

lemma contDiffOn_lapProf {σ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ)) :
    ContDiffOn ℝ ∞ (lapProf f) (stripSet σ) :=
  (contDiffOn_pd (contDiffOn_pd hf 0) 0).add (contDiffOn_pd (contDiffOn_pd hf 1) 1)

lemma fderiv_dir_comm {σ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    {x : Coord} (hx : x ∈ stripSet σ) (u v : Coord) :
    fderiv ℝ (fun y => fderiv ℝ f y u) x v = fderiv ℝ (fun y => fderiv ℝ f y v) x u := by
  have hfa : ContDiffAt ℝ ∞ f x := hf.contDiffAt ((isOpen_stripSet σ).mem_nhds hx)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfa.fderiv_right (m := (1 : ℕ)) (by simp)).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (fun y => fderiv ℝ f y u)
      ((ContinuousLinearMap.apply ℝ CMerid u).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ CMerid u).hasFDerivAt.comp x hfd.hasFDerivAt
  have h2 : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ CMerid v).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ CMerid v).hasFDerivAt.comp x hfd.hasFDerivAt
  rw [h1.fderiv, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact (hfa.isSymmSndFDerivAt (by simp)).eq v u

lemma pd_comm {σ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    {x : Coord} (hx : x ∈ stripSet σ) (i j : Fin 2) :
    F8U.pd i (F8U.pd j f) x = F8U.pd j (F8U.pd i f) x :=
  fderiv_dir_comm hf hx (F8U.sdir j) (F8U.sdir i)

lemma ps_pd_comm {σ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    {x : Coord} (hx : x ∈ stripSet σ) (i : Fin 2) :
    F8U.ps (F8U.pd i f) x = F8U.pd i (F8U.ps f) x :=
  fderiv_dir_comm hf hx (F8U.sdir i) (1, (0, 0))

lemma ps_add_at {σ : ℝ} {f g : CProf}
    (hf : ContDiffOn ℝ ∞ f (stripSet σ)) (hg : ContDiffOn ℝ ∞ g (stripSet σ))
    {x : Coord} (hx : x ∈ stripSet σ) :
    F8U.ps (fun y => f y + g y) x = F8U.ps f x + F8U.ps g x := by
  have hda : DifferentiableAt ℝ f x :=
    (hf.contDiffAt ((isOpen_stripSet σ).mem_nhds hx)).differentiableAt (by simp)
  have hdb : DifferentiableAt ℝ g x :=
    (hg.contDiffAt ((isOpen_stripSet σ).mem_nhds hx)).differentiableAt (by simp)
  unfold F8U.ps
  change fderiv ℝ (f + g) x (1, (0, 0)) = _
  rw [(hda.hasFDerivAt.add hdb.hasFDerivAt).fderiv, _root_.add_apply]

lemma ps_lapProf_eq {σ : ℝ} {w : CProf} (hw : ContDiffOn ℝ ∞ w (stripSet σ))
    {x : Coord} (hx : x ∈ stripSet σ) :
    F8U.ps (lapProf w) x =
      F8U.ps (F8U.pd 0 (F8U.pd 0 w)) x + F8U.ps (F8U.pd 1 (F8U.pd 1 w)) x :=
  ps_add_at (contDiffOn_pd (contDiffOn_pd hw 0) 0) (contDiffOn_pd (contDiffOn_pd hw 1) 1) hx

lemma periodic_fderiv_dir {σ c : ℝ} {f : CProf}
    (hper : ∀ x : Coord, x.1 ∈ Ioo σ (σ + 2) → f (qShift c x) = f x)
    (d : Coord) :
    ∀ x : Coord, x.1 ∈ Ioo σ (σ + 2) →
      (fun y => fderiv ℝ f y d) (qShift c x) = fderiv ℝ f x d := by
  intro x hx
  have hshift : ∀ y : Coord, qShift c y = y + (0, (c, 0)) := by
    intro y; ext <;> simp [qShift]
  have hev : (fun y : Coord => f (y + (0, (c, 0)))) =ᶠ[𝓝 x] f := by
    filter_upwards [(isOpen_stripSet σ).mem_nhds ⟨hx, trivial⟩] with y hy
    rw [← hshift y]
    exact hper y hy.1
  have hcomp := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) ((0, (c, 0)) : Coord)
  rw [hev.fderiv_eq] at hcomp
  dsimp only
  rw [hshift x, ← hcomp]

/-! ## 3. Planar slice calculus, cell integration by parts, and solenoidality -/

def pdir (i : Fin 2) (G : B0579.Plane → CMerid) (y : B0579.Plane) : CMerid :=
  fderiv ℝ G y (B0579.dir i)

def plap (G : B0579.Plane → CMerid) (y : B0579.Plane) : CMerid :=
  pdir 0 (pdir 0 G) y + pdir 1 (pdir 1 G) y

lemma contDiff_pdir {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G) (i : Fin 2) :
    ContDiff ℝ ∞ (pdir i G) :=
  ((contDiff_infty_iff_fderiv.1 hG).2).clm_apply contDiff_const

lemma contDiff_plap {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (plap G) :=
  (contDiff_pdir (contDiff_pdir hG 0) 0).add (contDiff_pdir (contDiff_pdir hG 1) 1)

lemma pdir_comm {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G) (i j : Fin 2) (y : B0579.Plane) :
    pdir i (pdir j G) y = pdir j (pdir i G) y := by
  have hGa : ContDiffAt ℝ ∞ G y := hG.contDiffAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hGa.fderiv_right (m := (1 : ℕ)) (by simp)).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (pdir j G)
      ((ContinuousLinearMap.apply ℝ CMerid (B0579.dir j)).comp (fderiv ℝ (fderiv ℝ G) y)) y :=
    (ContinuousLinearMap.apply ℝ CMerid (B0579.dir j)).hasFDerivAt.comp y hfd.hasFDerivAt
  have h2 : HasFDerivAt (pdir i G)
      ((ContinuousLinearMap.apply ℝ CMerid (B0579.dir i)).comp (fderiv ℝ (fderiv ℝ G) y)) y :=
    (ContinuousLinearMap.apply ℝ CMerid (B0579.dir i)).hasFDerivAt.comp y hfd.hasFDerivAt
  change fderiv ℝ (pdir j G) y (B0579.dir i) = fderiv ℝ (pdir i G) y (B0579.dir j)
  rw [h1.fderiv, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact (hGa.isSymmSndFDerivAt (by simp)).eq (B0579.dir i) (B0579.dir j)

lemma pdir_add {F G : B0579.Plane → CMerid} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (i : Fin 2) :
    pdir i (fun y => F y + G y) = fun y => pdir i F y + pdir i G y := by
  funext y
  have hdF : DifferentiableAt ℝ F y := hF.contDiffAt.differentiableAt (by simp)
  have hdG : DifferentiableAt ℝ G y := hG.contDiffAt.differentiableAt (by simp)
  unfold pdir
  change fderiv ℝ (F + G) y (B0579.dir i) = _
  rw [(hdF.hasFDerivAt.add hdG.hasFDerivAt).fderiv, _root_.add_apply]

lemma plap_add {F G : B0579.Plane → CMerid} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    plap (fun y => F y + G y) = fun y => plap F y + plap G y := by
  funext y
  unfold plap
  rw [pdir_add hF hG 0, pdir_add (contDiff_pdir hF 0) (contDiff_pdir hG 0) 0,
    pdir_add hF hG 1, pdir_add (contDiff_pdir hF 1) (contDiff_pdir hG 1) 1]
  dsimp only
  abel

lemma plap_pdir_comm {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G) (m : Fin 2)
    (y : B0579.Plane) :
    plap (pdir m G) y = pdir m (plap G) y := by
  have hc0 : pdir 0 (pdir m G) = pdir m (pdir 0 G) := funext (pdir_comm hG 0 m)
  have hc00 : pdir 0 (pdir 0 (pdir m G)) y = pdir m (pdir 0 (pdir 0 G)) y := by
    rw [hc0, pdir_comm (contDiff_pdir hG 0) 0 m y]
  have hc1 : pdir 1 (pdir m G) = pdir m (pdir 1 G) := funext (pdir_comm hG 1 m)
  have hc11 : pdir 1 (pdir 1 (pdir m G)) y = pdir m (pdir 1 (pdir 1 G)) y := by
    rw [hc1, pdir_comm (contDiff_pdir hG 1) 1 m y]
  have hadd := congrFun (pdir_add (contDiff_pdir (contDiff_pdir hG 0) 0)
    (contDiff_pdir (contDiff_pdir hG 1) 1) m) y
  unfold plap
  rw [hadd, hc00, hc11]

lemma contDiff_slice {σ τ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    (hτ : τ ∈ Ioo σ (σ + 2)) :
    ContDiff ℝ ∞ (F8U.slice f τ) :=
  hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => mem_stripSet hτ y)

lemma pdir_slice_eq {σ τ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    (hτ : τ ∈ Ioo σ (σ + 2)) (i : Fin 2) :
    pdir i (F8U.slice f τ) = F8U.slice (F8U.pd i f) τ := by
  funext y
  have hfa : DifferentiableAt ℝ f (τ, y) :=
    (hf.contDiffAt ((isOpen_stripSet σ).mem_nhds (mem_stripSet hτ y))).differentiableAt (by simp)
  have hin : HasFDerivAt (fun z : B0579.Plane => (τ, z))
      ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := hfa.hasFDerivAt.comp y hin
  unfold pdir F8U.slice F8U.pd
  change fderiv ℝ (f ∘ Prod.mk τ) y (B0579.dir i) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    _root_.zero_apply, ContinuousLinearMap.id_apply]
  fin_cases i <;> rfl

lemma plap_slice_eq {σ τ : ℝ} {f : CProf} (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    (hτ : τ ∈ Ioo σ (σ + 2)) :
    plap (F8U.slice f τ) = F8U.slice (lapProf f) τ := by
  funext y
  unfold plap lapProf
  rw [pdir_slice_eq hf hτ 0, pdir_slice_eq (contDiffOn_pd hf 0) hτ 0,
    pdir_slice_eq hf hτ 1, pdir_slice_eq (contDiffOn_pd hf 1) hτ 1]
  rfl

lemma periodic_pdir {c : ℝ} {G : B0579.Plane → CMerid}
    (hper : UnforcedLeray.Cyl.IsPeriodic c G) (i : Fin 2) :
    UnforcedLeray.Cyl.IsPeriodic c (pdir i G) := by
  intro y
  have hfun : (fun z : B0579.Plane => G (z + ((c, 0) : B0579.Plane))) = G := by
    funext z
    have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
    rw [hz]
    exact hper z
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := y) ((c, 0) : B0579.Plane)
  rw [hfun] at h
  have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
  rw [hy] at h
  unfold pdir
  rw [← h]

lemma partialQ_coord_eq_pdir {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G)
    (k : Fin 2) (y : B0579.Plane) :
    UnforcedLeray.Cyl.partialQ (fun z => G z k) y = pdir 0 G y k := by
  let πk : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  have hd : Differentiable ℝ (fun z => G z k) :=
    πk.differentiable.comp (hG.differentiable (by simp))
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hd y]
  have hc := (πk.hasFDerivAt.comp y (hG.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (πk ∘ G) y (1, 0) = πk (fderiv ℝ G y (B0579.dir 0))
  rw [hc]
  rfl

lemma partialEta_coord_eq_pdir {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G)
    (k : Fin 2) (y : B0579.Plane) :
    UnforcedLeray.Cyl.partialEta (fun z => G z k) y = pdir 1 G y k := by
  let πk : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  have hd : Differentiable ℝ (fun z => G z k) :=
    πk.differentiable.comp (hG.differentiable (by simp))
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hd y]
  have hc := (πk.hasFDerivAt.comp y (hG.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (πk ∘ G) y (0, 1) = πk (fderiv ℝ G y (B0579.dir 1))
  rw [hc]
  rfl

/-- `L²(cell)` integration by parts for `c`-periodic smooth meridional fields on `B0579.cell c`,
using `Cyl.integral_cell_partialQ_mul` and `Cyl.integral_cell_partialEta_mul`. -/
lemma cell_ibp_pdir {c : ℝ} (hc : 0 < c) (i : Fin 2) {F G : B0579.Plane → CMerid}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFp : UnforcedLeray.Cyl.IsPeriodic c F) (hGp : UnforcedLeray.Cyl.IsPeriodic c G)
    (hmF : MemLp F 2 (cellMeas c)) (hmdF : MemLp (pdir i F) 2 (cellMeas c))
    (hmG : MemLp G 2 (cellMeas c)) (hmdG : MemLp (pdir i G) 2 (cellMeas c)) :
    (∫ y in B0579.cell c, (inner ℂ (pdir i F y) (G y) : ℂ)) =
      - ∫ y in B0579.cell c, (inner ℂ (F y) (pdir i G y) : ℂ) := by
  let conjL : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hcoord : ∀ k : Fin 2,
      (∫ y in B0579.cell c, (starRingEnd ℂ) (pdir i F y k) * G y k) =
        - ∫ y in B0579.cell c, (starRingEnd ℂ) (F y k) * pdir i G y k := by
    intro k
    let uk : B0579.Plane → ℂ := fun z => F z k
    let fk : B0579.Plane → ℂ := fun z => (starRingEnd ℂ) (F z k)
    let gk : B0579.Plane → ℂ := fun z => G z k
    let πk : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).restrictScalars ℝ
    have huk : Differentiable ℝ uk :=
      πk.differentiable.comp (hF.differentiable (by simp))
    have hdfk : Differentiable ℝ fk :=
      conjL.differentiable.comp huk
    have hdgk : Differentiable ℝ gk :=
      πk.differentiable.comp (hG.differentiable (by simp))
    have hfpk : UnforcedLeray.Cyl.IsPeriodic c fk := fun z => by
      dsimp [fk]; rw [hFp z]
    have hgpk : UnforcedLeray.Cyl.IsPeriodic c gk := fun z => by
      dsimp [gk]; rw [hGp z]
    have hmfk : MemLp fk 2 (cellMeas c) :=
      conjL.comp_memLp' (memLp_coord_cmerid hmF k)
    have hmgk : MemLp gk 2 (cellMeas c) := memLp_coord_cmerid hmG k
    have hmdfk : MemLp (fun z => (starRingEnd ℂ) (pdir i F z k)) 2 (cellMeas c) :=
      conjL.comp_memLp' (memLp_coord_cmerid hmdF k)
    have hmdgk : MemLp (fun z => pdir i G z k) 2 (cellMeas c) :=
      memLp_coord_cmerid hmdG k
    have hi0 : IntegrableOn (fun z => fk z * gk z) (UnforcedLeray.Cyl.cell c) := by
      rw [← cell_eq_cylCell]; exact hmfk.integrable_mul hmgk
    have hi1 : IntegrableOn (fun z => (starRingEnd ℂ) (pdir i F z k) * gk z)
        (UnforcedLeray.Cyl.cell c) := by
      rw [← cell_eq_cylCell]; exact hmdfk.integrable_mul hmgk
    have hi2 : IntegrableOn (fun z => fk z * pdir i G z k) (UnforcedLeray.Cyl.cell c) := by
      rw [← cell_eq_cylCell]; exact hmfk.integrable_mul hmdgk
    fin_cases i
    · dsimp only [Fin.zero_eta, Fin.isValue] at hi1 hi2 ⊢
      have hpq_f : UnforcedLeray.Cyl.partialQ fk = fun z => (starRingEnd ℂ) (pdir 0 F z k) := by
        funext z
        rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hdfk z]
        have hc1 := (conjL.hasFDerivAt.comp z (huk z).hasFDerivAt).fderiv
        change fderiv ℝ (conjL ∘ uk) z (1, 0) = _
        rw [hc1, ContinuousLinearMap.comp_apply,
          ← UnforcedLeray.Cyl.partialQ_eq_fderiv huk z]
        dsimp only [uk]
        rw [partialQ_coord_eq_pdir hF k z]
        rfl
      have hpq_g : UnforcedLeray.Cyl.partialQ gk = fun z => pdir 0 G z k :=
        funext (partialQ_coord_eq_pdir hG k)
      have h1' : IntegrableOn (fun z => UnforcedLeray.Cyl.partialQ fk z * gk z)
          (UnforcedLeray.Cyl.cell c) := by rwa [hpq_f]
      have h2' : IntegrableOn (fun z => fk z * UnforcedLeray.Cyl.partialQ gk z)
          (UnforcedLeray.Cyl.cell c) := by rwa [hpq_g]
      have hibp := UnforcedLeray.Cyl.integral_cell_partialQ_mul hc hdfk hdgk hfpk hgpk h1' h2'
      rw [← cell_eq_cylCell, hpq_f, hpq_g] at hibp
      exact hibp
    · dsimp only [Fin.mk_one, Fin.isValue] at hi1 hi2 ⊢
      have hpe_f : UnforcedLeray.Cyl.partialEta fk = fun z => (starRingEnd ℂ) (pdir 1 F z k) := by
        funext z
        rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hdfk z]
        have hc1 := (conjL.hasFDerivAt.comp z (huk z).hasFDerivAt).fderiv
        change fderiv ℝ (conjL ∘ uk) z (0, 1) = _
        rw [hc1, ContinuousLinearMap.comp_apply,
          ← UnforcedLeray.Cyl.partialEta_eq_fderiv huk z]
        dsimp only [uk]
        rw [partialEta_coord_eq_pdir hF k z]
        rfl
      have hpe_g : UnforcedLeray.Cyl.partialEta gk = fun z => pdir 1 G z k :=
        funext (partialEta_coord_eq_pdir hG k)
      have h1' : IntegrableOn (fun z => UnforcedLeray.Cyl.partialEta fk z * gk z)
          (UnforcedLeray.Cyl.cell c) := by rwa [hpe_f]
      have h2' : IntegrableOn (fun z => fk z * UnforcedLeray.Cyl.partialEta gk z)
          (UnforcedLeray.Cyl.cell c) := by rwa [hpe_g]
      have hibp := UnforcedLeray.Cyl.integral_cell_partialEta_mul hdfk hdgk hi0 h1' h2'
      rw [← cell_eq_cylCell, hpe_f, hpe_g] at hibp
      exact hibp
  have hexp : ∀ A B : CMerid, (inner ℂ A B : ℂ) =
      (starRingEnd ℂ) (A 0) * B 0 + (starRingEnd ℂ) (A 1) * B 1 := by
    intro A B
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply, mul_comm]
  have hm_conj_dF : ∀ k : Fin 2,
      MemLp (fun y => (starRingEnd ℂ) (pdir i F y k)) 2 (cellMeas c) := fun k =>
    conjL.comp_memLp' (memLp_coord_cmerid hmdF k)
  have hm_conj_F : ∀ k : Fin 2,
      MemLp (fun y => (starRingEnd ℂ) (F y k)) 2 (cellMeas c) := fun k =>
    conjL.comp_memLp' (memLp_coord_cmerid hmF k)
  have hintL0 : IntegrableOn (fun y => (starRingEnd ℂ) (pdir i F y 0) * G y 0) (B0579.cell c) :=
    (hm_conj_dF 0).integrable_mul (memLp_coord_cmerid hmG 0)
  have hintL1 : IntegrableOn (fun y => (starRingEnd ℂ) (pdir i F y 1) * G y 1) (B0579.cell c) :=
    (hm_conj_dF 1).integrable_mul (memLp_coord_cmerid hmG 1)
  have hintR0 : IntegrableOn (fun y => (starRingEnd ℂ) (F y 0) * pdir i G y 0) (B0579.cell c) :=
    (hm_conj_F 0).integrable_mul (memLp_coord_cmerid hmdG 0)
  have hintR1 : IntegrableOn (fun y => (starRingEnd ℂ) (F y 1) * pdir i G y 1) (B0579.cell c) :=
    (hm_conj_F 1).integrable_mul (memLp_coord_cmerid hmdG 1)
  simp_rw [hexp]
  rw [integral_add hintL0 hintL1, integral_add hintR0 hintR1, hcoord 0, hcoord 1]
  ring

/-- Bochner / Calderón–Zygmund identity on the periodic cylinder cell:
`‖ΔG‖_{L²(cell)}² = ∑_{i, j} ‖∂_i ∂_j G‖_{L²(cell)}²`. -/
lemma cellL2_plap_sq_eq_sum {c : ℝ} (hc : 0 < c) {G : B0579.Plane → CMerid}
    (hG : ContDiff ℝ ∞ G) (hGp : UnforcedLeray.Cyl.IsPeriodic c G)
    (hm1 : ∀ i : Fin 2, MemLp (pdir i G) 2 (cellMeas c))
    (hm2 : ∀ i j : Fin 2, MemLp (pdir i (pdir j G)) 2 (cellMeas c))
    (hm3 : ∀ i j k : Fin 2, MemLp (pdir i (pdir j (pdir k G))) 2 (cellMeas c)) :
    (F8U.cellL2 c (plap G)).toReal ^ 2 =
      ∑ i : Fin 2, ∑ j : Fin 2, (F8U.cellL2 c (pdir i (pdir j G))).toReal ^ 2 := by
  have hm_lap : MemLp (plap G) 2 (cellMeas c) := (hm2 0 0).add (hm2 1 1)
  have hcross : (∫ y in B0579.cell c, (inner ℂ (pdir 0 (pdir 0 G) y) (pdir 1 (pdir 1 G) y) : ℂ)) =
      ((F8U.cellL2 c (pdir 0 (pdir 1 G))).toReal ^ 2 : ℝ) := by
    have h1 := cell_ibp_pdir hc 0 (contDiff_pdir hG 0) (contDiff_pdir (contDiff_pdir hG 1) 1)
      (periodic_pdir hGp 0) (periodic_pdir (periodic_pdir hGp 1) 1)
      (hm1 0) (hm2 0 0) (hm2 1 1) (hm3 0 1 1)
    have hcomm1 : pdir 0 (pdir 1 (pdir 1 G)) = pdir 1 (pdir 0 (pdir 1 G)) := by
      funext y
      exact pdir_comm (contDiff_pdir hG 1) 0 1 y
    rw [hcomm1] at h1
    have h2 := cell_ibp_pdir hc 1 (contDiff_pdir hG 0) (contDiff_pdir (contDiff_pdir hG 1) 0)
      (periodic_pdir hGp 0) (periodic_pdir (periodic_pdir hGp 1) 0)
      (hm1 0) (hm2 1 0) (hm2 0 1) (hm3 1 0 1)
    have hcomm2 : pdir 1 (pdir 0 G) = pdir 0 (pdir 1 G) := funext (pdir_comm hG 1 0)
    rw [hcomm2] at h2
    rw [h1, ← h2]
    have hself := integral_inner_eq_L2_inner (hm2 0 1) (hm2 0 1)
    rw [hself, inner_self_eq_norm_sq_to_K]
    simp [norm_toLp_eq_cellL2 (hm2 0 1)]
  have hsym01 : (F8U.cellL2 c (pdir 1 (pdir 0 G))).toReal =
      (F8U.cellL2 c (pdir 0 (pdir 1 G))).toReal := by
    rw [show pdir 1 (pdir 0 G) = pdir 0 (pdir 1 G) from funext (pdir_comm hG 1 0)]
  rw [← integral_norm_sq_eq_cellL2_sq hm_lap]
  have hexp : ∀ y : B0579.Plane, ‖plap G y‖ ^ 2 =
      ‖pdir 0 (pdir 0 G) y‖ ^ 2 +
        2 * (inner ℂ (pdir 0 (pdir 0 G) y) (pdir 1 (pdir 1 G) y) : ℂ).re +
        ‖pdir 1 (pdir 1 G) y‖ ^ 2 := by
    intro y
    unfold plap
    simpa only [RCLike.re_to_complex] using
      norm_add_sq (𝕜 := ℂ) (pdir 0 (pdir 0 G) y) (pdir 1 (pdir 1 G) y)
  simp_rw [hexp]
  have hi00 : IntegrableOn (fun y => ‖pdir 0 (pdir 0 G) y‖ ^ 2) (B0579.cell c) :=
    (hm2 0 0).integrable_norm_pow (by norm_num)
  have hi11 : IntegrableOn (fun y => ‖pdir 1 (pdir 1 G) y‖ ^ 2) (B0579.cell c) :=
    (hm2 1 1).integrable_norm_pow (by norm_num)
  have hic : IntegrableOn
      (fun y => (inner ℂ (pdir 0 (pdir 0 G) y) (pdir 1 (pdir 1 G) y) : ℂ).re) (B0579.cell c) :=
    Complex.reCLM.integrable_comp (integrableOn_inner_cell (hm2 0 0) (hm2 1 1))
  have hi_left : IntegrableOn
      (fun y => ‖pdir 0 (pdir 0 G) y‖ ^ 2 +
        2 * (inner ℂ (pdir 0 (pdir 0 G) y) (pdir 1 (pdir 1 G) y) : ℂ).re) (B0579.cell c) :=
    hi00.add (hic.const_mul 2)
  rw [integral_add hi_left hi11, integral_add hi00 (hic.const_mul 2),
    integral_const_mul]
  have hre_int : (∫ y in B0579.cell c,
      (inner ℂ (pdir 0 (pdir 0 G) y) (pdir 1 (pdir 1 G) y) : ℂ).re) =
      (∫ y in B0579.cell c,
        (inner ℂ (pdir 0 (pdir 0 G) y) (pdir 1 (pdir 1 G) y) : ℂ)).re := by
    simpa only [RCLike.re_to_complex] using
      integral_re (integrableOn_inner_cell (hm2 0 0) (hm2 1 1))
  rw [hre_int, hcross, Complex.ofReal_re, integral_norm_sq_eq_cellL2_sq (hm2 0 0),
    integral_norm_sq_eq_cellL2_sq (hm2 1 1), Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    hsym01]
  ring

/-- Compact-axial integrability helper on `B0579.cell c` against a cylinder test function. -/
lemma integrableOn_cont_mul_cylTest {c : ℝ} (_hc : 0 < c) {g : B0579.Plane → ℂ}
    {ψ : B0579.Plane → ℝ} (hg : Continuous g) (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun y => g y * (ψ y : ℂ)) (B0579.cell c) volume := by
  obtain ⟨R, hR⟩ := hψ.band
  set R₁ := max R 0
  have hsub : B0579.cell c ⊆ Icc (-c / 2) (c / 2) ×ˢ univ := by
    rw [cell_eq_cylCell]; exact prod_mono Ico_subset_Icc_self Subset.rfl
  have hbox_int : IntegrableOn (fun y => g y * (ψ y : ℂ))
      (Icc (-c / 2) (c / 2) ×ˢ Icc (-R₁) R₁) volume :=
    (hg.mul (Complex.continuous_ofReal.comp hψ.continuous)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  refine IntegrableOn.mono_set ?_ hsub
  rw [← integrable_indicator_iff (measurableSet_Icc.prod MeasurableSet.univ)]
  have heq : (Icc (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)).indicator (fun y => g y * (ψ y : ℂ)) =
      (Icc (-c / 2) (c / 2) ×ˢ Icc (-R₁) R₁).indicator (fun y => g y * (ψ y : ℂ)) := by
    funext y
    simp only [indicator_apply, mem_prod, mem_univ, and_true]
    by_cases hy1 : y.1 ∈ Icc (-c / 2) (c / 2)
    · by_cases hyR : |y.2| ≤ R₁
      · have hy2 : y.2 ∈ Icc (-R₁) R₁ := abs_le.mp hyR
        rw [ite_eq_left hy1, ite_eq_left ⟨hy1, hy2⟩]
      · have hgt : R < |y.2| := lt_of_le_of_lt (le_max_left R 0) (not_le.mp hyR)
        have hnot : ¬(y.1 ∈ Icc (-c / 2) (c / 2) ∧ y.2 ∈ Icc (-R₁) R₁) :=
          fun h => hyR (abs_le.mpr h.2)
        rw [ite_eq_left hy1, ite_eq_right hnot, hR y hgt, Complex.ofReal_zero, mul_zero]
    · have hnot : ¬(y.1 ∈ Icc (-c / 2) (c / 2) ∧ y.2 ∈ Icc (-R₁) R₁) := fun h => hy1 h.1
      rw [ite_eq_right hy1, ite_eq_right hnot]
  rw [heq, integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)]
  exact hbox_int

/-- Any smooth `c`-periodic classically divergence-free meridional field on `Plane` satisfies
`F8U.IsCellSolenoidal c`. -/
lemma isCellSolenoidal_of_div_free {c : ℝ} (hc : 0 < c) {F : B0579.Plane → CMerid}
    (hF : ContDiff ℝ ∞ F) (hFp : UnforcedLeray.Cyl.IsPeriodic c F)
    (hdiv : ∀ y : B0579.Plane, pdir 0 F y 0 + pdir 1 F y 1 = 0) :
    F8U.IsCellSolenoidal c F := by
  intro ψ hψ
  let π0 : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  let π1 : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj 1 : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  have hcF0 : Continuous (fun y => F y 0) := π0.continuous.comp hF.continuous
  have hcF1 : Continuous (fun y => F y 1) := π1.continuous.comp hF.continuous
  have hcdF0 : Continuous (fun y => pdir 0 F y 0) :=
    π0.continuous.comp (contDiff_pdir hF 0).continuous
  have hcdF1 : Continuous (fun y => pdir 1 F y 1) :=
    π1.continuous.comp (contDiff_pdir hF 1).continuous
  have hi0 := integrableOn_cont_mul_cylTest hc hcF0 (hψ.pd 0)
  have hi1 := integrableOn_cont_mul_cylTest hc hcF1 (hψ.pd 1)
  refine ⟨hi0.add hi1, ?_⟩
  have hdf0 : Differentiable ℝ (fun y => F y 0) :=
    π0.differentiable.comp (hF.differentiable (by simp))
  have hdf1 : Differentiable ℝ (fun y => F y 1) :=
    π1.differentiable.comp (hF.differentiable (by simp))
  have hdψ : Differentiable ℝ (fun y : B0579.Plane => (ψ y : ℂ)) :=
    (Complex.ofRealCLM.differentiable).comp hψ.differentiable
  have hpq_ψ : UnforcedLeray.Cyl.partialQ (fun y => (ψ y : ℂ)) = fun y => (B0579.pd 0 ψ y : ℂ) := by
    funext y
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hdψ y]
    have hc1 := (Complex.ofRealCLM.hasFDerivAt.comp y (hψ.differentiable y).hasFDerivAt).fderiv
    change fderiv ℝ (Complex.ofRealCLM ∘ ψ) y (1, 0) = _
    rw [hc1, ContinuousLinearMap.comp_apply]
    rfl
  have hpe_ψ : UnforcedLeray.Cyl.partialEta (fun y => (ψ y : ℂ)) =
      fun y => (B0579.pd 1 ψ y : ℂ) := by
    funext y
    rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hdψ y]
    have hc1 := (Complex.ofRealCLM.hasFDerivAt.comp y (hψ.differentiable y).hasFDerivAt).fderiv
    change fderiv ℝ (Complex.ofRealCLM ∘ ψ) y (0, 1) = _
    rw [hc1, ContinuousLinearMap.comp_apply]
    rfl
  have hpq_F : UnforcedLeray.Cyl.partialQ (fun y => F y 0) = fun y => pdir 0 F y 0 :=
    funext (partialQ_coord_eq_pdir hF 0)
  have hpe_F : UnforcedLeray.Cyl.partialEta (fun y => F y 1) = fun y => pdir 1 F y 1 :=
    funext (partialEta_coord_eq_pdir hF 1)
  have hd0_int : IntegrableOn (fun y => UnforcedLeray.Cyl.partialQ (fun z => F z 0) y * (ψ y : ℂ))
      (UnforcedLeray.Cyl.cell c) := by
    rw [hpq_F, ← cell_eq_cylCell]; exact integrableOn_cont_mul_cylTest hc hcdF0 hψ
  have hd1_int : IntegrableOn (fun y => UnforcedLeray.Cyl.partialEta (fun z => F z 1) y * (ψ y : ℂ))
      (UnforcedLeray.Cyl.cell c) := by
    rw [hpe_F, ← cell_eq_cylCell]; exact integrableOn_cont_mul_cylTest hc hcdF1 hψ
  have h0_int : IntegrableOn (fun y => F y 1 * (ψ y : ℂ)) (UnforcedLeray.Cyl.cell c) := by
    rw [← cell_eq_cylCell]; exact integrableOn_cont_mul_cylTest hc hcF1 hψ
  have hi0' : IntegrableOn (fun y => F y 0 * UnforcedLeray.Cyl.partialQ (fun z => (ψ z : ℂ)) y)
      (UnforcedLeray.Cyl.cell c) := by rw [hpq_ψ, ← cell_eq_cylCell]; exact hi0
  have hi1' : IntegrableOn (fun y => F y 1 * UnforcedLeray.Cyl.partialEta (fun z => (ψ z : ℂ)) y)
      (UnforcedLeray.Cyl.cell c) := by rw [hpe_ψ, ← cell_eq_cylCell]; exact hi1
  have hq := UnforcedLeray.Cyl.integral_cell_partialQ_mul hc hdf0 hdψ
    (fun z => congrArg (fun u => u 0) (hFp z))
    (fun z => congrArg Complex.ofReal (hψ.periodic z)) hd0_int hi0'
  have hη := UnforcedLeray.Cyl.integral_cell_partialEta_mul hdf1 hdψ h0_int hd1_int hi1'
  rw [hpq_F, hpq_ψ, ← cell_eq_cylCell] at hq
  rw [hpe_F, hpe_ψ, ← cell_eq_cylCell] at hη
  dsimp only at hq hη
  have hq' : (∫ y in B0579.cell c, F y 0 * (B0579.pd 0 ψ y : ℂ)) =
      - ∫ y in B0579.cell c, pdir 0 F y 0 * (ψ y : ℂ) := by
    rw [← neg_inj, neg_neg]; exact hq.symm
  have hη' : (∫ y in B0579.cell c, F y 1 * (B0579.pd 1 ψ y : ℂ)) =
      - ∫ y in B0579.cell c, pdir 1 F y 1 * (ψ y : ℂ) := by
    rw [← neg_inj, neg_neg]; exact hη.symm
  have hsum_d : (∫ y in B0579.cell c, pdir 0 F y 0 * (ψ y : ℂ)) +
      (∫ y in B0579.cell c, pdir 1 F y 1 * (ψ y : ℂ)) = 0 := by
    rw [← integral_add (integrableOn_cont_mul_cylTest hc hcdF0 hψ)
      (integrableOn_cont_mul_cylTest hc hcdF1 hψ)]
    have hzero : (fun y : B0579.Plane => pdir 0 F y 0 * (ψ y : ℂ) + pdir 1 F y 1 * (ψ y : ℂ)) =
        fun _ => 0 := by
      funext y; rw [← add_mul, hdiv y, zero_mul]
    rw [hzero, integral_zero]
  rw [integral_add hi0 hi1, hq', hη', ← neg_add, hsum_d, neg_zero]

lemma div_free_pdir {F : B0579.Plane → CMerid} (hF : ContDiff ℝ ∞ F)
    (hdiv : ∀ y : B0579.Plane, pdir 0 F y 0 + pdir 1 F y 1 = 0) (i : Fin 2) :
    ∀ y : B0579.Plane, pdir 0 (pdir i F) y 0 + pdir 1 (pdir i F) y 1 = 0 := by
  intro y
  rw [pdir_comm hF 0 i y, pdir_comm hF 1 i y]
  let π0 : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  let π1 : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj 1 : CMerid →L[ℂ] ℂ).restrictScalars ℝ
  have hd0 : HasFDerivAt (fun z : B0579.Plane => (pdir 0 F z 0 : ℂ))
      (π0.comp (fderiv ℝ (pdir 0 F) y)) y :=
    π0.hasFDerivAt.comp y ((contDiff_pdir hF 0).contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hd1 : HasFDerivAt (fun z : B0579.Plane => (pdir 1 F z 1 : ℂ))
      (π1.comp (fderiv ℝ (pdir 1 F) y)) y :=
    π1.hasFDerivAt.comp y ((contDiff_pdir hF 1).contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hsum : HasFDerivAt (fun z : B0579.Plane => (pdir 0 F z 0 : ℂ) + pdir 1 F z 1)
      (0 : B0579.Plane →L[ℝ] ℂ) y := by
    have hfun : (fun z : B0579.Plane => (pdir 0 F z 0 : ℂ) + pdir 1 F z 1) = fun _ => (0 : ℂ) :=
      funext hdiv
    rw [hfun]
    exact hasFDerivAt_const (0 : ℂ) y
  have heq := (hd0.add hd1).unique hsum
  have happ := congrArg (fun L : B0579.Plane →L[ℝ] ℂ => L (B0579.dir i)) heq
  simpa [pdir, π0, π1] using happ

lemma div_free_plap {F : B0579.Plane → CMerid} (hF : ContDiff ℝ ∞ F)
    (hdiv : ∀ y : B0579.Plane, pdir 0 F y 0 + pdir 1 F y 1 = 0) :
    ∀ y : B0579.Plane, pdir 0 (plap F) y 0 + pdir 1 (plap F) y 1 = 0 := by
  intro y
  have h0 := div_free_pdir (contDiff_pdir hF 0) (div_free_pdir hF hdiv 0) 0 y
  have h1 := div_free_pdir (contDiff_pdir hF 1) (div_free_pdir hF hdiv 1) 1 y
  unfold plap
  rw [pdir_add (contDiff_pdir (contDiff_pdir hF 0) 0) (contDiff_pdir (contDiff_pdir hF 1) 1) 0,
    pdir_add (contDiff_pdir (contDiff_pdir hF 0) 0) (contDiff_pdir (contDiff_pdir hF 1) 1) 1]
  simp only [PiLp.add_apply]
  calc (pdir 0 (pdir 0 (pdir 0 F)) y 0 + pdir 0 (pdir 1 (pdir 1 F)) y 0) +
        (pdir 1 (pdir 0 (pdir 0 F)) y 1 + pdir 1 (pdir 1 (pdir 1 F)) y 1)
      = (pdir 0 (pdir 0 (pdir 0 F)) y 0 + pdir 1 (pdir 0 (pdir 0 F)) y 1) +
        (pdir 0 (pdir 1 (pdir 1 F)) y 0 + pdir 1 (pdir 1 (pdir 1 F)) y 1) := by ring
    _ = 0 := by rw [h0, h1, add_zero]

lemma isCellSolenoidal_neg {c : ℝ} {F : B0579.Plane → CMerid}
    (hF : F8U.IsCellSolenoidal c F) :
    F8U.IsCellSolenoidal c (fun y => -F y) := by
  intro ψ hψ
  obtain ⟨hi, hz⟩ := hF ψ hψ
  have heq : (fun y => (-F y) 0 * (B0579.pd 0 ψ y : ℂ) + (-F y) 1 * (B0579.pd 1 ψ y : ℂ)) =
      fun y => -(F y 0 * (B0579.pd 0 ψ y : ℂ) + F y 1 * (B0579.pd 1 ψ y : ℂ)) := by
    funext y; simp only [PiLp.neg_apply]; ring
  rw [heq]
  exact ⟨hi.neg, by rw [integral_neg, hz, neg_zero]⟩

/-! ## 4. Age differentiability of slice `L²` energy -/

def energySlice (c : ℝ) (f : CProf) (τ : ℝ) : ℝ :=
  ∫ y in B0579.cell c, ‖f (τ, y)‖ ^ 2

def clamp01 (θ : ℝ) : ℝ := max 0 (min 1 θ)

lemma continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

lemma clamp01_mem_Icc (θ : ℝ) : clamp01 θ ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma clamp01_eq_of_mem {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) : clamp01 θ = θ := by
  unfold clamp01
  rw [min_eq_right hθ.2, max_eq_right hθ.1]

/-- Elementary Cauchy–Schwarz / Jensen on `(0, 1]`: `(∫_{(0, 1]} g)² ≤ ∫_{(0, 1]} g²`. -/
lemma sq_integral_Ioc_zero_one_le {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    (∫ θ in Ioc (0 : ℝ) 1, g θ) ^ 2 ≤ ∫ θ in Ioc (0 : ℝ) 1, g θ ^ 2 := by
  set m : ℝ := ∫ θ in Ioc (0 : ℝ) 1, g θ
  have hg_int : IntegrableOn g (Ioc 0 1) volume :=
    (hg.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hg2_int : IntegrableOn (fun θ => g θ ^ 2) (Ioc 0 1) volume :=
    ((hg.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have h1_int : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) volume := by
    simp
  have h1_val : (∫ _ in Ioc (0 : ℝ) 1, (1 : ℝ)) = 1 := by
    simp
  have hnonneg : 0 ≤ ∫ θ in Ioc (0 : ℝ) 1, (g θ - m) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hexp : (fun θ : ℝ => (g θ - m) ^ 2) =
      fun θ => (g θ ^ 2 - (2 * m) * g θ) + m ^ 2 * (1 : ℝ) := by
    funext θ; ring
  have hg_sub : IntegrableOn (fun θ => g θ ^ 2 - (2 * m) * g θ) (Ioc 0 1) volume :=
    hg2_int.sub (hg_int.const_mul _)
  rw [hexp, integral_add hg_sub (h1_int.const_mul _),
    integral_sub hg2_int (hg_int.const_mul _), integral_const_mul, integral_const_mul,
    h1_val, mul_one] at hnonneg
  have hm_eq : (2 * m) * (∫ θ in Ioc (0 : ℝ) 1, g θ) = 2 * m ^ 2 := by
    dsimp [m]; ring
  linarith

/-- Difference-quotient convergence `(f(τ + h) - f(τ)) / h → ps f (τ)` in `L²(cell)` via 1D FTC and
Tonelli on `(0, 1] × cell`. -/
lemma tendsto_diffQuot_slice_L2 {c σ τ : ℝ} {f : CProf}
    (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    (hfs_cont : Tendsto (fun t => F8U.cellL2 c (fun y => F8U.ps f (t, y) - F8U.ps f (τ, y)))
      (𝓝 τ) (𝓝 0))
    (hτ : τ ∈ Ioo σ (σ + 2)) :
    Tendsto (fun h : ℝ => F8U.cellL2 c (fun y =>
        h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)))
      (𝓝[≠] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, hr0, hrε, hr_top⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ ε ∧ ENNReal.ofReal r < ⊤ := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, htop ▸ le_top, ENNReal.ofReal_lt_top⟩
    · refine ⟨ε.toReal / 2, half_pos (ENNReal.toReal_pos hε.ne' htop), ?_, ENNReal.ofReal_lt_top⟩
      calc ENNReal.ofReal (ε.toReal / 2) ≤ ENNReal.ofReal ε.toReal :=
            ENNReal.ofReal_le_ofReal (half_le_self ENNReal.toReal_nonneg)
        _ = ε := ENNReal.ofReal_toReal htop
  set δ₀ : ℝ := min (τ - σ) (σ + 2 - τ) / 2
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact half_pos (lt_min (sub_pos.mpr hτ.1) (sub_pos.mpr hτ.2))
  have hcont_r := (ENNReal.tendsto_nhds_zero.mp hfs_cont) (ENNReal.ofReal r)
    (ENNReal.ofReal_pos.mpr hr0)
  rw [Metric.eventually_nhds_iff] at hcont_r
  obtain ⟨δ₁, hδ₁, hball⟩ := hcont_r
  set δ : ℝ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  refine eventually_nhdsWithin_iff.mpr (Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun h hh hne => ?_⟩)
  rw [Real.dist_eq, sub_zero] at hh
  have hh0 : |h| < δ₀ := hh.trans_le (min_le_left _ _)
  have hh1 : |h| < δ₁ := hh.trans_le (min_le_right _ _)
  have hmem_seg : ∀ θ ∈ Icc (0 : ℝ) 1, τ + θ * h ∈ Ioo σ (σ + 2) := by
    intro θ hθ
    have hθh : |θ * h| ≤ |h| := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      exact mul_le_of_le_one_left (abs_nonneg h) hθ.2
    have habs := abs_le.mp (hθh.trans hh0.le)
    have h1 : δ₀ ≤ (τ - σ) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have h2 : δ₀ ≤ (σ + 2 - τ) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hpt : ∀ y : B0579.Plane,
      ‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ ^ 2 ≤
        ∫ θ in Ioc (0 : ℝ) 1, ‖F8U.ps f (τ + clamp01 θ * h, y) - F8U.ps f (τ, y)‖ ^ 2 := by
    intro y
    let γ : ℝ → CMerid := fun θ => f (τ + θ * h, y) - (θ * h) • F8U.ps f (τ, y)
    let γ' : ℝ → CMerid := fun θ => h • (F8U.ps f (τ + θ * h, y) - F8U.ps f (τ, y))
    have hγ_deriv : ∀ θ ∈ Icc (0 : ℝ) 1, HasDerivAt γ (γ' θ) θ := by
      intro θ hθ
      have hcoord : HasDerivAt (fun s : ℝ => (τ + s * h, y)) (h, (0, 0)) θ := by
        have hs : HasDerivAt (fun s : ℝ => τ + s * h) h θ := by
          simpa using ((hasDerivAt_id θ).mul_const h).const_add τ
        exact hs.prodMk (hasDerivAt_const θ y)
      have hfa : DifferentiableAt ℝ f (τ + θ * h, y) :=
        (hf.contDiffAt ((isOpen_stripSet σ).mem_nhds
          (mem_stripSet (hmem_seg θ hθ) y))).differentiableAt (by simp)
      have hcomp := hfa.hasFDerivAt.comp_hasDerivAt θ hcoord
      have heq_d : fderiv ℝ f (τ + θ * h, y) (h, (0, 0)) = h • F8U.ps f (τ + θ * h, y) := by
        have : ((h, (0, 0)) : Coord) = h • ((1, (0, 0)) : Coord) := by ext <;> simp
        rw [this, map_smul]; rfl
      rw [heq_d] at hcomp
      have hcomp' : HasDerivAt (fun s : ℝ => f (τ + s * h, y)) (h • F8U.ps f (τ + θ * h, y)) θ :=
        hcomp
      have hlin : HasDerivAt (fun s : ℝ => (s * h) • F8U.ps f (τ, y))
          (h • F8U.ps f (τ, y)) θ := by
        have hs : HasDerivAt (fun s : ℝ => s * h) h θ := by
          simpa using (hasDerivAt_id θ).mul_const h
        simpa using hs.smul_const (F8U.ps f (τ, y))
      have hsub := hcomp'.sub hlin
      rw [← smul_sub] at hsub
      exact hsub
    have hps_cont : ContinuousOn (fun θ : ℝ => F8U.ps f (τ + θ * h, y) - F8U.ps f (τ, y))
        (Icc 0 1) := by
      refine ((contDiffOn_ps hf).continuousOn.comp
        ((continuousOn_const.add (continuousOn_id.mul continuousOn_const)).prodMk
          continuousOn_const) fun θ hθ => mem_stripSet (hmem_seg θ hθ) y).sub continuousOn_const
    have hγ'_int : IntervalIntegrable γ' volume 0 1 :=
      (hps_cont.const_smul h).intervalIntegrable_of_Icc zero_le_one
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (fun θ hθ => (hγ_deriv θ hθ).continuousAt.continuousWithinAt)
      (fun θ hθ => hγ_deriv θ ⟨hθ.1.le, hθ.2.le⟩) hγ'_int
    have hdiff : h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y) =
        ∫ θ in Ioc (0 : ℝ) 1, (F8U.ps f (τ + θ * h, y) - F8U.ps f (τ, y)) := by
      have hγ10 : γ 1 - γ 0 = f (τ + h, y) - f (τ, y) - h • F8U.ps f (τ, y) := by
        dsimp [γ]; simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hsmul := congrArg (fun v : CMerid => h⁻¹ • v) hftc.symm
      rw [hγ10, smul_sub, inv_smul_smul₀ hne] at hsmul
      rw [hsmul, intervalIntegral.integral_of_le zero_le_one]
      dsimp [γ']
      rw [integral_smul, inv_smul_smul₀ hne]
    have hnorm : ‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ ≤
        ∫ θ in Ioc (0 : ℝ) 1, ‖F8U.ps f (τ + clamp01 θ * h, y) - F8U.ps f (τ, y)‖ := by
      rw [hdiff]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
      rw [clamp01_eq_of_mem ⟨hθ.1.le, hθ.2⟩]
    have hg_cont : Continuous (fun θ : ℝ =>
        ‖F8U.ps f (τ + clamp01 θ * h, y) - F8U.ps f (τ, y)‖) := by
      refine Continuous.norm (((contDiffOn_ps hf).continuousOn.comp_continuous
        ((continuous_const.add (continuous_clamp01.mul continuous_const)).prodMk continuous_const)
        fun θ => mem_stripSet (hmem_seg (clamp01 θ) (clamp01_mem_Icc θ)) y).sub continuous_const)
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (sq_integral_Ioc_zero_one_le hg_cont.continuousOn)
  let Φ : ℝ → B0579.Plane → ℝ≥0∞ := fun θ y =>
    ENNReal.ofReal (‖F8U.ps f (τ + clamp01 θ * h, y) - F8U.ps f (τ, y)‖ ^ 2)
  have hΦ_meas : Measurable (Function.uncurry Φ) := by
    have hc_map : Continuous (fun p : ℝ × B0579.Plane =>
        F8U.ps f (τ + clamp01 p.1 * h, p.2) - F8U.ps f (τ, p.2)) := by
      refine ((contDiffOn_ps hf).continuousOn.comp_continuous
        ((continuous_const.add ((continuous_clamp01.comp continuous_fst).mul
          continuous_const)).prodMk continuous_snd)
        fun p => mem_stripSet (hmem_seg (clamp01 p.1) (clamp01_mem_Icc p.1)) p.2).sub ?_
      exact (contDiff_slice (contDiffOn_ps hf) hτ).continuous.comp continuous_snd
    exact ENNReal.measurable_ofReal.comp ((hc_map.norm.pow 2).measurable)
  have hpt_enn : ∀ y : B0579.Plane,
      ‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ θ in Ioc (0 : ℝ) 1, Φ θ y := by
    intro y
    have hcont_y : Continuous (fun θ : ℝ =>
        ‖F8U.ps f (τ + clamp01 θ * h, y) - F8U.ps f (τ, y)‖ ^ 2) := by
      refine (Continuous.norm (((contDiffOn_ps hf).continuousOn.comp_continuous
        ((continuous_const.add (continuous_clamp01.mul continuous_const)).prodMk continuous_const)
        fun θ => mem_stripSet (hmem_seg (clamp01 θ) (clamp01_mem_Icc θ)) y).sub
        continuous_const)).pow 2
    have hint_y : IntegrableOn (fun θ : ℝ =>
        ‖F8U.ps f (τ + clamp01 θ * h, y) - F8U.ps f (τ, y)‖ ^ 2) (Ioc 0 1) volume :=
      (hcont_y.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hlhs : ‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
      norm_num
    rw [hlhs, ← ofReal_integral_eq_lintegral_ofReal hint_y (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hpt y)
  have hswap : (∫⁻ y, (∫⁻ θ in Ioc (0 : ℝ) 1, Φ θ y) ∂cellMeas c) =
      ∫⁻ θ in Ioc (0 : ℝ) 1, (∫⁻ y, Φ θ y ∂cellMeas c) :=
    (lintegral_lintegral_swap hΦ_meas.aemeasurable).symm
  have hθ_bd : ∀ θ ∈ Ioc (0 : ℝ) 1,
      (∫⁻ y, Φ θ y ∂cellMeas c) ≤ ENNReal.ofReal r ^ (2 : ℝ) := by
    intro θ hθ
    have hθ_icc : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2⟩
    have hdist : dist (τ + θ * h) τ < δ₁ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg hθ_icc.1]
      exact (mul_le_of_le_one_left (abs_nonneg h) hθ_icc.2).trans_lt hh1
    have hlt : F8U.cellL2 c (fun y => F8U.ps f (τ + θ * h, y) - F8U.ps f (τ, y)) ≤
        ENNReal.ofReal r := hball hdist
    have heq_Φ : (fun y => Φ θ y) =
        fun y => ‖F8U.ps f (τ + θ * h, y) - F8U.ps f (τ, y)‖ₑ ^ (2 : ℝ) := by
      funext y
      dsimp [Φ]
      rw [clamp01_eq_of_mem hθ_icc, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
        ← ENNReal.rpow_natCast]
      norm_num
    rw [heq_Φ]
    have hcell_eq := sliceL2Norm_eq_lintegral c
      (fun x : Coord => F8U.ps f x - F8U.ps f (τ, x.2)) (τ + θ * h)
    have hpow := ENNReal.rpow_le_rpow hlt (by norm_num : (0 : ℝ) ≤ 2)
    change F8U.cellL2 c (fun y => F8U.ps f (τ + θ * h, y) - F8U.ps f (τ, y)) ^ (2 : ℝ) ≤ _ at hpow
    unfold F8U.cellL2 at hpow
    rw [hcell_eq, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
      at hpow
    exact hpow
  have htot : (∫⁻ y, ‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ₑ ^ (2 : ℝ) ∂cellMeas c) ≤
      ENNReal.ofReal r ^ (2 : ℝ) := by
    calc (∫⁻ y, ‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ₑ ^ (2 : ℝ) ∂cellMeas c)
        ≤ ∫⁻ y, (∫⁻ θ in Ioc (0 : ℝ) 1, Φ θ y) ∂cellMeas c := lintegral_mono hpt_enn
      _ = ∫⁻ θ in Ioc (0 : ℝ) 1, (∫⁻ y, Φ θ y ∂cellMeas c) := hswap
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, ENNReal.ofReal r ^ (2 : ℝ) :=
          setLIntegral_mono (measurable_const) hθ_bd
      _ = ENNReal.ofReal r ^ (2 : ℝ) := by simp
  have hcell : F8U.cellL2 c (fun y => h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)) ≤
      ENNReal.ofReal r := by
    unfold F8U.cellL2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, one_div]
    calc (∫⁻ y, ‖h⁻¹ • (f (τ + h, y) - f (τ, y)) - F8U.ps f (τ, y)‖ₑ ^ (2 : ℝ) ∂cellMeas c) ^
          (2 : ℝ)⁻¹
        ≤ (ENNReal.ofReal r ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := ENNReal.rpow_le_rpow htot (by norm_num)
      _ = ENNReal.ofReal r := by
          rw [← ENNReal.rpow_mul, show (2 : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num, ENNReal.rpow_one]
  exact hcell.trans hrε

/-- Age derivative of `energySlice c f` on `(σ, σ + 2)`:
`d/dτ ∫_{cell} ‖f(τ, y)‖² dy = 2 Re ∫_{cell} ⟨f(τ, y), ∂_s f(τ, y)⟩ dy`. -/
lemma hasDerivAt_energySlice {c σ τ : ℝ} {f : CProf}
    (hf : ContDiffOn ℝ ∞ f (stripSet σ))
    (hf_L2 : ∀ s ∈ Ioo σ (σ + 2), MemLp (F8U.slice f s) 2 (cellMeas c))
    (hfs_L2 : MemLp (F8U.slice (F8U.ps f) τ) 2 (cellMeas c))
    (hfs_cont : Tendsto (fun t => F8U.cellL2 c (fun y => F8U.ps f (t, y) - F8U.ps f (τ, y)))
      (𝓝 τ) (𝓝 0))
    (hτ : τ ∈ Ioo σ (σ + 2)) :
    HasDerivAt (energySlice c f)
      (2 * (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (F8U.ps f (τ, y)) : ℂ)).re) τ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let dq : ℝ → B0579.Plane → CMerid := fun h y => h⁻¹ • (f (τ + h, y) - f (τ, y))
  have hdq_lim : Tendsto (fun h : ℝ => F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y)))
      (𝓝[≠] 0) (𝓝 0) :=
    tendsto_diffQuot_slice_L2 hf hfs_cont hτ
  have hdq_toReal : Tendsto (fun h : ℝ => (F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y))).toReal)
      (𝓝[≠] 0) (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdq_lim
  set δ₀ : ℝ := min (τ - σ) (σ + 2 - τ) / 2
  have hδ₀ : 0 < δ₀ :=
    half_pos (lt_min (sub_pos.mpr hτ.1) (sub_pos.mpr hτ.2))
  have hev_in : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 ∧ τ + h ∈ Ioo σ (σ + 2) ∧
      F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y)) < 1 := by
    have h1 : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 := eventually_mem_nhdsWithin
    have h2 : ∀ᶠ h : ℝ in 𝓝[≠] 0, τ + h ∈ Ioo σ (σ + 2) := by
      refine eventually_nhdsWithin_of_eventually_nhds (Metric.eventually_nhds_iff.mpr ⟨δ₀, hδ₀, ?_⟩)
      intro h hh
      rw [Real.dist_eq, sub_zero] at hh
      have habs := abs_lt.mp hh
      have hl1 : δ₀ ≤ (τ - σ) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      have hl2 : δ₀ ≤ (σ + 2 - τ) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hhalf_lt : ENNReal.ofReal (1 / 2 : ℝ) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
    have h3' : ∀ᶠ h : ℝ in 𝓝[≠] 0, F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y)) < 1 :=
      (ENNReal.tendsto_nhds_zero.mp hdq_lim (ENNReal.ofReal (1 / 2))
        (ENNReal.ofReal_pos.mpr (by norm_num))).mono fun _ hh => lt_of_le_of_lt hh hhalf_lt
    exact h1.and (h2.and h3')
  have hinner_lim : Tendsto
      (fun h : ℝ => (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (dq h y) : ℂ)).re)
      (𝓝[≠] 0)
      (𝓝 ((∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (F8U.ps f (τ, y)) : ℂ)).re)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hmul : Tendsto
        (fun h : ℝ => (F8U.cellL2 c (F8U.slice f τ)).toReal *
          (F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y))).toReal)
        (𝓝[≠] 0) (𝓝 0) := by
      simpa using hdq_toReal.const_mul (F8U.cellL2 c (F8U.slice f τ)).toReal
    filter_upwards [hev_in, (Metric.tendsto_nhds.mp hmul) ε hε] with h ⟨_, hτh, _⟩ hbd
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg)] at hbd
    have hmem_dq : MemLp (dq h) 2 (cellMeas c) :=
      ((hf_L2 (τ + h) hτh).sub (hf_L2 τ hτ)).const_smul h⁻¹
    have hmem_diff : MemLp (fun y => dq h y - F8U.ps f (τ, y)) 2 (cellMeas c) :=
      hmem_dq.sub hfs_L2
    have hsub : (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (dq h y) : ℂ)).re -
        (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (F8U.ps f (τ, y)) : ℂ)).re =
        (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (dq h y - F8U.ps f (τ, y)) : ℂ)).re := by
      have hi1 : IntegrableOn (fun y => (inner ℂ (f (τ, y)) (dq h y) : ℂ))
          (B0579.cell c) volume := integrableOn_inner_cell (hf_L2 τ hτ) hmem_dq
      have hi2 : IntegrableOn (fun y => (inner ℂ (f (τ, y)) (F8U.ps f (τ, y)) : ℂ))
          (B0579.cell c) volume := integrableOn_inner_cell (hf_L2 τ hτ) hfs_L2
      have hcongr : (fun y => (inner ℂ (f (τ, y)) (dq h y - F8U.ps f (τ, y)) : ℂ)) =
          fun y => (inner ℂ (f (τ, y)) (dq h y) : ℂ) -
            (inner ℂ (f (τ, y)) (F8U.ps f (τ, y)) : ℂ) := by
        funext y; exact inner_sub_right _ _ _
      rw [hcongr, integral_sub hi1 hi2, Complex.sub_re]
    rw [Real.dist_eq, hsub]
    exact (abs_re_integral_inner_le (hf_L2 τ hτ) hmem_diff).trans_lt hbd
  have hrem_lim : Tendsto
      (fun h : ℝ => h * ∫ y in B0579.cell c, ‖dq h y‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    set B : ℝ := (1 + (F8U.cellL2 c (F8U.slice (F8U.ps f) τ)).toReal) ^ 2
    have hB_lim : Tendsto (fun h : ℝ => |h| * B) (𝓝[≠] 0) (𝓝 0) := by
      have hid : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
        simpa only [abs_zero] using
          (continuous_abs.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      simpa using hid.mul_const B
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hev_in, (Metric.tendsto_nhds.mp hB_lim) ε hε] with h ⟨_, hτh, hlt1⟩ hbd
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (abs_nonneg h) (sq_nonneg _))] at hbd
    have hmem_dq : MemLp (dq h) 2 (cellMeas c) :=
      ((hf_L2 (τ + h) hτh).sub (hf_L2 τ hτ)).const_smul h⁻¹
    have hmem_diff : MemLp (fun y => dq h y - F8U.ps f (τ, y)) 2 (cellMeas c) :=
      hmem_dq.sub hfs_L2
    have htri : F8U.cellL2 c (dq h) ≤
        F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y)) +
          F8U.cellL2 c (F8U.slice (F8U.ps f) τ) := by
      have heq : dq h = (fun y => dq h y - F8U.ps f (τ, y)) + F8U.slice (F8U.ps f) τ := by
        funext y; simp [F8U.slice]
      conv_lhs => rw [heq]
      exact eLpNorm_add_le hmem_diff.aestronglyMeasurable hfs_L2.aestronglyMeasurable one_le_two
    have hne1 : F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y)) ≠ ⊤ := hlt1.ne_top
    have hne2 : F8U.cellL2 c (F8U.slice (F8U.ps f) τ) ≠ ⊤ := hfs_L2.eLpNorm_ne_top
    have htoReal_le : (F8U.cellL2 c (dq h)).toReal ≤
        1 + (F8U.cellL2 c (F8U.slice (F8U.ps f) τ)).toReal := by
      have h1 := (ENNReal.toReal_le_toReal hmem_dq.eLpNorm_ne_top
        (ENNReal.add_ne_top.mpr ⟨hne1, hne2⟩)).mpr htri
      rw [ENNReal.toReal_add hne1 hne2] at h1
      change (F8U.cellL2 c (dq h)).toReal ≤ _ at h1
      have h2 : (F8U.cellL2 c (fun y => dq h y - F8U.ps f (τ, y))).toReal ≤ 1 := by
        have := (ENNReal.toReal_le_toReal hne1 ENNReal.one_ne_top).mpr hlt1.le
        simpa using this
      linarith
    have hint_le : (∫ y in B0579.cell c, ‖dq h y‖ ^ 2) ≤ B := by
      rw [integral_norm_sq_eq_cellL2_sq hmem_dq]
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg htoReal_le 2
    rw [Real.dist_eq, sub_zero, abs_mul,
      abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hint_le (abs_nonneg h)).trans_lt hbd
  have hcomb : Tendsto
      (fun h : ℝ => 2 * (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (dq h y) : ℂ)).re +
        h * ∫ y in B0579.cell c, ‖dq h y‖ ^ 2)
      (𝓝[≠] 0)
      (𝓝 (2 * (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (F8U.ps f (τ, y)) : ℂ)).re)) := by
    simpa using (hinner_lim.const_mul 2).add hrem_lim
  refine hcomb.congr' ?_
  filter_upwards [hev_in] with h ⟨hne, hτh, _⟩
  have hmem_dq : MemLp (dq h) 2 (cellMeas c) :=
    ((hf_L2 (τ + h) hτh).sub (hf_L2 τ hτ)).const_smul h⁻¹
  have hpt : ∀ y : B0579.Plane,
      ‖f (τ + h, y)‖ ^ 2 - ‖f (τ, y)‖ ^ 2 =
        2 * h * (inner ℂ (f (τ, y)) (dq h y)).re + h ^ 2 * ‖dq h y‖ ^ 2 := by
    intro y
    have hf_eq : f (τ + h, y) = f (τ, y) + (h : ℂ) • dq h y := by
      dsimp only [dq]
      rw [Complex.coe_smul, smul_smul, mul_inv_cancel₀ hne, one_smul, add_sub_cancel]
    rw [hf_eq, norm_add_sq (𝕜 := ℂ), RCLike.re_to_complex, inner_smul_right,
      Complex.re_ofReal_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hi_h : IntegrableOn (fun y => ‖f (τ + h, y)‖ ^ 2) (B0579.cell c) :=
    (hf_L2 (τ + h) hτh).integrable_norm_pow (by norm_num)
  have hi_0 : IntegrableOn (fun y => ‖f (τ, y)‖ ^ 2) (B0579.cell c) :=
    (hf_L2 τ hτ).integrable_norm_pow (by norm_num)
  have hi_in_c : IntegrableOn (fun y => (inner ℂ (f (τ, y)) (dq h y) : ℂ)) (B0579.cell c) :=
    integrableOn_inner_cell (hf_L2 τ hτ) hmem_dq
  have hi_in : IntegrableOn (fun y => (inner ℂ (f (τ, y)) (dq h y) : ℂ).re) (B0579.cell c) :=
    Complex.reCLM.integrable_comp hi_in_c
  have hi_dq : IntegrableOn (fun y => ‖dq h y‖ ^ 2) (B0579.cell c) :=
    hmem_dq.integrable_norm_pow (by norm_num)
  unfold energySlice
  rw [smul_eq_mul, ← integral_sub hi_h hi_0]
  simp_rw [hpt]
  have h1 : (fun y : B0579.Plane => 2 * h * (inner ℂ (f (τ, y)) (dq h y)).re +
      h ^ 2 * ‖dq h y‖ ^ 2) =
      fun y => (2 * h) * ((inner ℂ (f (τ, y)) (dq h y) : ℂ)).re +
        (h ^ 2) * ‖dq h y‖ ^ 2 := rfl
  rw [h1, integral_add (hi_in.const_mul (2 * h)) (hi_dq.const_mul (h ^ 2)),
    integral_const_mul, integral_const_mul]
  have hre_int : (∫ y in B0579.cell c, ((inner ℂ (f (τ, y)) (dq h y) : ℂ)).re) =
      (∫ y in B0579.cell c, (inner ℂ (f (τ, y)) (dq h y) : ℂ)).re := by
    simpa only [RCLike.re_to_complex] using integral_re hi_in_c
  rw [hre_int]
  field_simp [hne]

/-! ## 5. Scalar-multiplier calculus, train bounds, and convective cancellation -/

def sdirR (i : Fin 2) (a : B0579.Plane → ℝ) (y : B0579.Plane) : ℝ :=
  fderiv ℝ a y (B0579.dir i)

def slapR (a : B0579.Plane → ℝ) (y : B0579.Plane) : ℝ :=
  sdirR 0 (sdirR 0 a) y + sdirR 1 (sdirR 1 a) y

def mulReal (a : B0579.Plane → ℝ) (G : B0579.Plane → CMerid) (y : B0579.Plane) : CMerid :=
  (a y : ℂ) • G y

def compCLM (m k : Fin 2) : CMerid →L[ℝ] CMerid :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 2 (fun i : Fin 2 => if i = k then u m else 0)
      map_add' := fun u v => by
        ext i; simp only [PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun r u => by
        ext i; simp only [PiLp.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
    1
    (fun u => by
      have hsq : ‖WithLp.toLp 2 (fun i : Fin 2 => if i = k then u m else 0)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
        fin_cases k <;> simp [pow_two]
        · exact mul_self_le_mul_self (norm_nonneg _) (PiLp.norm_apply_le u m)
        · exact mul_self_le_mul_self (norm_nonneg _) (PiLp.norm_apply_le u m)
      have hle := (abs_le_of_sq_le_sq' hsq (norm_nonneg u)).2
      simpa using hle)

@[simp] lemma compCLM_apply (m k i : Fin 2) (u : CMerid) :
    compCLM m k u i = if i = k then u m else 0 := rfl

lemma norm_compCLM_apply_le (m k : Fin 2) (u : CMerid) :
    ‖compCLM m k u‖ ≤ ‖u‖ := by
  simpa using ContinuousLinearMap.le_of_opNorm_le (compCLM m k)
    (LinearMap.mkContinuous_norm_le _ zero_le_one _) u

lemma pdir_compCLM {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G) (m k i : Fin 2) :
    pdir i (fun y => compCLM m k (G y)) = fun y => compCLM m k (pdir i G y) := by
  funext y
  have hc := ((compCLM m k).hasFDerivAt.comp y
    (hG.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  unfold pdir
  change fderiv ℝ ((compCLM m k) ∘ G) y (B0579.dir i) = _
  rw [hc, ContinuousLinearMap.comp_apply]

lemma plap_compCLM {G : B0579.Plane → CMerid} (hG : ContDiff ℝ ∞ G) (m k : Fin 2) :
    plap (fun y => compCLM m k (G y)) = fun y => compCLM m k (plap G y) := by
  funext y
  unfold plap
  rw [pdir_compCLM hG m k 0, pdir_compCLM (contDiff_pdir hG 0) m k 0,
    pdir_compCLM hG m k 1, pdir_compCLM (contDiff_pdir hG 1) m k 1, ← map_add]

lemma memLp_compCLM {c : ℝ} {G : B0579.Plane → CMerid} (hG : MemLp G 2 (cellMeas c))
    (m k : Fin 2) :
    MemLp (fun y => compCLM m k (G y)) 2 (cellMeas c) :=
  (compCLM m k).comp_memLp' hG

lemma cellL2_compCLM_le {c : ℝ} {G : B0579.Plane → CMerid} (hG : MemLp G 2 (cellMeas c))
    (m k : Fin 2) :
    (F8U.cellL2 c (fun y => compCLM m k (G y))).toReal ≤ (F8U.cellL2 c G).toReal := by
  have hle : F8U.cellL2 c (fun y => compCLM m k (G y)) ≤ F8U.cellL2 c G :=
    eLpNorm_mono fun y => norm_compCLM_apply_le m k (G y)
  exact (ENNReal.toReal_le_toReal (memLp_compCLM hG m k).eLpNorm_ne_top hG.eLpNorm_ne_top).mpr hle

lemma contDiff_mulReal {a : B0579.Plane → ℝ} {G : B0579.Plane → CMerid}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (mulReal a G) := by
  have heq : mulReal a G = fun y => a y • G y := by
    funext y; unfold mulReal; exact Complex.coe_smul (a y) (G y)
  rw [heq]
  exact ha.smul hG

lemma periodic_mulReal {c : ℝ} {a : B0579.Plane → ℝ} {G : B0579.Plane → CMerid}
    (ha : UnforcedLeray.Cyl.IsPeriodic c a) (hG : UnforcedLeray.Cyl.IsPeriodic c G) :
    UnforcedLeray.Cyl.IsPeriodic c (mulReal a G) := by
  intro y; unfold mulReal; rw [ha y, hG y]

lemma pdir_mulReal {a : B0579.Plane → ℝ} {G : B0579.Plane → CMerid}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (i : Fin 2) :
    pdir i (mulReal a G) = fun y => mulReal (sdirR i a) G y + mulReal a (pdir i G) y := by
  funext y
  have heq : mulReal a G = a • G := by
    funext z; unfold mulReal; exact Complex.coe_smul (a z) (G z)
  have hda : HasFDerivAt a (fderiv ℝ a y) y :=
    (ha.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hdG : HasFDerivAt G (fderiv ℝ G y) y :=
    (hG.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  unfold pdir
  rw [heq, (hda.smul hdG).fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply]
  unfold mulReal sdirR
  rw [Complex.coe_smul, Complex.coe_smul, add_comm]

lemma contDiff_sdirR {a : B0579.Plane → ℝ} (ha : ContDiff ℝ ∞ a) (i : Fin 2) :
    ContDiff ℝ ∞ (sdirR i a) :=
  ((contDiff_infty_iff_fderiv.1 ha).2).clm_apply contDiff_const

lemma plap_mulReal {a : B0579.Plane → ℝ} {G : B0579.Plane → CMerid}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) :
    plap (mulReal a G) = fun y =>
      mulReal (slapR a) G y +
        ((2 : ℝ) • mulReal (sdirR 0 a) (pdir 0 G) y +
          (2 : ℝ) • mulReal (sdirR 1 a) (pdir 1 G) y) +
        mulReal a (plap G) y := by
  funext y
  unfold plap
  rw [pdir_mulReal ha hG 0, pdir_add (contDiff_mulReal (contDiff_sdirR ha 0) hG)
      (contDiff_mulReal ha (contDiff_pdir hG 0)) 0,
    pdir_mulReal (contDiff_sdirR ha 0) hG 0, pdir_mulReal ha (contDiff_pdir hG 0) 0,
    pdir_mulReal ha hG 1, pdir_add (contDiff_mulReal (contDiff_sdirR ha 1) hG)
      (contDiff_mulReal ha (contDiff_pdir hG 1)) 1,
    pdir_mulReal (contDiff_sdirR ha 1) hG 1, pdir_mulReal ha (contDiff_pdir hG 1) 1]
  ext k
  simp only [mulReal, slapR, PiLp.add_apply, PiLp.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

lemma memLp_mulReal_of_bdd {c M : ℝ} {a : B0579.Plane → ℝ} {G : B0579.Plane → CMerid}
    (ha : Continuous a) (hbdd : ∀ y, |a y| ≤ M) (hG : MemLp G 2 (cellMeas c)) :
    MemLp (mulReal a G) 2 (cellMeas c) ∧
      (F8U.cellL2 c (mulReal a G)).toReal ≤ max M 0 * (F8U.cellL2 c G).toReal := by
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right M 0
  have hmeas : AEStronglyMeasurable (mulReal a G) (cellMeas c) :=
    (Complex.continuous_ofReal.comp ha).aestronglyMeasurable.smul hG.aestronglyMeasurable
  have hle : F8U.cellL2 c (mulReal a G) ≤ ENNReal.ofReal M' * F8U.cellL2 c G := by
    have hpt : ∀ y : B0579.Plane, ‖mulReal a G y‖ ≤ ‖(M' : ℂ) • G y‖ := by
      intro y
      unfold mulReal
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg hM']
      exact mul_le_mul_of_nonneg_right ((hbdd y).trans (le_max_left M 0)) (norm_nonneg _)
    calc F8U.cellL2 c (mulReal a G)
        ≤ eLpNorm ((M' : ℂ) • G) 2 (cellMeas c) := eLpNorm_mono hpt
      _ = ‖(M' : ℂ)‖ₑ * F8U.cellL2 c G := eLpNorm_const_smul (M' : ℂ) G 2 (cellMeas c)
      _ = ENNReal.ofReal M' * F8U.cellL2 c G := by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hM']
  have hfin : F8U.cellL2 c (mulReal a G) < ⊤ :=
    lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.eLpNorm_ne_top.lt_top)
  have hm : MemLp (mulReal a G) 2 (cellMeas c) := ⟨hmeas, hfin⟩
  refine ⟨hm, ?_⟩
  have htr := (ENNReal.toReal_le_toReal hm.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top)).mpr hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM'] at htr

/-- Incompressibility cancellation `Re ∫_{cell} ⟨F, (v · ∇)F⟩ = 0` for divergence-free `v`. -/
lemma transport_re_inner_zero {c C_tr : ℝ} (hc : 0 < c) (hC : 0 ≤ C_tr)
    {v : B0579.Plane → UnforcedLeray.Train.Vec}
    (hv : ContDiff ℝ ∞ v) (hvp : UnforcedLeray.Cyl.IsPeriodic c v)
    (hdiv : ∀ y, UnforcedLeray.Cyl.divergence v y = 0)
    (hv0 : ∀ m : Fin 2, ∀ y, |v y m| ≤ C_tr)
    (hv1 : ∀ i m : Fin 2, ∀ y, |sdirR i (fun z => v z m) y| ≤ C_tr)
    {F : B0579.Plane → CMerid}
    (hF : ContDiff ℝ ∞ F) (hFp : UnforcedLeray.Cyl.IsPeriodic c F)
    (hmF : MemLp F 2 (cellMeas c))
    (hmdF : ∀ m : Fin 2, MemLp (pdir m F) 2 (cellMeas c)) :
    (∫ y in B0579.cell c,
      (inner ℂ (F y) (mulReal (fun z => v z 0) (pdir 0 F) y +
        mulReal (fun z => v z 1) (pdir 1 F) y) : ℂ)).re = 0 := by
  let T0 := mulReal (fun z => v z 0) (pdir 0 F)
  let T1 := mulReal (fun z => v z 1) (pdir 1 F)
  have hc_v : ∀ m : Fin 2, ContDiff ℝ ∞ (fun z => v z m) :=
    fun m => (EuclideanSpace.proj m : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp hv
  have hp_v : ∀ m : Fin 2, UnforcedLeray.Cyl.IsPeriodic c (fun z => v z m) :=
    fun m z => congrArg (fun u => u m) (hvp z)
  have hmT0 : MemLp T0 2 (cellMeas c) :=
    (memLp_mulReal_of_bdd (hc_v 0).continuous (hv0 0) (hmdF 0)).1
  have hmT1 : MemLp T1 2 (cellMeas c) :=
    (memLp_mulReal_of_bdd (hc_v 1).continuous (hv0 1) (hmdF 1)).1
  have hd_prod : ∀ m : Fin 2,
      MemLp (pdir m (mulReal (fun z => v z m) F)) 2 (cellMeas c) := by
    intro m
    rw [pdir_mulReal (hc_v m) hF m]
    exact (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v m) m).continuous (hv1 m m) hmF).1.add
      (memLp_mulReal_of_bdd (hc_v m).continuous (hv0 m) (hmdF m)).1
  have hm_vF : ∀ m : Fin 2, MemLp (mulReal (fun z => v z m) F) 2 (cellMeas c) :=
    fun m => (memLp_mulReal_of_bdd (hc_v m).continuous (hv0 m) hmF).1
  -- Integrate by parts: ⟨F, v_m ∂_m F⟩ = ⟨v_m F, ∂_m F⟩ = -⟨∂_m (v_m F), F⟩ = -⟨(∂_m v_m) F, F⟩ - ⟨v_m ∂_m F, F⟩
  have hibp : ∀ m : Fin 2,
      (∫ y in B0579.cell c, (inner ℂ (F y) (mulReal (fun z => v z m) (pdir m F) y) : ℂ)).re =
        -(1 / 2 : ℝ) * ∫ y in B0579.cell c,
          sdirR m (fun z => v z m) y * ‖F y‖ ^ 2 := by
    intro m
    have hsym_pt : ∀ y : B0579.Plane,
        (inner ℂ (F y) (mulReal (fun z => v z m) (pdir m F) y) : ℂ) =
          inner ℂ (mulReal (fun z => v z m) F y) (pdir m F y) := by
      intro y
      unfold mulReal
      rw [inner_smul_right, inner_smul_left, Complex.conj_ofReal]
    have h1 := cell_ibp_pdir hc m (contDiff_mulReal (hc_v m) hF) hF
      (periodic_mulReal (hp_v m) hFp) hFp (hm_vF m) (hd_prod m) hmF (hmdF m)
    have hp := pdir_mulReal (hc_v m) hF m
    rw [hp] at h1
    dsimp only at h1
    have hm_dvF : MemLp (mulReal (sdirR m (fun z => v z m)) F) 2 (cellMeas c) :=
      (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v m) m).continuous (hv1 m m) hmF).1
    have hm_vdF : MemLp (mulReal (fun z => v z m) (pdir m F)) 2 (cellMeas c) :=
      (memLp_mulReal_of_bdd (hc_v m).continuous (hv0 m) (hmdF m)).1
    have hsplit : (∫ y in B0579.cell c,
        (inner ℂ (mulReal (sdirR m (fun z => v z m)) F y +
          mulReal (fun z => v z m) (pdir m F) y) (F y) : ℂ)) =
        (∫ y in B0579.cell c,
          (inner ℂ (mulReal (sdirR m (fun z => v z m)) F y) (F y) : ℂ)) +
        (∫ y in B0579.cell c,
          (inner ℂ (mulReal (fun z => v z m) (pdir m F) y) (F y) : ℂ)) := by
      have heq : (fun y => (inner ℂ (mulReal (sdirR m (fun z => v z m)) F y +
          mulReal (fun z => v z m) (pdir m F) y) (F y) : ℂ)) =
          fun y => (inner ℂ (mulReal (sdirR m (fun z => v z m)) F y) (F y) : ℂ) +
            (inner ℂ (mulReal (fun z => v z m) (pdir m F) y) (F y) : ℂ) :=
        funext fun y => inner_add_left _ _ _
      rw [heq, integral_add (integrableOn_inner_cell hm_dvF hmF)
        (integrableOn_inner_cell hm_vdF hmF)]
    have hlhs : (∫ y in B0579.cell c,
        (inner ℂ (F y) (mulReal (fun z => v z m) (pdir m F) y) : ℂ)) =
        ∫ y in B0579.cell c, (inner ℂ (mulReal (fun z => v z m) F y) (pdir m F y) : ℂ) :=
      integral_congr_ae (ae_of_all _ hsym_pt)
    have hconj : (∫ y in B0579.cell c,
        (inner ℂ (mulReal (fun z => v z m) (pdir m F) y) (F y) : ℂ)).re =
        (∫ y in B0579.cell c,
          (inner ℂ (F y) (mulReal (fun z => v z m) (pdir m F) y) : ℂ)).re := by
      have hre1 : (∫ y in B0579.cell c,
          (inner ℂ (mulReal (fun z => v z m) (pdir m F) y) (F y) : ℂ)).re =
          ∫ y in B0579.cell c,
            ((inner ℂ (mulReal (fun z => v z m) (pdir m F) y) (F y) : ℂ)).re := by
        simpa only [RCLike.re_to_complex] using
          (integral_re (integrableOn_inner_cell hm_vdF hmF)).symm
      have hre2 : (∫ y in B0579.cell c,
          (inner ℂ (F y) (mulReal (fun z => v z m) (pdir m F) y) : ℂ)).re =
          ∫ y in B0579.cell c,
            ((inner ℂ (F y) (mulReal (fun z => v z m) (pdir m F) y) : ℂ)).re := by
        simpa only [RCLike.re_to_complex] using
          (integral_re (integrableOn_inner_cell hmF hm_vdF)).symm
      rw [hre1, hre2]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only
      rw [← inner_conj_symm (mulReal (fun z => v z m) (pdir m F) y) (F y), Complex.conj_re]
    have hdiag : (∫ y in B0579.cell c,
        (inner ℂ (mulReal (sdirR m (fun z => v z m)) F y) (F y) : ℂ)).re =
        ∫ y in B0579.cell c, sdirR m (fun z => v z m) y * ‖F y‖ ^ 2 := by
      have hre1 : (∫ y in B0579.cell c,
          (inner ℂ (mulReal (sdirR m (fun z => v z m)) F y) (F y) : ℂ)).re =
          ∫ y in B0579.cell c,
            ((inner ℂ (mulReal (sdirR m (fun z => v z m)) F y) (F y) : ℂ)).re := by
        simpa only [RCLike.re_to_complex] using
          (integral_re (integrableOn_inner_cell hm_dvF hmF)).symm
      rw [hre1]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only [mulReal]
      rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul, ← RCLike.re_to_complex,
        inner_self_eq_norm_sq]
    have hre_h1 := congrArg Complex.re h1
    rw [hsplit, Complex.add_re, Complex.neg_re, ← hlhs, hconj, hdiag] at hre_h1
    linarith
  have hi_add : (∫ y in B0579.cell c, (inner ℂ (F y) (T0 y + T1 y) : ℂ)).re =
      (∫ y in B0579.cell c, (inner ℂ (F y) (T0 y) : ℂ)).re +
        (∫ y in B0579.cell c, (inner ℂ (F y) (T1 y) : ℂ)).re := by
    have heq : (fun y => (inner ℂ (F y) (T0 y + T1 y) : ℂ)) =
        fun y => (inner ℂ (F y) (T0 y) : ℂ) + (inner ℂ (F y) (T1 y) : ℂ) :=
      funext fun y => inner_add_right _ _ _
    rw [heq, integral_add (integrableOn_inner_cell hmF hmT0) (integrableOn_inner_cell hmF hmT1),
      Complex.add_re]
  change (∫ y in B0579.cell c, (inner ℂ (F y) (T0 y + T1 y) : ℂ)).re = 0
  rw [hi_add, hibp 0, hibp 1]
  have hi_div0 : IntegrableOn (fun y => sdirR 0 (fun z => v z 0) y * ‖F y‖ ^ 2) (B0579.cell c) := by
    have hm0 := (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 0) 0).continuous (hv1 0 0) hmF).1
    have hre := Complex.reCLM.integrable_comp (integrableOn_inner_cell hm0 hmF)
    refine hre.congr (ae_of_all _ fun y => ?_)
    dsimp only [Function.comp_apply, Complex.reCLM_apply, mulReal]
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul, ← RCLike.re_to_complex,
      inner_self_eq_norm_sq]
  have hi_div1 : IntegrableOn (fun y => sdirR 1 (fun z => v z 1) y * ‖F y‖ ^ 2) (B0579.cell c) := by
    have hm1 := (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 1) 1).continuous (hv1 1 1) hmF).1
    have hre := Complex.reCLM.integrable_comp (integrableOn_inner_cell hm1 hmF)
    refine hre.congr (ae_of_all _ fun y => ?_)
    dsimp only [Function.comp_apply, Complex.reCLM_apply, mulReal]
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul, ← RCLike.re_to_complex,
      inner_self_eq_norm_sq]
  have hsum_zero : (∫ y in B0579.cell c, sdirR 0 (fun z => v z 0) y * ‖F y‖ ^ 2) +
      (∫ y in B0579.cell c, sdirR 1 (fun z => v z 1) y * ‖F y‖ ^ 2) = 0 := by
    rw [← integral_add hi_div0 hi_div1]
    have hzero : (fun y : B0579.Plane =>
        sdirR 0 (fun z => v z 0) y * ‖F y‖ ^ 2 + sdirR 1 (fun z => v z 1) y * ‖F y‖ ^ 2) =
        fun _ => 0 := by
      funext y
      have hd0 : Differentiable ℝ (fun z => v z 0) := (hc_v 0).differentiable (by simp)
      have hd1 : Differentiable ℝ (fun z => v z 1) := (hc_v 1).differentiable (by simp)
      have hq : sdirR 0 (fun z => v z 0) y = UnforcedLeray.Cyl.partialQ (fun z => v z 0) y :=
        (UnforcedLeray.Cyl.partialQ_eq_fderiv hd0 y).symm
      have hη : sdirR 1 (fun z => v z 1) y = UnforcedLeray.Cyl.partialEta (fun z => v z 1) y :=
        (UnforcedLeray.Cyl.partialEta_eq_fderiv hd1 y).symm
      rw [← add_mul, hq, hη]
      change UnforcedLeray.Cyl.divergence v y * ‖F y‖ ^ 2 = 0
      rw [hdiv y, zero_mul]
    rw [hzero, integral_zero]
  have _ := hC
  linarith

/-! ## 6. Train coordinate jet bounds up to order 3 -/

def vecDir (i : Fin 2) (V : B0579.Plane → UnforcedLeray.Train.Vec) (z : B0579.Plane) :
    UnforcedLeray.Train.Vec :=
  fderiv ℝ V z (B0579.dir i)

lemma norm_b0579_dir (i : Fin 2) : ‖B0579.dir i‖ = 1 := by
  fin_cases i <;> simp [B0579.dir, Prod.norm_def]

lemma vecIter_eq_iteratedFDeriv {V : B0579.Plane → UnforcedLeray.Train.Vec}
    (hV : ContDiff ℝ ∞ V) :
    (∀ z, V z = iteratedFDeriv ℝ 0 V z ![]) ∧
    (∀ i₁ z, vecDir i₁ V z = iteratedFDeriv ℝ 1 V z ![B0579.dir i₁]) ∧
    (∀ i₁ i₂ z, vecDir i₁ (vecDir i₂ V) z =
      iteratedFDeriv ℝ 2 V z ![B0579.dir i₁, B0579.dir i₂]) ∧
    (∀ i₁ i₂ i₃ z, vecDir i₁ (vecDir i₂ (vecDir i₃ V)) z =
      iteratedFDeriv ℝ 3 V z ![B0579.dir i₁, B0579.dir i₂, B0579.dir i₃]) := by
  have step : ∀ (n : ℕ) (m : Fin n → B0579.Plane) (i : Fin 2) (z : B0579.Plane),
      iteratedFDeriv ℝ (n + 1) V z (Fin.cons (B0579.dir i) m) =
        fderiv ℝ (fun y => iteratedFDeriv ℝ n V y m) z (B0579.dir i) := by
    intro n m i z
    rw [iteratedFDeriv_succ_apply_left]
    have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ n V) :=
      hV.iteratedFDeriv_right (m := ∞) (i := n) (by simp)
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n V) z :=
      hD.contDiffAt.differentiableAt (by simp)
    exact (fderiv_continuousMultilinear_apply_const_apply hdiff m (B0579.dir i)).symm
  refine ⟨fun z => by simp [iteratedFDeriv_zero_apply], ?_, ?_, ?_⟩
  · intro i₁ z
    have h1 := step 0 ![] i₁ z
    have hcons : Fin.cons (B0579.dir i₁) (![] : Fin 0 → B0579.Plane) = ![B0579.dir i₁] := by
      funext j; fin_cases j; rfl
    rw [hcons] at h1
    simp only [iteratedFDeriv_zero_apply] at h1
    exact h1.symm
  · intro i₁ i₂ z
    have h1 : vecDir i₂ V = fun y => iteratedFDeriv ℝ 1 V y ![B0579.dir i₂] := by
      funext y
      have h0 := step 0 ![] i₂ y
      have hcons : Fin.cons (B0579.dir i₂) (![] : Fin 0 → B0579.Plane) = ![B0579.dir i₂] := by
        funext j; fin_cases j; rfl
      rw [hcons] at h0
      simp only [iteratedFDeriv_zero_apply] at h0
      exact h0.symm
    have h2 := step 1 ![B0579.dir i₂] i₁ z
    have hcons : Fin.cons (B0579.dir i₁) ![B0579.dir i₂] = ![B0579.dir i₁, B0579.dir i₂] := by
      funext j; fin_cases j <;> rfl
    rw [hcons, ← h1] at h2
    exact h2.symm
  · intro i₁ i₂ i₃ z
    have h2_eq : vecDir i₂ (vecDir i₃ V) =
        fun y => iteratedFDeriv ℝ 2 V y ![B0579.dir i₂, B0579.dir i₃] := by
      funext y
      have h1 : vecDir i₃ V = fun q => iteratedFDeriv ℝ 1 V q ![B0579.dir i₃] := by
        funext q
        have h0 := step 0 ![] i₃ q
        have hc0 : Fin.cons (B0579.dir i₃) (![] : Fin 0 → B0579.Plane) = ![B0579.dir i₃] := by
          funext j; fin_cases j; rfl
        rw [hc0] at h0
        simp only [iteratedFDeriv_zero_apply] at h0
        exact h0.symm
      have hs := step 1 ![B0579.dir i₃] i₂ y
      have hc1 : Fin.cons (B0579.dir i₂) ![B0579.dir i₃] = ![B0579.dir i₂, B0579.dir i₃] := by
        funext j; fin_cases j <;> rfl
      rw [hc1, ← h1] at hs
      exact hs.symm
    have h3 := step 2 ![B0579.dir i₂, B0579.dir i₃] i₁ z
    have hcons : Fin.cons (B0579.dir i₁) ![B0579.dir i₂, B0579.dir i₃] =
        ![B0579.dir i₁, B0579.dir i₂, B0579.dir i₃] := by
      funext j; fin_cases j <;> rfl
    rw [hcons, ← h2_eq] at h3
    exact h3.symm

lemma sdirR_coord_eq_vecDir {V : B0579.Plane → UnforcedLeray.Train.Vec}
    (hV : ContDiff ℝ ∞ V) (i k : Fin 2) :
    sdirR i (fun z => V z k) = fun z => vecDir i V z k := by
  funext z
  let πk : UnforcedLeray.Train.Vec →L[ℝ] ℝ := EuclideanSpace.proj k
  have hc := (πk.hasFDerivAt.comp z (hV.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  unfold sdirR vecDir
  change fderiv ℝ (πk ∘ V) z (B0579.dir i) = πk (fderiv ℝ V z (B0579.dir i))
  rw [hc, ContinuousLinearMap.comp_apply]

lemma contDiff_vecDir {V : B0579.Plane → UnforcedLeray.Train.Vec}
    (hV : ContDiff ℝ ∞ V) (i : Fin 2) :
    ContDiff ℝ ∞ (vecDir i V) :=
  ((contDiff_infty_iff_fderiv.1 hV).2).clm_apply contDiff_const

lemma train_coord_bounds {C_tr : ℝ} {V : B0579.Plane → UnforcedLeray.Train.Vec}
    (hV : ContDiff ℝ ∞ V)
    (hb : ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j V z‖ ≤ C_tr) :
    (∀ k : Fin 2, ∀ z, |V z k| ≤ C_tr) ∧
    (∀ i k : Fin 2, ∀ z, |sdirR i (fun q => V q k) z| ≤ C_tr) ∧
    (∀ i₁ i₂ k : Fin 2, ∀ z, |sdirR i₁ (sdirR i₂ (fun q => V q k)) z| ≤ C_tr) ∧
    (∀ i₁ i₂ i₃ k : Fin 2, ∀ z,
      |sdirR i₁ (sdirR i₂ (sdirR i₃ (fun q => V q k))) z| ≤ C_tr) := by
  obtain ⟨e0, e1, e2, e3⟩ := vecIter_eq_iteratedFDeriv hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k z
    calc |V z k| = ‖V z k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖V z‖ := PiLp.norm_apply_le (V z) k
      _ = ‖iteratedFDeriv ℝ 0 V z ![]‖ := by rw [← e0 z]
      _ ≤ ‖iteratedFDeriv ℝ 0 V z‖ * ∏ j : Fin 0, ‖(![] : Fin 0 → B0579.Plane) j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 0 V z‖ := by simp
      _ ≤ C_tr := hb 0 (by decide) z
  · intro i k z
    rw [sdirR_coord_eq_vecDir hV i k]
    calc |vecDir i V z k| = ‖vecDir i V z k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖vecDir i V z‖ := PiLp.norm_apply_le _ k
      _ = ‖iteratedFDeriv ℝ 1 V z ![B0579.dir i]‖ := by rw [← e1 i z]
      _ ≤ ‖iteratedFDeriv ℝ 1 V z‖ * ∏ j : Fin 1, ‖(![B0579.dir i] : Fin 1 → B0579.Plane) j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 V z‖ := by simp [norm_b0579_dir]
      _ ≤ C_tr := hb 1 (by decide) z
  · intro i₁ i₂ k z
    rw [sdirR_coord_eq_vecDir hV i₂ k, sdirR_coord_eq_vecDir (contDiff_vecDir hV i₂) i₁ k]
    calc |vecDir i₁ (vecDir i₂ V) z k| = ‖vecDir i₁ (vecDir i₂ V) z k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖vecDir i₁ (vecDir i₂ V) z‖ := PiLp.norm_apply_le _ k
      _ = ‖iteratedFDeriv ℝ 2 V z ![B0579.dir i₁, B0579.dir i₂]‖ := by rw [← e2 i₁ i₂ z]
      _ ≤ ‖iteratedFDeriv ℝ 2 V z‖ *
          ∏ j : Fin 2, ‖(![B0579.dir i₁, B0579.dir i₂] : Fin 2 → B0579.Plane) j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 V z‖ := by simp [Fin.prod_univ_two, norm_b0579_dir]
      _ ≤ C_tr := hb 2 (by decide) z
  · intro i₁ i₂ i₃ k z
    rw [sdirR_coord_eq_vecDir hV i₃ k, sdirR_coord_eq_vecDir (contDiff_vecDir hV i₃) i₂ k,
      sdirR_coord_eq_vecDir (contDiff_vecDir (contDiff_vecDir hV i₃) i₂) i₁ k]
    calc |vecDir i₁ (vecDir i₂ (vecDir i₃ V)) z k|
        = ‖vecDir i₁ (vecDir i₂ (vecDir i₃ V)) z k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖vecDir i₁ (vecDir i₂ (vecDir i₃ V)) z‖ := PiLp.norm_apply_le _ k
      _ = ‖iteratedFDeriv ℝ 3 V z ![B0579.dir i₁, B0579.dir i₂, B0579.dir i₃]‖ := by
          rw [← e3 i₁ i₂ i₃ z]
      _ ≤ ‖iteratedFDeriv ℝ 3 V z‖ *
          ∏ j : Fin 3, ‖(![B0579.dir i₁, B0579.dir i₂, B0579.dir i₃] : Fin 3 → B0579.Plane) j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 3 V z‖ := by simp [Fin.prod_univ_three, norm_b0579_dir]
      _ ≤ C_tr := hb 3 (by decide) z

/-! ## 7. Slice convective decomposition and energy hierarchy at Levels 0, 1, 2 -/

def stretchSlice (V : B0579.Plane → UnforcedLeray.Train.Vec) (W : B0579.Plane → CMerid)
    (y : B0579.Plane) : CMerid :=
  ∑ k : Fin 2, ∑ m : Fin 2,
    mulReal (sdirR m (fun z => V z k)) (fun z => compCLM m k (W z)) y

def bvSlice (V : B0579.Plane → UnforcedLeray.Train.Vec) (W : B0579.Plane → CMerid)
    (y : B0579.Plane) : CMerid :=
  (mulReal (fun z => V z 0) (pdir 0 W) y + mulReal (fun z => V z 1) (pdir 1 W) y) +
    stretchSlice V W y

lemma flatBv_slice_eq {ν c σ τ : ℝ} (tr : B0140.TrainSol ν c) {w : CProf}
    (hw : ContDiffOn ℝ ∞ w (stripSet σ)) (hτ : τ ∈ Ioo σ (σ + 2)) :
    (fun y => flatBv tr w (F8U.pd 0 w) (F8U.pd 1 w) (τ, y)) =
      bvSlice (tr.v τ) (F8U.slice w τ) := by
  funext y
  have hd0 : F8U.pd 0 w (τ, y) = pdir 0 (F8U.slice w τ) y :=
    (congrFun (pdir_slice_eq hw hτ 0) y).symm
  have hd1 : F8U.pd 1 w (τ, y) = pdir 1 (F8U.slice w τ) y :=
    (congrFun (pdir_slice_eq hw hτ 1) y).symm
  ext k
  unfold flatBv bvSlice stretchSlice mulReal sdirR
  rw [hd0, hd1]
  simp only [Fin.sum_univ_two, compCLM_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    B0579.dir, Matrix.cons_val_zero, Matrix.cons_val_one, F8U.slice]
  fin_cases k <;> simp <;> ring

lemma stretchSlice_props {c C_tr : ℝ} (hC : 0 < C_tr)
    {V : B0579.Plane → UnforcedLeray.Train.Vec}
    (hV : ContDiff ℝ ∞ V) (hVp : UnforcedLeray.Cyl.IsPeriodic c V)
    (hb : ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j V z‖ ≤ C_tr)
    {W : B0579.Plane → CMerid} (hW : ContDiff ℝ ∞ W) (hWp : UnforcedLeray.Cyl.IsPeriodic c W)
    (hm0 : MemLp W 2 (cellMeas c))
    (hm1 : ∀ i : Fin 2, MemLp (pdir i W) 2 (cellMeas c))
    (hm2 : ∀ i j : Fin 2, MemLp (pdir i (pdir j W)) 2 (cellMeas c)) :
    ContDiff ℝ ∞ (stretchSlice V W) ∧
    UnforcedLeray.Cyl.IsPeriodic c (stretchSlice V W) ∧
    MemLp (stretchSlice V W) 2 (cellMeas c) ∧
    (F8U.cellL2 c (stretchSlice V W)).toReal ≤ 4 * C_tr * (F8U.cellL2 c W).toReal ∧
    (∀ i : Fin 2, MemLp (pdir i (stretchSlice V W)) 2 (cellMeas c) ∧
      (F8U.cellL2 c (pdir i (stretchSlice V W))).toReal ≤
        4 * C_tr * ((F8U.cellL2 c W).toReal + (F8U.cellL2 c (pdir i W)).toReal)) ∧
    (MemLp (plap (stretchSlice V W)) 2 (cellMeas c) ∧
      (F8U.cellL2 c (plap (stretchSlice V W))).toReal ≤
        8 * C_tr * ((F8U.cellL2 c W).toReal +
          ((F8U.cellL2 c (pdir 0 W)).toReal + (F8U.cellL2 c (pdir 1 W)).toReal) +
          (F8U.cellL2 c (plap W)).toReal)) := by
  obtain ⟨_, b1, b2, b3⟩ := train_coord_bounds hV hb
  have hc_a : ∀ k m : Fin 2, ContDiff ℝ ∞ (sdirR m (fun z => V z k)) :=
    fun k m => contDiff_sdirR ((EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp hV) m
  have hp_a : ∀ k m : Fin 2, UnforcedLeray.Cyl.IsPeriodic c (sdirR m (fun z => V z k)) := by
    intro k m z
    rw [sdirR_coord_eq_vecDir hV m k]
    have hfun : (fun q : B0579.Plane => V (q + ((c, 0) : B0579.Plane))) = V := by
      funext q
      have hq : q + ((c, 0) : B0579.Plane) = (q.1 + c, q.2) := by ext <;> simp
      rw [hq]; exact hVp q
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := V) (x := z) ((c, 0) : B0579.Plane)
    rw [hfun] at h
    have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
    rw [hz] at h
    unfold vecDir; dsimp only; rw [← h]
  let term (k m : Fin 2) : B0579.Plane → CMerid :=
    mulReal (sdirR m (fun z => V z k)) (fun z => compCLM m k (W z))
  have hc_cW : ∀ k m : Fin 2, ContDiff ℝ ∞ (fun z => compCLM m k (W z)) :=
    fun k m => (compCLM m k).contDiff.comp hW
  have hS_eq : stretchSlice V W = fun y => (term 0 0 y + term 0 1 y) + (term 1 0 y + term 1 1 y) := by
    funext y; unfold stretchSlice; simp [Fin.sum_univ_two, term]
  have hc_t : ∀ k m : Fin 2, ContDiff ℝ ∞ (term k m) :=
    fun k m => contDiff_mulReal (hc_a k m) (hc_cW k m)
  have hp_t : ∀ k m : Fin 2, UnforcedLeray.Cyl.IsPeriodic c (term k m) :=
    fun k m => periodic_mulReal (hp_a k m) (fun z => by rw [hWp z])
  have hmaxC : max C_tr 0 = C_tr := max_eq_left hC.le
  have hmax2C : max (2 * C_tr) 0 = 2 * C_tr := max_eq_left (by positivity)
  have hm_t : ∀ k m : Fin 2, MemLp (term k m) 2 (cellMeas c) ∧
      (F8U.cellL2 c (term k m)).toReal ≤ C_tr * (F8U.cellL2 c W).toReal := by
    intro k m
    obtain ⟨hm_cur, hbd_cur⟩ := memLp_mulReal_of_bdd (hc_a k m).continuous (b1 m k)
      (memLp_compCLM hm0 m k)
    rw [hmaxC] at hbd_cur
    exact ⟨hm_cur, hbd_cur.trans (mul_le_mul_of_nonneg_left (cellL2_compCLM_le hm0 m k) hC.le)⟩
  -- Helper: triangle inequality in .toReal for MemLp sums
  have tri2 : ∀ {A B : B0579.Plane → CMerid},
      MemLp A 2 (cellMeas c) → MemLp B 2 (cellMeas c) →
      (F8U.cellL2 c (fun y => A y + B y)).toReal ≤
        (F8U.cellL2 c A).toReal + (F8U.cellL2 c B).toReal := by
    intro A B hmA hmB
    have hle : F8U.cellL2 c (fun y => A y + B y) ≤ F8U.cellL2 c A + F8U.cellL2 c B :=
      eLpNorm_add_le hmA.aestronglyMeasurable hmB.aestronglyMeasurable one_le_two
    have htr := (ENNReal.toReal_le_toReal (hmA.add hmB).eLpNorm_ne_top
      (ENNReal.add_ne_top.mpr ⟨hmA.eLpNorm_ne_top, hmB.eLpNorm_ne_top⟩)).mpr hle
    rwa [ENNReal.toReal_add hmA.eLpNorm_ne_top hmB.eLpNorm_ne_top] at htr
  have tri4 : ∀ (F : Fin 2 → Fin 2 → B0579.Plane → CMerid),
      (∀ k m, MemLp (F k m) 2 (cellMeas c)) →
      MemLp (fun y => (F 0 0 y + F 0 1 y) + (F 1 0 y + F 1 1 y)) 2 (cellMeas c) ∧
      (F8U.cellL2 c (fun y => (F 0 0 y + F 0 1 y) + (F 1 0 y + F 1 1 y))).toReal ≤
        (F8U.cellL2 c (F 0 0)).toReal + (F8U.cellL2 c (F 0 1)).toReal +
          (F8U.cellL2 c (F 1 0)).toReal + (F8U.cellL2 c (F 1 1)).toReal := by
    intro F hmF
    have h0 : MemLp (fun y => F 0 0 y + F 0 1 y) 2 (cellMeas c) := (hmF 0 0).add (hmF 0 1)
    have h1 : MemLp (fun y => F 1 0 y + F 1 1 y) 2 (cellMeas c) := (hmF 1 0).add (hmF 1 1)
    refine ⟨h0.add h1, ?_⟩
    have b01 := tri2 (hmF 0 0) (hmF 0 1)
    have b11 := tri2 (hmF 1 0) (hmF 1 1)
    have btot := tri2 h0 h1
    linarith
  have hc_S : ContDiff ℝ ∞ (stretchSlice V W) := by
    rw [hS_eq]; exact ((hc_t 0 0).add (hc_t 0 1)).add ((hc_t 1 0).add (hc_t 1 1))
  have hp_S : UnforcedLeray.Cyl.IsPeriodic c (stretchSlice V W) := by
    intro z; rw [hS_eq]; dsimp; rw [hp_t 0 0 z, hp_t 0 1 z, hp_t 1 0 z, hp_t 1 1 z]
  obtain ⟨hm_S0, hbd_S0⟩ := tri4 term (fun k m => (hm_t k m).1)
  rw [← hS_eq] at hm_S0 hbd_S0
  refine ⟨hc_S, hp_S, hm_S0, ?_, ?_, ?_⟩
  · linarith [(hm_t 0 0).2, (hm_t 0 1).2, (hm_t 1 0).2, (hm_t 1 1).2]
  · intro i
    have hdt : ∀ k m : Fin 2, MemLp (pdir i (term k m)) 2 (cellMeas c) ∧
        (F8U.cellL2 c (pdir i (term k m))).toReal ≤
          C_tr * ((F8U.cellL2 c W).toReal + (F8U.cellL2 c (pdir i W)).toReal) := by
      intro k m
      have hp_eq := pdir_mulReal (hc_a k m) (hc_cW k m) i
      rw [pdir_compCLM hW m k i] at hp_eq
      obtain ⟨mA, bA⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_a k m) i).continuous
        (b2 i m k) (memLp_compCLM hm0 m k)
      obtain ⟨mB, bB⟩ := memLp_mulReal_of_bdd (hc_a k m).continuous (b1 m k)
        (memLp_compCLM (hm1 i) m k)
      rw [hmaxC] at bA bB
      have bA' := bA.trans (mul_le_mul_of_nonneg_left (cellL2_compCLM_le hm0 m k) hC.le)
      have bB' := bB.trans (mul_le_mul_of_nonneg_left (cellL2_compCLM_le (hm1 i) m k) hC.le)
      rw [hp_eq]
      exact ⟨mA.add mB, (tri2 mA mB).trans (by linarith)⟩
    have hpS_eq : pdir i (stretchSlice V W) =
        fun y => (pdir i (term 0 0) y + pdir i (term 0 1) y) +
          (pdir i (term 1 0) y + pdir i (term 1 1) y) := by
      rw [hS_eq, pdir_add ((hc_t 0 0).add (hc_t 0 1)) ((hc_t 1 0).add (hc_t 1 1)) i,
        pdir_add (hc_t 0 0) (hc_t 0 1) i, pdir_add (hc_t 1 0) (hc_t 1 1) i]
    obtain ⟨hm_dS, hbd_dS⟩ := tri4 (fun k m => pdir i (term k m)) (fun k m => (hdt k m).1)
    rw [← hpS_eq] at hm_dS hbd_dS
    exact ⟨hm_dS, hbd_dS.trans (by linarith [(hdt 0 0).2, (hdt 0 1).2, (hdt 1 0).2, (hdt 1 1).2])⟩
  · have hm_lapW : MemLp (plap W) 2 (cellMeas c) := (hm2 0 0).add (hm2 1 1)
    have hlt : ∀ k m : Fin 2, MemLp (plap (term k m)) 2 (cellMeas c) ∧
        (F8U.cellL2 c (plap (term k m))).toReal ≤
          2 * C_tr * ((F8U.cellL2 c W).toReal +
            ((F8U.cellL2 c (pdir 0 W)).toReal + (F8U.cellL2 c (pdir 1 W)).toReal) +
            (F8U.cellL2 c (plap W)).toReal) := by
      intro k m
      have hl_eq := plap_mulReal (hc_a k m) (hc_cW k m)
      rw [pdir_compCLM hW m k 0, pdir_compCLM hW m k 1, plap_compCLM hW m k] at hl_eq
      have hslap_bd : ∀ y, |slapR (sdirR m (fun z => V z k)) y| ≤ 2 * C_tr := by
        intro y
        unfold slapR
        exact (abs_add_le _ _).trans (by linarith [b3 0 0 m k y, b3 1 1 m k y])
      have hc_slap : Continuous (slapR (sdirR m (fun z => V z k))) :=
        ((contDiff_sdirR (contDiff_sdirR (hc_a k m) 0) 0).add
          (contDiff_sdirR (contDiff_sdirR (hc_a k m) 1) 1)).continuous
      obtain ⟨m1, l1⟩ := memLp_mulReal_of_bdd hc_slap hslap_bd (memLp_compCLM hm0 m k)
      obtain ⟨m20, l20⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_a k m) 0).continuous
        (b2 0 m k) (memLp_compCLM (hm1 0) m k)
      obtain ⟨m21, l21⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_a k m) 1).continuous
        (b2 1 m k) (memLp_compCLM (hm1 1) m k)
      obtain ⟨m3, l3⟩ := memLp_mulReal_of_bdd (hc_a k m).continuous (b1 m k)
        (memLp_compCLM hm_lapW m k)
      rw [hmax2C] at l1
      rw [hmaxC] at l20 l21 l3
      have l1' := l1.trans (mul_le_mul_of_nonneg_left (cellL2_compCLM_le hm0 m k) (by positivity))
      have l20' := l20.trans (mul_le_mul_of_nonneg_left (cellL2_compCLM_le (hm1 0) m k) hC.le)
      have l21' := l21.trans (mul_le_mul_of_nonneg_left (cellL2_compCLM_le (hm1 1) m k) hC.le)
      have l3' := l3.trans (mul_le_mul_of_nonneg_left (cellL2_compCLM_le hm_lapW m k) hC.le)
      have m20s : MemLp (fun y => (2 : ℝ) • mulReal (sdirR 0 (sdirR m (fun z => V z k)))
          (fun z => compCLM m k (pdir 0 W z)) y) 2 (cellMeas c) := m20.const_smul (2 : ℝ)
      have m21s : MemLp (fun y => (2 : ℝ) • mulReal (sdirR 1 (sdirR m (fun z => V z k)))
          (fun z => compCLM m k (pdir 1 W z)) y) 2 (cellMeas c) := m21.const_smul (2 : ℝ)
      have b20s : (F8U.cellL2 c (fun y => (2 : ℝ) • mulReal (sdirR 0 (sdirR m (fun z => V z k)))
          (fun z => compCLM m k (pdir 0 W z)) y)).toReal ≤
          2 * C_tr * (F8U.cellL2 c (pdir 0 W)).toReal := by
        have hsm : (F8U.cellL2 c (fun y => (2 : ℝ) • mulReal (sdirR 0 (sdirR m (fun z => V z k)))
            (fun z => compCLM m k (pdir 0 W z)) y)).toReal =
            2 * (F8U.cellL2 c (mulReal (sdirR 0 (sdirR m (fun z => V z k)))
              (fun z => compCLM m k (pdir 0 W z)))).toReal := by
          unfold F8U.cellL2
          change (eLpNorm ((2 : ℝ) • _) 2 (cellMeas c)).toReal = _
          rw [eLpNorm_const_smul (2 : ℝ) _ 2 (cellMeas c), ENNReal.toReal_mul, ← ofReal_norm,
            Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
            ENNReal.toReal_ofReal (by positivity)]
        rw [hsm]; linarith
      have b21s : (F8U.cellL2 c (fun y => (2 : ℝ) • mulReal (sdirR 1 (sdirR m (fun z => V z k)))
          (fun z => compCLM m k (pdir 1 W z)) y)).toReal ≤
          2 * C_tr * (F8U.cellL2 c (pdir 1 W)).toReal := by
        have hsm : (F8U.cellL2 c (fun y => (2 : ℝ) • mulReal (sdirR 1 (sdirR m (fun z => V z k)))
            (fun z => compCLM m k (pdir 1 W z)) y)).toReal =
            2 * (F8U.cellL2 c (mulReal (sdirR 1 (sdirR m (fun z => V z k)))
              (fun z => compCLM m k (pdir 1 W z)))).toReal := by
          unfold F8U.cellL2
          change (eLpNorm ((2 : ℝ) • _) 2 (cellMeas c)).toReal = _
          rw [eLpNorm_const_smul (2 : ℝ) _ 2 (cellMeas c), ENNReal.toReal_mul, ← ofReal_norm,
            Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
            ENNReal.toReal_ofReal (by positivity)]
        rw [hsm]; linarith
      have m2_sum : MemLp (fun y =>
          (2 : ℝ) • mulReal (sdirR 0 (sdirR m (fun z => V z k)))
            (fun z => compCLM m k (pdir 0 W z)) y +
          (2 : ℝ) • mulReal (sdirR 1 (sdirR m (fun z => V z k)))
            (fun z => compCLM m k (pdir 1 W z)) y) 2 (cellMeas c) := m20s.add m21s
      have m12_sum : MemLp (fun y =>
          mulReal (slapR (sdirR m (fun z => V z k))) (fun z => compCLM m k (W z)) y +
          ((2 : ℝ) • mulReal (sdirR 0 (sdirR m (fun z => V z k)))
            (fun z => compCLM m k (pdir 0 W z)) y +
           (2 : ℝ) • mulReal (sdirR 1 (sdirR m (fun z => V z k)))
            (fun z => compCLM m k (pdir 1 W z)) y)) 2 (cellMeas c) := m1.add m2_sum
      rw [hl_eq]
      refine ⟨m12_sum.add m3, ?_⟩
      have t_mid := tri2 m20s m21s
      have t_left := tri2 m1 m2_sum
      have t_all := tri2 m12_sum m3
      have hlap_nn : 0 ≤ C_tr * (F8U.cellL2 c (plap W)).toReal :=
        mul_nonneg hC.le ENNReal.toReal_nonneg
      linarith
    have hlapS_eq : plap (stretchSlice V W) =
        fun y => (plap (term 0 0) y + plap (term 0 1) y) +
          (plap (term 1 0) y + plap (term 1 1) y) := by
      rw [hS_eq, plap_add ((hc_t 0 0).add (hc_t 0 1)) ((hc_t 1 0).add (hc_t 1 1)),
        plap_add (hc_t 0 0) (hc_t 0 1), plap_add (hc_t 1 0) (hc_t 1 1)]
    obtain ⟨hm_lS, hbd_lS⟩ := tri4 (fun k m => plap (term k m)) (fun k m => (hlt k m).1)
    rw [← hlapS_eq] at hm_lS hbd_lS
    exact ⟨hm_lS, hbd_lS.trans (by linarith [(hlt 0 0).2, (hlt 0 1).2, (hlt 1 0).2, (hlt 1 1).2])⟩

lemma memLp_fun_add {c : ℝ} {F G : B0579.Plane → CMerid}
    (hF : MemLp F 2 (cellMeas c)) (hG : MemLp G 2 (cellMeas c)) :
    MemLp (fun y => F y + G y) 2 (cellMeas c) :=
  hF.add hG

lemma memLp_pdir_add {c : ℝ} {F G : B0579.Plane → CMerid}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i : Fin 2)
    (hmF : MemLp (pdir i F) 2 (cellMeas c)) (hmG : MemLp (pdir i G) 2 (cellMeas c)) :
    MemLp (pdir i (fun y => F y + G y)) 2 (cellMeas c) := by
  rw [pdir_add hF hG i]
  exact memLp_fun_add hmF hmG

lemma memLp_pdir2_add {c : ℝ} {F G : B0579.Plane → CMerid}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i : Fin 2)
    (hmF : MemLp (pdir i (pdir i F)) 2 (cellMeas c))
    (hmG : MemLp (pdir i (pdir i G)) 2 (cellMeas c)) :
    MemLp (pdir i (pdir i (fun y => F y + G y))) 2 (cellMeas c) := by
  rw [pdir_add hF hG i]
  exact memLp_pdir_add (contDiff_pdir hF i) (contDiff_pdir hG i) i hmF hmG

def trTermSlice (V : B0579.Plane → UnforcedLeray.Train.Vec) (W : B0579.Plane → CMerid)
    (y : B0579.Plane) : CMerid :=
  mulReal (fun z => V z 0) (pdir 0 W) y + mulReal (fun z => V z 1) (pdir 1 W) y

def trLapRemSlice (V : B0579.Plane → UnforcedLeray.Train.Vec) (W : B0579.Plane → CMerid)
    (y : B0579.Plane) : CMerid :=
  (mulReal (slapR (fun z => V z 0)) (pdir 0 W) y +
    mulReal (slapR (fun z => V z 1)) (pdir 1 W) y) +
  (((2 : ℝ) • mulReal (sdirR 0 (fun z => V z 0)) (pdir 0 (pdir 0 W)) y +
    (2 : ℝ) • mulReal (sdirR 1 (fun z => V z 0)) (pdir 1 (pdir 0 W)) y) +
   ((2 : ℝ) • mulReal (sdirR 0 (fun z => V z 1)) (pdir 0 (pdir 1 W)) y +
    (2 : ℝ) • mulReal (sdirR 1 (fun z => V z 1)) (pdir 1 (pdir 1 W)) y))

/-- Regularity, periodicity, and `L²` memberships of `bvSlice V W` up to order 2. -/
lemma bvSlice_reg_props {c C_tr : ℝ} (hc : 0 < c) (hC : 0 < C_tr)
    {V : B0579.Plane → UnforcedLeray.Train.Vec}
    (hV : ContDiff ℝ ∞ V) (hVp : UnforcedLeray.Cyl.IsPeriodic c V)
    (hb : ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j V z‖ ≤ C_tr)
    {W : B0579.Plane → CMerid} (hW : ContDiff ℝ ∞ W) (hWp : UnforcedLeray.Cyl.IsPeriodic c W)
    (hm0 : MemLp W 2 (cellMeas c))
    (hm1 : ∀ i : Fin 2, MemLp (pdir i W) 2 (cellMeas c))
    (hm2 : ∀ i j : Fin 2, MemLp (pdir i (pdir j W)) 2 (cellMeas c))
    (hm3 : ∀ i j k : Fin 2, MemLp (pdir i (pdir j (pdir k W))) 2 (cellMeas c)) :
    ContDiff ℝ ∞ (bvSlice V W) ∧
    UnforcedLeray.Cyl.IsPeriodic c (bvSlice V W) ∧
    MemLp (bvSlice V W) 2 (cellMeas c) ∧
    (∀ i : Fin 2, MemLp (pdir i (bvSlice V W)) 2 (cellMeas c)) ∧
    (∀ i : Fin 2, MemLp (pdir i (pdir i (bvSlice V W))) 2 (cellMeas c)) ∧
    MemLp (plap (bvSlice V W)) 2 (cellMeas c) ∧
    (∀ i : Fin 2, pdir i (trTermSlice V W) = fun y =>
      (mulReal (fun z => V z 0) (pdir 0 (pdir i W)) y +
        mulReal (fun z => V z 1) (pdir 1 (pdir i W)) y) +
      (mulReal (sdirR i (fun z => V z 0)) (pdir 0 W) y +
        mulReal (sdirR i (fun z => V z 1)) (pdir 1 W) y)) ∧
    plap (trTermSlice V W) = (fun y =>
      (mulReal (fun z => V z 0) (pdir 0 (plap W)) y +
        mulReal (fun z => V z 1) (pdir 1 (plap W)) y) + trLapRemSlice V W y) ∧
    MemLp (trLapRemSlice V W) 2 (cellMeas c) ∧
    (F8U.cellL2 c (trLapRemSlice V W)).toReal ≤
      2 * C_tr * ((F8U.cellL2 c (pdir 0 W)).toReal + (F8U.cellL2 c (pdir 1 W)).toReal) +
        8 * C_tr * (F8U.cellL2 c (plap W)).toReal := by
  obtain ⟨b0, b1, b2, b3⟩ := train_coord_bounds hV hb
  obtain ⟨hc_S, hp_S, hm_S, _, hd_S, hl_S⟩ :=
    stretchSlice_props hC hV hVp hb hW hWp hm0 hm1 hm2
  have hc_v : ∀ m : Fin 2, ContDiff ℝ ∞ (fun z => V z m) :=
    fun m => (EuclideanSpace.proj m : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp hV
  have hp_v : ∀ m : Fin 2, UnforcedLeray.Cyl.IsPeriodic c (fun z => V z m) :=
    fun m z => congrArg (fun u => u m) (hVp z)
  have hmaxC : max C_tr 0 = C_tr := max_eq_left hC.le
  have hmax2C : max (2 * C_tr) 0 = 2 * C_tr := max_eq_left (by positivity)
  have hc_tr : ContDiff ℝ ∞ (trTermSlice V W) :=
    (contDiff_mulReal (hc_v 0) (contDiff_pdir hW 0)).add
      (contDiff_mulReal (hc_v 1) (contDiff_pdir hW 1))
  have hp_tr : UnforcedLeray.Cyl.IsPeriodic c (trTermSlice V W) := fun z => by
    unfold trTermSlice
    rw [periodic_mulReal (hp_v 0) (periodic_pdir hWp 0) z,
      periodic_mulReal (hp_v 1) (periodic_pdir hWp 1) z]
  have hm_tr : MemLp (trTermSlice V W) 2 (cellMeas c) :=
    memLp_fun_add (memLp_mulReal_of_bdd (hc_v 0).continuous (b0 0) (hm1 0)).1
      (memLp_mulReal_of_bdd (hc_v 1).continuous (b0 1) (hm1 1)).1
  have hc_bv : ContDiff ℝ ∞ (bvSlice V W) := hc_tr.add hc_S
  have hp_bv : UnforcedLeray.Cyl.IsPeriodic c (bvSlice V W) := fun z => by
    show trTermSlice V W (z.1 + c, z.2) + stretchSlice V W (z.1 + c, z.2) =
      trTermSlice V W z + stretchSlice V W z
    rw [hp_tr z, hp_S z]
  have hm_bv : MemLp (bvSlice V W) 2 (cellMeas c) := memLp_fun_add hm_tr hm_S
  have hd_tr_eq : ∀ i : Fin 2, pdir i (trTermSlice V W) = fun y =>
      (mulReal (fun z => V z 0) (pdir 0 (pdir i W)) y +
        mulReal (fun z => V z 1) (pdir 1 (pdir i W)) y) +
      (mulReal (sdirR i (fun z => V z 0)) (pdir 0 W) y +
        mulReal (sdirR i (fun z => V z 1)) (pdir 1 W) y) := by
    intro i
    funext y
    unfold trTermSlice
    rw [pdir_add (contDiff_mulReal (hc_v 0) (contDiff_pdir hW 0))
        (contDiff_mulReal (hc_v 1) (contDiff_pdir hW 1)) i,
      pdir_mulReal (hc_v 0) (contDiff_pdir hW 0) i,
      pdir_mulReal (hc_v 1) (contDiff_pdir hW 1) i]
    dsimp only
    rw [funext (pdir_comm hW i 0), funext (pdir_comm hW i 1)]
    abel
  have hd_tr_mem : ∀ i : Fin 2, MemLp (pdir i (trTermSlice V W)) 2 (cellMeas c) := by
    intro i
    rw [hd_tr_eq i]
    exact memLp_fun_add
      (memLp_fun_add (memLp_mulReal_of_bdd (hc_v 0).continuous (b0 0) (hm2 0 i)).1
        (memLp_mulReal_of_bdd (hc_v 1).continuous (b0 1) (hm2 1 i)).1)
      (memLp_fun_add
        (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 0) i).continuous (b1 i 0) (hm1 0)).1
        (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 1) i).continuous (b1 i 1) (hm1 1)).1)
  have hd_bv_mem : ∀ i : Fin 2, MemLp (pdir i (bvSlice V W)) 2 (cellMeas c) :=
    fun i => memLp_pdir_add hc_tr hc_S i (hd_tr_mem i) (hd_S i).1
  have hm_d2_bv : ∀ i : Fin 2, MemLp (pdir i (pdir i (bvSlice V W))) 2 (cellMeas c) := by
    intro i
    let termS (k m : Fin 2) : B0579.Plane → CMerid :=
      mulReal (sdirR m (fun z => V z k)) (fun z => compCLM m k (W z))
    have hc_cW : ∀ k m : Fin 2, ContDiff ℝ ∞ (fun z => compCLM m k (W z)) :=
      fun k m => (compCLM m k).contDiff.comp hW
    have hc_s : ∀ k m, ContDiff ℝ ∞ (termS k m) := fun k m =>
      contDiff_mulReal (contDiff_sdirR (hc_v k) m) (hc_cW k m)
    have hm_d2_termS : ∀ k m : Fin 2, MemLp (pdir i (pdir i (termS k m))) 2 (cellMeas c) := by
      intro k m
      have hc_akm : ContDiff ℝ ∞ (sdirR m (fun z => V z k)) := contDiff_sdirR (hc_v k) m
      dsimp only [termS]
      rw [pdir_mulReal hc_akm (hc_cW k m) i,
        pdir_add (contDiff_mulReal (contDiff_sdirR hc_akm i) (hc_cW k m))
          (contDiff_mulReal hc_akm (contDiff_pdir (hc_cW k m) i)) i,
        pdir_mulReal (contDiff_sdirR hc_akm i) (hc_cW k m) i,
        pdir_mulReal hc_akm (contDiff_pdir (hc_cW k m) i) i,
        pdir_compCLM hW m k i, pdir_compCLM (contDiff_pdir hW i) m k i]
      exact memLp_fun_add
        (memLp_fun_add
          (memLp_mulReal_of_bdd (contDiff_sdirR (contDiff_sdirR hc_akm i) i).continuous
            (b3 i i m k) (memLp_compCLM hm0 m k)).1
          (memLp_mulReal_of_bdd (contDiff_sdirR hc_akm i).continuous
            (b2 i m k) (memLp_compCLM (hm1 i) m k)).1)
        (memLp_fun_add
          (memLp_mulReal_of_bdd (contDiff_sdirR hc_akm i).continuous
            (b2 i m k) (memLp_compCLM (hm1 i) m k)).1
          (memLp_mulReal_of_bdd hc_akm.continuous
            (b1 m k) (memLp_compCLM (hm2 i i) m k)).1)
    have hm_d2_tr_m : ∀ m : Fin 2,
        MemLp (pdir i (pdir i (mulReal (fun z => V z m) (pdir m W)))) 2 (cellMeas c) := by
      intro m
      rw [pdir_mulReal (hc_v m) (contDiff_pdir hW m) i,
        pdir_add (contDiff_mulReal (contDiff_sdirR (hc_v m) i) (contDiff_pdir hW m))
          (contDiff_mulReal (hc_v m) (contDiff_pdir (contDiff_pdir hW m) i)) i,
        pdir_mulReal (contDiff_sdirR (hc_v m) i) (contDiff_pdir hW m) i,
        pdir_mulReal (hc_v m) (contDiff_pdir (contDiff_pdir hW m) i) i]
      exact memLp_fun_add
        (memLp_fun_add
          (memLp_mulReal_of_bdd (contDiff_sdirR (contDiff_sdirR (hc_v m) i) i).continuous
            (b2 i i m) (hm1 m)).1
          (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v m) i).continuous
            (b1 i m) (hm2 i m)).1)
        (memLp_fun_add
          (memLp_mulReal_of_bdd (contDiff_sdirR (hc_v m) i).continuous
            (b1 i m) (hm2 i m)).1
          (memLp_mulReal_of_bdd (hc_v m).continuous
            (b0 m) (hm3 i i m)).1)
    have hm_d2_tr : MemLp (pdir i (pdir i (trTermSlice V W))) 2 (cellMeas c) :=
      memLp_pdir2_add (contDiff_mulReal (hc_v 0) (contDiff_pdir hW 0))
        (contDiff_mulReal (hc_v 1) (contDiff_pdir hW 1)) i (hm_d2_tr_m 0) (hm_d2_tr_m 1)
    have hS_eq : stretchSlice V W = fun y =>
        (termS 0 0 y + termS 0 1 y) + (termS 1 0 y + termS 1 1 y) := by
      funext y; unfold stretchSlice; simp [Fin.sum_univ_two, termS]
    have hm_d2_S : MemLp (pdir i (pdir i (stretchSlice V W))) 2 (cellMeas c) := by
      rw [hS_eq]
      exact memLp_pdir2_add ((hc_s 0 0).add (hc_s 0 1)) ((hc_s 1 0).add (hc_s 1 1)) i
        (memLp_pdir2_add (hc_s 0 0) (hc_s 0 1) i (hm_d2_termS 0 0) (hm_d2_termS 0 1))
        (memLp_pdir2_add (hc_s 1 0) (hc_s 1 1) i (hm_d2_termS 1 0) (hm_d2_termS 1 1))
    exact memLp_pdir2_add hc_tr hc_S i hm_d2_tr hm_d2_S
  have hm_plap_bv : MemLp (plap (bvSlice V W)) 2 (cellMeas c) :=
    memLp_fun_add (hm_d2_bv 0) (hm_d2_bv 1)
  have hl_tr_eq : plap (trTermSlice V W) = fun y =>
      (mulReal (fun z => V z 0) (pdir 0 (plap W)) y +
        mulReal (fun z => V z 1) (pdir 1 (plap W)) y) + trLapRemSlice V W y := by
    funext y
    unfold trTermSlice trLapRemSlice
    rw [plap_add (contDiff_mulReal (hc_v 0) (contDiff_pdir hW 0))
        (contDiff_mulReal (hc_v 1) (contDiff_pdir hW 1)),
      plap_mulReal (hc_v 0) (contDiff_pdir hW 0),
      plap_mulReal (hc_v 1) (contDiff_pdir hW 1)]
    dsimp only
    rw [funext (plap_pdir_comm hW 0), funext (plap_pdir_comm hW 1)]
    abel
  have hslap_v_bd : ∀ m : Fin 2, ∀ y, |slapR (fun z => V z m) y| ≤ 2 * C_tr := by
    intro m y; unfold slapR
    exact (abs_add_le _ _).trans (by linarith [b2 0 0 m y, b2 1 1 m y])
  have hc_slap_v : ∀ m : Fin 2, Continuous (slapR (fun z => V z m)) :=
    fun m => ((contDiff_sdirR (contDiff_sdirR (hc_v m) 0) 0).add
      (contDiff_sdirR (contDiff_sdirR (hc_v m) 1) 1)).continuous
  obtain ⟨mr0, br0⟩ := memLp_mulReal_of_bdd (hc_slap_v 0) (hslap_v_bd 0) (hm1 0)
  obtain ⟨mr1, br1⟩ := memLp_mulReal_of_bdd (hc_slap_v 1) (hslap_v_bd 1) (hm1 1)
  obtain ⟨mc00, bc00⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 0) 0).continuous (b1 0 0) (hm2 0 0)
  obtain ⟨mc10, bc10⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 0) 1).continuous (b1 1 0) (hm2 1 0)
  obtain ⟨mc01, bc01⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 1) 0).continuous (b1 0 1) (hm2 0 1)
  obtain ⟨mc11, bc11⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 1) 1).continuous (b1 1 1) (hm2 1 1)
  rw [hmax2C] at br0 br1
  rw [hmaxC] at bc00 bc10 bc01 bc11
  have hm_trLapRem : MemLp (trLapRemSlice V W) 2 (cellMeas c) :=
    memLp_fun_add (memLp_fun_add mr0 mr1)
      (memLp_fun_add (memLp_fun_add (mc00.const_smul (2 : ℝ)) (mc10.const_smul (2 : ℝ)))
        (memLp_fun_add (mc01.const_smul (2 : ℝ)) (mc11.const_smul (2 : ℝ))))
  have hplap_sq := cellL2_plap_sq_eq_sum hc hW hWp hm1 hm2 hm3
  have hd2_le_plap : ∀ i j : Fin 2,
      (F8U.cellL2 c (pdir i (pdir j W))).toReal ≤ (F8U.cellL2 c (plap W)).toReal := by
    intro i j
    have hsq_le : (F8U.cellL2 c (pdir i (pdir j W))).toReal ^ 2 ≤
        (F8U.cellL2 c (plap W)).toReal ^ 2 := by
      rw [hplap_sq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
        nlinarith [sq_nonneg (F8U.cellL2 c (pdir 0 (pdir 0 W))).toReal,
          sq_nonneg (F8U.cellL2 c (pdir 0 (pdir 1 W))).toReal,
          sq_nonneg (F8U.cellL2 c (pdir 1 (pdir 0 W))).toReal,
          sq_nonneg (F8U.cellL2 c (pdir 1 (pdir 1 W))).toReal]
    exact (abs_le_of_sq_le_sq' hsq_le ENNReal.toReal_nonneg).2
  have tri_real : ∀ {A B : B0579.Plane → CMerid},
      MemLp A 2 (cellMeas c) → MemLp B 2 (cellMeas c) →
      (F8U.cellL2 c (fun y => A y + B y)).toReal ≤
        (F8U.cellL2 c A).toReal + (F8U.cellL2 c B).toReal := by
    intro A B mA mB
    have hle := eLpNorm_add_le mA.aestronglyMeasurable mB.aestronglyMeasurable one_le_two
    have htr := (ENNReal.toReal_le_toReal (mA.add mB).eLpNorm_ne_top
      (ENNReal.add_ne_top.mpr ⟨mA.eLpNorm_ne_top, mB.eLpNorm_ne_top⟩)).mpr hle
    rwa [ENNReal.toReal_add mA.eLpNorm_ne_top mB.eLpNorm_ne_top] at htr
  have smul2_real : ∀ {A : B0579.Plane → CMerid},
      (F8U.cellL2 c (fun y => (2 : ℝ) • A y)).toReal = 2 * (F8U.cellL2 c A).toReal := by
    intro A
    unfold F8U.cellL2
    change (eLpNorm ((2 : ℝ) • A) 2 (cellMeas c)).toReal = _
    rw [eLpNorm_const_smul (2 : ℝ) A 2 (cellMeas c), ENNReal.toReal_mul, ← ofReal_norm,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2), ENNReal.toReal_ofReal (by positivity)]
  have b_rem : (F8U.cellL2 c (trLapRemSlice V W)).toReal ≤
      2 * C_tr * ((F8U.cellL2 c (pdir 0 W)).toReal + (F8U.cellL2 c (pdir 1 W)).toReal) +
        8 * C_tr * (F8U.cellL2 c (plap W)).toReal := by
    have t1 := tri_real mr0 mr1
    have t2 := tri_real (mc00.const_smul (2 : ℝ)) (mc10.const_smul (2 : ℝ))
    have t3 := tri_real (mc01.const_smul (2 : ℝ)) (mc11.const_smul (2 : ℝ))
    have t4 := tri_real (memLp_fun_add (mc00.const_smul (2 : ℝ)) (mc10.const_smul (2 : ℝ)))
      (memLp_fun_add (mc01.const_smul (2 : ℝ)) (mc11.const_smul (2 : ℝ)))
    have t5 := tri_real (memLp_fun_add mr0 mr1)
      (memLp_fun_add (memLp_fun_add (mc00.const_smul (2 : ℝ)) (mc10.const_smul (2 : ℝ)))
        (memLp_fun_add (mc01.const_smul (2 : ℝ)) (mc11.const_smul (2 : ℝ))))
    change _ ≤ (F8U.cellL2 c (fun y => (2 : ℝ) • _)).toReal +
      (F8U.cellL2 c (fun y => (2 : ℝ) • _)).toReal at t2
    change _ ≤ (F8U.cellL2 c (fun y => (2 : ℝ) • _)).toReal +
      (F8U.cellL2 c (fun y => (2 : ℝ) • _)).toReal at t3
    rw [smul2_real, smul2_real] at t2
    rw [smul2_real, smul2_real] at t3
    have d00 := mul_le_mul_of_nonneg_left (hd2_le_plap 0 0) hC.le
    have d10 := mul_le_mul_of_nonneg_left (hd2_le_plap 1 0) hC.le
    have d01 := mul_le_mul_of_nonneg_left (hd2_le_plap 0 1) hC.le
    have d11 := mul_le_mul_of_nonneg_left (hd2_le_plap 1 1) hC.le
    change (F8U.cellL2 c (trLapRemSlice V W)).toReal ≤ _ at t5
    linarith
  exact ⟨hc_bv, hp_bv, hm_bv, hd_bv_mem, hm_d2_bv, hm_plap_bv, hd_tr_eq, hl_tr_eq,
    hm_trLapRem, b_rem⟩

/-- Core convective pairing bounds at Levels 0, 1, 2 for a single smooth periodic slice `W`. -/
lemma bvSlice_pairing_bounds {c C_tr : ℝ} (hc : 0 < c) (hC : 0 < C_tr)
    {V : B0579.Plane → UnforcedLeray.Train.Vec}
    (hV : ContDiff ℝ ∞ V) (hVp : UnforcedLeray.Cyl.IsPeriodic c V)
    (hVdiv : ∀ y, UnforcedLeray.Cyl.divergence V y = 0)
    (hb : ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j V z‖ ≤ C_tr)
    {W : B0579.Plane → CMerid} (hW : ContDiff ℝ ∞ W) (hWp : UnforcedLeray.Cyl.IsPeriodic c W)
    (hm0 : MemLp W 2 (cellMeas c))
    (hm1 : ∀ i : Fin 2, MemLp (pdir i W) 2 (cellMeas c))
    (hm2 : ∀ i j : Fin 2, MemLp (pdir i (pdir j W)) 2 (cellMeas c))
    (hm3 : ∀ i j k : Fin 2, MemLp (pdir i (pdir j (pdir k W))) 2 (cellMeas c))
    (hm4 : ∀ i j k l : Fin 2, MemLp (pdir i (pdir j (pdir k (pdir l W)))) 2 (cellMeas c)) :
    let e0 := (F8U.cellL2 c W).toReal ^ 2
    let e1 := (F8U.cellL2 c (pdir 0 W)).toReal ^ 2 + (F8U.cellL2 c (pdir 1 W)).toReal ^ 2
    let e2 := (F8U.cellL2 c (plap W)).toReal ^ 2
    MemLp (bvSlice V W) 2 (cellMeas c) ∧
    (∀ i : Fin 2, MemLp (pdir i (bvSlice V W)) 2 (cellMeas c)) ∧
    MemLp (plap (bvSlice V W)) 2 (cellMeas c) ∧
    |(∫ y in B0579.cell c, (inner ℂ (W y) (bvSlice V W y) : ℂ)).re| ≤ 4 * C_tr * e0 ∧
    |(∫ y in B0579.cell c, (inner ℂ (-plap W y) (bvSlice V W y) : ℂ)).re| ≤
      12 * C_tr * (e0 + e1) ∧
    |(∫ y in B0579.cell c, (inner ℂ (plap (plap W) y) (bvSlice V W y) : ℂ)).re| ≤
      24 * C_tr * (e0 + e1 + e2) := by
  intro e0 e1 e2
  obtain ⟨b0, b1, _, _⟩ := train_coord_bounds hV hb
  obtain ⟨hc_S, _, hm_S, bd_S, hd_S, hl_S⟩ :=
    stretchSlice_props hC hV hVp hb hW hWp hm0 hm1 hm2
  obtain ⟨hc_bv, hp_bv, hm_bv, hd_bv_mem, hm_d2_bv, hm_plap_bv, hd_tr_eq, hl_tr_eq,
      hm_trLapRem, b_rem⟩ :=
    bvSlice_reg_props hc hC hV hVp hb hW hWp hm0 hm1 hm2 hm3
  have hc_v : ∀ m : Fin 2, ContDiff ℝ ∞ (fun z => V z m) :=
    fun m => (EuclideanSpace.proj m : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp hV
  have hmaxC : max C_tr 0 = C_tr := max_eq_left hC.le
  have hc_tr : ContDiff ℝ ∞ (trTermSlice V W) :=
    (contDiff_mulReal (hc_v 0) (contDiff_pdir hW 0)).add
      (contDiff_mulReal (hc_v 1) (contDiff_pdir hW 1))
  have hm_tr : MemLp (trTermSlice V W) 2 (cellMeas c) :=
    memLp_fun_add (memLp_mulReal_of_bdd (hc_v 0).continuous (b0 0) (hm1 0)).1
      (memLp_mulReal_of_bdd (hc_v 1).continuous (b0 1) (hm1 1)).1
  refine ⟨hm_bv, hd_bv_mem, hm_plap_bv, ?_, ?_, ?_⟩
  · -- Level 0: |Re ⟨W, bvSlice V W⟩| ≤ 4 C_tr e0
    have hsplit : (∫ y in B0579.cell c, (inner ℂ (W y) (bvSlice V W y) : ℂ)).re =
        (∫ y in B0579.cell c, (inner ℂ (W y) (trTermSlice V W y) : ℂ)).re +
          (∫ y in B0579.cell c, (inner ℂ (W y) (stretchSlice V W y) : ℂ)).re := by
      have heq : (fun y => (inner ℂ (W y) (bvSlice V W y) : ℂ)) =
          fun y => (inner ℂ (W y) (trTermSlice V W y) : ℂ) +
            (inner ℂ (W y) (stretchSlice V W y) : ℂ) :=
        funext fun y => inner_add_right _ _ _
      rw [heq, integral_add (integrableOn_inner_cell hm0 hm_tr) (integrableOn_inner_cell hm0 hm_S),
        Complex.add_re]
    have htr0 := transport_re_inner_zero hc hC.le hV hVp hVdiv b0 b1 hW hWp hm0 hm1
    change (∫ y in B0579.cell c, (inner ℂ (W y) (trTermSlice V W y) : ℂ)).re = 0 at htr0
    rw [hsplit, htr0, zero_add]
    calc |(∫ y in B0579.cell c, (inner ℂ (W y) (stretchSlice V W y) : ℂ)).re|
        ≤ (F8U.cellL2 c W).toReal * (F8U.cellL2 c (stretchSlice V W)).toReal :=
          abs_re_integral_inner_le hm0 hm_S
      _ ≤ (F8U.cellL2 c W).toReal * (4 * C_tr * (F8U.cellL2 c W).toReal) :=
          mul_le_mul_of_nonneg_left bd_S ENNReal.toReal_nonneg
      _ = 4 * C_tr * e0 := by dsimp [e0]; ring
  · -- Level 1: |Re ⟨-plap W, bvSlice V W⟩| ≤ 12 C_tr (e0 + e1)
    have hibp : (∫ y in B0579.cell c, (inner ℂ (-plap W y) (bvSlice V W y) : ℂ)) =
        (∫ y in B0579.cell c, (inner ℂ (pdir 0 W y) (pdir 0 (bvSlice V W) y) : ℂ)) +
          (∫ y in B0579.cell c, (inner ℂ (pdir 1 W y) (pdir 1 (bvSlice V W) y) : ℂ)) := by
      have heq : (fun y => (inner ℂ (-plap W y) (bvSlice V W y) : ℂ)) =
          fun y => -((inner ℂ (pdir 0 (pdir 0 W) y) (bvSlice V W y) : ℂ) +
            (inner ℂ (pdir 1 (pdir 1 W) y) (bvSlice V W y) : ℂ)) := by
        funext y; unfold plap; rw [inner_neg_left, inner_add_left]
      rw [heq, integral_neg, integral_add (integrableOn_inner_cell (hm2 0 0) hm_bv)
          (integrableOn_inner_cell (hm2 1 1) hm_bv),
        neg_add,
        cell_ibp_pdir hc 0 (contDiff_pdir hW 0) hc_bv (periodic_pdir hWp 0) hp_bv
          (hm1 0) (hm2 0 0) hm_bv (hd_bv_mem 0),
        cell_ibp_pdir hc 1 (contDiff_pdir hW 1) hc_bv (periodic_pdir hWp 1) hp_bv
          (hm1 1) (hm2 1 1) hm_bv (hd_bv_mem 1),
        neg_neg, neg_neg]
    have hdir_bd : ∀ i : Fin 2,
        |(∫ y in B0579.cell c, (inner ℂ (pdir i W y) (pdir i (bvSlice V W) y) : ℂ)).re| ≤
          (F8U.cellL2 c (pdir i W)).toReal *
            (C_tr * ((F8U.cellL2 c (pdir 0 W)).toReal + (F8U.cellL2 c (pdir 1 W)).toReal) +
              4 * C_tr * ((F8U.cellL2 c W).toReal + (F8U.cellL2 c (pdir i W)).toReal)) := by
      intro i
      let trLead := fun y => mulReal (fun z => V z 0) (pdir 0 (pdir i W)) y +
        mulReal (fun z => V z 1) (pdir 1 (pdir i W)) y
      let trLow := fun y => mulReal (sdirR i (fun z => V z 0)) (pdir 0 W) y +
        mulReal (sdirR i (fun z => V z 1)) (pdir 1 W) y
      have hm_lead : MemLp trLead 2 (cellMeas c) :=
        memLp_fun_add (memLp_mulReal_of_bdd (hc_v 0).continuous (b0 0) (hm2 0 i)).1
          (memLp_mulReal_of_bdd (hc_v 1).continuous (b0 1) (hm2 1 i)).1
      obtain ⟨m_l0, b_l0⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 0) i).continuous
        (b1 i 0) (hm1 0)
      obtain ⟨m_l1, b_l1⟩ := memLp_mulReal_of_bdd (contDiff_sdirR (hc_v 1) i).continuous
        (b1 i 1) (hm1 1)
      rw [hmaxC] at b_l0 b_l1
      have hm_low : MemLp trLow 2 (cellMeas c) := memLp_fun_add m_l0 m_l1
      have htr_zero := transport_re_inner_zero hc hC.le hV hVp hVdiv b0 b1
        (contDiff_pdir hW i) (periodic_pdir hWp i) (hm1 i) (fun m => hm2 m i)
      have hp_bv_i : pdir i (bvSlice V W) =
          fun y => trLead y + (trLow y + pdir i (stretchSlice V W) y) := by
        funext y
        change pdir i (fun z => trTermSlice V W z + stretchSlice V W z) y = _
        rw [pdir_add hc_tr hc_S i, hd_tr_eq i]
        dsimp [trLead, trLow]
        abel
      have hsplit : (∫ y in B0579.cell c,
          (inner ℂ (pdir i W y) (pdir i (bvSlice V W) y) : ℂ)).re =
          (∫ y in B0579.cell c, (inner ℂ (pdir i W y) (trLead y) : ℂ)).re +
          ((∫ y in B0579.cell c, (inner ℂ (pdir i W y) (trLow y) : ℂ)).re +
            (∫ y in B0579.cell c, (inner ℂ (pdir i W y) (pdir i (stretchSlice V W) y) : ℂ)).re) := by
        rw [hp_bv_i]
        have he1 : (fun y => (inner ℂ (pdir i W y)
            (trLead y + (trLow y + pdir i (stretchSlice V W) y)) : ℂ)) =
            fun y => (inner ℂ (pdir i W y) (trLead y) : ℂ) +
              ((inner ℂ (pdir i W y) (trLow y) : ℂ) +
                (inner ℂ (pdir i W y) (pdir i (stretchSlice V W) y) : ℂ)) :=
          funext fun y => (inner_add_right _ _ _).trans (congrArg _ (inner_add_right _ _ _))
        have hi_lead := integrableOn_inner_cell (hm1 i) hm_lead
        have hi_low := integrableOn_inner_cell (hm1 i) hm_low
        have hi_dS := integrableOn_inner_cell (hm1 i) (hd_S i).1
        have hi_rhs : IntegrableOn
            (fun y => (inner ℂ (pdir i W y) (trLow y) : ℂ) +
              (inner ℂ (pdir i W y) (pdir i (stretchSlice V W) y) : ℂ)) (B0579.cell c) :=
          hi_low.add hi_dS
        rw [he1, integral_add hi_lead hi_rhs, integral_add hi_low hi_dS,
          Complex.add_re, Complex.add_re]
      change (∫ y in B0579.cell c, (inner ℂ (pdir i W y) (trLead y) : ℂ)).re = 0 at htr_zero
      rw [hsplit, htr_zero, zero_add]
      have hlow_bd : (F8U.cellL2 c trLow).toReal ≤
          C_tr * ((F8U.cellL2 c (pdir 0 W)).toReal + (F8U.cellL2 c (pdir 1 W)).toReal) := by
        have hle := eLpNorm_add_le m_l0.aestronglyMeasurable m_l1.aestronglyMeasurable one_le_two
        have htr := (ENNReal.toReal_le_toReal hm_low.eLpNorm_ne_top
          (ENNReal.add_ne_top.mpr ⟨m_l0.eLpNorm_ne_top, m_l1.eLpNorm_ne_top⟩)).mpr hle
        rw [ENNReal.toReal_add m_l0.eLpNorm_ne_top m_l1.eLpNorm_ne_top] at htr
        change (F8U.cellL2 c trLow).toReal ≤
          (F8U.cellL2 c (mulReal (sdirR i (fun z => V z 0)) (pdir 0 W))).toReal +
            (F8U.cellL2 c (mulReal (sdirR i (fun z => V z 1)) (pdir 1 W))).toReal at htr
        linarith
      calc |(∫ y in B0579.cell c, (inner ℂ (pdir i W y) (trLow y) : ℂ)).re +
              (∫ y in B0579.cell c, (inner ℂ (pdir i W y) (pdir i (stretchSlice V W) y) : ℂ)).re|
          ≤ |(∫ y in B0579.cell c, (inner ℂ (pdir i W y) (trLow y) : ℂ)).re| +
              |(∫ y in B0579.cell c, (inner ℂ (pdir i W y) (pdir i (stretchSlice V W) y) : ℂ)).re| :=
            abs_add_le _ _
        _ ≤ (F8U.cellL2 c (pdir i W)).toReal * (F8U.cellL2 c trLow).toReal +
              (F8U.cellL2 c (pdir i W)).toReal *
                (F8U.cellL2 c (pdir i (stretchSlice V W))).toReal :=
            add_le_add (abs_re_integral_inner_le (hm1 i) hm_low)
              (abs_re_integral_inner_le (hm1 i) (hd_S i).1)
        _ ≤ (F8U.cellL2 c (pdir i W)).toReal *
              (C_tr * ((F8U.cellL2 c (pdir 0 W)).toReal + (F8U.cellL2 c (pdir 1 W)).toReal)) +
              (F8U.cellL2 c (pdir i W)).toReal *
                (4 * C_tr * ((F8U.cellL2 c W).toReal + (F8U.cellL2 c (pdir i W)).toReal)) :=
            add_le_add (mul_le_mul_of_nonneg_left hlow_bd ENNReal.toReal_nonneg)
              (mul_le_mul_of_nonneg_left (hd_S i).2 ENNReal.toReal_nonneg)
        _ = _ := by ring
    rw [hibp, Complex.add_re]
    set n0 := (F8U.cellL2 c W).toReal
    set d0 := (F8U.cellL2 c (pdir 0 W)).toReal
    set d1 := (F8U.cellL2 c (pdir 1 W)).toReal
    have hb_0 := hdir_bd 0
    have hb_1 := hdir_bd 1
    have hsum_le : d0 * (C_tr * (d0 + d1) + 4 * C_tr * (n0 + d0)) +
        d1 * (C_tr * (d0 + d1) + 4 * C_tr * (n0 + d1)) ≤ 12 * C_tr * (e0 + e1) := by
      have hdiff : 12 * C_tr * (e0 + e1) -
          (d0 * (C_tr * (d0 + d1) + 4 * C_tr * (n0 + d0)) +
            d1 * (C_tr * (d0 + d1) + 4 * C_tr * (n0 + d1))) =
          C_tr * (8 * n0 ^ 2 + 2 * (n0 - d0) ^ 2 + 2 * (n0 - d1) ^ 2 +
            (d0 - d1) ^ 2 + 4 * d0 ^ 2 + 4 * d1 ^ 2) := by
        dsimp [e0, e1]; ring
      have hnn : 0 ≤ C_tr * (8 * n0 ^ 2 + 2 * (n0 - d0) ^ 2 + 2 * (n0 - d1) ^ 2 +
          (d0 - d1) ^ 2 + 4 * d0 ^ 2 + 4 * d1 ^ 2) := by positivity
      linarith
    exact (abs_add_le _ _).trans ((add_le_add hb_0 hb_1).trans hsum_le)
  · -- Level 2: |Re ⟨plap (plap W), bvSlice V W⟩| ≤ 24 C_tr (e0 + e1 + e2)
    have hm_lapW : MemLp (plap W) 2 (cellMeas c) := memLp_fun_add (hm2 0 0) (hm2 1 1)
    have hm_pdir_lapW : ∀ m : Fin 2, MemLp (pdir m (plap W)) 2 (cellMeas c) :=
      fun m => memLp_pdir_add (contDiff_pdir (contDiff_pdir hW 0) 0)
        (contDiff_pdir (contDiff_pdir hW 1) 1) m (hm3 m 0 0) (hm3 m 1 1)
    have hm_d2_lapW : ∀ i : Fin 2, MemLp (pdir i (pdir i (plap W))) 2 (cellMeas c) :=
      fun i => memLp_pdir2_add (contDiff_pdir (contDiff_pdir hW 0) 0)
        (contDiff_pdir (contDiff_pdir hW 1) 1) i (hm4 i i 0 0) (hm4 i i 1 1)
    have hp_lapW : UnforcedLeray.Cyl.IsPeriodic c (plap W) := fun z => by
      unfold plap
      rw [periodic_pdir (periodic_pdir hWp 0) 0 z, periodic_pdir (periodic_pdir hWp 1) 1 z]
    have hibp2 : (∫ y in B0579.cell c, (inner ℂ (plap (plap W) y) (bvSlice V W y) : ℂ)) =
        ∫ y in B0579.cell c, (inner ℂ (plap W y) (plap (bvSlice V W) y) : ℂ) := by
      have hstep : ∀ i : Fin 2,
          (∫ y in B0579.cell c, (inner ℂ (pdir i (pdir i (plap W)) y) (bvSlice V W y) : ℂ)) =
            ∫ y in B0579.cell c, (inner ℂ (plap W y) (pdir i (pdir i (bvSlice V W)) y) : ℂ) := by
        intro i
        have s1 := cell_ibp_pdir hc i (contDiff_pdir (contDiff_plap hW) i) hc_bv
          (periodic_pdir hp_lapW i) hp_bv
          (hm_pdir_lapW i) (hm_d2_lapW i) hm_bv (hd_bv_mem i)
        have s2 := cell_ibp_pdir hc i (contDiff_plap hW) (contDiff_pdir hc_bv i)
          hp_lapW (periodic_pdir hp_bv i)
          hm_lapW (hm_pdir_lapW i) (hd_bv_mem i) (hm_d2_bv i)
        rw [s1, s2, neg_neg]
      have hlhs : (fun y => (inner ℂ (plap (plap W) y) (bvSlice V W y) : ℂ)) =
          fun y => (inner ℂ (pdir 0 (pdir 0 (plap W)) y) (bvSlice V W y) : ℂ) +
            (inner ℂ (pdir 1 (pdir 1 (plap W)) y) (bvSlice V W y) : ℂ) :=
        funext fun y => inner_add_left _ _ _
      have hrhs : (fun y => (inner ℂ (plap W y) (plap (bvSlice V W) y) : ℂ)) =
          fun y => (inner ℂ (plap W y) (pdir 0 (pdir 0 (bvSlice V W)) y) : ℂ) +
            (inner ℂ (plap W y) (pdir 1 (pdir 1 (bvSlice V W)) y) : ℂ) :=
        funext fun y => inner_add_right _ _ _
      rw [hlhs, integral_add (integrableOn_inner_cell (hm_d2_lapW 0) hm_bv)
          (integrableOn_inner_cell (hm_d2_lapW 1) hm_bv),
        hstep 0, hstep 1,
        hrhs, integral_add (integrableOn_inner_cell hm_lapW (hm_d2_bv 0))
          (integrableOn_inner_cell hm_lapW (hm_d2_bv 1))]
    rw [hibp2]
    have htr_zero2 := transport_re_inner_zero hc hC.le hV hVp hVdiv b0 b1
      (contDiff_plap hW) hp_lapW hm_lapW hm_pdir_lapW
    let trLapLead : B0579.Plane → CMerid := fun y =>
      mulReal (fun z => V z 0) (pdir 0 (plap W)) y +
        mulReal (fun z => V z 1) (pdir 1 (plap W)) y
    have hm_trLap_lead : MemLp trLapLead 2 (cellMeas c) :=
      memLp_fun_add (memLp_mulReal_of_bdd (hc_v 0).continuous (b0 0) (hm_pdir_lapW 0)).1
        (memLp_mulReal_of_bdd (hc_v 1).continuous (b0 1) (hm_pdir_lapW 1)).1
    have hplap_bv_eq : plap (bvSlice V W) = fun y =>
        trLapLead y + (trLapRemSlice V W y + plap (stretchSlice V W) y) := by
      funext y
      change plap (fun z => trTermSlice V W z + stretchSlice V W z) y = _
      rw [plap_add hc_tr hc_S, hl_tr_eq]
      dsimp [trLapLead]
      abel
    have hsplit2 : (∫ y in B0579.cell c, (inner ℂ (plap W y) (plap (bvSlice V W) y) : ℂ)).re =
        (∫ y in B0579.cell c, (inner ℂ (plap W y) (trLapLead y) : ℂ)).re +
        ((∫ y in B0579.cell c, (inner ℂ (plap W y) (trLapRemSlice V W y) : ℂ)).re +
          (∫ y in B0579.cell c, (inner ℂ (plap W y) (plap (stretchSlice V W) y) : ℂ)).re) := by
      rw [hplap_bv_eq]
      have he : (fun y => (inner ℂ (plap W y)
          (trLapLead y + (trLapRemSlice V W y + plap (stretchSlice V W) y)) : ℂ)) =
          fun y => (inner ℂ (plap W y) (trLapLead y) : ℂ) +
            ((inner ℂ (plap W y) (trLapRemSlice V W y) : ℂ) +
              (inner ℂ (plap W y) (plap (stretchSlice V W) y) : ℂ)) :=
        funext fun y => (inner_add_right _ _ _).trans (congrArg _ (inner_add_right _ _ _))
      have hi_lead2 := integrableOn_inner_cell hm_lapW hm_trLap_lead
      have hi_rem2 := integrableOn_inner_cell hm_lapW hm_trLapRem
      have hi_lS2 := integrableOn_inner_cell hm_lapW hl_S.1
      have hi_rhs2 : IntegrableOn
          (fun y => (inner ℂ (plap W y) (trLapRemSlice V W y) : ℂ) +
            (inner ℂ (plap W y) (plap (stretchSlice V W) y) : ℂ)) (B0579.cell c) :=
        hi_rem2.add hi_lS2
      rw [he, integral_add hi_lead2 hi_rhs2, integral_add hi_rem2 hi_lS2,
        Complex.add_re, Complex.add_re]
    change (∫ y in B0579.cell c, (inner ℂ (plap W y) (trLapLead y) : ℂ)).re = 0 at htr_zero2
    rw [hsplit2, htr_zero2, zero_add]
    set n0 := (F8U.cellL2 c W).toReal
    set d0 := (F8U.cellL2 c (pdir 0 W)).toReal
    set d1 := (F8U.cellL2 c (pdir 1 W)).toReal
    set l2 := (F8U.cellL2 c (plap W)).toReal
    have hcs1 := abs_re_integral_inner_le hm_lapW hm_trLapRem
    have hcs2 := abs_re_integral_inner_le hm_lapW hl_S.1
    have hprod1 : l2 * (F8U.cellL2 c (trLapRemSlice V W)).toReal ≤
        l2 * (2 * C_tr * (d0 + d1) + 8 * C_tr * l2) :=
      mul_le_mul_of_nonneg_left b_rem ENNReal.toReal_nonneg
    have hprod2 : l2 * (F8U.cellL2 c (plap (stretchSlice V W))).toReal ≤
        l2 * (8 * C_tr * (n0 + (d0 + d1) + l2)) :=
      mul_le_mul_of_nonneg_left hl_S.2 ENNReal.toReal_nonneg
    have halg : l2 * (2 * C_tr * (d0 + d1) + 8 * C_tr * l2) +
        l2 * (8 * C_tr * (n0 + (d0 + d1) + l2)) ≤ 24 * C_tr * (e0 + e1 + e2) := by
      have hid : 24 * C_tr * (e0 + e1 + e2) -
          (l2 * (2 * C_tr * (d0 + d1) + 8 * C_tr * l2) +
            l2 * (8 * C_tr * (n0 + (d0 + d1) + l2))) =
          C_tr * (8 * n0 ^ 2 + (4 * n0 - l2) ^ 2 +
            (23 / 2 : ℝ) * d0 ^ 2 + (1 / 2 : ℝ) * (5 * d0 - 2 * l2) ^ 2 +
            (23 / 2 : ℝ) * d1 ^ 2 + (1 / 2 : ℝ) * (5 * d1 - 2 * l2) ^ 2 +
            3 * l2 ^ 2) := by
        dsimp [e0, e1, e2]; ring
      have hnn : 0 ≤ C_tr * (8 * n0 ^ 2 + (4 * n0 - l2) ^ 2 +
          (23 / 2 : ℝ) * d0 ^ 2 + (1 / 2 : ℝ) * (5 * d0 - 2 * l2) ^ 2 +
          (23 / 2 : ℝ) * d1 ^ 2 + (1 / 2 : ℝ) * (5 * d1 - 2 * l2) ^ 2 +
          3 * l2 ^ 2) := by positivity
      linarith
    exact (abs_add_le _ _).trans ((add_le_add (hcs1.trans hprod1) (hcs2.trans hprod2)).trans halg)

/-! ## 8. Orbit energy differential inequalities and initial-data limit -/

lemma periodic_plap {c : ℝ} {G : B0579.Plane → CMerid}
    (hper : UnforcedLeray.Cyl.IsPeriodic c G) :
    UnforcedLeray.Cyl.IsPeriodic c (plap G) := by
  intro y
  unfold plap
  rw [periodic_pdir (periodic_pdir hper 0) 0 y, periodic_pdir (periodic_pdir hper 1) 1 y]

lemma energySlice_eq_cellL2_sq {c τ : ℝ} {g : CProf}
    (hg : MemLp (F8U.slice g τ) 2 (cellMeas c)) :
    energySlice c g τ = (F8U.cellL2 c (F8U.slice g τ)).toReal ^ 2 :=
  integral_norm_sq_eq_cellL2_sq hg

lemma cellL2_ne_top {c : ℝ} {f : B0579.Plane → CMerid} (hf : MemLp f 2 (cellMeas c)) :
    F8U.cellL2 c f ≠ ⊤ :=
  hf.eLpNorm_ne_top

lemma re_inner_self_eq_cellL2_sq {c : ℝ} {f : B0579.Plane → CMerid}
    (hf : MemLp f 2 (cellMeas c)) :
    (∫ y in B0579.cell c, (inner ℂ (f y) (f y) : ℂ)).re = (F8U.cellL2 c f).toReal ^ 2 := by
  rw [integral_inner_eq_L2_inner hf hf, inner_self_eq_norm_sq_to_K, norm_toLp_eq_cellL2 hf]
  change (((F8U.cellL2 c f).toReal : ℂ) ^ 2).re = (F8U.cellL2 c f).toReal ^ 2
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma cell_ibp_neg_plap_left {c : ℝ} (hc : 0 < c) {F G : B0579.Plane → CMerid}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFp : UnforcedLeray.Cyl.IsPeriodic c F) (hGp : UnforcedLeray.Cyl.IsPeriodic c G)
    (hmdF : ∀ i : Fin 2, MemLp (pdir i F) 2 (cellMeas c))
    (hmddF : ∀ i j : Fin 2, MemLp (pdir i (pdir j F)) 2 (cellMeas c))
    (hmG : MemLp G 2 (cellMeas c))
    (hmdG : ∀ i : Fin 2, MemLp (pdir i G) 2 (cellMeas c)) :
    (∫ y in B0579.cell c, (inner ℂ (-plap F y) (G y) : ℂ)) =
      (∫ y in B0579.cell c, (inner ℂ (pdir 0 F y) (pdir 0 G y) : ℂ)) +
        (∫ y in B0579.cell c, (inner ℂ (pdir 1 F y) (pdir 1 G y) : ℂ)) := by
  have heq : (fun y => (inner ℂ (-plap F y) (G y) : ℂ)) =
      fun y => -((inner ℂ (pdir 0 (pdir 0 F) y) (G y) : ℂ) +
        (inner ℂ (pdir 1 (pdir 1 F) y) (G y) : ℂ)) := by
    funext y; unfold plap; rw [inner_neg_left, inner_add_left]
  rw [heq, integral_neg, integral_add (integrableOn_inner_cell (hmddF 0 0) hmG)
      (integrableOn_inner_cell (hmddF 1 1) hmG),
    neg_add,
    cell_ibp_pdir hc 0 (contDiff_pdir hF 0) hG (periodic_pdir hFp 0) hGp
      (hmdF 0) (hmddF 0 0) hmG (hmdG 0),
    cell_ibp_pdir hc 1 (contDiff_pdir hF 1) hG (periodic_pdir hFp 1) hGp
      (hmdF 1) (hmddF 1 1) hmG (hmdG 1),
    neg_neg, neg_neg]

lemma cell_ibp_neg_plap_right {c : ℝ} (hc : 0 < c) {F G : B0579.Plane → CMerid}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFp : UnforcedLeray.Cyl.IsPeriodic c F) (hGp : UnforcedLeray.Cyl.IsPeriodic c G)
    (hmF : MemLp F 2 (cellMeas c))
    (hmdF : ∀ i : Fin 2, MemLp (pdir i F) 2 (cellMeas c))
    (hmdG : ∀ i : Fin 2, MemLp (pdir i G) 2 (cellMeas c))
    (hmddG : ∀ i j : Fin 2, MemLp (pdir i (pdir j G)) 2 (cellMeas c)) :
    - (∫ y in B0579.cell c, (inner ℂ (F y) (plap G y) : ℂ)) =
      (∫ y in B0579.cell c, (inner ℂ (pdir 0 F y) (pdir 0 G y) : ℂ)) +
        (∫ y in B0579.cell c, (inner ℂ (pdir 1 F y) (pdir 1 G y) : ℂ)) := by
  have heq : (fun y => (inner ℂ (F y) (plap G y) : ℂ)) =
      fun y => (inner ℂ (F y) (pdir 0 (pdir 0 G) y) : ℂ) +
        (inner ℂ (F y) (pdir 1 (pdir 1 G) y) : ℂ) := by
    funext y; unfold plap; rw [inner_add_right]
  have hibp0 := cell_ibp_pdir hc 0 hF (contDiff_pdir hG 0) hFp (periodic_pdir hGp 0)
    hmF (hmdF 0) (hmdG 0) (hmddG 0 0)
  have hibp1 := cell_ibp_pdir hc 1 hF (contDiff_pdir hG 1) hFp (periodic_pdir hGp 1)
    hmF (hmdF 1) (hmdG 1) (hmddG 1 1)
  rw [heq, integral_add (integrableOn_inner_cell hmF (hmddG 0 0))
    (integrableOn_inner_cell hmF (hmddG 1 1)), neg_add, ← hibp0, ← hibp1]

lemma orbit_hierarchy_step {p : Params} {σ C_tr : ℝ} (hσ : 0 ≤ σ) (hν1 : p.ν ≤ 1)
    (hC : 0 < C_tr)
    (htr : ∀ s : ℝ, 0 ≤ s → ∀ j : ℕ, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (p.train.v s) z‖ ≤ C_tr)
    {u uq uη : B0579.Plane → CMerid} {w : CProf}
    (hw : F8U.IsCylOseenOrbit p σ w u uq uη) :
    let E0 := energySlice p.c w
    let E1 := fun τ => energySlice p.c (F8U.pd 0 w) τ + energySlice p.c (F8U.pd 1 w) τ
    let E2 := energySlice p.c (lapProf w)
    let E3 := fun τ => energySlice p.c (F8U.pd 0 (lapProf w)) τ +
      energySlice p.c (F8U.pd 1 (lapProf w)) τ
    let P1 := fun τ => E0 τ + E1 τ
    let P2 := fun τ => E0 τ + E1 τ + E2 τ
    let P3 := fun τ => E1 τ + E2 τ + E3 τ
    let K := 48 * C_tr + 2
    ∃ (P1' P2' : ℝ → ℝ),
      (∀ τ ∈ Ioo σ (σ + 2), ContinuousAt P1 τ ∧ ContinuousAt P2 τ ∧
        0 ≤ P1 τ ∧ P1 τ ≤ P2 τ ∧ 0 ≤ P3 τ ∧
        HasDerivWithinAt P1 (P1' τ) (Ici τ) τ ∧
        HasDerivWithinAt P2 (P2' τ) (Ici τ) τ ∧
        P1' τ + p.ν * P2 τ ≤ K * P1 τ ∧
        P2' τ + p.ν * P3 τ ≤ K * (P1 τ + P2 τ)) := by
  intro E0 E1 E2 E3 P1 P2 P3 K
  have hc0 : 0 < p.c := p.c_pos
  have hν0 : 0 < p.ν := p.ν_pos
  let dE0 : ℝ → ℝ := fun τ =>
    2 * (∫ y in B0579.cell p.c, (inner ℂ (w (τ, y)) (F8U.ps w (τ, y)) : ℂ)).re
  let dE1 : ℝ → ℝ := fun τ =>
    2 * (∫ y in B0579.cell p.c, (inner ℂ (F8U.pd 0 w (τ, y)) (F8U.ps (F8U.pd 0 w) (τ, y)) : ℂ)).re +
    2 * (∫ y in B0579.cell p.c, (inner ℂ (F8U.pd 1 w (τ, y)) (F8U.ps (F8U.pd 1 w) (τ, y)) : ℂ)).re
  let dE2 : ℝ → ℝ := fun τ =>
    2 * (∫ y in B0579.cell p.c, (inner ℂ (lapProf w (τ, y)) (F8U.ps (lapProf w) (τ, y)) : ℂ)).re
  refine ⟨fun τ => dE0 τ + dE1 τ, fun τ => dE0 τ + dE1 τ + dE2 τ, fun τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := hσ.trans hτ.1.le
  -- Slice L² memberships from hw.memL2 and hw.memL2_s
  have hm0 : ∀ s ∈ Ioo σ (σ + 2), MemLp (F8U.slice w s) 2 (cellMeas p.c) :=
    fun s hs => hw.memL2 s hs 0 (by decide) ![]
  have hm1 : ∀ s ∈ Ioo σ (σ + 2), ∀ i : Fin 2, MemLp (F8U.slice (F8U.pd i w) s) 2 (cellMeas p.c) :=
    fun s hs i => hw.memL2 s hs 1 (by decide) ![i]
  have hm2 : ∀ s ∈ Ioo σ (σ + 2), ∀ i j : Fin 2,
      MemLp (F8U.slice (F8U.pd i (F8U.pd j w)) s) 2 (cellMeas p.c) :=
    fun s hs i j => hw.memL2 s hs 2 (by decide) ![i, j]
  have hm3 : ∀ s ∈ Ioo σ (σ + 2), ∀ i j k : Fin 2,
      MemLp (F8U.slice (F8U.pd i (F8U.pd j (F8U.pd k w))) s) 2 (cellMeas p.c) :=
    fun s hs i j k => hw.memL2 s hs 3 (by decide) ![i, j, k]
  have hm4 : ∀ s ∈ Ioo σ (σ + 2), ∀ i j k l : Fin 2,
      MemLp (F8U.slice (F8U.pd i (F8U.pd j (F8U.pd k (F8U.pd l w)))) s) 2 (cellMeas p.c) :=
    fun s hs i j k l => hw.memL2 s hs 4 (by decide) ![i, j, k, l]
  have hm_lap : ∀ s ∈ Ioo σ (σ + 2), MemLp (F8U.slice (lapProf w) s) 2 (cellMeas p.c) :=
    fun s hs => (hm2 s hs 0 0).add (hm2 s hs 1 1)
  have hms0 : MemLp (F8U.slice (F8U.ps w) τ) 2 (cellMeas p.c) :=
    hw.memL2_s τ hτ 0 (by decide) ![]
  have hms1 : ∀ i : Fin 2, MemLp (F8U.slice (F8U.ps (F8U.pd i w)) τ) 2 (cellMeas p.c) :=
    fun i => hw.memL2_s τ hτ 1 (by decide) ![i]
  have hms2 : ∀ i j : Fin 2,
      MemLp (F8U.slice (F8U.ps (F8U.pd i (F8U.pd j w))) τ) 2 (cellMeas p.c) :=
    fun i j => hw.memL2_s τ hτ 2 (by decide) ![i, j]
  have hms_lap : MemLp (F8U.slice (F8U.ps (lapProf w)) τ) 2 (cellMeas p.c) := by
    have heq : F8U.slice (F8U.ps (lapProf w)) τ =
        F8U.slice (F8U.ps (F8U.pd 0 (F8U.pd 0 w))) τ +
          F8U.slice (F8U.ps (F8U.pd 1 (F8U.pd 1 w))) τ := by
      funext y; exact ps_lapProf_eq hw.smooth (mem_stripSet hτ y)
    rw [heq]; exact (hms2 0 0).add (hms2 1 1)
  have hcs_lap : Tendsto (fun t => F8U.cellL2 p.c (fun y =>
      F8U.ps (lapProf w) (t, y) - F8U.ps (lapProf w) (τ, y))) (𝓝 τ) (𝓝 0) := by
    have c00 := hw.cont_s τ hτ 2 (by decide) ![0, 0]
    have c11 := hw.cont_s τ hτ 2 (by decide) ![1, 1]
    change Tendsto (fun t => F8U.cellL2 p.c (fun y => F8U.ps (F8U.pd 0 (F8U.pd 0 w)) (t, y) -
      F8U.ps (F8U.pd 0 (F8U.pd 0 w)) (τ, y))) (𝓝 τ) (𝓝 0) at c00
    change Tendsto (fun t => F8U.cellL2 p.c (fun y => F8U.ps (F8U.pd 1 (F8U.pd 1 w)) (t, y) -
      F8U.ps (F8U.pd 1 (F8U.pd 1 w)) (τ, y))) (𝓝 τ) (𝓝 0) at c11
    have hsum := c00.add c11
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
    have hmd (i : Fin 2) : MemLp (fun y => F8U.ps (F8U.pd i (F8U.pd i w)) (t, y) -
        F8U.ps (F8U.pd i (F8U.pd i w)) (τ, y)) 2 (cellMeas p.c) :=
      (hw.memL2_s t ht 2 (by decide) ![i, i]).sub (hms2 i i)
    have hdecomp : (fun y => F8U.ps (lapProf w) (t, y) - F8U.ps (lapProf w) (τ, y)) =
        (fun y => F8U.ps (F8U.pd 0 (F8U.pd 0 w)) (t, y) -
          F8U.ps (F8U.pd 0 (F8U.pd 0 w)) (τ, y)) +
        (fun y => F8U.ps (F8U.pd 1 (F8U.pd 1 w)) (t, y) -
          F8U.ps (F8U.pd 1 (F8U.pd 1 w)) (τ, y)) := by
      funext y
      simp only [Pi.add_apply]
      rw [ps_lapProf_eq hw.smooth (mem_stripSet ht y),
        ps_lapProf_eq hw.smooth (mem_stripSet hτ y)]
      abel
    rw [hdecomp]
    exact eLpNorm_add_le (hmd 0).aestronglyMeasurable (hmd 1).aestronglyMeasurable one_le_two
  -- Age differentiability of E0, E1, E2, P1, P2
  have hdE0 : HasDerivAt E0 (dE0 τ) τ :=
    hasDerivAt_energySlice hw.smooth hm0 hms0 (hw.cont_s τ hτ 0 (by decide) ![]) hτ
  have hdE1_0 : HasDerivAt (energySlice p.c (F8U.pd 0 w))
      (2 * (∫ y in B0579.cell p.c, (inner ℂ (F8U.pd 0 w (τ, y)) (F8U.ps (F8U.pd 0 w) (τ, y)) : ℂ)).re) τ :=
    hasDerivAt_energySlice (contDiffOn_pd hw.smooth 0) (fun s hs => hm1 s hs 0)
      (hms1 0) (hw.cont_s τ hτ 1 (by decide) ![0]) hτ
  have hdE1_1 : HasDerivAt (energySlice p.c (F8U.pd 1 w))
      (2 * (∫ y in B0579.cell p.c, (inner ℂ (F8U.pd 1 w (τ, y)) (F8U.ps (F8U.pd 1 w) (τ, y)) : ℂ)).re) τ :=
    hasDerivAt_energySlice (contDiffOn_pd hw.smooth 1) (fun s hs => hm1 s hs 1)
      (hms1 1) (hw.cont_s τ hτ 1 (by decide) ![1]) hτ
  have hdE1 : HasDerivAt E1 (dE1 τ) τ := hdE1_0.add hdE1_1
  have hdE2 : HasDerivAt E2 (dE2 τ) τ :=
    hasDerivAt_energySlice (contDiffOn_lapProf hw.smooth) hm_lap hms_lap hcs_lap hτ
  have hdP1 : HasDerivAt P1 (dE0 τ + dE1 τ) τ := hdE0.add hdE1
  have hdP2 : HasDerivAt P2 (dE0 τ + dE1 τ + dE2 τ) τ := hdP1.add hdE2
  -- Slice objects W = w(τ, ·), Ws = ∂_s w(τ, ·), V = v(τ, ·)
  let W : B0579.Plane → CMerid := F8U.slice w τ
  let Ws : B0579.Plane → CMerid := F8U.slice (F8U.ps w) τ
  let V : B0579.Plane → UnforcedLeray.Train.Vec := p.train.v τ
  have hW : ContDiff ℝ ∞ W := contDiff_slice hw.smooth hτ
  have hWp : UnforcedLeray.Cyl.IsPeriodic p.c W := fun y => hw.periodic (τ, y) hτ
  have hWs : ContDiff ℝ ∞ Ws := contDiff_slice (contDiffOn_ps hw.smooth) hτ
  have hWsp : UnforcedLeray.Cyl.IsPeriodic p.c Ws :=
    fun y => periodic_fderiv_dir hw.periodic (1, (0, 0)) (τ, y) hτ
  have hV : ContDiff ℝ ∞ V :=
    p.train.isTrain.smooth_v.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨hτ0, trivial⟩)
  have hVp : UnforcedLeray.Cyl.IsPeriodic p.c V := p.train.isTrain.periodic_v τ hτ0
  have hVdiv : ∀ y, UnforcedLeray.Cyl.divergence V y = 0 := p.train.isTrain.solenoidal τ hτ0
  -- Relating planar derivatives of W and Ws to space-time slices
  have hp1 : ∀ i, pdir i W = F8U.slice (F8U.pd i w) τ := pdir_slice_eq hw.smooth hτ
  have hp2 : ∀ i j, pdir i (pdir j W) = F8U.slice (F8U.pd i (F8U.pd j w)) τ := fun i j => by
    rw [hp1 j, pdir_slice_eq (contDiffOn_pd hw.smooth j) hτ i]
  have hp3 : ∀ i j k, pdir i (pdir j (pdir k W)) =
      F8U.slice (F8U.pd i (F8U.pd j (F8U.pd k w))) τ := fun i j k => by
    rw [hp2 j k, pdir_slice_eq (contDiffOn_pd (contDiffOn_pd hw.smooth k) j) hτ i]
  have hp4 : ∀ i j k l, pdir i (pdir j (pdir k (pdir l W))) =
      F8U.slice (F8U.pd i (F8U.pd j (F8U.pd k (F8U.pd l w)))) τ := fun i j k l => by
    rw [hp3 j k l, pdir_slice_eq (contDiffOn_pd (contDiffOn_pd (contDiffOn_pd hw.smooth l) k) j) hτ i]
  have hplap : plap W = F8U.slice (lapProf w) τ := plap_slice_eq hw.smooth hτ
  have hp_plap : ∀ i, pdir i (plap W) = F8U.slice (F8U.pd i (lapProf w)) τ := fun i => by
    rw [hplap, pdir_slice_eq (contDiffOn_lapProf hw.smooth) hτ i]
  have hpWs1 : ∀ i, pdir i Ws = F8U.slice (F8U.ps (F8U.pd i w)) τ := fun i => by
    funext y
    rw [pdir_slice_eq (contDiffOn_ps hw.smooth) hτ i]
    exact (ps_pd_comm hw.smooth (mem_stripSet hτ y) i).symm
  have hpWs2 : ∀ i j, pdir i (pdir j Ws) = F8U.slice (F8U.ps (F8U.pd i (F8U.pd j w))) τ :=
    fun i j => by
      funext y
      rw [hpWs1 j, pdir_slice_eq (contDiffOn_ps (contDiffOn_pd hw.smooth j)) hτ i]
      exact (ps_pd_comm (contDiffOn_pd hw.smooth j) (mem_stripSet hτ y) i).symm
  have hplapWs : plap Ws = F8U.slice (F8U.ps (lapProf w)) τ := by
    funext y
    unfold plap
    rw [hpWs2 0 0, hpWs2 1 1]
    exact (ps_lapProf_eq hw.smooth (mem_stripSet hτ y)).symm
  -- L² memberships of W and Ws derivatives
  have hmW0 : MemLp W 2 (cellMeas p.c) := hm0 τ hτ
  have hmW1 : ∀ i, MemLp (pdir i W) 2 (cellMeas p.c) := fun i => by rw [hp1 i]; exact hm1 τ hτ i
  have hmW2 : ∀ i j, MemLp (pdir i (pdir j W)) 2 (cellMeas p.c) := fun i j => by
    rw [hp2 i j]; exact hm2 τ hτ i j
  have hmW3 : ∀ i j k, MemLp (pdir i (pdir j (pdir k W))) 2 (cellMeas p.c) := fun i j k => by
    rw [hp3 i j k]; exact hm3 τ hτ i j k
  have hmW4 : ∀ i j k l, MemLp (pdir i (pdir j (pdir k (pdir l W)))) 2 (cellMeas p.c) :=
    fun i j k l => by rw [hp4 i j k l]; exact hm4 τ hτ i j k l
  have hmW_lap : MemLp (plap W) 2 (cellMeas p.c) := (hmW2 0 0).add (hmW2 1 1)
  have hmW_dlap : ∀ i, MemLp (pdir i (plap W)) 2 (cellMeas p.c) := fun i => by
    unfold plap
    rw [pdir_add (contDiff_pdir (contDiff_pdir hW 0) 0) (contDiff_pdir (contDiff_pdir hW 1) 1) i]
    exact (hmW3 i 0 0).add (hmW3 i 1 1)
  have hmW_ddlap : ∀ i j, MemLp (pdir i (pdir j (plap W))) 2 (cellMeas p.c) := fun i j => by
    unfold plap
    rw [pdir_add (contDiff_pdir (contDiff_pdir hW 0) 0) (contDiff_pdir (contDiff_pdir hW 1) 1) j,
      pdir_add (contDiff_pdir (contDiff_pdir (contDiff_pdir hW 0) 0) j)
        (contDiff_pdir (contDiff_pdir (contDiff_pdir hW 1) 1) j) i]
    exact (hmW4 i j 0 0).add (hmW4 i j 1 1)
  have hmW_lap2 : MemLp (plap (plap W)) 2 (cellMeas p.c) := (hmW_ddlap 0 0).add (hmW_ddlap 1 1)
  have hmWs1 : ∀ i, MemLp (pdir i Ws) 2 (cellMeas p.c) := fun i => by rw [hpWs1 i]; exact hms1 i
  have hmWs2 : ∀ i j, MemLp (pdir i (pdir j Ws)) 2 (cellMeas p.c) := fun i j => by
    rw [hpWs2 i j]; exact hms2 i j
  -- Relating E0, E1, E2, E3 to slice cellL2 norms
  have hE0_eq : E0 τ = (F8U.cellL2 p.c W).toReal ^ 2 := integral_norm_sq_eq_cellL2_sq hmW0
  have hE1_eq : E1 τ = (F8U.cellL2 p.c (pdir 0 W)).toReal ^ 2 +
      (F8U.cellL2 p.c (pdir 1 W)).toReal ^ 2 := by
    dsimp only [E1]
    rw [energySlice_eq_cellL2_sq (hm1 τ hτ 0),
      energySlice_eq_cellL2_sq (hm1 τ hτ 1), ← hp1 0, ← hp1 1]
  have hE2_eq : E2 τ = (F8U.cellL2 p.c (plap W)).toReal ^ 2 := by
    dsimp only [E2]
    rw [energySlice_eq_cellL2_sq (hm_lap τ hτ), ← hplap]
  have hE3_eq : E3 τ = (F8U.cellL2 p.c (pdir 0 (plap W))).toReal ^ 2 +
      (F8U.cellL2 p.c (pdir 1 (plap W))).toReal ^ 2 := by
    have hm_dlap0 : MemLp (F8U.slice (F8U.pd 0 (lapProf w)) τ) 2 (cellMeas p.c) := by
      rw [← hp_plap 0]; exact hmW_dlap 0
    have hm_dlap1 : MemLp (F8U.slice (F8U.pd 1 (lapProf w)) τ) 2 (cellMeas p.c) := by
      rw [← hp_plap 1]; exact hmW_dlap 1
    dsimp only [E3]
    rw [energySlice_eq_cellL2_sq hm_dlap0, energySlice_eq_cellL2_sq hm_dlap1,
      ← hp_plap 0, ← hp_plap 1]
  have hE0_nn : 0 ≤ E0 τ := by rw [hE0_eq]; positivity
  have hE1_nn : 0 ≤ E1 τ := by rw [hE1_eq]; positivity
  have hE2_nn : 0 ≤ E2 τ := by rw [hE2_eq]; positivity
  have hE3_nn : 0 ≤ E3 τ := by rw [hE3_eq]; positivity
  -- Convective bounds from bvSlice_pairing_bounds
  obtain ⟨hm_bv, _, _, hbv0, hbv1, hbv2⟩ :=
    bvSlice_pairing_bounds hc0 hC hV hVp hVdiv (htr τ hτ0) hW hWp hmW0 hmW1 hmW2 hmW3 hmW4
  rw [← hE0_eq] at hbv0 hbv1 hbv2
  rw [← hE1_eq] at hbv1 hbv2
  rw [← hE2_eq] at hbv2
  -- Solenoidality of the three test multipliers W, -plap W, plap (plap W)
  have hW_div : ∀ y, pdir 0 W y 0 + pdir 1 W y 1 = 0 := fun y => by
    rw [hp1 0, hp1 1]; exact hw.div_free (τ, y) hτ
  have hsol0 : F8U.IsCellSolenoidal p.c W := isCellSolenoidal_of_div_free hc0 hW hWp hW_div
  have hsol_lap : F8U.IsCellSolenoidal p.c (plap W) :=
    isCellSolenoidal_of_div_free hc0 (contDiff_plap hW) (periodic_plap hWp)
      (div_free_plap hW hW_div)
  have hsol1 : F8U.IsCellSolenoidal p.c (fun y => -plap W y) := isCellSolenoidal_neg hsol_lap
  have hsol2 : F8U.IsCellSolenoidal p.c (plap (plap W)) :=
    isCellSolenoidal_of_div_free hc0 (contDiff_plap (contDiff_plap hW))
      (periodic_plap (periodic_plap hWp))
      (div_free_plap (contDiff_plap hW) (div_free_plap hW hW_div))
  -- Splitting the real part of hw.projected against any solenoidal multiplier φ
  have hres_eq : (fun y => F8U.homResidual p w (τ, y)) =
      fun y => (Ws y - p.ν • plap W y) + bvSlice V W y := by
    funext y
    have hfl := congrFun (flatBv_slice_eq p.train hw.smooth hτ) y
    have hlp := congrFun hplap y
    dsimp [F8U.homResidual, Ws, W, V, lapProf, F8U.slice] at hfl hlp ⊢
    rw [hlp, hfl]
  have hproj_re : ∀ (φ : B0579.Plane → CMerid),
      MemLp φ 2 (cellMeas p.c) → F8U.IsCellSolenoidal p.c φ →
      (∫ y in B0579.cell p.c, (inner ℂ (φ y) (Ws y) : ℂ)).re +
        p.ν * (-(∫ y in B0579.cell p.c, (inner ℂ (φ y) (plap W y) : ℂ)).re) +
        (∫ y in B0579.cell p.c, (inner ℂ (φ y) (bvSlice V W y) : ℂ)).re = 0 := by
    intro φ hmφ hsolφ
    have h0 := congrArg Complex.re (hw.projected τ hτ φ hmφ hsolφ)
    rw [Complex.zero_re] at h0
    have hsmul : ∀ y, (inner ℂ (φ y) (p.ν • plap W y) : ℂ) =
        (p.ν : ℂ) * (inner ℂ (φ y) (plap W y) : ℂ) := fun y => by
      rw [← Complex.coe_smul, inner_smul_right]
    have hexp : (fun y => (inner ℂ (φ y) (F8U.homResidual p w (τ, y)) : ℂ)) =
        fun y => ((inner ℂ (φ y) (Ws y) : ℂ) - (p.ν : ℂ) * (inner ℂ (φ y) (plap W y) : ℂ)) +
          (inner ℂ (φ y) (bvSlice V W y) : ℂ) := by
      funext y
      rw [congrFun hres_eq y, inner_add_right, inner_sub_right, hsmul y]
    have hms0' : MemLp Ws 2 (cellMeas p.c) := hms0
    have hi_ws := integrableOn_inner_cell hmφ hms0'
    have hi_lap := (integrableOn_inner_cell hmφ hmW_lap).const_mul (p.ν : ℂ)
    have hi_sub : IntegrableOn
        (fun y => (inner ℂ (φ y) (Ws y) : ℂ) - (p.ν : ℂ) * (inner ℂ (φ y) (plap W y) : ℂ))
        (B0579.cell p.c) := hi_ws.sub hi_lap
    have hi_bv := integrableOn_inner_cell hmφ hm_bv
    rw [hexp, integral_add hi_sub hi_bv, integral_sub hi_ws hi_lap,
      integral_const_mul, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h0
    linarith
  -- Level 0 identity (`φ = W`)
  have hlev0 : dE0 τ + 2 * p.ν * E1 τ ≤ 8 * C_tr * E0 τ := by
    have hp := hproj_re W hmW0 hsol0
    have hvisc : -(∫ y in B0579.cell p.c, (inner ℂ (W y) (plap W y) : ℂ)).re = E1 τ := by
      have hibp := congrArg Complex.re
        (cell_ibp_neg_plap_right hc0 hW hW hWp hWp hmW0 hmW1 hmW1 hmW2)
      rw [Complex.neg_re, Complex.add_re, re_inner_self_eq_cellL2_sq (hmW1 0),
        re_inner_self_eq_cellL2_sq (hmW1 1), ← hE1_eq] at hibp
      exact hibp
    rw [hvisc] at hp
    have hd0_def : 2 * (∫ y in B0579.cell p.c, (inner ℂ (W y) (Ws y) : ℂ)).re = dE0 τ := rfl
    have habs := (abs_le.mp hbv0).1
    linarith
  -- Level 1 identity (`φ = -plap W`)
  have hlev1 : dE1 τ + 2 * p.ν * E2 τ ≤ 24 * C_tr * (E0 τ + E1 τ) := by
    have hp := hproj_re (fun y => -plap W y) hmW_lap.neg hsol1
    have htime : 2 * (∫ y in B0579.cell p.c, (inner ℂ (-plap W y) (Ws y) : ℂ)).re = dE1 τ := by
      have hibp := congrArg Complex.re
        (cell_ibp_neg_plap_left hc0 hW hWs hWp hWsp hmW1 hmW2 hms0 hmWs1)
      rw [Complex.add_re] at hibp
      simp only [hp1, hpWs1, F8U.slice] at hibp
      dsimp [dE1]
      linarith
    have hvisc : -(∫ y in B0579.cell p.c, (inner ℂ (-plap W y) (plap W y) : ℂ)).re = E2 τ := by
      have hneg : (fun y => (inner ℂ (-plap W y) (plap W y) : ℂ)) =
          fun y => -(inner ℂ (plap W y) (plap W y) : ℂ) := funext fun y => inner_neg_left _ _
      rw [hneg, integral_neg, Complex.neg_re, neg_neg, re_inner_self_eq_cellL2_sq hmW_lap, ← hE2_eq]
    rw [hvisc] at hp
    have habs := (abs_le.mp hbv1).1
    linarith
  -- Level 2 identity (`φ = plap (plap W)`)
  have hlev2 : dE2 τ + 2 * p.ν * E3 τ ≤ 48 * C_tr * (E0 τ + E1 τ + E2 τ) := by
    have hp := hproj_re (plap (plap W)) hmW_lap2 hsol2
    have htime : 2 * (∫ y in B0579.cell p.c, (inner ℂ (plap (plap W) y) (Ws y) : ℂ)).re =
        dE2 τ := by
      have hl := cell_ibp_neg_plap_left hc0 (contDiff_plap hW) hWs (periodic_plap hWp) hWsp
        hmW_dlap hmW_ddlap hms0 hmWs1
      have hr := cell_ibp_neg_plap_right hc0 (contDiff_plap hW) hWs (periodic_plap hWp) hWsp
        hmW_lap hmW_dlap hmWs1 hmWs2
      have hneg : (fun y => (inner ℂ (-plap (plap W) y) (Ws y) : ℂ)) =
          fun y => -(inner ℂ (plap (plap W) y) (Ws y) : ℂ) := funext fun y => inner_neg_left _ _
      rw [hneg, integral_neg] at hl
      have heq_c : (∫ y in B0579.cell p.c, (inner ℂ (plap (plap W) y) (Ws y) : ℂ)) =
          ∫ y in B0579.cell p.c, (inner ℂ (plap W y) (plap Ws y) : ℂ) :=
        neg_injective (hl.trans hr.symm)
      have hre := congrArg Complex.re heq_c
      have hrhs : (fun y => (inner ℂ (plap W y) (plap Ws y) : ℂ)) =
          fun y => (inner ℂ (lapProf w (τ, y)) (F8U.ps (lapProf w) (τ, y)) : ℂ) := by
        funext y; rw [hplap, hplapWs]; rfl
      rw [hre, hrhs]
    have hvisc : -(∫ y in B0579.cell p.c, (inner ℂ (plap (plap W) y) (plap W y) : ℂ)).re =
        E3 τ := by
      have hl := cell_ibp_neg_plap_left hc0 (contDiff_plap hW) (contDiff_plap hW)
        (periodic_plap hWp) (periodic_plap hWp) hmW_dlap hmW_ddlap hmW_lap hmW_dlap
      have hneg : (fun y => (inner ℂ (-plap (plap W) y) (plap W y) : ℂ)) =
          fun y => -(inner ℂ (plap (plap W) y) (plap W y) : ℂ) :=
        funext fun y => inner_neg_left _ _
      rw [hneg, integral_neg] at hl
      have hre := congrArg Complex.re hl
      rw [Complex.neg_re, Complex.add_re, re_inner_self_eq_cellL2_sq (hmW_dlap 0),
        re_inner_self_eq_cellL2_sq (hmW_dlap 1), ← hE3_eq] at hre
      exact hre
    rw [hvisc] at hp
    have habs := (abs_le.mp hbv2).1
    linarith
  -- Assemble all 9 conclusions for orbit_hierarchy_step
  refine ⟨hdP1.continuousAt, hdP2.continuousAt, by dsimp [P1]; linarith,
    by dsimp [P1, P2]; linarith, by dsimp [P3]; linarith,
    hdP1.hasDerivWithinAt, hdP2.hasDerivWithinAt, ?_, ?_⟩
  · have hνE0 : p.ν * E0 τ ≤ E0 τ := mul_le_of_le_one_left hE0_nn hν1
    have hν12 : 0 ≤ p.ν * (E1 τ + E2 τ) := mul_nonneg hν0.le (by linarith)
    have hCE0 : 0 ≤ C_tr * E0 τ := mul_nonneg hC.le hE0_nn
    have hCE1 : 0 ≤ C_tr * E1 τ := mul_nonneg hC.le hE1_nn
    dsimp [P1, P2, K]
    linarith
  · have hνP3 : 0 ≤ p.ν * (E1 τ + E2 τ + E3 τ) := mul_nonneg hν0.le (by linarith)
    have hCE0 : 0 ≤ C_tr * E0 τ := mul_nonneg hC.le hE0_nn
    have hCE1 : 0 ≤ C_tr * E1 τ := mul_nonneg hC.le hE1_nn
    have hCE2 : 0 ≤ C_tr * E2 τ := mul_nonneg hC.le hE2_nn
    dsimp [P1, P2, P3, K]
    linarith

lemma cellL2_sub_triangle_toReal {c : ℝ} {A B : B0579.Plane → CMerid}
    (hmA : MemLp A 2 (cellMeas c)) (hmB : MemLp B 2 (cellMeas c)) :
    (F8U.cellL2 c A).toReal ≤
      (F8U.cellL2 c (fun y => A y - B y)).toReal + (F8U.cellL2 c B).toReal := by
  let D : B0579.Plane → CMerid := fun y => A y - B y
  have hmD : MemLp D 2 (cellMeas c) := hmA.sub hmB
  have heq : A = D + B := by funext y; exact (sub_add_cancel (A y) (B y)).symm
  have hle : eLpNorm A 2 (cellMeas c) ≤ eLpNorm D 2 (cellMeas c) + eLpNorm B 2 (cellMeas c) := by
    rw [heq]
    exact eLpNorm_add_le hmD.aestronglyMeasurable hmB.aestronglyMeasurable one_le_two
  have htr := (ENNReal.toReal_le_toReal hmA.eLpNorm_ne_top
    (ENNReal.add_ne_top.mpr ⟨hmD.eLpNorm_ne_top, hmB.eLpNorm_ne_top⟩)).mpr hle
  rwa [ENNReal.toReal_add hmD.eLpNorm_ne_top hmB.eLpNorm_ne_top] at htr

lemma sqrt_P1_le_err_add {c s' : ℝ} {w : CProf} {u uq uη : B0579.Plane → CMerid}
    (mw : MemLp (F8U.slice w s') 2 (cellMeas c))
    (mw0 : MemLp (F8U.slice (F8U.pd 0 w) s') 2 (cellMeas c))
    (mw1 : MemLp (F8U.slice (F8U.pd 1 w) s') 2 (cellMeas c))
    (mu : MemLp u 2 (cellMeas c))
    (muq : MemLp uq 2 (cellMeas c))
    (muη : MemLp uη 2 (cellMeas c)) :
    Real.sqrt (energySlice c w s' +
      (energySlice c (F8U.pd 0 w) s' + energySlice c (F8U.pd 1 w) s')) ≤
      (F8U.cylH1 c (fun y => w (s', y) - u y)
        (fun y => F8U.pd 0 w (s', y) - uq y)
        (fun y => F8U.pd 1 w (s', y) - uη y)).toReal +
      (F8U.cylH1 c u uq uη).toReal := by
  have mdw : MemLp (fun y => w (s', y) - u y) 2 (cellMeas c) := mw.sub mu
  have mdw0 : MemLp (fun y => F8U.pd 0 w (s', y) - uq y) 2 (cellMeas c) := mw0.sub muq
  have mdw1 : MemLp (fun y => F8U.pd 1 w (s', y) - uη y) 2 (cellMeas c) := mw1.sub muη
  have b0 : (F8U.cellL2 c (F8U.slice w s')).toReal ≤
      (F8U.cellL2 c (fun y => w (s', y) - u y)).toReal + (F8U.cellL2 c u).toReal :=
    cellL2_sub_triangle_toReal mw mu
  have b1 : (F8U.cellL2 c (F8U.slice (F8U.pd 0 w) s')).toReal ≤
      (F8U.cellL2 c (fun y => F8U.pd 0 w (s', y) - uq y)).toReal + (F8U.cellL2 c uq).toReal :=
    cellL2_sub_triangle_toReal mw0 muq
  have b2 : (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) s')).toReal ≤
      (F8U.cellL2 c (fun y => F8U.pd 1 w (s', y) - uη y)).toReal + (F8U.cellL2 c uη).toReal :=
    cellL2_sub_triangle_toReal mw1 muη
  have hP1_eq : energySlice c w s' +
      (energySlice c (F8U.pd 0 w) s' + energySlice c (F8U.pd 1 w) s') =
      (F8U.cellL2 c (F8U.slice w s')).toReal ^ 2 +
        ((F8U.cellL2 c (F8U.slice (F8U.pd 0 w) s')).toReal ^ 2 +
          (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) s')).toReal ^ 2) := by
    rw [energySlice_eq_cellL2_sq mw, energySlice_eq_cellL2_sq mw0, energySlice_eq_cellL2_sq mw1]
  set a0 := (F8U.cellL2 c (F8U.slice w s')).toReal
  set a1 := (F8U.cellL2 c (F8U.slice (F8U.pd 0 w) s')).toReal
  set a2 := (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) s')).toReal
  have ha0 : 0 ≤ a0 := ENNReal.toReal_nonneg
  have ha1 : 0 ≤ a1 := ENNReal.toReal_nonneg
  have ha2 : 0 ≤ a2 := ENNReal.toReal_nonneg
  have hsqrt_le : Real.sqrt (energySlice c w s' +
      (energySlice c (F8U.pd 0 w) s' + energySlice c (F8U.pd 1 w) s')) ≤ a0 + a1 + a2 := by
    rw [hP1_eq, ← Real.sqrt_sq (by linarith : 0 ≤ a0 + a1 + a2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have herr_split : (F8U.cylH1 c (fun y => w (s', y) - u y)
      (fun y => F8U.pd 0 w (s', y) - uq y)
      (fun y => F8U.pd 1 w (s', y) - uη y)).toReal =
      (F8U.cellL2 c (fun y => w (s', y) - u y)).toReal +
      (F8U.cellL2 c (fun y => F8U.pd 0 w (s', y) - uq y)).toReal +
      (F8U.cellL2 c (fun y => F8U.pd 1 w (s', y) - uη y)).toReal := by
    unfold F8U.cylH1
    rw [ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr ⟨cellL2_ne_top mdw, cellL2_ne_top mdw0⟩)
        (cellL2_ne_top mdw1),
      ENNReal.toReal_add (cellL2_ne_top mdw) (cellL2_ne_top mdw0)]
  have hM0_split : (F8U.cylH1 c u uq uη).toReal =
      (F8U.cellL2 c u).toReal + (F8U.cellL2 c uq).toReal + (F8U.cellL2 c uη).toReal := by
    unfold F8U.cylH1
    rw [ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr ⟨cellL2_ne_top mu, cellL2_ne_top muq⟩)
        (cellL2_ne_top muη),
      ENNReal.toReal_add (cellL2_ne_top mu) (cellL2_ne_top muq)]
  linarith

lemma cylH1_le_of_sqrt_P1 {c K M0 t : ℝ} {w : CProf}
    (mwt : MemLp (F8U.slice w t) 2 (cellMeas c))
    (mwt0 : MemLp (F8U.slice (F8U.pd 0 w) t) 2 (cellMeas c))
    (mwt1 : MemLp (F8U.slice (F8U.pd 1 w) t) 2 (cellMeas c))
    (hlim : Real.sqrt (energySlice c w t +
      (energySlice c (F8U.pd 0 w) t + energySlice c (F8U.pd 1 w) t)) ≤ Real.exp K * M0) :
    F8U.cylH1 c (F8U.slice w t) (F8U.slice (F8U.pd 0 w) t) (F8U.slice (F8U.pd 1 w) t) ≤
      ENNReal.ofReal (4 * Real.exp K) * ENNReal.ofReal M0 := by
  set P1t := energySlice c w t + (energySlice c (F8U.pd 0 w) t + energySlice c (F8U.pd 1 w) t)
  have hP1t_eq : P1t = (F8U.cellL2 c (F8U.slice w t)).toReal ^ 2 +
      ((F8U.cellL2 c (F8U.slice (F8U.pd 0 w) t)).toReal ^ 2 +
        (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) t)).toReal ^ 2) := by
    dsimp only [P1t]
    rw [energySlice_eq_cellL2_sq mwt, energySlice_eq_cellL2_sq mwt0, energySlice_eq_cellL2_sq mwt1]
  have hb_w : (F8U.cellL2 c (F8U.slice w t)).toReal ≤ Real.sqrt P1t := by
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg]
    apply Real.sqrt_le_sqrt; rw [hP1t_eq]
    nlinarith [sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 0 w) t)).toReal,
      sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) t)).toReal]
  have hb_w0 : (F8U.cellL2 c (F8U.slice (F8U.pd 0 w) t)).toReal ≤ Real.sqrt P1t := by
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg]
    apply Real.sqrt_le_sqrt; rw [hP1t_eq]
    nlinarith [sq_nonneg (F8U.cellL2 c (F8U.slice w t)).toReal,
      sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) t)).toReal]
  have hb_w1 : (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) t)).toReal ≤ Real.sqrt P1t := by
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg]
    apply Real.sqrt_le_sqrt; rw [hP1t_eq]
    nlinarith [sq_nonneg (F8U.cellL2 c (F8U.slice w t)).toReal,
      sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 0 w) t)).toReal]
  have hfin_t : F8U.cylH1 c (F8U.slice w t) (F8U.slice (F8U.pd 0 w) t)
      (F8U.slice (F8U.pd 1 w) t) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨cellL2_ne_top mwt, cellL2_ne_top mwt0⟩,
        cellL2_ne_top mwt1⟩
  have htr_le : (F8U.cylH1 c (F8U.slice w t) (F8U.slice (F8U.pd 0 w) t)
      (F8U.slice (F8U.pd 1 w) t)).toReal ≤ (4 * Real.exp K) * M0 := by
    have hsplit : (F8U.cylH1 c (F8U.slice w t) (F8U.slice (F8U.pd 0 w) t)
        (F8U.slice (F8U.pd 1 w) t)).toReal =
        (F8U.cellL2 c (F8U.slice w t)).toReal +
        (F8U.cellL2 c (F8U.slice (F8U.pd 0 w) t)).toReal +
        (F8U.cellL2 c (F8U.slice (F8U.pd 1 w) t)).toReal := by
      unfold F8U.cylH1
      rw [ENNReal.toReal_add
          (ENNReal.add_ne_top.mpr ⟨cellL2_ne_top mwt, cellL2_ne_top mwt0⟩)
          (cellL2_ne_top mwt1),
        ENNReal.toReal_add (cellL2_ne_top mwt) (cellL2_ne_top mwt0)]
    have hsqrt_nn : 0 ≤ Real.sqrt P1t := Real.sqrt_nonneg _
    linarith
  rw [← ENNReal.ofReal_toReal hfin_t, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal htr_le

lemma sum_d2_le_of_sqrt_E2 {c ν σ K M0 t : ℝ} (hc0 : 0 < c) (hν0 : 0 < ν) (ht : σ < t)
    {w : CProf} (hw_sm : ContDiffOn ℝ ∞ w (stripSet σ))
    (hw_per : ∀ x : Coord, x.1 ∈ Ioo σ (σ + 2) → w (qShift c x) = w x)
    (ht_in : t ∈ Ioo σ (σ + 2))
    (mwt1 : ∀ i : Fin 2, MemLp (F8U.slice (F8U.pd i w) t) 2 (cellMeas c))
    (mwt2 : ∀ i j : Fin 2, MemLp (F8U.slice (F8U.pd i (F8U.pd j w)) t) 2 (cellMeas c))
    (mwt3 : ∀ i j k : Fin 2, MemLp (F8U.slice (F8U.pd i (F8U.pd j (F8U.pd k w))) t) 2 (cellMeas c))
    (hE2_lim : Real.sqrt (energySlice c (lapProf w) t) ≤
      Real.exp K * ν ^ (-1 / 2 : ℝ) * (t - σ) ^ (-1 / 2 : ℝ) * M0) :
    ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 c (F8U.slice (F8U.pd i (F8U.pd j w)) t) ≤
      ENNReal.ofReal ((4 * Real.exp K) * ν ^ (-1 / 2 : ℝ) * (t - σ) ^ (-1 / 2 : ℝ)) *
        ENNReal.ofReal M0 := by
  let Wt := F8U.slice w t
  have hWt : ContDiff ℝ ∞ Wt := contDiff_slice hw_sm ht_in
  have hWtp : UnforcedLeray.Cyl.IsPeriodic c Wt := fun y => hw_per (t, y) ht_in
  have hp1 : ∀ i, pdir i Wt = F8U.slice (F8U.pd i w) t := pdir_slice_eq hw_sm ht_in
  have hp2 : ∀ i j, pdir i (pdir j Wt) = F8U.slice (F8U.pd i (F8U.pd j w)) t :=
    fun i j => by rw [hp1 j, pdir_slice_eq (contDiffOn_pd hw_sm j) ht_in i]
  have hp3 : ∀ i j k, pdir i (pdir j (pdir k Wt)) =
      F8U.slice (F8U.pd i (F8U.pd j (F8U.pd k w))) t :=
    fun i j k => by
      rw [hp2 j k, pdir_slice_eq (contDiffOn_pd (contDiffOn_pd hw_sm k) j) ht_in i]
  have hplap_t : plap Wt = F8U.slice (lapProf w) t := plap_slice_eq hw_sm ht_in
  have hboch := cellL2_plap_sq_eq_sum hc0 hWt hWtp
    (fun i => by rw [hp1 i]; exact mwt1 i)
    (fun i j => by rw [hp2 i j]; exact mwt2 i j)
    (fun i j k => by rw [hp3 i j k]; exact mwt3 i j k)
  have hm_lap_t : MemLp (F8U.slice (lapProf w) t) 2 (cellMeas c) :=
    memLp_fun_add (mwt2 0 0) (mwt2 1 1)
  have hE2t_eq : energySlice c (lapProf w) t = (F8U.cellL2 c (plap Wt)).toReal ^ 2 := by
    rw [energySlice_eq_cellL2_sq hm_lap_t, ← hplap_t]
  have hd2_each : ∀ i j : Fin 2,
      F8U.cellL2 c (F8U.slice (F8U.pd i (F8U.pd j w)) t) ≤
        ENNReal.ofReal (Real.sqrt (energySlice c (lapProf w) t)) := by
    intro i j
    have hsq : (F8U.cellL2 c (F8U.slice (F8U.pd i (F8U.pd j w)) t)).toReal ^ 2 ≤
        energySlice c (lapProf w) t := by
      rw [hE2t_eq, hboch]
      simp_rw [hp2]
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
        nlinarith [sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 0 (F8U.pd 0 w)) t)).toReal,
          sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 0 (F8U.pd 1 w)) t)).toReal,
          sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 1 (F8U.pd 0 w)) t)).toReal,
          sq_nonneg (F8U.cellL2 c (F8U.slice (F8U.pd 1 (F8U.pd 1 w)) t)).toReal]
    have hle_r : (F8U.cellL2 c (F8U.slice (F8U.pd i (F8U.pd j w)) t)).toReal ≤
        Real.sqrt (energySlice c (lapProf w) t) := by
      rw [← Real.sqrt_sq ENNReal.toReal_nonneg]
      exact Real.sqrt_le_sqrt hsq
    rw [← ENNReal.ofReal_toReal (cellL2_ne_top (mwt2 i j))]
    exact ENNReal.ofReal_le_ofReal hle_r
  have hsum_le : ∑ i : Fin 2, ∑ j : Fin 2,
      F8U.cellL2 c (F8U.slice (F8U.pd i (F8U.pd j w)) t) ≤
      ENNReal.ofReal (4 * Real.sqrt (energySlice c (lapProf w) t)) := by
    calc ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 c (F8U.slice (F8U.pd i (F8U.pd j w)) t)
        ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, ENNReal.ofReal (Real.sqrt (energySlice c (lapProf w) t)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hd2_each i j
      _ = ENNReal.ofReal (4 * Real.sqrt (energySlice c (lapProf w) t)) := by
          rw [Fin.sum_univ_two, Fin.sum_univ_two]
          have hnn : 0 ≤ Real.sqrt (energySlice c (lapProf w) t) := Real.sqrt_nonneg _
          rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  have h4E2 : 4 * Real.sqrt (energySlice c (lapProf w) t) ≤
      ((4 * Real.exp K) * ν ^ (-1 / 2 : ℝ) * (t - σ) ^ (-1 / 2 : ℝ)) * M0 := by
    linarith [hE2_lim]
  have hfac_nn : 0 ≤ (4 * Real.exp K) * ν ^ (-1 / 2 : ℝ) * (t - σ) ^ (-1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hν0.le _))
      (Real.rpow_nonneg (sub_pos.mpr ht).le _)
  rw [← ENNReal.ofReal_mul hfac_nn]
  exact hsum_le.trans (ENNReal.ofReal_le_ofReal h4E2)

end F8Sm

/-- **Unconditional proof of `CylOseenOrbitSmoothing` (`PartII-b:F8/1/org/1`, SP 2296–2301)**. -/
theorem cylOseenOrbitSmoothing_proof : UnforcedLeray.Short.IIb.CylOseenOrbitSmoothing := by
  intro C_tr hC
  let K : ℝ := 48 * C_tr + 2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨4 * Real.exp K, by positivity, ?_⟩
  intro dm dp p d _ hν1 htr σ hσ u uq uη w hdat hw t ht
  have hc0 : 0 < p.c := p.c_pos
  have hν0 : 0 < p.ν := p.ν_pos
  have ht_in : t ∈ Ioo σ (σ + 2) := ⟨ht.1, by linarith [ht.2]⟩
  let E0 := F8Sm.energySlice p.c w
  let E1 := fun τ => F8Sm.energySlice p.c (F8U.pd 0 w) τ + F8Sm.energySlice p.c (F8U.pd 1 w) τ
  let E2 := F8Sm.energySlice p.c (F8Sm.lapProf w)
  let P1 := fun τ => E0 τ + E1 τ
  let P2 := fun τ => E0 τ + E1 τ + E2 τ
  obtain ⟨P1', P2', hstep⟩ := F8Sm.orbit_hierarchy_step hσ hν1 hC htr hw
  have hu_fin : F8U.cylH1 p.c u uq uη ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hdat.memL2.1.eLpNorm_ne_top, hdat.memL2.2.1.eLpNorm_ne_top⟩,
        hdat.memL2.2.2.eLpNorm_ne_top⟩
  set M0 : ℝ := (F8U.cylH1 p.c u uq uη).toReal
  have hu_ofReal : F8U.cylH1 p.c u uq uη = ENNReal.ofReal M0 :=
    (ENNReal.ofReal_toReal hu_fin).symm
  let errE : ℝ → ℝ≥0∞ := fun s' =>
    F8U.cylH1 p.c (fun y => w (s', y) - u y)
      (fun y => F8U.pd 0 w (s', y) - uq y)
      (fun y => F8U.pd 1 w (s', y) - uη y)
  have herr_toReal : Tendsto (fun s' => (errE s').toReal) (𝓝[>] σ) (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hw.initial
  have hstep_s : ∀ s' ∈ Ioo σ t,
      Real.sqrt (P1 t) ≤ Real.exp K * ((errE s').toReal + M0) ∧
      Real.sqrt (E2 t) ≤ Real.exp K * p.ν ^ (-1 / 2 : ℝ) * (t - s') ^ (-1 / 2 : ℝ) *
        ((errE s').toReal + M0) := by
    intro s' hs'
    have hs'_in : s' ∈ Ioo σ (σ + 2) := ⟨hs'.1, hs'.2.trans ht_in.2⟩
    have hinit : Real.sqrt (P1 s') ≤ (errE s').toReal + M0 :=
      F8Sm.sqrt_P1_le_err_add
        (hw.memL2 s' hs'_in 0 (by decide) ![])
        (hw.memL2 s' hs'_in 1 (by decide) ![0])
        (hw.memL2 s' hs'_in 1 (by decide) ![1])
        hdat.memL2.1 hdat.memL2.2.1 hdat.memL2.2.2
    have hsub : Icc s' t ⊆ Ioo σ (σ + 2) := fun τ hτ =>
      ⟨lt_of_lt_of_le hs'.1 hτ.1, lt_of_le_of_lt hτ.2 ht_in.2⟩
    have hc1 : ContinuousOn P1 (Icc s' t) :=
      fun τ hτ => (hstep τ (hsub hτ)).1.continuousWithinAt
    have hc2 : ContinuousOn P2 (Icc s' t) :=
      fun τ hτ => (hstep τ (hsub hτ)).2.1.continuousWithinAt
    have hgron := F8U.parabolic_multiplier_gronwall hν0.le hK.le hs'.2.le hc1 hc2
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.2.2.2)
    have hts1 : t - s' ≤ 1 := by linarith [ht.2, hs'.1]
    have hsm := F8U.parabolic_sqrt_E2_le_of_hierarchy hν0 hK.le hs'.2 hts1 hc1 hc2
      (fun τ hτ => (hstep τ (hsub hτ)).2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.2.2.1)
      (fun τ hτ => (hstep τ (hsub ⟨hτ.1, hτ.2.le⟩)).2.2.2.2.2.2.2.2)
    have hP1s_nn : 0 ≤ P1 s' := (hstep s' (hsub ⟨le_rfl, hs'.2.le⟩)).2.2.1
    have hP2t_nn : 0 ≤ P2 t := (hstep t ht_in).2.2.1.trans (hstep t ht_in).2.2.2.1
    have hlyap_ge : P1 t ≤ F8U.parabolicLyapunov p.ν s' P1 P2 t := by
      unfold F8U.parabolicLyapunov
      have : 0 ≤ p.ν * (t - s') * P2 t :=
        mul_nonneg (mul_nonneg hν0.le (sub_nonneg.mpr hs'.2.le)) hP2t_nn
      linarith
    have hexp_le : Real.exp (2 * K * (t - s')) ≤ Real.exp (2 * K) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hP1t_le : P1 t ≤ Real.exp (2 * K) * P1 s' :=
      (hlyap_ge.trans hgron).trans (mul_le_mul_of_nonneg_right hexp_le hP1s_nn)
    have hsqrt_exp : Real.sqrt (Real.exp (2 * K)) = Real.exp K := by
      rw [show 2 * K = K + K by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos K).le]
    have h1 : Real.sqrt (P1 t) ≤ Real.exp K * Real.sqrt (P1 s') := by
      have hsq := Real.sqrt_le_sqrt hP1t_le
      rwa [Real.sqrt_mul (Real.exp_pos _).le, hsqrt_exp] at hsq
    have hE2_le_P2 : E2 t ≤ P2 t := by
      have hP1t_nn : 0 ≤ P1 t := (hstep t ht_in).2.2.1
      dsimp [P1, P2] at hP1t_nn ⊢
      linarith
    refine ⟨h1.trans (mul_le_mul_of_nonneg_left hinit (Real.exp_pos K).le), ?_⟩
    have hfac_nn : 0 ≤ Real.exp K * p.ν ^ (-1 / 2 : ℝ) * (t - s') ^ (-1 / 2 : ℝ) :=
      mul_nonneg (mul_nonneg (Real.exp_pos K).le (Real.rpow_nonneg hν0.le _))
        (Real.rpow_nonneg (sub_pos.mpr hs'.2).le _)
    exact (Real.sqrt_le_sqrt hE2_le_P2).trans
      (hsm.trans (mul_le_mul_of_nonneg_left hinit hfac_nn))
  have hev_Ioo : ∀ᶠ s' in 𝓝[>] σ, s' ∈ Ioo σ t :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds ht.1))
  have hlim_init : Tendsto (fun s' => (errE s').toReal + M0) (𝓝[>] σ) (𝓝 M0) := by
    simpa only [zero_add] using herr_toReal.add tendsto_const_nhds
  have hP1_lim : Real.sqrt (P1 t) ≤ Real.exp K * M0 :=
    ge_of_tendsto (hlim_init.const_mul (Real.exp K))
      (hev_Ioo.mono fun s' hs' => (hstep_s s' hs').1)
  have hcont_ts : ContinuousAt (fun s' : ℝ => (t - s') ^ (-1 / 2 : ℝ)) σ :=
    (continuousAt_const.sub continuousAt_id).rpow continuousAt_const
      (Or.inl (sub_pos.mpr ht.1).ne')
  have hlim_ts : Tendsto (fun s' : ℝ => (t - s') ^ (-1 / 2 : ℝ)) (𝓝[>] σ)
      (𝓝 ((t - σ) ^ (-1 / 2 : ℝ))) :=
    hcont_ts.tendsto.mono_left nhdsWithin_le_nhds
  have hE2_lim : Real.sqrt (E2 t) ≤
      Real.exp K * p.ν ^ (-1 / 2 : ℝ) * (t - σ) ^ (-1 / 2 : ℝ) * M0 :=
    ge_of_tendsto ((hlim_ts.const_mul (Real.exp K * p.ν ^ (-1 / 2 : ℝ))).mul hlim_init)
      (hev_Ioo.mono fun s' hs' => (hstep_s s' hs').2)
  rw [hu_ofReal]
  exact ⟨F8Sm.cylH1_le_of_sqrt_P1
      (hw.memL2 t ht_in 0 (by decide) ![])
      (hw.memL2 t ht_in 1 (by decide) ![0])
      (hw.memL2 t ht_in 1 (by decide) ![1]) hP1_lim,
    F8Sm.sum_d2_le_of_sqrt_E2 hc0 hν0 ht.1 hw.smooth hw.periodic ht_in
      (fun i => hw.memL2 t ht_in 1 (by decide) ![i])
      (fun i j => hw.memL2 t ht_in 2 (by decide) ![i, j])
      (fun i j k => hw.memL2 t ht_in 3 (by decide) ![i, j, k]) hE2_lim⟩

end UnforcedLeray.Short.IIb
