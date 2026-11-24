import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5_5

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ### Slices and the Laplacian of a joint function -/

theorem hasFDerivAt_slice (t : ℝ) (z : Space) :
    HasFDerivAt (fun w : Space => (t, w))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) z :=
  (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)

theorem fderiv_slice_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} {t : ℝ} {z : Space} (hf : DifferentiableAt ℝ f (t, z)) (v : Space) :
    fderiv ℝ (fun w : Space => f (t, w)) z v = fderiv ℝ f (t, z) (0, v) := by
  have h := hf.hasFDerivAt.comp z (hasFDerivAt_slice t z)
  rw [show (fun w : Space => f (t, w)) = f ∘ (fun w : Space => (t, w)) from rfl, h.fderiv]
  simp

/-- The vector Laplacian of a joint function, computed on a time slice. -/
theorem lapT_eq_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} {W : Set (ℝ × Space)} (hW : IsOpen W) (hf : ContDiffOn ℝ 2 f W)
    {t : ℝ} {y : Space} (hp : (t, y) ∈ W) :
    lapT f (t, y) = ∑ i : Fin 3, fderiv ℝ (fun x =>
      fderiv ℝ (fun w : Space => f (t, w)) x (coordinateVector i)) y (coordinateVector i) := by
  have hfd1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ f x) W := hf.fderiv_of_isOpen hW (by norm_num)
  have hDfd : ∀ q ∈ W, DifferentiableAt ℝ (fun x => fderiv ℝ f x) q :=
    fun q hq => ((hfd1.differentiableOn (by norm_num)) q hq).differentiableAt (hW.mem_nhds hq)
  have hDf : ∀ q ∈ W, DifferentiableAt ℝ f q := fun q hq =>
    (hf.contDiffAt (hW.mem_nhds hq)).differentiableAt (by norm_num)
  have hdyD : ∀ j : Fin 3, ∀ q ∈ W, DifferentiableAt ℝ (dy j f) q := fun j q hq =>
    (hDfd q hq).clm_apply (differentiableAt_const _)
  have hopen : IsOpen {z : Space | (t, z) ∈ W} :=
    hW.preimage (Continuous.prodMk continuous_const continuous_id)
  unfold lapT
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : fderiv ℝ (fun z : Space => dy j f (t, z)) y (coordinateVector j) =
      fderiv ℝ (dy j f) (t, y) (0, coordinateVector j) := by
    have h := (hdyD j (t, y) hp).hasFDerivAt.comp y (hasFDerivAt_slice t y)
    rw [show (fun z : Space => dy j f (t, z)) = dy j f ∘ (fun w : Space => (t, w)) from rfl,
      h.fderiv]
    simp
  have h3 : (fun z : Space => dy j f (t, z)) =ᶠ[𝓝 y]
      (fun z : Space => fderiv ℝ (fun w : Space => f (t, w)) z (coordinateVector j)) := by
    filter_upwards [hopen.mem_nhds hp] with z hz
    show fderiv ℝ f (t, z) (0, coordinateVector j) = _
    rw [fderiv_slice_eq (hDf (t, z) hz)]
  show fderiv ℝ (dy j f) (t, y) (0, coordinateVector j) = _
  rw [← h2, h3.fderiv_eq]


/-! ### Two-term Laplacian through continuous linear maps -/

theorem lap_comb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set Space}
    (hU : IsOpen U) (A B : Space →L[ℝ] E) {h1 h2 : Space → Space}
    (hh1 : ContDiffOn ℝ 2 h1 U) (hh2 : ContDiffOn ℝ 2 h2 U) {y : Space} (hy : y ∈ U)
    {G : Space → E} (hG : ∀ w, G w = A (h1 w) + B (h2 w)) :
    ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ G x
        (coordinateVector i)) y (coordinateVector i) =
      A (UnforcedLeray.Axi.vecLap h1 y) + B (UnforcedLeray.Axi.vecLap h2 y) := by
  have hGe : G = fun w => A (h1 w) + B (h2 w) := funext hG
  subst hGe
  have hd1 : ∀ x ∈ U, DifferentiableAt ℝ h1 x := fun x hx =>
    (hh1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hd2 : ∀ x ∈ U, DifferentiableAt ℝ h2 x := fun x hx =>
    (hh2.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hf1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ h1 x) U := hh1.fderiv_of_isOpen hU (by norm_num)
  have hf2 : ContDiffOn ℝ 1 (fun x => fderiv ℝ h2 x) U := hh2.fderiv_of_isOpen hU (by norm_num)
  have hD1 : DifferentiableAt ℝ (fun x => fderiv ℝ h1 x) y :=
    ((hf1.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)
  have hD2 : DifferentiableAt ℝ (fun x => fderiv ℝ h2 x) y :=
    ((hf2.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)
  unfold UnforcedLeray.Axi.vecLap
  rw [map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hev : (fun x => fderiv ℝ (fun w => A (h1 w) + B (h2 w)) x (coordinateVector i)) =ᶠ[𝓝 y]
      (fun x => A (fderiv ℝ h1 x (coordinateVector i)) +
        B (fderiv ℝ h2 x (coordinateVector i))) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    have : HasFDerivAt (fun w => A (h1 w) + B (h2 w))
        (A ∘L fderiv ℝ h1 x + B ∘L fderiv ℝ h2 x) x :=
      (A.hasFDerivAt.comp x (hd1 x hx).hasFDerivAt).add
        (B.hasFDerivAt.comp x (hd2 x hx).hasFDerivAt)
    rw [this.fderiv]
    simp
  rw [hev.fderiv_eq]
  have e1 : DifferentiableAt ℝ (fun x => fderiv ℝ h1 x (coordinateVector i)) y :=
    hD1.clm_apply (differentiableAt_const _)
  have e2 : DifferentiableAt ℝ (fun x => fderiv ℝ h2 x (coordinateVector i)) y :=
    hD2.clm_apply (differentiableAt_const _)
  have : HasFDerivAt (fun x => A (fderiv ℝ h1 x (coordinateVector i)) +
        B (fderiv ℝ h2 x (coordinateVector i)))
      (A ∘L fderiv ℝ (fun x => fderiv ℝ h1 x (coordinateVector i)) y +
        B ∘L fderiv ℝ (fun x => fderiv ℝ h2 x (coordinateVector i)) y) y :=
    (A.hasFDerivAt.comp y e1.hasFDerivAt).add (B.hasFDerivAt.comp y e2.hasFDerivAt)
  rw [this.fderiv]
  simp

/-! ### Joint smoothness of `Nv` off the axis -/

theorem isOpen_offAxis : IsOpen {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} := by
  have hc : IsClosed {y : Space | y ∈ UnforcedLeray.Axi.axis} := by
    have : {y : Space | y ∈ UnforcedLeray.Axi.axis} = {y : Space | y 0 = 0} ∩ {y | y 1 = 0} := rfl
    rw [this]
    exact (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) continuous_const)
  exact (hc.isOpen_compl).preimage continuous_snd

theorem contDiffOn_Nv_joint {R : ℝ} (hR : R ≠ 0) {b : Coord → UnforcedLeray.Axi.Merid}
    (hb : ContDiff ℝ ∞ b) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R b x.1 x.2)
      {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} := by
  set W : Set (ℝ × Space) := {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} with hW
  have hϱ : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.ϱ x.2) W :=
    UnforcedLeray.Axi.contDiffOn_ϱ.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hϱ0 : ∀ x ∈ W, UnforcedLeray.Axi.ϱ x.2 ≠ 0 := fun x hx => UnforcedLeray.Axi.ϱ_ne_zero hx
  have hage : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.age R x.2) W := by
    unfold UnforcedLeray.Axi.age
    exact contDiffOn_const.div (hϱ.pow 2) fun x hx => pow_ne_zero 2 (hϱ0 x hx)
  have hage0 : ∀ x ∈ W, UnforcedLeray.Axi.age R x.2 ≠ 0 := fun x hx =>
    (UnforcedLeray.Axi.age_pos hR hx).ne'
  have hphase : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.phase R x.1 x.2) W := by
    unfold UnforcedLeray.Axi.phase
    exact (contDiff_const.mul contDiff_fst).div_const 2 |>.contDiffOn.sub
      (contDiffOn_const.mul (hage.log hage0))
  have htrans : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.trans R x.2) W := by
    unfold UnforcedLeray.Axi.trans
    have h2 : ContDiff ℝ ∞ (fun x : ℝ × Space => x.2 2) := by fun_prop
    exact ((contDiff_const.mul h2).contDiffOn (s := W)).div hϱ hϱ0
  have hchart : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.chart R x.1 x.2) W := by
    unfold UnforcedLeray.Axi.chart
    exact hage.prodMk (hphase.prodMk htrans)
  have hbc : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (UnforcedLeray.Axi.chart R x.1 x.2)) W :=
    hb.comp_contDiffOn hchart
  have hb0 : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (UnforcedLeray.Axi.chart R x.1 x.2) 0) W :=
    (EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have hb1 : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (UnforcedLeray.Axi.chart R x.1 x.2) 1) W :=
    (EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have heR : ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.eR x.2) W :=
    UnforcedLeray.Axi.contDiffOn_eR.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hsq : ContDiffOn ℝ ∞ (fun x : ℝ × Space => √(UnforcedLeray.Axi.age R x.2)) W :=
    hage.sqrt hage0
  have : (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R b x.1 x.2) = fun x =>
      √(UnforcedLeray.Axi.age R x.2) •
        (b (UnforcedLeray.Axi.chart R x.1 x.2) 0 • UnforcedLeray.Axi.eR x.2 +
          b (UnforcedLeray.Axi.chart R x.1 x.2) 1 • UnforcedLeray.Axi.e3) := by
    funext x
    simp [UnforcedLeray.Axi.Nv, UnforcedLeray.Axi.frameL_apply]
  rw [this]
  exact hsq.smul ((hb0.smul heR).add (hb1.smul contDiffOn_const))

/-- `reM` as a continuous real-linear map. -/
def reML : CMerid →L[ℝ] UnforcedLeray.Axi.Merid :=
  LinearMap.toContinuousLinearMap
    { toFun := reM
      map_add' := reM_add
      map_smul' := fun r v => by
        simpa [Complex.real_smul] using reM_real_smul r v }

def imML : CMerid →L[ℝ] UnforcedLeray.Axi.Merid :=
  LinearMap.toContinuousLinearMap
    { toFun := imM
      map_add' := imM_add
      map_smul' := fun r v => by
        simpa [Complex.real_smul] using imM_real_smul r v }

/-- Real vectors in `ℂ³`, as a real-linear map. -/
def realCLs : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => UnforcedLeray.B0412.realC x
      map_add' := fun x y => by ext i; simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by ext i; simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul] }

/-- `i ·` realC, as a real-linear map. -/
def imCLs : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Complex.I • UnforcedLeray.B0412.realC x
      map_add' := fun x y => by ext i; simp [UnforcedLeray.B0412.realC_apply, mul_add]
      map_smul' := fun c x => by
        ext i; simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul]; ring }

theorem NvC_eq (R : ℝ) (b : CProf) (x : ℝ × Space) :
    NvC R b x = realCLs (UnforcedLeray.Axi.Nv R (fun z => reM (b z)) x.1 x.2) +
      imCLs (UnforcedLeray.Axi.Nv R (fun z => imM (b z)) x.1 x.2) := by
  simp [NvC, realCLs, imCLs]

theorem slice_cd {F : ℝ → Space → Space} {W : Set (ℝ × Space)}
    (h : ContDiffOn ℝ 2 (fun x : ℝ × Space => F x.1 x.2) W) (t : ℝ) :
    ContDiffOn ℝ 2 (F t) {z : Space | (t, z) ∈ W} := by
  have hsl : ContDiff ℝ 2 (fun z : Space => ((t, z) : ℝ × Space)) :=
    contDiff_const.prodMk contDiff_id
  exact h.comp hsl.contDiffOn (fun z hz => hz)

theorem le2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  first
  | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  | exact (by norm_cast; exact le_top)
  | simp
  | exact ENat.LEInfty.out

theorem lapSplit : UnforcedLeray.Short.IIb.LapSplit := by
  intro R b hR hb t y hy
  have hR0 : R ≠ 0 := hR.ne'
  have hre : ContDiff ℝ ∞ (fun x => reM (b x)) := reML.contDiff.comp hb
  have him : ContDiff ℝ ∞ (fun x => imM (b x)) := imML.contDiff.comp hb
  set W : Set (ℝ × Space) := {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} with hW
  have hWo : IsOpen W := isOpen_offAxis
  have j1 := contDiffOn_Nv_joint hR0 hre
  have j2 := contDiffOn_Nv_joint hR0 him
  have hfun : NvC R b = fun x : ℝ × Space =>
      realCLs (UnforcedLeray.Axi.Nv R (fun z => reM (b z)) x.1 x.2) +
        imCLs (UnforcedLeray.Axi.Nv R (fun z => imM (b z)) x.1 x.2) := by
    funext x; exact NvC_eq R b x
  have hg : ContDiffOn ℝ 2 (NvC R b) W := by
    rw [hfun]
    exact (realCLs.contDiff.comp_contDiffOn (j1.of_le le2)).add
      (imCLs.contDiff.comp_contDiffOn (j2.of_le le2))
  have hU : IsOpen (UnforcedLeray.Axi.axis)ᶜ := by
    have hc : IsClosed UnforcedLeray.Axi.axis := by
      have : UnforcedLeray.Axi.axis = {y : Space | y 0 = 0} ∩ {y | y 1 = 0} := rfl
      rw [this]
      exact (isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const)
    exact hc.isOpen_compl
  have hyU : y ∈ (UnforcedLeray.Axi.axis)ᶜ := hy
  have hsl : ContDiffOn ℝ 2 (fun z : Space => ((t, z) : ℝ × Space)) (UnforcedLeray.Axi.axis)ᶜ :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmp : Set.MapsTo (fun z : Space => ((t, z) : ℝ × Space)) (UnforcedLeray.Axi.axis)ᶜ W :=
    fun z hz => hz
  have j1' : ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R (fun z => reM (b z)) x.1 x.2) W :=
    j1.of_le le2
  have j2' : ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R (fun z => imM (b z)) x.1 x.2) W :=
    j2.of_le le2
  have s1 : ContDiffOn ℝ 2 (fun z => UnforcedLeray.Axi.Nv R (fun x => reM (b x)) t z)
      (UnforcedLeray.Axi.axis)ᶜ := slice_cd j1' t
  have s2 : ContDiffOn ℝ 2 (fun z => UnforcedLeray.Axi.Nv R (fun x => imM (b x)) t z)
      (UnforcedLeray.Axi.axis)ᶜ := slice_cd j2' t
  rw [lapT_eq_slice hWo hg (show (t, y) ∈ W from hy)]
  have h := lap_comb hU realCLs imCLs s1 s2 hyU (G := fun w : Space => NvC R b (t, w))
    (fun w => NvC_eq R b (t, w))
  rw [h]
  have c1 : ∀ v, realCLs v = UnforcedLeray.B0412.realC v := fun v => rfl
  have c2 : ∀ v, imCLs v = Complex.I • UnforcedLeray.B0412.realC v := fun v => rfl
  exact congrArg₂ (· + ·) (c1 _) (c2 _)

end UnforcedLeray.Short.IIb
