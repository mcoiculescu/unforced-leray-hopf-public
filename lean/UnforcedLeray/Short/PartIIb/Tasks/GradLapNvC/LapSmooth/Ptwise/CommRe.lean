import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5_5

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

namespace LapCommReHelp

/-- `vQ ε` has smooth components. -/
lemma vQ_component_smooth (ε : ℝ) (j : Fin 3) : ContDiff ℝ ∞ (fun x : Coord => vQ ε x j) := by
  fin_cases j <;> simp [vQ] <;> fun_prop

/-- The derivative of a smooth profile is smooth. -/
lemma fderiv_smooth {b : CProf} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (fderiv ℝ b) :=
  hb.fderiv_right (by simp)

/-- Directional derivatives of a smooth profile are smooth. -/
lemma fderiv_dir_smooth {b : CProf} (hb : ContDiff ℝ ∞ b) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ b x (cdir j)) :=
  (fderiv_smooth hb).clm_apply contDiff_const

/-- `classQ ε b` is smooth. -/
lemma classQ_smooth (ε : ℝ) {b : CProf} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (classQ ε b) := by
  have hdQ : ContDiff ℝ ∞ (dQ ε) := contDiff_const
  have hsum : ContDiff ℝ ∞ (fun x : Coord => ∑ j : Fin 3, vQ ε x j • fderiv ℝ b x (cdir j)) :=
    ContDiff.sum (fun j _ => (vQ_component_smooth ε j).smul (fderiv_dir_smooth hb j))
  exact hsum.add (hdQ.smul hb)

/-- `classEta b` is smooth. -/
lemma classEta_smooth {b : CProf} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (classEta b) :=
  fderiv_dir_smooth hb 2

/-- `reM` as a real-linear map. -/
def reML : CMerid →L[ℝ] UnforcedLeray.Axi.Merid :=
  LinearMap.toContinuousLinearMap
    { toFun := reM
      map_add' := reM_add
      map_smul' := fun c v => by ext i; simp [reM] }

/-- `imM` as a real-linear map. -/
def imML : CMerid →L[ℝ] UnforcedLeray.Axi.Merid :=
  LinearMap.toContinuousLinearMap
    { toFun := imM
      map_add' := imM_add
      map_smul' := fun c v => by ext i; simp [imM] }

/-- Chain rule: the derivative of `reM ∘ b` is `reM` of the derivative of `b`. -/
lemma fderiv_reM_apply {b : CProf} (hb : ContDiff ℝ ∞ b) (x : Coord) (v : Coord) :
    fderiv ℝ (fun y => reM (b y)) x v = reM (fderiv ℝ b x v) := by
  have h := reML.hasFDerivAt.comp x ((hb.differentiable (by simp)) x).hasFDerivAt
  show fderiv ℝ (reML ∘ b) x v = _
  rw [h.fderiv]
  rfl

lemma fderiv_imM_apply {b : CProf} (hb : ContDiff ℝ ∞ b) (x : Coord) (v : Coord) :
    fderiv ℝ (fun y => imM (b y)) x v = imM (fderiv ℝ b x v) := by
  have h := imML.hasFDerivAt.comp x ((hb.differentiable (by simp)) x).hasFDerivAt
  show fderiv ℝ (imML ∘ b) x v = _
  rw [h.fderiv]
  rfl

lemma reM_classQ {b : CProf} (ε : ℝ) (hb : ContDiff ℝ ∞ b) (x : Coord) :
    reM (classQ ε b x) = classQg ε (fun y => reM (b y)) x := by
  unfold classQ classQg
  simp only [fderiv_reM_apply hb]
  change reML ((∑ j : Fin 3, vQ ε x j • fderiv ℝ b x (cdir j)) + dQ ε x • b x) = _
  simp only [map_add, map_sum, map_smul]
  rfl

lemma imM_classQ {b : CProf} (ε : ℝ) (hb : ContDiff ℝ ∞ b) (x : Coord) :
    imM (classQ ε b x) = classQg ε (fun y => imM (b y)) x := by
  unfold classQ classQg
  simp only [fderiv_imM_apply hb]
  change imML ((∑ j : Fin 3, vQ ε x j • fderiv ℝ b x (cdir j)) + dQ ε x • b x) = _
  simp only [map_add, map_sum, map_smul]
  rfl

lemma reM_classEta {b : CProf} (hb : ContDiff ℝ ∞ b) (x : Coord) :
    reM (classEta b x) = classEtaG (fun y => reM (b y)) x := by
  unfold classEta classEtaG
  exact (fderiv_reM_apply hb x (cdir 2)).symm

lemma imM_classEta {b : CProf} (hb : ContDiff ℝ ∞ b) (x : Coord) :
    imM (classEta b x) = classEtaG (fun y => imM (b y)) x := by
  unfold classEta classEtaG
  exact (fderiv_imM_apply hb x (cdir 2)).symm

end LapCommReHelp

open LapCommReHelp in
/-- **Leaf `T09/5/5/4`** (`reM`, `imM` are real-linear coordinate projections, so commute with
`fderiv`). -/
theorem lapCommRe : UnforcedLeray.Short.IIb.LapCommRe := by
  intro ε b hb
  have hre : ContDiff ℝ ∞ (fun x => reM (b x)) := reML.contDiff.comp hb
  have him : ContDiff ℝ ∞ (fun x => imM (b x)) := imML.contDiff.comp hb
  exact ⟨hre, him, classQ_smooth ε hb, classEta_smooth hb,
    fun x => reM_classQ ε hb x, fun x => imM_classQ ε hb x,
    fun x => reM_classEta hb x, fun x => imM_classEta hb x⟩

end UnforcedLeray.Short.IIb
