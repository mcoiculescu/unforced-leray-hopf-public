import UnforcedLeray.Short.PartIIIb.NearInst.Body.Conj
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# Real forms of the body inverses `T_ε`, `T_0` (source 1675-1677)

Source of record: `the November 2 reference manuscript`.  `T_ε = (μ - A_ε)^{-1}P_ε`
(`PartIIa.Teps = B0223.RepsVec ∘ PartIIa.PepsC ε c`, `P = 2εc`) and `T_0` (`PartIIa.T0flat =
B0225.R0 ∘ PartIIa.PepsC 0 c`) act on the complex `H = L²(s^{-3/2} ds dq dη; ℂ²)` over the cell
`q ∈ (0, c]`.  For real `μ` with `μ + 1/4 > 0` they commute with complex conjugation, hence map real
fields to real fields and have real forms on the near space `Hsp c` (`Concrete/Spaces.lean`, cell
`q ∈ [-c/2, c/2)`, `dq/c`).

## Leaf statements (one per real-kernel fact)

* `SolenoidalConj` : the exact solenoidal subspace `PartIIa.solenoidalHC ε c` (the range of the
  conjugated Cartesian Leray projection `P_ε`, 1675-1676) is conjugation invariant: it is the
  orthogonal complement of the span of the complexified *real* gradients `(D_εΦ, ∂_ηΦ)`.
* `LiftVecConj` : the meridional lift `J_ε = B0223.liftVec` (real frame `e_r, e_z`, real weight)
  commutes with conjugation.
* `OuterSConj` : the outer Ornstein-Uhlenbeck semigroup `S_ε(t)` (`B0223.outerS`, real Gaussian
  kernel, `S_formula`) commutes with conjugation.
* `T0Conj` : the flat cylinder semigroup `T_0(t)` (`B0224.T0`, real plane heat kernel,
  `T0_apply_ae`) commutes with conjugation.
* `Masked.CellPtH c`, `Masked.CellPtInvH c` : the change-of-variables identities of the recentring
  `cellPt c : (0, c] → [-c/2, c/2)` and its inverse `Masked.cellPtInv c` between `s^{-3/2} ds dq dη`
  (`B0220.measureH c`) and `s^{-3/2} ds dq/c dη` (`Axi.ageμ c (-3/2)`).

## Derived (proved here)

`pepsC_conj`, `physRes_conj`, `repsVec_conj`, `teps_conj`, `r0_conj`, `t0flat_conj`; the real
form `bodyForm = Re ∘ R' ∘ (merC ∘ · ∘ cellPt)` of a complex body operator `R'` and
`isBodyTransport_bodyForm` (`IsBodyTransport`, `NearInst.lean`); `bodyRealForms_of`; and
`tepsReal_of` (`Masked.TepsReal` from the leaves).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile cell)

/-- Componentwise conjugation as a real-linear isometric equivalence (to commute it with Bochner
integrals, `LinearIsometryEquiv.integral_comp_comm`, without integrability). -/
def conjVR (n : ℕ) : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun := conjV n
  invFun := conjV n
  map_add' v w := map_add (conjV n) v w
  map_smul' r v := by
    ext i
    simp
  left_inv := conjV_conjV n
  right_inv := conjV_conjV n
  norm_map' v := norm_conjVLin n v

theorem conjVR_apply (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) : conjVR n v = conjV n v := rfl

/-! ## Leaf statements -/

/-- **The exact solenoidal subspace is conjugation invariant** (source 1675-1676: `P_ε` is the
conjugated Cartesian Leray projection, a real operator).  `PartIIa.solenoidalHC ε c` is the
orthogonal complement of the span of the complexified real gradients `(D_εΦ, ∂_ηΦ)`, `Φ` a real
profile test (`PartIIa.cgrad`), each fixed by conjugation; so the conjugate of an element is again
orthogonal to all of them. -/
def SolenoidalConj : Prop :=
  ∀ (ε c : ℝ) (g : HSpace c MeridC), g ∈ UnforcedLeray.Short.PartIIa.solenoidalHC ε c →
    cjLp (measureH c) 2 g ∈ UnforcedLeray.Short.PartIIa.solenoidalHC ε c

/-- **The meridional lift is real** (source 1638-1646; `B0223.coeFn_liftVec`:
`J_ε b = (√(2π)ε)⁻¹ a (b_r e_r + b_z e_z)` with the real frame `frameC` and real weight `liftA`):
`J_ε \bar b = \overline{J_ε b}`. -/
def LiftVecConj : Prop :=
  ∀ (P ε c : ℝ) [Fact (0 < P)] (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (b : HSpace c MeridC),
    liftVec hε hc hP (cjLp (measureH c) 2 b) =
      cjLp (volume : Measure (PSpace P)) 3 (liftVec hε hc hP b)

/-- **The outer semigroup is real** (source 1675-1677, the free Cartesian evolution of `A_ε`;
`B0223.S_formula`: `S_ε(t)F(x, τ) = e^{t/2}[e^{νε²(e^t-1)Δ}F(·, τ-t)](e^{t/2}x)`, a real Gaussian
average): `S_ε(t)\bar F = \overline{S_ε(t)F}` for `t > 0`. -/
def OuterSConj : Prop :=
  ∀ (P ν ε : ℝ) [Fact (0 < P)] (hν : 0 < ν) (t : ℝ), 0 < t → ∀ F : X SpaceC P,
    (outerS (E := SpaceC) (P := P) hν ε).T t (cjLp (volume : Measure (PSpace P)) 3 F) =
      cjLp (volume : Measure (PSpace P)) 3 ((outerS (E := SpaceC) (P := P) hν ε).T t F)

/-- **The flat cylinder semigroup is real** (source 1655-1656, 1686-1689, the flat equation
`(∂_s + μ/s - νΔ)b = ⋯`; `B0224.T0_apply_ae`: `T_0(t)f(s) = e^{νs(1-e^{-t})Δ_{q,η}} f(se^{-t})`, a
real plane heat average): `T_0(t)\bar f = \overline{T_0(t)f}`. -/
def T0Conj : Prop :=
  ∀ (c ν t : ℝ) (hc : 0 < c) (f : HSpace c MeridC),
    UnforcedLeray.B0224.T0 hc ν t (cjLp (measureH c) 2 f) =
      cjLp (measureH c) 2 (UnforcedLeray.B0224.T0 hc ν t f)

/-! ## Derived commutations -/

/-- `P_ε \bar f = \overline{P_ε f}`. -/
theorem pepsC_conj (hS : SolenoidalConj) (ε c : ℝ) (f : HSpace c MeridC) :
    UnforcedLeray.Short.PartIIa.PepsC ε c (cjLp (measureH c) 2 f) =
      cjLp (measureH c) 2 (UnforcedLeray.Short.PartIIa.PepsC ε c f) :=
  conjComm_starProjection (isConj_cjLp _ 2) _ (hS ε c) f

/-- `R(μ) = ∫_0^∞ e^{-μt}S_ε(t) dt` commutes with conjugation for real `μ > -1/4`. -/
theorem physRes_conj (hO : OuterSConj) {P ν ε : ℝ} [Fact (0 < P)] (hν : 0 < ν) {μ : ℝ}
    (hμ : 0 < μ + 1 / 4) (F : X SpaceC P) :
    physRes (E := SpaceC) (P := P) hν ε (μ : ℂ) (cjLp (volume : Measure (PSpace P)) 3 F) =
      cjLp (volume : Measure (PSpace P)) 3 (physRes (E := SpaceC) (P := P) hν ε (μ : ℂ) F) := by
  have hω : (outerS (E := SpaceC) (P := P) hν ε).ω < μ := by
    have := omega_lt (E := SpaceC) (P := P) (μ := (μ : ℂ)) (by simpa using hμ) hν ε
    simpa using this
  exact conjComm_laplace (outerS hν ε) (cjLp _ 3) (fun t ht x => hO P ν ε hν t ht x) hω F

/-- `R_ε^{vec}(μ) = J_ε† R(μ) J_ε` commutes with conjugation for real `μ > -1/4`. -/
theorem repsVec_conj (hL : LiftVecConj) (hO : OuterSConj) {P ν ε c : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℝ} (hμ : 0 < μ + 1 / 4)
    (b : HSpace c MeridC) :
    RepsVec hν hε hc hP (μ : ℂ) (cjLp (measureH c) 2 b) =
      cjLp (measureH c) 2 (RepsVec hν hε hc hP (μ : ℂ) b) := by
  have h1 : ∀ x : HSpace c MeridC, (liftVec hε hc hP).toContinuousLinearMap
      (cjLp (measureH c) 2 x) =
        cjLp (volume : Measure (PSpace P)) 3 ((liftVec hε hc hP).toContinuousLinearMap x) :=
    fun x => hL P ε c hε hc hP x
  unfold RepsVec
  rw [compress_apply, compress_apply]
  rw [show (liftVec hε hc hP) (cjLp (measureH c) 2 b) =
      cjLp (volume : Measure (PSpace P)) 3 ((liftVec hε hc hP) b) from hL P ε c hε hc hP b,
    physRes_conj hO hν hμ]
  exact conjComm_adjoint (isConj_cjLp _ 2) (isConj_cjLp _ 3) _ h1 _

/-- `T_ε = R_ε^{vec}(μ)P_ε` commutes with conjugation for real `μ > -1/4` (source 1675-1677). -/
theorem teps_conj (hS : SolenoidalConj) (hL : LiftVecConj) (hO : OuterSConj) {P ν ε c : ℝ}
    [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℝ}
    (hμ : 0 < μ + 1 / 4) (f : HSpace c MeridC) :
    UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ) (cjLp (measureH c) 2 f) =
      cjLp (measureH c) 2 (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ) f) := by
  simp only [UnforcedLeray.Short.PartIIa.Teps, ContinuousLinearMap.comp_apply]
  rw [pepsC_conj hS, repsVec_conj hL hO hν hε hc hP hμ]

/-- `R_0(μ) = ∫_0^∞ e^{-μt}T_0(t) dt` commutes with conjugation for real `μ > -1/4`. -/
theorem r0_conj (hT : T0Conj) {c : ℝ} (hc : 0 < c) (ν : ℝ) {μ : ℝ} (hμ : 0 < μ + 1 / 4)
    (f : HSpace c MeridC) :
    UnforcedLeray.B0225.R0 hc ν (μ : ℂ) (cjLp (measureH c) 2 f) =
      cjLp (measureH c) 2 (UnforcedLeray.B0225.R0 hc ν (μ : ℂ) f) := by
  have hμ' : 0 < (μ : ℂ).re + 1 / 4 := by simpa using hμ
  rw [UnforcedLeray.B0225.R0_apply hc ν hμ', UnforcedLeray.B0225.R0_apply hc ν hμ']
  have h1 := cj_setIntegral_exp_smul (cjLp (measureH c) 2)
    (fun t => UnforcedLeray.B0224.T0 hc ν t f) μ (UnforcedLeray.B0225.integrableOn_lapT0 hc ν hμ' f)
  have h2 : ∫ t in Ioi (0 : ℝ), Complex.exp (-((μ : ℂ) * t)) •
        UnforcedLeray.B0224.T0 hc ν t (cjLp (measureH c) 2 f) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-((μ : ℂ) * t)) •
        cjLp (measureH c) 2 (UnforcedLeray.B0224.T0 hc ν t f) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [hT c ν t hc f]
  exact h2.trans h1.symm

/-- `T_0 = R_0(μ)P_0` commutes with conjugation for real `μ > -1/4` (source 1676). -/
theorem t0flat_conj (hS : SolenoidalConj) (hT : T0Conj) {c : ℝ} (hc : 0 < c) (ν : ℝ) {μ : ℝ}
    (hμ : 0 < μ + 1 / 4) (f : HSpace c MeridC) :
    UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ) (cjLp (measureH c) 2 f) =
      cjLp (measureH c) 2 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ) f) := by
  simp only [UnforcedLeray.Short.PartIIa.T0flat, ContinuousLinearMap.comp_apply]
  rw [pepsC_conj hS, r0_conj hT hc ν hμ]

/-! ## The transports -/

/-- `merC` as a real-linear map `Merid → MeridC`. -/
def merCLin : Merid →ₗ[ℝ] MeridC where
  toFun := merC
  map_add' a b := by
    ext i
    simp [merC]
  map_smul' r a := by
    ext i
    simp [merC]

/-- `merC`, continuous. -/
def merCL : Merid →L[ℝ] MeridC := LinearMap.toContinuousLinearMap merCLin

/-- The real part `MeridC → Merid`. -/
def merReLin : MeridC →ₗ[ℝ] Merid where
  toFun g := WithLp.toLp 2 fun i => (g i).re
  map_add' g g' := by
    ext i
    simp
  map_smul' a g := by
    ext i
    simp

/-- The real part, continuous. -/
def merReL : MeridC →L[ℝ] Merid := LinearMap.toContinuousLinearMap merReLin

theorem merC_merReL {g : MeridC} (h : conjV 2 g = g) : merC (merReL g) = g := by
  ext i
  have hi : conj (g i) = g i := by
    have := congrArg (fun v : MeridC => v i) h
    simpa using this
  apply Complex.ext
  · simp [merC, merReL, merReLin]
  · have him : (g i).im = 0 := by
      have := congrArg Complex.im hi
      simp at this
      linarith
    simp [merC, merReL, merReLin, him]

theorem conjV_merC (b : Merid) : conjV 2 (merC b) = merC b := by
  ext i
  simp [merC]

theorem measurable_cellPt' (c : ℝ) : Measurable (cellPt c) := by
  unfold cellPt
  refine measurable_fst.prodMk (Measurable.prodMk ?_ (measurable_snd.comp measurable_snd))
  refine Measurable.ite ?_ (measurable_fst.comp measurable_snd)
    ((measurable_fst.comp measurable_snd).sub_const c)
  exact measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const

theorem ae_mem_cell (c : ℝ) : ∀ᵐ p ∂measureH c, p ∈ cell c := by
  have hm : MeasurableSet (cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hm)

/-- `f ↦ merC ∘ f ∘ cellPt : Hsp c → HSpace c MeridC`. -/
def cplxH (c : ℝ) (h : Masked.CellPtH c) : Hsp c →L[ℝ] HSpace c MeridC :=
  (Lp.compMeasurePreservingₗᵢ ℝ (cellPt c)
      ((measurable_cellPt' c).measurePreserving (measureH c))).toContinuousLinearMap.comp
    ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le).comp (merCL.compLpL 2 (ageμ c (-3 / 2))))

/-- `g ↦ Re g ∘ cellPtInv : HSpace c MeridC → Hsp c`. -/
def reV (c : ℝ) (h : Masked.CellPtInvH c) : HSpace c MeridC →L[ℝ] Hsp c :=
  (merReL.compLpL 2 (ageμ c (-3 / 2))).comp
    ((Lp.compMeasurePreservingₗᵢ ℝ (Masked.cellPtInv c)
        ((Masked.measurable_cellPtInv c).measurePreserving (ageμ c (-3 / 2)))).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le))

theorem cplxH_ae (c : ℝ) (h : Masked.CellPtH c) (f : Hsp c) :
    (cplxH c h f : Profile → MeridC) =ᵐ[measureH c]
      fun p => merC ((f : Chart → Merid) (cellPt c p)) := by
  have h' : Measure.map (cellPt c) (measureH c) ≤ ENNReal.ofReal c • ageμ c (-3 / 2) := h.le
  have hmp := (measurable_cellPt' c).measurePreserving (measureH c)
  have hac := Measure.absolutelyContinuous_of_le_smul h'
  have e : cplxH c h f = Lp.compMeasurePreserving (cellPt c) hmp
      ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h') (merCL.compLp f)) := rfl
  have h1 := Lp.coeFn_compMeasurePreserving
    ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h') (merCL.compLp f)) hmp
  have h2 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h' (merCL.compLp f)
  have h3 : ∀ᵐ x ∂Measure.map (cellPt c) (measureH c),
      (merCL.compLp f : Chart → MeridC) x = merCL ((f : Chart → Merid) x) :=
    hac.ae_le (merCL.coeFn_compLp f)
  have h4 := ae_of_ae_map hmp.aemeasurable (h2.and h3)
  rw [e]
  filter_upwards [h1, h4] with p hp1 hp4
  rw [hp1, Function.comp_apply, hp4.1, hp4.2]
  rfl

theorem reV_ae (c : ℝ) (h : Masked.CellPtInvH c) (g : HSpace c MeridC) :
    (reV c h g : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] fun x =>
      merReL ((g : Profile → MeridC) (Masked.cellPtInv c x)) := by
  have h' : Measure.map (Masked.cellPtInv c) (ageμ c (-3 / 2)) ≤ ENNReal.ofReal c⁻¹ • measureH c := h.le
  have hmp := (Masked.measurable_cellPtInv c).measurePreserving (ageμ c (-3 / 2))
  have e : reV c h g = merReL.compLp (Lp.compMeasurePreserving (Masked.cellPtInv c) hmp
      ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h') g)) := rfl
  have h0 := merReL.coeFn_compLp (Lp.compMeasurePreserving (Masked.cellPtInv c) hmp
      ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h') g))
  have h1 := Lp.coeFn_compMeasurePreserving ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h') g) hmp
  have h2 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h' g
  have h4 := ae_of_ae_map hmp.aemeasurable h2
  rw [e]
  filter_upwards [h0, h1, h4] with x hx0 hx1 hx4
  rw [hx0, hx1, Function.comp_apply, hx4]

/-- The real form `Re ∘ R' ∘ (merC ∘ · ∘ cellPt) : Hsp c → Hsp c` of a complex body operator. -/
def bodyForm (c : ℝ) (hH : Masked.CellPtH c) (hHi : Masked.CellPtInvH c)
    (R' : HSpace c MeridC →L[ℂ] HSpace c MeridC) : Hsp c →L[ℝ] Hsp c :=
  (reV c hHi).comp ((R'.restrictScalars ℝ).comp (cplxH c hH))

/-- **The real form is a transport** (source 1641-1646, 2676-2683): if `R'` commutes with
conjugation, `bodyForm R'` satisfies `IsBodyTransport`. -/
theorem isBodyTransport_bodyForm {c : ℝ} (hH : Masked.CellPtH c) (hHi : Masked.CellPtInvH c)
    (R' : HSpace c MeridC →L[ℂ] HSpace c MeridC)
    (hR : ∀ g : HSpace c MeridC, R' (cjLp (measureH c) 2 g) = cjLp (measureH c) 2 (R' g)) :
    IsBodyTransport (bodyForm c hH hHi R') R' := by
  intro f f' hf'
  have hin : f' = cplxH c hH f := by
    apply Lp.ext
    filter_upwards [hf', cplxH_ae c hH f] with p h1 h2
    rw [h1, h2]
  -- the input is real
  have hreal : cjLp (measureH c) 2 f' = f' := by
    apply Lp.ext
    filter_upwards [coeFn_cjLp (measureH c) 2 f', hf'] with p h1 h2
    rw [h1, h2, conjV_merC]
  -- so is the output
  have hout : cjLp (measureH c) 2 (R' f') = R' f' := by rw [← hR, hreal]
  have hpt : ∀ᵐ p ∂measureH c, conjV 2 ((R' f' : Profile → MeridC) p) =
      (R' f' : Profile → MeridC) p := by
    filter_upwards [coeFn_cjLp (measureH c) 2 (R' f')] with p hp
    rw [← hp, hout]
  have hmp := (measurable_cellPt' c).measurePreserving (measureH c)
  have hH' : Measure.map (cellPt c) (measureH c) ≤ ENNReal.ofReal c • ageμ c (-3 / 2) := hH.le
  have hac := Measure.absolutelyContinuous_of_le_smul hH'
  have hre := ae_of_ae_map hmp.aemeasurable (hac.ae_le (reV_ae c hHi (R' f')))
  filter_upwards [hpt, hre, ae_mem_cell c] with p hp1 hp2 hp3
  have hS : bodyForm c hH hHi R' f = reV c hHi (R' f') := by
    rw [hin]; rfl
  rw [hS, hp2, Masked.cellPtInv_cellPt hp3.2.1.1 hp3.2.1.2, merC_merReL hp1]

/-! ## Real fields and `Masked.TepsReal` -/

theorem isRealH_iff {c : ℝ} (g : HSpace c MeridC) :
    Masked.IsRealH c g ↔ cjLp (measureH c) 2 g = g := by
  constructor
  · intro h
    apply Lp.ext
    filter_upwards [coeFn_cjLp (measureH c) 2 g, h] with p h1 h2
    rw [h1]
    ext i
    apply Complex.ext
    · simp
    · simp [h2 i]
  · intro h
    filter_upwards [coeFn_cjLp (measureH c) 2 g] with p hp i
    have h1 := congrArg (fun v : MeridC => (v i).im) hp
    simp only [h, conjV_apply, Complex.conj_im] at h1
    linarith

/-- **`T_ε` preserves real fields** (`Masked.TepsReal`, source 1675-1677) from the three leaves. -/
theorem tepsReal_of (hS : SolenoidalConj) (hL : LiftVecConj) (hO : OuterSConj) :
    Masked.TepsReal := by
  intro ν ε c P _ hν hε hc hP μ hμ g hg
  rw [isRealH_iff] at hg ⊢
  rw [← teps_conj hS hL hO hν hε hc hP (by linarith) g, hg]

/-! ## Assembly -/

/-- **`BodyRealForms`** (source 1675-1677): the body inverses `T_ε`, `T_0` have real forms at every
level and every real `μ ∈ K ⋐ (0, 1/4)`. -/
theorem bodyRealForms_of (hS : SolenoidalConj) (hL : LiftVecConj) (hO : OuterSConj)
    (hT : T0Conj) (hH : ∀ c : ℝ, 0 < c → Masked.CellPtH c) (hHi : ∀ c : ℝ, 0 < c → Masked.CellPtInvH c) :
    BodyRealForms := by
  intro Kset _ hKsub dm dp _
  refine ⟨1, one_pos, fun p d _ _ μ hμ => ?_⟩
  have hμ' : 0 < μ + 1 / 4 := by
    have := (hKsub hμ).1
    linarith
  exact ⟨⟨_, isBodyTransport_bodyForm (hH p.c p.c_pos) (hHi p.c p.c_pos) _
      (fun g => teps_conj (P := p.period) hS hL hO p.ν_pos p.ε_pos p.c_pos rfl hμ' g)⟩,
    ⟨_, isBodyTransport_bodyForm (hH p.c p.c_pos) (hHi p.c p.c_pos) _
      (fun g => t0flat_conj hS hT p.c_pos p.ν hμ' g)⟩⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Body
