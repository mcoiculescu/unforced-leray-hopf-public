import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7

/-!
# Part II-b, task `PartII-b:G4/3/7/2` (`ColQPeriodic`)

Source of record: `the November 2 reference manuscript`, lines 2347-2348, 2360-2374.
The column `colEps p i` is built from the inlet profile (`c`-periodic in `q` everywhere,
`inletProfile_periodic`) and the raw profile `rawProf` (`c`-periodic in `q` for `s > 0`,
`rawProfile_periodic`). Chart derivatives of `c`-periodic functions are `c`-periodic, so the
column is `c`-periodic in `q` at every point of `s > 0`, and `colEpsR` vanishes for `s ≤ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

private theorem colQ_qShift_eq (c : ℝ) (x : Coord) : qShift c x = x + (0, (c, 0)) := by
  simp [qShift, Prod.ext_iff]

/-- Translation invariance of a derivative: `F` `c`-periodic in `q` on an open set `U` gives
`fderiv F` `c`-periodic in `q` on `U`. -/
private theorem colQ_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    fderiv ℝ F (qShift c x) = fderiv ℝ F x := by
  have hev : (fun y => F (qShift c y)) =ᶠ[𝓝 x] F := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hF y hy
  have hfun : (fun y => F (qShift c y)) = fun y => F (y + (0, (c, 0))) := by
    funext y
    rw [colQ_qShift_eq]
  have h1 : fderiv ℝ (fun y => F (qShift c y)) x = fderiv ℝ F x := hev.fderiv_eq
  rw [hfun, fderiv_comp_add_right] at h1
  rw [colQ_qShift_eq]
  exact h1

private theorem colQ_dS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    Axi.dS F (qShift c x) = Axi.dS F x := by
  unfold Axi.dS
  rw [colQ_fderiv hU hF hx]

private theorem colQ_dQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    Axi.dQ F (qShift c x) = Axi.dQ F x := by
  unfold Axi.dQ
  rw [colQ_fderiv hU hF hx]

private theorem colQ_dEta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    Axi.dEta F (qShift c x) = Axi.dEta F x := by
  unfold Axi.dEta
  rw [colQ_fderiv hU hF hx]

private theorem colQ_kAge {F : Coord → Axi.Merid} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    kAge F (qShift c x) = kAge F x := by
  unfold kAge
  rw [colQ_dS hU hF hx, colQ_dEta hU hF hx]
  rfl

private theorem colQ_qEps {ε c : ℝ} {F : Coord → Axi.Merid} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    qEps ε F (qShift c x) = qEps ε F x := by
  unfold qEps
  rw [colQ_dQ hU hF hx, colQ_kAge hU hF hx, hF x hx]

private theorem colQ_vecDiffEps {ε c : ℝ} {F : Coord → Axi.Merid} {U : Set Coord}
    (hU : IsOpen U) (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    vecDiffEps ε F (qShift c x) = vecDiffEps ε F x := by
  have hG1 : ∀ y ∈ U, Axi.dQ F (qShift c y) = Axi.dQ F y := fun y hy => colQ_dQ hU hF hy
  have hG2 : ∀ y ∈ U, Axi.dQ (Axi.dQ F) (qShift c y) = Axi.dQ (Axi.dQ F) y :=
    fun y hy => colQ_dQ hU hG1 hy
  have hE1 : ∀ y ∈ U, Axi.dEta F (qShift c y) = Axi.dEta F y := fun y hy => colQ_dEta hU hF hy
  have hE2 : ∀ y ∈ U, Axi.dEta (Axi.dEta F) (qShift c y) = Axi.dEta (Axi.dEta F) y :=
    fun y hy => colQ_dEta hU hE1 hy
  have hK1 : ∀ y ∈ U, kAge (Axi.dQ F) (qShift c y) = kAge (Axi.dQ F) y :=
    fun y hy => colQ_kAge hU hG1 hy
  have hS : ∀ y ∈ U, (fun z => kAge F z + F z) (qShift c y) = (fun z => kAge F z + F z) y := by
    intro y hy
    show kAge F (qShift c y) + F (qShift c y) = kAge F y + F y
    rw [colQ_kAge hU hF hy, hF y hy]
  have hK2 : ∀ y ∈ U, kAge (fun z => kAge F z + F z) (qShift c y) =
      kAge (fun z => kAge F z + F z) y :=
    fun y hy => colQ_kAge hU hS hy
  unfold vecDiffEps
  rw [hG2 x hx, hE2 x hx, hK1 x hx, hG1 x hx, hK2 x hx, colQ_kAge hU hF hx, hF x hx]

private theorem colQ_bEps {c : ℝ} {p : Params} {F : Coord → Axi.Merid} {U : Set Coord}
    (hU : IsOpen U) (hF : ∀ y ∈ U, F (qShift c y) = F y)
    (hR : ∀ y ∈ U, rawProf p (qShift c y) = rawProf p y) {x : Coord} (hx : x ∈ U) :
    bEps p F (qShift c x) = bEps p F x := by
  have hRq : ∀ y ∈ U, rawProf p (qShift c y) = rawProf p y := hR
  unfold bEps
  rw [hRq x hx, colQ_qEps hU hF hx, colQ_qEps hU hRq hx, colQ_dEta hU hF hx,
    colQ_dEta hU hRq hx, hF x hx]

/-- `c`-periodicity of the raw profile on `s > 0` (`rawProfile_periodic`). -/
private theorem colQ_rawProf_per (p : Params) :
    ∀ y ∈ {x : Coord | 0 < x.1}, rawProf p (qShift p.c y) = rawProf p y := by
  intro y hy
  unfold rawProf
  exact UnforcedLeray.Cons.C03.rawProfile_periodic p.train hy y.2.1 y.2.2

/-- The inlet profile is `c`-periodic in `q` everywhere (`inletProfile_periodic`). -/
private theorem colQ_inlet_per (p : Params) (i : Fin 2) :
    ∀ y ∈ (univ : Set Coord), p.inletProfile i (qShift p.c y) = p.inletProfile i y := by
  intro y _
  exact p.inletProfile_periodic i y.1 y.2.1 y.2.2

private theorem colQ_colDiffR {p : Params} {i : Fin 2} {x : Coord}
    (hx : 0 < x.1) :
    colDiffR p i (qShift p.c x) = colDiffR p i x := by
  have hU : IsOpen {y : Coord | 0 < y.1} := isOpen_lt continuous_const continuous_fst
  have hxU : x ∈ {y : Coord | 0 < y.1} := hx
  have hF : ∀ y ∈ {y : Coord | 0 < y.1}, p.inletProfile i (qShift p.c y) = p.inletProfile i y :=
    fun y hy => colQ_inlet_per p i y trivial
  have hs : (qShift p.c x).1 = x.1 := rfl
  unfold colDiffR
  rw [hs, colQ_dS hU hF hxU, colQ_vecDiffEps hU hF hxU]

private theorem colQ_colIntR {p : Params} {i : Fin 2} {x : Coord}
    (hx : 0 < x.1) :
    colIntR p i (qShift p.c x) = colIntR p i x := by
  have hU : IsOpen {y : Coord | 0 < y.1} := isOpen_lt continuous_const continuous_fst
  have hxU : x ∈ {y : Coord | 0 < y.1} := hx
  have hF : ∀ y ∈ {y : Coord | 0 < y.1}, p.inletProfile i (qShift p.c y) = p.inletProfile i y :=
    fun y hy => colQ_inlet_per p i y trivial
  have hs : (qShift p.c x).1 = x.1 := rfl
  unfold colIntR
  rw [hs, colQ_bEps hU hF (colQ_rawProf_per p) hxU]

/-- **`ColQPeriodic`** (SP 2347-2348, 2360-2374): the column is `c`-periodic in `q`. -/
theorem colQPeriodic : UnforcedLeray.Short.IIb.ColQPeriodic := by
  intro Sig lam q hSig hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d _ i
  unfold QPeriodic
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hcol : colEpsR p i (qShift p.c x) = colEpsR p i x := by
    have hs : (qShift p.c x).1 = x.1 := rfl
    unfold colEpsR
    rw [hs]
    split_ifs with hx
    · rw [colQ_colDiffR hx, colQ_colIntR hx]
    · rfl
  simp only [colEps, cplx, hcol]

end UnforcedLeray.Short.IIb
