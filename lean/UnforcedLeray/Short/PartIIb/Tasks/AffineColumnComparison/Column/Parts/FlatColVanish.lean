import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8

/-!
# Part II-b, task `PartII-b:G4/3/8/3` (`FlatColVanish`)

Source of record: `the November 2 reference manuscript` (SP), lines 2360-2366.
The inlet component `e_0 = (-∂_ηφ) m0 + (∂_qφ) m1` is built from the age cutoff `φ = cutStream i`,
which vanishes on the open set `s > H/2`. Hence `e_0`, and all its chart derivatives used in
`flatColumn`, vanish on that open set, so the flat column vanishes there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- A function vanishing on an open set `U` of the chart space has vanishing first chart
derivatives (`dS`, `dQ`, `dEta`) at every point of `U`. -/
theorem chart_deriv_zero_of_zero_on_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {U : Set Coord} (hU : IsOpen U) (hF : ∀ y ∈ U, F y = 0) :
    ∀ y ∈ U, Axi.dS F y = 0 ∧ Axi.dQ F y = 0 ∧ Axi.dEta F y = 0 := by
  intro y hy
  have hev : F =ᶠ[𝓝 y] fun _ => (0 : E) :=
    Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hF z hz)
  have h : fderiv ℝ F y = fderiv ℝ (fun _ => (0 : E)) y := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
  refine ⟨?_, ?_, ?_⟩ <;> simp [Axi.dS, Axi.dQ, Axi.dEta, h]

/-- **The flat column vanishes beyond the cutoff** (SP 2360-2366). -/
theorem flatColVanish : FlatColVanish := by
  intro Sig lam q hSig hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg i x hx
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  -- the open set `s > H/2`
  have hUo : IsOpen {y : Coord | p.H / 2 < y.1} := isOpen_lt continuous_const continuous_fst
  -- the age cutoff `cutStream i` vanishes on it
  have hcutU : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, p.cutStream i y = 0 := by
    intro y hy
    have hy' : p.H / 2 < y.1 := hy
    unfold Params.cutStream
    simp [ageCutoff_eq_zero hH hy'.le]
  have hcutD := fun y hy => chart_deriv_zero_of_zero_on_open hUo hcutU y hy
  -- hence `e_0` vanishes on it
  have he0U : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, inletE0 p i y = 0 := by
    intro y hy
    obtain ⟨-, h1, h2⟩ := hcutD y hy
    simp [inletE0, h1, h2]
  -- and so do its chart derivatives
  have hdSe0U : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, Axi.dS (inletE0 p i) y = 0 :=
    fun y hy => (chart_deriv_zero_of_zero_on_open hUo he0U y hy).1
  have hdQe0U : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, Axi.dQ (inletE0 p i) y = 0 :=
    fun y hy => (chart_deriv_zero_of_zero_on_open hUo he0U y hy).2.1
  have hdEe0U : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, Axi.dEta (inletE0 p i) y = 0 :=
    fun y hy => (chart_deriv_zero_of_zero_on_open hUo he0U y hy).2.2
  have hdQdQU : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, Axi.dQ (Axi.dQ (inletE0 p i)) y = 0 :=
    fun y hy => (chart_deriv_zero_of_zero_on_open hUo hdQe0U y hy).2.1
  have hdEdEU : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, Axi.dEta (Axi.dEta (inletE0 p i)) y = 0 :=
    fun y hy => (chart_deriv_zero_of_zero_on_open hUo hdEe0U y hy).2.2
  have hx' : x ∈ {y : Coord | p.H / 2 < y.1} := hx
  have z0 : inletE0 p i x = 0 := he0U x hx'
  have zS : Axi.dS (inletE0 p i) x = 0 := hdSe0U x hx'
  have zQ : Axi.dQ (inletE0 p i) x = 0 := hdQe0U x hx'
  have zE : Axi.dEta (inletE0 p i) x = 0 := hdEe0U x hx'
  have zQQ : Axi.dQ (Axi.dQ (inletE0 p i)) x = 0 := hdQdQU x hx'
  have zEE : Axi.dEta (Axi.dEta (inletE0 p i)) x = 0 := hdEdEU x hx'
  unfold flatColumn
  ext j
  simp [cplx, flatK, z0, zS, zQ, zE, zQQ, zEE]

end UnforcedLeray.Short.IIb

end
