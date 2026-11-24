import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_4.Meas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_ax
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Fderiv
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Lap

/-!
# Pointwise calculus of the entrance source (helpers of `PartIII-b:C/rep/8/2/pres/3/2/6`)

Source `the November 2 reference manuscript`
2346-2347 (the complete equation source of `E_εα = V - U_raw`), 2388-2392, 4139-4141 (`D₀`),
5277-5279; 1205-1225, 2031 (periodicity and axisymmetry of the raw lift and the inlets).

For a general split `V = r + E` (`r` jointly `C²` off the axis, `E` jointly `C^∞`):

* `esG_E`, `esG_eq_of`: the source is `D₀E + (V·∇V - r·∇r)`, and off the axis
  `= [D₀E + E·∇r + r·∇E] + E·∇E` (linear plus quadratic inlet source);
* `esG_continuousOn`: it is continuous off the axis;
* `esG_add_period`: it is `P`-periodic when `V`, `r` are;
* `esG_norm_merPt`: its norm is invariant under `merPt` when `E` and a ring lift `r'` agreeing
  with `r` off the axis are axisymmetric without swirl.

Level facts: `raw_add_period`, `inlet_add_period` (`P = 2εc`, `chart_add_period`),
`axi_Nv` (ring lifts are axisymmetric without swirl).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.ES326

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The entrance source for a general pair `(V, r)` (`entSrc` with `V = L.V`, `r = U_raw`). -/
def esG (ν : ℝ) (V r : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  physDmu ν 0 (fun t y' => V t y' - r t y') τ y +
    (fderiv ℝ (V τ) y (V τ y) - fderiv ℝ (r τ) y (r τ y))

theorem entSrc_eq (Pl : PlanarData) (L : ReturnLevel) :
    entSrc Pl L = esG L.ν L.V (rawU Pl L) := rfl

/-! ## Time slices and continuity of `D_μ` -/

theorem deriv_tslice {O : Set (ℝ × Space)} (hO : IsOpen O) {F : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 1 F O) {τ : ℝ} {y : Space} (hx : (τ, y) ∈ O) :
    deriv (fun t => F (t, y)) τ = fderiv ℝ F (τ, y) ((1 : ℝ), (0 : Space)) := by
  have hd : DifferentiableAt ℝ F (τ, y) :=
    (hF.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)
  have hc : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ y)
  exact (hd.hasFDerivAt.comp_hasDerivAt τ hc).deriv

theorem dmuT_continuousOn {O : Set (ℝ × Space)} (hO : IsOpen O) {X : ℝ → Space → Space}
    (hX : ContDiffOn ℝ 2 (fun x : ℝ × Space => X x.1 x.2) O) :
    ContinuousOn (fun x : ℝ × Space => deriv (fun t => X t x.2) x.1) O := by
  have hc : ContinuousOn (fun x => fderiv ℝ (fun x : ℝ × Space => X x.1 x.2) x
      ((1 : ℝ), (0 : Space))) O :=
    (hX.continuousOn_fderiv_of_isOpen hO (by norm_num)).clm_apply continuousOn_const
  refine hc.congr fun x hx => ?_
  have hx' : (x.1, x.2) ∈ O := hx
  have h1 : ContDiffOn ℝ 1 (fun x : ℝ × Space => X x.1 x.2) O := hX.of_le (by norm_num)
  exact deriv_tslice hO h1 hx'

theorem dmuS_continuousOn {O : Set (ℝ × Space)} (hO : IsOpen O) {X : ℝ → Space → Space}
    (hX : ContDiffOn ℝ 2 (fun x : ℝ × Space => X x.1 x.2) O) :
    ContinuousOn (fun x : ℝ × Space => fderiv ℝ (X x.1) x.2 x.2) O :=
  (fderiv_slice_continuousOn hO hX).clm_apply continuousOn_snd

theorem dmuL_continuousOn {O : Set (ℝ × Space)} (hO : IsOpen O) {X : ℝ → Space → Space}
    (hX : ContDiffOn ℝ 2 (fun x : ℝ × Space => X x.1 x.2) O) :
    ContinuousOn (fun x : ℝ × Space => physLap (X x.1) x.2) O := by
  obtain ⟨-, -, h2⟩ := jet_continuousOn hO hX
  have e : (fun x : ℝ × Space => physLap (X x.1) x.2) =
      fun x => ∑ j : Fin 3, physPd2 (X x.1) j j x.2 := rfl
  rw [e]
  exact continuousOn_finsetSum _ fun j _ => h2 j j

/-- `(τ, y) ↦ D_μX(τ, y)` is continuous on an open set where `X` is jointly `C²`. -/
theorem physDmu_continuousOn {O : Set (ℝ × Space)} (hO : IsOpen O) {X : ℝ → Space → Space}
    (hX : ContDiffOn ℝ 2 (fun x : ℝ × Space => X x.1 x.2) O) (ν μ : ℝ) :
    ContinuousOn (fun x : ℝ × Space => physDmu ν μ X x.1 x.2) O := by
  have hT := dmuT_continuousOn hO hX
  have hS := dmuS_continuousOn hO hX
  have hL := dmuL_continuousOn hO hX
  have h0 : ContinuousOn (fun x : ℝ × Space => X x.1 x.2) O := hX.continuousOn
  have hall := ((hT.sub (hS.const_smul (1 / 2 : ℝ))).sub (hL.const_smul ν)).add
    (h0.const_smul (μ - 1 / 2))
  exact hall.congr fun x _ => rfl

/-! ## The split `V = r + E` -/

theorem esG_E {ν : ℝ} {V r E : ℝ → Space → Space} (hV : ∀ t y, V t y = r t y + E t y)
    (τ : ℝ) (y : Space) :
    esG ν V r τ y = physDmu ν 0 E τ y + (fderiv ℝ (V τ) y (V τ y) - fderiv ℝ (r τ) y (r τ y)) := by
  have hX : (fun t y' => V t y' - r t y') = E := by
    funext t y'
    rw [hV]
    exact add_sub_cancel_left _ _
  rw [esG, hX]

/-- **The split of the entrance source** (source 2388-2392, 5277-5279): off the axis (where `r` is
differentiable) the source is the linear inlet source plus the quadratic one. -/
theorem esG_eq_of {ν : ℝ} {V r E : ℝ → Space → Space} (hV : ∀ t y, V t y = r t y + E t y)
    {τ : ℝ} {y : Space} (hr : DifferentiableAt ℝ (r τ) y) (hE : DifferentiableAt ℝ (E τ) y) :
    esG ν V r τ y = (physDmu ν 0 E τ y + (fderiv ℝ (E τ) y (r τ y) + fderiv ℝ (r τ) y (E τ y))) +
      fderiv ℝ (E τ) y (E τ y) := by
  have hVτ : V τ = fun y' => r τ y' + E τ y' := funext (hV τ)
  have hD : fderiv ℝ (V τ) y = fderiv ℝ (r τ) y + fderiv ℝ (E τ) y := by
    rw [hVτ]
    exact fderiv_add hr hE
  rw [esG_E hV, hD, hV τ y]
  simp only [ContinuousLinearMap.add_apply, map_add]
  abel

theorem esG_continuousOn {ν : ℝ} {V r E : ℝ → Space → Space}
    (hV : ∀ t y, V t y = r t y + E t y)
    (hr : ContDiffOn ℝ 2 (fun x : ℝ × Space => r x.1 x.2) offAxis)
    (hE : ContDiffOn ℝ 2 (fun x : ℝ × Space => E x.1 x.2) offAxis) :
    ContinuousOn (fun x : ℝ × Space => esG ν V r x.1 x.2) offAxis := by
  have hVj : ContDiffOn ℝ 2 (fun x : ℝ × Space => V x.1 x.2) offAxis :=
    (hr.add hE).congr fun x _ => hV x.1 x.2
  have h1 := physDmu_continuousOn isOpen_offAxis hE ν 0
  have h2 : ContinuousOn (fun x : ℝ × Space => fderiv ℝ (V x.1) x.2 (V x.1 x.2)) offAxis :=
    (fderiv_slice_continuousOn isOpen_offAxis hVj).clm_apply hVj.continuousOn
  have h3 : ContinuousOn (fun x : ℝ × Space => fderiv ℝ (r x.1) x.2 (r x.1 x.2)) offAxis :=
    (fderiv_slice_continuousOn isOpen_offAxis hr).clm_apply hr.continuousOn
  refine (h1.add (h2.sub h3)).congr fun x _ => ?_
  exact esG_E hV x.1 x.2

theorem esG_add_period {ν P : ℝ} {V r : ℝ → Space → Space} (hV : Function.Periodic V P)
    (hr : Function.Periodic r P) (τ : ℝ) (y : Space) :
    esG ν V r (τ + P) y = esG ν V r τ y := by
  have hd : deriv (fun t => V t y - r t y) (τ + P) = deriv (fun t => V t y - r t y) τ := by
    rw [← deriv_comp_add_const]
    congr 1
    funext t
    simp only [hV t, hr t]
  simp only [esG, physDmu]
  rw [hd]
  simp only [hV τ, hr τ]

/-! ## Axisymmetry -/

theorem fderiv_equiv {f : Space → Space} (hf : AxiNoSwirlPt f) (g : Space ≃ₗᵢ[ℝ] Space)
    (hg : FixesAxis g) (y v : Space) : fderiv ℝ f (g y) (g v) = g (fderiv ℝ f y v) := by
  have hfun : (fun x => g (f (g.symm x))) = f := funext fun x => hf g hg x
  have key := axiDens_fderiv_conj g g f (g y)
  rw [hfun, g.symm_apply_apply] at key
  rw [key]
  simp

theorem esG_axi {ν : ℝ} {V r E : ℝ → Space → Space} (hV : ∀ t y, V t y = r t y + E t y)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => E x.1 x.2))
    (hEa : ∀ t, AxiNoSwirlPt (E t)) (hra : ∀ t, AxiNoSwirlPt (r t)) (τ : ℝ) :
    AxiNoSwirlPt (esG ν V r τ) := by
  have hVa : AxiNoSwirlPt (V τ) := by
    intro g hg x
    rw [hV τ, hV τ, map_add, hra τ g hg x, hEa τ g hg x]
  refine axi_of_gEqv fun g hg y => ?_
  have hD := dmu_gEqv fderivEqv_proved lapEqv_proved ν 0 E hE g
    (fun t => axi_gEqv (hEa t) hg) τ y
  have h1 : V τ (g y) = g (V τ y) := axi_gEqv hVa hg y
  have h2 : r τ (g y) = g (r τ y) := axi_gEqv (hra τ) hg y
  rw [esG_E hV, esG_E hV, hD, h1, h2, fderiv_equiv hVa g hg, fderiv_equiv (hra τ) g hg,
    map_add, map_sub]

/-- **Axisymmetry of the entrance source density**: if `r` agrees off the axis with a field `r'`
that is axisymmetric without swirl, and `E` is, then `‖esG‖` is invariant under `merPt`. -/
theorem esG_norm_merPt {ν : ℝ} {V r r' E : ℝ → Space → Space}
    (hV : ∀ t y, V t y = r t y + E t y)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => E x.1 x.2))
    (hEa : ∀ t, AxiNoSwirlPt (E t)) (hra : ∀ t, AxiNoSwirlPt (r' t))
    (hrr : ∀ t y, y ∉ axis → r t y = r' t y) (τ : ℝ) (y : Space) :
    ‖esG ν V r τ y‖ = ‖esG ν V r τ (merPt y)‖ := by
  set V' : ℝ → Space → Space := fun t y => r' t y + E t y with hV'def
  have hV' : ∀ t y, V' t y = r' t y + E t y := fun t y => rfl
  have hloc : ∀ x, x ∉ axis → esG ν V r τ x = esG ν V' r' τ x := by
    intro x hx
    have hn : {x' : Space | x' ∉ axis} ∈ 𝓝 x := isClosed_axis.isOpen_compl.mem_nhds hx
    have er : r τ =ᶠ[𝓝 x] r' τ := Filter.mem_of_superset hn fun x' hx' => hrr τ x' hx'
    have eV : V τ =ᶠ[𝓝 x] V' τ := Filter.mem_of_superset hn fun x' hx' => by
      show V τ x' = V' τ x'
      rw [hV, hrr τ x' hx']
    rw [esG_E hV, esG_E hV', er.fderiv_eq, eV.fderiv_eq, eV.eq_of_nhds, er.eq_of_nhds]
  by_cases hy : y ∈ axis
  · rw [pf4_merPt_of_mem_axis hy]
  · rw [hloc y hy, hloc (merPt y) (pf_merPt_not_mem_axis hy)]
    exact (axiDens_azimuth (esG_axi hV' hE hEa hra τ) y).1

/-! ## The level fields -/

/-- Ring lifts are axisymmetric without swirl, pointwise. -/
theorem axi_Nv (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) : AxiNoSwirlPt (Nv R b τ) := by
  intro g hg x
  rw [UnforcedLeray.Axi.Nv_eq_liftMer]
  exact liftMer_equivariant g _ hg x

theorem axi_E (p : UnforcedLeray.Cons.C03.Concrete.Params) (α : Fin 2 → ℝ) (t : ℝ) :
    AxiNoSwirlPt (fun y => ∑ i : Fin 2, α i • p.inlet i t y) := by
  intro g hg x
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun v => α i • v) (axi_Nv p.R (p.inletProfile i) t g hg x)

/-- `U_raw` is `P`-periodic, `P = 2εc` (source 1205-1225, `eq:m3-ring-lift`; on the axis by the
limit from off the axis). -/
theorem raw_add_period (p : UnforcedLeray.Cons.C03.Concrete.Params) (τ : ℝ) :
    p.raw (τ + p.period) = p.raw τ := by
  have hoff : ∀ y', y' ∉ axis →
      Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) (τ + p.period) y' =
        Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ y' :=
    fun y' hy' => UnforcedLeray.Cons.C03.Nv_add_period_of_not_mem_axis p.R_pos.ne' p.period_eq
      (fun s hs ξ η => UnforcedLeray.Cons.C03.rawProfile_periodic p.train hs ξ η) τ hy'
  funext y
  by_cases hy : y ∈ axis
  · simp only [UnforcedLeray.Cons.C03.Concrete.Params.raw, UnforcedLeray.Cons.C03.Concrete.axisExt,
      hy, ↓reduceIte]
    have hev : Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) (τ + p.period)
        =ᶠ[𝓝[axisᶜ] y] Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ :=
      eventually_nhdsWithin_of_forall fun y' hy' => hoff y' hy'
    unfold limUnder
    rw [Filter.map_congr hev]
  · rw [UnforcedLeray.Cons.C03.Concrete.Params.raw_eq_off_axis p _ y hy,
      UnforcedLeray.Cons.C03.Concrete.Params.raw_eq_off_axis p _ y hy]
    exact hoff y hy

/-- The inlet columns are `P`-periodic (source 2347-2369: `c`-periodic profiles). -/
theorem inlet_add_period (p : UnforcedLeray.Cons.C03.Concrete.Params) (i : Fin 2) (τ : ℝ) :
    p.inlet i (τ + p.period) = p.inlet i τ := by
  funext y
  rw [UnforcedLeray.Cons.C03.Concrete.Params.inlet, UnforcedLeray.Cons.C03.Concrete.Params.inlet,
    Nv, Nv, UnforcedLeray.Axi.chart_add_period p.R_pos.ne' p.period_eq, p.inletProfile_periodic]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.ES326
