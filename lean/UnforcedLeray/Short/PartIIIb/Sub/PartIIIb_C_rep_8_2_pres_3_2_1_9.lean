import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableSupport

/-!
# The linearity leaf `DmuChgLin` (`PartIII-b:C/rep/8/2/pres/3/2/1/9`)

Source of record: `the November 2 reference manuscript` (4140-4141: `D₀` is linear
and local; 1213-1225, 5200-5201, 5254-5257).  Off the axis, `dmuChg = D₀U - D₀(V - U_raw) - D₀U_raw`
equals `D₀X` for every jointly smooth `X` agreeing with `r_b` off the axis: `V - U_raw` is
`U - X - U_raw` near every off-axis point (`U - V = r_b = X`), and `D_μ` is additive on fields
that are `C²` near the point (`dcl_physDmu_sub`, proved here locally, since `U_raw` is only `C²`
off the axis).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete



open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **Local additivity of `D_μ`**: for fields `f`, `g` that are jointly `C²` on an open set `O`
containing `(τ, y)`, `D_μ(f - g)(τ, y) = D_μ f(τ, y) - D_μ g(τ, y)`. -/
theorem dcl_physDmu_sub {O : Set (ℝ × Space)} (hO : IsOpen O) {f g : ℝ × Space → Space}
    (hf : ContDiffOn ℝ 2 f O) (hg : ContDiffOn ℝ 2 g O) {τ : ℝ} {y : Space} (hx : (τ, y) ∈ O)
    (ν μ : ℝ) :
    physDmu ν μ (fun t y' => f (t, y') - g (t, y')) τ y =
      physDmu ν μ (fun t y' => f (t, y')) τ y - physDmu ν μ (fun t y' => g (t, y')) τ y := by
  have hdf : ∀ x ∈ O, DifferentiableAt ℝ f x := fun x hx' =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx')
  have hdg : ∀ x ∈ O, DifferentiableAt ℝ g x := fun x hx' =>
    (hg.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx')
  -- time slices and space slices of a field differentiable on `O`
  have ht : ∀ H : ℝ × Space → Space, (∀ x ∈ O, DifferentiableAt ℝ H x) →
      DifferentiableAt ℝ (fun t : ℝ => H (t, y)) τ := fun H hH =>
    (hH (τ, y) hx).comp τ (differentiableAt_id.prodMk (differentiableAt_const y))
  have hs : ∀ H : ℝ × Space → Space, (∀ x ∈ O, DifferentiableAt ℝ H x) →
      DifferentiableAt ℝ (fun y' : Space => H (τ, y')) y := fun H hH =>
    (hH (τ, y) hx).comp y ((differentiableAt_const τ).prodMk differentiableAt_id)
  have hT : deriv (fun t => f (t, y) - g (t, y)) τ =
      deriv (fun t => f (t, y)) τ - deriv (fun t => g (t, y)) τ :=
    deriv_sub (ht f hdf) (ht g hdg)
  have hS : fderiv ℝ (fun y' => f (τ, y') - g (τ, y')) y =
      fderiv ℝ (fun y' => f (τ, y')) y - fderiv ℝ (fun y' => g (τ, y')) y :=
    fderiv_sub (hs f hdf) (hs g hdg)
  -- the second derivative of a slice is a fibre derivative of the joint field
  have hL : ∀ F : ℝ × Space → Space, ContDiffOn ℝ 2 F O → ∀ j : Fin 3,
      physPd2 (fun y' => F (τ, y')) j j y =
        fderiv ℝ (fun x => fderiv ℝ F x (0, coordinateVector j)) (τ, y) (0, coordinateVector j) :=
    fun F hF j => physPd2_slice hO hF j j hx
  -- fibre derivatives split on `O`
  have hfd : ∀ (v w : Space),
      fderiv ℝ (fun x => fderiv ℝ (f - g) x (0, v)) (τ, y) (0, w) =
        fderiv ℝ (fun x => fderiv ℝ f x (0, v)) (τ, y) (0, w) -
          fderiv ℝ (fun x => fderiv ℝ g x (0, v)) (τ, y) (0, w) := by
    intro v w
    have ev : (fun x => fderiv ℝ (f - g) x (0, v)) =ᶠ[𝓝 (τ, y)]
        (fun x => fderiv ℝ f x (0, v) - fderiv ℝ g x (0, v)) := by
      filter_upwards [hO.mem_nhds hx] with x hx'
      show fderiv ℝ (f - g) x (0, v) = fderiv ℝ f x (0, v) - fderiv ℝ g x (0, v)
      rw [fderiv_sub (hdf x hx') (hdg x hx')]
      rfl
    have hdA : DifferentiableAt ℝ (fun x => fderiv ℝ f x (0, v)) (τ, y) :=
      ((contDiffOn_fderiv_apply hO hf v).differentiableOn (by norm_num)).differentiableAt
        (hO.mem_nhds hx)
    have hdB : DifferentiableAt ℝ (fun x => fderiv ℝ g x (0, v)) (τ, y) :=
      ((contDiffOn_fderiv_apply hO hg v).differentiableOn (by norm_num)).differentiableAt
        (hO.mem_nhds hx)
    rw [ev.fderiv_eq]
    exact congrArg (fun L : ℝ × Space →L[ℝ] Space => L (0, w)) (fderiv_sub hdA hdB)
  have hlap : physLap (fun y' => f (τ, y') - g (τ, y')) y =
      physLap (fun y' => f (τ, y')) y - physLap (fun y' => g (τ, y')) y := by
    unfold physLap
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have k1 : physPd2 (fun y' => f (τ, y') - g (τ, y')) j j y =
        fderiv ℝ (fun x => fderiv ℝ (f - g) x (0, coordinateVector j))
          (τ, y) (0, coordinateVector j) :=
      hL (f - g) (hf.sub hg) j
    rw [k1, hL f hf j, hL g hg j, hfd]
  unfold physDmu
  simp only [smul_sub]
  rw [hT, hS, hlap]
  simp only [sub_apply, smul_sub]
  abel

/-- **`DmuChgLinAt` for one level**: `dmuChg = D₀X` off the axis for every jointly `C^∞` field
`X` agreeing with `r_b = U - V` off the axis (source 4140-4141, `U = V + r_b`). -/
theorem dcl_dmuChgLinAt (Pl : PlanarData) (L : ReturnLevel)
    (hU : ContDiff ℝ ∞ (fun x : ℝ × Space => L.U x.1 x.2))
    (hψ : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => L.train.ψ x.1 x.2)
      (Set.Ioi 0 ×ˢ Set.univ)) :
    DmuChgLinAt Pl L := by
  intro X hXs hXeq τ y hy
  have hxO : (τ, y) ∈ offAxis := hy
  have hψ3 : ContDiffOn ℝ 3 (fun x : ℝ × UnforcedLeray.Cyl.Plane => (L.params Pl).train.ψ x.1 x.2)
      (Set.Ioi 0 ×ˢ Set.univ) := hψ.of_le (by norm_num)
  have hUc : ContDiffOn ℝ 2 (fun x : ℝ × Space => L.U x.1 x.2) offAxis :=
    (hU.contDiffOn).of_le (by norm_num)
  have hXc : ContDiffOn ℝ 2 (fun x : ℝ × Space => X x.1 x.2) offAxis :=
    (hXs.contDiffOn).of_le (by norm_num)
  have hRc : ContDiffOn ℝ 2 (fun x : ℝ × Space => rawU Pl L x.1 x.2) offAxis :=
    rawU_contDiffOn_offAxis_of (L.params Pl) L.ε_pos hψ3
  have hA : physDmu L.ν 0 (fun t y' => L.U t y' - X t y' - rawU Pl L t y') τ y =
      physDmu L.ν 0 (fun t y' => L.U t y' - X t y') τ y - physDmu L.ν 0 (rawU Pl L) τ y :=
    dcl_physDmu_sub isOpen_offAxis (hUc.sub hXc) hRc hxO L.ν 0
  have hB : physDmu L.ν 0 (fun t y' => L.U t y' - X t y') τ y =
      physDmu L.ν 0 L.U τ y - physDmu L.ν 0 X τ y :=
    dcl_physDmu_sub isOpen_offAxis hUc hXc hxO L.ν 0
  have hC : physDmu L.ν 0 (fun t y' => L.V t y' - rawU Pl L t y') τ y =
      physDmu L.ν 0 (fun t y' => L.U t y' - X t y' - rawU Pl L t y') τ y := by
    apply physDmu_congr_nhds
    intro t
    refine Filter.eventuallyEq_of_mem (isOpen_compl_axis.mem_nhds hy) fun y' hy' => ?_
    show L.V t y' - rawU Pl L t y' = L.U t y' - X t y' - rawU Pl L t y'
    rw [hXeq t y' hy']
    show L.V t y' - rawU Pl L t y' = (L.V t y' + L.rb t y') - L.rb t y' - rawU Pl L t y'
    abel
  unfold dmuChg
  rw [hC, hA, hB]
  abel

/-- **`dmuChgLin`** (`PartIII-b:C/rep/8/2/pres/3/2/1/9`, source 4140-4141, 1213-1225): along the
sequence, `dmuChg` is the `D₀` of a jointly smooth solenoidal extension of `r_b`. -/
theorem dmuChgLin (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.DmuChgLin := by
  filter_upwards [hst.actual] with n hact
  exact dcl_dmuChgLinAt D.Pl (D.level n) hact.profile.smoothU
    (D.level n).train_stream_smooth

end UnforcedLeray.Short.PartIIIb.Concrete
