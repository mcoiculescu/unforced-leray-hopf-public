import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7`, leaf `CylFieldSmooth`: the Cartesian lift is `C²` off the axis

Proves `UnforcedLeray.Short.IIb.CylFieldSmooth` (defined in `Sub/R1_7.lean`). Source of record:
`the November 2 reference manuscript`, lines 1203-1263. The off-axis smoothness of
`ϱ` and `eR` is `Axi.contDiffOn_ϱ` and `Axi.contDiffOn_eR` (`Lib/Axisymmetric/Cylindrical.lean`).

Proof idea. The chart `Ψ(t, x) = (ϱ x, x₃, t)` maps `ℝ × ℝ³` off the axis at positive time into the
open set `meridDomain`, where each meridional profile is `C²`. The composition
`(t, x) ↦ f(ϱ x, x₃, t)` is then `C²`, and the field is the sum of the two profiles times the
`C²` frame vectors `eR x` and `e₃`.

No hypotheses are added to the statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-- The open domain `meridDomain = {r > 0, t > 0}` is open. -/
theorem cylFS_isOpen_meridDomain : IsOpen meridDomain := by
  unfold meridDomain
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd.snd)

/-- The chart `(t, x) ↦ (ϱ x, x₃, t)` is `C²` off the axis. -/
theorem cylFS_chart_contDiffAt {t : ℝ} {x : Space} (hx : x ∉ Axi.axis) :
    ContDiffAt ℝ 2 (fun q : ℝ × Space => (Axi.ϱ q.2, q.2 2, q.1)) (t, x) := by
  have hϱ : ContDiffAt ℝ 2 Axi.ϱ x :=
    (Axi.contDiffOn_ϱ (k := 2)).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hx)
  have h1 : ContDiffAt ℝ 2 (Axi.ϱ ∘ Prod.snd) (t, x) :=
    hϱ.comp (t, x) contDiffAt_snd
  have h2 : ContDiff ℝ 2 (fun q : ℝ × Space => q.2 2) := by
    fun_prop
  have h3 : ContDiff ℝ 2 (fun q : ℝ × Space => q.1) := by
    fun_prop
  exact h1.prodMk (h2.contDiffAt.prodMk h3.contDiffAt)

/-- A `C²` meridional profile `f` composes with the chart: `(t, x) ↦ f(ϱ x, x₃, t)` is `C²` at
positive time off the axis. -/
theorem cylFS_comp_contDiffAt {f : ℝ → ℝ → ℝ → ℝ} {t : ℝ} {x : Space}
    (ht : 0 < t) (hx : x ∉ Axi.axis) (hf : MeridSmooth 2 f) :
    ContDiffAt ℝ 2 (fun q : ℝ × Space => f (Axi.ϱ q.2) (q.2 2) q.1) (t, x) := by
  have hmem : ((Axi.ϱ x, x 2, t) : ℝ × ℝ × ℝ) ∈ meridDomain := by
    unfold meridDomain
    exact ⟨Axi.ϱ_pos hx, ht⟩
  have hg : ContDiffAt ℝ 2 (fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) (Axi.ϱ x, x 2, t) :=
    ContDiffOn.contDiffAt hf (cylFS_isOpen_meridDomain.mem_nhds hmem)
  exact hg.comp (t, x) (cylFS_chart_contDiffAt hx)

/-- **`CylFieldSmooth`.** The Cartesian field and pressure of `C²` meridional profiles are `C²`
jointly in `(t, x)` off the axis at positive time. -/
theorem cylFieldSmooth : UnforcedLeray.Short.IIb.CylFieldSmooth := by
  unfold CylFieldSmooth
  intro ur uz p t x ht hx hur huz hp
  have hR : ContDiffAt ℝ 2 Axi.eR x :=
    (Axi.contDiffOn_eR (k := 2)).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hx)
  have hEx : ContDiffAt ℝ 2 (Axi.eR ∘ Prod.snd) (t, x) :=
    hR.comp (t, x) contDiffAt_snd
  have hE3 : ContDiffAt ℝ 2 (fun _ : ℝ × Space => Axi.e3) (t, x) := contDiffAt_const
  have hUr := cylFS_comp_contDiffAt ht hx hur
  have hUz := cylFS_comp_contDiffAt ht hx huz
  have hP := cylFS_comp_contDiffAt ht hx hp
  refine ⟨?_, hP⟩
  exact (hUr.smul hEx).add (hUz.smul hE3)
