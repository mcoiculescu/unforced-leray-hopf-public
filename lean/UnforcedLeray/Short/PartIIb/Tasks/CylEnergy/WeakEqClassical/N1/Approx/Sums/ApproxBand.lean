import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.EtaCutProps

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
On the open set `U = {y | 2R < |y.2|}` the cut test `θ_R φ` vanishes identically, hence so does
each term of the age interpolation `sepApprox`; all planar derivatives of a function vanishing on
an open set vanish there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- A function vanishing on an open set has vanishing first partials there. -/
theorem pd_zero_of_zero_on {U : Set B0579.Plane} (hU : IsOpen U) (f : B0579.Plane → ℝ)
    (hf : ∀ y ∈ U, f y = 0) (j : Fin 2) (y : B0579.Plane) (hy : y ∈ U) :
    B0579.pd j f y = 0 := by
  have hev : f =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hf z hz
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

/-- A Laplacian of a function vanishing on an open set vanishes there. -/
theorem lapP_zero_of_zero_on {U : Set B0579.Plane} (hU : IsOpen U) (f : B0579.Plane → ℝ)
    (hf : ∀ y ∈ U, f y = 0) (y : B0579.Plane) (hy : y ∈ U) :
    lapP f y = 0 := by
  unfold lapP
  rw [pd_zero_of_zero_on hU (B0579.pd 0 f) (fun z hz => pd_zero_of_zero_on hU f hf 0 z hz) 0 y hy,
    pd_zero_of_zero_on hU (B0579.pd 1 f) (fun z hz => pd_zero_of_zero_on hU f hf 1 z hz) 1 y hy]
  norm_num

theorem approxBand : UnforcedLeray.Short.IIb.TdSums.ApproxBand := by
  intro t₀ t₁ R K φ hR r x hx
  have hRpos : 0 < R := by linarith
  have hEC := etaCutProps
  unfold EtaCutProps at hEC
  obtain ⟨Cθ, hCθ0, hCθ⟩ := hEC
  set U : Set B0579.Plane := {y | 2 * R < |y.2|} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_snd.abs
  have hxU : x ∈ U := by
    show 2 * R < |x.2|
    linarith
  have hcut0 : ∀ y ∈ U, ∀ s : ℝ, cutTest R φ s y = 0 := by
    intro y hy s
    have hy' : 2 * R < |y.2| := hy
    have hθ : etaCut R y = 0 := (hCθ R hR).2 y |>.2.2.2.1 hy'.le
    unfold cutTest
    rw [hθ, zero_mul]
  have hsep0 : ∀ y ∈ U, ∀ s : ℝ, sepApprox t₀ t₁ K R φ s y = 0 := by
    intro y hy s
    have hfun : (fun s' : ℝ => cutTest R φ s' y) = fun _ => (0 : ℝ) :=
      funext (fun s' => hcut0 y hy s')
    unfold sepApprox
    rw [hfun]
    unfold interp1
    simp
  have hg : ∀ y ∈ U, sepApprox t₀ t₁ K R φ r y = 0 := fun y hy => hsep0 y hy r
  have hh : ∀ y ∈ U, cutTest R φ r y = 0 := fun y hy => hcut0 y hy r
  have hθx : etaCut R x = 0 := (hCθ R hR).2 x |>.2.2.2.1 (by linarith)
  constructor
  · unfold planarErr
    rw [pd_zero_of_zero_on hUopen _ hg 0 x hxU, pd_zero_of_zero_on hUopen _ hg 1 x hxU,
      pd_zero_of_zero_on hUopen _ hh 0 x hxU, pd_zero_of_zero_on hUopen _ hh 1 x hxU,
      lapP_zero_of_zero_on hUopen _ hg x hxU, lapP_zero_of_zero_on hUopen _ hh x hxU,
      hg x hxU, hh x hxU]
    simp
  · have hzero_fun : (fun s : ℝ => sepApprox t₀ t₁ K R φ s x) = fun _ => (0 : ℝ) :=
      funext (fun s => hsep0 x hxU s)
    rw [hzero_fun, deriv_const, hθx]
    simp

end TdSums

end UnforcedLeray.Short.IIb
