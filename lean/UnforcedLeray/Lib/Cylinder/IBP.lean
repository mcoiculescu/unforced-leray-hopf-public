import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Integration by parts on the centred cell (INF13, target CY05, first part)


§5 CY05 (`integral_cell_partialQ_mul`, `integral_cell_curl_eq_zero`); decisions D1 and D10 of
`scoping/README.md` §3.

The two one-dimensional fundamental theorems on the cell `[-c/2, c/2) × ℝ`:
* along `q` on `[-c/2, c/2]` with the seam boundary term (`integral_cell_deriv_q`), which
  vanishes for periodic functions (`integral_cell_deriv_q_of_periodic`);
* along `η` on the whole line, for an integrable function with an integrable derivative
  (`integral_cell_deriv_eta`).

Consequences:
* `integral_cell_partialQ_mul`, `integral_cell_partialEta_mul`: partial integration;
* `integral_cell_curl_eq_zero` (`paper/main.tex` lines 4653-4677, unit B0285: "It has zero
  circulation as the curl of a spatially localized integrable vector"; lines 2180-2182, unit
  B0144, vorticity mass zero) and `integral_cell_divergence_eq_zero`.

The slice calculus (`hasDerivAt_sliceQ`, `partialQ_eq_fderiv`, `contDiff_partialQ`, `C2`) is

functions and `GaussianVortex.partialX`), here for functions with values in any real normed
space.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace UnforcedLeray.Cyl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Slice calculus (adapted from `Units/B0242/Seam.lean`) -/

section Slices

theorem hasDerivAt_sliceQ {h : Plane → E} (hd : Differentiable ℝ h) (q η : ℝ) :
    HasDerivAt (fun q' => h (q', η)) (partialQ h (q, η)) q := by
  have : DifferentiableAt ℝ (fun q' : ℝ => h (q', η)) q :=
    (hd (q, η)).comp q (differentiableAt_id.prodMk (differentiableAt_const η))
  exact this.hasDerivAt

theorem hasDerivAt_sliceEta {h : Plane → E} (hd : Differentiable ℝ h) (q η : ℝ) :
    HasDerivAt (fun η' => h (q, η')) (partialEta h (q, η)) η := by
  have : DifferentiableAt ℝ (fun η' : ℝ => h (q, η')) η :=
    (hd (q, η)).comp η ((differentiableAt_const q).prodMk differentiableAt_id)
  exact this.hasDerivAt

theorem partialQ_eq_fderiv {h : Plane → E} (hd : Differentiable ℝ h) (z : Plane) :
    partialQ h z = fderiv ℝ h z (1, 0) := by
  have h1 : HasDerivAt (fun q' : ℝ => h (q', z.2)) (fderiv ℝ h (z.1, z.2) (1, 0)) z.1 := by
    have h0 : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    exact (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h0
  exact h1.deriv

theorem partialEta_eq_fderiv {h : Plane → E} (hd : Differentiable ℝ h) (z : Plane) :
    partialEta h z = fderiv ℝ h z (0, 1) := by
  have h1 : HasDerivAt (fun η' : ℝ => h (z.1, η')) (fderiv ℝ h (z.1, z.2) (0, 1)) z.2 := by
    have h0 : HasDerivAt (fun η : ℝ => (z.1, η)) ((0 : ℝ), (1 : ℝ)) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    exact (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h0
  exact h1.deriv

theorem contDiff_partialQ {n : WithTop ℕ∞} {h : Plane → E} (hh : ContDiff ℝ (n + 1) h) :
    ContDiff ℝ n (partialQ h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialQ h = fun z => fderiv ℝ h z (1, 0) from funext (partialQ_eq_fderiv hd)]
  exact (hh.fderiv_right le_rfl).clm_apply contDiff_const

theorem contDiff_partialEta {n : WithTop ℕ∞} {h : Plane → E} (hh : ContDiff ℝ (n + 1) h) :
    ContDiff ℝ n (partialEta h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialEta h = fun z => fderiv ℝ h z (0, 1) from funext (partialEta_eq_fderiv hd)]
  exact (hh.fderiv_right le_rfl).clm_apply contDiff_const

/-- The regularity package of a `C²` function used in the integrations by parts. -/
structure C2 (φ : Plane → E) : Prop where
  cont : Continuous φ
  diff : Differentiable ℝ φ
  diffQ : Differentiable ℝ (partialQ φ)
  diffEta : Differentiable ℝ (partialEta φ)
  contQ : Continuous (partialQ φ)
  contEta : Continuous (partialEta φ)
  contQQ : Continuous (partialQ (partialQ φ))
  contEtaEta : Continuous (partialEta (partialEta φ))

theorem C2.of_contDiff {φ : Plane → E} (hφ : ContDiff ℝ 2 φ) : C2 φ := by
  have h11 : ContDiff ℝ (1 + 1) φ := by rwa [one_add_one_eq_two]
  have hX1 : ContDiff ℝ 1 (partialQ φ) := contDiff_partialQ h11
  have hY1 : ContDiff ℝ 1 (partialEta φ) := contDiff_partialEta h11
  have hX1' : ContDiff ℝ (0 + 1) (partialQ φ) := by simpa using hX1
  have hY1' : ContDiff ℝ (0 + 1) (partialEta φ) := by simpa using hY1
  exact ⟨hφ.continuous, hφ.differentiable (by norm_num), hX1.differentiable (by norm_num),
    hY1.differentiable (by norm_num), hX1.continuous, hY1.continuous,
    (contDiff_partialQ hX1').continuous, (contDiff_partialEta hY1').continuous⟩

theorem C1_partial_of_contDiff {φ : Plane → E} (hφ : ContDiff ℝ 1 φ) :
    Continuous (partialQ φ) ∧ Continuous (partialEta φ) := by
  have h1 : ContDiff ℝ (0 + 1) φ := by simpa using hφ
  exact ⟨(contDiff_partialQ h1).continuous, (contDiff_partialEta h1).continuous⟩

end Slices

/-- The Laplacian `∂_q² + ∂_η²` with classical partial derivatives. -/
def laplacian (f : Plane → E) (z : Plane) : E :=
  partialQ (partialQ f) z + partialEta (partialEta f) z

/-! ### The fundamental theorems on the cell -/

section FTC

variable [CompleteSpace E]

/-- FTC along `q` on the centred cell, with the seam boundary term. -/
theorem integral_cell_deriv_q {c : ℝ} (hc : 0 < c) {F F' : Plane → E}
    (hd : ∀ q η, HasDerivAt (fun q' => F (q', η)) (F' (q, η)) q)
    (hi : IntegrableOn F' (cell c)) :
    ∫ z in cell c, F' z = ∫ η, (F (c / 2, η) - F (-c / 2, η)) := by
  rw [integral_cell_eq_integral_integral hi]
  refine integral_congr_ae ?_
  have hi' : Integrable F' ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
    rw [← volume_restrict_cell]; exact hi
  filter_upwards [hi'.prod_left_ae] with η hη
  have hle : -c / 2 ≤ c / 2 := by linarith
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun q => F (q, η))
    (fun q _ => hd q η) ?_
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
  exact (integrableOn_Ioc_iff_integrableOn_Ioo).2 ((integrableOn_Ico_iff_integrableOn_Ioo).1 hη)

/-- FTC along `q` for a periodic function: no boundary term. -/
theorem integral_cell_deriv_q_of_periodic {c : ℝ} (hc : 0 < c) {F F' : Plane → E}
    (hper : IsPeriodic c F) (hd : ∀ q η, HasDerivAt (fun q' => F (q', η)) (F' (q, η)) q)
    (hi : IntegrableOn F' (cell c)) :
    ∫ z in cell c, F' z = 0 := by
  rw [integral_cell_deriv_q hc hd hi]
  simp [hper.neg_half]

omit [CompleteSpace E] in
/-- FTC along `η` on the whole line: an integrable function with integrable derivative. -/
theorem integral_cell_deriv_eta {c : ℝ} {F F' : Plane → E}
    (hd : ∀ q η, HasDerivAt (fun η' => F (q, η')) (F' (q, η)) η)
    (hF : IntegrableOn F (cell c)) (hi : IntegrableOn F' (cell c)) :
    ∫ z in cell c, F' z = 0 := by
  rw [integral_cell_eq_integral_integral' hi]
  have hi' : Integrable F' ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
    rw [← volume_restrict_cell]; exact hi
  have hF' : Integrable F ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
    rw [← volume_restrict_cell]; exact hF
  have h0 : ∀ᵐ q ∂(volume.restrict (Ico (-c / 2) (c / 2))), ∫ η, F' (q, η) = 0 := by
    filter_upwards [hF'.prod_right_ae, hi'.prod_right_ae] with q h1 h2
    exact integral_eq_zero_of_hasDerivAt_of_integrable (fun η => hd q η) h2 h1
  rw [integral_congr_ae h0, integral_zero]

end FTC

/-! ### Partial integration -/

section Parts

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Partial integration in `q`** for periodic functions (CY05). -/
theorem integral_cell_partialQ_mul {c : ℝ} (hc : 0 < c) {f g : Plane → 𝔸}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfp : IsPeriodic c f) (hgp : IsPeriodic c g)
    (h1 : IntegrableOn (fun z => partialQ f z * g z) (cell c))
    (h2 : IntegrableOn (fun z => f z * partialQ g z) (cell c)) :
    ∫ z in cell c, partialQ f z * g z = -∫ z in cell c, f z * partialQ g z := by
  have hd : ∀ q η, HasDerivAt (fun q' => f (q', η) * g (q', η))
      (partialQ f (q, η) * g (q, η) + f (q, η) * partialQ g (q, η)) q := fun q η =>
    (hasDerivAt_sliceQ hf q η).mul (hasDerivAt_sliceQ hg q η)
  have hper : IsPeriodic c (fun z => f z * g z) := fun z => by
    show f _ * g _ = f z * g z
    rw [hfp z, hgp z]
  have h := integral_cell_deriv_q_of_periodic hc hper
    (F' := fun z => partialQ f z * g z + f z * partialQ g z) hd (h1.add h2)
  rw [integral_add h1 h2] at h
  exact eq_neg_of_add_eq_zero_left h

omit [CompleteSpace 𝔸] in
/-- **Partial integration in `η`** for functions with integrable products (CY05). -/
theorem integral_cell_partialEta_mul {c : ℝ} {f g : Plane → 𝔸}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (h0 : IntegrableOn (fun z => f z * g z) (cell c))
    (h1 : IntegrableOn (fun z => partialEta f z * g z) (cell c))
    (h2 : IntegrableOn (fun z => f z * partialEta g z) (cell c)) :
    ∫ z in cell c, partialEta f z * g z = -∫ z in cell c, f z * partialEta g z := by
  have hd : ∀ q η, HasDerivAt (fun η' => f (q, η') * g (q, η'))
      (partialEta f (q, η) * g (q, η) + f (q, η) * partialEta g (q, η)) η := fun q η =>
    (hasDerivAt_sliceEta hf q η).mul (hasDerivAt_sliceEta hg q η)
  have h := integral_cell_deriv_eta (F := fun z => f z * g z)
    (F' := fun z => partialEta f z * g z + f z * partialEta g z) hd h0 (h1.add h2)
  rw [integral_add h1 h2] at h
  exact eq_neg_of_add_eq_zero_left h

end Parts

/-! ### Zero circulation of curls and divergences -/

theorem differentiable_component {u : Plane → Vec2} (hu : Differentiable ℝ u) (i : Fin 2) :
    Differentiable ℝ fun z => u z i :=
  (EuclideanSpace.proj i : Vec2 →L[ℝ] ℝ).differentiable.comp hu

/-- **Zero circulation of a curl** (CY05; B0285, tex 4653-4677; B0144, tex 2180-2182).
The curl of a differentiable `c`-periodic meridional field `u` with `u₁`, `∂_q u₂` and
`∂_η u₁` integrable on the cell has zero cell integral. -/
theorem integral_cell_curl_eq_zero {c : ℝ} (hc : 0 < c) {u : Plane → Vec2}
    (hu : Differentiable ℝ u) (hper : IsPeriodic c u)
    (hu₀ : IntegrableOn (fun z => u z 0) (cell c))
    (hq : IntegrableOn (partialQ fun z => u z 1) (cell c))
    (hη : IntegrableOn (partialEta fun z => u z 0) (cell c)) :
    ∫ z in cell c, curl u z = 0 := by
  have h1 : ∫ z in cell c, partialQ (fun z => u z 1) z = 0 :=
    integral_cell_deriv_q_of_periodic hc (hper.fun_comp fun x => x 1)
      (hasDerivAt_sliceQ (differentiable_component hu 1)) hq
  have h2 : ∫ z in cell c, partialEta (fun z => u z 0) z = 0 :=
    integral_cell_deriv_eta (hasDerivAt_sliceEta (differentiable_component hu 0)) hu₀ hη
  simp only [curl]
  rw [integral_sub hq hη, h1, h2, sub_zero]

/-- Zero cell integral of a divergence. -/
theorem integral_cell_divergence_eq_zero {c : ℝ} (hc : 0 < c) {u : Plane → Vec2}
    (hu : Differentiable ℝ u) (hper : IsPeriodic c u)
    (hu₁ : IntegrableOn (fun z => u z 1) (cell c))
    (hq : IntegrableOn (partialQ fun z => u z 0) (cell c))
    (hη : IntegrableOn (partialEta fun z => u z 1) (cell c)) :
    ∫ z in cell c, divergence u z = 0 := by
  have h1 : ∫ z in cell c, partialQ (fun z => u z 0) z = 0 :=
    integral_cell_deriv_q_of_periodic hc (hper.fun_comp fun x => x 0)
      (hasDerivAt_sliceQ (differentiable_component hu 0)) hq
  have h2 : ∫ z in cell c, partialEta (fun z => u z 1) z = 0 :=
    integral_cell_deriv_eta (hasDerivAt_sliceEta (differentiable_component hu 1)) hu₁ hη
  simp only [divergence]
  rw [integral_add hq hη, h1, h2, add_zero]

/-! ### Functions with compact support in `η` -/

/-- `f` vanishes for `|η| > R`. -/
def VanishesOutside (R : ℝ) (f : Plane → E) : Prop := ∀ z : Plane, R < |z.2| → f z = 0

theorem VanishesOutside.partialQ {R : ℝ} {f : Plane → E} (hf : VanishesOutside R f) :
    VanishesOutside R (partialQ f) := by
  intro z hz
  simp only [Cyl.partialQ]
  have : (fun q : ℝ => f (q, z.2)) = fun _ => 0 := funext fun q => hf (q, z.2) hz
  rw [this, deriv_const]

theorem VanishesOutside.partialEta {R : ℝ} {f : Plane → E} (hf : VanishesOutside R f) :
    VanishesOutside R (partialEta f) := by
  intro z hz
  simp only [Cyl.partialEta]
  have hopen : IsOpen {η : ℝ | R < |η|} := isOpen_lt continuous_const continuous_abs
  have hev : (fun η : ℝ => f (z.1, η)) =ᶠ[𝓝 z.2] fun _ => 0 :=
    Filter.eventually_of_mem (hopen.mem_nhds hz) fun η hη => hf (z.1, η) hη
  rw [hev.deriv_eq, deriv_const]

theorem VanishesOutside.mul_left {𝔸 : Type*} [NormedRing 𝔸] {R : ℝ} {f : Plane → 𝔸}
    (hf : VanishesOutside R f) (g : Plane → 𝔸) : VanishesOutside R fun z => g z * f z :=
  fun z hz => by show g z * f z = 0; rw [hf z hz, mul_zero]

theorem VanishesOutside.mul_right {𝔸 : Type*} [NormedRing 𝔸] {R : ℝ} {f : Plane → 𝔸}
    (hf : VanishesOutside R f) (g : Plane → 𝔸) : VanishesOutside R fun z => f z * g z :=
  fun z hz => by show f z * g z = 0; rw [hf z hz, zero_mul]

omit [NormedSpace ℝ E] in
/-- A continuous function with compact support in `η` is integrable on the cell. -/
theorem VanishesOutside.integrableOn_cell {R : ℝ} {f : Plane → E} (hf : VanishesOutside R f)
    (hc : Continuous f) (c : ℝ) : IntegrableOn f (cell c) := by
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  refine (hc.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero (measurableSet_cell c)
    fun z hz => hf z ?_
  obtain ⟨hz1, hz2⟩ := hz
  rw [mem_cell] at hz1
  simp only [mem_prod, mem_Icc, not_and, not_le] at hz2
  have := hz2 ⟨hz1.1, hz1.2.le⟩
  by_contra hle
  push Not at hle
  rw [abs_le] at hle
  rcases le_or_gt (-R) z.2 with h | h
  · exact absurd hle.2 (not_le.2 (this h))
  · linarith [hle.1]

end UnforcedLeray.Cyl
