import UnforcedLeray.Loc.L09CompactDatum.Datum

/-!
# L9 helper: `u_{0,h}` is `𝒪`-invariant

Helper of `Loc/L09CompactDatum.lean` (step L9, `paper/main.tex` lines 433–436 and 451,
blueprint units B0717, B0719; infrastructure INF24, "symmetry of the azimuthal potential").

An isometry `g` fixing `e₃` maps `e₁, e₂` into the plane `x₃ = 0`; with
`d = det g = ±1` (`axisDet`), `(ga) × (gb) = d · g(a × b)` (`FixesAxis.crossProd_map`). Hence:
* `A_loc(gx) = d · g A_loc(x)` (`DSSField.homotopyPotential_map`; `A_loc` is a pseudo-vector);
* if `G(gy) = c · g G(y)` then `curl G (gx) = c d · g curl G(x)` (`curl_map_of_equivariant`);
* `u_{0,h}(gx) = d² g u_{0,h}(x) = g u_{0,h}(x)` off zero, so `u_{0,h}` is axisymmetric without
  swirl (`DSSField.compactDatum_symmetric`). Line 436: "`A_loc = A_θ e_θ` is an azimuthal
  potential and `u_{0,h}` is axisymmetric without swirl".
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

variable {g : Space ≃ₗᵢ[ℝ] Space}

/-- The determinant of the `2×2` block of an axis-fixing isometry. -/
def axisDet (g : Space ≃ₗᵢ[ℝ] Space) : ℝ :=
  g (coordinateVector 0) 0 * g (coordinateVector 1) 1 -
    g (coordinateVector 0) 1 * g (coordinateVector 1) 0

namespace FixesAxis

/-- The columns `p = g e₁`, `r = g e₂` are orthonormal and lie in `x₃ = 0`. -/
theorem facts (hg : FixesAxis g) :
    g (coordinateVector 0) 2 = 0 ∧ g (coordinateVector 1) 2 = 0 ∧
    g (coordinateVector 0) 0 * g (coordinateVector 0) 0 +
      g (coordinateVector 0) 1 * g (coordinateVector 0) 1 = 1 ∧
    g (coordinateVector 1) 0 * g (coordinateVector 1) 0 +
      g (coordinateVector 1) 1 * g (coordinateVector 1) 1 = 1 ∧
    g (coordinateVector 0) 0 * g (coordinateVector 1) 0 +
      g (coordinateVector 0) 1 * g (coordinateVector 1) 1 = 0 := by
  have hg2 : g (coordinateVector 2) = coordinateVector 2 := hg
  have h02 := g.inner_map_map (coordinateVector 0) (coordinateVector 2)
  have h12 := g.inner_map_map (coordinateVector 1) (coordinateVector 2)
  have h00 := g.inner_map_map (coordinateVector 0) (coordinateVector 0)
  have h11 := g.inner_map_map (coordinateVector 1) (coordinateVector 1)
  have h01 := g.inner_map_map (coordinateVector 0) (coordinateVector 1)
  rw [hg2] at h02 h12
  simp only [inner_coords, cv00, cv01, cv02, cv10, cv11, cv12, cv20, cv21, cv22, mul_zero,
    zero_mul, mul_one, one_mul, add_zero, zero_add] at h02 h12 h00 h11 h01
  rw [h02, mul_zero, add_zero] at h00
  rw [h12, mul_zero, add_zero] at h11
  rw [h02, zero_mul, add_zero] at h01
  exact ⟨h02, h12, h00, h11, h01⟩

theorem apply_coord (hg : FixesAxis g) (a : Space) :
    g a 0 = a 0 * g (coordinateVector 0) 0 + a 1 * g (coordinateVector 1) 0 ∧
    g a 1 = a 0 * g (coordinateVector 0) 1 + a 1 * g (coordinateVector 1) 1 ∧
    g a 2 = a 2 := by
  obtain ⟨hp2, hr2, -, -, -⟩ := FixesAxis.facts hg
  have hg2 : g (coordinateVector 2) = coordinateVector 2 := hg
  have hexp : g a = a 0 • g (coordinateVector 0) + a 1 • g (coordinateVector 1) +
      a 2 • coordinateVector 2 := by
    conv_lhs => rw [← sum_coord_smul_basis a]
    rw [map_sum, Fin.sum_univ_three, map_smul, map_smul, map_smul, hg2]
  rw [hexp]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cv20, cv21, cv22, hp2, hr2,
    mul_zero, mul_one, add_zero, zero_add]
  refine ⟨?_, ?_, ?_⟩ <;> trivial

/-- `det g = ±1`. -/
theorem axisDet_mul_self (hg : FixesAxis g) : axisDet g * axisDet g = 1 := by
  obtain ⟨-, -, hpp, hrr, hpr⟩ := FixesAxis.facts hg
  unfold axisDet
  linear_combination (g (coordinateVector 1) 0 * g (coordinateVector 1) 0 +
      g (coordinateVector 1) 1 * g (coordinateVector 1) 1) * hpp + hrr -
    (g (coordinateVector 0) 0 * g (coordinateVector 1) 0 +
      g (coordinateVector 0) 1 * g (coordinateVector 1) 1) * hpr

/-- **`(ga) × (gb) = det g · g(a × b)`.** -/
theorem crossProd_map (hg : FixesAxis g) (a b : Space) :
    crossProd (g a) (g b) = axisDet g • g (crossProd a b) := by
  obtain ⟨-, -, hpp, hrr, hpr⟩ := FixesAxis.facts hg
  obtain ⟨ha0, ha1, ha2⟩ := FixesAxis.apply_coord hg a
  obtain ⟨hb0, hb1, hb2⟩ := FixesAxis.apply_coord hg b
  obtain ⟨hc0, hc1, hc2⟩ := FixesAxis.apply_coord hg (crossProd a b)
  rw [space_ext_iff]
  simp only [crossProd_coord0, crossProd_coord1, crossProd_coord2, PiLp.smul_apply, smul_eq_mul,
    ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2, axisDet]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (a 1 * b 2 - a 2 * b 1) *
        (-(g (coordinateVector 1) 1) * hpp + g (coordinateVector 0) 1 * hpr) +
      (a 2 * b 0 - a 0 * b 2) *
        (g (coordinateVector 0) 1 * hrr - g (coordinateVector 1) 1 * hpr)
  · linear_combination (a 2 * b 0 - a 0 * b 2) *
        (-(g (coordinateVector 0) 0) * hrr + g (coordinateVector 1) 0 * hpr) +
      (a 1 * b 2 - a 2 * b 1) *
        (g (coordinateVector 1) 0 * hpp - g (coordinateVector 0) 0 * hpr)
  · ring

/-- `(g⁻¹ eⱼ)ₖ = (g eₖ)ⱼ`. -/
theorem symm_coord (g : Space ≃ₗᵢ[ℝ] Space) (j k : Fin 3) :
    g.symm (coordinateVector j) k = g (coordinateVector k) j := by
  have h := g.inner_map_map (g.symm (coordinateVector j)) (coordinateVector k)
  rw [g.apply_symm_apply] at h
  simp only [coordinateVector, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, map_one, one_mul, RCLike.conj_to_real] at h
  exact h.symm

/-- `∑ⱼ eⱼ × g M g⁻¹ eⱼ = det g · g ∑ₖ eₖ × M eₖ`. -/
theorem sum_cross_conj (hg : FixesAxis g) (M : Space →L[ℝ] Space) :
    ∑ j : Fin 3, crossProd (coordinateVector j) (g (M (g.symm (coordinateVector j)))) =
      axisDet g • g (∑ k : Fin 3, crossProd (coordinateVector k) (M (coordinateVector k))) := by
  have hexp : ∀ j : Fin 3, g (M (g.symm (coordinateVector j))) =
      ∑ k : Fin 3, g (coordinateVector k) j • g (M (coordinateVector k)) := by
    intro j
    conv_lhs => rw [← sum_coord_smul_basis (g.symm (coordinateVector j))]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, symm_coord]
  have hcross : ∀ j : Fin 3,
      crossProd (coordinateVector j) (g (M (g.symm (coordinateVector j)))) =
        ∑ k : Fin 3, crossProd (coordinateVector j)
          (g (coordinateVector k) j • g (M (coordinateVector k))) := by
    intro j
    rw [hexp j, ← crossCLM_apply, map_sum]
    simp only [crossCLM_apply]
  simp_rw [hcross]
  rw [Finset.sum_comm]
  simp_rw [sum_crossProd_smul, sum_coord_smul_basis, FixesAxis.crossProd_map hg]
  rw [← Finset.smul_sum, ← map_sum]

end FixesAxis

/-- If `G(gy) = c · g G(y)` then `DG(gx) v = c · g DG(x) g⁻¹ v`. -/
theorem fderiv_map_of_equivariant {G : Space → Space} {c : ℝ}
    (hG : ∀ y, G (g y) = c • g (G y)) {x : Space} (hx : DifferentiableAt ℝ G x) (v : Space) :
    fderiv ℝ G (g x) v = c • g (fderiv ℝ G x (g.symm v)) := by
  have hG' : ∀ z, G z = c • g (G (g.symm z)) := fun z => by
    rw [← hG, g.apply_symm_apply]
  have hs : HasFDerivAt (fun z => g.symm z)
      (g.symm.toContinuousLinearEquiv : Space →L[ℝ] Space) (g x) :=
    g.symm.toContinuousLinearEquiv.hasFDerivAt
  have hFx : HasFDerivAt G (fderiv ℝ G x) (g.symm (g x)) := by
    rw [g.symm_apply_apply]
    exact hx.hasFDerivAt
  have h1 := hFx.comp (g x) hs
  have h2 := ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp (g x) h1).const_smul c
  have h3 := h2.congr_of_eventuallyEq (Eventually.of_forall fun z => hG' z)
  rw [h3.fderiv]
  simp

/-- If `G(gy) = c · g G(y)` then `curl G (gx) = c det g · g curl G(x)`. -/
theorem curl_map_of_equivariant (hg : FixesAxis g) {G : Space → Space} {c : ℝ}
    (hG : ∀ y, G (g y) = c • g (G y)) {x : Space} (hx : DifferentiableAt ℝ G x) :
    curl G (g x) = (c * axisDet g) • g (curl G x) := by
  simp only [curl]
  simp_rw [fderiv_map_of_equivariant hG hx, crossProd_smul_right]
  rw [← Finset.smul_sum, FixesAxis.sum_cross_conj hg (fderiv ℝ G x), smul_smul]

variable {q : ℝ} {u : SpatialField}

namespace DSSField

/-- `A_loc(gx) = det g · g A_loc(x)`. -/
theorem homotopyPotential_map (hu : DSSField q u) (hg : FixesAxis g) (y : Space) :
    homotopyPotential u (g y) = axisDet g • g (homotopyPotential u y) := by
  set L : Space →L[ℝ] Space :=
    axisDet g • (g.toContinuousLinearEquiv : Space →L[ℝ] Space) with hL
  have hLapp : ∀ v : Space, L v = axisDet g • g v := fun v => by simp [hL]
  have hpt : ∀ r : ℝ, r • crossProd (g y) (u (r • g y)) = L (r • crossProd y (u (r • y))) := by
    intro r
    rw [hLapp]
    by_cases hry : r • y = 0
    · rcases smul_eq_zero.mp hry with hr | hy
      · simp [hr]
      · simp [hy]
    · rw [← map_smul g r y, hu.map_isometry hg hry, FixesAxis.crossProd_map hg, map_smul, smul_comm]
  unfold homotopyPotential
  simp_rw [hpt]
  rw [L.intervalIntegral_comp_comm (hu.homotopy_intervalIntegrable y zero_le_one), map_neg,
    hLapp, smul_neg]

/-- The potential `χ A_loc` of the datum transforms like `A_loc`. -/
theorem datumPotential_map (hu : DSSField q u) (hg : FixesAxis g) (y : Space) :
    cutoff (g y) • homotopyPotential u (g y) =
      axisDet g • g (cutoff y • homotopyPotential u y) := by
  have hc : cutoff (g y) = cutoff y := by simp only [cutoff, LinearIsometryEquiv.norm_map]
  rw [hc, hu.homotopyPotential_map hg, map_smul, smul_comm]

/-- `u_{0,h}(gx) = g u_{0,h}(x)` off zero. -/
theorem compactDatum_map (hu : DSSField q u) (hg : FixesAxis g) {x : Space} (hx : x ≠ 0) :
    compactDatum cutoff u (g x) = g (compactDatum cutoff u x) := by
  have hdiff : DifferentiableAt ℝ (fun y => cutoff y • homotopyPotential u y) x :=
    ((cutoff_contDiff.contDiffOn.smul hu.potential_contDiffOn).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  have h := curl_map_of_equivariant hg (hu.datumPotential_map hg) hdiff
  rw [FixesAxis.axisDet_mul_self hg, one_smul] at h
  exact h

/-- **`u_{0,h}` is axisymmetric without swirl** (line 436). -/
theorem compactDatum_symmetric (hu : DSSField q u) :
    IsAxisymmetricNoSwirl (compactDatum cutoff u) := by
  intro g hg
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Space))] with x hx
  have hx0 : g.symm x ≠ 0 := by
    intro h
    apply hx
    rw [mem_singleton_iff]
    simpa using congrArg g h
  have h := hu.compactDatum_map hg hx0
  rw [g.apply_symm_apply] at h
  exact h.symm

end DSSField

end UnforcedLeray.L09
