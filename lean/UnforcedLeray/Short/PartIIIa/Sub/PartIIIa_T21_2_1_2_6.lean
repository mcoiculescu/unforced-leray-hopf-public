import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_5

/-!
# `KerCurlPointwise` from the regularised stream function (SP 2081-2084, 3121)

`K_d = ∇^⊥ G_d`, `ΔG_d = Σ_n δ_{(nd,0)}`.  With `G_{d,ε} = (4π)⁻¹ log (den + ε)` (see
`PartIII-a_T21_2_1_2_5.lean`) we have `r_ε K = ∇^⊥ G_{d,ε}` off the lattice, `r_ε = den/(den+ε)`,
so `r_ε (K_q ∂_η φ - K_η ∂_q φ) = -∇G_{d,ε} · ∇φ`, whose integral is `∫ ΔG_{d,ε} φ` by one
integration by parts.  Dominated convergence on the left (same dominator as in the divergence case)
and the approximate identity `ΔG_{d,ε} → δ` on the right give the result.

Leaves (each its own task): `KerGradIBP` (integration by parts of the gradient pairing, for
`G` smooth `q`-periodic) and `KerApproxId` (the approximate identity).  Reused from the
divergence case: `KerRegSmooth`, `KerRegDeriv`, `KerBandInt`, `KerLatticeNull`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Gradient integration by parts** (periodicity in `q`, band support in `η`):
for `G` smooth and `d`-periodic in `q` and a cylinder test `φ`,
`∫_{C_d} ∇G · ∇φ = -∫_{C_d} ΔG φ`. -/
def KerGradIBP : Prop :=
  ∀ d : ℝ, 0 < d → ∀ G : ℝ × ℝ → ℝ, ContDiff ℝ ∞ G → (∀ z : ℝ × ℝ, G (z.1 + d, z.2) = G z) →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ →
      ∫ x in B0579.cell d, (B0579.pd 0 G x * B0579.pd 0 φ x + B0579.pd 1 G x * B0579.pd 1 φ x) =
        -∫ x in B0579.cell d,
          (B0579.pd 0 (B0579.pd 0 G) x + B0579.pd 1 (B0579.pd 1 G) x) * φ x

/-- **Approximate identity** `ΔG_{d,ε}(· - y) → δ_y` on the cylinder (SP 2081-2084):
`ΔG_{d,ε}(z) = (π ε/d²)(cosh(2πη/d) + cos(2πq/d))/(den(z) + ε)² ≥ 0` has `∫_{C_d} = 1`, and is
`≤ C_δ ε` (with exponentially decaying tail) on `{‖z‖ ≥ δ}` modulo the period, so for a
continuous periodic band-supported `φ` the pairing tends to `φ y` (periodic shift to centre the
cell at `y`). -/
def KerApproxId : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ → ∀ y : ℝ × ℝ,
    Tendsto (fun ε : ℝ => ∫ x in B0579.cell d,
      (B0579.pd 0 (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x +
        B0579.pd 1 (B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x) * φ x)
      (𝓝[>] 0) (𝓝 (φ y))

/-- **Assembly** (SP 2081-2084, 3121). -/
theorem kerCurlPointwise_of_parts (hS : KerRegSmooth) (hD : KerRegDeriv) (hI : KerGradIBP)
    (hA : KerApproxId) (hB : KerBandInt) (hN : KerLatticeNull) : KerCurlPointwise := by
  intro d hd φ hφ y
  have hd0 : 0 < d := by linarith
  set F : ℝ × ℝ → ℝ := fun x =>
    kerD d (x - y) 0 * B0579.pd 1 φ x - kerD d (x - y) 1 * B0579.pd 0 φ x with hF
  set dn : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0592.den d (x - y) with hdn
  have hFint : IntegrableOn F (B0579.cell d) :=
    (hB d hd _ (hφ.pd 1) y 0).sub (hB d hd _ (hφ.pd 0) y 1)
  have hdn_cont : Continuous dn := (continuous_den d).comp (continuous_id.sub continuous_const)
  have hdn_nn : ∀ x, 0 ≤ dn x := fun x => den_nonneg d _
  have hnull : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), dn x ≠ 0 := by
    rw [ae_iff]
    have : {x : ℝ × ℝ | ¬ dn x ≠ 0} =
        (fun h : ℝ × ℝ => h + -y) ⁻¹' {z : ℝ × ℝ | UnforcedLeray.B0592.den d z = 0} := by
      ext x; simp [hdn, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
    exact hN d hd0
  have hnull' : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), dn x ≠ 0 := ae_restrict_of_ae hnull
  -- the regularised pairing equals the Laplacian pairing
  have hreg : ∀ ε : ℝ, 0 < ε → ∫ x in B0579.cell d, dn x / (dn x + ε) * F x =
      ∫ x in B0579.cell d,
      (B0579.pd 0 (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x +
        B0579.pd 1 (B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x) * φ x := by
    intro ε hε
    obtain ⟨hsm, hper⟩ := hS d ε hd0 hε
    have hGsm : ContDiff ℝ ∞ (fun x : ℝ × ℝ => kerReg d ε (x - y)) :=
      hsm.comp (contDiff_id.sub contDiff_const)
    have hGper : ∀ z : ℝ × ℝ, (fun x : ℝ × ℝ => kerReg d ε (x - y)) (z.1 + d, z.2) =
        (fun x : ℝ × ℝ => kerReg d ε (x - y)) z := by
      intro z
      have : ((z.1 + d, z.2) - y : ℝ × ℝ) = ((z - y).1 + d, (z - y).2) := by
        ext <;> simp <;> ring
      simp only [this, hper]
    have h0 := hI d hd0 _ hGsm hGper φ hφ
    have h1 : ∫ x in B0579.cell d, dn x / (dn x + ε) * F x =
        -∫ x in B0579.cell d,
          (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y)) x * B0579.pd 0 φ x +
            B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y)) x * B0579.pd 1 φ x) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hnull'] with x hx
      have hx' : UnforcedLeray.B0592.den d (x - y) ≠ 0 := hx
      obtain ⟨e0, e1⟩ := hD d ε hd0 hε (x - y) hx'
      rw [pd_shift, pd_shift, e0, e1]
      simp only [hF, hdn]
      ring
    rw [h1, h0, neg_neg]
  have hlim : Tendsto (fun ε : ℝ => ∫ x in B0579.cell d, dn x / (dn x + ε) * F x) (𝓝[>] 0)
      (𝓝 (∫ x in B0579.cell d, F x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hFint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hc : Continuous fun x => dn x / (dn x + ε) :=
        hdn_cont.div (hdn_cont.add continuous_const) (fun x => by linarith [hdn_nn x])
      exact hc.aestronglyMeasurable.mul hFint.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      refine Eventually.of_forall fun x => ?_
      have h1 : 0 ≤ dn x / (dn x + ε) := div_nonneg (hdn_nn x) (by linarith [hdn_nn x])
      have h2 : dn x / (dn x + ε) ≤ 1 := by
        rw [div_le_one (by linarith [hdn_nn x])]; linarith
      rw [norm_mul, Real.norm_of_nonneg h1]
      exact mul_le_of_le_one_left (norm_nonneg _) h2
    · filter_upwards [hnull'] with x hx
      have hpos : 0 < dn x := lt_of_le_of_ne (hdn_nn x) (Ne.symm hx)
      have h1 : Tendsto (fun ε : ℝ => dn x / (dn x + ε)) (𝓝 0) (𝓝 (dn x / (dn x + 0))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_id) (by simpa using hpos.ne')
      rw [add_zero, div_self hpos.ne'] at h1
      simpa using (h1.mono_left nhdsWithin_le_nhds).mul_const (F x)
  have hlim2 : Tendsto (fun ε : ℝ => ∫ x in B0579.cell d, dn x / (dn x + ε) * F x) (𝓝[>] 0)
      (𝓝 (φ y)) := by
    refine (hA d hd φ hφ y).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hreg ε hε).symm
  exact tendsto_nhds_unique hlim hlim2

/-- **`KerCurlPointwise`** from the leaves and `KerNearFar`-derived band integrability. -/
theorem kerCurlPointwise_of_leaves (hS : KerRegSmooth) (hD : KerRegDeriv) (hI : KerGradIBP)
    (hA : KerApproxId) (hB : KerBandInt) (hN : KerLatticeNull) : KerCurlPointwise :=
  kerCurlPointwise_of_parts hS hD hI hA hB hN

end UnforcedLeray.Short.IIIa
