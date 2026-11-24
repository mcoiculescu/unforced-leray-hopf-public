import UnforcedLeray.Short.PartI.StatementsSeed

/-!
# Part I, task `PartI:S08`: the adjoint eigenvector is unique up to scale

Source of record: `the November 2 reference manuscript`, lines 897-905 (the
index-zero Fredholm argument for `L_0 - λ`: one-dimensional kernel, adjoint kernel spanned by
`h_X`).

Proof outline.
* `g` annihilates `range (L_0 - λ)`, because `L_0^† g = λ̄ g`.
* Every `x` with `ℓ x = 0` lies in `range (L_0 - λ)`. The Laurent form of the simple spectral
  projection `P = ℓ(·) q` gives `R₀ x = lim_{z → λ} (z - L_0)⁻¹ x`, and `(λ - L_0) R₀ x = x`.
* Hence `g ⊥ ker ℓ`. Since `ℓ = ⟪qd, ·⟫`, the vector `g` is a multiple of `qd`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Infra.Dunford (rankOneProj rankOneProj_apply)

/-- For a seed triple `(λ, q, ℓ)`, every `x` with `ℓ x = 0` is of the form `λ y - L_0 y`. -/
theorem seed_kernel_mem_range {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {x : B0010.XG} (hx : l x = 0) :
    ∃ y : B0010.XG, x = lam • y - Planar.L0 y := by
  obtain ⟨R₀, hR⟩ := hI.proj.laurent
  have hv : Tendsto (fun z => resolvent Planar.L0 z x) (𝓝[≠] lam) (𝓝 (R₀ x)) := by
    have h2 := ((ContinuousLinearMap.apply ℂ B0010.XG x).continuous.tendsto R₀).comp hR
    refine h2.congr (fun z => ?_)
    simp [rankOneProj_apply, hx]
  have hres : ∀ z ∈ resolventSet ℂ Planar.L0,
      (algebraMap ℂ (B0010.XG →L[ℂ] B0010.XG) z - Planar.L0) * resolvent Planar.L0 z = 1 := by
    intro z hz
    have key := Units.mul_inv hz.unit
    rw [hz.unit_spec] at key
    rw [spectrum.resolvent_eq hz]
    exact key
  have hevent : ∀ᶠ z in 𝓝[≠] lam,
      z • resolvent Planar.L0 z x - Planar.L0 (resolvent Planar.L0 z x) = x := by
    filter_upwards [hI.proj.eventually_mem_resolventSet] with z hz
    have h1 := congrArg (fun T : B0010.XG →L[ℂ] B0010.XG => T x) (hres z hz)
    simpa [Algebra.algebraMap_eq_smul_one] using h1
  have hconst : Tendsto
      (fun z => z • resolvent Planar.L0 z x - Planar.L0 (resolvent Planar.L0 z x))
      (𝓝[≠] lam) (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    exact hevent.mono fun z hz => hz.symm
  have hid : Tendsto (fun z : ℂ => z) (𝓝[≠] lam) (𝓝 lam) :=
    (continuous_id.tendsto lam).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun z => z • resolvent Planar.L0 z x - Planar.L0 (resolvent Planar.L0 z x))
      (𝓝[≠] lam) (𝓝 (lam • R₀ x - Planar.L0 (R₀ x))) :=
    (hid.smul hv).sub ((Planar.L0.continuous.tendsto (R₀ x)).comp hv)
  exact ⟨R₀ x, tendsto_nhds_unique hconst hlim⟩

/-- **Task `PartI:S08`: the adjoint eigenvector is unique up to scale** (source lines 897-905).
If `(λ, q, ℓ)` is a seed triple, `qd` represents `ℓ` (`ℓ f = ⟪qd, f⟫`), and `g` is an adjoint
eigenvector, `L_0^† g = λ̄ g`, then `g` is a multiple of `qd`. -/
theorem adjoint_eigenvector_unique {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {qd g : B0010.XG} (hqd : ∀ f, l f = inner ℂ qd f)
    (hg : ContinuousLinearMap.adjoint Planar.L0 g = (starRingEnd ℂ) lam • g) :
    ∃ μ : ℂ, g = μ • qd := by
  -- `g` annihilates the range of `L_0 - λ`.
  have horth : ∀ y : B0010.XG, inner ℂ g (lam • y - Planar.L0 y) = 0 := by
    intro y
    have h1 := ContinuousLinearMap.adjoint_inner_left Planar.L0 y g
    rw [hg, inner_smul_left, starRingEnd_self_apply] at h1
    rw [inner_sub_right, inner_smul_right, ← h1, sub_self]
  -- Hence `g` annihilates `ker ℓ`.
  have hperp : ∀ x : B0010.XG, l x = 0 → inner ℂ g x = 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := seed_kernel_mem_range hI hx
    rw [hy]
    exact horth y
  -- `qd ≠ 0`, since `ℓ q = 1`.
  have hqd0 : qd ≠ 0 := by
    intro h0
    have h1 := hI.ell_q
    rw [hqd q, h0, inner_zero_left] at h1
    exact zero_ne_one h1
  have hden : inner ℂ qd qd ≠ 0 := inner_self_ne_zero.2 hqd0
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = inner ℂ qd g / inner ℂ qd qd := ⟨_, rfl⟩
  refine ⟨c, ?_⟩
  -- The component `w = g - c qd` is orthogonal to `qd`, hence to `ker ℓ`.
  obtain ⟨w, hw⟩ : ∃ w : B0010.XG, w = g - c • qd := ⟨_, rfl⟩
  have hqw : inner ℂ qd w = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hc, div_mul_cancel₀ _ hden, sub_self]
  have hlw : l w = 0 := (hqd w).trans hqw
  have hgw : inner ℂ g w = 0 := hperp w hlw
  have hwqd : inner ℂ w qd = 0 := inner_eq_zero_symm.1 hqw
  have hwg : inner ℂ w g = 0 := inner_eq_zero_symm.1 hgw
  have hww : inner ℂ w w = 0 := by
    have e : inner ℂ w w = inner ℂ w g - c * inner ℂ w qd := by
      rw [← inner_smul_right, ← inner_sub_right, ← hw]
    rw [e, hwg, hwqd, mul_zero, sub_zero]
  have hw0 : w = 0 := inner_self_eq_zero.1 hww
  rw [hw] at hw0
  exact sub_eq_zero.1 hw0

end UnforcedLeray.Short.PartI
