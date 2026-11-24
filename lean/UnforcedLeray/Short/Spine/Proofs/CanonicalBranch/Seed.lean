import UnforcedLeray.Short.Spine.Sub.SP_CAN
import UnforcedLeray.Short.PartI.Compose
import UnforcedLeray.Short.PartI.Tasks.AdjointKernelOneDim

/-!
# Spine, task `Spine:SP-CAN`, bridge 1: the whole-line mode is a Part I seed

Source of record: `the November 2 reference manuscript`, `prop:short-gaussian-seed`
(lines 592-624; "The same `λ` is the sole growing spectral value of `L_0` on `X_G`" at line 602).
The Prop `WholeLineModeIsSeed` is defined in `Short/Spine/Sub/SP_CAN.lean`.

Proof. Let `(lam₀, q₀, ℓ₀)` be a Part I seed triple (`PartI.seedXGExists`).
* `lamMode c = -2ic` has real part `2 c.im > 0`, and `qMode hF ≠ 0` since `⟪qdagMode hF, qMode hF⟫ = 1`.
* `qMode hF` and `q₀` are eigenvectors of `L₀` with eigenvalues of positive real part, so the
  uniqueness theorem `Planar.L0_eigen_unique` gives `lamMode c = lam₀` and `qMode hF = μ • q₀`.
* `qdagMode hF` is an adjoint eigenvector for `conj lam₀` (from `inner_qdagMode_L0`). With the
  Riesz representative `qd₀` of `ℓ₀`, `PartI.adjoint_eigenvector_unique` gives `qdagMode hF = κ • qd₀`.
* The normalization `⟪qdagMode hF, qMode hF⟫ = 1` gives `conj κ * μ = 1`. Hence the rank-one
  projections `rankOneProj (innerSL ℂ (qdagMode hF)) (qMode hF)` and `rankOneProj ℓ₀ q₀` agree, and
  the simple spectral projection property transfers from the seed triple.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.Cons.G3b

/-- **Bridge 1** (lines 593-609, 602): the whole-line mode `(c, F)` gives a Part I seed triple
`(lamMode c, qMode hF, innerSL ℂ (qdagMode hF))`. -/
theorem wholeLineModeIsSeed : UnforcedLeray.Short.Spine.WholeLineModeIsSeed := by
  intro c F hF
  -- (1) `Re λ = 2 Im c > 0`.
  have hre : 0 < (lamMode c).re := by
    have him : 0 < c.im := hF.mode.upper_half_plane
    have e : (lamMode c).re = 2 * c.im := by
      simp [lamMode]
    rw [e]
    linarith
  -- (2) `q ≠ 0`, since `⟪q†, q⟫ = 1`.
  have hq0 : qMode hF ≠ 0 := by
    intro h0
    have h1 := inner_qdagMode_qMode hF
    rw [h0, inner_zero_right] at h1
    exact zero_ne_one h1
  -- (3) the eigen equation on `X_G`.
  have heig : UnforcedLeray.Planar.L0 (qMode hF) = lamMode c • qMode hF := L0_qMode hF
  -- (4) a Part I seed triple (line 593).
  obtain ⟨lam₀, h₀, hh₀, ℓ₀, hI₀⟩ :=
    (UnforcedLeray.Short.PartI.seedXGExists : UnforcedLeray.Short.PartI.SeedXGExists)
  set q₀ : UnforcedLeray.B0010.XG := hh₀.toLp h₀ with hq₀def
  -- (5) `λ = lam₀` and `q = μ q₀` (uniqueness of the eigenline in `{Re z > 0}`, line 602).
  obtain ⟨hlam, μ, hμ⟩ :=
    UnforcedLeray.Planar.L0_eigen_unique hI₀.re_pos hre hI₀.eigen heig hI₀.ne_zero hq0
  -- (6) `qdagMode hF` is an adjoint eigenvector for `conj lam₀`.
  have hL : ∀ v : UnforcedLeray.B0010.XG,
      inner ℂ (qdagMode hF) (UnforcedLeray.Planar.L0 v) = lamMode c * inner ℂ (qdagMode hF) v :=
    fun v => inner_qdagMode_L0 hF v
  have hadj : ContinuousLinearMap.adjoint UnforcedLeray.Planar.L0 (qdagMode hF) =
      (starRingEnd ℂ) lam₀ • qdagMode hF := by
    apply ext_inner_right ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left, starRingEnd_self_apply, hL v,
      hlam]
  -- (7) the Riesz representative `qd₀` of `ℓ₀`, and `qdagMode hF = κ • qd₀` by simplicity.
  obtain ⟨qd₀, hqd₀⟩ : ∃ qd₀ : UnforcedLeray.B0010.XG,
      ∀ f : UnforcedLeray.B0010.XG, ℓ₀ f = inner ℂ qd₀ f :=
    ⟨(InnerProductSpace.toDual ℂ UnforcedLeray.B0010.XG).symm ℓ₀,
      fun f => (InnerProductSpace.toDual_symm_apply).symm⟩
  obtain ⟨κ, hκ⟩ := UnforcedLeray.Short.PartI.adjoint_eigenvector_unique hI₀ hqd₀ hadj
  -- (8) normalization: `conj κ * μ = 1`.
  have hκμ : (starRingEnd ℂ) κ * μ = 1 := by
    have h1 := inner_qdagMode_qMode hF
    rw [hκ, hμ, inner_smul_left, inner_smul_right, ← hqd₀, hI₀.ell_q, mul_one] at h1
    exact h1
  -- (9) the two rank-one projections agree.
  have hP : UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ (qdagMode hF)) (qMode hF) =
      UnforcedLeray.Infra.Dunford.rankOneProj ℓ₀ q₀ := by
    ext x
    rw [UnforcedLeray.Infra.Dunford.rankOneProj_apply, UnforcedLeray.Infra.Dunford.rankOneProj_apply,
      innerSL_apply_apply, hκ, inner_smul_left, ← hqd₀ x, hμ, smul_smul]
    have hc : (starRingEnd ℂ) κ * ℓ₀ x * μ = ℓ₀ x := by
      linear_combination (ℓ₀ x) * hκμ
    rw [hc]
  -- (10) assemble the seed triple.
  have hell : innerSL ℂ (qdagMode hF) (qMode hF) = 1 := by
    rw [innerSL_apply_apply]
    exact inner_qdagMode_qMode hF
  have hproj : UnforcedLeray.Infra.Dunford.IsSimpleSpectralProj UnforcedLeray.Planar.L0
      (UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ (qdagMode hF)) (qMode hF))
      (lamMode c) := by
    rw [hP, hlam]
    exact hI₀.proj
  exact ⟨hre, hq0, heig, hell, hproj⟩

end UnforcedLeray.Short.Spine
