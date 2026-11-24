import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import UnforcedLeray.Lib.Semigroups.Dunford.Deflation

/-!
# Compact perturbations of an invertible part: eigenvalues and simple spectral projections

Abstract layer of the INF10 targets G-2 and G-4 (scoping note

plan `scoping/README.md` §5, Wave 3, block 3F PLAN2). Manuscript (`paper/main.tex`): lines
1424–1437 (units `B0087`, `B0088`: for `Re z > 0`, `z + 2iΩ` is invertible and
`z - L₀ = (z + 2iΩ)(I - (z + 2iΩ)⁻¹ 2ikR)`, a compact perturbation of the identity), and lines
1390–1400 (unit `B0083`: the growing spectrum consists of isolated, algebraically simple
eigenvalues).

The manuscript cites the holomorphic Fredholm theorem (Glück, Thm. 6.1.18). Here only Mathlib's
Fredholm alternative for one compact operator is used
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`):

* `exists_eigen_of_mem_spectrum`: if `z - T` is invertible and `K` is compact, every
  `z ∈ σ(T + K)` is an eigenvalue of `T + K`;
* `isSimpleSpectralProj_of_compact`: if moreover, on an open set `U` where `z - T` is invertible,
  the only eigenvalue of `T + K` is `z₀`, its eigenvectors are the multiples of `q`, and `ℓ` is a
  left eigenvector with `ℓ q = 1`, then `x ↦ ℓ(x) q` is the spectral projection of a simple
  isolated eigenvalue (`Dunford.IsSimpleSpectralProj`, the Laurent form of restructuring R2 of the
  vendored Dunford layer, `Lib/Semigroups/Dunford/Defs.lean`). The Laurent limit is
  `(z₀ - Ã)⁻¹(1 - P)` for the deflated operator `Ã = T + K - P`, which has no eigenvalue at `z₀`.

Namespace `UnforcedLeray.Infra.CompactPerturb`. Nothing here is specific to the manuscript.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Infra.CompactPerturb

open UnforcedLeray.Infra.Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem algebraMap_apply (z : ℂ) (x : X) : (algebraMap ℂ (X →L[ℂ] X) z) x = z • x := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

variable [CompleteSpace X]

/-- **Fredholm alternative for a compact perturbation of an invertible part.** If `z - T` is
invertible and `K` is compact, every spectral point `z` of `T + K` is an eigenvalue. -/
theorem exists_eigen_of_mem_spectrum {T K : X →L[ℂ] X} (hK : IsCompactOperator K) {z : ℂ}
    (hT : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - T)) (hz : z ∈ spectrum ℂ (T + K)) :
    ∃ w : X, w ≠ 0 ∧ (T + K) w = z • w := by
  set S : X →L[ℂ] X := algebraMap ℂ (X →L[ℂ] X) z - T with hS
  set R : X →L[ℂ] X := Ring.inverse S with hR
  have hSR : S * R = 1 := Ring.mul_inverse_cancel S hT
  have hRK : IsCompactOperator (R ∘L K) := hK.clm_comp R
  rcases hRK.hasEigenvalue_or_mem_resolventSet (one_ne_zero (α := ℂ)) with h | h
  · obtain ⟨w, hw⟩ := h.exists_hasEigenvector
    refine ⟨w, hw.2, ?_⟩
    have h1 : R (K w) = w := by
      have := hw.apply_eq_smul
      simpa using this
    have h2 : S (R (K w)) = K w := by
      rw [← ContinuousLinearMap.mul_apply, hSR, ContinuousLinearMap.one_apply]
    rw [h1, hS, ContinuousLinearMap.sub_apply, algebraMap_apply] at h2
    rw [ContinuousLinearMap.add_apply, ← h2]
    abel
  · exfalso
    rw [spectrum.mem_resolventSet_iff] at h
    apply (spectrum.mem_iff.1 hz)
    have hfac : algebraMap ℂ (X →L[ℂ] X) z - (T + K) =
        S * (algebraMap ℂ (X →L[ℂ] X) 1 - R ∘L K) := by
      have e : (R ∘L K : X →L[ℂ] X) = R * K := rfl
      rw [e, map_one, mul_sub, mul_one, ← mul_assoc, hSR, one_mul, hS]
      abel
    rw [hfac]
    exact hT.mul h

/-- The rank-one operator `x ↦ ℓ(x) q` is compact. -/
theorem isCompactOperator_rankOneProj (ℓ : X →L[ℂ] ℂ) (q : X) :
    IsCompactOperator (rankOneProj ℓ q) := by
  have h := (isCompactOperator_of_locallyCompactSpace_dom ℓ).clm_comp
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) q)
  have e : ⇑(rankOneProj ℓ q) = ⇑(ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) q) ∘ ⇑ℓ := by
    ext x
    simp [rankOneProj]
  rw [e]
  exact h

/-- **Simple isolated eigenvalue of a compact perturbation** (abstract form of target G-4). Let
`U` be open, `z - T` invertible for `z ∈ U`, `K` compact, `A = T + K`. Suppose `z₀ ∈ U`,
`A q = z₀ q`, `ℓ ∘ A = z₀ ℓ`, `ℓ q = 1`, and every eigenvector of `A` with eigenvalue in `U` has
eigenvalue `z₀` and is a multiple of `q`. Then `P = ℓ(·) q` is the spectral projection of the
simple isolated eigenvalue `z₀` (`IsSimpleSpectralProj`), with Laurent limit
`(z₀ - Ã)⁻¹(1 - P)`, `Ã = A - P`. -/
theorem isSimpleSpectralProj_of_compact {T K : X →L[ℂ] X} (hK : IsCompactOperator K)
    {U : Set ℂ} (hU : IsOpen U) (hTU : ∀ z ∈ U, IsUnit (algebraMap ℂ (X →L[ℂ] X) z - T))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {q : X} (hq : (T + K) q = z₀ • q) {ℓ : X →L[ℂ] ℂ}
    (hℓ : ℓ.comp (T + K) = z₀ • ℓ) (hℓq : ℓ q = 1)
    (heig : ∀ z ∈ U, ∀ w : X, w ≠ 0 → (T + K) w = z • w → z = z₀ ∧ ∃ μ : ℂ, w = μ • q) :
    IsSimpleSpectralProj (T + K) (rankOneProj ℓ q) z₀ := by
  set A : X →L[ℂ] X := T + K with hA
  set P : X →L[ℂ] X := rankOneProj ℓ q with hP
  have hPP : P * P = P := rankOneProj_mul_self hℓq
  have hAP : A * P = z₀ • P := mul_rankOneProj hq
  have hPA : P * A = z₀ • P := rankOneProj_mul hℓ
  -- the deflated operator `Ã = A - P`
  set Ad : X →L[ℂ] X := A - P with hAd
  have hAdP : Ad * P = (z₀ - 1) • P := by
    rw [hAd, sub_mul, hAP, hPP, sub_smul, one_smul]
  have hPAd : P * Ad = (z₀ - 1) • P := by
    rw [hAd, mul_sub, hPA, hPP, sub_smul, one_smul]
  have hz₀Ad : z₀ ∈ resolventSet ℂ Ad := by
    by_contra hcon
    have hmem : z₀ ∈ spectrum ℂ (T + (K - P)) := by
      have e : T + (K - P) = Ad := by rw [hAd, hA]; abel
      rw [e]
      exact hcon
    obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum (hK.sub
      (isCompactOperator_rankOneProj ℓ q)) (hTU z₀ hz₀) hmem
    have e : T + (K - P) = Ad := by rw [hAd, hA]; abel
    rw [e] at hw
    -- `P w = 0`
    have hPw : P w = 0 := by
      have h1 : P (Ad w) = (z₀ - 1) • P w := by
        rw [← ContinuousLinearMap.mul_apply, hPAd, ContinuousLinearMap.smul_apply]
      rw [hw, map_smul] at h1
      have h2 : (1 : ℂ) • P w = 0 := by
        have : z₀ • P w - (z₀ - 1) • P w = 0 := by rw [h1, sub_self]
        rw [← sub_smul] at this
        simpa using this
      simpa using h2
    have hAw : A w = z₀ • w := by
      have : Ad w = A w - P w := rfl
      rw [hPw, sub_zero] at this
      rw [← this, hw]
    obtain ⟨-, μ, hμ⟩ := heig z₀ hz₀ w hw0 hAw
    have hℓw : ℓ w = 0 := by
      have h1 : P w = ℓ w • q := rankOneProj_apply ℓ q w
      rw [hPw] at h1
      have hq0 : q ≠ 0 := by
        intro h
        rw [h, map_zero] at hℓq
        exact zero_ne_one hℓq
      exact (smul_eq_zero.1 h1.symm).resolve_right hq0
    rw [hμ, map_smul, hℓq, smul_eq_mul, mul_one] at hℓw
    exact hw0 (by rw [hμ, hℓw, zero_smul])
  have hopen : IsOpen (resolventSet ℂ Ad) := spectrum.isOpen_resolventSet Ad
  have hev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ U ∧ z ∈ resolventSet ℂ Ad ∧ z ≠ z₀ := by
    have h1 : ∀ᶠ z in 𝓝[≠] z₀, z ∈ U := nhdsWithin_le_nhds (hU.mem_nhds hz₀)
    have h2 : ∀ᶠ z in 𝓝[≠] z₀, z ∈ resolventSet ℂ Ad :=
      nhdsWithin_le_nhds (hopen.mem_nhds hz₀Ad)
    have h3 : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := self_mem_nhdsWithin
    filter_upwards [h1, h2, h3] with z a b c
    exact ⟨a, b, c⟩
  -- the resolvent of `A` near `z₀`
  have hres : ∀ z, z ∈ resolventSet ℂ Ad → z ≠ z₀ →
      IsUnit (algebraMap ℂ (X →L[ℂ] X) z - A) ∧
        resolvent A z - (z - z₀)⁻¹ • P = resolvent Ad z * (1 - P) := by
    intro z hz hzz
    set S : X →L[ℂ] X := resolvent Ad z with hS
    have hu : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - Ad) := spectrum.mem_resolventSet_iff.1 hz
    have h1 : (algebraMap ℂ (X →L[ℂ] X) z - Ad) * S = 1 := Ring.mul_inverse_cancel _ hu
    have h2 : S * (algebraMap ℂ (X →L[ℂ] X) z - Ad) = 1 := Ring.inverse_mul_cancel _ hu
    have hzz' : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
    -- `S` commutes with `P`
    have hcomm : (algebraMap ℂ (X →L[ℂ] X) z - Ad) * P = P * (algebraMap ℂ (X →L[ℂ] X) z - Ad) := by
      rw [mul_sub, sub_mul, hAdP, hPAd, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        mul_smul_comm, one_mul, mul_one]
    have hSP : S * P = P * S := by
      calc S * P = S * (P * ((algebraMap ℂ (X →L[ℂ] X) z - Ad) * S)) := by rw [h1, mul_one]
        _ = S * (P * (algebraMap ℂ (X →L[ℂ] X) z - Ad)) * S := by simp only [mul_assoc]
        _ = S * ((algebraMap ℂ (X →L[ℂ] X) z - Ad) * P) * S := by rw [hcomm]
        _ = P * S := by rw [← mul_assoc S _ P, h2, one_mul]
    have hAsplit : algebraMap ℂ (X →L[ℂ] X) z - A = (algebraMap ℂ (X →L[ℂ] X) z - Ad) - P := by
      rw [hAd]; abel
    have hAPz : (algebraMap ℂ (X →L[ℂ] X) z - A) * P = (z - z₀) • P := by
      rw [sub_mul, hAP, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sub_smul]
    have hPAz : P * (algebraMap ℂ (X →L[ℂ] X) z - A) = (z - z₀) • P := by
      rw [mul_sub, hPA, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, sub_smul]
    set B : X →L[ℂ] X := S * (1 - P) + (z - z₀)⁻¹ • P with hB
    have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
    have hP1' : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
    have hright : (algebraMap ℂ (X →L[ℂ] X) z - A) * B = 1 := by
      rw [hB, mul_add, mul_smul_comm, hAPz, smul_smul, inv_mul_cancel₀ hzz', one_smul, hAsplit,
        sub_mul, ← mul_assoc, h1, one_mul, ← mul_assoc, ← hSP, mul_assoc, hP1, mul_zero, sub_zero]
      abel
    have e1 : (1 - P) * (algebraMap ℂ (X →L[ℂ] X) z - Ad) =
        (algebraMap ℂ (X →L[ℂ] X) z - Ad) * (1 - P) := by
      rw [sub_mul (1 : X →L[ℂ] X) P, mul_sub _ (1 : X →L[ℂ] X) P, one_mul, mul_one, hcomm]
    have hleft : B * (algebraMap ℂ (X →L[ℂ] X) z - A) = 1 := by
      have e2 : S * (1 - P) * ((algebraMap ℂ (X →L[ℂ] X) z - Ad) - P) = 1 - P := by
        rw [mul_sub, mul_assoc S (1 - P) P, hP1', mul_zero, sub_zero,
          mul_assoc S (1 - P), e1, ← mul_assoc, h2, one_mul]
      rw [hB, add_mul, smul_mul_assoc, hPAz, smul_smul, inv_mul_cancel₀ hzz', one_smul, hAsplit,
        e2]
      abel
    have hunit : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - A) :=
      ⟨⟨_, B, hright, hleft⟩, rfl⟩
    refine ⟨hunit, ?_⟩
    have hinv : resolvent A z = B := by
      unfold resolvent
      have := (Ring.inverse_mul_eq_iff_eq_mul _ (1 : X →L[ℂ] X) B hunit).2 hright.symm
      rwa [mul_one] at this
    rw [hinv, hB]
    abel
  refine ⟨hPP, hAP, hPA, ?_, ?_⟩
  · filter_upwards [hev] with z hz
    exact spectrum.mem_resolventSet_iff.2 (hres z hz.2.1 hz.2.2).1
  · refine ⟨resolvent Ad z₀ * (1 - P), ?_⟩
    have hcont : ContinuousAt (fun z => resolvent Ad z * (1 - P)) z₀ :=
      (IntegralAux.continuousAt_resolvent hz₀Ad).mul continuousAt_const
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with z hz
    exact ((hres z hz.2.1 hz.2.2).2).symm

end UnforcedLeray.Infra.CompactPerturb
