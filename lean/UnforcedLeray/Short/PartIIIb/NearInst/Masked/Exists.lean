import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearSolver
import UnforcedLeray.Short.PartIIb.Compose

/-!
# `MaskedNearExists` from its lemmas (source 1675-1690, 3905-3914)

Source of record: `the November 2 reference manuscript`.

At a level `p` of the regime with `ν` small (so that `ε ≤ 1` and `P = 2εc ≤ 1`):

* `PartIIa.NearStressMapExists` (`near:free-energy`, 1678-1690) gives the complex stress map
  `S'_ε` of `T_ε` (`P = p.period`);
* `StressMapReal` makes it real on real tensors, so its real form
  `realForm S'_ε = reH ∘ S'_ε ∘ cplxT ∘ zsumL` has the pin `IsStressTransport`
  (`isStressTransport_realForm`, using the change of variables `CellPtHT`, `CellPtInvH`,
  `CellPtH`);
* `FarMaskExists` gives `S_far` with the pin `IsFarMask` (3905-3912);
* `S_N = S_ε - S_far` (3909).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete

/-- `ε ≤ 1` in the regime. -/
theorem eps_le_one_of_regime {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) : p.ε ≤ 1 := by
  rw [hreg.eps_eq]
  apply Real.exp_le_one_iff.2
  have hd : 0 < d := lt_of_lt_of_le hreg.dm_pos hreg.dm_le
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) p.ν_pos.le

/-- `P = 2εc ≤ 1` for small `ν` in the regime. -/
theorem exists_period_le_one {dm : ℝ} (hdm : 0 < dm) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (p : Params) (d dp : ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.period ≤ 1 := by
  obtain ⟨ν₁, hν₁, hsmall⟩ := ns_small (2 * dm) (by positivity) 2 2 1 one_pos
  refine ⟨ν₁, hν₁, fun p d dp hreg hν => ?_⟩
  apply UnforcedLeray.Short.IIb.period_le_one_of hreg
  have h := hsmall p.ν p.ν_pos hν
  have e2 : -(2 * dm) / (2 * p.ν) = -dm / p.ν := by
    rw [show -(2 * dm) = 2 * (-dm) by ring, mul_div_mul_left _ _ (two_ne_zero)]
  rw [e2, inv_pow] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact h

/-- **`MaskedNearExists`** (source 1675-1690, 3905-3914) from the existence of the complex stress
map (`PartIIa.NearStressMapExists`), its reality (`StressMapReal`), the change of variables of the
cell recentring and the far kernel realization (`FarMaskExists`). -/
theorem maskedNearExists_of (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hR : StressMapReal) (hT : ∀ c : ℝ, 0 < c → CellPtHT c)
    (hH : ∀ c : ℝ, 0 < c → CellPtInvH c) (hH' : ∀ c : ℝ, 0 < c → CellPtH c)
    (hF : FarMaskExists) : MaskedNearExists := by
  intro Kset _ hKsub mZ hmZ b δ _ _ hδ dm dp hdm
  obtain ⟨ν₀, hν₀, hper⟩ := exists_period_le_one hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν ρb hρ μ hμ => ?_⟩
  have hμ' : μ ∈ Ioo (0 : ℝ) (1 / 4) := hKsub hμ
  have hε1 : p.ε ≤ 1 := eps_le_one_of_regime hreg
  have hP1 : p.period ≤ 1 := hper p d dp hreg hν
  obtain ⟨C, _, hNS⟩ := hN
  have hμn : ‖(μ : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ'.1]
    exact hμ'.2.le
  have hμr : (1 / 4 : ℝ) ≤ (μ : ℂ).re + 1 / 4 := by
    rw [Complex.ofReal_re]
    linarith [hμ'.1]
  obtain ⟨⟨S', hS', -⟩, -⟩ := hNS p.ν p.c (1 / 4) (1 / 4) p.ν_pos p.c_pos (by norm_num) p.ε
    p.ε_pos hε1 p.period rfl hP1 (μ : ℂ) hμn hμr
  have hreal : IsRealStress p.c S' :=
    hR p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl μ (by linarith [hμ'.1]) S' hS'
  have htr := isStressTransport_realForm hmZ hρ (hT p.c p.c_pos) (hH p.c p.c_pos)
    (hH' p.c p.c_pos) S' hreal
  obtain ⟨Sf, hSf⟩ := hF p.c mZ ρb p.R p.ν δ (p.ε ^ (-b)) μ p.c_pos hmZ hρ p.R_pos p.ν_pos hδ
    (Real.rpow_pos_of_pos p.ε_pos _) (by linarith [hμ'.1])
  exact ⟨realForm p.c mZ ρb hmZ hρ (hT p.c p.c_pos) (hH p.c p.c_pos) S' - Sf,
    realForm p.c mZ ρb hmZ hρ (hT p.c p.c_pos) (hH p.c p.c_pos) S', Sf, S', hS', htr, hSf, rfl⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
