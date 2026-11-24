import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org

/-!
# Part II-b, `PartII-b:G2/1/org/C`: `PhysKOutExistsBound` from three leaves

`K_ε = s B_{U_raw} T_ε` (SP 2007-2010).  The late coefficient bound on `U_raw`
(SP 2432-2437) controls the Biot-Savart output pointwise by `b, Sb, √s Q b, √s ∂_η b`, whose norms
are bounded by the graph bound (SP 1912-1918).  Leaves:
* `PhysKOutCand`: an `H_p`-profile `g₀` with `IsKOut p b g₀` and the late norm bound (SP 2432-2437);
* `PhysHpRep`: every `H_p`-profile is represented by an element of `HpR` (the `Lp` class);
* `PhysKOutCongr`: `IsKOut` depends on the output only through its `hMeas`-a.e. class.
Composition: `physKOutExistsBound_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- (C1) Candidate output (SP 2432-2437, 2007-2010): a profile `g₀ ∈ H_p` with `IsKOut p b g₀`
and `‖g₀‖ ≤ CK ν^{-k} ‖F‖`, under the late coefficient bound and the graph bound. -/
def PhysKOutCand : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
  ∀ (C_late : ℝ) (k_late : ℕ) (C_phys : ℝ), 0 < C_late → 0 < C_phys →
    ∃ (ν₀ CK : ℝ) (k : ℕ), 0 < ν₀ ∧ 0 < CK ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        p.ε ≤ 1 → 2 * p.ε * p.c ≤ 1 →
        (∀ S : ℝ, 1 ≤ S → ∀ (τ : ℝ) (y : Space), (y ∈ Axi.axis ∨ S < Axi.age p.R y) →
          DifferentiableAt ℝ (p.raw τ) y ∧
          ‖p.raw τ y‖ + ‖fderiv ℝ (p.raw τ) y‖ ≤
            C_late * (p.ν ^ k_late)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε)) →
        ∀ F b : CProf, InHr p.c bgp F → InHr p.c bgp b → (∀ x i, (b x i).im = 0) →
          GraphBound p.ν p.c bgp p.ε C_phys F b →
          ∃ g₀ : CProf, InHr p.c bgp g₀ ∧ (∀ x i, (g₀ x i).im = 0) ∧ IsKOut p b g₀ ∧
            hNorm p.c bgp g₀ ≤ ENNReal.ofReal (CK * (p.ν ^ k)⁻¹) * hNorm p.c bgp F

/-- (C2) Every `H_p`-profile is represented by a class of `HpR`, with the same norm. -/
def PhysHpRep : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ g₀ : CProf, InHr c bgp g₀ → (∀ x i, (g₀ x i).im = 0) →
    ∃ g : HpR c, toProf c g =ᵐ[hMeas c bgp] g₀ ∧ ‖g‖ = (hNorm c bgp g₀).toReal

/-- (C3) `IsKOut` is invariant under `hMeas`-a.e. change of the output among `H_p`-profiles
(`InHr` is needed: off-cell perturbations have nonzero pairings). -/
def PhysKOutCongr : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp →
  ∀ (b g g' : CProf), InHr p.c bgp g → InHr p.c bgp g' → g =ᵐ[hMeas p.c bgp] g' →
    IsKOut p b g → IsKOut p b g'

theorem physKOutExistsBound_of (h1 : PhysKOutCand) (h2 : PhysHpRep) (h3 : PhysKOutCongr) :
    PhysKOutExistsBound := by
  intro dm dp hdm C_late k_late C_phys hCl hCp
  obtain ⟨ν₀, CK, k, hν₀, hCK, H⟩ := h1 dm dp hdm C_late k_late C_phys hCl hCp
  refine ⟨ν₀, CK, k, hν₀, hCK, ?_⟩
  intro p d hreg hν hε h2ε hlate F b hF hb hbr hG
  obtain ⟨g₀, hg₀, hr₀, hK, hn⟩ := H p d hreg hν hε h2ε hlate F b hF hb hbr hG
  obtain ⟨g, hge, hgn⟩ := h2 p.c p.c_pos g₀ hg₀ hr₀
  refine ⟨g, ?_, ?_⟩
  · exact h3 p d dm dp hreg b g₀ _ hg₀ (RespOp.inHr_toProf p.c_pos g) hge.symm hK
  · rw [hgn]
    have hFt := hF.finite
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFt.ne) hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal] at this
    · exact this
    · have := p.ν_pos
      positivity
end UnforcedLeray.Short.IIb
