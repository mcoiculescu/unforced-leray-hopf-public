import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_dec

/-!
# `PartIII-b:C/rep/5/1/org`: the far thin velocity split along `ageVel = (S_μ - S_N) + Y`

Source `the November 2 reference manuscript` 5569-5600, 5618-5619.  The per-bin
velocity estimate (5585-5593: logarithmic bins of width `h < δ/2`, radial gap `D_j ≍ R/√s_j`,
order-four kernel `L²` norm `C D_j^{-5/2}`, normalized velocity `≤ C ε^{3/2}(s_j^{1/2}+s_j^{3/4})‖T‖_{Z₁}`)
and the bin summation with `P_ν S^k` (5594-5600) bound the far-mask operator `S_μ - S_N` and the
stream transitions `Y = (wardOps).1` on thin sources, with the gain margins `γ/18` (late output) and
`γ/10` (early source) of 5601-5605 and the common bound `e^{(γ/10+ω_b+3m₀/2)/ν}` of 5618-5619.
Here the two components are stated separately; the assembly into `AgeVelThin` is proved.

**Correction (organizer `PartIII-b:C/rep/5/1/cancel/org`).**  The source never bounds `S_far` or `Y`
separately in the gain norms (the margins `γ/18`, `γ/10` are for the pieces of the SUM, 5594-5599,
5688-5689): on output ages `s ≤ 4/(5ν)` the young-old rectangle cancels exactly between the two
(4171-4199), and each alone contains it, of gained size `P_ν e^{γ/(6ν)}`.  So the leaves
`AgeVelSopThin`, `AgeVelWardThin` below are NOT source statements and are false in substance; they
are kept only because the generic implications of `…_5_1_2Org`/`…_5_1_2_4Org` mention them.  The
live route to `AgeVelThin` is `ageVelThin_of_pieces` in `PartIII-b_C_rep_5_1_cancelOrg.lean`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

/-- Far-mask part of the thin velocity (5569-5600): `‖(S_μ - S_N)(thinPart T)‖ ≤
P_ν e^{(γ/10+ω_b+3m₀/2)/ν}‖T‖`. -/
def AgeVelSopThinAt (D : SeqData) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖(Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
          (thinPart T)‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp ((gRate D.Pl / 10 + ωb + 3 * D.K.m0 / 2) / (D.level n).ν) * ‖T‖

/-- Stream-transition part of the thin velocity (5569-5600, 5618-5619): `‖Y(thinPart T)‖` with the
same bound. -/
def AgeVelWardThinAt (D : SeqData) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖(wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T)‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp ((gRate D.Pl / 10 + ωb + 3 * D.K.m0 / 2) / (D.level n).ν) * ‖T‖

end SeqData

/-- (Not a source statement, see the correction above.) Leaf (c1): far mask on thin sources, S-degree `k₀` chosen before `b` (`ω_b = k₀ b γ/3`). -/
def AgeVelSopThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    D.AgeVelSopThinAt ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- (Not a source statement, see the correction above.) Leaf (c2): stream transitions on thin sources. -/
def AgeVelWardThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    D.AgeVelWardThinAt ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- `ageVel = (S_μ - S_N) + Y`, so (c1), (c2) give `AgeVelThin`. -/
theorem ageVelThin_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : AgeVelSopThin Pl σ₀ mZ dm dp) (h2 : AgeVelWardThin Pl σ₀ mZ dm dp) :
    AgeVelThin Pl σ₀ mZ dm dp := by
  obtain ⟨k1, H1⟩ := h1
  obtain ⟨k2, H2⟩ := h2
  refine ⟨max k1 k2, fun D hPl hσ hmZ hst => ?_⟩
  have hb := hst.b_pos
  have hg := hst.gamma_pos
  have hmono : ∀ j : ℕ, j ≤ max k1 k2 →
      (j : ℝ) * D.K.b * (gRate D.Pl / 3) ≤ ((max k1 k2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) := by
    intro j hj
    have : (j : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := by exact_mod_cast hj
    have hbg : 0 ≤ D.K.b * (gRate D.Pl / 3) := by positivity
    nlinarith
  obtain ⟨C1, j1, e1⟩ := H1 D hPl hσ hmZ hst
  obtain ⟨C2, j2, e2⟩ := H2 D hPl hσ hmZ hst
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  set ω := ((max k1 k2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) with hω
  have m1 := hmono k1 (le_max_left _ _)
  have m2 := hmono k2 (le_max_right _ _)
  refine ⟨|C1| + |C2|, max j1 j2, ?_⟩
  filter_upwards [e1, e2, hν1] with n a1 a2 hν z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hν
  have hi : 1 ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hνp).2 hν1'
  have hP : ∀ j : ℕ, 0 ≤ (D.level n).ν⁻¹ ^ j := fun j => by positivity
  have pj1 : (D.level n).ν⁻¹ ^ j1 ≤ (D.level n).ν⁻¹ ^ (max j1 j2) :=
    pow_le_pow_right₀ hi (le_max_left _ _)
  have pj2 : (D.level n).ν⁻¹ ^ j2 ≤ (D.level n).ν⁻¹ ^ (max j1 j2) :=
    pow_le_pow_right₀ hi (le_max_right _ _)
  have ex1 : Real.exp ((gRate D.Pl / 10 + (k1 : ℝ) * D.K.b * (gRate D.Pl / 3) +
        3 * D.K.m0 / 2) / (D.level n).ν) ≤
        Real.exp ((gRate D.Pl / 10 + ω + 3 * D.K.m0 / 2) / (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    linarith
  have ex2 : Real.exp ((gRate D.Pl / 10 + (k2 : ℝ) * D.K.b * (gRate D.Pl / 3) +
        3 * D.K.m0 / 2) / (D.level n).ν) ≤
        Real.exp ((gRate D.Pl / 10 + ω + 3 * D.K.m0 / 2) / (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    linarith
  have b1 := lift (a1 z hz T) (le_refl |C1|)
    (hP j1) pj1 (Real.exp_pos _).le ex1 (norm_nonneg T)
  have b2 := lift (a2 z hz T) (le_refl |C2|)
    (hP j2) pj2 (Real.exp_pos _).le ex2 (norm_nonneg T)
  have key : ageVel D.Pl D.K (D.level n) (D.mu n z) (thinPart T) =
      (Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
          (thinPart T) +
        (wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T) := rfl
  rw [key]
  refine (norm_add_le _ _).trans ?_
  linarith [b1, b2]

end UnforcedLeray.Short.PartIIIb.Concrete
