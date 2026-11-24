import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Sub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegularSeq
import UnforcedLeray.Cons.C03Background.RawLift

/-!
# Organizer: the raw sup bound from the train bounds (task `PartIII-b:C/rep/8/2/pres/4/2/1/1/org`)

Source `the November 2 reference manuscript`:
2043-2046 (`V_0 = U_raw`), 2715-2725 (`sup √s W|v| ≤ P_ν`, `W ≥ 1`), 5461-5463
(`U_raw = √s(v + εHe_z)`, `H` with finite weighted train bounds), 5130-5139 (`P_ν` a fixed polynomial
in `ν⁻¹`), 1205-1225 (the lift is smooth through the axis).

`rawU = Params.raw = axisExt (Nv R (rawProfile ε v ψ))`.  Off the axis `|U_raw| = √s |b_raw|` at the
chart point, `b_raw = v + εH e_z`; on the axis it is a limit of off-axis values.  So the sup bound
follows from (i) `√s|v| ≤ P_ν`, (ii) `√s ε|H| ≤ P_ν` (both for the train of the level at all ages
`s > 0`) and (iii) the continuity of the axis extension.  All three are needed only for large `n`
(`RawSupBound` is an `∀ᶠ n` statement), so (iii) is taken in its eventual form, which is what the
Part I standing hypotheses (437-467, valid for `ν ≤ ν₀`) supply: `rawAxisCont_eventually_of`
(`Axis.lean`, task `pres/4/2/1/1/3`, source 1205-1225).
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RawSupOrg

/-- **Weighted sup bound of the train velocity** (source 2715-2725: `sup √s W|v| ≤ P_ν`, `W ≥ 1`):
for large `n`, `√s |v(s, z)| ≤ Cν^{-k}` at every age `s > 0` and plane point `z` of the train of
level `n`. -/
def VelWeightedSup (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, 0 < s → ∀ z : UnforcedLeray.Cyl.Plane,
    Real.sqrt s * ‖(D.train n).v s z‖ ≤ C * (D.level n).ν⁻¹ ^ k

/-- **Weighted sup bound of the raised stream** (source 5461-5463: `U_raw = √s(v + εHe_z)` with `H`
having finite weighted train bounds, `H = (1-K_age)ψ`, 2076): for large `n`,
`√s · ε |H(s, ξ, η)| ≤ Cν^{-k}` at every age `s > 0` and plane point. -/
def RaisedWeightedSup (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ (s ξ η : ℝ), 0 < s →
    Real.sqrt s * ((D.level n).ε *
      |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s ξ η|) ≤ C * (D.level n).ν⁻¹ ^ k

end RawSupOrg

open RawSupOrg

/-- The sup bound of the raw background from the two weighted train bounds and the continuity of
the axis extension at every large level (source 2715-2725, 1205-1225). -/
theorem rawSupBound_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : VelWeightedSup D) (h2 : RaisedWeightedSup D)
    (h3 : ∀ᶠ n : ℕ in atTop, RawAxisContinuous D.Pl (D.level n)) :
    RawSupBound D := by
  obtain ⟨C1, k1, hA⟩ := h1
  obtain ⟨C2, k2, hB⟩ := h2
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  refine ⟨|C1| + |C2|, max k1 k2, ?_⟩
  filter_upwards [hA, hB, hν1, h3] with n hA hB hν hax τ y
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have ha : (1 : ℝ) ≤ (D.level n).ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hν⟩
  set a := (D.level n).ν⁻¹ with hadef
  have hapos : 0 < a := by linarith
  -- the bound on the off-axis points
  have hoff : ∀ y : Space, y ∉ axis →
      ‖rawU D.Pl (D.level n) τ y‖ ≤ (|C1| + |C2|) * a ^ (max k1 k2) := by
    intro y hy
    have hε := (D.level n).ε_pos
    have hR : ((D.level n).ε⁻¹) ≠ 0 := (inv_pos.2 hε).ne'
    have hs : 0 < age (D.level n).ε⁻¹ y := age_pos hR hy
    have e : rawU D.Pl (D.level n) τ y = Nv (D.level n).ε⁻¹
        (UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v (D.train n).ψ) τ y :=
      ((D.level n).params D.Pl).raw_eq_off_axis τ y hy
    rw [e, norm_Nv _ _ _ hy]
    set s := age (D.level n).ε⁻¹ y
    set z := (chart (D.level n).ε⁻¹ τ y).2 with hz
    have hchart : (chart (D.level n).ε⁻¹ τ y) = (s, z) := rfl
    rw [hchart]
    have hp : ‖UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v (D.train n).ψ (s, z)‖
        ≤ ‖(D.train n).v s z‖ + (D.level n).ε *
          |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s z.1 z.2| := by
      unfold UnforcedLeray.Cons.C03.rawProfile
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, PiLp.norm_single, norm_one, Real.norm_eq_abs, mul_one, abs_mul,
        abs_of_pos hε]
    have h1 := hA s hs z
    have h2 := hB s z.1 z.2 hs
    have hk1 : a ^ k1 ≤ a ^ (max k1 k2) := pow_le_pow_right₀ ha (le_max_left _ _)
    have hk2 : a ^ k2 ≤ a ^ (max k1 k2) := pow_le_pow_right₀ ha (le_max_right _ _)
    have hsq := Real.sqrt_nonneg s
    calc Real.sqrt s * ‖UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v
            (D.train n).ψ (s, z)‖
        ≤ Real.sqrt s * (‖(D.train n).v s z‖ + (D.level n).ε *
          |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s z.1 z.2|) :=
          mul_le_mul_of_nonneg_left hp hsq
      _ = Real.sqrt s * ‖(D.train n).v s z‖ + Real.sqrt s * ((D.level n).ε *
          |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s z.1 z.2|) := by ring
      _ ≤ C1 * a ^ k1 + C2 * a ^ k2 := add_le_add h1 h2
      _ ≤ |C1| * a ^ k1 + |C2| * a ^ k2 :=
          add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
            (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      _ ≤ |C1| * a ^ (max k1 k2) + |C2| * a ^ (max k1 k2) :=
          add_le_add (mul_le_mul_of_nonneg_left hk1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hk2 (abs_nonneg _))
      _ = (|C1| + |C2|) * a ^ (max k1 k2) := by ring
  by_cases hy : y ∈ axis
  · -- axis: limit of off-axis values along `y + (m+1)⁻¹ e₀`
    have hlim := hax τ y hy
    refine le_of_tendsto hlim.norm (Eventually.of_forall fun m => hoff _ ?_)
    intro hm
    have h0 := hm.1
    have h1 := hy.1
    simp [coordinateVector] at h0
    have : ((m : ℝ) + 1)⁻¹ ≠ 0 := by positivity
    simp_all
  · exact hoff y hy

end UnforcedLeray.Short.PartIIIb.Concrete
