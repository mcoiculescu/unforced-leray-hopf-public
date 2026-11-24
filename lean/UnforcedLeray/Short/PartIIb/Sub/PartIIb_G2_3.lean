import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2
import UnforcedLeray.Short.PartIIb.Sub.G4_3_org

/-!
# `PartII-b:G2/3` decomposition: young and late bounds for the flat operator `K_0`

Source: `the November 2 reference manuscript` lines
2439-2445 (`v = O(P_nu/s)`, `Dv = O(P_nu/s^{3/2})` paired with the free `sqrt s Db_0` graph bound;
smooth inlet coefficients at the young end).
Lemmas: `FlatNormTransfer`, `FlatKYoungProfile`, `FlatKLateProfile`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete

/-- Norm transfer (lines 2436-2445): for `c > 0`, measurable `A`, `g : HpR c`, the indicator norm
`hpIndNorm c A g` is the real part of `hNorm c bgp (1_A * toProf c g)`, and `‖g‖ = hNorm (toProf g)`. -/
def FlatNormTransfer : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (A : Set Coord), MeasurableSet A → ∀ g : HpR c,
    hpIndNorm c A g = (hNorm c bgp (A.indicator (toProf c g))).toReal ∧
    hNorm c bgp (toProf c g) = ENNReal.ofReal ‖g‖

/-- Young bound for the flat interaction profile (SP 2443-2445): smooth inlet coefficients
(train `v`, `Dv` bounded by `P_nu` for `s < 1`) with the free graph bound. -/
def FlatKYoungProfile : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ C_flat : ℝ, 0 < C_flat →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        (∀ F : CProf, InHr p.c bgp F →
          ∃ b, InFlatClass p.c bgp b ∧ IsFlatResponse p.ν 0 F b ∧
            GraphBound p.ν p.c bgp 0 C_flat F b ∧
            ∀ b', InFlatClass p.c bgp b' → IsFlatResponse p.ν 0 F b' → b' =ᵐ[hMeas p.c bgp] b) →
        ∀ F b gq gη : CProf, InHr p.c bgp F → InFlatClass p.c bgp b → IsFlatResponse p.ν 0 F b →
          HasWeakVec vQ0 dZero b gq → HasWeakVec vEta dZero b gη →
          ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
            hNorm p.c bgp ((youngAgeSet σ).indicator (flatK p.train b gq gη)) ≤
              ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * Real.sqrt σ) * hNorm p.c bgp F

/-- Late bound for the flat interaction profile (SP 2439-2442): `|v| ≤ P/s`, `|Dv| ≤ P/s^{3/2}`
for `s ≥ 1` with the free graph bound on `b, √s Db`. -/
def FlatKLateProfile : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ C_flat : ℝ, 0 < C_flat →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        (∀ F : CProf, InHr p.c bgp F →
          ∃ b, InFlatClass p.c bgp b ∧ IsFlatResponse p.ν 0 F b ∧
            GraphBound p.ν p.c bgp 0 C_flat F b ∧
            ∀ b', InFlatClass p.c bgp b' → IsFlatResponse p.ν 0 F b' → b' =ᵐ[hMeas p.c bgp] b) →
        ∀ F b gq gη : CProf, InHr p.c bgp F → InFlatClass p.c bgp b → IsFlatResponse p.ν 0 F b →
          HasWeakVec vQ0 dZero b gq → HasWeakVec vEta dZero b gη →
          ∀ S : ℝ, 1 ≤ S →
            hNorm p.c bgp ((lateAgeSet S).indicator (flatK p.train b gq gη)) ≤
              ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * S ^ (-(1 / 2 : ℝ))) * hNorm p.c bgp F

theorem flatK0opYoungLateBounds_of (hT : FlatNormTransfer) (hY : FlatKYoungProfile)
    (hL : FlatKLateProfile) : FlatK0opYoungLateBounds := by
  intro dm dp hdm Cf hCf
  obtain ⟨C1, k1, ν1, hC1, hν1, H1⟩ := hY dm dp hdm Cf hCf
  obtain ⟨C2, k2, ν2, hC2, hν2, H2⟩ := hL dm dp hdm Cf hCf
  refine ⟨max C1 C2, max k1 k2, min (min ν1 ν2) 1, lt_max_of_lt_left hC1, lt_min (lt_min hν1 hν2) one_pos, ?_⟩
  intro p d hp hν hF K0 hK0
  have hc : 0 < p.c := p.c_pos
  have hν0 : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2 : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hC : ∀ (Ci : ℝ) (ki : ℕ), 0 < Ci → Ci ≤ max C1 C2 → ki ≤ max k1 k2 →
      Ci * (p.ν ^ ki)⁻¹ ≤ max C1 C2 * (p.ν ^ max k1 k2)⁻¹ := fun Ci ki hCi h1 h2 =>
    mul_le_mul h1 (by rw [inv_le_inv₀ (pow_pos hν0 ki) (pow_pos hν0 _)]
                      exact pow_le_pow_of_le_one hν0.le hν3 h2)
      (inv_nonneg.2 (pow_pos hν0 _).le) (hC1.trans_le (le_max_left _ _)).le
  have hkey : ∀ f : HpR p.c, ∀ (A : Set Coord), MeasurableSet A → ∀ X : ℝ, 0 ≤ X →
      (∀ F b gq gη : CProf, InHr p.c bgp F → InFlatClass p.c bgp b → IsFlatResponse p.ν 0 F b →
          HasWeakVec vQ0 dZero b gq → HasWeakVec vEta dZero b gη →
          hNorm p.c bgp (A.indicator (flatK p.train b gq gη)) ≤
            ENNReal.ofReal X * hNorm p.c bgp F) →
      hpIndNorm p.c A (K0 f) ≤ X * ‖f‖ := by
    intro f A hA X hX hb
    obtain ⟨b, gq, gη, hbc, hresp, hq, he, hae⟩ := hK0 f
    obtain ⟨hTn, hTf⟩ := hT p.c hc A hA (K0 f)
    have hF0 := hb (toProf p.c f) b gq gη (inHr_toProf hc f) hbc hresp hq he
    have hind : A.indicator (toProf p.c (K0 f)) =ᵐ[hMeas p.c bgp]
        A.indicator (flatK p.train b gq gη) := by
      filter_upwards [hae] with x hx
      by_cases hxA : x ∈ A <;> simp [Set.indicator, hxA, hx]
    have hfn := (hT p.c hc A hA f).2
    rw [hTn]
    have hcg : hNorm p.c bgp (A.indicator (toProf p.c (K0 f))) =
        hNorm p.c bgp (A.indicator (flatK p.train b gq gη)) := eLpNorm_congr_ae hind
    rw [hcg]
    have h1 : (hNorm p.c bgp (A.indicator (flatK p.train b gq gη))).toReal ≤
        (ENNReal.ofReal X * hNorm p.c bgp (toProf p.c f)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by rw [hfn]; exact ENNReal.ofReal_ne_top)) hF0
    rw [hfn, ← ENNReal.ofReal_mul hX, ENNReal.toReal_ofReal (by positivity)] at h1
    exact h1
  have hm1 := hC C1 k1 hC1 (le_max_left _ _) (le_max_left _ _)
  have hm2 := hC C2 k2 hC2 (le_max_right _ _) (le_max_right _ _)
  have hM0 : 0 ≤ max C1 C2 * (p.ν ^ max k1 k2)⁻¹ :=
    mul_nonneg (hC1.trans_le (le_max_left _ _)).le (inv_nonneg.2 (pow_pos hν0 _).le)
  constructor
  · intro σ hσ hσ1 f
    have := hkey f (youngAgeSet σ) (measurableSet_youngAgeSet σ)
      (max C1 C2 * (p.ν ^ max k1 k2)⁻¹ * Real.sqrt σ) (mul_nonneg hM0 (Real.sqrt_nonneg _))
      (fun F b gq gη hFi hbi hri hqi hei => by
        refine (H1 p d hp hν1 hF F b gq gη hFi hbi hri hqi hei σ hσ hσ1).trans ?_
        gcongr)
    exact this
  · intro S hS f
    have hSp : 0 ≤ S ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have := hkey f (lateAgeSet S) (measurableSet_lateAgeSet S)
      (max C1 C2 * (p.ν ^ max k1 k2)⁻¹ * S ^ (-(1 / 2 : ℝ))) (mul_nonneg hM0 hSp)
      (fun F b gq gη hFi hbi hri hqi hei => by
        refine (H2 p d hp hν2 hF F b gq gη hFi hbi hri hqi hei S hS).trans ?_
        gcongr)
    exact this

end UnforcedLeray.Short.IIb
