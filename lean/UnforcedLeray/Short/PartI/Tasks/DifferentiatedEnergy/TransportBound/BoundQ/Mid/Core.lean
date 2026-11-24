import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1_3
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.DerivFinite

/-!
# Part I, task `PartI:T08/7/3/1/3/3`: `midCore_of_parts`

Source: `the November 2 reference manuscript` lines 352-358.
From the three-factor Hölder inequality `MidHolder3` and the word form of Gagliardo-Nirenberg
`MidGNWord`, prove the leaf `MidCore`. Exponents: `p = 2n/l₁`, `q = 2n/l₂`, `1/p + 1/q + 1/2 = 1`.
The first factor gives `J^{1/2}`, the GN bounds give `C·G^{1-l₁/n} J^{l₁/(2n)}` and
`C·G^{1-l₂/n} J^{l₂/(2n)}`; the exponents of `G` and `J` add to `1`.

Helper `midCore_memLp_word`: every word derivative of an admissible function lies in `L^p(cell)`
for `2 ≤ p < ∞`. It uses the sup bound `enorm_derivWord_le` (all four words are in `L²`, by the
`L²` part of `MidAdm`) and `memLp_of_memLp_two_of_enorm_le`, as in `cylDerivFinite_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

open UnforcedLeray
open UnforcedLeray.Short.PartI

/-- Every word derivative of an admissible function is in `L^p(cell)` for `2 ≤ p < ∞`. -/
theorem midCore_memLp_word {c G J : ℝ} {n : ℕ} {g : Cyl.Plane → ℝ} (hc : 1 ≤ c)
    (hg : MidAdm c G J n g) (w : List Bool) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p ≠ ⊤) :
    MemLp (B0151.derivWord w g) p (Cyl.cellμ c) := by
  obtain ⟨hf, hper, hL, -, -⟩ := hg
  have hc0 : 0 < c := by linarith
  have hfB : B0151.IsPeriodicQ c g := by
    intro q η
    exact hper (q, η)
  have hgM : ∀ v : List Bool, Measurable (B0151.derivWord v g) := fun v =>
    (B0151.contDiff_derivWord hf v).continuous.measurable
  have hgP : ∀ v : List Bool, Cyl.IsPeriodic c (B0151.derivWord v g) := by
    intro v z
    exact B0151.periodic_derivWord hfB v z.1 z.2
  have hB : ∀ v : List Bool, MemLp (B0151.derivWord v g) 2 (B0151.cellMeasure c) :=
    fun v => (memLp_cellMeasure_iff hc0 (hgM v) (hgP v) 2).2 (hL v)
  obtain ⟨K, hKtop, hKbd⟩ : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ z, ‖B0151.derivWord w g z‖ₑ ≤ K := by
    refine ⟨_, ?_, fun z => B0151.enorm_derivWord_le hc hf hfB w (hB w) (hB (true :: w))
      (hB (false :: w)) (hB (false :: true :: w)) z⟩
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
        ⟨(hB w).eLpNorm_lt_top.ne, (hB (true :: w)).eLpNorm_lt_top.ne⟩,
        (hB (false :: w)).eLpNorm_lt_top.ne⟩, (hB (false :: true :: w)).eLpNorm_lt_top.ne⟩)
  exact memLp_of_memLp_two_of_enorm_le (hL w) hKtop hKbd hp2 hpt

/-- **Target** `midCore_of_parts`: `MidCore` from `MidHolder3` and `MidGNWord`. -/
theorem midCore_of_parts : UnforcedLeray.Short.PartI.MidHolder3 → UnforcedLeray.Short.PartI.MidGNWord → UnforcedLeray.Short.PartI.MidCore := by
  intro hH hGNW n hn
  obtain ⟨C', hC', hG⟩ := hGNW n (by omega)
  refine ⟨C' * C', mul_nonneg hC' hC', ?_⟩
  intro c hc g₁ g₂ g₃ G J hG0 hJ0 H1 H2 H3 l₁ l₂ hl₁ hl₂ hsum u₁ u₂ u₃ hu₁ hu₂ hu₃
  obtain ⟨-, -, L1, -, J1⟩ := H1
  have hl1R : (1:ℝ) ≤ l₁ := by exact_mod_cast hl₁
  have hl2R : (1:ℝ) ≤ l₂ := by exact_mod_cast hl₂
  have hsumR : (l₁:ℝ) + l₂ = n := by exact_mod_cast hsum
  have hl1n : l₁ ≤ n := by omega
  have hl2n : l₂ ≤ n := by omega
  have hl1nR : (l₁:ℝ) ≤ n := by exact_mod_cast hl1n
  have hl2nR : (l₂:ℝ) ≤ n := by exact_mod_cast hl2n
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hl1pos : (0:ℝ) < l₁ := by linarith
  have hl2pos : (0:ℝ) < l₂ := by linarith
  have hnpos : (0:ℝ) < n := by linarith
  have hnne : (n:ℝ) ≠ 0 := hnpos.ne'
  have h2npos : (0:ℝ) < 2 * n := by linarith
  -- Exponents of the Hölder inequality.
  have hp1 : (1:ℝ) < 2 * (n:ℝ) / l₁ := by rw [one_lt_div hl1pos]; linarith
  have hq1 : (1:ℝ) < 2 * (n:ℝ) / l₂ := by rw [one_lt_div hl2pos]; linarith
  have hp2 : (2:ℝ) ≤ 2 * (n:ℝ) / l₁ := by rw [le_div_iff₀ hl1pos]; linarith
  have hq2 : (2:ℝ) ≤ 2 * (n:ℝ) / l₂ := by rw [le_div_iff₀ hl2pos]; linarith
  have hsplit : (l₁:ℝ) / (2 * n) + (l₂:ℝ) / (2 * n) = 1 / 2 := by
    rw [← add_div, hsumR, div_eq_iff h2npos.ne']
    ring
  have hsumP : 1 / (2 * (n:ℝ) / l₁) + 1 / (2 * (n:ℝ) / l₂) + 1 / 2 = 1 := by
    rw [one_div_div, one_div_div]
    linarith
  have eP2 : (2:ℝ≥0∞) ≤ ENNReal.ofReal (2 * (n:ℝ) / l₁) :=
    ((ENNReal.ofReal_ofNat 2).symm.le).trans (ENNReal.ofReal_le_ofReal hp2)
  have eQ2 : (2:ℝ≥0∞) ≤ ENNReal.ofReal (2 * (n:ℝ) / l₂) :=
    ((ENNReal.ofReal_ofNat 2).symm.le).trans (ENNReal.ofReal_le_ofReal hq2)
  -- Memberships.
  have ha : MemLp (B0151.derivWord u₁ g₁) 2 (Cyl.cellμ c) := L1 u₁
  have hb : MemLp (B0151.derivWord u₂ g₂) (ENNReal.ofReal (2 * (n:ℝ) / l₁)) (Cyl.cellμ c) :=
    midCore_memLp_word hc H2 u₂ eP2 ENNReal.ofReal_ne_top
  have hd : MemLp (B0151.derivWord u₃ g₃) (ENNReal.ofReal (2 * (n:ℝ) / l₂)) (Cyl.cellμ c) :=
    midCore_memLp_word hc H3 u₃ eQ2 ENNReal.ofReal_ne_top
  have hH' := hH c (B0151.derivWord u₁ g₁) (B0151.derivWord u₂ g₂) (B0151.derivWord u₃ g₃)
    (2 * (n:ℝ) / l₁) (2 * (n:ℝ) / l₂) hp1 hq1 hsumP ha hb hd
  -- Gagliardo-Nirenberg bounds for the second and third factor.
  have hG2 := hG c hc g₂ G J hG0 hJ0 H2 l₁ hl₁ hl1n u₂ hu₂
  have hG3 := hG c hc g₃ G J hG0 hJ0 H3 l₂ hl₂ hl2n u₃ hu₃
  have hBp : (∫ z in Cyl.cell c, |B0151.derivWord u₂ g₂ z| ^ (2 * (n:ℝ) / l₁)) ^
      (1 / (2 * (n:ℝ) / l₁)) ≤ C' * (G ^ (1 - (l₁:ℝ) / n) * J ^ ((l₁:ℝ) / (2 * n))) := by
    rw [one_div_div]
    exact hG2
  have hDq : (∫ z in Cyl.cell c, |B0151.derivWord u₃ g₃ z| ^ (2 * (n:ℝ) / l₂)) ^
      (1 / (2 * (n:ℝ) / l₂)) ≤ C' * (G ^ (1 - (l₂:ℝ) / n) * J ^ ((l₂:ℝ) / (2 * n))) := by
    rw [one_div_div]
    exact hG3
  -- Bounds on the first factor and nonnegativity.
  have hA0 : 0 ≤ ∫ z in Cyl.cell c, B0151.derivWord u₁ g₁ z * B0151.derivWord u₁ g₁ z :=
    integral_nonneg fun z => mul_self_nonneg _
  have hAJ := J1 u₁ hu₁
  have h1 : (∫ z in Cyl.cell c, B0151.derivWord u₁ g₁ z * B0151.derivWord u₁ g₁ z) ^ (1 / 2 : ℝ)
      ≤ J ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hA0 hAJ (by norm_num)
  have hJh0 : 0 ≤ J ^ (1 / 2 : ℝ) := Real.rpow_nonneg hJ0 _
  have hBp0 : 0 ≤ (∫ z in Cyl.cell c, |B0151.derivWord u₂ g₂ z| ^ (2 * (n:ℝ) / l₁)) ^
      (1 / (2 * (n:ℝ) / l₁)) :=
    Real.rpow_nonneg (integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _) _
  have hDq0 : 0 ≤ (∫ z in Cyl.cell c, |B0151.derivWord u₃ g₃ z| ^ (2 * (n:ℝ) / l₂)) ^
      (1 / (2 * (n:ℝ) / l₂)) :=
    Real.rpow_nonneg (integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _) _
  have hX0 : 0 ≤ C' * (G ^ (1 - (l₁:ℝ) / n) * J ^ ((l₁:ℝ) / (2 * n))) :=
    mul_nonneg hC' (mul_nonneg (Real.rpow_nonneg hG0 _) (Real.rpow_nonneg hJ0 _))
  -- Exponent bookkeeping for `G` (exponents add to `1`).
  have hsG : (1 - (l₁:ℝ) / n) + (1 - (l₂:ℝ) / n) = 1 := by
    have : (l₁:ℝ) / n + (l₂:ℝ) / n = 1 := by
      rw [← add_div, hsumR, div_self hnne]
    linarith
  have hneG : (1 - (l₁:ℝ) / n) + (1 - (l₂:ℝ) / n) ≠ 0 := by
    rw [hsG]; norm_num
  have eG : G ^ (1 - (l₁:ℝ) / n) * G ^ (1 - (l₂:ℝ) / n) = G := by
    rw [← Real.rpow_add' hG0 hneG, hsG, Real.rpow_one]
  -- Exponent bookkeeping for `J` (exponents `1/2`, `l₁/(2n)`, `l₂/(2n)` add to `1`).
  have hsJ : (1 / 2 : ℝ) + (l₁:ℝ) / (2 * n) + (l₂:ℝ) / (2 * n) = 1 := by
    linarith
  have hneJ1 : (1 / 2 : ℝ) + (l₁:ℝ) / (2 * n) ≠ 0 := by positivity
  have hneJ2 : (1 / 2 : ℝ) + (l₁:ℝ) / (2 * n) + (l₂:ℝ) / (2 * n) ≠ 0 := by
    rw [hsJ]; norm_num
  have eJ : J ^ (1 / 2 : ℝ) * J ^ ((l₁:ℝ) / (2 * n)) * J ^ ((l₂:ℝ) / (2 * n)) = J := by
    rw [← Real.rpow_add' hJ0 hneJ1, ← Real.rpow_add' hJ0 hneJ2, hsJ, Real.rpow_one]
  -- Assemble.
  refine le_trans hH' ?_
  refine le_trans (mul_le_mul (mul_le_mul h1 hBp hBp0 hJh0) hDq hDq0 (mul_nonneg hJh0 hX0)) ?_
  refine le_of_eq ?_
  linear_combination (C' * C' * (J ^ (1 / 2 : ℝ) * J ^ ((l₁:ℝ) / (2 * n)) * J ^ ((l₂:ℝ) / (2 * n)))) * eG
    + (C' * C' * G) * eJ
